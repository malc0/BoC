#!/usr/bin/perl -T

use 5.014;	# get guaranteed correct exception handling
use warnings;

use Fcntl qw(O_RDWR O_WRONLY O_EXCL O_CREAT LOCK_EX LOCK_SH LOCK_NB SEEK_SET);
use CGI qw(param);
use CGI::Carp qw(fatalsToBrowser);
use Digest::SHA qw(sha1_hex);
use List::Util qw(first max min sum);
use Text::Wrap;
use Time::HiRes 1.9725 qw(stat usleep);

# non core
use CGI::Session '-ip-match';
use Crypt::Cracklib;	# this is optional: comment this and the two lines below containing the substring `rack' to avoid it
use Crypt::PasswdMD5;
use File::Slurp;
use Git::Wrapper;
use HTML::Template;
use HTML::Template::Pro;
use JSON::XS;
use MIME::Lite;
use Text::Password::Pronounceable;
use Time::ParseDate;
use UUID::Tiny;

use lib '.';
use Accts;
use Attrs;
use CleanData qw(untaint encode_for_commit encode_for_file encode_for_filename encode_for_html transcode_uri_for_html clean_date clean_email clean_filename clean_int clean_text clean_unit clean_username clean_word clean_words true validate_acct validate_acctname validate_date validate_decimal validate_int validate_unitname validate_unit);
use Events;
use HeadedTSV;
use TG;
use Units;

use subs qw(unlink);

my %config;
my $git;
my %tgds;	# only ever used in generate phase, so never twice in one request
my %pres;
my %evs;

sub unlink
{
	CORE::unlink($_[0]) or die;
}

sub update_global_config
{
	my (%append_cfg) = @_;

	@config{keys %append_cfg} = values %append_cfg;	# merge settings
	$config{LongName} //= 'Set LongName in installation config!';
	$config{ShortName} //= 'Set ShortName in installation config!';
	$config{StyleURL} //= 'boc.pl?serve=bocstyle';
	$config{TimeoutURL} //= 'boc.pl?serve=timeout';

	return;
}

sub flock_and_read
{
	my ($filename, $shared) = @_;

	sysopen (my $fh, $filename, O_RDWR|O_CREAT) or die;
	flock ($fh, $shared ? LOCK_SH : LOCK_EX) or die;

	my $data;
	read_file($fh, buf_ref => \$data);
	my $datahr = $data ? decode_json($data) : {};

	return ($fh, $datahr);
}

sub flock_rc
{
	(my $fh, my $hr) = flock_and_read($_[0], 1);
	close $fh or die;
	return $hr;
}

sub write_and_close
{
	my ($fh, $datahr) = @_;

	my $data = encode_json($datahr);
	seek ($fh, 0, SEEK_SET) or die;
	truncate ($fh, 0) or die;
	return write_file($fh, $data);	# write_file does close() for us
}

sub flock_wc
{
	my ($filename, $hr) = @_;

	sysopen (my $fh, $filename, O_RDWR|O_CREAT) or die "Couldn't open $filename";
	flock ($fh, LOCK_EX) or die;

	return write_and_close($fh, $hr);
}

sub flock_rm
{
	my ($filename) = @_;

	if (sysopen (my $fh, $filename, O_WRONLY)) {
		flock ($fh, LOCK_EX) or die;
		unlink $filename;
		close $fh or die;
	}

	return;
}

sub push_session_data
{
	my ($sessid, $key, $value) = @_;

	my $file = File::Spec->tmpdir() . '/' . sprintf("${CGI::Session::Driver::file::FileName}_bocdata", $sessid);

	my ($fh, $data) = flock_and_read($file);
	$data->{$key} = $value;

	return write_and_close($fh, $data);
}

sub pop_session_data
{
	my ($sessid, $key) = @_;

	my $file = File::Spec->tmpdir() . '/' . sprintf("${CGI::Session::Driver::file::FileName}_bocdata", $sessid);

	my ($fh, $data) = flock_and_read($file);

	unless (defined $data->{$key}) {
		close ($fh);
		return undef;
	}

	my $value = $data->{$key};
	delete $data->{$key};

	write_and_close($fh, $data);

	return $value;
}

sub peek_session_data
{
	my ($sessid, $key) = @_;

	my $file = File::Spec->tmpdir() . '/' . sprintf("${CGI::Session::Driver::file::FileName}_bocdata", $sessid);

	return flock_rc($file)->{$key};
}

sub get_edit_token
{
	my ($sessid, $add_obj_str, $nest) = @_;

	my $tok_obj = peek_session_data(@_);
	push (@{$tok_obj}, create_UUID_as_string(UUID_V4));
	push_session_data($sessid, @{$tok_obj}[-1], $nest) if $nest;
	push_session_data($sessid, $add_obj_str, $tok_obj);

	return @{$tok_obj}[-1];
}

sub redeem_edit_token
{
	my ($sessid, $add_obj_str, $etoken) = @_;

	my $rv = eval {
		my $tok_obj = peek_session_data($sessid, $add_obj_str);
		return undef unless defined $tok_obj;

		my $index = first { @{$tok_obj}[$_] eq $etoken } 0 .. $#{$tok_obj};
		return undef unless defined $index;

		return pop_session_data($sessid, $add_obj_str) if scalar @{$tok_obj} == 1;

		splice (@{$tok_obj}, $index, 1);
		push_session_data($sessid, $add_obj_str, $tok_obj);
		return $etoken;
	};

	return ($@ or not $rv) ? undef : $rv;
}

sub try_lock_raw
{
	my ($file, $sessid, $renew) = @_;
	my $lockfile = "$file.lock";
	$lockfile =~ s/^(.*\/)([^\/]*)/$1.$2/;	# insert a . to hide file (especially from directory globbing)
	my $lock;

	unless (sysopen ($lock, $lockfile, O_WRONLY | O_EXCL | O_CREAT)) {	# we assume it's not on NFSv2
		my $mtime = (stat($lockfile))[9];

		if ($mtime && (time() - $mtime) < 600) {
			my $mine = 0;

			return undef unless open ($lock, '<', $lockfile);
			$mine = $sessid eq <$lock>;
			return undef unless close ($lock);

			return ($mine ? 0 : undef) unless $mine && $renew;
		}

		return undef unless open ($lock, '+>', $lockfile);
		return undef unless flock ($lock, LOCK_EX | LOCK_NB);
	}

	print $lock $sessid;

	return undef unless close ($lock);

	return $sessid;
}

sub unlock
{
	my $lockfile = "$_[0].lock";
	$lockfile =~ s/^(.*\/)([^\/]*)/$1.$2/;	# insert a . to hide file (especially from directory globbing)
	return unlink $lockfile;
}

sub try_lock_wait_raw
{
	my ($file, $sessid) = @_;

	my $ms_remaining = 5000;
	while ($ms_remaining) {
		return $sessid if (try_lock_raw($file, $sessid));
		usleep(10000);
		$ms_remaining -= 10;
	}
	return undef;
}

sub try_commit_lock
{
	return try_lock_wait_raw("$config{Root}/DSLOCK", $_[0]);
}

sub un_commit_lock
{
	return unlink "$config{Root}/.DSLOCK.lock";
}

sub cache_lock
{
	# NOTE: VERY important this is against DSLOCK: we are trying to
	# guarantee no data-store writes during the lock
	# FIXME: no use of sessid (since we normally don't have it)
	# Seems very unlikely you'd ordinarily get stuck between lock and unlock
	return try_lock_raw("$config{Root}/DSLOCK", 'cache');
}

sub cache_unlock
{
	return un_commit_lock;
}

sub try_lock
{
	my ($file, $sessid, $renew) = @_;

	return undef unless try_commit_lock($sessid);
	my $rv = try_lock_raw($file, $sessid, $renew);
	un_commit_lock;
	return $rv;
}

sub clear_lock
{
	my ($lf, $sessid) = @_;

	(my $file = $lf) =~ s/(.*)\/\.([^\/]*).lock/$1\/$2/;
	return 1 unless try_lock($file, $sessid);
	unlink $lf;

	return undef;
}

sub clear_locks
{
	my ($path, $sessid) = @_;

	foreach (glob ("$path/.*.lock")) {
		$_ = untaint($_);
		return 1 if clear_lock($_, $sessid);
	}

	return undef;
}

sub read_simp_cfg
{
	return read_htsv(@_);
}

sub write_simp_cfg
{
	my ($file, %cfg) = @_;

	return write_htsv($file, \%cfg);
}

sub fmtime
{
	return ((stat ("$config{Root}/$_[0]"))[9] // 0);
}

sub read_tg2
{
	my ($tg_file) = @_;

	unless ($tg_file =~ /.*\/E([^\/]+)$/ && -e "$config{Root}/events/$1") {
		(my $tg = $tg_file) =~ s/.*\/([^\/]+)$/$1/;
		my $mtime = fmtime("transaction_groups/$tg");
		if (fmtime("transaction_groups/.$tg.json") > $mtime) {
			return %{flock_rc("$config{Root}/transaction_groups/.$tg.json")};
		} else {
			my %tgd = read_tg($tg_file);
			if (cache_lock) {
				flock_wc("$config{Root}/transaction_groups/.$tg.json", \%tgd) if fmtime("transaction_groups/$tg") == $mtime;
				cache_unlock;
			}
			return %tgd;
		}
	}

	return event_to_tg(%{{read_htsv("$config{Root}/events/$1", undef, [ 'Person', 'Notes' ])}});
}

sub read_htsv_encode
{
	my $content = $_[0];

	foreach my $key (keys %$content) {
		$content->{$key} = encode_for_html($content->{$key}) unless (ref($content->{$key}) || !$content->{$key});
		@{$content->{$key}} = map ($_ eq '' ? undef : $_, split ('&#9;', encode_for_html(join ('	', map ((defined) ? $_ : '', @{$content->{$key}}))), -1)) if ref ($content->{$key});
		$content->{encode_for_html($key)} = delete $content->{$key};
	}

	return;
}

sub write_htsv_encode
{
	my $content = $_[0];

	foreach my $key (keys %$content) {
		$content->{$key} = encode_for_file($content->{$key}) unless (ref($content->{$key}) || !$content->{$key});
		@{$content->{$key}} = map (encode_for_file($_), @{$content->{$key}}) if ref ($content->{$key});
		$content->{encode_for_file($key)} = delete $content->{$key};
	}

	return;
}

sub commit
{
	my ($message, $userdata) = @_;
	my $user = ref $userdata ? $userdata->param('User') : $userdata;
	my $name = ref $userdata ? $userdata->param('Name') : $userdata;
	return $git->commit({ author => encode_for_commit("$name <$user>"), message => encode_for_commit($message) });
}

sub add_commit
{
	my ($file, $message, $userdata) = @_;
	$git->add($file);
	my $statuses = $git->status;
	commit($message, $userdata) if $statuses->get('indexed');
	return;
}

sub try_commit_and_unlock
{
	my ($sub, $extra_lock) = @_;

	eval { $sub->() };
	my $commit_fail = $@;
#	say STDERR $@->output() if $@;
	if ($commit_fail) {
		eval { $git->reset({hard => 1}) };
		eval { unlink untaint($_) foreach (glob ("$config{Root}/*.new $config{Root}/*/*.new")) } unless $@;
		if ($@) {
			# die hard, leaving locks, if we can't clean up
			unless (-e "$config{Root}/RepoBroke") {
				open (my $fh, '>', "$config{Root}/RepoBroke");
				close $fh;
			}
			die "Clean up failed: $@\nOriginally due to: $commit_fail";
		}
	}
	un_commit_lock;
	unlock($extra_lock) if $extra_lock;
	die $commit_fail if $commit_fail;

	return;
}

sub bad_token_whinge
{
	un_commit_lock;
	return whinge('Invalid edit token (double submission?)', $_[0]);
}

sub unroot
{
	return undef unless $_[0] =~ /$config{Root}\/(.*)/;
	return $1;
}

sub nonfinite
{
	my $infinite = 0;
	foreach (@_) {
		$infinite++ if $_ == 0+'inf' || $_ == 0-'inf';
	}
	return $infinite;
}

sub compute_tg_c
{
	my ($tg, $omit, $neg_accts, $resolved, $rel_acc, $rel_accts, $die) = @_;

	return if $omit && exists $tgds{$tg}->{Omit};

	if (-r "$config{Root}/transaction_groups/$tg" && exists $pres{$tg}) {
		return %{$pres{$tg}} unless $rel_acc && exists $pres{$tg}->{$rel_acc} || exists $tgds{$tg}->{Omit};
	}

	my %computed;
	my $newest = fmtime('newest');
	if (-r "$config{Root}/transaction_groups/$tg" && -r "$config{Root}/transaction_groups/.$tg.precomp") {
		%computed = %{flock_rc("$config{Root}/transaction_groups/.$tg.precomp")};

		goto compute_me if $rel_acc && exists $computed{$rel_acc};

		return %computed if fmtime("transaction_groups/.$tg.precomp") > $newest;

		goto compute_me if $tg =~ /^[A-Z]/ || exists $tgds{$tg}->{Omit};

		return %computed unless (-M "$config{Root}/transaction_groups/.$tg.precomp" > -M "$config{Root}/transaction_groups/$tg") || (-M "$config{Root}/transaction_groups/.$tg.precomp" > -M "$config{Root}/config_units");
	}

compute_me:
	%computed = compute_tg($tg, $tgds{$tg}, undef, $neg_accts, $resolved, $die, $rel_acc, $rel_accts, fmtime("transaction_groups/.$tg.precomp") > $newest);

	# check for drains directly; this means resolution can be done without account validation,
	# and account validation can be done separately from resolution
	foreach (0 .. $#{$tgds{$tg}->{Creditor}}) {
		return %computed if $tgds{$tg}->{Amount}[$_] =~ /^\s*[*]\s*$/ && !($tgds{$tg}->{Creditor}[$_] =~ /^TrnsfrPot\d$/);
	}

	unless ($rel_acc || nonfinite(values %computed) || !cache_lock) {
		flock_wc("$config{Root}/transaction_groups/.$tg.precomp", \%computed) if fmtime('newest') == $newest;
		cache_unlock;
	}

	return %computed;
}

sub drained_accts
{
	my ($exempt, $to_zero_only) = @_;
	$exempt = '' unless $exempt;
	my %drained;

	my $newest = fmtime('newest');
	%tgds = %{flock_rc("$config{Root}/transaction_groups/.tgds")} if fmtime('transaction_groups/.tgds') > $newest;
	foreach my $tg (glob ("$config{Root}/transaction_groups/*")) {
		$tg = $1 if $tg =~ /([^\/]*)$/;
		$tgds{$tg} = \%{{read_tg2("$config{Root}/transaction_groups/$tg")}} unless exists $tgds{$tg};
		my %tgdetails = %{$tgds{$tg}};
		next if exists $tgdetails{Omit};

		foreach (0 .. $#{$tgdetails{Creditor}}) {
			push (@{$drained{$tgdetails{Creditor}[$_]}}, $tg) if (defined $tgdetails{Creditor}[$_] && $tgdetails{Amount}[$_] =~ /^\s*[*]\s*$/ && !($tgdetails{Creditor}[$_] =~ /^TrnsfrPot\d$/)) && $tg ne $exempt && !($to_zero_only && $tgdetails{$tgdetails{Creditor}[$_]}[$_]);
		}
	}
	if (%tgds && cache_lock) {
		flock_wc("$config{Root}/transaction_groups/.tgds", \%tgds) unless (fmtime('newest') != $newest || fmtime('transaction_groups/.tgds') > $newest);
		cache_unlock;
	}

	return %drained;
}

sub double_drainers
{
	my %drained = drained_accts;
	my %bad;

	foreach my $acct (grep (scalar @{$drained{$_}} > 1, keys %drained)) {
		$bad{$_} = $acct foreach (@{$drained{$acct}});
	}

	return %bad;
}

sub stround
{
	# this whole ridiculous mess is coz Perl does very odd and unhelpful rounding
	my ($n, $places) = @_;
	my $sign = ($n < 0) ? '-' : '';
	my $abs = abs $n;

	return sprintf("%.${places}f", $sign . substr ($abs + ('0.' . '0' x $places . '5'), 0, $places + length (int ($abs)) + 1));
}

sub resolve_accts
{
	my ($ddsr, $nar) = @_;
	my %dds = %{$ddsr};
	my %neg_accts = %{$nar};
	my %das = drained_accts(undef, 1);
	my %resolved;
	my $loops = 50;

	my $newest = fmtime('newest');
	return %{flock_rc("$config{Root}/transaction_groups/.res")} if fmtime('transaction_groups/.res') > $newest;
	%pres = %{flock_rc("$config{Root}/transaction_groups/.pres")} if fmtime('transaction_groups/.pres') > $newest;
	while ($loops--) {
		my %running;
		$running{$_} = 0 foreach (keys %das);

		foreach my $tg (glob ("$config{Root}/transaction_groups/*")) {
			$tg = $1 if $tg =~ /([^\/]*)$/;
			next if exists $dds{$tg};
			my %computed = eval { compute_tg_c($tg, 1, \%neg_accts, \%resolved) };
			return if $@;
			foreach (keys %computed) {
				$running{$_} = 0 unless exists $running{$_};
				$running{$_} += $computed{$_};
			}
			$pres{$tg} = \%computed unless $pres{$tg} || nonfinite(values %computed) || !(-r "$config{Root}/transaction_groups/.$tg.precomp");
		}

		my $unresolved = nonfinite(values %resolved);

		my $again = 0;
		foreach (keys %resolved) {
			if (exists $das{$_} && $running{$_} != $resolved{$_} && abs $resolved{$_} != 0+'inf' && abs $running{$_} >= .005) {
				$resolved{$_} = stround($resolved{$_} + $running{$_}, 2);
				$again = 1;
			}
		}
		next if $again;

		foreach (keys %running) {
			$resolved{$_} = $running{$_} if !exists $resolved{$_} || nonfinite($resolved{$_});
		}

		if (nonfinite(values %resolved) == 0 || nonfinite(values %resolved) == $unresolved) {
			if (cache_lock) {
				if (fmtime('newest') == $newest) {
					flock_wc("$config{Root}/transaction_groups/.pres", \%pres) unless !%pres || fmtime('transaction_groups/.pres') > $newest;
					flock_wc("$config{Root}/transaction_groups/.res", \%resolved) unless !%resolved || nonfinite(values %resolved) || fmtime('transaction_groups/.res') > $newest;
				}
				cache_unlock;
			}
			return %resolved;
		}
	}

	return;
}

sub load_template
{
	my ($file, $etoken, $session, $not_pro) = @_;

	my $tmpl;
	unless ($not_pro) {
		$tmpl = HTML::Template::Pro->new(filename => $file, global_vars => 1, case_sensitive => 1) or die;
	} else {
		$tmpl = HTML::Template->new(filename => $file, global_vars => 1, case_sensitive => 1) or die;
	}
	$tmpl->param(SN => $config{ShortName});
	$tmpl->param(LN => $config{LongName});
	$tmpl->param(JS => $config{TimeoutURL});
	$tmpl->param(STYLE => $config{StyleURL});
	$tmpl->param(ETOKEN => $etoken) if $etoken;
	$tmpl->param(TCP => $session->param('IsAdmin')) if $session;
	return $tmpl;
}

sub load_email_template
{
	my ($file, $url) = @_;

	my $tmpl = HTML::Template::Pro->new(filename => $file, case_sensitive => 1) or die;
	$tmpl->param(SN => $config{ShortName});
	$tmpl->param(LN => $config{LongName});
	$tmpl->param(URL => $url, CONTACT => $config{email});
	return $tmpl;
}

sub emit
{
	print "Content-Type: text/html\n\n", $_[0]->output;
	exit;
}

sub emit_with_status
{
	my ($status, $tmpl) = @_;
	$tmpl->param(STATUS => encode_for_html($status));
	print "Content-Type: text/html\n\n", $tmpl->output;
	exit;
}

sub serve
{
	my ($file, $type) = @_;

	my @st = stat($file);
	my ($sec, $min, $hour, $mday, $mon, $year, $wday, $yday, $isdst) = gmtime(CleanData::clean_decimal($st[9]));
	my @weekday = qw(Sun Mon Tue Wed Thu Fri Sat);
	my @month = qw(Jan Feb Mar Apr May Jun Jul Aug Sep Oct Nov Dec);
	$year += 1900;

	print "Content-Type: $type\n";
	# Last-Modified means browser-side caching might work...
	printf "Last-Modified: $weekday[$wday], %02d $month[$mon] $year %02d:%02d:%02d GMT\n", $mday, $hour, $min, $sec;
	print "Content-Length: $st[7]\n\n";

	open (my $fh, '<', $file) or die;
	while (<$fh>) {
		print;
	}
	close ($fh);

	exit;
}

sub pre_whinge
{
	my ($whinge, $tmpl) = @_;
	my $old_param = $tmpl->param('WHINGE') ? $tmpl->param('WHINGE') . ' ' : '';
	$tmpl->param(WHINGE => $old_param . encode_for_html($whinge));
	return 0;
}

sub whinge
{
	my ($whinge, $tmpl) = @_;
	my $old_param = $tmpl->param('WHINGE') ? $tmpl->param('WHINGE') . ' ' : '';
	$tmpl->param(WHINGE => $old_param . encode_for_html($whinge));
	print "Content-Type: text/html\n\n", $tmpl->output;
	exit;
}

sub gen_cds_p
{
	my $reason = $_[0];
	my $tmpl = load_template('create_ds_p.html');
	$tmpl->param(REASON => encode_for_html($reason));
	$tmpl->param(ROOT => $config{Root});

	return $tmpl;
}

sub create_datastore
{
	my ($cgi, $reason) = @_;

	if (defined $cgi->param('tmpl') and $cgi->param('tmpl') eq 'create_ds_p') {
		my $whinge = sub { whinge($_[0], gen_cds_p($reason)) };
		my $user_path = "$config{Root}/users";
		my $user = validate_acctname(scalar $cgi->param('user'), $whinge);

		my $cracklib_rv = fascist_check($cgi->param('pass'));
		$whinge->("Problem with password: $cracklib_rv") unless ($cracklib_rv eq 'ok');

		my $cryptpass = unix_md5_crypt($cgi->param('pass'));
		my %userdetails = (
			Name => $user,	# FIXME could do a full "Add user" page/parse?
			Password => $cryptpass,
			IsAdmin => undef,
		);
		(mkdir $user_path or die) unless (-d "$user_path");
		$git->init();
		$whinge->('Unable to get commit lock') unless try_commit_lock($cryptpass);
		# no session so not edit_token protected.
		try_commit_and_unlock(sub {
			write_simp_cfg("$user_path/$user", %userdetails);
			add_commit("$user_path/$user", 'CDS admin creation', $user);
		});
	} else {
		emit(gen_cds_p($reason));
	}

	return;
}

sub gen_login
{
	my $tmpl = load_template('login.html');
	$tmpl->param(USER => $_[0]);

	return $tmpl;
}

sub login
{
	my $cgi = $_[0];
	my $user = clean_username($cgi->param('user'));
	my $pass = $cgi->param('pass');
	my $whinge = sub { whinge('Login failed!', gen_login($user)) };

	$whinge->() unless $user and (-r "$config{Root}/users/$user");
	my %userdetails = read_simp_cfg("$config{Root}/users/$user");
	$whinge->() unless defined $userdetails{Password};

	my ($empty, $id, $salt, $encrypted) = split(/\$/, $userdetails{Password}, 4);

	my $cryptpass = unix_md5_crypt($pass, $salt);

	sleep(1);	# avoid remote brute-forcing

	$whinge->() unless ($cryptpass eq $userdetails{Password});

	$userdetails{User} = $user;
	return %userdetails;
}

sub gen_login_nopw
{
	my $tmpl = load_template('login_nopw.html');

	my @users = glob ("$config{Root}/users/*");
	my @userlist;

	foreach my $user (@users) {
		next unless $user =~ /.*\/(.*)/;
		push (@userlist, { USER => $1 });
	}
	$tmpl->param(PPL => \@userlist);

	return $tmpl;
}

sub login_nopw
{
	my ($cgi, $userdetout) = @_;
	my $user = clean_username($cgi->param('user'));

	whinge('Login failed!', gen_login_nopw) unless $user and (-r "$config{Root}/users/$user");
	my %userdetails = read_simp_cfg("$config{Root}/users/$user");
	$userdetails{User} = $user;
	%{$userdetout} = %userdetails;

	return (defined $userdetails{Password}) ? 'No PW login on account with password set?' : 'ok';
}

sub clear_old_session_locks
{
	my $sessid = $_[0];
	my @locks = glob ("$config{Root}/*/.*.lock");
	push (@locks, glob ("$config{Root}/.config*.lock"));
	push (@locks, "$config{Root}/.DSLOCK.lock");

	foreach my $lockfile (@locks) {
		$lockfile = untaint($lockfile);
		next unless open (my $lock, '<', $lockfile);

		unlink ($lockfile) if $sessid eq <$lock>;

		close ($lock);
	}

	return;
}

sub refresh_session
{
	my ($session, $username, $authed) = @_;

	$session->param('AcctMtime', fmtime("users/$username"));

	my %userdetails = read_simp_cfg("$config{Root}/users/$username");
	$userdetails{User} = $username;
	delete $userdetails{IsAdmin} unless $authed;

	my %attr_syns = get_attr_synonyms;
	my @sys_attrs = get_sys_attrs;
	my %perms;
	foreach my $sysattr (@sys_attrs) {
		$perms{$sysattr} = grep (attr_condition_met($_, $authed, %userdetails), @{$attr_syns{$sysattr}});
	}

	$session->param('User', $userdetails{User});
	$session->param('Name', exists $userdetails{Name} ? $userdetails{Name} : $userdetails{User});
	$session->param($_, $perms{$_}) foreach (@sys_attrs);
	$session->param('Instance', $config{Root});
	$session->expire('+10m');
	$session->flush();
}

sub get_new_session
{
	my ($session, $cgi) = @_;
	my $last_tmpl = $cgi->param('tmpl') // '';

	my $expired = ($session->is_expired() and not defined $cgi->param('logout'));
	$session->delete();
	$session->flush();

	if (defined $cgi->cookie(CGI::Session->name()) and $cgi->cookie(CGI::Session->name()) =~ /^([a-f0-9]*)$/) {	# hex untaint
		my $old_bocdata = File::Spec->tmpdir() . '/' . sprintf("${CGI::Session::Driver::file::FileName}_bocdata", $1);
		unlink $old_bocdata if -r $old_bocdata;
		clear_old_session_locks($1);
	}

	my $tmpl;
	my %userdetails;
	my $authed = 0;
	if ($last_tmpl eq 'login_nopw' and exists $config{Passwordless}) {
		$tmpl = gen_login($userdetails{User}) if (login_nopw($cgi, \%userdetails) eq 'No PW login on account with password set?');
	} elsif ($last_tmpl eq 'login') {
		%userdetails = login($cgi);
		$authed = 1;
	} else {
		$tmpl = (exists $config{Passwordless}) ? gen_login_nopw : gen_login;
	}
	($expired ? whinge('Session expired', $tmpl) : emit($tmpl)) if $tmpl;

	$session = CGI::Session->new($cgi) or die CGI::Session->errstr;
	print $session->header();
	refresh_session($session, $userdetails{User}, $authed);

	return $session;
}

sub valid_fee_cfg
{
	local $_;
	return unless -r "$config{Root}/config_fees";

	my %cf = read_htsv("$config{Root}/config_fees");

	my %acct_names = get_acct_name_map;
	my $whinge = sub { goto whingefail };
	validate_acct($cf{DefaultAccount}, \%acct_names, $whinge);

	return %cf unless exists $cf{Headings};

	foreach my $hd ('Fee', 'IsBool', 'IsDrain', 'Expensable', 'Account', 'Description') {
		return unless grep ($_ eq $hd, @{$cf{Headings}});
		return unless exists $cf{$hd};
	}

	my %cds = known_commod_descs;

	my %seen;
	foreach (@{$cf{Fee}}) {
		return unless defined;
		return if $seen{$_}++;
	}

	foreach my $row (0 .. $#{$cf{Fee}}) {
		return if clean_int($cf{Fee}[$row]);
		return unless defined $cf{Account}[$row] && exists $acct_names{$cf{Account}[$row]};

		if ($cf{Fee}[$row] =~ /[A-Z]/) {
			return unless exists $cds{$cf{Fee}[$row]};
			return if true($cf{IsDrain}[$row]) || true($cf{Expensable}[$row]);
		} else {
			return if true($cf{IsBool}[$row]) && !true($cf{IsDrain}[$row]);
			return if true($cf{IsBool}[$row]) && true($cf{Expensable}[$row]);
			return unless defined $cf{Description}[$row] && length $cf{Description}[$row];
		}
	}

	return %cf;

whingefail:
	return;
}

sub get_cf_drains
{
	my %cf = @_;

	my %drains;
	$drains{$cf{Fee}[$_]} = 1 foreach (grep (!($cf{Fee}[$_] =~ /[A-Z]/) && true($cf{IsDrain}[$_]), 0 .. $#{$cf{Fee}}));
	return %drains;
}

sub gen_tcp
{
	my $tmpl = load_template('treasurer_cp.html');

	my %units_cfg = read_units_cfg("$config{Root}/config_units");
	validate_units(\%units_cfg, sub { $tmpl->param(WHINGE => 'Units config broken: fix it!') }, 1, "$config{Root}/config_units");

	my %vaccts = grep_acct_key('accounts', 'Name');
	my %cf = valid_fee_cfg;
	$tmpl->param(VACCTS => scalar keys %vaccts, EVENTS => !!%cf, COMMODS => ((scalar keys %{{known_commod_descs}}) + (scalar keys %{{get_cf_drains(%cf)}})), CF_UNITS => (exists $cf{Fee} && scalar @{$cf{Fee}}));
	pre_whinge('Expenses config is broken', $tmpl) if !%cf && -e "$config{Root}/config_fees";

	return $tmpl;
}

sub gen_manage_accts
{
	my $people = $_[0];
	my $tmpl = load_template('manage_accts.html');
	my @accounts = $people ? glob ("$config{Root}/users/*") : glob ("$config{Root}/accounts/*");
	my @acctlist;
	my @attrs_list = (get_attrs, 'Password');

	foreach my $acct (@accounts) {
		my %acctdetails = read_simp_cfg($acct);
		next unless $acct =~ /.*\/(.*)/;
		my %outputdetails = ( ACCT => $1, ACCT_CL => clean_username($1) ? '' : 'broken', NAME => $acctdetails{Name}, NAME_CL => (defined $acctdetails{Name} && length $acctdetails{Name}) ? '' : 'broken' );
		if ($people) {
			my @attrs = map ({ C => (exists $acctdetails{$_} || $_ eq 'IsPleb') }, @attrs_list);
			%outputdetails = ( %outputdetails,
				EMAIL => $acctdetails{email},
				EMAIL_CL => clean_email($acctdetails{email}) ? '' : 'broken',
				ATTRS => \@attrs,
				PW => (exists $acctdetails{Password}),
			);
		} else {
			%outputdetails = ( %outputdetails,
				IS_NEGATED => (exists $acctdetails{IsNegated}),
			);
		}
		push (@acctlist, \%outputdetails);
	}
	my @attrsh = map ({ A => $_ }, @attrs_list);
	$tmpl->param(ATTRSH => \@attrsh);
	$tmpl->param(ACCTS => \@acctlist);
	$tmpl->param(USER_ACCT => 1) if $people;

	return $tmpl;
}

sub fmt_impl_attrs
{
	return undef unless $_[0];
	
	my $s = $_[0];
	$s =~ s/\s*:\s*/, /g;
	return $s;
}

sub gen_add_edit_acc
{
	my ($edit_acct, $person, $session, $etoken, $filt_sys_attrs) = @_;
	my $tmpl = load_template('edit_acct.html', $etoken);
	my %acctdetails;
	my %addr_alts = read_htsv("$config{Root}/config_addr_alts", 1);

	if ($edit_acct) {
		$tmpl->param(ADMINCHECK => 1) if $session->param('User') eq $edit_acct && $session->param('IsAdmin');
		$tmpl->param(EACCT => $edit_acct);
		%acctdetails = read_simp_cfg($person ? "$config{Root}/users/$edit_acct" : "$config{Root}/accounts/$edit_acct");
		$tmpl->param(ACCT => $edit_acct);
		$tmpl->param(NAME => $acctdetails{Name});
		$tmpl->param(EMAIL => $acctdetails{email});
		$tmpl->param(ADDRESS => $acctdetails{Address});
		$tmpl->param(IS_NEGATED => 1) if exists $acctdetails{IsNegated};
	}

	my %attrs = get_attrs_full(0, 1);
	if ($filt_sys_attrs) {
		my %syns = get_attr_synonyms;
		foreach my $sa (get_sys_attrs) {
			foreach (@{$syns{$sa}}) {
				delete $attrs{$_} foreach (split ('&amp;&amp;'));
			}
		}
	}
	my @attr_set = map ({ A => $_, C => (exists $acctdetails{$_} || $_ eq 'IsPleb'), I => fmt_impl_attrs($attrs{$_}), D => ($_ eq 'IsPleb') }, keys %attrs);
	$tmpl->param(ATTRS => \@attr_set);

	$tmpl->param(USER_ACCT => 1) if $person;

	my @alts;
	foreach my $alt (@{$addr_alts{Headings}}) {
		my @extra = (!(defined $acctdetails{$alt}) || grep ($_ eq $acctdetails{$alt}, @{$addr_alts{$alt}})) ? () : ($acctdetails{$alt});
		my @opts = map ({ V => $_, S => (defined $acctdetails{$alt} && $_ eq $acctdetails{$alt}) }, @{$addr_alts{$alt}}, @extra);
		push (@alts, { T => $alt, OPTS => \@opts, CL => @extra ? 'unknown' : undef });
	}
	$tmpl->param(ADDR_ALTS => \@alts);

	return $tmpl;
}

sub gen_edit_addr_alts
{
	my $tmpl = load_template('edit_addr_alts.html', $_[0]);
	my %addr_alts = read_htsv("$config{Root}/config_addr_alts", 1);
	my @alts = @{$addr_alts{Headings} // []};

	push (@alts, ('') x ((scalar @alts > 0) ? min(2, 10 - scalar @alts) : 4));

	my @altcols;
	foreach my $altn (0 .. $#alts) {
		my $defd += grep (defined, @{$addr_alts{$alts[$altn]}});
		my @opts = map ({ O => $addr_alts{$alts[$altn]}[$_], R => $_ }, 0 .. ($defd + (($defd > 0) ? min(10, 50 - $defd) : 20) - 1));
		push (@altcols, { TYPE => $alts[$altn], T => $altn, OPTS => \@opts });
	}
	$tmpl->param(COLS => \@altcols);

	return $tmpl;
}

sub gen_edit_inst_cfg
{
	my $tmpl = load_template('edit_inst_cfg.html', $_[0], undef, 1);
	my %inst_cfg = read_simp_cfg("$config{Root}/config", 1);

	foreach my $param ($tmpl->param()) {
		next if $tmpl->param($param);
		$tmpl->param($param => $inst_cfg{$param});
		$tmpl->param($param => '" data-noop="') if exists $inst_cfg{$param} and not defined $inst_cfg{$param};
	}

	return $tmpl;
}

sub gen_manage_event_types
{
	my $tmpl = load_template('manage_event_types.html');

	my %cf = valid_fee_cfg;
	my (%cfcds, %drain_descs, %exp_descs);
	foreach (0 .. $#{$cf{Fee}}) {
		$cfcds{$cf{Fee}[$_]} = 1 if $cf{Fee}[$_] =~ /[A-Z]/;
		next if $cf{Fee}[$_] =~ /[A-Z]/;
		$drain_descs{$cf{Fee}[$_]} = $cf{Description}[$_] if true($cf{IsDrain}[$_]);
		$exp_descs{$cf{Fee}[$_]} = $cf{Description}[$_] unless true($cf{IsDrain}[$_]);
	}
	my %comb_descs = (%{{ known_commod_descs }}, %drain_descs, %exp_descs);
	my %comb_exists = (%cfcds, %drain_descs, %exp_descs);
	my %vaccts = grep_acct_key('accounts', 'Name');

	my @list;
	foreach my $et_f (map { /.*\/([^\/]*)/; $1 } glob ("$config{Root}/event_types/*")) {
		my %et = read_htsv("$config{Root}/event_types/$et_f", undef, [ 'Unit', 'DispText' ]);
		my $link_acct = (exists $et{LinkedAcct}) ? $et{LinkedAcct} : $cf{DefaultAccount};
		my $valid_link = ($link_acct && exists $vaccts{$link_acct});
		my ($fees, $exps) = get_event_types(\%et, \%drain_descs);
		my @cols = map ((defined $comb_descs{$_} && length $comb_descs{$_}) ? $comb_descs{$_} : $_, (@$fees, @$exps));
		push (@list, { ET => $et_f, NAME => transcode_uri_for_html($et_f), NAME_CL => ($et_f eq 'none' || $et_f =~ /[.]/) ? 'broken' : '', A => $valid_link ? $vaccts{$link_acct} : $link_acct, ACCT_CL => $valid_link ? '' : 'broken', COLS => join (', ', @cols), CL => (scalar grep (!(exists $comb_exists{$_}), (@$fees, @$exps))) ? 'broken' : '' });
	}
	$tmpl->param(ETS => \@list);

	return $tmpl;
}

sub gen_edit_et
{
	my ($edit_id, $etoken) = @_;
	my $tmpl = load_template('edit_event_type.html', $etoken);

	my %et;
	%et = read_htsv("$config{Root}/event_types/$edit_id", undef, [ 'Unit', 'DispText' ]) if $edit_id;

	$tmpl->param(NAME => transcode_uri_for_html($edit_id));

	my %vaccts = grep_acct_key('accounts', 'Name');
	my @sorted_vaccts = sort_AoH(\%vaccts);
	my %cf = valid_fee_cfg;
	my $link_acct = (exists $et{LinkedAcct}) ? $et{LinkedAcct} : $cf{DefaultAccount};

	my @accts = map ({ O => $vaccts{$_}, V => $_, S => (defined $link_acct && $link_acct eq $_) }, @sorted_vaccts);
	unless (defined $link_acct && grep ($_ eq $link_acct, @sorted_vaccts)) {
		push (@accts, { O => $link_acct, V => $link_acct, S => 1 });
		$tmpl->param(SEL_CL => 'broken');
	}
	$tmpl->param(ACCTS => \@accts);

	my %cds = known_commod_descs;
	foreach my $thing (@{$cf{Fee}}) {
		next if grep (defined $_ && $_ eq $thing, @{$et{Unit}});
		my $pos = push (@{$et{Unit}}, $thing);
		@{$et{Column}}[$pos - 1] = 99999999;	# magic number -- attempt to sort to last in list
	}

	my %drains = get_cf_drains(%cf);
	my ($fee_rows, $exp_rows) = get_event_types(\%et, \%drains, 1);

	my (@fees, @exps);
	foreach my $ord (0 .. $#$fee_rows) {
		my $row = @$fee_rows[$ord];
		my $dr_row = (grep (@{$cf{Fee}}[$_] eq $et{Unit}[$row], 0 .. $#{$cf{Fee}}))[0] if exists $drains{$et{Unit}[$row]};
		my $unit_cl = ($et{Unit}[$row] =~ /[A-Z]/ && grep ($_ eq $et{Unit}[$row], @{$cf{Fee}})) || (exists $drains{$et{Unit}[$row]}) ? '' : 'broken';
		push (@fees, { CODE => $et{Unit}[$row], UNIT => (exists $drains{$et{Unit}[$row]}) ? @{$cf{Description}}[$dr_row] : $cds{$et{Unit}[$row]} // $et{Unit}[$row], N => $row, C_CL => $unit_cl, COL => (defined $et{Column}[$row] && $et{Column}[$row] == 99999999) ? -1 : $ord * 10 + 10, EX => true($et{Unusual}[$row]), DISP => $et{DispText}[$row] });
	}
	foreach my $ord (0 .. $#$exp_rows) {
		my $row = @$exp_rows[$ord];
		my $exp_row = (grep (@{$cf{Fee}}[$_] eq $et{Unit}[$row], grep (!exists $drains{$et{Unit}[$row]}, 0 .. $#{$cf{Fee}})))[0];
		push (@exps, { CODE => $et{Unit}[$row], UNIT => (defined $exp_row) ? @{$cf{Description}}[$exp_row] : $et{Unit}[$row], N => $row, C_CL => $exp_row ? '' : 'broken', COL => (defined $et{Column}[$row] && $et{Column}[$row] == 99999999) ? -1 : $ord * 10 + 10, EX => true($et{Unusual}[$row]), DISP => $et{DispText}[$row] });
	}

	$tmpl->param(FEES => \@fees, EXPS => \@exps);

	return $tmpl;
}

sub format_ft_name
{
	(my $name = $_[0]) =~ s/\./: /;
	$name =~ s/: none$/: No template/;
	return $name;
}

sub gen_manage_fee_tmpls
{
	my $tmpl = load_template('manage_fee_tmpls.html');

	my %cf = valid_fee_cfg;
	my @list = map ({ TMPL => $_, NAME => format_ft_name(transcode_uri_for_html($_)), CL => !!valid_ft("$config{Root}/fee_tmpls/$_", \%cf) ? undef : 'broken' }, map { /.*\/([^\/]*)/; $1 } glob ("$config{Root}/fee_tmpls/*"));
	my @ets = map { /.*\/([^\/]*)/; { ET => transcode_uri_for_html($1) } } grep (!!valid_event_type($_, \%cf), glob ("$config{Root}/event_types/*"));
	$tmpl->param(TMPLS => \@list, ETS => \@ets);

	return $tmpl;
}

sub gen_ft_tg_common
{
	my ($file, $is_tg, $max_rows, $view, $key_col, $key_fill, $cur_col, $d_row, $row_lim, $units) = @_;

	my %htsv;
	my $init_rows = 0;

	if ($file) {
		%htsv = $is_tg ? read_tg2($file) : read_htsv($file, undef, [ 'Unit', 'Condition' ]);
		$init_rows = (exists $htsv{$key_col}) ? scalar @{$htsv{$key_col}} : 0;
		$max_rows = $init_rows + ($view ? 0 : min($d_row, $row_lim - $init_rows)) if $init_rows || $view;
	}

	# saved by autovivification if the columns don't exist!
	push (@{$htsv{$key_col}}, ($key_fill) x ($max_rows - scalar @{$htsv{$key_col}}));
	push (@{$htsv{$cur_col}}, ('') x ($init_rows - scalar @{$htsv{$cur_col}})) if scalar @{$units} > 1;
	push (@{$htsv{$cur_col}}, ((scalar @{$units}) ? $$units[0] : '') x ($max_rows - scalar @{$htsv{$cur_col}})) if scalar @{$units} || exists $htsv{$cur_col};

	return %htsv;
}

sub gen_edit_fee_tmpl
{
	my ($edit_id, $etoken, $et_id, $etr) = @_;

	my $tmpl = load_template('edit_fee_tmpl.html', $etoken);

	my @units;
	my %drains = get_cf_drains(valid_fee_cfg);
	if (%$etr) {
		my ($fees, $exps) = get_event_types($etr, \%drains);
		@units = @$fees;
	} else {
		@units = (keys %{{known_commod_descs}}, keys %drains);
	}

	my %ft = gen_ft_tg_common($edit_id ? "$config{Root}/fee_tmpls/" . encode_for_filename($edit_id) : undef, 0, 5, !$etoken, 'Fee', 0, 'Unit', 3, 30, \@units);
	my %oldft = $edit_id ? read_htsv("$config{Root}/fee_tmpls/" . encode_for_filename($edit_id), undef, [ 'Unit', 'Condition' ]) : %ft;

	my %rawattrs = get_attrs_full(1, 1);
	my %moreattrs;
	foreach my $row (0 .. $#{$oldft{Fee}}) {
		next unless defined $ft{Condition}[$row];
		(my $cond = $ft{Condition}[$row]) =~ s/\s*//g;
		my @conds = split ('&amp;&amp;', $cond);
		foreach (@conds) {
			s/^!//;
			$moreattrs{$_} = 1 unless exists $rawattrs{$_};
		}
	}

	my @attrs = map ({ A => $_, I => fmt_impl_attrs($rawattrs{$_}), A_CL => exists $moreattrs{$_} ? 'broken' : '' }, (keys %rawattrs, keys %moreattrs));

	$tmpl->param(RO => !$etoken);
	$tmpl->param(FTID => transcode_uri_for_html($edit_id));
	my $name = transcode_uri_for_html($edit_id) // '';
	if ($et_id && $name =~ /^[^\/.]+\.([^\/]+)$/) {
		$name = $1;
	}
	$tmpl->param(NAME => $name) if length $name;
	$tmpl->param(ET => transcode_uri_for_html($et_id));
	$tmpl->param(NATTRS => scalar @attrs + scalar keys %moreattrs);
	$tmpl->param(FH_CL => (!$edit_id || !(exists $oldft{Headings}) || (exists $oldft{Fee} && exists $oldft{Unit})) ? '' : 'broken');
	$tmpl->param(AH_CL => (!$edit_id || !(exists $oldft{Headings}) || exists $oldft{Condition}) ? '' : 'broken');

	my @fees;
	foreach my $row (0 .. $#{$ft{Fee}}) {
		my $unk_cur = !grep ($_ eq $ft{Unit}[$row], @units);
		my @currencies = (exists $ft{Unit}) ? map ({ C => $_, S => ($_ eq $ft{Unit}[$row]) }, $unk_cur ? (@units, $ft{Unit}[$row]) : @units) : ();
		my @fattrs;
		foreach (keys %rawattrs, keys %moreattrs) {
			my $cond = '';
			($cond = $ft{Condition}[$row]) =~ s/\s*//g if defined $ft{Condition}[$row];
			$cond =~ s/&amp;/&/g;
			$cond = '&&' . $cond . '&&';
			my $if = ($cond =~ /&&$_&&/);
			my $unless = ($cond =~ /&&!$_&&/);
			$unless = 0 if $if;
			my $dc = !($if or $unless);
			push (@fattrs, { A => $_, I => $if, U => $unless, D => $dc, A_CL => exists $moreattrs{$_} ? 'broken' : '' });
		}
		push (@fees, { F => $ft{Fee}[$row], N => $row, CURS => \@currencies, FATTRS => \@fattrs, F_CL => (defined CleanData::clean_decimal($ft{Fee}[$row])) ? '' : 'broken', C_CL => $unk_cur ? 'broken' : '' });
	}

	$tmpl->param(ATTRS => \@attrs, FEES => \@fees);

	return $tmpl;
}

sub gen_edit_fee_cfg
{
	my $tmpl = load_template('edit_fee_cfg.html', $_[0]);

	my %cfg = read_htsv("$config{Root}/config_fees", 1);

	my %vaccts = grep_acct_key('accounts', 'Name');
	my @sorted_vaccts = sort_AoH(\%vaccts);

	my @accts = map ({ O => $vaccts{$_}, V => $_, S => (defined $cfg{DefaultAccount} && $cfg{DefaultAccount} eq $_) }, @sorted_vaccts);
	unless (defined $cfg{DefaultAccount} && grep ($_ eq $cfg{DefaultAccount}, @sorted_vaccts)) {
		push (@accts, { O => $cfg{DefaultAccount}, V => $cfg{DefaultAccount}, S => 1 });
		$tmpl->param(SEL_CL => 'broken');
	}

	my %ppl = grep_acct_key('users', 'Name');
	my %acct_names = (%vaccts, %ppl);
	my @sorted_accts = (@sorted_vaccts, sort_AoH(\%ppl));

	@{$cfg{Fee}} = map ($_ // '', @{$cfg{Fee}});

	my %seen;
	$seen{$_}++ foreach (@{$cfg{Fee}});

	my %cds = known_commod_descs;
	my @drains = grep (!exists $cds{$_}, @{$cfg{Fee}});
	my $num_rows = (scalar keys %cds) + (scalar @drains) + ((scalar @drains > 0) ? min(3, 30 - scalar @drains) : 4);
	my @fees = (keys %cds, @drains);
	my @feerows;
	foreach my $row (0 .. $#fees) {
		my $cf_row = first { @{$cfg{Fee}}[$_] eq $fees[$row] } 0 .. $#{$cfg{Fee}};
		my $commod = exists $cds{$fees[$row]};
		my $broken_acct = defined $cf_row && (!defined $cfg{Account}[$cf_row] || !(exists $acct_names{$cfg{Account}[$cf_row]}));
		my @unkaccts;
		@unkaccts = map ({ O => $_, V => $_, S => 1 }, ($cfg{Account}[$cf_row])) if $broken_acct && defined $cfg{Account}[$cf_row];
		my @vacctaccts = map ({ O => $vaccts{$_}, V => $_, S => (defined $cf_row && defined $cfg{Account}[$cf_row] && $cfg{Account}[$cf_row] eq $_) }, @sorted_vaccts);
		my @pplaccts = map ({ O => $ppl{$_}, V => $_, S => (defined $cf_row && defined $cfg{Account}[$cf_row] && $cfg{Account}[$cf_row] eq $_) }, sort_AoH(\%ppl));
		my $broken_fee = (defined $seen{$fees[$row]} && $seen{$fees[$row]} > 1) || !(defined $fees[$row]) || clean_int($fees[$row]) || (!$commod && $fees[$row] =~ /[A-Z]/);
		my $broken_bd = !$commod && true($cfg{IsBool}[$cf_row]) && !true($cfg{IsDrain}[$cf_row]);
		my $broken_d = $commod && $cf_row && true($cfg{IsDrain}[$cf_row]);
		my $broken_be = !$commod && true($cfg{IsBool}[$cf_row]) && true($cfg{Expensable}[$cf_row]);
		my $broken_e = $commod && $cf_row && true($cfg{Expensable}[$cf_row]);
		push (@feerows, { COMMOD => $commod, R => $row, FEEID => $fees[$row], FEED => $commod ? $cds{$fees[$row]} : $cfg{Description}[$cf_row], BOOL => (defined $cf_row && true($cfg{IsBool}[$cf_row])), DRAIN => (defined $cf_row && true($cfg{IsDrain}[$cf_row])), EXP => (defined $cf_row && true($cfg{Expensable}[$cf_row])), UNKACCTS => \@unkaccts, PPLACCTS => \@pplaccts, VACCTS => \@vacctaccts, ID_CL => $broken_fee ? 'broken' : '', DESC_CL => (!$commod && !(defined $cfg{Description}[$cf_row] && length $cfg{Description}[$cf_row])) ? 'broken' : '', B_CL => ($broken_bd || $broken_be) ? 'broken' : '', D_CL => ($broken_bd || $broken_d) ? 'broken' : '', E_CL => ($broken_be || $broken_e) ? 'broken' : '', ACCT_CL => $broken_acct ? 'broken' : '' });
	}
	my @vacctaccts = map ({ O => $vaccts{$_}, V => $_ }, @sorted_vaccts);
	my @pplaccts = map ({ O => $ppl{$_}, V => $_ }, sort_AoH(\%ppl));
	push (@feerows, { R => $_, FEEID => '', FEED => '', PPLACCTS => \@pplaccts, VACCTS => \@vacctaccts }) foreach (((scalar keys %cds) + (scalar @drains)) .. ($num_rows - 1));

	$tmpl->param(ACCTS => \@accts, FEEROWS => \@feerows);

	return $tmpl;
}

sub gen_edit_pers_attrs
{
	my $tmpl = load_template('edit_pers_attrs.html', $_[0]);

	my @types = ( 'Has', 'Is' );

	my @attrs = get_attrs(1);

	my $num_rows = (scalar @attrs > 0) ? scalar @attrs + min(5, 30 - scalar @attrs) : 10;
	push (@attrs, ('') x ($num_rows - scalar @attrs));
	my @rows;
	my %type;
	foreach my $row (0 .. ($num_rows - 1)) {
		my @rowoptions = map ({ T => $_, S => ($attrs[$row] =~ /^$_/ && ($attrs[$row] =~ s/^$_//, 1) && ($type{$attrs[$row]} = $_)) }, @types);
		push (@rowoptions, { T => '', S => 1 }) if length $attrs[$row] && !(exists $type{$attrs[$row]});
		push (@rows, { TYPES => \@rowoptions, A => $attrs[$row], OA => ((exists $type{$attrs[$row]}) ? $type{$attrs[$row]} : '') . $attrs[$row], R => $row, CL => (length $attrs[$row] && !(exists $type{$attrs[$row]})) ? 'unknown' : undef });
	}
	$tmpl->param(ROWS => \@rows);

	return $tmpl;
}

sub gen_edit_attr_groups
{
	my $tmpl = load_template('edit_attr_groups.html', $_[0]);

	my %cfg = get_attrs_full;
	my @sorted_attrs = get_attrs(1);
	my %attr_syns = get_attr_synonyms;
	my @extra_attrs = grep (!(exists $cfg{$_}), sort keys %attr_syns);

	my @impsh = map ({ I => $_ }, (@sorted_attrs, get_sys_attrs, @extra_attrs));

	my @attrs;
	foreach my $attr (@sorted_attrs, 'IsAuthed', 'IsPleb') {
		my $imp = $cfg{$attr} // '';
		my @imps = map ({ I => $_, C => ($_ eq $attr || !!($imp =~ /(^|:)\s*$_\s*(:|$)/)), NO => ($_ eq $attr) }, @sorted_attrs);
		my @simps = map ({ I => $_, C => ($_ eq $attr || !!($imp =~ /(^|:)\s*$_\s*(:|$)/)), NO => ($_ eq $attr), CL => 'system' }, get_sys_attrs);
		my @nimps = map ({ I => $_, C => ($_ eq $attr || !!($imp =~ /(^|:)\s*$_\s*(:|$)/)), NO => ($_ eq $attr), CL => 'unknown' }, @extra_attrs);
		push (@imps, (@simps, @nimps));
		push (@attrs, { A => $attr, IMPS => \@imps });
	}
	$tmpl->param(NIMPS => scalar @impsh, IMPSH => \@impsh, ATTRS => \@attrs);

	my %comb_extras;
	foreach my $comb (grep (/&amp;&amp;/, keys %cfg)) {
		$comb =~ s/\s*//g;
		$comb_extras{$_} = 1 foreach (grep (!(exists $cfg{$_}), split ('&amp;&amp;', $comb)));
	}
	push (@extra_attrs, sort keys %comb_extras);
	my @impsh2 = map ({ I => $_ }, (@sorted_attrs, get_sys_attrs, @extra_attrs));

	my @cattrs;
	foreach my $comb (grep (/&amp;&amp;/, keys %cfg)) {
		my @imps = map ({ I => $_, C => !!($comb =~ /(^|&amp;&amp;)\s*$_\s*(&amp;&amp;|$)/) }, @sorted_attrs);
		my @simps = map ({ I => $_, C => !!($comb =~ /(^|&amp;&amp;)\s*$_\s*(&amp;&amp;|$)/), CL => 'system' }, get_sys_attrs);
		my @nimps = map ({ I => $_, C => !!($comb =~ /(^|&amp;&amp;)\s*$_\s*(&amp;&amp;|$)/), CL => 'unknown' }, @extra_attrs);
		push (@imps, (@simps, @nimps));

		my $imp = $cfg{$comb} // '';
		$imp =~ s/\s*//g;
		foreach my $i (split (':', $imp)) {
			my $unk = 0;
			my @ats = map ({ A => $_, S => $i eq $_ }, (@sorted_attrs, get_sys_attrs));
			unless (grep ($_ eq $i, (@sorted_attrs, get_sys_attrs))) {
				push (@ats, { A => $i, S => 1 });
				$unk = 1;
				$tmpl->param(SEL_CL => 'unknown');
			}
			push (@cattrs, { N => scalar @cattrs, IMPS => \@imps, ATS => \@ats, SEL_CL => $unk ? 'unknown'  : '' });
		}
	}

	my @imps = map ({ I => $_ }, @sorted_attrs);
	my @simps = map ({ I => $_, CL => 'system' }, get_sys_attrs);
	my @nimps = map ({ I => $_, CL => 'unknown' }, @extra_attrs);
	push (@imps, (@simps, @nimps));
	my @ats = map ({ A => $_ }, (@sorted_attrs, get_sys_attrs));
	push (@cattrs, { N => scalar @cattrs, IMPS => \@imps, ATS => \@ats, SEL_CL => '' }) foreach (0 .. 4);

	$tmpl->param(NIMPS2 => scalar @impsh2, IMPSH2 => \@impsh2, CATTRS => \@cattrs);

	return $tmpl;
}

sub gen_edit_units
{
	my $tmpl = load_template('edit_units.html', $_[0]);

	my %cfg = read_units_cfg("$config{Root}/config_units");
	my @units = known_units(%cfg);
	my $num_rows = (scalar @units > 0) ? (scalar @units) + 3 : 5;
	my @rows = map ({ D => $cfg{$units[$_]}, C => $units[$_], A => !!($cfg{Commodities} =~ /(^|;)$units[$_]($|;)/), B => ($cfg{Anchor} eq $units[$_]), P => ($cfg{Default} eq $units[$_]), R => $_ }, 0 .. $#units);
	push (@rows, { D => '', C => '', B => 0, A => 0, P => 0, R => $_ }) foreach (scalar @units .. ($num_rows - 1));

	$tmpl->param(ROWS => \@rows);

	return $tmpl;
}

sub gen_edit_rates
{
	my $tmpl = load_template('edit_rates.html', $_[0]);

	my %cfg = date_sort_rates(read_units_cfg("$config{Root}/config_units.p1"));
	# note that similarly to gen_tg we don't validate here -- the form has to give the opportunity to correct invalid data
	# we make a best-efforts attempt to parse the file here, and display it, but ultimately if our parsing is shit
	# it doesn't matter, as it won't validate correctly when attempting to save

	my @units = known_units(%cfg);
	my %curs;
	$curs{$_} = 1 foreach (known_currs(%cfg));

	@units = grep ($_ ne $cfg{Anchor}, @units);	# exclude self-referencing rate henceforth

	my %in;
	foreach my $unit (@units) {
		$in{$unit} = $cfg{Anchor};
		my @try_in = grep (/\/$unit$/, @{$cfg{Headings}});
		next if scalar @try_in < 1;
		($in{$unit} = $try_in[0]) =~ s/\/.*//;
		$in{$unit} = undef unless exists $cfg{$in{$unit}};	# deal with disappearing denominators
	}

	my @heads;
	foreach my $unit (@units) {
		my @currencies = map ({ C => $_, S => $_ eq $in{$unit} }, keys %curs);
		push (@heads, { COMMOD => (not exists $curs{$unit}), ONECUR => (scalar keys %curs < 2), ANCHOR => $cfg{Anchor}, U => $unit, CURS => \@currencies });
	}
	$tmpl->param(HEADINGS => \@heads);

	my @blankrates = map ({ X => '', U => $_ }, @units);
	my @rows;
	if (exists $cfg{Date} and scalar @{$cfg{Date}}) {
		my $counter = 0;
		push (@rows, { DATE => '', R => $counter++, RATES => \@blankrates });
		foreach my $row (0 .. $#{$cfg{Date}}) {
			my @rates;
			foreach (@units) {
				my $str = (exists $curs{$_}) ? "$_/$in{$_}" : "$in{$_}/$_";
				push (@rates, { X => ((exists $cfg{$str}) ? $cfg{$str}[$row] : ''), U => $_ });
			}
			push (@rows, { DATE => $cfg{Date}[$row], R => $counter++, RATES => \@rates });
			push (@rows, { DATE => '', R => $counter++, RATES => \@blankrates });
		}
		push (@rows, { DATE => '', R => $counter++, RATES => \@blankrates });
	} else {
		@rows = map ({ DATE => '', R => $_, RATES => \@blankrates }, 0 .. 4);
	}
	$tmpl->param(ROWS => \@rows);

	return $tmpl;
}

sub unlock_dir
{
	my ($dir, $sessid, $whinge, $objective, $dir_what) = @_;

	if (scalar glob ("$config{Root}/$dir/.*.lock") && clear_locks("$config{Root}/$dir", $sessid)) {
		un_commit_lock;
		$whinge->("Cannot perform $objective at present: $dir_what busy");
	}

	return;
}

sub dir_mod_all
{
	my ($dir, $tg, $rename, $sub, $given_ts) = @_;

	foreach my $f (glob ("$config{Root}/$dir/*")) {
		next if $tg && $f =~ /\/[A-Z][^\/]*$/;	# skip auto gen TGs
		$f = untaint($f);
		my %htsv = $tg ? read_tg2($f) : read_htsv($f);

		foreach my $old (@$rename) {
			$sub->(\%htsv, $old);
		}

		$tg ? write_tg($f, %htsv) : write_htsv($f, \%htsv, $given_ts);
		$git->add($f);
	}
	return;
}

sub commit_config_units
{
	my ($whinge, $session, $etoken, $rename, $cfg) = @_;
	my $sessid = $session->id();
	my $cfg_file = "$config{Root}/config_units";

	$whinge->('Unable to get commit lock') unless try_commit_lock($sessid);
	if (keys %$rename) {
		unlock_dir('transaction_groups', $sessid, $whinge, 'unit recode', 'transaction groups');
		unlock_dir('event_types', $sessid, $whinge, 'unit recode', 'event types');
		unlock_dir('fee_tmpls', $sessid, $whinge, 'unit recode', 'fee templates');
		unlock_dir('events', $sessid, $whinge, 'unit recode', 'events');
		if (-e "$config{Root}/.config_fees.lock" && clear_lock("$config{Root}/.config_fees.lock", $sessid)) {
			un_commit_lock;
			$whinge->('Cannot perform unit recode at present: config_fees busy');
		}
	}
	bad_token_whinge(gen_tcp) unless redeem_edit_token($sessid, 'edit_units', $etoken);
	return try_commit_and_unlock(sub {
		my $commit_msg = 'config_units: units/rates modified';

		if (keys %$rename) {
			my @renames = keys %$rename;
			dir_mod_all('transaction_groups', 1, \@renames, sub { my ($tg, $old) = @_; foreach (@{$tg->{Currency}}) { s/^$old$/$rename->{$old}/ if $_; } });
			dir_mod_all('event_types', 0, \@renames, sub { my ($et, $old) = @_; foreach (@{$et->{Unit}}) { s/^$old$/$rename->{$old}/ if $_; } });
			dir_mod_all('fee_tmpls', 0, \@renames, sub { my ($ft, $old) = @_; foreach (@{$ft->{Unit}}) { s/^$old$/$rename->{$old}/ if $_; } });
			dir_mod_all('events', 0, \@renames, sub { my ($evnt, $old) = @_;
				$evnt->{Currency} =~ s/^$old$/$rename->{$old}/ if defined $evnt->{Currency};
				if (defined $evnt->{Headings}) {
					s/^$old$/$rename->{$old}/ foreach (@{$evnt->{Headings}});
				}
				$evnt->{$rename->{$old}} = delete $evnt->{$old} if exists $evnt->{$old}; }, 11);
			my %cf = read_htsv("$config{Root}/config_fees", 1);
			if (%cf && exists $cf{Fee}) {
				foreach my $old (keys %$rename) {
					foreach (@{$cf{Fee}}) {
						s/^$old$/$rename->{$old}/ if $_;
					}
				}

				write_htsv("$config{Root}/config_fees", \%cf, 11);
				$git->add("$config{Root}/config_fees");
			}
			$commit_msg .= ' AND RENAMED';
		}

		write_units_cfg($cfg_file, $cfg);
		add_commit($cfg_file, $commit_msg, $session);
		unlink "$cfg_file.p1" if -e "$cfg_file.p1";
		unlink "$cfg_file.rename" if -e "$cfg_file.rename";
	}, $cfg_file);
}

sub gen_manage_events
{
	my $session = $_[0];
	my $tmpl = load_template('manage_events.html', undef, $session);
	my %ppl = grep_acct_key('users', 'Name');
	my %cf = valid_fee_cfg;
	my @etfs = map { /.*\/([^\/]*)/; transcode_uri_for_html($1) } grep (!!valid_event_type($_, \%cf), glob ("$config{Root}/event_types/*"));
	my @ftfs = map { /.*\/([^\/]*)/; transcode_uri_for_html($1) } grep (!!valid_ft($_, \%cf), glob ("$config{Root}/fee_tmpls/*"));
	my %fts;
	@{$fts{$_}} = () foreach (@etfs, 'none');
	foreach (@ftfs) {
		if (/([^.]+)\.(.+)/) {
			push (@{$fts{$1}}, $2);
		} else {
			push (@{$fts{none}}, $_);
		}
	}
	push (@{$fts{$_}}, 'none') foreach (keys %fts);

	my @evlist;
	foreach my $mid (date_sorted_htsvs('events')) {
		my %evnt = %{$evs{$mid}};
		my $leader = (defined $evnt{Leader}) ? ((exists $ppl{$evnt{Leader}}) ? $ppl{$evnt{Leader}} : $evnt{Leader}) : '';
		$evnt{EventType} //= 'none';
		$evnt{Template} //= 'none';
		my $et_state = $evnt{EventType} eq 'none' || !!grep ($_ eq $evnt{EventType}, @etfs);
		my $ft_prefix = ($evnt{EventType} ne 'none') ? "$evnt{EventType}." : '';
		my $ft_state = $evnt{Template} eq 'none' || !!grep ($_ eq "$ft_prefix$evnt{Template}", @ftfs);
		my $ft_exists = $evnt{Template} ne 'none' && -r "$config{Root}/fee_tmpls/" . encode_for_filename("$ft_prefix$evnt{Template}");

		push (@evlist, { MID => $mid, NAME => $evnt{Name}, M_CL => (defined $evnt{Name} && event_valid(\%evnt, \%cf)) ? '' : 'broken', DATE => $evnt{Date}, D_CL => (defined clean_date($evnt{Date})) ? '' : 'broken', LEN => $evnt{Duration}, LEN_CL => (defined clean_int($evnt{Duration}) && clean_int($evnt{Duration}) > 0) ? '' : 'broken', LDR_CL => (defined $evnt{Leader} && exists $ppl{$evnt{Leader}}) ? '' : 'unknown', LEADER => $leader, FT_CL => ($et_state && $ft_state) ? '' : 'unknown', FT => format_ft_name("$ft_prefix$evnt{Template}"), FTID => ($session->param('IsAdmin') && $ft_exists) ? encode_for_filename("$ft_prefix$evnt{Template}") : '', LOCKED => (exists $evnt{Locked}) });
	}
	my @people = map ({ A => $_, N => $ppl{$_} }, sort_AoH(\%ppl));
	my @ftlist;
	foreach my $et (sort keys %fts) {
		push (@ftlist, map ({ FTID => $_, FT => format_ft_name($_) }, map ("$et.$_", @{$fts{$et}})));
	}

	$tmpl->param(EVENTS => \@evlist, PPL => \@people, FTS => \@ftlist, ADDDELOK => $session->param('MayStewardEvents'), LOCKOK => $session->param('IsAdmin'));

	return $tmpl;
}

sub format_et
{
	my $et = $_[0];

	return $et if defined $et && $et ne 'none';
	return 'Event';
}

sub event_edit_ok
{
	my ($evnt, $session, $steward) = @_;

	return 1 if $session->param('IsAdmin');
	return if exists $evnt->{Locked};

	return $session->param('MayStewardEvents') if $steward;
	return $session->param('User') eq $evnt->{Leader} && $session->param('MayEditOwnEvents');
}

sub gen_edit_event
{
	my ($edit_id, $cfr, $session, $etoken) = @_;

	my $tmpl = load_template('edit_event.html', $etoken, $session);
	my %evnt = read_htsv("$config{Root}/events/$edit_id", undef, [ 'Person', 'Notes' ]);

	$tmpl->param(ET => format_et($evnt{EventType}));
	$tmpl->param(MID => $edit_id);
	$tmpl->param(RO => !$etoken);
	$tmpl->param(NAME => $evnt{Name}, DATE => $evnt{Date}, DUR => $evnt{Duration});

	my %units_cfg = read_units_cfg("$config{Root}/config_units");
	my @units = known_units(%units_cfg);

	my $sel_cur = $units_cfg{Default};
	if (exists $evnt{Currency}) {
		$sel_cur = $evnt{Currency};
		if (@units) {
			$sel_cur = (scalar @units > 1) ? '' : $units_cfg{Default} unless defined $evnt{Currency};
		} else {
			push (@units, 'N/A') if defined $evnt{Currency};
		}
	}
	my $red_unit;

	if (defined $sel_cur && !grep ($_ eq $sel_cur, @units)) {
		$red_unit = 1;
		push (@units, $sel_cur);
	}

	my @currencies = map ({ C => $_, D => $units_cfg{$_}, S => $sel_cur eq $_ }, @units);
	$tmpl->param(CURS => \@currencies, CUR_CL => $red_unit ? 'unknown' : '');

	my %cf = %$cfr;
	my %cds = known_commod_descs;

	my %et;
	%et = valid_event_type("$config{Root}/event_types/" . encode_for_filename($evnt{EventType}), $cfr) if defined $evnt{EventType} && $evnt{EventType} ne 'none';
	my %drains = get_cf_drains(%cf);

	my (@ccs, @exps);
	my (%unusual, %dispt);
	if (%et) {
		my ($fee_rows, $exp_rows) = get_event_types(\%et, \%drains, 1);
		@ccs = map { my $fee = $_; (grep ($fee eq $cf{Fee}[$_], 0 .. $#{$cf{Fee}}))[0] } (map ($et{Unit}[$_], @$fee_rows));
		@exps = map { my $fee = $_; (grep ($fee eq $cf{Fee}[$_], 0 .. $#{$cf{Fee}}))[0] } (map ($et{Unit}[$_], @$exp_rows));
		$unusual{$et{Unit}[$_]} = 1 foreach (grep (true($et{Unusual}[$_]), (@$fee_rows, @$exp_rows)));
		$dispt{$et{Unit}[$_]} = $et{DispText}[$_] foreach (grep ($et{DispText}[$_] && length $et{DispText}[$_], (@$fee_rows, @$exp_rows)));
	} else {
		@ccs = grep (exists $cds{$cf{Fee}[$_]}, 0 .. $#{$cf{Fee}});
		push (@ccs, grep (!(exists $cds{$cf{Fee}[$_]}) && true($cf{IsDrain}[$_]), 0 .. $#{$cf{Fee}}));
		@exps = grep (!(exists $cds{$cf{Fee}[$_]} || true($cf{IsDrain}[$_])), 0 .. $#{$cf{Fee}});
	}
	my (@unks, %split_exp_sum, %split_shr_sum, %splits);
	foreach my $hd (grep (!/^(Person|CustomFee|Notes|Split[1-9](Exps|Shrs))$/, @{$evnt{Headings}})) {
		push (@unks, $hd) unless grep ($cf{Fee}[$_] eq $hd, (@ccs, @exps));
	}
	foreach my $hd (grep (/^Split[1-9](Exps|Shrs)$/, @{$evnt{Headings}})) {
		if ($hd =~ /Split([1-9])Exps/) {
			$split_exp_sum{$1} += $_ foreach (grep (CleanData::clean_decimal($_), @{$evnt{$hd}}));
			$splits{$1} = 1;
		}
		if ($hd =~ /Split([1-9])Shrs/) {
			$split_shr_sum{$1} += $_ foreach (grep (CleanData::clean_decimal($_), @{$evnt{$hd}}));
			$splits{$1} = 1;
		}
	}
	my $added_splts = 0;
	foreach (1 .. 9) {
		if ($etoken && !(exists $splits{$_})) {
			$splits{$_} = 1;
			$added_splts++;
			last if $added_splts == 2;
		}
	}

	my %rates;
	if (clean_date($evnt{Date})) {
		%rates = get_rates($evnt{Date});
	}

	my @feesh = ({ FEE => 'Custom Fee', LINKA => %et ? $et{LinkedAcct} : $cf{DefaultAccount} });
	push (@feesh, map ({ CDESC => (exists $rates{$cf{Fee}[$_]}) ? "$rates{$cf{Fee}[$_]} $units[0]" : '', FEE => (exists $dispt{$cf{Fee}[$_]}) ? $dispt{$cf{Fee}[$_]} : (exists $cds{$cf{Fee}[$_]}) ? ($cds{$cf{Fee}[$_]} // $cf{Fee}[$_]) : $cf{Description}[$_], LINKA => $cf{Account}[$_] }, @ccs));
	my @expsh = map ({ EXP => (exists $dispt{$cf{Fee}[$_]}) ? $dispt{$cf{Fee}[$_]} : $cf{Description}[$_], LINKA => $cf{Account}[$_] }, @exps);
	my @unksh = map ({ UNK => $_ }, @unks);
	my @splitsh = map ({ SPLIT => $_ }, sort keys %splits);
	$tmpl->param(NFEES => scalar @feesh, FEESH => \@feesh, NEXPS => scalar @expsh, EXPSH => \@expsh, NUNKS => scalar @unksh, UNKSH => \@unksh, NSPLITS => 2 * scalar @splitsh, SPLITSH => \@splitsh);

	my %ppl_seen;
	$ppl_seen{$evnt{Person}[$_]}++ foreach (grep (defined $evnt{Person}[$_], 0 .. $#{$evnt{Person}}));

	my %accts = grep_acct_key('users', 'Name');
	my %neg_accts = grep_acct_key('accounts', 'IsNegated');
	my %vaccts = grep_acct_key('accounts', 'Name');
	my (@ppl, @nas);
	foreach my $row (0 .. $#{$evnt{Person}}) {
		my @rfees = ({ F => 'Custom', V => $evnt{CustomFee}[$row] ? $evnt{CustomFee}[$row] : '', D_CL => (defined CleanData::clean_decimal($evnt{CustomFee}[$row])) ? '' : 'broken' });
		push (@rfees, map ({ F => $cf{Fee}[$_], V => ((exists $evnt{$cf{Fee}[$_]}) && $evnt{$cf{Fee}[$_]}[$row]) ? $evnt{$cf{Fee}[$_]}[$row] : '', BOOL => true($cf{IsBool}[$_]), D_CL => (!(exists $evnt{$cf{Fee}[$_]}) || (defined CleanData::clean_decimal($evnt{$cf{Fee}[$_]}[$row]))) ? '' : 'broken', EXCPT => (exists $unusual{$cf{Fee}[$_]}) }, (@ccs, @exps)));
		push (@rfees, map ({ F => $_, V => $evnt{$_}[$row], D_CL => 'unknown' }, @unks));
		my @rsplits = map ({ F => $_, EV => (exists $evnt{"Split${_}Exps"} && $evnt{"Split${_}Exps"}[$row]) ? $evnt{"Split${_}Exps"}[$row] : '', ED_CL => (!(exists $evnt{"Split${_}Exps"}) || (exists $evnt{"Split${_}Exps"} && defined CleanData::clean_decimal($evnt{"Split${_}Exps"}[$row]))) ? '' : 'broken', SV => (exists $evnt{"Split${_}Shrs"} && $evnt{"Split${_}Shrs"}[$row]) ? $evnt{"Split${_}Shrs"}[$row] : '', SD_CL => (exists $evnt{"Split${_}Shrs"} && (!(defined CleanData::clean_decimal($evnt{"Split${_}Shrs"}[$row])) || CleanData::clean_decimal($evnt{"Split${_}Shrs"}[$row]) < 0) || ($split_exp_sum{$_} && !$split_shr_sum{$_})) ? 'broken' : '' }, sort keys %splits);
		my $a = $evnt{Person}[$row] // '';
		(exists $neg_accts{$a}) ?
			push (@nas, { PER_CL => ((exists $neg_accts{$a}) ? 'negated' : 'unknown negated') . ((!(defined $ppl_seen{$a}) || $ppl_seen{$a} == 1) ? '' : ' dup'), NAME => (exists $vaccts{$a}) ? $vaccts{$a} : $a, A => $a, FEES => \@rfees, SPLITS => \@rsplits, NOTEV => $evnt{Notes}[$row] }) :
			push (@ppl, { PER_CL => ((exists $accts{$a}) ? '' : 'unknown') . ((!(defined $ppl_seen{$a}) || $ppl_seen{$a} == 1) ? '' : ' dup'), NAME => (exists $accts{$a}) ? $accts{$a} : $a, A => $a, FEES => \@rfees, SPLITS => \@rsplits, NOTEV => $evnt{Notes}[$row] });
	}
	@ppl = (@ppl, @nas);
	my @splitds = map ({ SPLIT => $_, SPLITD => $evnt{"Split${_}Desc"}, DD_CL => (!$split_exp_sum{$_} || $evnt{"Split${_}Desc"}) ? '' : 'broken' }, sort keys %splits);
	$tmpl->param(PPL => \@ppl);
	$tmpl->param(SPLITDS => \@splitds);
	$tmpl->param(FILLEDSPLITS => scalar @splitsh - $added_splts);
	$tmpl->param(EDITOK => event_edit_ok(\%evnt, $session));
	$tmpl->param(EDITHDRS => event_edit_ok(\%evnt, $session, 1));
	$tmpl->param(VALID => event_valid(\%evnt, $cfr));

	return $tmpl;
}

sub mru_event_accts
{
	my ($thresh) = @_;
#	my ($et, $max_delta) = @_;

	my %accts;

	foreach my $mid (reverse date_sorted_htsvs('events')) {
		last if defined clean_date($evs{$mid}->{Date}) && clean_date($evs{$mid}->{Date}) < $thresh;
#		next unless !(defined $et) || (defined $evnt{EventType} && $et eq $evnt{EventType});
		$accts{$_} = 1 foreach (@{$evs{$mid}->{Person}});
	}

	return %accts;
}

sub gen_edit_event_ppl
{
	my ($edit_id, $sessid, $etoken) = @_;

	my $tmpl = load_template('edit_event_ppl.html', $etoken);
	my %evnt = read_htsv("$config{Root}/events/$edit_id", undef, [ 'Person', 'Notes' ]);

	my %accts = grep_acct_key('users', 'Name');
	my %vaccts = grep_acct_key('accounts', 'Name');
	my %neg_accts = grep_acct_key('accounts', 'IsNegated');
	my @unks = grep (!(exists $accts{$_} || exists $neg_accts{$_}), map ($_ // '', @{$evnt{Person}}));

	my %ppl_seen;
	$ppl_seen{$evnt{Person}[$_]}++ foreach (grep (defined $evnt{Person}[$_], 0 .. $#{$evnt{Person}}));

	my $adds = peek_session_data($sessid, "${etoken}_add_accts");
	my @adds = split ('\.', $adds) if $adds;

	my %try;
	%try = mru_event_accts(clean_date($evnt{Date}) - ($config{EvMRUPeriod} * 86400)) if $config{EvMRUPeriod};	# 86400 is days to seconds
	my @rppl;
	foreach my $user (grep { my $u = $_; exists $try{$u} || grep ($_ eq $u, @adds) } sort_AoH(\%accts)) {
		$ppl_seen{$user} = 0 unless exists $ppl_seen{$user};
		my @dups = map ({ A => "$user.$_" }, 2 .. $ppl_seen{$user});
		push (@rppl, { NAME => $accts{$user}, A => $user, Y => (grep ($_ eq $user, @adds) || !!grep ($_ eq $user, grep (defined, @{$evnt{Person}}))), DUPS => \@dups, P_CL => ($ppl_seen{$user} > 1) ? 'dup' : '' });
	}
	push (@rppl, { NAME => $_, A => $_, Y => 1, P_CL => ($ppl_seen{$_} && $ppl_seen{$_} > 1) ? 'unknown dup' : 'unknown' }) foreach (@unks);

	my @ppl;
	foreach my $user (grep { my $u = $_; !(exists $try{$u} || grep ($_ eq $u, @adds)) } sort_AoH(\%accts)) {
		$ppl_seen{$user} = 0 unless exists $ppl_seen{$user};
		my @dups = map ({ A => "$user.$_" }, 2 .. $ppl_seen{$user});
		push (@ppl, { NAME => $accts{$user}, A => $user, Y => (grep ($_ eq $user, @adds) || !!grep ($_ eq $user, grep (defined, @{$evnt{Person}}))), DUPS => \@dups, P_CL => ($ppl_seen{$user} > 1) ? 'dup' : '' });
	}
	push (@ppl, { NAME => $_, A => $_, Y => 1, P_CL => ($ppl_seen{$_} && $ppl_seen{$_} > 1) ? 'unknown dup' : 'unknown' }) foreach (@unks);

	my @negs;
	foreach my $na (grep (exists $neg_accts{$_}, sort_AoH(\%vaccts))) {
		$ppl_seen{$na} = 0 unless exists $ppl_seen{$na};
		my @dups = map ({ A => "$na.$_" }, 2 .. $ppl_seen{$na});
		push (@negs, { NAME => $vaccts{$na}, A => $na, Y => !!grep ($_ eq $na, grep (defined, @{$evnt{Person}})), DUPS => \@dups, P_CL => ($ppl_seen{$na} > 1) ? 'dup' : '' });
	}

	$tmpl->param(ET => format_et($evnt{EventType}));
	$tmpl->param(MID => $edit_id);
	$tmpl->param(NAME => $evnt{Name}, PPL => \@ppl, NEGS => \@negs, DUPTEXT => !!grep ($_ > 1, values %ppl_seen));
	$tmpl->param(RPPL => \@rppl) if @rppl;

	return $tmpl;
}

sub gen_edit_event_hdrs
{
	my ($edit_id, $cfr, $etoken) = @_;

	my $tmpl = load_template('edit_event_hdrs.html', $etoken);
	my %evnt = read_htsv("$config{Root}/events/$edit_id", undef, [ 'Person', 'Notes' ]);

	my %ppl = grep_acct_key('users', 'Name');
	my @people = map ({ A => $_, N => $ppl{$_}, S => (defined $evnt{Leader} && $_ eq $evnt{Leader}) }, sort_AoH(\%ppl));
	unless (defined $evnt{Leader} && exists $ppl{$evnt{Leader}}) {
		$evnt{Leader} //= '';
		push (@people, { A => $evnt{Leader}, N => $evnt{Leader}, S => 1 });
	}

	my @etfs = map { /.*\/([^\/]*)/; transcode_uri_for_html($1) } grep (!!valid_event_type($_, $cfr), glob ("$config{Root}/event_types/*"));
	my @ftfs = map { /.*\/([^\/]*)/; transcode_uri_for_html($1) } grep (!!valid_ft($_, $cfr), glob ("$config{Root}/fee_tmpls/*"));
	my %fts;
	@{$fts{$_}} = () foreach (@etfs, 'none');
	foreach (@ftfs) {
		if (/([^.]+)\.(.+)/) {
			push (@{$fts{$1}}, $2);
		} else {
			push (@{$fts{none}}, $_);
		}
	}
	push (@{$fts{$_}}, 'none') foreach (keys %fts);
	$evnt{EventType} //= 'none';
	$evnt{Template} //= 'none';
	my $et_state = $evnt{EventType} eq 'none' || !!grep ($_ eq $evnt{EventType}, @etfs);
	my $ft_prefix = ($evnt{EventType} ne 'none') ? "$evnt{EventType}." : '';
	my $ft_state = $evnt{Template} eq 'none' || !!grep ($_ eq "$ft_prefix$evnt{Template}", @ftfs);
	my @ftlist;
	foreach my $et (sort keys %fts) {
		push (@ftlist, map ({ FTID => $_, FT => format_ft_name($_), S => ("$evnt{EventType}.$evnt{Template}" eq $_) }, map ("$et.$_", @{$fts{$et}})));
	}
	push (@ftlist, { FTID => "$ft_prefix$evnt{Template}", FT => format_ft_name("$ft_prefix$evnt{Template}"), S => 1 }) unless $et_state && $ft_state;

	$tmpl->param(MID => $edit_id, NAME => $evnt{Name}, N_CL => (defined $evnt{Name}) ? '' : 'broken', DATE => $evnt{Date}, D_CL => (defined clean_date($evnt{Date})) ? '' : 'broken', DUR => $evnt{Duration}, DUR_CL => (defined clean_int($evnt{Duration}) && clean_int($evnt{Duration}) > 0) ? '' : 'broken', PPL => \@people, LDR_CL => (exists $ppl{$evnt{Leader}}) ? '' : 'unknown', FTS => \@ftlist, FT_CL => ($et_state && $ft_state) ? '' : 'unknown');

	return $tmpl;
}

sub event_to_tg
{
	my %evnt = @_;
	my %tg = ( Date => $evnt{Date}, Name => format_et($evnt{EventType}) . ': ' . ($evnt{Name} // '') );
	my %colsum;

	my %cf = read_htsv("$config{Root}/config_fees", 1);
	my %et = valid_event_type("$config{Root}/event_types/" . encode_for_filename($evnt{EventType}), \%cf) if defined $evnt{EventType} && $evnt{EventType} ne 'none';
	my $def_acct = %et ? $et{LinkedAcct} : $cf{DefaultAccount};

	unless (defined $def_acct && event_valid(\%evnt, \%cf, 1)) {
		$tg{Date} = 'now';
		$tg{Name} .= ' (broken)';
		$tg{Omit} = undef;
		return %tg;
	}

	foreach my $row (0 .. $#{$evnt{Person}}) {
		$evnt{Person}[$row] //= '';
		$colsum{$_} += $evnt{$_}[$row] foreach (grep (!/^(Person|Notes)$/, @{$evnt{Headings}}));
	}
	foreach my $row (0 .. $#{$evnt{Person}}) {
		foreach (grep ($colsum{$_} && !($_ =~ /^Split[1-9]Exps$/), @{$evnt{Headings}})) {
			next if $_ =~ /^Split([1-9])Shrs$/ && !(exists $evnt{"Split$1Exps"});
			push (@{$tg{$evnt{Person}[$row]}}, $evnt{$_}[$row]);
		}
	}

	my @units = known_units;
	my %cds = known_commod_descs;

	foreach my $hd (@{$evnt{Headings}}) {
		next if ($hd eq 'Person' || $hd eq 'Notes');
		next unless $colsum{$hd};
		if (grep ($_ eq $hd, grep (defined, @{$cf{Fee}}))) {
			my $mc_row = first { $cf{Fee}[$_] eq $hd } 0 .. $#{$cf{Fee}};
			push (@{$tg{Creditor}}, $cf{Account}[$mc_row]);
			if (exists $cds{$hd}) {
				push (@{$tg{Amount}}, $colsum{$hd});
				push (@{$tg{Currency}}, $hd);
				push (@{$tg{Description}}, ($cds{$hd} // $hd));
			} elsif (true($cf{IsDrain}[$mc_row])) {
				push (@{$tg{Amount}}, '*');
				push (@{$tg{Currency}}, '');
				push (@{$tg{Description}}, $cf{Description}[$mc_row]);
			} else {
				push (@{$tg{Amount}}, -$colsum{$hd});
				push (@{$tg{Currency}}, $evnt{Currency}) if scalar @units;
				push (@{$tg{Description}}, $cf{Description}[$mc_row]);
			}
		} elsif ($hd eq 'CustomFee') {
			push (@{$tg{Creditor}}, $def_acct);
			push (@{$tg{Amount}}, $colsum{CustomFee});
			push (@{$tg{Currency}}, $evnt{Currency}) if scalar @units;
			push (@{$tg{Description}}, 'Event fee');
		} elsif ($hd =~ /^Split([1-9])Exps$/) {
			my $creds = 0;
			$creds++ foreach (grep ($evnt{$hd}[$_], 0 .. $#{$evnt{$hd}}));

			my $split_desc = $evnt{"Split$1Desc"};
			push (@{$tg{Description}}, "Split: $split_desc");
			if ($creds > 1) {
				my $off = push (@{$tg{Creditor}}, "TrnsfrPot$1");
				push (@{$tg{Amount}}, '*');
				push (@{$tg{Currency}}, '') if scalar @units;
				splice (@{$tg{$_}}, $off, 0, (0) x $creds) foreach (@{$evnt{Person}});
				$tg{TrnsfrPot}[$_] = $1 foreach ($off .. ($off + $creds - 1));
				push (@{$tg{Description}}, ('"') x $creds);
			}

			foreach (grep ($evnt{"Split$1Exps"}[$_], 0 .. $#{$evnt{"Split$1Exps"}})) {
				push (@{$tg{Creditor}}, $evnt{Person}[$_]);
				push (@{$tg{Amount}}, $evnt{"Split$1Exps"}[$_]);
				push (@{$tg{Currency}}, $evnt{Currency}) if scalar @units;
			}
		}
	}

	@{$tg{Headings}} = ( 'Creditor', 'Amount', @{$evnt{Person}}, 'Description' );
	splice (@{$tg{Headings}}, 2, 0, 'TrnsfrPot') if exists $tg{TrnsfrPot};
	splice (@{$tg{Headings}}, 2, 0, 'Currency') if exists $tg{Currency};

	return %tg;
}

sub valid_edit_id
{
	my ($id, $path, $type, $whinge, $id_required) = @_;

	$whinge->("No $type ID defined") if $id_required && !(defined $id);

	my $edit_id = transcode_uri_for_html(clean_filename(encode_for_filename($id), $path));

	$whinge->("No such $type \"$id\"") if (defined $id || $id_required) && !$edit_id;

	return $edit_id;
}

sub get_rows
{
	my ($max, $cgi, $prefix, $whinge) = @_;

	my $max_rows = -1;
	$max_rows++ while ($max_rows < $max && defined $cgi->param($prefix . ($max_rows + 1)));
	$whinge->() unless $max_rows >= 0;

	return $max_rows;
}

sub delete_common
{
	my ($file, $thing, $session, $done, $extra_file) = @_;

	whinge("Couldn't get lock for $thing", $done->()) unless try_lock($file, $session->id());
	unless (-r $file) {
		unlock($file);
		emit_with_status(ucfirst $thing . ' already deleted', $done->());
	}
	unless (try_commit_lock($session->id())) {
		unlock($file);
		whinge('Unable to get commit lock', $done->());
	}
	try_commit_and_unlock(sub {
		$git->rm($file);
		$git->rm($extra_file) if $extra_file && -r $extra_file;
		commit(unroot($file) . ': deleted', $session);
	}, $file);
	return emit_with_status("Deleted $thing", $done->());
}

sub mail
{
	my ($to, $subj, $text) = @_;

	return undef unless $config{email} && $config{Relay};
	local ($Text::Wrap::columns) = 72;
	local ($Text::Wrap::huge) = 'overflow';

	my $msg = MIME::Lite->new(
		From	=> $config{email},
		To	=> $to,
		Subject	=> $subj,
		Data	=> wrap('', '', $text)
	);

	($config{Relay} eq 'sendmail') ? $msg->send : $msg->send('smtp', $config{Relay});

	return $msg->last_send_successful;
}

sub mail_password
{
	my ($acct, $plain, $url) = @_;

	my %acct = read_simp_cfg("$config{Root}/users/$acct");

	my $tmpl = load_email_template('new_password.eml', $url);
	$tmpl->param(NAME => $acct{Name}, PW => $plain, USER => $acct);

	return mail($acct{email}, "New $config{ShortName} password for $acct", $tmpl->output);
}

sub lock_or_whinge
{
	my ($file, $thing, $session, $bail, $action, $etkey) = @_;

	my $break = grep ("force_$action" eq $_, $session->query()->param);
	my $rv = try_lock($file, $session->id(), $break);
	pop_session_data($session->id(), $etkey ? $etkey : $action) if $rv && $break;
	return if $rv;

	whinge(ucfirst $thing . ' is being edited by another user session', $bail->()) unless defined $rv;

	my $tmpl = $bail->();
	$tmpl->param(BREAKLOCK => "force_$action");
	whinge("You are already editing $thing!", $tmpl);
}

sub despatch_admin
{
	my $session = $_[0];
	my $sessid = $session->id();
	my $cgi = $session->query();
	my $etoken = $cgi->param('etoken');

	emit(gen_tcp) if defined $cgi->param('to_cp');

	if ($cgi->param('tmpl') eq 'tcp') {
		emit(gen_manage_accts(1)) if (defined $cgi->param('view_ppl'));
		emit(gen_manage_accts(0)) if (defined $cgi->param('view_accts'));
		if (grep (/^(force_)?edit_addr_alts$/, $cgi->param)) {
			lock_or_whinge("$config{Root}/config_addr_alts", 'configuration file "config_addr_alts"', $session, sub { gen_tcp }, 'edit_addr_alts');
			emit(gen_edit_addr_alts(get_edit_token($sessid, 'edit_addr_alts')));
		}
		if (grep (/^(force_)?edit_inst_cfg$/, $cgi->param)) {
			lock_or_whinge("$config{Root}/config", 'configuration file "config"', $session, sub { gen_tcp }, 'edit_inst_cfg');
			emit(gen_edit_inst_cfg(get_edit_token($sessid, 'edit_inst_cfg')));
		}
		emit(gen_manage_event_types) if (defined $cgi->param('manage_event_types'));
		emit(gen_manage_fee_tmpls) if (defined $cgi->param('manage_fee_tmpls'));
		if (grep (/^(force_)?edit_fee_cfg$/, $cgi->param)) {
			lock_or_whinge("$config{Root}/config_fees", 'configuration file "config_fees"', $session, sub { gen_tcp }, 'edit_fee_cfg');
			emit(gen_edit_fee_cfg(get_edit_token($sessid, 'edit_fee_cfg')));
		}
		if (grep (/^(force_)?edit_pers_attrs$/, $cgi->param)) {
			lock_or_whinge("$config{Root}/config_pers_attrs", 'configuration file "config_pers_attrs"', $session, sub { gen_tcp }, 'edit_pers_attrs');
			emit(gen_edit_pers_attrs(get_edit_token($sessid, 'edit_pers_attrs')));
		}
		if (grep (/^(force_)?edit_attr_groups$/, $cgi->param)) {
			lock_or_whinge("$config{Root}/config_pers_attrs", 'configuration file "config_pers_attrs"', $session, sub { gen_tcp }, 'edit_attr_groups');
			emit(gen_edit_attr_groups(get_edit_token($sessid, 'edit_attr_groups')));
		}
		if (grep (/^(force_)?edit_units$/, $cgi->param)) {
			lock_or_whinge("$config{Root}/config_units", 'configuration file "config_units"', $session, sub { gen_tcp }, 'edit_units');
			emit(gen_edit_units(get_edit_token($sessid, 'edit_units')));
		}
	}
	if ($cgi->param('tmpl') eq 'view_ppl' or $cgi->param('tmpl') eq 'view_vaccts') {
		my $acct;
		my ($delete, $cpw, $spw) = (0) x 3;
		my $person = $cgi->param('tmpl') eq 'view_ppl';
		my $whinge = sub { whinge($_[0], gen_manage_accts($person)) };

		my $p;
		foreach ($cgi->param) {
			if (/^(force_)?edit_(.+)$/) {
				$acct = $2;
			}
			if (/^del_(.+)$/) {
				$acct = $1;
				$delete = 1;
			}
			if (/^(force_)?clearpw_(.+)$/) {
				$acct = $2;
				$cpw = 1;
			}
			if (/^(force_)?setpw_(.+)$/) {
				$acct = $2;
				$spw = 1;
			}
			if ($acct) {
				($p = $_) =~ s/^force_//;
				last;
			}
		}

		$acct = valid_edit_id($acct, $person ? "$config{Root}/users" : "$config{Root}/accounts", 'account', $whinge);
		my $acct_file = $person ? "$config{Root}/users/$acct" : "$config{Root}/accounts/$acct" if $acct;
		unless ($delete) {
			if ($acct) {
				lock_or_whinge($acct_file, "account \"$acct\"", $session, sub { gen_manage_accts($person) }, $p, "edit_$acct");
				unless (-r $acct_file) {
					unlock($acct_file);
					$whinge->("Couldn't edit account \"$acct\", file disappeared");
				}
				if ($cpw || $spw) {
					my %acct = read_simp_cfg($acct_file);
					my $mail_ret = '';

					if ($spw) {
						my $plain = Text::Password::Pronounceable->generate(8, 12);
						$acct{Password} = unix_md5_crypt($plain);
						$mail_ret = '(email failed -- check settings)' unless mail_password($acct, $plain, $cgi->url);
					} else {
						delete $acct{Password};
					}

					$whinge->('Unable to get commit lock') unless try_commit_lock($sessid);
					try_commit_and_unlock(sub {
						write_simp_cfg($acct_file, %acct);
						add_commit($acct_file, unroot($acct_file) . ': password ' . ($cpw ? 'cleared' : 'set'), $session);
					}, $acct_file);
					emit_with_status("Password for account \"$acct\" " . ($cpw ? 'cleared' : "set $mail_ret"), gen_manage_accts($person));
				}
			}
			$etoken = get_edit_token($sessid, $acct ? "edit_$acct" : $person ? 'add_acct' : 'add_vacct');
			emit(gen_add_edit_acc($acct, $person, $session, $etoken));
		} else {
			delete_common($acct_file, "account \"$acct\"", $session, sub { gen_manage_accts($person) });
		}
	}
	if ($cgi->param('tmpl') eq 'edit_addr_alts') {
		my $cfg_file = "$config{Root}/config_addr_alts";

		if (defined $cgi->param('save')) {
			my %cfg;
			my $whinge = sub { whinge($_[0], gen_edit_addr_alts($etoken)) };

			foreach my $col (0 .. get_rows(10, $cgi, 'Type_', sub { $whinge->('No types?') })) {
				next unless length $cgi->param("Type_$col");

				my $type = clean_word($cgi->param("Type_$col"));
				$whinge->('Bad type "' . $cgi->param("Type_$col") . '"') unless defined $type && length $type;

				foreach my $row (0 .. get_rows(50, $cgi, "Opt_${col}_", sub { $whinge->("No options for \"$type\"?") })) {
					next unless length $cgi->param("Opt_${col}_$row");

					my $opt = clean_words($cgi->param("Opt_${col}_$row"));
					$whinge->('Bad option "' . $cgi->param("Opt_${col}_$row") . '"') unless defined $opt && length $opt;

					push (@{$cfg{$type}}, $opt);
				}
			}

			@{$cfg{Headings}} = keys %cfg;

			$whinge->('Unable to get commit lock') unless try_commit_lock($sessid);
			bad_token_whinge(gen_tcp) unless redeem_edit_token($sessid, 'edit_addr_alts', $etoken);
			try_commit_and_unlock(sub {
				write_htsv($cfg_file, \%cfg, 21);
				add_commit($cfg_file, 'config_addr_alts: address alternatives configuration modified', $session);
			}, $cfg_file);
		} else {
			unlock($cfg_file) if redeem_edit_token($sessid, 'edit_addr_alts', $etoken);
		}

		emit_with_status((defined $cgi->param('save')) ? 'Saved edits to address alternatives config' : 'Edit address alternatives config cancelled', gen_tcp);
	}
	if ($cgi->param('tmpl') eq 'manage_events') {
		my $whinge = sub { whinge($_[0], gen_manage_events($session)) };
		if (((grep (/^(force_)?lock_.+$/, $cgi->param))[0] // '') =~ /^(force_)?lock_(.+)$/) {
			my $mid = valid_edit_id($2, "$config{Root}/events", 'event', $whinge, 1);
			my $mt_file = "$config{Root}/events/$mid";
			lock_or_whinge($mt_file, "event \"$mid\"", $session, sub { gen_manage_events($session) }, "lock_$mid", "edit_$mid");
			my %evnt = read_htsv($mt_file, undef, [ 'Person', 'Notes' ]);
			(exists $evnt{Locked}) ? delete $evnt{Locked} : ($evnt{Locked} = undef);
			$whinge->('Unable to get commit lock') unless try_commit_lock($sessid);
			try_commit_and_unlock(sub {
				write_htsv($mt_file, \%evnt, 11);
				my @split_mf = split('-', unroot($mt_file));
				add_commit($mt_file, "$split_mf[0]...: Event \"$evnt{Name}\" " . ((exists $evnt{Locked}) ? 'locked' : 'unlocked'), $session);
			}, $mt_file);
			emit_with_status("Event \"$evnt{Name}\" " . ((exists $evnt{Locked}) ? 'locked' : 'unlocked'), gen_manage_events($session));
		}
	}
	if ($cgi->param('tmpl') eq 'edit_inst_cfg') {
		my $cfg_file = "$config{Root}/config";

		if (defined $cgi->param('save')) {
			my %inst_cfg;

			foreach my $param ($cgi->param()) {
				next if ($param eq 'tmpl' or $param eq 'etoken' or $param eq 'save');
				$inst_cfg{$param} = clean_words($cgi->param($param));
			}

			whinge('Unable to get commit lock', gen_edit_inst_cfg($etoken)) unless try_commit_lock($sessid);
			bad_token_whinge(gen_tcp) unless redeem_edit_token($sessid, 'edit_inst_cfg', $etoken);
			try_commit_and_unlock(sub {
				write_simp_cfg($cfg_file, %inst_cfg);
				add_commit($cfg_file, 'config: installation config modified', $session);
			}, $cfg_file);
			update_global_config(%inst_cfg);
		} else {
			unlock($cfg_file) if redeem_edit_token($sessid, 'edit_inst_cfg', $etoken);
		}

		emit_with_status((defined $cgi->param('save')) ? 'Saved edits to installation config' : 'Edit installation config cancelled', gen_tcp);
	}
	if ($cgi->param('tmpl') eq 'manage_event_types') {
		my $et;
		my $delete = 0;
		my $whinge = sub { whinge($_[0], gen_manage_event_types) };

		foreach ($cgi->param) {
			if (/^(force_)?edit_(.+)$/) {
				$et = $2;
				last;
			}
			if (/^del_(.+)$/) {
				$et = $1;
				$delete = 1;
				last;
			}
		}

		$et = valid_edit_id($et, "$config{Root}/event_types", 'event type', $whinge);
		my $et_file = "$config{Root}/event_types/$et" if $et;
		unless ($delete) {
			if ($et) {
				lock_or_whinge($et_file, "event type \"$et\"", $session, sub { gen_manage_event_types }, "edit_$et");
				unless (-r $et_file) {
					unlock($et_file);
					$whinge->("Couldn't edit event type \"$et\", file disappeared");
				}
			}
			$etoken = get_edit_token($sessid, $et ? "edit_$et" : 'add_et');
			emit(gen_edit_et($et, $etoken));
		} else {
			delete_common($et_file, "event type \"$et\"", $session, sub { gen_manage_event_types });
		}
	}
	if ($cgi->param('tmpl') eq 'edit_event_type') {
		my $whinge = sub { whinge($_[0], gen_manage_event_types) };

		my $edit_id = valid_edit_id(scalar $cgi->param('et_id'), "$config{Root}/event_types", 'event type', $whinge);
		my $file = $edit_id ? "$config{Root}/event_types/" . encode_for_filename($edit_id) : undef;

		# only left with save and cancel now
		my $new_id = clean_words($cgi->param('name'));

		if (defined $cgi->param('save')) {
			my %et;
			$whinge = sub { whinge($_[0], gen_edit_et($edit_id, $etoken)) };

			$whinge->('Missing event type name') unless $new_id;
			$whinge->('"none" is a reserved type') if $new_id eq 'none';
			$whinge->('Type cannot contain \'.\'') if $new_id =~ /[.]/;
			my $old_file = $file;
			$file = "$config{Root}/event_types/" . encode_for_filename($new_id);
			my $rename = ($edit_id && $edit_id ne encode_for_html($new_id));
			$whinge->('Event type is already in use') if (-e $file && (!(defined $edit_id) || $rename));

			my %vaccts = grep_acct_key('accounts', 'Name');
			$whinge->('Missing account name') unless clean_username($cgi->param('DefAcct'));
			$et{LinkedAcct} = validate_acct(scalar $cgi->param('DefAcct'), \%vaccts, $whinge);

			my %cf = valid_fee_cfg;

			foreach my $row (0 .. get_rows(30, $cgi, 'Col_', sub { $whinge->('No columns?') })) {
				my $cur = $cgi->param("Unit_$row");
				my $col = validate_int(scalar $cgi->param("Col_$row"), 'Column ordering', undef, $whinge);
				next if $col < 0;

				$whinge->('Missing unit') unless defined $cur;
				if ($cur =~ /[A-Z]/) {
					$whinge->("Commodity \"$cur\" unknown to config_fees") unless grep ($_ eq $cur, @{$cf{Fee}});
				} else {
					$whinge->("Unknown drain/expense \"$cur\"") unless grep ($_ eq $cur, @{$cf{Fee}});
				}

				push (@{$et{Unit}}, $cur);
				push (@{$et{Column}}, $col);
				push (@{$et{Unusual}}, (defined $cgi->param("Ex_$row")));
				push (@{$et{DispText}}, $cgi->param("Disp_$row"));
			}

			@{$et{Headings}} = ( 'Unit', 'Column', 'Unusual', 'DispText' ) if exists $et{Unit};

			$whinge->('Unable to get commit lock') unless try_commit_lock($sessid);
			if ($rename) {
				unlock_dir('fee_tmpls', $sessid, $whinge, 'ET rename', 'fee templates');
				unlock_dir('events', $sessid, $whinge, 'ET rename', 'events');
			}
			bad_token_whinge(gen_manage_event_types) unless redeem_edit_token($sessid, $edit_id ? "edit_$edit_id" : 'add_et', $etoken);
			try_commit_and_unlock(sub {
				if ($rename) {
					(my $from = $old_file) =~ s/event_types/fee_tmpls/;
					(my $to = $file) =~ s/event_types/fee_tmpls/;
					foreach my $ft (grep (/$from\..+/, glob ("$config{Root}/fee_tmpls/*"))) {
						$ft = untaint($ft);
						(my $ft_id = $ft) =~ s/$from\.//;
						$git->mv($ft, "$to.$ft_id");
					}
					dir_mod_all('events', 0, [ $edit_id ], sub { my ($evnt, $old) = @_; $evnt->{EventType} =~ s/^$old$/$new_id/ if defined $evnt->{EventType} }, 11);
					$git->mv($old_file, $file);
				}
				(mkdir "$config{Root}/event_types" or die) unless (-d "$config{Root}/event_types");
				write_htsv($file, \%et);
				if ($rename) {
					add_commit($file, 'Rename ET ' . unroot($old_file) . ' to ' . unroot($file), $session);
				} else {
					add_commit($file, unroot($file) . ": ET \"$new_id\" " . ($edit_id ? 'modified' : 'created'), $session);
				}
			}, $rename ? $old_file : ($edit_id) ? $file : undef);
		} else {
			unlock($file) if redeem_edit_token($sessid, $edit_id ? "edit_$edit_id" : 'add_et', $etoken) && $file;
		}

		if ($edit_id) {
			emit_with_status((defined $cgi->param('save')) ? "Saved edits to \"$new_id\" event type" : 'Edit cancelled', gen_manage_event_types);
		} else {
			emit_with_status((defined $cgi->param('save')) ? "Added event type \"$new_id\"" : 'Add event type cancelled', gen_manage_event_types);
		}
	}
	if ($cgi->param('tmpl') eq 'manage_fee_tmpls') {
		if (defined $cgi->param('view') || defined $cgi->param('add')) {
			my $whinge = sub { whinge($_[0], gen_manage_fee_tmpls) };
			my $view = valid_edit_id(scalar $cgi->param('view'), "$config{Root}/fee_tmpls", 'fee template', $whinge);
			my $et_id;
			if (defined $cgi->param('view')) {
				if ($view =~ /^([^\/.]+)\.[^\/]+$/) {
					$et_id = $1;
				}
			} else {
				$et_id = ($cgi->param('event_type') eq 'none') ? undef : valid_edit_id(scalar $cgi->param('event_type'), "$config{Root}/event_types", 'event type', $whinge, 1);
			}

			my %et = $et_id ? valid_event_type("$config{Root}/event_types/$et_id", \%{{valid_fee_cfg}}) : ();
			$whinge->('Cannot ' . ((defined $cgi->param('view')) ? 'view' : 'add') . ' fee template: associated event type is broken') unless %et || !$et_id;
			emit(gen_edit_fee_tmpl($view, $view ? undef : get_edit_token($sessid, 'add_ft'), $et_id, \%et));
		}
	}
	if ($cgi->param('tmpl') eq 'edit_fee_tmpl' || ($cgi->param('tmpl') eq 'manage_fee_tmpls' && grep (/^force_edit_.+/, $cgi->param))) {
		emit(gen_manage_fee_tmpls) if (defined $cgi->param('manage_fee_tmpls'));
		my $whinge = sub { whinge($_[0], gen_manage_fee_tmpls) };
		my $is_edit = $cgi->param('tmpl') eq 'manage_fee_tmpls' || defined $cgi->param('edit');

		my $ft_id = $cgi->param('ft_id');
		($ft_id = (grep (/^force_edit_.+/, $cgi->param))[0]) =~ s/^force_edit_// if $cgi->param('tmpl') eq 'manage_fee_tmpls';
		my $edit_id = valid_edit_id($ft_id, "$config{Root}/fee_tmpls", 'fee template', $whinge, $is_edit);

		my $et_id = $cgi->param('event_type') ? valid_edit_id(scalar $cgi->param('event_type'), "$config{Root}/event_types", 'event type', $whinge, 1) : undef;
		$et_id = $1 if $is_edit && !$et_id && $ft_id =~ /^([^\/.]+)\.[^\/]+$/;

		my %cf = valid_fee_cfg;
		my %et = $et_id ? valid_event_type("$config{Root}/event_types/$et_id", \%cf) : ();
		my $file = $edit_id ? "$config{Root}/fee_tmpls/" . encode_for_filename($edit_id) : undef;

		if ($is_edit) {
			lock_or_whinge($file, "fee template \"$edit_id\"", $session, sub { gen_manage_fee_tmpls }, "edit_$edit_id");
			unless (-r $file) {
				unlock($file);
				$whinge->("Couldn't edit fee template \"$edit_id\", file disappeared");
			}
			$whinge->('Cannot edit fee template: associated event type is broken') unless %et || !$et_id;
			emit(gen_edit_fee_tmpl($edit_id, get_edit_token($sessid, "edit_$edit_id"), $et_id, \%et));
		}

		# only left with save and cancel now
		my $new_id = ($et_id ? "$et_id." : '') . (clean_words($cgi->param('name')) // '');

		if (defined $cgi->param('save')) {
			$whinge->('Cannot save fee template: associated event type is broken') unless %et || !$et_id;
			my %ft;
			$whinge = sub { whinge($_[0], gen_edit_fee_tmpl($edit_id, $etoken, $et_id, \%et)) };

			my $new_ft_id = clean_words($cgi->param('name'));
			$whinge->('Missing fee template name') unless $new_ft_id;
			$whinge->('"none" is a reserved name') if $new_ft_id eq 'none';
			$whinge->('Name cannot contain \'.\'') if $new_ft_id =~ /[.]/;
			my $old_file = $file;
			$file = "$config{Root}/fee_tmpls/" . encode_for_filename($new_id);
			my $rename = ($edit_id && $edit_id ne encode_for_html($new_id));
			$whinge->('Fee template name is already in use') if (-e $file && (!(defined $edit_id) || $rename));

			my @commods = keys %{{known_commod_descs}};
			my %drains = get_cf_drains(%cf);

			foreach my $row (0 .. get_rows(30, $cgi, 'Fee_', sub { $whinge->('No fees?') })) {
				my $amnt = validate_decimal(scalar $cgi->param("Fee_$row"), 'Fee/Drain amount', undef, $whinge);

				my @conds;
				foreach (get_attrs(1)) {
					if ($cgi->param("${_}_$row") eq 'if') {
						push (@conds, $_);
					} elsif ($cgi->param("${_}_$row") eq 'unless') {
						push (@conds, "!$_");
					}
				}
				my $cond = join (' && ', @conds);

				$whinge->('Missing fee/drain amount (but condition set)') if length $cond && $amnt == 0;
				next if $amnt == 0;

				my $cur;
				if (exists $drains{$cgi->param("Unit_$row")}) {
					$cur = $cgi->param("Unit_$row");
				} else {
					$cur = validate_unit(scalar $cgi->param("Unit_$row"), \@commods, $whinge);
				}

				push (@{$ft{Fee}}, $amnt);
				push (@{$ft{Unit}}, $cur);
				push (@{$ft{Condition}}, $cond);
			}

			if (exists $ft{Fee}) {
				@{$ft{Headings}} = ( 'Fee', 'Condition' );
				splice (@{$ft{Headings}}, 1, 0, 'Unit') if exists $ft{Unit};
			}

			$whinge->('Unable to get commit lock') unless try_commit_lock($sessid);
			unlock_dir('events', $sessid, $whinge, 'FT rename', 'events') if $rename;
			bad_token_whinge(gen_manage_fee_tmpls) unless redeem_edit_token($sessid, $edit_id ? "edit_$edit_id" : 'add_ft', $etoken);
			try_commit_and_unlock(sub {
				if ($rename) {
					my $old_ft_id = $edit_id;
					if ($et_id && $old_ft_id =~ /^[^\/.]+\.([^\/]+)$/) {
						$old_ft_id = $1;
					}
					dir_mod_all('events', 0, [ $old_ft_id ], sub { my ($evnt, $old) = @_; $evnt->{Template} =~ s/^$old$/$new_ft_id/ if defined $evnt->{Template} && ((defined $evnt->{EventType} && $et_id && $evnt->{EventType} eq $et_id) || !(defined $evnt->{EventType})) }, 11);
					$git->mv($old_file, $file);
				}
				(mkdir "$config{Root}/fee_tmpls" or die) unless (-d "$config{Root}/fee_tmpls");
				write_htsv($file, \%ft);
				if ($rename) {
					add_commit($file, 'Rename FT ' . unroot($old_file) . ' to ' . unroot($file), $session);
				} else {
					add_commit($file, unroot($file) . ": FT \"$new_id\" " . ($edit_id ? 'modified' : 'created'), $session);
				}
			}, $rename ? $old_file : ($edit_id) ? $file : undef);
		} else {
			unlock($file) if redeem_edit_token($sessid, $edit_id ? "edit_$edit_id" : 'add_ft', $etoken) && $file;
		}

		if ($edit_id) {
			emit_with_status((defined $cgi->param('save')) ? "Saved edits to \"$new_id\" fee template" : 'Edit cancelled', gen_edit_fee_tmpl((defined $cgi->param('save')) ? $new_id : $edit_id, undef, $et_id, \%et));
		} else {
			emit_with_status((defined $cgi->param('save')) ? "Added fee template \"$new_id\"" : 'Add fee template cancelled', gen_manage_fee_tmpls);
		}
	}
	if ($cgi->param('tmpl') eq 'edit_fee_cfg') {
		my $cfg_file = "$config{Root}/config_fees";

		if (defined $cgi->param('save')) {
			my %cfg;
			my %oldcf = read_htsv($cfg_file, 1);
			my $whinge = sub { whinge($_[0], gen_edit_fee_cfg($etoken)) };

			my %vaccts = grep_acct_key('accounts', 'Name');
			my %ppl = grep_acct_key('users', 'Name');
			my %acct_names = (%vaccts, %ppl);

			$whinge->('Missing account name') unless clean_username($cgi->param('DefAcct'));
			$cfg{DefaultAccount} = validate_acct(scalar $cgi->param('DefAcct'), \%vaccts, $whinge);

			my %cds = known_commod_descs;
			my %recode;
			foreach my $row (0 .. get_rows(30, $cgi, 'Acct_', sub { $whinge->('No fees?') })) {
				my $oldcode = clean_word($cgi->param("OldID_$row"));
				my $desc = clean_words($cgi->param("FeeDesc_$row"));

				if (defined $oldcode && exists $cds{$oldcode}) {
					next unless length $cgi->param("Acct_$row");
					$whinge->("\"$oldcode\" multiply defined") if grep ($_ eq $oldcode, @{$cfg{Fee}});
					push (@{$cfg{Fee}}, $oldcode);
					push (@{$cfg{Account}}, validate_acct(scalar $cgi->param("Acct_$row"), \%acct_names, $whinge));
					push (@{$cfg{IsDrain}}, '');
					push (@{$cfg{Expensable}}, '');
				} else {
					my $id = clean_word($cgi->param("FeeID_$row"));
					$whinge->("ID cannot be a number ($id)") if defined $id && !($id =~ /^\s*$/) && defined clean_int($id);
					my $acct = clean_username($cgi->param("Acct_$row"));
					next unless (defined $id && !($id =~ /^\s*$/)) || defined $desc;
					$whinge->("Missing ID for \"$desc\"") unless defined $id;
					$id = lc $id;
					$whinge->("\"$id\" multiply defined") if grep ($_ eq $id, @{$cfg{Fee}});
					$recode{$oldcode} = $id if defined $oldcode && !($oldcode =~ /[A-Z]/) && grep ($_ eq $oldcode, grep (defined, @{$oldcf{Fee}})) && $oldcode ne $id;
					$whinge->("Missing display text for \"$id\"") unless defined $desc;
					$whinge->("Missing linked account for \"$desc\"") unless defined $acct && length $acct;
					$whinge->("Expense (\"$id\") cannot be Boolean (not a drain)") if defined $cgi->param("Bool_$row") && !(defined $cgi->param("Drain_$row"));
					$whinge->("Expense (\"$id\") cannot be Boolean and Expensable") if defined $cgi->param("Bool_$row") && defined $cgi->param("Expensable_$row");
					push (@{$cfg{Fee}}, $id);
					push (@{$cfg{Account}}, validate_acct(scalar $acct, \%acct_names, $whinge));
					push (@{$cfg{IsDrain}}, (defined $cgi->param("Drain_$row")));
					push (@{$cfg{Expensable}}, (defined $cgi->param("Exp_$row")));
				}
				push (@{$cfg{IsBool}}, (defined $cgi->param("Bool_$row")));
				push (@{$cfg{Description}}, $desc);
			}

			@{$cfg{Headings}} = ( 'Fee', 'IsBool', 'IsDrain', 'Expensable', 'Account', 'Description' ) if exists $cfg{Fee};

			$whinge->('Unable to get commit lock') unless try_commit_lock($sessid);
			if (keys %recode) {
				unlock_dir('event_types', $sessid, $whinge, 'fee recode', 'event types');
				unlock_dir('fee_tmpls', $sessid, $whinge, 'fee recode', 'fee templates');
				unlock_dir('events', $sessid, $whinge, 'fee recode', 'events');
			}
			bad_token_whinge(gen_tcp) unless redeem_edit_token($sessid, 'edit_fee_cfg', $etoken);
			try_commit_and_unlock(sub {
				my $commit_msg = 'config_fees: expense configuration modified';

				if (keys %recode) {
					dir_mod_all('event_types', 0, [ keys %recode ], sub { my ($et, $old) = @_; foreach (@{$et->{Unit}}) { s/^$old$/$recode{$old}/ if $_; } });
					dir_mod_all('fee_tmpls', 0, [ keys %recode ], sub { my ($ft, $old) = @_; foreach (@{$ft->{Unit}}) { s/^$old$/$recode{$old}/ if $_; } });
					dir_mod_all('events', 0, [ keys %recode ], sub { my ($evnt, $old) = @_;
						if (defined $evnt->{Headings}) {
							s/^$old$/$recode{$old}/ foreach (@{$evnt->{Headings}});
						}
						$evnt->{$recode{$old}} = delete $evnt->{$old} if exists $evnt->{$old}; }, 11);
					$commit_msg .= ' AND CODES ALTERED';
				}

				write_htsv($cfg_file, \%cfg, 11);
				add_commit($cfg_file, $commit_msg, $session);
			}, $cfg_file);
		} else {
			unlock($cfg_file) if redeem_edit_token($sessid, 'edit_fee_cfg', $etoken);
		}

		emit_with_status((defined $cgi->param('save')) ? 'Saved edits to expense config' : 'Edit expense config cancelled', gen_tcp);
	}
	if ($cgi->param('tmpl') eq 'edit_pers_attrs') {
		my $cfg_file = "$config{Root}/config_pers_attrs";

		if (defined $cgi->param('save')) {
			my %cfg;
			my %oldcfg = get_attrs_full;
			my $whinge = sub { whinge($_[0], gen_edit_pers_attrs($etoken)) };
			my @types = ( 'Has', 'Is' );
			my %rename;

			foreach my $row (0 .. get_rows(100, $cgi, 'Type_', sub { $whinge->('No attributes?') })) {
				my $type = clean_word($cgi->param("Type_$row")) // '';
				my $attr = clean_words($cgi->param("Attr_$row"));
				my $oldattr = clean_word($cgi->param("OldAttr_$row"));
				next unless $attr;
				$whinge->('Invalid type prefix') if defined $type && length $type && !grep ($_ eq $type, @types);
				$whinge->('Attributes cannot have \':\' in them') if $attr =~ /:/;
				$whinge->('Attributes cannot have spaces') unless clean_word($attr);
				$attr = ucfirst $type . ucfirst $attr;
				$whinge->("'$attr' is reserved for internal use") if grep ($_ eq $attr, get_sys_attrs);
				$whinge->('no.') if grep ($_ eq $oldattr, get_sys_attrs);
				$rename{$oldattr} = $attr if defined $oldattr && exists $oldcfg{$oldattr} && $oldattr ne $attr;
				$whinge->('Attributes renames must have type prefix') if $rename{$oldattr} && !(defined $type && length $type);
				$cfg{$attr} = (defined $oldattr && exists $oldcfg{$oldattr}) ? $oldcfg{$oldattr} : undef;
			}
			$cfg{IsAuthed} = $oldcfg{IsAuthed} if $oldcfg{IsAuthed};
			$cfg{IsPleb} = $oldcfg{IsPleb} if $oldcfg{IsPleb};
			$cfg{$_} = $oldcfg{$_} foreach (grep (/&amp;&amp;/, keys %oldcfg));

			$whinge->('Unable to get commit lock') unless try_commit_lock($sessid);
			if (%rename) {
				unlock_dir('users', $sessid, $whinge, 'attribute rename', 'users');
				unlock_dir('fee_tmpls', $sessid, $whinge, 'attribute rename', 'fee templates');
			}

			bad_token_whinge(gen_tcp) unless redeem_edit_token($sessid, 'edit_pers_attrs', $etoken);
			try_commit_and_unlock(sub {
				if (%rename) {
					my @renames = keys %rename;
					dir_mod_all('users', 0, \@renames, sub { my ($acct, $old) = @_; if (exists $acct->{$old}) { $acct->{$rename{$old}} = delete $acct->{$old}; } });
					dir_mod_all('fee_tmpls', 0, \@renames, sub { my ($ft, $old) = @_; foreach (@{$ft->{Condition}}) { s/((^|&amp;&amp;)\s*!?\s*)$old(\s*($|&amp;&amp;))/$1$rename{$old}$3/ if $_; } });
					foreach my $attr (keys %cfg) {
						next unless $cfg{$attr};
						$cfg{$attr} =~ s/(^|:)\s*$_\s*(:|$)/$1$rename{$_}$2/ foreach (@renames);
					}
				}

				write_htsv($cfg_file, \%cfg);
				add_commit($cfg_file, 'config_pers_attrs: personal attribute types modified', $session);
			}, $cfg_file);
		} else {
			unlock($cfg_file) if redeem_edit_token($sessid, 'edit_pers_attrs', $etoken);
		}

		emit_with_status((defined $cgi->param('save')) ? 'Saved edits to attribute config' : 'Edit attribute config cancelled', gen_tcp);
	}
	if ($cgi->param('tmpl') eq 'edit_attr_groups') {
		my $cfg_file = "$config{Root}/config_pers_attrs";

		if (defined $cgi->param('save')) {
			my %cfg;
			my $whinge = sub { whinge($_[0], gen_edit_attr_groups($etoken)) };

			foreach my $attr (get_attrs(1), 'IsAuthed', 'IsPleb') {
				$cfg{$attr} = join (':', sort map { s/^${attr}_//; $_ } grep (/^${attr}_/, $cgi->param()));
			}
			delete $cfg{IsAuthed} unless length $cfg{IsAuthed};
			delete $cfg{IsPleb} unless length $cfg{IsPleb};

			my %comb;
			foreach my $row (0 .. get_rows(30, $cgi, 'ImpAttr_', sub { $whinge->('No combination rows?') })) {
				my $imp = $cgi->param("ImpAttr_$row");
				next unless $imp;
				next unless grep (/^${row}_/, $cgi->param());
				push (@{$comb{join ('&&', sort map { s/^${row}_//; $_ } grep (/^${row}_/, $cgi->param()))}}, $imp);
			}
			foreach (keys %comb) {
				if (/&&/) {
					$cfg{$_} = join (':', sort @{$comb{$_}});
				} else {
					$whinge->('No combination specified: use implication table instead');
				}
			}

			$whinge->('Unable to get commit lock') unless try_commit_lock($sessid);
			bad_token_whinge(gen_tcp) unless redeem_edit_token($sessid, 'edit_attr_groups', $etoken);
			try_commit_and_unlock(sub {
				write_htsv($cfg_file, \%cfg);
				add_commit($cfg_file, 'config_pers_attrs: attribute groups modified', $session);
			}, $cfg_file);
		} else {
			unlock($cfg_file) if redeem_edit_token($sessid, 'edit_attr_groups', $etoken);
		}

		emit_with_status((defined $cgi->param('save')) ? 'Saved edits to attribute config' : 'Edit attribute config cancelled', gen_tcp);
	}

	if ($cgi->param('tmpl') eq 'edit_units') {
		my $cfg_file = "$config{Root}/config_units";

		if (defined $cgi->param('rates')) {
			my $whinge = sub { whinge($_[0], gen_edit_units($etoken)) };

			my %cfg = read_units_cfg($cfg_file, 1);
			my %oldcfg = %cfg;
			delete $cfg{$_} foreach (grep (!ref $cfg{$_}, keys %cfg));

			$cfg{Commodities} = '';
			my $anchor_set = 0;
			my $pres_set = 0;
			my $nunits = 0;
			my %rename;

			foreach my $row (0 .. get_rows(100, $cgi, 'Description_', sub { $whinge->('No currencies?') })) {
				my $code = clean_unit($cgi->param("Code_$row"));
				my $oldcode = clean_unit($cgi->param("OldCode_$row"));
				my $desc = clean_words($cgi->param("Description_$row"));
				next unless $code or $desc;
				$whinge->('Missing/invalid short code') unless $code;
				$whinge->("\"$code\" multiply defined") if exists $cfg{$code};
				validate_unitname($code, $whinge);
				if (defined $oldcode && exists $oldcfg{$oldcode} && $oldcode ne $code) {
					# renaming!
					foreach my $key (keys %cfg) {
						if (ref $cfg{$key} && $key =~ /^$oldcode\/(.*)$/) {
							my $new = "$code/$1";
							s/^$key$/$new/ foreach (@{$cfg{Headings}});
							$cfg{$new} = $cfg{$key};
							delete $cfg{$key};
						}
						if (ref $cfg{$key} && $key =~ /^(.*)\/$oldcode$/) {
							my $new = "$1/$code";
							s/^$key$/$new/ foreach (@{$cfg{Headings}});
							$cfg{$new} = $cfg{$key};
							delete $cfg{$key};
						}
					}

					$rename{$oldcode} = $code;
				}
				$cfg{$code} = $desc;
				$nunits++;

				$cfg{Commodities} .= "$code;" if defined $cgi->param("Commodity_$row");
				if (defined $cgi->param('Anchor') and $cgi->param('Anchor') eq $row) {
					$whinge->('More than one anchor currency?') if $anchor_set;
					$cfg{Anchor} = $code;
					$anchor_set = 1;
				}
				if (defined $cgi->param('Default') and $cgi->param('Default') eq $row) {
					$whinge->('More than one presentation currency?') if $pres_set;
					$cfg{Default} = $code;
					$pres_set = 1;
				}
			}
			$cfg{Commodities} =~ s/;$//;
			if ($nunits < 2) {
				delete $cfg{Anchor};
				delete $cfg{Default};
			}

			validate_units(\%cfg, $whinge, 1);

			if ($nunits < 2) {
				commit_config_units($whinge, $session, $etoken, \%rename, \%cfg);
				emit_with_status('Saved edits to units config (rate setting inapplicable)', gen_tcp);
			} else {
				write_units_cfg("$cfg_file.p1", \%cfg);
				write_simp_cfg("$cfg_file.rename", %rename) if keys %rename;

				emit(gen_edit_rates($etoken));
			}
		} else {
			unlock($cfg_file) if redeem_edit_token($sessid, 'edit_units', $etoken);
			emit_with_status('Edit units config cancelled', gen_tcp);
		}
	}
	if ($cgi->param('tmpl') eq 'edit_rates') {
		my $cfg_file = "$config{Root}/config_units";

		if (defined $cgi->param('save')) {
			my $whinge = sub { whinge($_[0], gen_edit_rates($etoken)) };

			my %cfg = read_units_cfg("$cfg_file.p1");	# presume we got here having successfully just defined units
			delete $cfg{$_} foreach (grep (ref $cfg{$_}, keys %cfg));

			my %curs;
			$curs{$_} = 1 foreach (known_currs(%cfg));

			@{$cfg{Headings}} = ( 'Date' );
			foreach (sort (known_units(%cfg))) {
				next if $_ eq $cfg{Anchor};
				if (exists $curs{$_}) {
					push (@{$cfg{Headings}}, "$_/$cfg{Anchor}");
				} elsif (scalar keys %curs == 1) {
					push (@{$cfg{Headings}}, "$cfg{Anchor}/$_");
				} else {
					my $in = clean_unit($cgi->param("Denom_$_"));
					$whinge->("No valid defining currency for $_") unless $in;
					push (@{$cfg{Headings}}, "$in/$_");
				}
			}

			my $added = 0;
			foreach my $row (0 .. get_rows(100, $cgi, 'Date_', sub { $whinge->('No rates?') })) {
				my $rate_found = 0;
				my %row;
				foreach (@{$cfg{Headings}}) {
					next if $_ eq 'Date';
					(my $unit = $_) =~ s/.*\///;
					($unit = $_) =~ s/\/.*// if $unit eq $cfg{Anchor};
					my $rate = validate_decimal(scalar $cgi->param("Rate_${row}_$unit"), 'Exchange rate', undef, $whinge);
					$rate_found = 1 unless $rate == 0;
					$row{$_} = ($rate != 0) ? $rate : undef;
				}
				if ($rate_found) {
					$row{Date} = validate_date(scalar $cgi->param("Date_$row"), $whinge);
					push (@{$cfg{$_}}, $row{$_}) foreach (@{$cfg{Headings}});
					$added++;
				}
			}
			$whinge->('No rates set') unless $added;

			validate_units(\%cfg, $whinge);
			%cfg = date_sort_rates(%cfg);

			my %rename = read_simp_cfg("$cfg_file.rename", 1);
			commit_config_units($whinge, $session, $etoken, \%rename, \%cfg);
		} else {
			unlink "$cfg_file.p1";
			unlink "$cfg_file.rename" if -e "$cfg_file.rename";
			unlock($cfg_file) if redeem_edit_token($sessid, 'edit_units', $etoken);
		}

		emit_with_status((defined $cgi->param('save')) ? 'Saved edits to units config' : 'Edit units config cancelled', gen_tcp);
	}

	return;
}

sub date_sorted_htsvs
{
	my $flavour = $_[0];

	my %dates;
	if ($flavour eq 'transaction_groups') {
		$dates{$_} = $tgds{$_}{Date} foreach (keys %tgds);
	} else {
		unless (%evs) {
			foreach (grep (-f, glob ("$config{Root}/events/*"))) {
				(my $ev = $_) =~ s/^.*\///;
				$evs{$ev} = \%{{read_htsv($_, undef, [ 'Person', 'Notes' ])}};
			}
		}
		$dates{$_} = $evs{$_}{Date} foreach (keys %evs);
	}

	my %rds;
	foreach (keys %dates) {
		$dates{$_} = '0.0.0' unless defined $dates{$_} and $dates{$_} =~ /^\s*\d+\s*[.]\s*\d+\s*[.]\s*\d+\s*$/;
		push (@{$rds{$dates{$_}}}, $_);	# non-unique dates
	}
	foreach (keys %rds) {
		@{$rds{$_}} = sort @{$rds{$_}};	# stable sort order for HTSVs on the same date
	}
	return map (@{$rds{$_->[0]}}, sort { $a->[1] cmp $b->[1] } map ([ $_, sprintf('%04d%02d%02d', (split /[.]/, $_)[2,1,0]) ], keys %rds));	# Schwartzian transform ftw
}

sub sprint_monetary
{
	my ($value, $no_plus) = @_;

	return ($value && abs $value > .001) ? sprintf($no_plus ? '%.2f' : '%+.2f', $value) : sprintf('0.00');
}

sub unk_computed_accts
{
	my ($va, $comp) = @_;

	return grep (!(exists $va->{$_}), keys %$comp);
}

sub gen_ucp
{
	my ($session, $acct) = @_;
	my $tmpl = load_template('user_cp.html', undef, $session);
	my $user = $acct // $session->param('User');

	my @events;
	my $newest = fmtime('newest');
	%evs = %{flock_rc("$config{Root}/events/.evs")} if fmtime('events/.evs') > $newest;
	foreach my $mid (date_sorted_htsvs('events')) {
		push (@events, { MID => $mid, NAME => $evs{$mid}->{Name}, DATE => $evs{$mid}->{Date}, LOCKED => (exists $evs{$mid}->{Locked}) }) if ($evs{$mid}->{Leader} // '') eq $user;
	}
	if (%evs && cache_lock) {
		flock_wc("$config{Root}/events/.evs", \%evs) unless (fmtime('newest') != $newest || fmtime('events/.evs') > $newest);
		cache_unlock;
	}

	my %acct_names = get_acct_name_map;
	my %dds = double_drainers;
	my %neg_accts = grep_acct_key('accounts', 'IsNegated');
	my %resolved = resolve_accts(\%dds, \%neg_accts);

	my $credsum = 0;
	my $debsum = 0;
	my (@credlist, @debtlist);
	foreach my $tg (date_sorted_htsvs('transaction_groups')) {
		my %rcomputed;
		my %computed = eval { compute_tg_c($tg, undef, \%neg_accts, \%resolved, $user, \%rcomputed) };
		my $tg_indet = nonfinite(values %computed);
		my $tg_broken = $@ ne '' || (%resolved && $tg_indet) || exists $dds{$tg};
		next unless exists $computed{$user} or $tg_broken;

		my %tgdetails = %{$tgds{$tg}};
		my (@to, @from, @to_extras, @from_extras);
		my $bidi = !(exists $neg_accts{$user});
		unless ($tg_broken) {
			# since 0 net entries are listed in credits, force appearance of credit for arrow selection purposes
			$rcomputed{$user} = 1 if $rcomputed{$user} == 0;

			# foreach one that would appear in @to
			foreach (grep ($_ ne $user && (!$rcomputed{$_} || (((exists $neg_accts{$user}) == (exists $neg_accts{$_})) == ($rcomputed{$_} * $rcomputed{$user} < 0))), keys %rcomputed)) {
				$bidi = (exists $neg_accts{$user}) if !(exists $neg_accts{$_});
			}
			$computed{$user} >= 0 ? $credsum : $debsum += $computed{$user} unless exists $tgdetails{Omit};

			@to = map ({ SEP => ', ', N => $acct_names{$_}, A => $_ }, grep ($_ ne $user && (!$rcomputed{$_} || ($bidi && exists $neg_accts{$user}) || (((exists $neg_accts{$user}) == (exists $neg_accts{$_})) == ($rcomputed{$_} * $rcomputed{$user} < 0))), sort keys %rcomputed));
			@from = map ({ SEP => ', ', N => $acct_names{$_}, A => $_ }, grep ($_ ne $user && !($rcomputed{$_} && $bidi && exists $neg_accts{$user}) && (((exists $neg_accts{$user}) == (exists $neg_accts{$_})) == ($rcomputed{$_} * $rcomputed{$user} >= 0)), sort keys %rcomputed));

			$to[0]->{SEP} = '' if scalar @to;
			$to[-1]->{SEP} = ' and ' if scalar @to > 1;
			if (scalar @to > 5) {
				@to_extras = map ($to[$_]->{N}, (4 .. $#to));
				$#to = 3;
			}
			$from[0]->{SEP} = '' if scalar @from;
			$from[-1]->{SEP} = ' and ' if scalar @from > 1;
			if (scalar @from > 5) {
				@from_extras = map ($from[$_]->{N}, (4 .. $#from));
				$#from = 3;
			}
		}

		my $is_event = $tg =~ /^E/;
		my %outputdetails = (
			EVENT => $is_event,
			ACC => $is_event ? substr ($tg, 1) : $tg,
			TG_CL => (exists $tgdetails{Omit}) ? 'omitted' : '',
			NAME => $tgdetails{Name},
			TO => \@to,
			TO_EXTRA => join (', ', @to_extras),
			FROM => \@from,
			FROM_EXTRA => join (', ', @from_extras),
			BIDI => $bidi,
			DATE => $tgdetails{Date},
			SUMMARY_CL => $tg_broken ? 'broken' : $tg_indet ? 'indet' : '',
			SUMMARY => encode_for_html($tg_broken ? 'TG BROKEN' : $tg_indet ? 'incalculable' : ($computed{$user} > 0 ? '+' : '') . $computed{$user}),
		);
		push (@{($tg_broken or $computed{$user} >= 0) ? \@credlist : \@debtlist}, \%outputdetails);
	}
	my %cf = read_htsv("$config{Root}/config_fees", 1);
	my %id_count;
	my @simptransidcounts = map ($id_count{$cf{Fee}[$_]}++, grep (defined $cf{Fee}[$_] && length $cf{Fee}[$_] && !($cf{Fee}[$_] =~ /[A-Z]/ || true($cf{IsBool}[$_])) && true($cf{Expensable}[$_]) && defined $cf{Account}[$_] && exists $acct_names{$cf{Account}[$_]} && defined $cf{Description}[$_] && length $cf{Description}[$_], 0 .. $#{$cf{Description}}));
	$tmpl->param(SIMPTRANS => scalar @simptransidcounts && !grep ($_ > 0, @simptransidcounts));
	$tmpl->param(ACCT => (exists $acct_names{$acct}) ? $acct_names{$acct} : $acct) if defined $acct && $acct ne $session->param('User');
	$tmpl->param(MYEVENTS => \@events);
	$tmpl->param(ACCTSN => $user);
	$tmpl->param(BAL => sprint_monetary($credsum + $debsum));
	$tmpl->param(CRED_TOT => sprint_monetary($credsum));
	$tmpl->param(DEB_TOT => sprint_monetary($debsum));
	my %units_cfg = read_units_cfg("$config{Root}/config_units");
	my @units = known_units(%units_cfg);
	$tmpl->param(DEFCUR => (scalar @units) ? $units[0] : undef);
	$tmpl->param(DEFCURDESC => (scalar @units) ? $units_cfg{$units[0]} : undef);
	$tmpl->param(CREDITS => \@credlist);
	$tmpl->param(DEBITS => \@debtlist);
	$tmpl->param(LOGIN => $session->param('User'));
	$tmpl->param(ADDTG => $session->param('MayAddEditTGs'));
	$tmpl->param(BANK => $session->param('IsAdmin') && scalar %neg_accts);
	$tmpl->param(EVENTS => !!valid_fee_cfg);

	return $tmpl;
}

sub gen_accts_disp
{
	my ($session, $nozeros, $by_bal) = @_;
	my $tmpl = load_template('accts_disp.html', undef, $session);

	my %dds = double_drainers;
	my %neg_accts = grep_acct_key('accounts', 'IsNegated');
	my %resolved = resolve_accts(\%dds, \%neg_accts);
	my @tgs = glob ("$config{Root}/transaction_groups/*");
	if ($@ || (!%resolved && @tgs) || nonfinite(values %resolved)) {
		$tmpl->param(BROKEN => 1);
		return $tmpl;
	}

	my %running;
	foreach my $tg (@tgs) {
		$tg = $1 if $tg =~ /([^\/]*)$/;
		if (exists $dds{$tg}) {
			$tmpl->param(BROKEN => 1);
			return $tmpl;
		}
		my %computed = compute_tg_c($tg, 1, \%neg_accts, \%resolved);
		foreach (keys %computed) {
			$running{$_} = 0 unless exists $running{$_};
			$running{$_} += $computed{$_};
			$running{$_} = 0 if abs $running{$_} < .000000001;
		}
	}

	my %ppl = grep_acct_key('users', 'Name');
	my %vaccts = grep_acct_key('accounts', 'Name');
	my %acct_names = (%ppl, %vaccts);
	my @unknown;
	my ($maxu, $maxp, $maxv) = (0, 0, 0);
	foreach (keys %running) {
		if (exists $ppl{$_}) {
			$maxp = abs $running{$_} if abs $running{$_} > $maxp;
		} elsif (exists $vaccts{$_}) {
			$maxv = abs $running{$_} if abs $running{$_} > $maxv;
		} else {
			$maxu = abs $running{$_} if abs $running{$_} > $maxu;
			push (@unknown, $_);
		}
	}
	my @accts = ((sort @unknown), sort_AoH(\%ppl, \%vaccts));
	$running{$_} = 0 foreach grep (!(exists $running{$_}), @accts);
	my (@unklist, @ppllist, @vacctslist);
	my ($sum_debts, $sum_creds) = (0, 0);
	foreach ($by_bal ? map ($_->[0], sort { $a->[1] <=> $b->[1] } map ([ $_, $running{$_} ], @accts)) : @accts) {	# Schwartzian transform ftw
		next if $nozeros && abs $running{$_} < .005;

		my $pc = 0;
		if (exists $ppl{$_} && $maxp) {
			$pc = 100 / $maxp * abs $running{$_};
		} elsif (exists $vaccts{$_} && $maxv) {
			$pc = 100 / $maxv * abs $running{$_};
		} elsif ($maxu) {
			$pc = 100 / $maxu * abs $running{$_};
		}
		my ($r, $g, $b) = (255, 255, 0);
		$r = 255 * 2 * $pc / 100 if $pc < 50;
		$g -= 255 * 2 * ($pc - 50) / 100 if $pc > 50;

		my %outputdetails = (
			ACC => $_,
			NAME => (exists $acct_names{$_}) ? $acct_names{$_} : $_,
			A_CL => (exists $neg_accts{$_}) ? 'negated' : '',
			VAL => sprint_monetary($running{$_}),
			C => sprintf('#%02x%02x%02x', $r, $g, $b),
			L => $running{$_} > 0 ? 0 : $pc,
			R => $running{$_} <= 0 ? 0 : $pc,
		);
		($running{$_} < 0) ? $sum_debts : $sum_creds += $running{$_} if exists $ppl{$_};
		if (exists $acct_names{$_}) {
			push (@{(exists $ppl{$_}) ? \@ppllist : \@vacctslist}, \%outputdetails);
		} else {
			push (@unklist, \%outputdetails);
		}
	}
	$tmpl->param(NOZEROS => $nozeros);
	$tmpl->param(SORT => $by_bal ? 'bal' : 'name');
	$tmpl->param(NOZEROS => $nozeros);
	$tmpl->param(UNKNOWN => \@unklist) if scalar @unklist;
	$tmpl->param(PPL => \@ppllist) if scalar @ppllist;
	$tmpl->param(SDEBTS => sprint_monetary(-$sum_debts, 1), SCREDS => sprint_monetary($sum_creds, 1));
	$tmpl->param(VACCTS => \@vacctslist) if scalar @vacctslist;
	my %units_cfg = read_units_cfg("$config{Root}/config_units");
	my @units = known_units(%units_cfg);
	$tmpl->param(DEFCUR => (scalar @units) ? "$units_cfg{$units_cfg{Default}} ($units_cfg{Default})" : undef);

	return $tmpl;
}

sub gen_add_swap
{
	my ($swap, $def_cred, $etoken) = @_;
	my $tmpl = load_template('add_swap.html', $etoken);

	my %accts = grep_acct_key('users', 'Name');
	my @sorted_accts = sort_AoH(\%accts);
	my @pploptions = map ({ O => $accts{$_}, V => $_, S => $def_cred eq $_ }, @sorted_accts);
	my %units_cfg = read_units_cfg("$config{Root}/config_units");
	my @units = known_units(%units_cfg);
	my @currencies = map ({ C => $_, D => $units_cfg{$_}, S => $units_cfg{Default} eq $_ }, @units);

	my @debtaccts;
	if ($swap) {
		@debtaccts = map ({ O => $accts{$_}, V => $_ }, @sorted_accts);
	} else {
		my %cfg = read_htsv("$config{Root}/config_fees");
		my %acct_names = get_acct_name_map;
		my @sorteddescs = map ($_->[0], sort { $a->[1] cmp $b->[1] } map ([ $_, $cfg{Description}[$_]], grep (defined $cfg{Fee}[$_] && length $cfg{Fee}[$_] && !($cfg{Fee}[$_] =~ /[A-Z]/ || true($cfg{IsBool}[$_])) && true($cfg{Expensable}[$_]) && defined $cfg{Account}[$_] && exists $acct_names{$cfg{Account}[$_]} && defined $cfg{Description}[$_] && length $cfg{Description}[$_], 0 .. $#{$cfg{Description}})));	# Schwartzian transform ftw
		@debtaccts = map ({ O => $cfg{Description}[$_], V => "$cfg{Fee}[$_]" }, @sorteddescs);
	}

	$tmpl->param(SWAP => $swap, PPL => \@pploptions, CUR => (scalar @units > 1), CURS => \@currencies, DEBTACCTS => \@debtaccts);

	return $tmpl;
}

sub gen_add_split
{
	my ($bank, $vacct, $etoken) = @_;
	my $tmpl = load_template('add_split.html', $etoken);

	my %accts = grep_acct_key('users', 'Name');
	my %vaccts = grep_acct_key('accounts', 'Name');
	my @pploptions = map ({ NAME => $accts{$_}, A => $_ }, sort_AoH(\%accts));
	my %units_cfg = read_units_cfg("$config{Root}/config_units");
	my @units = known_units(%units_cfg);
	my @currencies = map ({ C => $_, D => $units_cfg{$_}, S => $units_cfg{Default} eq $_ }, @units);

	my @nas;
	if ($bank) {
		my %neg_accts = grep_acct_key('accounts', 'IsNegated');
		@nas = map ({ NAME => $vaccts{$_}, A => $_ }, sort_AoH({ map (($_ => $vaccts{$_}), keys %neg_accts) }));
	}

	my @vaccts;
	if ($vacct) {
		my %cfg = read_htsv("$config{Root}/config_fees");
		my %acct_names = get_acct_name_map;
		my @sorteddescs = map ($_->[0], sort { $a->[1] cmp $b->[1] } map ([ $_, $cfg{Description}[$_]], grep (defined $cfg{Fee}[$_] && length $cfg{Fee}[$_] && !($cfg{Fee}[$_] =~ /[A-Z]/ || true($cfg{IsBool}[$_])) && true($cfg{Expensable}[$_]) && defined $cfg{Account}[$_] && exists $acct_names{$cfg{Account}[$_]} && defined $cfg{Description}[$_] && length $cfg{Description}[$_], 0 .. $#{$cfg{Description}})));	# Schwartzian transform ftw
		@vaccts = map ({ NAME => $cfg{Description}[$_], A => "$cfg{Fee}[$_]" }, @sorteddescs);
	} else {
		if ($bank and scalar @nas == 1) {
			@vaccts = map ({ NAME => $vaccts{$_}, A => $_ }, grep ($_ ne $nas[0]{'A'}, sort_AoH(\%vaccts)));
		} else {
			@vaccts = map ({ NAME => $vaccts{$_}, A => $_ }, sort_AoH(\%vaccts));
		}
	}

	$tmpl->param(BANK => $bank, VACCT => $vacct, PPL => \@pploptions, NAS => \@nas, CUR => (scalar @units > 1), CURS => \@currencies, VACCTS => \@vaccts);

	return $tmpl;
}

sub gen_manage_tgs
{
	my $session = $_[0];
	my $tmpl = load_template('manage_transactions.html', undef, $session);
	my %acct_names = get_acct_name_map;
	my %dds = double_drainers;
	my %neg_accts = grep_acct_key('accounts', 'IsNegated');
	my %resolved = resolve_accts(\%dds, \%neg_accts);

	my %units_cfg = read_units_cfg("$config{Root}/config_units");
	my $defcur = (scalar known_currs(%units_cfg) > 1) ? $units_cfg{Default} : '';
	my @tglist;
	my %daterates;
	foreach my $tg (date_sorted_htsvs('transaction_groups')) {
		my $tg_fail;
		my %computed = eval { compute_tg_c($tg, undef, \%neg_accts, \%resolved, undef, undef, sub { $tg_fail = $_[0]; die }) };
		my %tgdetails = %{$tgds{$tg}};
		my %rates = get_rates($tgdetails{Date}) unless $@;
		my @unks = unk_computed_accts(\%acct_names, \%computed) unless $@;
		$tg_fail = 'Non-existent account(s) "' . join ('", "', @unks) . '"' if @unks && !$@;
		my $tg_indet = nonfinite(values %computed) ? 'TG depends on broken TG' : '';
		$tg_fail = 'TGs drain in a loop!' if %resolved && $tg_indet && !$tg_fail;
		$tg_fail = "Multiple drains of '$dds{$tg}'" if exists $dds{$tg} && !$tg_fail;

		my @sum_str;
		if ($tg_fail || $tg_indet) {
			push (@sum_str, { FIRST => 1, VAL => encode_for_html($tg_fail ? $tg_fail : $tg_indet) });
		} else {
			my %summary;
			foreach my $i (0 .. $#{$tgdetails{Creditor}}) {
				my $acct = $tgdetails{Creditor}[$i];
				my $drained = 0;
				next if $acct =~ /^TrnsfrPot\d$/;
				next if exists $summary{$acct};
				$summary{$acct} = 0;
				foreach ($i .. $#{$tgdetails{Creditor}}) {
					next if $tgdetails{Creditor}[$_] ne $acct;
					if ($tgdetails{Amount}[$_] =~ /^\s*[*]\s*$/) {
						$drained = 1;
					} else {
						my $rate = (scalar keys %rates < 2) ? 1 : $rates{$tgdetails{Currency}[$_]};
						$summary{$acct} += $tgdetails{Amount}[$_] * $rate;
					}
				}
				push (@sum_str, { FIRST => !(scalar @sum_str), N => $acct_names{$acct}, A => $acct, VAL => ($drained ? 'drained' : (($summary{$acct} < 0) ? '' : '+') . sprintf('%.2f', $summary{$acct}) . " $defcur") });
			}
		}

		my %outputdetails = (
			ACC => $tg,
			TG_CL => (exists $tgdetails{Omit}) ? 'omitted' : '',
			NAME => $tgdetails{Name},
			DATE => $tgdetails{Date},
			SUMMARY_CL => $tg_fail ? 'broken' : $tg_indet ? 'indet' : '',
			SUMMARY => \@sum_str,
			DELTG => $session->param('IsAdmin') && !($tg =~ /^[A-Z]/),
		);
		push (@tglist, \%outputdetails);
	}
	my @units = known_units(%units_cfg);
	$tmpl->param(TGS => \@tglist, DEFCUR => (scalar @units) ? "$units_cfg{$units_cfg{Default}} ($units_cfg{Default})" : undef);
	$tmpl->param(ADDTG => $session->param('MayAddEditTGs'));

	return $tmpl;
}

sub sort_AoH
{
	my @sorted;

	while (my $sortme = shift) {
		if (ref $sortme) {
			my %rev = reverse %$sortme;
			push (@sorted, map ($rev{$_}, sort keys %rev));
		} else {
			push (@sorted, $sortme) unless ref $sortme;
		}
	}

	return @sorted;
}

sub gen_tg
{
	my ($edit_id, $calced, $def_cred, $session, $etoken) = @_;

	my $tmpl = load_template('edit_tg.html', $etoken, $session);

	my %ppl = grep_acct_key('users', 'Name');
	$def_cred = $session->param('User') unless $def_cred && exists $ppl{$def_cred};

	my %units_cfg = read_units_cfg("$config{Root}/config_units");
	my @units = known_units(%units_cfg);
	my %tgdetails = gen_ft_tg_common($edit_id ? "$config{Root}/transaction_groups/$edit_id" : undef, 1, 10, !$etoken, 'Creditor', $def_cred, 'Currency', 5, 100, \@units);

	my %dds;
	if ($calced) {
		my $whinge = sub { whinge("Can't display calculated values: $_[0]", gen_tg($edit_id, undef, $def_cred, $session, $etoken)) };
		validate_tg($edit_id, \%tgdetails, $whinge);
		validate_units(\%units_cfg, $whinge, undef, "$config{Root}/config_units");
		%dds = double_drainers;
		$whinge->("Multiple drains of '$dds{$edit_id}'") if exists $dds{$edit_id};
	}

	my %vaccts = grep_acct_key('accounts', 'Name');
	my %acct_names = (%ppl, %vaccts);
	my (%unknown, %in_use_ppl, %in_use_vaccts, %in_use_unk);
	my @tps_in_use;
	foreach my $acct (@{$tgdetails{Headings}}[2 .. ($#{$tgdetails{Headings}} - 1)], @{$tgdetails{Creditor}}) {
		$acct //= '';
		next if $acct eq 'Currency';
		$unknown{$acct} = $acct unless $acct =~ /^TrnsfrPot\d?$/ || exists $acct_names{$acct};
		$tps_in_use[$1] = 1 if ($acct =~ /^TrnsfrPot(\d)$/);
		next if $etoken || $acct =~ /^TrnsfrPot\d?$/;
		my $has_data = 0;
		foreach (@{$tgdetails{$acct}}) {
			$has_data = 1 if defined $_ && $_ != 0;
			last if $has_data;
		}
		next unless $has_data;
		$in_use_ppl{$acct} = $acct_names{$acct} if exists $ppl{$acct};
		$in_use_vaccts{$acct} = $acct_names{$acct} if exists $vaccts{$acct};
		$in_use_unk{$acct} = $acct if exists $unknown{$acct};
	}
	my @sorted_accts = sort_AoH(\%unknown, \%ppl, \%vaccts);
	my @sorted_in_use = $etoken ? @sorted_accts : sort_AoH(\%in_use_unk, \%in_use_ppl, \%in_use_vaccts);

	push (@{$tgdetails{$_}}, (0) x (scalar @{$tgdetails{Creditor}} - scalar @{$tgdetails{$_}})) foreach ('Amount', @sorted_in_use);

	my %tps;
	my $tps_to_add = 3;
	foreach my $i (1 .. 9) {
		unless (defined $tps_in_use[$i] or $tps_to_add == 0) {
			$tps_in_use[$i] = 1;
			$tps_to_add--;
		}
		$tps{"TrnsfrPot$i"} = "Transfer Pot $i" if $tps_in_use[$i];
	}
	%acct_names = (%unknown, %ppl, %vaccts, %tps);

	$tmpl->param(TG_ID => $edit_id);
	$tmpl->param(DEF_CRED => $def_cred);
	$tmpl->param(RO => !$etoken);
	$tmpl->param(IN_CVS => $calced);
	$tmpl->param(EDITOK => $edit_id && !($edit_id =~ /^[A-Z]/) && $session->param('MayAddEditTGs'));
	$tmpl->param(DELTG => $session->param('IsAdmin') && $edit_id && !($edit_id =~ /^[A-Z]/));
	$tmpl->param(NAME => $tgdetails{Name});
	$tmpl->param(DATE => $tgdetails{Date});
	$tmpl->param(OMIT => 1) if exists $tgdetails{Omit};
	$tmpl->param(NOACCTS => scalar @sorted_in_use);
	my %negated = grep_acct_key('accounts', 'IsNegated');
	my @heads;
	foreach (@sorted_in_use) {
		my $class = (exists $negated{$_}) ? 'negated' : '';
		$class .= ' unknown_d' if exists $unknown{$_};
		push (@heads, { H => $acct_names{$_}, A => $_, HEAD_CL => $class });
	}
	$tmpl->param(HEADINGS => \@heads);

	my %resolved;
	my %rates;
	if (!$etoken && clean_date($tgdetails{Date})) {
		%rates = get_rates($tgdetails{Date});
	}
	my @tp_per_share;
	my @tp_cur;
	if ($calced) {
		my $is_drain = 0;
		my $has_tp = 0;
		my @tp_curs;

		foreach my $row (0 .. $#{$tgdetails{Creditor}}) {
			my $cred = $tgdetails{Creditor}[$row] // '';
			$is_drain = 1 if $tgdetails{Amount}[$row] =~ /^\s*[*]\s*$/ && !($cred =~ /^TrnsfrPot\d$/);
			$has_tp = 1 if $cred =~ /^TrnsfrPot(\d)$/;

			if (defined $tgdetails{TrnsfrPot}[$row] && $tgdetails{TrnsfrPot}[$row] =~ /^\s*(\d)\s*$/) {
				$has_tp = 1;

				# validate_tg has been previously called, so if there's a Currency column it has *only* valid values
				$tp_curs[$1]{(exists $tgdetails{Currency} && !$is_drain) ? $tgdetails{Currency}[$row] : $units[0]} = 1 if scalar @units;
			}
		}
		$tp_cur[$_] = (scalar keys %{$tp_curs[$_]} == 1) ? (keys %{$tp_curs[$_]})[0] : $units[0] foreach grep ($tp_curs[$_], (1 .. 9));

		%resolved = resolve_accts(\%dds, \%negated) if $is_drain;
		if ($has_tp) {
			@tp_per_share = tg_tp_amnt_per_share(\@sorted_in_use, $tgdetails{Creditor}, \%tgdetails, \%rates, \%resolved, \%negated);
		}
	}

	my @rows;
	foreach my $row (0 .. $#{$tgdetails{Creditor}}) {
		my $cred = $tgdetails{Creditor}[$row] // '';
		my @credunk = map ({ O => $acct_names{$_}, V => $_, S => 1 }, grep (exists $unknown{$_}, ($cred)));
		my @credppl = map ({ O => $acct_names{$_}, V => $_, S => $cred eq $_ }, sort_AoH(\%ppl));
		my @credvas = map ({ O => $acct_names{$_}, V => $_, S => $cred eq $_ }, sort_AoH(\%vaccts));
		my @credtps = map ({ O => $acct_names{$_}, V => $_, S => $cred eq $_, CR_CL => 'tp' }, sort_AoH(\%tps));
		my $amnt = $tgdetails{Amount}[$row];
		my $per_share;
		my $tp = 0;
		if ($calced) {
			my $is_drain = $amnt =~ /^\s*[*]\s*$/ && !($cred =~ /^TrnsfrPot\d$/);
			$tp = $1 if ($cred =~ /^TrnsfrPot(\d)$/ || (defined $tgdetails{TrnsfrPot}[$row] && $tgdetails{TrnsfrPot}[$row] =~ /^\s*(\d)\s*$/));

			$tgdetails{Currency}[$row] = $tp ? $tp_cur[$tp] : $units[0] if scalar @units && $amnt =~ /^\s*[*]\s*$/;
			# the '1 *' turns 0.000 into 0, etc.
			$amnt = 1 * sprintf ('%.3f', ((exists $resolved{$cred}) ? -$resolved{$cred} : 0+'inf')) if $is_drain;

			my $cur_cur = $tgdetails{Currency}[$row] ? $tgdetails{Currency}[$row] : $units[0];
			my $row_tps = $tp_per_share[$tp] / ((scalar @units > 1 && $cur_cur ne $units[0]) ? $rates{$cur_cur} : 1) if $tp;
			my $shares = sum map (CleanData::clean_decimal($tgdetails{$_}[$row]), @sorted_in_use);
			$per_share = $tp ? -$row_tps : -$amnt / $shares;
		}
		$tgdetails{Currency}[$row] //= '';
		my $unk_cur = !grep ($_ eq $tgdetails{Currency}[$row], @units);
		my @currencies = map ({ C => $_, S => ($_ eq $tgdetails{Currency}[$row]), CDESC => ($units_cfg{$_} // $_), RATE => (exists $rates{$_}) ? "$rates{$_} $units[0]" : '' }, $unk_cur ? (@units, $tgdetails{Currency}[$row]) : @units);
		my @rowcontents = map ({ D => 1 * sprintf ('%.3f', (($calced && ((!$tp && (exists $negated{$cred})) xor (exists $negated{$_}))) ? -1 : 1) * $tgdetails{$_}[$row] * ($per_share // 1)), N => "${_}_$row", D_CL => ((exists $unknown{$_}) ? 'unknown_d' : '') . ((exists $vaccts{$_}) ? ' vacct' : '') }, @sorted_in_use);
		my @tps = map ({ V => $_, S => ($tgdetails{TrnsfrPot}[$row] ? $tgdetails{TrnsfrPot}[$row] eq $_ : undef) }, 1 .. 9);
		push (@rows, { ROW_CL => (exists $unknown{$cred}) ? 'unknown_c' : '',
			       R => $row,
			       CREDUNK => \@credunk,
			       CREDPPL => \@credppl,
			       CREDVAS => \@credvas,
			       CREDTPS => \@credtps,
			       CUR_CL => (!(exists $tps{$cred}) && !($tgdetails{Amount}[$row] =~ /^\s*[*]\s*$/) && !grep ($_ eq $tgdetails{Currency}[$row], @units)) ? 'unknown_u' : '',
			       CURS => \@currencies,
			       A => $amnt,
			       RC => \@rowcontents,
			       TP => (defined $tgdetails{TrnsfrPot}[$row] && $tgdetails{TrnsfrPot}[$row] =~ /[1-9]/) ? $tgdetails{TrnsfrPot}[$row] : 'N/A',
			       TPS => \@tps,
			       DESC => $tgdetails{Description}[$row] });
	}
	$tmpl->param(ROWS => \@rows);

	my @allunits = @units;
	foreach my $cur (grep (defined, @{$tgdetails{Currency}})) {
		push (@allunits, $cur) unless grep ($_ eq $cur, @allunits);
	}

	$tmpl->param(CUROPTS => scalar @allunits > 1);
	$tmpl->param(DEFCUR => (scalar @allunits == 1) ? ((scalar @units) ? "$units_cfg{$units_cfg{Default}} ($units_cfg{Default})" : "$allunits[0] (UNKNOWN!)") : undef);

	return $tmpl;
}

sub new_uuidfile
{
	my $path = $_[0];
	my $id;
	(mkdir "$path" or die) unless (-d $path);
	do {
		$id = create_UUID_as_string(UUID_V4);
	} while (-e "$path/$id");
	return "$path/$id";
}

sub clean_tg
{
	my ($tg, $compact_creds) = @_;
	my %newtg;

	$newtg{Name} = $tg->{Name};
	$newtg{Date} = $tg->{Date};
	$newtg{Omit} = undef if exists $tg->{Omit};

	foreach my $row (0 .. $#$compact_creds) {
		next unless $$compact_creds[$row];
		$tg->{Amount}[$row] = '*' if $tg->{Creditor}[$row] =~ /^TrnsfrPot[1-9]$/;
		$tg->{Currency}[$row] = '' if $tg->{Amount}[$row] =~ /^\s*[*]\s*$/;
		push (@{$newtg{$_}}, $tg->{$_}[$row]) foreach (@{$tg->{Headings}});
	}

	$newtg{Headings} = $tg->{Headings};

	return %newtg;
}

sub update_event_tg
{
	my ($edit_id, $tg) = @_;

	my $tg_file = "$config{Root}/transaction_groups/E$edit_id";
	if (exists $tg->{Creditor} && scalar @{$tg->{Creditor}}) {
		(mkdir "$config{Root}/transaction_groups" or die) unless (-d "$config{Root}/transaction_groups");
		open (my $fh, '>', $tg_file) or die;
		say $fh "Event TGs are autogenerated at runtime";
		close $fh or die;
		$git->add($tg_file);
	} else {
		$git->rm($tg_file) if -e $tg_file;
		flock_rm("$config{Root}/transaction_groups/.E$edit_id.precomp");
		clear_caches('');
	}

	return;
}

sub despatch
{
	my $session = $_[0];
	my $sessid = $session->id();
	my $cgi = $session->query();
	my $etoken = $cgi->param('etoken');

	return if (defined $cgi->param('logout'));

	emit(gen_manage_tgs($session)) if (defined $cgi->param('manage_tgs'));
	emit(gen_manage_events($session)) if (defined $cgi->param('manage_events'));
	emit(gen_ucp($session)) if (defined $cgi->param('to_acct'));
	emit(gen_accts_disp($session)) if (defined $cgi->param('disp_accts'));

	despatch_admin($session) if $session->param('IsAdmin');

	if ($cgi->param('tmpl') eq 'login' || $cgi->param('tmpl') eq 'login_nopw') {
		my $tmpl = gen_ucp($session);
		print $tmpl->output;
		exit;
	}
	if ($cgi->param('tmpl') eq 'ucp') {
		if (defined $cgi->param('add_swap') || defined $cgi->param('add_vacct_swap')) {
			my $swap = defined $cgi->param('add_swap');
			my %acct_names = grep_acct_key('users', 'Name');
			emit(gen_add_swap($swap, ((exists $acct_names{$cgi->param('acct')}) ? $cgi->param('acct') : $session->param('User')), get_edit_token($sessid, $swap ? 'add_swap' : 'add_vacct_swap')));
		}
		if (defined $cgi->param('add_split') || defined $cgi->param('add_vacct_split') || defined $cgi->param('add_bank_split')) {
			redeem_edit_token($sessid, 'add_vacct_swap', $etoken) if $etoken;
			my $bank = defined $cgi->param('add_bank_split');
			my $vacct = defined $cgi->param('add_vacct_split');
			emit(gen_add_split($bank, $vacct, get_edit_token($sessid, !$vacct ? ($bank ? 'add_bank_split' : 'add_split') : 'add_vacct_split')));
		}
	}
	if ($cgi->param('tmpl') eq 'add_swap' || $cgi->param('tmpl') eq 'add_vacct_swap') {
		whinge('Action not permitted', gen_ucp($session)) unless $session->param('MayAddEditTGs');
		my $swap = ($cgi->param('tmpl') eq 'add_swap');
		my $tgfile;

		if (defined $cgi->param('save')) {
			my %tg;
			my %acct_names = grep_acct_key('users', 'Name');
			my $whinge = sub { whinge($_[0], gen_add_swap($swap, ((exists $acct_names{$cgi->param('Creditor')}) ? $cgi->param('Creditor') : $session->param('User')), $etoken)) };

			my @units = known_units();

			$tg{Date} = validate_date(scalar $cgi->param('tg_date'), $whinge);
			push (@{$tg{Creditor}}, validate_acct(scalar $cgi->param('Creditor'), \%acct_names, $whinge));
			push (@{$tg{Amount}}, CleanData::clean_decimal($cgi->param('Amount')) ? CleanData::clean_decimal($cgi->param('Amount')) : clean_word($cgi->param('Amount')));
			push (@{$tg{Currency}}, (scalar @units > 1) ? clean_word($cgi->param('Currency')) : $units[0]) if (scalar @units);
			push (@{$tg{Description}}, clean_words($cgi->param('Description')));

			my $debtor;
			if ($swap) {
				$whinge->('Missing description') unless defined @{$tg{Description}}[0];
				$debtor = validate_acct(scalar $cgi->param('Debtor'), \%acct_names, $whinge);
				my $namedesc = @{$tg{Description}}[0];
				$namedesc = substr ($namedesc, 0, rindex ($namedesc, ' ', 14)) . ' [...]' if (length $namedesc > 20);
				$tg{Name} = "Swap: $acct_names{$debtor}->$acct_names{@{$tg{Creditor}}[0]} for $namedesc";
			} else {
				my %cf = read_htsv("$config{Root}/config_fees");
				my $fee = clean_word($cgi->param('Debtor'));
				$whinge->('Broken expense type') unless defined $fee && !($fee =~ /[A-Z]/);
				my $row = first { defined $cf{Fee}[$_] && $cf{Fee}[$_] eq $fee } 0 .. $#{$cf{Fee}};
				$whinge->('Unknown expense type') unless defined $row;
				$whinge->('Broken expense type') if true($cf{IsBool}[$row]) || !true($cf{Expensable}[$row]);
				$debtor = validate_acct($cf{Account}[$row], \%{{get_acct_name_map}}, $whinge);
				$tg{Name} = "Expense: $cf{Description}[$row]";
				$tg{Name} .= lc " ($tg{Description}[0])" if length $tg{Description}[0];
			}
			push (@{$tg{$debtor}}, 1);

			@{$tg{Headings}} = ( 'Creditor', 'Amount', $debtor, 'Description' );
			splice (@{$tg{Headings}}, 2, 0, 'Currency') if exists $tg{Currency};

			validate_tg(undef, \%tg, $whinge);

			$whinge->('Unable to get commit lock') unless try_commit_lock($sessid);
			bad_token_whinge(gen_ucp($session)) unless redeem_edit_token($sessid, $swap ? 'add_swap' : 'add_vacct_swap', $etoken);
			try_commit_and_unlock(sub {
				$tgfile = new_uuidfile("$config{Root}/transaction_groups");
				write_tg($tgfile, %tg);
				my @split_tgf = split('-', unroot($tgfile));
				add_commit($tgfile, "$split_tgf[0]...: TG \"$tg{Name}\" created", $session);
			});
		} else {
			redeem_edit_token($sessid, $swap ? 'add_swap' : 'add_vacct_swap', $etoken);
		}

		$tgfile =~ /\/([^\/]{1,4})[^\/]*$/ if $tgfile;
		if ($swap) {
			emit_with_status((defined $cgi->param('save')) ? "Swap saved ($1)" : 'Add swap cancelled', gen_ucp($session));
		} else {
			emit_with_status((defined $cgi->param('save')) ? "Expense saved ($1)" : 'Add expense cancelled', gen_ucp($session));
		}
	}
	if ($cgi->param('tmpl') eq 'add_split' || $cgi->param('tmpl') eq 'add_vacct_split' || $cgi->param('tmpl') eq 'add_bank_split') {
		whinge('Action not permitted', gen_ucp($session)) unless $session->param('MayAddEditTGs');
		my $bank = ($cgi->param('tmpl') eq 'add_bank_split'); 
		whinge('Action not permitted', gen_ucp($session)) if $bank && !$session->param('IsAdmin');
		my $vacct = ($cgi->param('tmpl') eq 'add_vacct_split'); 
		my $tgfile;

		if (defined $cgi->param('save')) {
			my %tg;
			my $whinge = sub { whinge($_[0], gen_add_split($bank, $vacct, $etoken)) };

			$tg{Name} = ($bank ? 'Tied transaction: ' : 'Split' . ($vacct ? ' expense: ' : ': ')) . clean_words($cgi->param('tg_name'));
			$tg{Date} = validate_date(scalar $cgi->param('tg_date'), $whinge);

			my %ppl = grep_acct_key('users', 'Name');
			my %neg_accts = grep_acct_key('accounts', 'IsNegated');
			my %creds;
			foreach my $acct (map { /^Cred_(.*)/; $1 } grep (/^Cred_.+$/, $cgi->param)) {
				validate_acct($acct, ($bank ? \%neg_accts : \%ppl), $whinge);
				my $amnt = ($cgi->param("Cred_$acct") && $cgi->param("Cred_$acct") =~ /^\s*[*]\s*$/) ? '*' : validate_decimal(scalar $cgi->param("Cred_$acct"), 'Creditor amount', undef, $whinge);
				$creds{$acct} = $amnt if $amnt eq '*' || $amnt != 0;
			}
			$whinge->('No creditors?') unless scalar keys %creds;

			my @units = known_units();

			if (scalar keys %creds > 1) {
				push (@{$tg{Creditor}}, 'TrnsfrPot1');
				push (@{$tg{Amount}}, '*');
				push (@{$tg{Currency}}, undef) if (scalar @units);
				push (@{$tg{TrnsfrPot}}, undef);
			}
			foreach my $cred (keys %creds) {
				push (@{$tg{Creditor}}, $cred);
				push (@{$tg{Amount}}, $creds{$cred});
				push (@{$tg{Currency}}, (scalar @units > 1) ? clean_word($cgi->param('Currency')) : $units[0]) if (scalar @units);
				push (@{$tg{TrnsfrPot}}, 1) if scalar keys %creds > 1;
			}

			my %cf;
			my %acct_names = get_acct_name_map;
			my @accts;
			my @descstrs;
			foreach my $dacct (map { /^Debt_(.*)/; $1 } grep (/^Debt_.+$/, $cgi->param)) {
				my $ds = validate_decimal(scalar $cgi->param("Debt_$dacct"), 'Debt share', 1, $whinge);
				next unless $ds;

				my $acct;
				my $type;
				unless ($dacct =~ /^V/) {
					$acct = validate_acct($dacct, ($bank ? \%acct_names : \%ppl), $whinge);
				} else {
					%cf = read_htsv("$config{Root}/config_fees") unless %cf;
					my $fee = clean_word($dacct);
					$fee =~ s/^V// if defined $fee;
					$whinge->('Broken expense type') unless defined $fee && !($fee =~ /[A-Z]/);
					my $row = first { defined $cf{Fee}[$_] && $cf{Fee}[$_] eq $fee } 0 .. $#{$cf{Fee}};
					$whinge->('Unknown expense type') unless defined $row;
					$whinge->('Broken expense type') if true($cf{IsBool}[$row]) || !true($cf{Expensable}[$row]);
					$acct = validate_acct($cf{Account}[$row], \%acct_names, $whinge);
					$type = $cf{Description}[$row];
				}

				$tg{$acct}[0] = (exists $tg{$acct}) ? $tg{$acct}[0] + $ds : $ds;
				push (@accts, $acct) unless grep ($_ eq $acct, @accts);
				push (@descstrs, "$type ($acct) -> $ds") if $dacct =~ /^V/;
			}

			my $descstr = join (', ', @descstrs);
			if (length clean_text($cgi->param('Description'))) {
				$descstr .= ': ' if length $descstr;
				$descstr .= clean_text($cgi->param('Description'));
			}
			push (@{$tg{Description}}, $descstr);

			@{$tg{Headings}} = ( 'Creditor', 'Amount' );
			push (@{$tg{Headings}}, 'Currency') if exists $tg{Currency};
			push (@{$tg{Headings}}, 'TrnsfrPot') if scalar keys %creds > 1;
			push (@{$tg{Headings}}, ((sort @accts), 'Description'));

			validate_tg(undef, \%tg, $whinge);

			$whinge->('Unable to get commit lock') unless try_commit_lock($sessid);
			bad_token_whinge(gen_ucp($session)) unless redeem_edit_token($sessid, !$vacct ? ($bank ? 'add_bank_split' : 'add_split') : 'add_vacct_split', $etoken);
			try_commit_and_unlock(sub {
				$tgfile = new_uuidfile("$config{Root}/transaction_groups");
				write_tg($tgfile, %tg);
				my @split_tgf = split('-', unroot($tgfile));
				add_commit($tgfile, "$split_tgf[0]...: TG \"$tg{Name}\" created", $session);
			});
		} else {
			redeem_edit_token($sessid, !$vacct ? ($bank ? 'add_bank_split' : 'add_split') : 'add_vacct_split', $etoken);
		}

		$tgfile =~ /\/([^\/]{1,4})[^\/]*$/ if $tgfile;
		if ($vacct) {
			emit_with_status((defined $cgi->param('save')) ? "Split expense saved ($1)" : 'Add split expense cancelled', gen_ucp($session));
		} elsif ($bank) {
			emit_with_status((defined $cgi->param('save')) ? "Tied transaction saved ($1)" : 'Add tied transaction cancelled', gen_ucp($session));
		} else {
			emit_with_status((defined $cgi->param('save')) ? "Split saved ($1)" : 'Add split cancelled', gen_ucp($session));
		}
	}
	if ($cgi->param('tmpl') eq 'accts_disp') {
		if (defined $cgi->param('view')) {
			emit(gen_ucp($session, scalar $cgi->param('view')));
		}
		my $nozeros = $cgi->param('last_nz') // 0;
		my $sort = $cgi->param('last_sort') // 'name';
		$nozeros = 0 if defined $cgi->param('showzeros');
		$nozeros = 1 if defined $cgi->param('nozeros');
		$sort = $cgi->param('sort') if defined $cgi->param('sort');

		emit(gen_accts_disp($session, $nozeros, $sort eq 'bal'));
	}
	if ($cgi->param('tmpl') eq 'manage_tgs') {
		my $whinge = sub { whinge($_[0], gen_manage_tgs($session)) };
		if (defined $cgi->param('view') or defined $cgi->param('add')) {
			my $view = valid_edit_id(scalar $cgi->param('view'), "$config{Root}/transaction_groups", 'TG', $whinge);

			emit(gen_tg($view, undef, scalar $cgi->param('def_cred'), $session, $view ? undef : get_edit_token($sessid, 'add_tg', $etoken)));
		}
		if (((grep (/^del_.+$/, $cgi->param))[0] // '') =~ /^del_(.+)$/) {
			my $edit_id = valid_edit_id($1, "$config{Root}/transaction_groups", 'TG', $whinge, 1);
			whinge('Deletion not permitted', gen_manage_tgs($session)) unless $session->param('IsAdmin') && $edit_id && !($edit_id =~ /^[A-Z]/);
			delete_common("$config{Root}/transaction_groups/$edit_id", "TG \"$edit_id\"", $session, sub {
				flock_rm("$config{Root}/transaction_groups/.$edit_id.json");
				flock_rm("$config{Root}/transaction_groups/.$edit_id.precomp");
				clear_caches('');
				gen_manage_tgs($session) });
		}
	}
	if ($cgi->param('tmpl') eq 'edit_tg' || ($cgi->param('tmpl') eq 'manage_tgs' && grep (/^force_edit_.+/, $cgi->param))) {
		my $whinge = sub { whinge($_[0], gen_manage_tgs($session)) };
		my $is_edit = $cgi->param('tmpl') eq 'manage_tgs' || defined $cgi->param('edit');
		my $tg_id = $cgi->param('tg_id');
		($tg_id = (grep (/^force_edit_.+/, $cgi->param))[0]) =~ s/^force_edit_// if $cgi->param('tmpl') eq 'manage_tgs';
		my $edit_id = valid_edit_id($tg_id, "$config{Root}/transaction_groups", 'TG', $whinge, $is_edit);

		if (defined $cgi->param('showcvs') || defined $cgi->param('hidecvs')) {
			emit(gen_tg($edit_id, (defined $cgi->param('showcvs')), scalar $cgi->param('def_cred'), $session, undef));
		}

		whinge('Action not permitted', $edit_id ? gen_tg($edit_id, undef, scalar $cgi->param('def_cred'), $session, undef) : gen_manage_tgs($session)) unless $session->param('MayAddEditTGs');
		my $tgfile = $edit_id ? "$config{Root}/transaction_groups/$edit_id" : undef;

		if ($is_edit) {
			whinge('Editing of generated TGs not allowed', gen_tg($edit_id, undef, scalar $cgi->param('def_cred'), $session, undef)) if $edit_id && $edit_id =~ /^[A-Z]/;

			lock_or_whinge($tgfile, "transaction group \"$edit_id\"", $session, sub { gen_manage_tgs($session) }, "edit_$edit_id");
			unless (-r $tgfile) {
				unlock($tgfile);
				$whinge->("Couldn't edit transaction group \"$edit_id\", file disappeared");
			}
			emit(gen_tg($edit_id, undef, scalar $cgi->param('def_cred'), $session, get_edit_token($sessid, "edit_$edit_id")));
		}
		if (defined $cgi->param('delete')) {
			whinge('Deletion not permitted', gen_tg($edit_id, undef, scalar $cgi->param('def_cred'), $session, undef)) unless $session->param('IsAdmin') && $edit_id && !($edit_id =~ /^[A-Z]/);
			delete_common($tgfile, "TG \"$edit_id\"", $session, sub {
				flock_rm("$config{Root}/transaction_groups/.$edit_id.json");
				flock_rm("$config{Root}/transaction_groups/.$edit_id.precomp");
				clear_caches('');
				gen_manage_tgs($session) });
		}

		# only left with save and cancel now
		my %tg;

		if (defined $cgi->param('save')) {
			$whinge = sub { whinge($_[0], gen_tg($edit_id, undef, scalar $cgi->param('def_cred'), $session, $etoken)) };

			$tg{Name} = clean_words($cgi->param('tg_name'));
			$tg{Date} = validate_date(scalar $cgi->param('tg_date'), $whinge);
			(defined $cgi->param('omit')) ? $tg{Omit} = undef : delete $tg{Omit};

			my $max_rows = get_rows(100, $cgi, 'Creditor_', sub { $whinge->('No transactions?') });

			my %acct_names = get_acct_name_map;
			my @accts = map { /^(.*)_0$/; $1 } grep ((/^(.+)_0$/ and $1 ne 'Creditor' and $1 ne 'Amount' and $1 ne 'Currency' and $1 ne 'TrnsfrPot' and $1 ne 'Description'), $cgi->param);
			my (%ppl, %vaccts);
			foreach my $acct (@accts) {
				unless (exists $acct_names{$acct}) {
					my $in_use = 0;
					foreach (0 .. $max_rows) {
						$in_use = 1 unless CleanData::clean_decimal($cgi->param("${acct}_$_")) == 0;
					}
					next unless $in_use;
				}
				validate_acct($acct, \%acct_names, $whinge);
				((-r "$config{Root}/users/$acct") ? $ppl{$acct} : $vaccts{$acct}) = $acct_names{$acct};
			}

			my @units = known_units();
			foreach my $row (0 .. $max_rows) {
				push (@{$tg{Creditor}}, clean_word($cgi->param("Creditor_$row")));
				push (@{$tg{Amount}}, CleanData::clean_decimal($cgi->param("Amount_$row")) ? CleanData::clean_decimal($cgi->param("Amount_$row")) : clean_word($cgi->param("Amount_$row")));
				push (@{$tg{Currency}}, (scalar @units > 1) ? clean_word($cgi->param("Currency_$row")) : $units[0]) if (scalar @units);
				push (@{$tg{$_}}, clean_word($cgi->param("${_}_$row"))) foreach (keys %ppl, keys %vaccts);
				push (@{$tg{TrnsfrPot}}, clean_word($cgi->param("TrnsfrPot_$row")));
				push (@{$tg{Description}}, clean_words($cgi->param("Description_$row")));
			}
			@{$tg{Headings}} = sort_AoH('Creditor', 'Amount', 'TrnsfrPot', \%ppl, \%vaccts, 'Description');
			splice (@{$tg{Headings}}, 2, 0, 'Currency') if exists $tg{Currency};

			my @cred_accts = validate_tg($edit_id, \%tg, $whinge, \%acct_names, \%{{drained_accts($edit_id)}});

			%tg = clean_tg(\%tg, \@cred_accts);
			$whinge->('No transactions?') unless exists $tg{Creditor};

			my %neg_accts = grep_acct_key('accounts', 'IsNegated');
			eval { compute_tg($edit_id, \%tg, undef, \%neg_accts, undef, $whinge) };
			# FIXME ought to check we're not creating a drain loop.  problem is, if other TGs are errorful, resolve_accts can't be expected to work fully.  without this, we have no loop checker.  disabling editing until TGs are fixed is self defeating...

			$whinge->('Unable to get commit lock') unless try_commit_lock($sessid);
			bad_token_whinge(gen_manage_tgs($session)) unless redeem_edit_token($sessid, $edit_id ? "edit_$edit_id" : 'add_tg', $etoken);
			try_commit_and_unlock(sub {
				$tgfile = new_uuidfile("$config{Root}/transaction_groups") unless ($tgfile);
				write_tg($tgfile, %tg);
				my @split_tgf = split('-', unroot($tgfile));
				add_commit($tgfile, "$split_tgf[0]...: TG \"$tg{Name}\" " . ($edit_id ? 'modified' : 'created'), $session);
			}, $tgfile);
		} else {
			unlock($tgfile) if redeem_edit_token($sessid, $edit_id ? "edit_$edit_id" : 'add_tg', $etoken) && $tgfile;
		}

		$tgfile =~ /\/([^\/]{1,4})[^\/]*$/ if $tgfile;
		if ($edit_id) {
			emit_with_status((defined $cgi->param('save')) ? "Saved edits to \"$tg{Name}\" ($1) transaction group" : 'Edit cancelled', gen_tg($edit_id, undef, scalar $cgi->param('def_cred'), $session, undef));
		} else {
			$etoken = pop_session_data($sessid, $etoken);
			redeem_edit_token($sessid, 'add_vacct_swap', $etoken) if $etoken;
			emit_with_status((defined $cgi->param('save')) ? "Added transaction group \"$tg{Name}\" ($1)" : 'Add transaction group cancelled', $etoken ? gen_ucp($session) : gen_manage_tgs($session));
		}
	}
	if ($cgi->param('tmpl') eq 'manage_events') {
		my $whinge = sub { whinge($_[0], gen_manage_events($session)) };
		if (defined $cgi->param('view')) {
			my %cf = valid_fee_cfg;
			$whinge->('Cannot view event: expenses config is broken') unless %cf;
			my $mid = valid_edit_id(scalar $cgi->param('view'), "$config{Root}/events", 'event', $whinge, 1);

			emit(gen_edit_event($mid, \%cf, $session, undef));
		}
		if (defined $cgi->param('add')) {
			$whinge->('Action not permitted') unless $session->param('MayStewardEvents');

			my %evnt;
			my %ppl = grep_acct_key('users', 'Name');

			$evnt{Name} = clean_words($cgi->param('name'));
			$evnt{Date} = validate_date(scalar $cgi->param('date'), $whinge);
			$evnt{Duration} = validate_int(scalar $cgi->param('len'), 'Duration', 1, $whinge);
			$evnt{Leader} = validate_acct(scalar $cgi->param('leader'), \%ppl, $whinge);
			if ($cgi->param('fee_tmpl') && $cgi->param('fee_tmpl') =~ /(.*)\.(.*)/) {
				my $et = ($1 eq 'none') ? undef : valid_edit_id($1, "$config{Root}/event_types", 'event type', $whinge, 1);
				my $ft = ($2 eq 'none') ? undef : valid_edit_id($et ? "$et.$2" : $2, "$config{Root}/fee_tmpls", 'fee template', $whinge, 1);
				$ft =~ s/^$et\.// if $et;
				$evnt{EventType} = $et if $et;
				$evnt{Template} = $ft if $ft;
			}

			$whinge->('No event name given') unless length $evnt{Name};
			$whinge->('Zero duration?') unless $evnt{Duration} > 0;

			$whinge->('Unable to get commit lock') unless try_commit_lock($sessid);
			try_commit_and_unlock(sub {
				my $file = new_uuidfile("$config{Root}/events");
				write_simp_cfg($file, %evnt);
				my @split_f = split('-', unroot($file));
				add_commit($file, "$split_f[0]...: Event \"$evnt{Name}\" created", $session);
			});
			emit_with_status("Added event \"$evnt{Name}\"", gen_manage_events($session));
		}
		if (((grep (/^del_.+$/, $cgi->param))[0] // '') =~ /^del_(.+)$/) {
			my $mid = valid_edit_id($1, "$config{Root}/events", 'event', $whinge, 1);
			my %evnt = read_htsv("$config{Root}/events/$mid", undef, [ 'Person', 'Notes' ]);
			$whinge->('Action not permitted') unless event_edit_ok(\%evnt, $session, 1);
			$whinge->('Event not empty, you cannot delete it') unless $session->param('IsAdmin') || !(exists $evnt{Person} && scalar @{$evnt{Person}});

			delete_common("$config{Root}/events/$mid", "event \"$mid\"", $session, sub {
				flock_rm("$config{Root}/events/.evs");
				clear_caches('');
				gen_manage_events($session) }, "$config{Root}/transaction_groups/E$mid");
		}
	}
	if ($cgi->param('tmpl') eq 'edit_event' || ($cgi->param('tmpl') eq 'manage_events' && grep (/^force_edit_.+/, $cgi->param))) {
		my $whinge = sub { whinge($_[0], gen_manage_events($session)) };
		my $m_id = $cgi->param('m_id');
		($m_id = (grep (/^force_edit_.+/, $cgi->param))[0]) =~ s/^force_edit.*_// if $cgi->param('tmpl') eq 'manage_events';
		my $edit_id = valid_edit_id($m_id, "$config{Root}/events", 'event', $whinge, 1);
		my $mt_file = "$config{Root}/events/$edit_id";

		if (defined $cgi->param('cancel')) {
			unlock($mt_file) if redeem_edit_token($sessid, "edit_$edit_id", $etoken);
		}

		my %cf = valid_fee_cfg;
		$whinge->('Cannot display event: expenses config is broken') unless %cf;

		my %evnt = read_htsv($mt_file, undef, [ 'Person', 'Notes' ]);

		if (defined $cgi->param('edit_hdrs') || grep (/^force_edit_hdrs_.+/, $cgi->param)) {
			whinge('Action not permitted', gen_edit_event($edit_id, \%cf, $session, undef)) unless event_edit_ok(\%evnt, $session, 1);
			lock_or_whinge($mt_file, "event \"$edit_id\"", $session, sub { gen_manage_events($session) }, "edit_hdrs_$edit_id", "edit_$edit_id");
			unless (-r $mt_file) {
				unlock($mt_file);
				$whinge->("Couldn't edit event \"$edit_id\", file disappeared");
			}

			emit(gen_edit_event_hdrs($edit_id, \%cf, get_edit_token($sessid, "edit_$edit_id")));
		}

		whinge('Action not permitted', gen_edit_event($edit_id, \%cf, $session, undef)) unless event_edit_ok(\%evnt, $session);

		if (defined $cgi->param('edit_ppl') || defined $cgi->param('edit') || $cgi->param('tmpl') eq 'manage_events') {
			my $edit = defined $cgi->param('edit') || ($cgi->param('tmpl') eq 'manage_events' && !grep (/^force_edit_ppl_.+/, $cgi->param));
			lock_or_whinge($mt_file, "event \"$edit_id\"", $session, sub { gen_manage_events($session) }, ($edit ? 'edit_' : 'edit_ppl_') . $edit_id, "edit_$edit_id");
			unless (-r $mt_file) {
				unlock($mt_file);
				$whinge->("Couldn't edit event \"$edit_id\", file disappeared");
			}

			if ($edit) {
				emit(gen_edit_event($edit_id, \%cf, $session, get_edit_token($sessid, "edit_$edit_id")));
			} else {
				emit(gen_edit_event_ppl($edit_id, $sessid, get_edit_token($sessid, "edit_$edit_id")));
			}
		}

		if (defined $cgi->param('save')) {
			$whinge = sub { whinge($_[0], gen_edit_event($edit_id, \%cf, $session, $etoken)) };

			delete $evnt{Currency};
			my @ppl = @{$evnt{Person}};
			delete $evnt{$_} foreach (grep (ref $evnt{$_} || $_ =~ /^Split[1-9]Desc$/, keys %evnt));
			@{$evnt{Person}} = @ppl;

			my @units = known_units;
			$whinge->('No currency definition?') if scalar @units && !(defined $cgi->param('Currency'));
			if (defined $cgi->param('Currency') && $cgi->param('Currency') ne 'N/A') {
				$evnt{Currency} = validate_unit(scalar $cgi->param('Currency'), \@units, $whinge);
			}

			my %relevant_splits;
			foreach my $split (1 .. 9) {
				my $split_exp_count = scalar grep ($_ =~ /_Split${split}E$/, $cgi->param);
				my $split_shr_count = scalar grep ($_ =~ /_Split${split}S$/, $cgi->param);

				$whinge->('Number of split expense and share columns not equal') unless $split_exp_count == $split_shr_count;
				$relevant_splits{$split} = 1 if $split_exp_count || $split_shr_count;
			}

			my %cds = known_commod_descs;
			my %et;
			%et = valid_event_type("$config{Root}/event_types/" . encode_for_filename($evnt{EventType}), \%cf) if defined $evnt{EventType} && $evnt{EventType} ne 'none';

			my %pers_count;
			foreach my $pers (@{$evnt{Person}}) {
				$pers //= '';
				$pers_count{$pers} = 0 unless exists $pers_count{$pers};
				my @arr = $cgi->param("${pers}_Custom");
				push (@{$evnt{CustomFee}}, validate_decimal($arr[$pers_count{$pers}], 'Custom fee', 1, $whinge));
				foreach (%et ? map { my $fee = $_; (grep ($fee eq $cf{Fee}[$_], 0 .. $#{$cf{Fee}}))[0] } (@{$et{Unit}}) : 0 .. $#{$cf{Fee}}) {
					@arr = $cgi->param("${pers}_@{$cf{Fee}}[$_]");
					push (@{$evnt{@{$cf{Fee}}[$_]}}, validate_decimal($arr[$pers_count{$pers}], (exists $cds{$cf{Fee}[$_]}) ? ($cds{$cf{Fee}[$_]} // $cf{Fee}[$_]) : @{$cf{Description}}[$_] . ' value', 1, $whinge));
				}
				foreach (keys %relevant_splits) {
					@arr = $cgi->param("${pers}_Split${_}E");
					push (@{$evnt{"Split${_}Exps"}}, validate_decimal($arr[$pers_count{$pers}], 'Split expense', 0, $whinge));
					@arr = $cgi->param("${pers}_Split${_}S");
					push (@{$evnt{"Split${_}Shrs"}}, validate_decimal($arr[$pers_count{$pers}], 'Split debt share', 1, $whinge));
				}
				@arr = $cgi->param("${pers}_Notes");
				push (@{$evnt{Notes}}, clean_words($arr[$pers_count{$pers}]));
				$pers_count{$pers}++;
			}

			my @compact_splits;
			foreach (sort keys %relevant_splits) {
				if (!sum (@{$evnt{"Split${_}Exps"}})) {
					delete $relevant_splits{$_};
					delete $evnt{"Split${_}Exps"};
					delete $evnt{"Split${_}Shrs"};
					next;
				}
				$whinge->('Split expense without shares') unless sum (@{$evnt{"Split${_}Shrs"}});
				push (@compact_splits, 1 + scalar @compact_splits);
				$evnt{'Split' . $compact_splits[-1] . 'Exps'} = delete $evnt{"Split${_}Exps"};
				$evnt{'Split' . $compact_splits[-1] . 'Shrs'} = delete $evnt{"Split${_}Shrs"};
				$evnt{'Split' . $compact_splits[-1] . 'Desc'} = clean_words($cgi->param("Split${_}D"));
				$whinge->('Missing split description') unless ($evnt{'Split' . $compact_splits[-1] . 'Desc'});
			}

			my @midheads;
			if (%et) {
				my %drains = get_cf_drains(%cf);
				my ($fees, $exps) = get_event_types(\%et, \%drains);
				@midheads = (@$fees, @$exps);
			} else {
				@midheads = @{$cf{Fee}};
			}
			push (@midheads, ("Split${_}Exps", "Split${_}Shrs")) foreach (@compact_splits);
			@{$evnt{Headings}} = ( 'Person', 'CustomFee', @midheads, 'Notes' ) if scalar @{$evnt{Person}};

			my %tg = event_to_tg(%evnt);

			$whinge->('Unable to get commit lock') unless try_commit_lock($sessid);
			bad_token_whinge(gen_manage_events($session)) unless redeem_edit_token($sessid, "edit_$edit_id", $etoken);
			try_commit_and_unlock(sub {
				update_event_tg($edit_id, \%tg);
				write_htsv($mt_file, \%evnt, 11);
				my @split_mf = split('-', unroot($mt_file));
				add_commit($mt_file, "$split_mf[0]...: Event \"$evnt{Name}\" modified", $session);
			}, $mt_file);
		}

		$mt_file =~ /\/([^\/]{1,4})[^\/]*$/;
		emit_with_status((defined $cgi->param('save')) ? "Saved edits to event \"$evnt{Name}\" ($1)" : 'Edit cancelled', gen_edit_event($edit_id, \%cf, $session, undef));
	}
	if ($cgi->param('tmpl') eq 'edit_event_ppl') {
		my $edit_id = valid_edit_id(scalar $cgi->param('m_id'), "$config{Root}/events", 'event', sub { whinge($_[0], gen_manage_events($session)) }, 1);
		my $mt_file = "$config{Root}/events/$edit_id";

		if (defined $cgi->param('new_user')) {
			push_session_data($sessid, "${etoken}_editid", $edit_id);
			emit(gen_add_edit_acc(undef, 1, $session, get_edit_token($sessid, 'add_acct', $etoken), !$session->param('IsAdmin')));
		}

		if (defined $cgi->param('cancel')) {
			unlock($mt_file) if redeem_edit_token($sessid, "edit_$edit_id", $etoken) && $mt_file;
			pop_session_data($sessid, "${etoken}_add_accts");
		}

		my %cf = valid_fee_cfg;
		whinge('Cannot display event: expenses config is broken', gen_manage_events($session)) unless %cf;

		my %evnt = read_htsv($mt_file, undef, [ 'Person', 'Notes' ]);
		whinge('Action not permitted', gen_edit_event($edit_id, \%cf, $session, undef)) unless event_edit_ok(\%evnt, $session);

		if (defined $cgi->param('save')) {
			my $whinge = sub { whinge($_[0], gen_edit_event_ppl($edit_id, $sessid, $etoken)) };
			my %accts = grep_acct_key('users', 'Name');
			my %neg_accts = grep_acct_key('accounts', 'IsNegated');

			my %seen_ppl;
			my @ppl;
			foreach (map { /^Pers_(.*)/; $1 } grep (/^Pers_.+$/, $cgi->param)) {
				(my $stripped = $_) =~ s/\..*$//;
				push (@ppl, $_) if validate_acct($stripped, \%accts, $whinge);
				$seen_ppl{$stripped}++;
			}
			foreach (map { /^Acct_(.*)/; $1 } grep (/^Acct_.+$/, $cgi->param)) {
				(my $stripped = $_) =~ s/\..*$//;
				push (@ppl, $_) if validate_acct($stripped, \%neg_accts, $whinge);
				$seen_ppl{$stripped}++;
			}
			$whinge->('Having duplicate people is silly') if grep ($_ > 1, values %seen_ppl);
			delete $evnt{Headings} unless scalar @ppl;
			@ppl = sort @ppl;
			if (exists $evnt{Headings}) {
				my %new_m;
				my %ppl_pos;
				push (@{$ppl_pos{$evnt{Person}[$_]}}, $_) foreach grep (defined $evnt{Person}[$_], 0 .. $#{$evnt{Person}});
				foreach my $p_n (0 .. $#ppl) {
					(my $pers = $ppl[$p_n]) =~ s/\..*$//;
					my $inst = ($ppl[$p_n] =~ /\.(\d*)$/) ? $1 - 1 : 0;
					my $row = $ppl_pos{$pers}[$inst];
					next unless defined $row;
					$new_m{$_}[$p_n] = $evnt{$_}[$row] foreach (@{$evnt{Headings}});
				}
				@{$evnt{$_}} = @{$new_m{$_}} foreach (@{$evnt{Headings}});
			} elsif (scalar @ppl) {
				@{$evnt{Headings}} = ( 'Person' );
			}
			@{$evnt{Person}} = map { s/\..*$//; $_ } (@ppl);

			my (%et, %ft);
			my $ft_prefix = '';
			if (defined $evnt{EventType} && $evnt{EventType} ne 'none') {
				%et = valid_event_type("$config{Root}/event_types/" . encode_for_filename($evnt{EventType}), \%cf);
				$ft_prefix = "$evnt{EventType}.";
			}
			%ft = valid_ft("$config{Root}/fee_tmpls/" . encode_for_filename("$ft_prefix$evnt{Template}"), \%cf) if defined $evnt{Template} && $evnt{Template} ne 'none';
			if (scalar @{$evnt{Person}} && %ft) {
				my %cds = known_commod_descs;
				my %drains = get_cf_drains(%cf);
				my ($fees, $exps) = get_event_types(\%et, \%drains);
				my @feecols = %et ? @$fees : grep (exists $cds{$_} || exists $drains{$_}, @{$cf{Fee}});

				splice (@{$evnt{Headings}}, 1, 0, 'CustomFee') if !grep ($_ eq 'CustomFee', @{$evnt{Headings}});	# necessary so subsequent ones added at position 2
				foreach my $unit (reverse @feecols) {
					splice (@{$evnt{Headings}}, 2, 0, $unit) if !grep ($_ eq $unit, @{$evnt{Headings}});
				}

				foreach my $p_n (0 .. $#ppl) {
					next if exists $neg_accts{$evnt{Person}[$p_n]};
					next if sum (map ((defined $evnt{$_}[$p_n]), @{$evnt{Headings}})) > 1;
					my %def_fees = get_ft_fees($evnt{Person}[$p_n], %ft);
					$evnt{$_}[$p_n] = $def_fees{$_} foreach (@feecols);
				}
			}
			foreach my $p_n (0 .. $#ppl) {
				$evnt{$_}[$p_n] //= 0 foreach (grep (!/^(Person|Notes)$/, @{$evnt{Headings}}));
			}

			my %tg;
			%tg = event_to_tg(%evnt) if (scalar @{$evnt{Person}});

			$whinge->('Unable to get commit lock') unless try_commit_lock($sessid);
			bad_token_whinge(gen_manage_events($session)) unless redeem_edit_token($sessid, "edit_$edit_id", $etoken);
			pop_session_data($sessid, "${etoken}_add_accts");
			try_commit_and_unlock(sub {
				update_event_tg($edit_id, \%tg);
				write_htsv($mt_file, \%evnt, 11);
				my @split_mf = split('-', unroot($mt_file));
				add_commit($mt_file, "$split_mf[0]...: Event \"$evnt{Name}\" participants modified", $session);
			}, $mt_file);
		}

		$mt_file =~ /\/([^\/]{1,4})[^\/]*$/;
		emit_with_status((defined $cgi->param('save')) ? "Saved edits to \"$evnt{Name}\" ($1) event participants" : 'Edit cancelled', gen_edit_event($edit_id, \%cf, $session, undef));
	}
	if ($cgi->param('tmpl') eq 'edit_event_hdrs') {
		my $edit_id = valid_edit_id(scalar $cgi->param('m_id'), "$config{Root}/events", 'event', sub { whinge($_[0], gen_manage_events($session)) }, 1);
		my $mt_file = "$config{Root}/events/$edit_id";

		if (defined $cgi->param('cancel')) {
			unlock($mt_file) if redeem_edit_token($sessid, "edit_$edit_id", $etoken) && $mt_file;
		}

		my %cf = valid_fee_cfg;
		whinge('Cannot display event: expenses config is broken', gen_manage_events($session)) unless %cf;

		my %evnt = read_htsv($mt_file, undef, [ 'Person', 'Notes' ]);

		whinge('Action not permitted', gen_edit_event($edit_id, \%cf, $session, undef)) unless event_edit_ok(\%evnt, $session, 1);

		if (defined $cgi->param('save')) {
			my $whinge = sub { whinge($_[0], gen_edit_event_hdrs($edit_id, \%cf, $etoken)) };

			my %ppl = grep_acct_key('users', 'Name');

			$evnt{Name} = clean_words($cgi->param('name'));
			$evnt{Date} = validate_date(scalar $cgi->param('date'), $whinge);
			$evnt{Duration} = validate_int(scalar $cgi->param('duration'), 'Duration', 1, $whinge);
			$evnt{Leader} = validate_acct(scalar $cgi->param('leader'), \%ppl, $whinge);
			delete $evnt{EventType};
			delete $evnt{Template};
			if ($cgi->param('fee_tmpl') && $cgi->param('fee_tmpl') =~ /(.*)\.(.*)/) {
				my $et = ($1 eq 'none') ? undef : valid_edit_id($1, "$config{Root}/event_types", 'event type', $whinge, 1);
				my $ft = ($2 eq 'none') ? undef : valid_edit_id($et ? "$et.$2" : $2, "$config{Root}/fee_tmpls", 'fee template', $whinge, 1);
				$ft =~ s/^$et\.// if $et;
				$evnt{EventType} = $et if $et;
				$evnt{Template} = $ft if $ft;
			}

			$whinge->('No event name given') unless length $evnt{Name};
			$whinge->('Zero duration?') unless $evnt{Duration} > 0;

			my %tg;
			%tg = event_to_tg(%evnt) if $evnt{Person} and (scalar @{$evnt{Person}});

			$whinge->('Unable to get commit lock') unless try_commit_lock($sessid);
			bad_token_whinge(gen_manage_events($session)) unless redeem_edit_token($sessid, "edit_$edit_id", $etoken);
			try_commit_and_unlock(sub {
				update_event_tg($edit_id, \%tg);
				write_htsv($mt_file, \%evnt, 11);
				my @split_mf = split('-', unroot($mt_file));
				add_commit($mt_file, "$split_mf[0]...: Event \"$evnt{Name}\" headers modified", $session);
			}, $mt_file);
		}

		$mt_file =~ /\/([^\/]{1,4})[^\/]*$/;
		emit_with_status((defined $cgi->param('save')) ? "Saved edits to \"$evnt{Name}\" ($1) event headers" : 'Edit cancelled', gen_edit_event($edit_id, \%cf, $session, undef));
	}
	if ($cgi->param('tmpl') eq 'edit_acct') {
		my $person = defined $cgi->param('email');
		my $root = $config{Root};
		my $acct_path = $person ? "$root/users" : "$root/accounts";
		my $edit_acct = valid_edit_id(scalar $cgi->param('eacct'), $acct_path, 'account', sub { whinge($_[0], gen_manage_accts($person)) });
		my $file = $edit_acct ? "$acct_path/$edit_acct" : undef;
		my $new_acct;

		whinge('Action not permitted', gen_ucp($session)) unless $session->param('IsAdmin') || (!$edit_acct && $person && peek_session_data($sessid, $etoken));

		if (defined $cgi->param('save') || defined $cgi->param('savenadd')) {
			my $whinge = sub { whinge($_[0], gen_add_edit_acc($edit_acct, $person, $session, $etoken, !$session->param('IsAdmin'))) };

			my %addr_alts = read_htsv("$config{Root}/config_addr_alts", 1);
			$new_acct = validate_acctname(scalar $cgi->param('account'), $whinge);
			my $fullname = clean_words($cgi->param('fullname'));
			my $email = clean_email($cgi->param('email'));
			my $address = clean_text($cgi->param('address'));
			my $nalts = grep (length $cgi->param($_), @{$addr_alts{Headings}});
			my $rename = ($edit_acct and $edit_acct ne $new_acct);
			my $old_file = $file;
			$file = "$acct_path/$new_acct";

			$whinge->('Short name is already taken') if ((-e "$root/accounts/$new_acct" or -e "$root/users/$new_acct") and ((not defined $edit_acct) or $rename));
			$whinge->('Full name too short') unless defined $fullname;
			$whinge->('Full name too long') if length $fullname > 100;
			if ($person) {
				$whinge->('Not an email address') unless defined $email;
				$whinge->('No real-world contact details given') unless defined $address || $nalts;
			}

			my %userdetails;
			%userdetails = read_simp_cfg($old_file) if ($edit_acct);
			$userdetails{Name} = $fullname;
			if ($person) {
				$userdetails{email} = $email;
				$address ? $userdetails{Address} = $address : delete $userdetails{Address};
				foreach my $alt (@{$addr_alts{Headings}}) {
					if (length $cgi->param($alt)) {
						my $want = encode_for_html($cgi->param($alt));
						my $row = first { defined $addr_alts{$alt}[$_] && $addr_alts{$alt}[$_] eq $want } 0 .. $#{$addr_alts{$alt}};
						$whinge->('"' . $cgi->param($alt) . "\" is not a known $alt") unless defined $row;
						$userdetails{$alt} = $addr_alts{$alt}[$row];
					} else {
						delete $userdetails{$alt};
					}
				}
				(defined $cgi->param($_)) ? $userdetails{$_} = undef : delete $userdetails{$_} foreach (grep ($_ ne 'IsPleb', get_attrs));
			} else {
				(mkdir $acct_path or die) unless (-d $acct_path);
				(defined $cgi->param('is_negated')) ? $userdetails{IsNegated} = undef : delete $userdetails{IsNegated};
			}

			$whinge->('Unable to get commit lock') unless try_commit_lock($sessid);
			if ($rename) {
				unlock_dir('transaction_groups', $sessid, $whinge, 'account rename', 'transaction groups');
				unlock_dir('events', $sessid, $whinge, 'account rename', 'events');
				unlock_dir('event_types', $sessid, $whinge, 'account rename', 'event types');
				if (-e "$config{Root}/.config_fees.lock" && clear_lock("$config{Root}/.config_fees.lock", $sessid)) {
					un_commit_lock;
					$whinge->('Cannot perform account rename at present: config_fees busy');
				}
			}
			bad_token_whinge(gen_manage_accts($person)) unless redeem_edit_token($sessid, $edit_acct ? "edit_$edit_acct" : $person ? 'add_acct' : 'add_vacct', $etoken);
			try_commit_and_unlock(sub {
				if ($rename) {
					dir_mod_all('transaction_groups', 1, [ $edit_acct ], sub { my ($tg, $old) = @_; foreach (@{$tg->{Creditor}}, @{$tg->{Headings}}) { s/^$old$/$new_acct/ if $_; } $tg->{$new_acct} = delete $tg->{$old} if exists $tg->{$old}; });
					dir_mod_all('events', 0, [ $edit_acct ], sub { my ($evnt, $old) = @_; $evnt->{Leader} =~ s/^$old$/$new_acct/ if defined $evnt->{Leader}; foreach (@{$evnt->{Person}}) { s/^$old$/$new_acct/ if $_; } }, 11);
					dir_mod_all('event_types', 0, [ $edit_acct ], sub { my ($et, $old) = @_; $et->{LinkedAcct} =~ s/^$old$/$new_acct/ if defined $et->{LinkedAcct}; });
					my %cf = read_htsv("$config{Root}/config_fees", 1);
					if (%cf) {
						$cf{DefaultAccount} =~ s/^$edit_acct$/$new_acct/ if defined $cf{DefaultAccount};
						if (exists $cf{Account}) {
							foreach (@{$cf{Account}}) {
								s/^$edit_acct$/$new_acct/ if $_;
							}
						}

						write_htsv("$config{Root}/config_fees", \%cf, 11);
						$git->add("$config{Root}/config_fees");
					}
					$git->mv($old_file, $file);
				}
				write_simp_cfg($file, %userdetails);
				if ($rename) {
					add_commit($file, 'Rename ' . unroot($old_file) . ' to ' . unroot($file), $session);
				} else {
					add_commit($file, unroot($file) . ': ' . ($edit_acct ? 'modified' : 'created'), $session);
				}
			}, $rename ? $old_file : ($edit_acct) ? $file : undef);

			refresh_session($session, $new_acct, $session->param('IsAuthed')) if (defined $edit_acct) && $edit_acct eq $session->param('User');

			my $net = peek_session_data($sessid, $etoken);
			if ($net) {
				my $adds = pop_session_data($sessid, "${net}_add_accts");
				$adds = $adds ? "$adds.$new_acct" : $new_acct;
				push_session_data($sessid, "${net}_add_accts", $adds);
			}
		} else {
			unlock($file) if redeem_edit_token($sessid, $edit_acct ? "edit_$edit_acct" : $person ? 'add_acct' : 'add_vacct', $etoken) && $file;
		}

		if ($edit_acct) {
			emit_with_status((defined $cgi->param('save')) ? "Saved edits to account \"$new_acct\"" : 'Edit account cancelled', gen_manage_accts($person));
		} else {
			$etoken = pop_session_data($sessid, $etoken);
			if (defined $cgi->param('savenadd')) {
				$etoken = get_edit_token($sessid, $person ? 'add_acct' : 'add_vacct', $etoken);
				emit_with_status("Added account \"$new_acct\"", gen_add_edit_acc(undef, $person, $session, $etoken, !$session->param('IsAdmin')));
			}
			my $edit_id = $etoken ? pop_session_data($sessid, "${etoken}_editid") : undef;
			my $tmpl = $etoken ? gen_edit_event_ppl($edit_id, $sessid, $etoken) : gen_manage_accts($person);
			emit_with_status((defined $cgi->param('save')) ? "Added account \"$new_acct\"" : 'Add account cancelled', $tmpl);
		}
	}

	return;
}

sub fix_newest
{
	my $ref = fmtime('newest');
	my $max = untaint (max map (((stat)[9] // 0), grep (-f, glob ("$config{Root}/* $config{Root}/*/*"))));
	if ($max > $ref) {
		flock_wc("$config{Root}/newest", {});
		utime ($max, $max, "$config{Root}/newest");
	}

	return;
}

sub clear_caches
{
	my ($filename) = @_;

	flock_wc("$config{Root}/newest", {});	# effectively `touch'
	# the approach here is to ensure in-process caches are consistent WITHOUT threads:
	# we would need more locking for threading with shared caches...
	undef %tgds;
	undef %pres;
	undef %evs;
	clear_cache_tg;
	clear_cache_accts if $filename =~ /(users|accounts)\/[a-z0-9\-+_]*$/;

	return;
}

set_htsv_callbacks(\&read_htsv_encode, \&write_htsv_encode, \&clear_caches);
my $cgi = CGI->new;

%config = read_simp_cfg('boc_config');

die 'Can\'t find value for "Root" key in ./boc_config' unless defined $config{Root};
die 'Can\'t find value for "TemplateDir" key in ./boc_config' unless defined $config{TemplateDir};
die "The BoC root directory (set as $config{Root} in ./boc_config) must exist and be readable and writable by the webserver --" unless (-r $config{Root} and -w $config{Root});
$ENV{HTML_TEMPLATE_ROOT} = $config{TemplateDir};

emit(load_template(untaint($cgi->param('serve')) . '.html')) if defined $cgi->param('serve') && !($cgi->param('serve') =~ /\./) && -r "$config{TemplateDir}/" . $cgi->param('serve') . ".html";
serve("$config{TemplateDir}/" . untaint($cgi->param('serve')) . '.js', 'application/javascript') if defined $cgi->param('serve') && !($cgi->param('serve') =~ /\./) && -r "$config{TemplateDir}/" . $cgi->param('serve') . ".js";
serve("$config{TemplateDir}/" . untaint($cgi->param('serve')) . '.css', 'text/css') if defined $cgi->param('serve') && !($cgi->param('serve') =~ /\./) && -r "$config{TemplateDir}/" . $cgi->param('serve') . ".css";

$ENV{PATH} = '/bin:/usr/bin';
$git = Git::Wrapper->new($config{Root});
update_global_config(read_simp_cfg("$config{Root}/config", 1));

set_accts_config_root($config{Root});
init_attr_cfg("$config{Root}/config_pers_attrs");
init_units_cfg("$config{Root}/config_units");
set_event_config_root($config{Root});

create_datastore($cgi, "$config{Root} does not appear to be a BoC data store") unless (-d "$config{Root}/users");
create_datastore($cgi, 'No useable administrator account') unless scalar grep (defined, grep_acct_key('users', 'IsAdmin', 'Password'));

CGI::Session->name(sha1_hex($config{Root}));
my $session = CGI::Session->load($cgi) or die CGI::Session->errstr;
$session = get_new_session($session, $cgi) if ($session->is_empty || !(defined $cgi->param('tmpl')) || $cgi->param('tmpl') =~ m/^login(_nopw)?$/ || $session->param('Instance') ne $config{Root});
refresh_session($session, $session->param('User'), $session->param('IsAuthed')) if fmtime('users/' . $session->param('User')) > $session->param('AcctMtime');

fix_newest;

despatch($session);

# the despatchers fall through if the requested action is unknown: make them log in again!
get_new_session($session, $cgi);
