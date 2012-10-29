#!/usr/bin/perl -T

use 5.014;	# get guaranteed correct exception handling
use autodie;
use warnings;

use Fcntl qw(O_RDWR O_WRONLY O_EXCL O_CREAT LOCK_EX LOCK_NB SEEK_SET);
use CGI qw(param);
use CGI::Carp qw(fatalsToBrowser);
use File::Find;
use List::Util qw(first min sum);
use Time::HiRes qw(usleep);

# non core
use CGI::Session '-ip-match';
use Crypt::Cracklib;
use Crypt::PasswdMD5;
use File::Slurp;
use Git::Wrapper;
use HTML::Template;
use Time::ParseDate;
use UUID::Tiny;
use YAML::XS;

use lib '.';
use Accts;
use Attrs;
use CleanData qw(untaint encode_for_commit encode_for_file encode_for_filename encode_for_html transcode_uri_for_html clean_date clean_email clean_filename clean_int clean_text clean_unit clean_username clean_word clean_words true validate_acct validate_acctname validate_date validate_decimal validate_int validate_unitname validate_unit);
use Events;
use HeadedTSV;
use TG;
use Units;

my %config;
my $git;
my %tgds;

sub update_global_config
{
	my (%append_cfg) = @_;
	@config{keys %append_cfg} = values %append_cfg;	# merge settings
	$config{LongName} //= 'Set LongName in installation config!';
	$config{ShortName} //= 'Set ShortName in installation config!';
	return;
}

sub flock_only
{
	sysopen(my $fh, $_[0], O_RDWR|O_CREAT) or die;
	flock ($fh, LOCK_EX) or die;

	return $fh;
}

sub flock_and_read
{
	my $filename = $_[0];

	sysopen(my $fh, $filename, O_RDWR|O_CREAT) or die;
	flock ($fh, LOCK_EX) or die;

	my $data = read_file($fh);
	my %datah = Load($data);

	return ($fh, %datah);
}

sub write_and_close
{
	my ($fh, %datah) = @_;

	my $data = Dump(%datah);
	seek ($fh, 0, SEEK_SET);
	truncate ($fh, 0);
	return write_file($fh, $data);	# write_file does close() for us
}

sub push_session_data
{
	my ($sessid, $key, $value) = @_;

	my $file = File::Spec->tmpdir() . '/' . sprintf("${CGI::Session::Driver::file::FileName}_bocdata", $sessid);

	my ($fh, %data) = flock_and_read($file);
	$data{$key} = $value;

	return write_and_close($fh, %data);
}

sub pop_session_data
{
	my ($sessid, $key) = @_;

	my $file = File::Spec->tmpdir() . '/' . sprintf("${CGI::Session::Driver::file::FileName}_bocdata", $sessid);

	my ($fh, %data) = flock_and_read($file);

	unless (defined $data{$key}) {
		close ($fh);
		return undef;
	}

	my $value = $data{$key};
	delete $data{$key};

	write_and_close($fh, %data);

	return $value;
}

sub peek_session_data
{
	my ($sessid, $key) = @_;

	my $file = File::Spec->tmpdir() . '/' . sprintf("${CGI::Session::Driver::file::FileName}_bocdata", $sessid);

	my ($fh, %data) = flock_and_read($file);
	close ($fh);

	return $data{$key};
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
	my ($file, $sessid) = @_;
	my $lockfile = "$file.lock";
	$lockfile =~ s/^(.*\/)([^\/]*)/$1.$2/;	# insert a . to hide file (especially from directory globbing)
	my $lock;

	no autodie qw(sysopen open);	# sysopen and open are intended to fail sometimes
	unless (sysopen ($lock, $lockfile, O_WRONLY | O_EXCL | O_CREAT)) {	# we assume it's not on NFSv2
		my $mtime = (stat($lockfile))[9];

		return undef if defined $mtime and (time() - $mtime) < 600;

		return undef unless open ($lock, '+>', $lockfile);
		return undef unless flock ($lock, LOCK_EX | LOCK_NB);
	}

	print $lock $sessid;

	close ($lock);

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

sub try_lock
{
	my ($file, $sessid) = @_;

	return undef unless try_commit_lock($sessid);
	my $rv = try_lock_raw($file, $sessid);
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

sub read_tg2
{
	my ($tg_file) = @_;

	return read_tg($tg_file) unless $tg_file =~ /.*\/M([^\/]+)$/ && -e "$config{Root}/meets/$1";

	return meet_to_tg(%{{read_htsv("$config{Root}/meets/$1", undef, [ 'Person', 'Notes' ])}});
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
		eval { find({ wanted => sub { /^(.*\.new)$/ and unlink $1 }, untaint => 1}, $config{Root}) } unless $@;
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
	my ($tg, $omit, $neg_accts, $resolved, $die) = @_;

	if (-r "$config{Root}/transaction_groups/$tg" && -r "$config{Root}/transaction_groups/.$tg.precomp" && (-M "$config{Root}/transaction_groups/.$tg.precomp" < -M "$config{Root}/transaction_groups/$tg") && (-M "$config{Root}/transaction_groups/.$tg.precomp" < -M "$config{Root}/config_units")) {
		my ($fh, %computed) = flock_and_read("$config{Root}/transaction_groups/.$tg.precomp");
		close $fh;
		return %computed;
	} else {
		my %tgdetails = %{$tgds{$tg}};
		return if $omit && exists $tgdetails{Omit};

		my %computed = compute_tg($tg, \%tgdetails, undef, $neg_accts, $resolved, $die);

		# check for drains directly; this means resolution can be done without account validation,
		# and account validation can be done separately from resolution
		my $is_drain = 0;
		foreach (0 .. $#{$tgdetails{Creditor}}) {
			$is_drain = 1 if $tgdetails{Amount}[$_] =~ /^\s*[*]\s*$/ && !($tgdetails{Creditor}[$_] =~ /^TrnsfrPot\d$/);
		}
		if (!(exists $tgdetails{Omit}) && !$is_drain) {
			my $fh = flock_only("$config{Root}/transaction_groups/.$tg.precomp");
			write_and_close($fh, %computed);
		}

		return %computed;
	}
}

sub drained_accts
{
	my ($exempt, $to_zero_only) = @_;
	$exempt = '' unless $exempt;
	my %drained;

	foreach my $tg (glob ("$config{Root}/transaction_groups/*")) {
		$tg = $1 if $tg =~ /([^\/]*)$/;
		$tgds{$tg} = \%{{read_tg2("$config{Root}/transaction_groups/$tg")}} unless exists $tgds{$tg};
		my %tgdetails = %{$tgds{$tg}};
		next if exists $tgdetails{Omit};

		foreach (0 .. $#{$tgdetails{Creditor}}) {
			push (@{$drained{$tgdetails{Creditor}[$_]}}, $tg) if (defined $tgdetails{Creditor}[$_] && $tgdetails{Amount}[$_] =~ /^\s*[*]\s*$/ && !($tgdetails{Creditor}[$_] =~ /^TrnsfrPot\d$/)) && $tg ne $exempt && !($to_zero_only && $tgdetails{$tgdetails{Creditor}[$_]}[$_]);
		}
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
	my ($n, $places) = @_;
	my $sign = ($n < 0) ? '-' : '';
	my $abs = abs $n;

	return $sign . substr ($abs + ('0.' . '0' x $places . '5'), 0, $places + length (int ($abs)) + 1);
}

sub resolve_accts
{
	my ($ddsr, $nar) = @_;
	my %dds = %{$ddsr};
	my %neg_accts = %{$nar};
	my %das = drained_accts(undef, 1);
	my %resolved;
	my $loops = 50;

	while ($loops--) {
		my %running;

		foreach my $tg (glob ("$config{Root}/transaction_groups/*")) {
			$tg = $1 if $tg =~ /([^\/]*)$/;
			next if exists $dds{$tg};
			my %computed = eval { compute_tg_c($tg, 1, \%neg_accts, \%resolved) };
			return if $@;
			foreach (keys %computed) {
				$running{$_} = 0 unless exists $running{$_};
				$running{$_} += $computed{$_};
			}
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

		return %resolved if nonfinite(values %resolved) == 0 || nonfinite(values %resolved) == $unresolved;
	}

	return;
}

sub load_template
{
	my $tmpl = HTML::Template->new(filename => "$_[0]", global_vars => 1, case_sensitive => 1) or die;
	$tmpl->param(SN => $config{ShortName}) if $tmpl->query(name => 'SN');
	$tmpl->param(LN => $config{LongName}) if $tmpl->query(name => 'LN');
	$tmpl->param(STYLE => $config{StyleURL}) if $tmpl->query(name => 'STYLE');
	$tmpl->param(ETOKEN => $_[1]) if defined $_[1];
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
	$tmpl->param(STATUS => encode_for_html("Status: $status"));
	print "Content-Type: text/html\n\n", $tmpl->output;
	exit;
}

sub whinge
{
	my ($whinge, $tmpl) = @_;
	$tmpl->param(STATUS => encode_for_html($whinge));
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

sub validate_admins
{
	my @users = grep { (my $acct = $_) =~ s/^.*\///; clean_username($acct) } glob ("$config{Root}/users/*");

	my @valid_admins;
	foreach my $user (@users) {
		my %userdetails = read_simp_cfg($user);
		push (@valid_admins, $user) if (exists $userdetails{IsAdmin} and defined $userdetails{Password});
	}

	return scalar @valid_admins;
}

sub login
{
	my $cgi = $_[0];
	my $user = clean_username($cgi->param('user'));
	my $pass = $cgi->param('pass');
	my $whinge = sub { whinge('Login failed!', load_template('login.html')) };

	$whinge->() unless $user and (-r "$config{Root}/users/$user");
	my %userdetails = read_simp_cfg("$config{Root}/users/$user");
	$whinge->() unless defined $userdetails{Password};

	my ($empty, $id, $salt, $encrypted) = split(/\$/, $userdetails{Password}, 4);

	my $cryptpass = unix_md5_crypt($pass, $salt);

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
	return 'No PW login on account with password set?' if defined $userdetails{Password};

	$userdetails{User} = $user;
	%{$userdetout} = %userdetails;
	return 'ok';
}

sub clear_old_session_locks
{
	my $sessid = $_[0];
	my @locks = glob ("$config{Root}/*/.*.lock");
	push (@locks, "$config{Root}/.DSLOCK.lock");

	no autodie qw(open);	# file may not exist
	foreach my $lockfile (@locks) {
		$lockfile = untaint($lockfile);
		next unless open (my $lock, '<', $lockfile);

		unlink ($lockfile) if $sessid eq <$lock>;

		close ($lock);
	}

	return;
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
	if ($last_tmpl eq 'login_nopw' and exists $config{Passwordless}) {
		$tmpl = load_template('login.html') if (login_nopw($cgi, \%userdetails) eq 'No PW login on account with password set?');
	} elsif ($last_tmpl eq 'login') {
		%userdetails = login($cgi);
	} else {
		$tmpl = (exists $config{Passwordless}) ? gen_login_nopw : load_template('login.html');
	}
	($expired ? whinge('Session expired', $tmpl) : emit($tmpl)) if $tmpl;

	my %attr_syns = get_attr_synonyms;
	my @sys_attrs = get_sys_attrs;
	my %perms;
	foreach my $sysattr (@sys_attrs) {
		$perms{$sysattr} = grep (($_ eq 'IsPleb' || exists $userdetails{$_}), @{$attr_syns{$sysattr}});
	}

	$session = CGI::Session->new($cgi) or die CGI::Session->errstr;
	print $session->header();
	$session->param('User', $userdetails{User});
	$session->param('Name', exists $userdetails{Name} ? $userdetails{Name} : $userdetails{User});
	$session->param($_, $perms{$_}) foreach (@sys_attrs);
	$session->param('Instance', $config{Root});
	$session->expire('+10m');
	$session->flush();

	return $session;
}

sub valid_fee_cfg
{
	local $_;
	return unless -r "$config{Root}/config_fees";

	my %cf = read_htsv("$config{Root}/config_fees");

	my %acct_names = get_acct_name_map;
	my $bad = 0;
	my $whinge = sub { $bad = 1 };
	validate_acct($cf{MeetAccount}, \%acct_names, $whinge);
	return if $bad;

	return %cf unless exists $cf{Headings};

	foreach my $hd ('Fee', 'IsBool', 'IsDrain', 'Account', 'Description') {
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
		} else {
			return if true($cf{IsBool}) && !true($cf{IsDrain});
			return unless defined $cf{Description}[$row] && length $cf{Description}[$row];
		}
	}

	return %cf;
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
	validate_units(\%units_cfg, sub { $tmpl->param(STATUS => 'Units config broken: fix it!') }, 1);

	my %vaccts = grep_acct_key('accounts', 'Name');
	my %cf = valid_fee_cfg;
	$tmpl->param(VACCTS => scalar keys %vaccts, MEETS => !!%cf, COMMODS => ((scalar keys %{{known_commod_descs}}) + (scalar keys %{{get_cf_drains(%cf)}})), CF_UNITS => (exists $cf{Fee} && scalar @{$cf{Fee}}));

	return $tmpl;
}

sub gen_manage_accts
{
	my $people = $_[0];
	my $tmpl = load_template('manage_accts.html');
	my @accounts = $people ? glob ("$config{Root}/users/*") : glob ("$config{Root}/accounts/*");
	my @acctlist;
	my @attrs_list = get_attrs;

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
	my ($edit_acct, $person, $etoken) = @_;
	my $tmpl = load_template('edit_acct.html', $etoken);
	my %acctdetails;
	my %addr_alts = read_htsv("$config{Root}/config_addr_alts", 1);

	if ($edit_acct) {
		$tmpl->param(EACCT => $edit_acct);
		%acctdetails = read_simp_cfg($person ? "$config{Root}/users/$edit_acct" : "$config{Root}/accounts/$edit_acct");
		$tmpl->param(ACCT => $edit_acct);
		$tmpl->param(NAME => $acctdetails{Name});
		$tmpl->param(EMAIL => $acctdetails{email});
		$tmpl->param(ADDRESS => $acctdetails{Address});
		$tmpl->param(IS_NEGATED => 1) if exists $acctdetails{IsNegated};
	}
	my %attrs = get_attrs_full;
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
	my $tmpl = load_template('edit_inst_cfg.html', $_[0]);
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

	my @list;
	foreach my $et_f (map { /.*\/([^\/]*)/; $1 } glob ("$config{Root}/event_types/*")) {
		my %et = read_htsv("$config{Root}/event_types/$et_f", undef, [ 'Unit' ]);
		my ($fees, $exps) = get_event_types(\%et, \%drain_descs);
		my @cols = map ((defined $comb_descs{$_} && length $comb_descs{$_}) ? $comb_descs{$_} : $_, (@$fees, @$exps));
		push (@list, { ET => $et_f, NAME => transcode_uri_for_html($et_f), NAME_CL => ($et_f eq 'none' || $et_f =~ /[.]/) ? 'broken' : '', COLS => join (', ', @cols), CL => (scalar grep (!(exists $comb_exists{$_}), (@$fees, @$exps))) ? 'broken' : '' });
	}
	$tmpl->param(ETS => \@list);

	return $tmpl;
}

sub gen_edit_et
{
	my ($edit_id, $etoken) = @_;
	my $tmpl = load_template('edit_event_type.html', $etoken);

	my %et;
	%et = read_htsv("$config{Root}/event_types/$edit_id", undef, [ 'Unit' ]) if $edit_id;

	$tmpl->param(NAME => transcode_uri_for_html($edit_id));

	my %cds = known_commod_descs;
	my %cf = valid_fee_cfg;
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
		push (@fees, { CODE => $et{Unit}[$row], UNIT => (exists $drains{$et{Unit}[$row]}) ? @{$cf{Description}}[$dr_row] : $cds{$et{Unit}[$row]} // $et{Unit}[$row], N => $row, C_CL => $unit_cl, COL => (defined $et{Column}[$row] && $et{Column}[$row] == 99999999) ? -1 : $ord * 10 + 10, EX => true($et{Unusual}[$row]) });
	}
	foreach my $ord (0 .. $#$exp_rows) {
		my $row = @$exp_rows[$ord];
		my $exp_row = (grep (@{$cf{Fee}}[$_] eq $et{Unit}[$row], grep (!exists $drains{$et{Unit}[$row]}, 0 .. $#{$cf{Fee}})))[0];
		push (@exps, { CODE => $et{Unit}[$row], UNIT => (defined $exp_row) ? @{$cf{Description}}[$exp_row] : $et{Unit}[$row], N => $row, C_CL => $exp_row ? '' : 'broken', COL => (defined $et{Column}[$row] && $et{Column}[$row] == 99999999) ? -1 : $ord * 10 + 10, EX => true($et{Unusual}[$row]) });
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

	my %rawattrs = get_attrs_full(1);
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
		my @currencies = map ({ C => $_, S => ($_ eq $ft{Unit}[$row]) }, $unk_cur ? (@units, $ft{Unit}[$row]) : @units);
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

	my @accts = map ({ O => $vaccts{$_}, V => $_, S => (defined $cfg{MeetAccount} && $cfg{MeetAccount} eq $_) }, @sorted_vaccts);
	unless (defined $cfg{MeetAccount} && grep ($_ eq $cfg{MeetAccount}, @sorted_vaccts)) {
		push (@accts, { O => $cfg{MeetAccount}, V => $cfg{MeetAccount}, S => 1 });
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
		push (@feerows, { COMMOD => $commod, R => $row, FEEID => $fees[$row], FEED => $commod ? $cds{$fees[$row]} : $cfg{Description}[$cf_row], BOOL => (defined $cf_row && true($cfg{IsBool}[$cf_row])), DRAIN => (defined $cf_row && true($cfg{IsDrain}[$cf_row])), UNKACCTS => \@unkaccts, PPLACCTS => \@pplaccts, VACCTS => \@vacctaccts, ID_CL => $broken_fee ? 'broken' : '', DESC_CL => (!$commod && !(defined $cfg{Description}[$cf_row] && length $cfg{Description}[$cf_row])) ? 'broken' : '', BD_CL => (!$commod && true($cfg{IsBool}[$cf_row]) && !true($cfg{IsDrain}[$cf_row])) ? 'broken' : '', ACCT_CL => $broken_acct ? 'broken' : '' });
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
	foreach my $attr (@sorted_attrs, 'IsPleb') {
		my @imps = map { my $a = $_; { I => $_, C => ($_ eq $attr || defined $cfg{$attr} && !!grep (/\s*$a\s*/, split (':', $cfg{$attr}))), NO => ($_ eq $attr) }; } @sorted_attrs;
		my @simps = map { my $a = $_; { I => $_, C => ($_ eq $attr || defined $cfg{$attr} && !!grep (/\s*$a\s*/, split (':', $cfg{$attr}))), NO => ($_ eq $attr), CL => 'system' }; } get_sys_attrs;
		my @nimps = map { my $a = $_; { I => $_, C => ($_ eq $attr || defined $cfg{$attr} && !!grep (/\s*$a\s*/, split (':', $cfg{$attr}))), NO => ($_ eq $attr), CL => 'unknown' }; } @extra_attrs;
		push (@imps, (@simps, @nimps));
		push (@attrs, { A => $attr, IMPS => \@imps });
	}
	$tmpl->param(NIMPS => scalar @impsh, IMPSH => \@impsh, ATTRS => \@attrs);

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

	my %cfg = read_units_cfg("$config{Root}/config_units.p1");
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
		unlock_dir('meets', $sessid, $whinge, 'unit recode', 'meets');
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
			dir_mod_all('meets', 0, \@renames, sub { my ($meet, $old) = @_;
				$meet->{Currency} =~ s/^$old$/$rename->{$old}/ if defined $meet->{Currency};
				s/^$old$/$rename->{$old}/ foreach (@{$meet->{Headings}});
				$meet->{$rename->{$old}} = delete $meet->{$old} if exists $meet->{$old}; }, 11);
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

sub gen_manage_meets
{
	my $session = $_[0];
	my $tmpl = load_template('manage_meets.html');
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

	my @meetlist;
	foreach my $mid (date_sorted_htsvs('meets')) {
		my %meet = read_htsv("$config{Root}/meets/$mid", undef, [ 'Person', 'Notes' ]);
		my $leader = (defined $meet{Leader}) ? ((exists $ppl{$meet{Leader}}) ? $ppl{$meet{Leader}} : $meet{Leader}) : '';
		$meet{EventType} //= 'none';
		$meet{Template} //= 'none';
		my $et_state = $meet{EventType} eq 'none' || !!grep ($_ eq $meet{EventType}, @etfs);
		my $ft_prefix = ($meet{EventType} ne 'none') ? "$meet{EventType}." : '';
		my $ft_state = $meet{Template} eq 'none' || !!grep ($_ eq "$ft_prefix$meet{Template}", @ftfs);
		my $ft_exists = $meet{Template} ne 'none' && -r "$config{Root}/fee_tmpls/" . encode_for_filename("$ft_prefix$meet{Template}");

		push (@meetlist, { MID => $mid, NAME => $meet{Name}, M_CL => (defined $meet{Name} && meet_valid(\%meet, \%cf)) ? '' : 'broken', DATE => $meet{Date}, D_CL => (defined clean_date($meet{Date})) ? '' : 'broken', LEN => $meet{Duration}, LEN_CL => (defined $meet{Duration}) ? '' : 'broken', LDR_CL => (defined $meet{Leader} && exists $ppl{$meet{Leader}}) ? '' : 'unknown', LEADER => $leader, FT_CL => ($et_state && $ft_state) ? '' : 'unknown', FT => format_ft_name("$ft_prefix$meet{Template}"), FTID => ($session->param('IsAdmin') && $ft_exists) ? encode_for_filename("$ft_prefix$meet{Template}") : '' });
	}
	my @people = map ({ A => $_, N => $ppl{$_} }, sort_AoH(\%ppl));
	my @ftlist;
	foreach my $et (sort keys %fts) {
		push (@ftlist, map ({ FTID => $_, FT => format_ft_name($_) }, map ("$et.$_", @{$fts{$et}})));
	}

	$tmpl->param(MEETS => \@meetlist, PPL => \@people, FTS => \@ftlist, ADDDELOK => $session->param('IsAdmin'));

	return $tmpl;
}

sub gen_edit_meet
{
	my ($edit_id, $mcr, $session, $etoken) = @_;

	my $tmpl = load_template('edit_meet.html', $etoken);
	my %meet = read_htsv("$config{Root}/meets/$edit_id", undef, [ 'Person', 'Notes' ]);

	$tmpl->param(MID => $edit_id);
	$tmpl->param(RO => !$etoken);
	$tmpl->param(NAME => $meet{Name}, DATE => $meet{Date}, DUR => $meet{Duration});

	my %units_cfg = read_units_cfg("$config{Root}/config_units");
	my @units = known_units(%units_cfg);

	my $sel_cur = $units_cfg{Default};
	if (exists $meet{Currency}) {
		$sel_cur = $meet{Currency};
		if (@units) {
			$sel_cur = (scalar @units > 1) ? '' : $units_cfg{Default} unless defined $meet{Currency};
		} else {
			push (@units, 'N/A') if defined $meet{Currency};
		}
	}
	my $red_unit;

	if (defined $sel_cur && !grep ($_ eq $sel_cur, @units)) {
		$red_unit = 1;
		push (@units, $sel_cur);
	}

	my @currencies = map ({ C => $_, D => $units_cfg{$_}, S => $sel_cur eq $_ }, @units);
	$tmpl->param(CURS => \@currencies, CUR_CL => $red_unit ? 'unknown' : '');

	my %meet_cfg = %$mcr;
	my %cds = known_commod_descs;

	my %et;
	%et = valid_event_type("$config{Root}/event_types/" . encode_for_filename($meet{EventType}), $mcr) if defined $meet{EventType} && $meet{EventType} ne 'none';
	my %drains = get_cf_drains(%meet_cfg);

	my (@ccs, @exps);
	if (%et) {
		my ($fees, $exps) = get_event_types(\%et, \%drains);
		@ccs = map { my $fee = $_; (grep ($fee eq $meet_cfg{Fee}[$_], 0 .. $#{$meet_cfg{Fee}}))[0] } (@$fees);
		@exps = map { my $fee = $_; (grep ($fee eq $meet_cfg{Fee}[$_], 0 .. $#{$meet_cfg{Fee}}))[0] } (@$exps);
	} else {
		@ccs = grep (exists $cds{$meet_cfg{Fee}[$_]}, 0 .. $#{$meet_cfg{Fee}});
		push (@ccs, grep (!(exists $cds{$meet_cfg{Fee}[$_]}) && true($meet_cfg{IsDrain}[$_]), 0 .. $#{$meet_cfg{Fee}}));
		@exps = grep (!(exists $cds{$meet_cfg{Fee}[$_]} || true($meet_cfg{IsDrain}[$_])), 0 .. $#{$meet_cfg{Fee}});
	}
	my @unks;
	foreach my $hd (grep (!/^(Person|CustomFee|Notes)$/, @{$meet{Headings}})) {
		push (@unks, $hd) unless grep ($meet_cfg{Fee}[$_] eq $hd, (@ccs, @exps));
	}

	my @feesh = ({ FEE => 'Custom Fee', LINKA => $meet_cfg{MeetAccount} });
	push (@feesh, map ({ FEE => (exists $cds{$meet_cfg{Fee}[$_]}) ? $cds{$meet_cfg{Fee}[$_]} : $meet_cfg{Description}[$_], LINKA => $meet_cfg{Account}[$_] }, @ccs));
	my @expsh = map ({ EXP => $meet_cfg{Description}[$_], LINKA => $meet_cfg{Account}[$_] }, @exps);
	my @unksh = map ({ UNK => $_ }, @unks);
	$tmpl->param(NFEES => scalar @feesh, FEESH => \@feesh, NEXPS => scalar @expsh, EXPSH => \@expsh, NUNKS => scalar @unksh, UNKSH => \@unksh);

	my %ppl_seen;
	$ppl_seen{$meet{Person}[$_]}++ foreach (grep (defined $meet{Person}[$_], 0 .. $#{$meet{Person}}));

	my %accts = grep_acct_key('users', 'Name');
	my @ppl;
	foreach my $row (0 .. $#{$meet{Person}}) {
		my @rfees = ({ F => 'Custom', V => $meet{CustomFee}[$row], D_CL => (defined CleanData::clean_decimal($meet{CustomFee}[$row])) ? '' : 'broken' });
		push (@rfees, map ({ F => $meet_cfg{Fee}[$_], V => $meet{$meet_cfg{Fee}[$_]}[$row] ? $meet{$meet_cfg{Fee}[$_]}[$row] : '', BOOL => true($meet_cfg{IsBool}[$_]), D_CL => (defined CleanData::clean_decimal($meet{$meet_cfg{Fee}[$_]}[$row])) ? '' : 'broken' }, (@ccs, @exps)));
		push (@rfees, map ({ F => $_, V => $meet{$_}[$row], D_CL => 'unknown' }, @unks));
		my $a = $meet{Person}[$row] // '';
		push (@ppl, { PER_CL => ((exists $accts{$a}) ? '' : 'unknown') . ((!(defined $ppl_seen{$a}) || $ppl_seen{$a} == 1) ? '' : ' dup'), NAME => (exists $accts{$a}) ? $accts{$a} : $a, A => $a, FEES => \@rfees, NOTEV => $meet{Notes}[$row] });
	}
        $tmpl->param(PPL => \@ppl);
        $tmpl->param(EDITOK => $session->param('IsAdmin'));
        $tmpl->param(VALID => meet_valid(\%meet, $mcr));

	return $tmpl;
}

sub gen_edit_meet_ppl
{
	my ($edit_id, $sessid, $etoken) = @_;

	my $tmpl = load_template('edit_meet_ppl.html', $etoken);
	my %meet = read_htsv("$config{Root}/meets/$edit_id", undef, [ 'Person', 'Notes' ]);

	my %accts = grep_acct_key('users', 'Name');
	my @unks = grep (!(exists $accts{$_}), map ($_ // '', @{$meet{Person}}));

	my %ppl_seen;
	$ppl_seen{$meet{Person}[$_]}++ foreach (grep (defined $meet{Person}[$_], 0 .. $#{$meet{Person}}));

	my $adds = peek_session_data($sessid, "${etoken}_add_accts");
	my @adds = split ('\.', $adds) if $adds;

	my @ppl;
	foreach my $user (sort_AoH(\%accts)) {
		$ppl_seen{$user} = 0 unless exists $ppl_seen{$user};
		my @dups = map ({ A => "$user.$_" }, 2 .. $ppl_seen{$user});
		push (@ppl, { NAME => $accts{$user}, A => $user, Y => (grep ($_ eq $user, @adds) || !!grep ($_ eq $user, grep (defined, @{$meet{Person}}))), DUPS => \@dups, P_CL => ($ppl_seen{$user} > 1) ? 'dup' : '' });
	}
	push (@ppl, { NAME => $_, A => $_, Y => 1, P_CL => ($ppl_seen{$_} && $ppl_seen{$_} > 1) ? 'unknown dup' : 'unknown' }) foreach (@unks);

	$tmpl->param(MID => $edit_id);
	$tmpl->param(NAME => $meet{Name}, PPL => \@ppl, DUPTEXT => !!grep ($_ > 1, values %ppl_seen));

	return $tmpl;
}

sub meet_to_tg
{
	my %meet = @_;
	my %tg = ( Date => $meet{Date}, Name => "Meet: " . ($meet{Name} // '') );
	my %colsum;

	my %meet_cfg = read_htsv("$config{Root}/config_fees");	# world breaks if doesn't exist (need MeetAccount)
	unless (meet_valid(\%meet, \%meet_cfg, 1)) {
		$tg{Date} = 'now';
		$tg{Name} .= ' (broken)';
		$tg{Omit} = undef;
		return %tg;
	}

	foreach my $row (0 .. $#{$meet{Person}}) {
		$meet{Person}[$row] //= '';
		$colsum{$_} += $meet{$_}[$row] foreach (grep (!/^(Person|Notes)$/, @{$meet{Headings}}));
	}
	foreach my $row (0 .. $#{$meet{Person}}) {
		push (@{$tg{$meet{Person}[$row]}}, $meet{$_}[$row]) foreach (grep ($colsum{$_}, @{$meet{Headings}}));
	}

	my @units = known_units;
	my %cds = known_commod_descs;

	foreach my $hd (@{$meet{Headings}}) {
		next if ($hd eq 'Person' || $hd eq 'Notes');
		next unless $colsum{$hd};
		if (grep ($_ eq $hd, grep (defined, @{$meet_cfg{Fee}}))) {
			my $mc_row = first { $meet_cfg{Fee}[$_] eq $hd } 0 .. $#{$meet_cfg{Fee}};
			push (@{$tg{Creditor}}, $meet_cfg{Account}[$mc_row]);
			if (exists $cds{$hd}) {
				push (@{$tg{Amount}}, $colsum{$hd});
				push (@{$tg{Currency}}, $hd);
				push (@{$tg{Description}}, $cds{$hd});
			} elsif (true($meet_cfg{IsDrain}[$mc_row])) {
				push (@{$tg{Amount}}, '*');
				push (@{$tg{Currency}}, '');
				push (@{$tg{Description}}, $meet_cfg{Description}[$mc_row]);
			} else {
				push (@{$tg{Amount}}, -$colsum{$hd});
				push (@{$tg{Currency}}, $meet{Currency}) if scalar @units;
				push (@{$tg{Description}}, $meet_cfg{Description}[$mc_row]);
			}
		} elsif ($hd eq 'CustomFee') {
			push (@{$tg{Creditor}}, $meet_cfg{MeetAccount});
			push (@{$tg{Amount}}, $colsum{CustomFee});
			push (@{$tg{Currency}}, $meet{Currency}) if scalar @units;
			push (@{$tg{Description}}, 'Meet fee');
		}
	}

	@{$tg{Headings}} = ( 'Creditor', 'Amount', @{$meet{Person}}, 'Description' );
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
		$git->rm($extra_file) if $extra_file;
		commit(unroot($file) . ': deleted', $session);
	}, $file);
	return emit_with_status("Deleted $thing", $done->());
}

sub despatch_admin
{
	my $session = $_[0];
	my $sessid = $session->id();
	my $cgi = $session->query();
	my $etoken = $cgi->param('etoken');

	emit(gen_tcp) if defined $cgi->param('to_cp');

	if ($cgi->param('tmpl') eq 'login') {
		my $tmpl = gen_tcp;
		print $tmpl->output;
		exit;
	}
	if ($cgi->param('tmpl') eq 'tcp') {
		my $whinge = sub { whinge('Couldn\'t get edit lock for configuration file', gen_tcp) };
		emit(gen_manage_accts(1)) if (defined $cgi->param('view_ppl'));
		emit(gen_manage_accts(0)) if (defined $cgi->param('view_accts'));
		if (defined $cgi->param('edit_addr_alts')) {
			$whinge->() unless try_lock("$config{Root}/config_addr_alts", $sessid);
			emit(gen_edit_addr_alts(get_edit_token($sessid, 'edit_addr_alts')));
		}
		if (defined $cgi->param('edit_inst_cfg')) {
			$whinge->() unless try_lock("$config{Root}/config", $sessid);
			emit(gen_edit_inst_cfg(get_edit_token($sessid, 'edit_inst_cfg')));
		}
		emit(gen_manage_event_types) if (defined $cgi->param('manage_event_types'));
		emit(gen_manage_fee_tmpls) if (defined $cgi->param('manage_fee_tmpls'));
		if (defined $cgi->param('edit_fee_cfg')) {
			$whinge->() unless try_lock("$config{Root}/config_fees", $sessid);
			emit(gen_edit_fee_cfg(get_edit_token($sessid, 'edit_fee_cfg')));
		}
		if (defined $cgi->param('edit_pers_attrs')) {
			$whinge->() unless try_lock("$config{Root}/config_pers_attrs", $sessid);
			emit(gen_edit_pers_attrs(get_edit_token($sessid, 'edit_pers_attrs')));
		}
		if (defined $cgi->param('edit_attr_groups')) {
			$whinge->() unless try_lock("$config{Root}/config_pers_attrs", $sessid);
			emit(gen_edit_attr_groups(get_edit_token($sessid, 'edit_attr_groups')));
		}
		if (defined $cgi->param('edit_units')) {
			$whinge->() unless try_lock("$config{Root}/config_units", $sessid);
			emit(gen_edit_units(get_edit_token($sessid, 'edit_units')));
		}
	}
	if ($cgi->param('tmpl') eq 'edit_acct') {
		my $person = defined $cgi->param('email');
		my $root = $config{Root};
		my $acct_path = $person ? "$root/users" : "$root/accounts";
		my $edit_acct = valid_edit_id(scalar $cgi->param('eacct'), $acct_path, 'account', sub { whinge($_[0], gen_manage_accts($person)) });
		my $file = $edit_acct ? "$acct_path/$edit_acct" : undef;
		my $new_acct;

		if (defined $cgi->param('save') || defined $cgi->param('savenadd')) {
			my $whinge = sub { whinge($_[0], gen_add_edit_acc($edit_acct, $person, $etoken)) };

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
				unlock_dir('meets', $sessid, $whinge, 'account rename', 'meets');
				if (-e "$config{Root}/.config_fees.lock" && clear_lock("$config{Root}/.config_fees.lock", $sessid)) {
					un_commit_lock;
					$whinge->('Cannot perform account rename at present: config_fees busy');
				}
			}
			bad_token_whinge(gen_manage_accts($person)) unless redeem_edit_token($sessid, $edit_acct ? "edit_$edit_acct" : $person ? 'add_acct' : 'add_vacct', $etoken);
			if (defined $edit_acct and $edit_acct eq $session->param('User')) {
				$session->param('User', $new_acct);
				$session->param('Name', $userdetails{Name});
				$session->flush();
			}
			try_commit_and_unlock(sub {
				if ($rename) {
					dir_mod_all('transaction_groups', 1, [ $edit_acct ], sub { my ($tg, $old) = @_; foreach (@{$tg->{Creditor}}, @{$tg->{Headings}}) { s/^$old$/$new_acct/ if $_; } $tg->{$new_acct} = delete $tg->{$old} if exists $tg->{$old}; });
					dir_mod_all('meets', 0, [ $edit_acct ], sub { my ($meet, $old) = @_; $meet->{Leader} =~ s/^$old$/$new_acct/ if defined $meet->{Leader}; foreach (@{$meet->{Person}}) { s/^$old$/$new_acct/ if $_; } }, 11);
					my %cf = read_htsv("$config{Root}/config_fees", 1);
					if (%cf) {
						$cf{MeetAccount} =~ s/^$edit_acct$/$new_acct/ if defined $cf{MeetAccount};
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

			my $net = peek_session_data($sessid, $etoken);
			if ($net) {
				my $adds = pop_session_data($sessid, "${net}_add_accts");
				$adds = $adds ? "$adds.$new_acct" : $new_acct;
				push_session_data($sessid, "${net}_add_accts", $adds);
			}
		} else {
			unlock($file) if ($file);
			redeem_edit_token($sessid, $edit_acct ? "edit_$edit_acct" : $person ? 'add_acct' : 'add_vacct', $etoken);
		}

		if ($edit_acct) {
			emit_with_status((defined $cgi->param('save')) ? "Saved edits to account \"$new_acct\"" : 'Edit account cancelled', gen_manage_accts($person));
		} else {
			$etoken = pop_session_data($sessid, $etoken);
			if (defined $cgi->param('savenadd')) {
				$etoken = get_edit_token($sessid, $person ? 'add_acct' : 'add_vacct', $etoken);
				emit_with_status("Added account \"$new_acct\"", gen_add_edit_acc(undef, $person, $etoken));
			}
			my $edit_id = $etoken ? pop_session_data($sessid, "${etoken}_editid") : undef;
			my $tmpl = $etoken ? gen_edit_meet_ppl($edit_id, $sessid, $etoken) : gen_manage_accts($person);
			emit_with_status((defined $cgi->param('save')) ? "Added account \"$new_acct\"" : 'Add account cancelled', $tmpl);
		}
	}
	if ($cgi->param('tmpl') eq 'view_ppl' or $cgi->param('tmpl') eq 'view_vaccts') {
		my $acct;
		my $delete = 0;
		my $person = $cgi->param('tmpl') eq 'view_ppl';
		my $whinge = sub { whinge($_[0], gen_manage_accts($person)) };

		foreach my $p ($cgi->param) {
			if ($p =~ /^edit_(.+)$/) {
				$acct = $1;
				last;
			}
			if ($p =~ /^del_(.+)$/) {
				$acct = $1;
				$delete = 1;
				last;
			}
		}

		$acct = valid_edit_id($acct, $person ? "$config{Root}/users" : "$config{Root}/accounts", 'account', $whinge);
		my $acct_file = $person ? "$config{Root}/users/$acct" : "$config{Root}/accounts/$acct" if $acct;
		unless ($delete) {
			if ($acct) {
				$whinge->("Couldn't get edit lock for account \"$acct\"") unless try_lock($acct_file, $sessid);
				unless (-r $acct_file) {
					unlock($acct_file);
					$whinge->("Couldn't edit account \"$acct\", file disappeared");
				}
			}
			$etoken = get_edit_token($sessid, $acct ? "edit_$acct" : $person ? 'add_acct' : 'add_vacct');
			emit(gen_add_edit_acc($acct, $person, $etoken));
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
			unlock($cfg_file);
			redeem_edit_token($sessid, 'edit_addr_alts', $etoken);
		}

		emit_with_status((defined $cgi->param('save')) ? 'Saved edits to address alternatives config' : 'Edit address alternatives config cancelled', gen_tcp);
	}
	if ($cgi->param('tmpl') eq 'manage_meets') {
		my $whinge = sub { whinge($_[0], gen_manage_meets($session)) };
		if (defined $cgi->param('add')) {
			my %meet;
			my %ppl = grep_acct_key('users', 'Name');

			$meet{Name} = clean_words($cgi->param('name'));
			$meet{Date} = validate_date(scalar $cgi->param('date'), $whinge);
			$meet{Duration} = validate_int(scalar $cgi->param('len'), 'Duration', 1, $whinge);
			$meet{Leader} = validate_acct(scalar $cgi->param('leader'), \%ppl, $whinge);
			if ($cgi->param('fee_tmpl') && $cgi->param('fee_tmpl') =~ /(.*)\.(.*)/) {
				my $et = ($1 eq 'none') ? undef : valid_edit_id($1, "$config{Root}/event_types", 'event type', $whinge, 1);
				my $ft = ($2 eq 'none') ? undef : valid_edit_id($et ? "$et.$2" : $2, "$config{Root}/fee_tmpls", 'fee template', $whinge, 1);
				$ft =~ s/^$et\.// if $et;
				$meet{EventType} = $et if $et;
				$meet{Template} = $ft if $ft;
			}

			$whinge->('No meet name given') unless length $meet{Name};
			$whinge->('Zero duration?') unless $meet{Duration} > 0;

			$whinge->('Unable to get commit lock') unless try_commit_lock($sessid);
			try_commit_and_unlock(sub {
				my $file = new_uuidfile("$config{Root}/meets");
				write_simp_cfg($file, %meet);
				my @split_f = split('-', unroot($file));
				add_commit($file, "$split_f[0]...: Meet \"$meet{Name}\" created", $session);
			});
			emit_with_status("Added meet \"$meet{Name}\"", gen_manage_meets($session));
		}
		if (grep (/^del_.*$/, $cgi->param)) {
			my @dels = grep (/^del_.*$/, $cgi->param);
			next unless $dels[0] =~ /^del_(.*)$/;
			my $mid = valid_edit_id($1, "$config{Root}/meets", 'meet', $whinge, 1);
			delete_common("$config{Root}/meets/$mid", "meet \"$mid\"", $session, sub { gen_manage_meets($session) }, "$config{Root}/transaction_groups/M$mid");
		}
	}
	if ($cgi->param('tmpl') eq 'edit_meet') {
		my $whinge = sub { whinge($_[0], gen_manage_meets($session)) };
		my $edit_id = valid_edit_id(scalar $cgi->param('m_id'), "$config{Root}/meets", 'meet', $whinge, 1);
		my $mt_file = "$config{Root}/meets/$edit_id";
		my %meet_cfg = valid_fee_cfg;

		if (defined $cgi->param('edit_ppl') or defined $cgi->param('edit')) {
			$whinge->('Cannot edit meet: expenses config is broken') unless %meet_cfg;
			$whinge->("Couldn't get edit lock for meet \"$edit_id\"") unless try_lock($mt_file, $sessid);
			unless (-r $mt_file) {
				unlock($mt_file);
				$whinge->("Couldn't edit meet \"$edit_id\", file disappeared");
			}

			if (defined $cgi->param('edit')) {
				emit(gen_edit_meet($edit_id, \%meet_cfg, $session, get_edit_token($sessid, "edit_$edit_id")));
			} else {
				emit(gen_edit_meet_ppl($edit_id, $sessid, get_edit_token($sessid, "edit_$edit_id")));
			}
		}

		my %meet = read_htsv($mt_file, undef, [ 'Person', 'Notes' ]);

		if (defined $cgi->param('save')) {
			$whinge->('Cannot save meet: expenses config is broken') unless %meet_cfg;
			$whinge = sub { whinge($_[0], gen_edit_meet($edit_id, \%meet_cfg, $session, $etoken)) };

			delete $meet{Currency};
			my @ppl = @{$meet{Person}};
			delete $meet{$_} foreach (grep (ref $meet{$_}, keys %meet));
			@{$meet{Person}} = @ppl;

			my @units = known_units;
			$whinge->('No currency definition?') if scalar @units && !(defined $cgi->param('Currency'));
			if (defined $cgi->param('Currency') && $cgi->param('Currency') ne 'N/A') {
				$meet{Currency} = validate_unit(scalar $cgi->param('Currency'), \@units, $whinge);
			}

			my %cds = known_commod_descs;
			my %et;
			%et = valid_event_type("$config{Root}/event_types/" . encode_for_filename($meet{EventType}), \%meet_cfg) if defined $meet{EventType} && $meet{EventType} ne 'none';

			my %pers_count;
			foreach my $pers (@{$meet{Person}}) {
				$pers //= '';
				$pers_count{$pers} = 0 unless exists $pers_count{$pers};
				my @arr = $cgi->param("${pers}_Custom");
				push (@{$meet{CustomFee}}, validate_decimal($arr[$pers_count{$pers}], 'Custom fee', 1, $whinge));
				foreach (%et ? map { my $fee = $_; (grep ($fee eq $meet_cfg{Fee}[$_], 0 .. $#{$meet_cfg{Fee}}))[0] } (@{$et{Unit}}) : 0 .. $#{$meet_cfg{Fee}}) {
					@arr = $cgi->param("${pers}_@{$meet_cfg{Fee}}[$_]");
					push (@{$meet{@{$meet_cfg{Fee}}[$_]}}, validate_decimal($arr[$pers_count{$pers}], (exists $cds{@{$meet_cfg{Fee}}[$_]}) ? $cds{@{$meet_cfg{Fee}}[$_]} : @{$meet_cfg{Description}}[$_] . ' value', 1, $whinge));
				}
				@arr = $cgi->param("${pers}_Notes");
				push (@{$meet{Notes}}, clean_words($arr[$pers_count{$pers}]));
				$pers_count{$pers}++;
			}

			my @midheads;
			if (%et) {
				my %drains = get_cf_drains(%meet_cfg);
				my ($fees, $exps) = get_event_types(\%et, \%drains);
				@midheads = (@$fees, @$exps);
			} else {
				@midheads = @{$meet_cfg{Fee}};
			}
			@{$meet{Headings}} = ( 'Person', 'CustomFee', @midheads, 'Notes' ) if scalar @{$meet{Person}};

			my %tg = meet_to_tg(%meet);

			$whinge->('Unable to get commit lock') unless try_commit_lock($sessid);
			bad_token_whinge(gen_manage_meets($session)) unless redeem_edit_token($sessid, "edit_$edit_id", $etoken);
			try_commit_and_unlock(sub {
				my $tg_file = "$config{Root}/transaction_groups/M$edit_id";
				if (exists $tg{Creditor} && scalar @{$tg{Creditor}}) {
					(mkdir "$config{Root}/transaction_groups" or die) unless (-d "$config{Root}/transaction_groups");
					open (my $fh, '>', $tg_file) or die;
					say $fh "Meet TGs are autogenerated at runtime";
					close $fh;
					$git->add($tg_file);
				} else {
				       	$git->rm($tg_file) if -e $tg_file;
				}
				write_htsv($mt_file, \%meet, 11);
				my @split_mf = split('-', unroot($mt_file));
				add_commit($mt_file, "$split_mf[0]...: Meet \"$meet{Name}\" modified", $session);
			}, $mt_file);
		} else {
			unlock($mt_file);
			redeem_edit_token($sessid, "edit_$edit_id", $etoken);
		}

		$mt_file =~ /\/([^\/]{1,4})[^\/]*$/;
		emit_with_status((defined $cgi->param('save')) ? "Saved edits to meet \"$meet{Name}\" ($1)" : 'Edit cancelled', gen_edit_meet($edit_id, \%meet_cfg, $session, undef));
	}
	if ($cgi->param('tmpl') eq 'edit_meet_ppl') {
		my $edit_id = valid_edit_id(scalar $cgi->param('m_id'), "$config{Root}/meets", 'meet', sub { whinge($_[0], gen_manage_meets($session)) }, 1);
		my $mt_file = "$config{Root}/meets/$edit_id";
		my %cf = valid_fee_cfg;

		if (defined $cgi->param('new_user')) {
			push_session_data($sessid, "${etoken}_editid", $edit_id);
			emit(gen_add_edit_acc(undef, 1, get_edit_token($sessid, 'add_acct', $etoken)));
		}

		my %meet = read_htsv($mt_file, undef, [ 'Person', 'Notes' ]);

		if (defined $cgi->param('save')) {
			whinge('Cannot save meet: expenses config is broken', gen_manage_meets($session)) unless %cf;
			my $whinge = sub { whinge($_[0], gen_edit_meet_ppl($edit_id, $sessid, $etoken)) };
			my %accts = grep_acct_key('users', 'Name');

			my @ppl;
			my %seen_ppl;
			foreach (map { /^Pers_(.*)/; $1 } grep (/^Pers_.+$/, $cgi->param)) {
				(my $stripped = $_) =~ s/\..*$//;
				push (@ppl, $_) if validate_acct($stripped, \%accts, $whinge);
				$seen_ppl{$stripped}++;
			}
			$whinge->('Having duplicate people is silly') if grep ($_ > 1, values %seen_ppl);
			delete $meet{Headings} unless scalar @ppl;
			if (exists $meet{Headings}) {
				my %new_m;
				my %ppl_pos;
				push (@{$ppl_pos{$meet{Person}[$_]}}, $_) foreach grep (defined $meet{Person}[$_], 0 .. $#{$meet{Person}});
				foreach my $p_n (0 .. $#ppl) {
					(my $pers = $ppl[$p_n]) =~ s/\..*$//;
					my $inst = ($ppl[$p_n] =~ /\.(\d*)$/) ? $1 - 1 : 0;
					my $row = $ppl_pos{$pers}[$inst];
					next unless defined $row;
					$new_m{$_}[$p_n] = $meet{$_}[$row] foreach (@{$meet{Headings}});
				}
				@{$meet{$_}} = @{$new_m{$_}} foreach (@{$meet{Headings}});
			} elsif (scalar @ppl) {
				@{$meet{Headings}} = ( 'Person' );
			}
			@{$meet{Person}} = map { s/\..*$//; $_ } (@ppl);

			my (%et, %ft);
			my $ft_prefix = '';
			if (defined $meet{EventType} && $meet{EventType} ne 'none') {
				%et = valid_event_type("$config{Root}/event_types/" . encode_for_filename($meet{EventType}), \%cf);
				$ft_prefix = "$meet{EventType}.";
			}
			%ft = valid_ft("$config{Root}/fee_tmpls/" . encode_for_filename("$ft_prefix$meet{Template}"), \%cf) if defined $meet{Template} && $meet{Template} ne 'none';
			if (scalar @{$meet{Person}} && %ft) {
				my %cds = known_commod_descs;
				my %drains = get_cf_drains(%cf);
				my ($fees, $exps) = get_event_types(\%et, \%drains);
				my @feecols = %et ? @$fees : grep (exists $cds{$_} || exists $drains{$_}, @{$cf{Fee}});

				splice (@{$meet{Headings}}, 1, 0, 'CustomFee') if !grep ($_ eq 'CustomFee', @{$meet{Headings}});	# necessary so subsequent ones added at position 2
				foreach my $unit (@feecols) {
					splice (@{$meet{Headings}}, 2, 0, $unit) if !grep ($_ eq $unit, @{$meet{Headings}});
				}

				foreach my $p_n (0 .. $#ppl) {
					next if sum (map ((defined $meet{$_}[$p_n]), @{$meet{Headings}})) > 1;
					my %def_fees = get_ft_fees($meet{Person}[$p_n], %ft);
					$meet{$_}[$p_n] = $def_fees{$_} foreach (@feecols);
				}
			}
			foreach my $p_n (0 .. $#ppl) {
				$meet{$_}[$p_n] //= 0 foreach (grep (!/^(Person|Notes)$/, @{$meet{Headings}}));
			}

			my %tg;
			%tg = meet_to_tg(%meet) if (scalar @{$meet{Person}});

			$whinge->('Unable to get commit lock') unless try_commit_lock($sessid);
			bad_token_whinge(gen_manage_meets($session)) unless redeem_edit_token($sessid, "edit_$edit_id", $etoken);
			pop_session_data($sessid, "${etoken}_add_accts");
			try_commit_and_unlock(sub {
				my $tg_file = "$config{Root}/transaction_groups/M$edit_id";
				if (exists $tg{Creditor} && scalar @{$tg{Creditor}}) {
					(mkdir "$config{Root}/transaction_groups" or die) unless (-d "$config{Root}/transaction_groups");
					open (my $fh, '>', $tg_file) or die;
					say $fh "Meet TGs are autogenerated at runtime";
					close $fh;
					$git->add($tg_file);
				} else {
				       	$git->rm($tg_file) if -e $tg_file;
				}
				write_htsv($mt_file, \%meet, 11);
				my @split_mf = split('-', unroot($mt_file));
				add_commit($mt_file, "$split_mf[0]...: Meet \"$meet{Name}\" participants modified", $session);
			}, $mt_file);
		} else {
			unlock($mt_file) if $mt_file;
			redeem_edit_token($sessid, "edit_$edit_id", $etoken);
			pop_session_data($sessid, "${etoken}_add_accts");
		}

		$mt_file =~ /\/([^\/]{1,4})[^\/]*$/;
		emit_with_status((defined $cgi->param('save')) ? "Saved edits to \"$meet{Name}\" ($1) meet participants" : 'Edit cancelled', gen_edit_meet($edit_id, \%cf, $session, undef));
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
			unlock($cfg_file);
			redeem_edit_token($sessid, 'edit_inst_cfg', $etoken);
		}

		emit_with_status((defined $cgi->param('save')) ? 'Saved edits to installation config' : 'Edit installation config cancelled', gen_tcp);
	}
	if ($cgi->param('tmpl') eq 'manage_event_types') {
		my $et;
		my $delete = 0;
		my $whinge = sub { whinge($_[0], gen_manage_event_types) };

		foreach my $p ($cgi->param) {
			if ($p =~ /^edit_(.+)$/) {
				$et = $1;
				last;
			}
			if ($p =~ /^del_(.+)$/) {
				$et = $1;
				$delete = 1;
				last;
			}
		}

		$et = valid_edit_id($et, "$config{Root}/event_types", 'event type', $whinge);
		my $et_file = "$config{Root}/event_types/$et" if $et;
		unless ($delete) {
			if ($et) {
				$whinge->("Couldn't get edit lock for event type \"$et\"") unless try_lock($et_file, $sessid);
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
			}

			@{$et{Headings}} = ( 'Unit', 'Column', 'Unusual' ) if exists $et{Unit};

			$whinge->('Unable to get commit lock') unless try_commit_lock($sessid);
			if ($rename) {
				unlock_dir('fee_tmpls', $sessid, $whinge, 'ET rename', 'fee templates');
				unlock_dir('meets', $sessid, $whinge, 'ET rename', 'meets');
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
					dir_mod_all('meets', 0, [ $edit_id ], sub { my ($meet, $old) = @_; $meet->{EventType} =~ s/^$old$/$new_id/ if defined $meet->{EventType} }, 11);
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
			unlock($file) if $file;
			redeem_edit_token($sessid, $edit_id ? "edit_$edit_id" : 'add_et', $etoken);
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
	if ($cgi->param('tmpl') eq 'edit_fee_tmpl') {
		emit(gen_manage_fee_tmpls) if (defined $cgi->param('manage_fee_tmpls'));
		my $whinge = sub { whinge($_[0], gen_manage_fee_tmpls) };

		my $edit_id = valid_edit_id(scalar $cgi->param('ft_id'), "$config{Root}/fee_tmpls", 'fee template', $whinge, (defined $cgi->param('edit')));
		my $et_id = $cgi->param('event_type') ? valid_edit_id(scalar $cgi->param('event_type'), "$config{Root}/event_types", 'event type', $whinge, 1) : undef;
		my %cf = valid_fee_cfg;
		my %et = $et_id ? valid_event_type("$config{Root}/event_types/$et_id", \%cf) : ();
		my $file = $edit_id ? "$config{Root}/fee_tmpls/" . encode_for_filename($edit_id) : undef;

		if (defined $cgi->param('edit')) {
			$whinge->("Couldn't get edit lock for fee template \"$edit_id\"") unless try_lock($file, $sessid);
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
			unlock_dir('meets', $sessid, $whinge, 'FT rename', 'meets') if $rename;
			bad_token_whinge(gen_manage_fee_tmpls) unless redeem_edit_token($sessid, $edit_id ? "edit_$edit_id" : 'add_ft', $etoken);
			try_commit_and_unlock(sub {
				if ($rename) {
					my $old_ft_id = $edit_id;
					if ($et_id && $old_ft_id =~ /^[^\/.]+\.([^\/]+)$/) {
						$old_ft_id = $1;
					}
					dir_mod_all('meets', 0, [ $old_ft_id ], sub { my ($meet, $old) = @_; $meet->{Template} =~ s/^$old$/$new_ft_id/ if defined $meet->{Template} && ((defined $meet->{EventType} && $et_id && $meet->{EventType} eq $et_id) || !(defined $meet->{EventType})) }, 11);
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
			unlock($file) if $file;
			redeem_edit_token($sessid, $edit_id ? "edit_$edit_id" : 'add_ft', $etoken);
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

			$whinge->('Missing account name') unless clean_username($cgi->param('MeetAcct'));
			$cfg{MeetAccount} = validate_acct(scalar $cgi->param('MeetAcct'), \%vaccts, $whinge);

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
					$whinge->("Expense (\"$id\") cannot be Boolean") if defined $cgi->param("Bool_$row") && !(defined $cgi->param("Drain_$row"));
					push (@{$cfg{Fee}}, $id);
					push (@{$cfg{Account}}, validate_acct(scalar $acct, \%acct_names, $whinge));
					push (@{$cfg{IsDrain}}, (defined $cgi->param("Drain_$row")));
				}
				push (@{$cfg{IsBool}}, (defined $cgi->param("Bool_$row")));
				push (@{$cfg{Description}}, $desc);
			}

			@{$cfg{Headings}} = ( 'Fee', 'IsBool', 'IsDrain', 'Account', 'Description' ) if exists $cfg{Fee};

			$whinge->('Unable to get commit lock') unless try_commit_lock($sessid);
			if (keys %recode) {
				unlock_dir('event_types', $sessid, $whinge, 'fee recode', 'event types');
				unlock_dir('fee_tmpls', $sessid, $whinge, 'fee recode', 'fee templates');
				unlock_dir('meets', $sessid, $whinge, 'fee recode', 'meets');
			}
			bad_token_whinge(gen_tcp) unless redeem_edit_token($sessid, 'edit_fee_cfg', $etoken);
			try_commit_and_unlock(sub {
				my $commit_msg = 'config_fees: expense configuration modified';

				if (keys %recode) {
					dir_mod_all('event_types', 0, [ keys %recode ], sub { my ($et, $old) = @_; foreach (@{$et->{Unit}}) { s/^$old$/$recode{$old}/ if $_; } });
					dir_mod_all('fee_tmpls', 0, [ keys %recode ], sub { my ($ft, $old) = @_; foreach (@{$ft->{Unit}}) { s/^$old$/$recode{$old}/ if $_; } });
					dir_mod_all('meets', 0, [ keys %recode ], sub { my ($meet, $old) = @_; s/^$old$/$recode{$old}/ foreach (@{$meet->{Headings}}); $meet->{$recode{$old}} = delete $meet->{$old} if exists $meet->{$old}; }, 11);
					$commit_msg .= ' AND CODES ALTERED';
				}

				write_htsv($cfg_file, \%cfg, 11);
				add_commit($cfg_file, $commit_msg, $session);
			}, $cfg_file);
		} else {
			unlock($cfg_file);
			redeem_edit_token($sessid, 'edit_fee_cfg', $etoken);
		}

		emit_with_status((defined $cgi->param('save')) ? 'Saved edits to meet form config' : 'Edit meet form config cancelled', gen_tcp);
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
			$cfg{IsPleb} = $oldcfg{IsPleb} if exists $oldcfg{IsPleb};

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
			unlock($cfg_file);
			redeem_edit_token($sessid, 'edit_pers_attrs', $etoken);
		}

		emit_with_status((defined $cgi->param('save')) ? 'Saved edits to attribute config' : 'Edit attribute config cancelled', gen_tcp);
	}
	if ($cgi->param('tmpl') eq 'edit_attr_groups') {
		my $cfg_file = "$config{Root}/config_pers_attrs";

		if (defined $cgi->param('save')) {
			my %cfg;
			my $whinge = sub { whinge($_[0], gen_edit_attr_groups($etoken)) };

			foreach my $attr (get_attrs(1), 'IsPleb') {
				$cfg{$attr} = join (':', map { s/^${attr}_//; $_ } grep (/^${attr}_/, $cgi->param()));
			}
			delete $cfg{IsPleb} unless length $cfg{IsPleb};

			$whinge->('Unable to get commit lock') unless try_commit_lock($sessid);
			bad_token_whinge(gen_tcp) unless redeem_edit_token($sessid, 'edit_attr_groups', $etoken);
			try_commit_and_unlock(sub {
				write_htsv($cfg_file, \%cfg);
				add_commit($cfg_file, 'config_pers_attrs: attribute groups modified', $session);
			}, $cfg_file);
		} else {
			unlock($cfg_file);
			redeem_edit_token($sessid, 'edit_attr_groups', $etoken);
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
			unlock($cfg_file);
			redeem_edit_token($sessid, 'edit_units', $etoken);
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
			unlock($cfg_file);
			redeem_edit_token($sessid, 'edit_units', $etoken);
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
		%dates = grep_htsv_key("$config{Root}/$flavour/*", 'Date', 1);
	}

	my %rds;
	foreach (keys %dates) {
		$dates{$_} = '0.0.0' unless defined $dates{$_} and $dates{$_} =~ /^\s*\d+\s*[.]\s*\d+\s*[.]\s*\d+\s*$/;
		push (@{$rds{$dates{$_}}}, $_);	# non-unique dates
	}
	return map (@{$rds{$_->[0]}}, sort { $a->[1] cmp $b->[1] } map ([ $_, sprintf('%04d%02d%02d', (split /[.]/, $_)[2,1,0]) ], keys %rds));	# Schwartzian transform ftw
}

sub sprint_monetary
{
	return sprintf($_[0] ? '%+.2f' : '0.00', $_[0]);
}

sub unk_computed_accts
{
	my ($va, $comp) = @_;

	return grep (!(exists $va->{$_}), keys %$comp);
}

sub gen_ucp
{
	my ($session, $acct) = @_;
	my $tmpl = load_template('user_cp.html');
	my $user = $acct // $session->param('User');

	my %acct_names = get_acct_name_map;
	my %dds = double_drainers;
	my %neg_accts = grep_acct_key('accounts', 'IsNegated');
	my %resolved = resolve_accts(\%dds, \%neg_accts);

	my $credsum = 0;
	my $debsum = 0;
	my (@credlist, @debtlist);
	foreach my $tg (date_sorted_htsvs('transaction_groups')) {
		my %computed = eval { compute_tg_c($tg, undef, \%neg_accts, \%resolved) };
		my $tg_indet = nonfinite(values %computed);
		my $tg_broken = $@ ne '' || (%resolved && $tg_indet) || exists $dds{$tg};
		next unless exists $computed{$user} or $tg_broken;

		my %tgdetails = %{$tgds{$tg}};
		my @to;
		my @to_extras;
		unless ($tg_broken) {
			$computed{$user} >= 0 ? $credsum : $debsum += $computed{$user} unless exists $tgdetails{Omit};

			if (($computed{$user} < 0 && exists $neg_accts{$user}) || ($computed{$user} > 0 && !(exists $neg_accts{$user}))) {
				@to = map ({ SEP => ', ', N => $acct_names{$_}, A => $_ }, grep (exists $neg_accts{$_} ? $computed{$_} > 0 : $computed{$_} < 0, keys %computed));
			} elsif (($computed{$user} > 0 && exists $neg_accts{$user}) || ($computed{$user} < 0 && !(exists $neg_accts{$user}))) {
				@to = map ({ SEP => ', ', N => $acct_names{$_}, A => $_ }, grep (exists $neg_accts{$_} ? $computed{$_} < 0 : $computed{$_} > 0, keys %computed));
			}
			$to[0]->{SEP} = '';
			$to[-1]->{SEP} = ' and ' if scalar @to > 1;
			if (scalar @to > 5) {
				@to_extras = map ($to[$_]->{N}, (4 .. $#to));
				$#to = 3;
			}
		}

		my $is_meet = $tg =~ /^M/;
		my %outputdetails = (
			MEET => $is_meet,
			ACC => $is_meet ? substr ($tg, 1) : $tg,
			TG_CL => (exists $tgdetails{Omit}) ? 'omitted' : '',
			NAME => $tgdetails{Name},
			TO => \@to,
			TO_EXTRA => join (', ', @to_extras),
			DATE => $tgdetails{Date},
			SUMMARY_CL => $tg_broken ? 'broken' : $tg_indet ? 'indet' : '',
			SUMMARY => encode_for_html($tg_broken ? 'TG BROKEN' : $tg_indet ? 'incalculable' : ($computed{$user} > 0 ? '+' : '') . $computed{$user}),
		);
		push (@{($tg_broken or $computed{$user} >= 0) ? \@credlist : \@debtlist}, \%outputdetails);
	}
	my %cf = read_htsv("$config{Root}/config_fees", 1);
	my %id_count;
	my @simptransidcounts = map ($id_count{$cf{Fee}[$_]}++, grep (defined $cf{Fee}[$_] && length $cf{Fee}[$_] && !($cf{Fee}[$_] =~ /[A-Z]/ || true($cf{IsBool}[$_]) || true($cf{IsDrain}[$_])) && defined $cf{Account}[$_] && exists $acct_names{$cf{Account}[$_]} && defined $cf{Description}[$_] && length $cf{Description}[$_], 0 .. $#{$cf{Description}}));
	$tmpl->param(SIMPTRANS => scalar @simptransidcounts && !grep ($_ > 0, @simptransidcounts));
	$tmpl->param(ACCT => (exists $acct_names{$acct}) ? $acct_names{$acct} : $acct) if defined $acct;
	$tmpl->param(BAL => sprint_monetary($credsum + $debsum));
	$tmpl->param(CRED_TOT => sprint_monetary($credsum));
	$tmpl->param(DEB_TOT => sprint_monetary($debsum));
	my @units = known_units();
	$tmpl->param(DEFCUR => (scalar @units) ? $units[0] : undef);
	$tmpl->param(CREDITS => \@credlist);
	$tmpl->param(DEBITS => \@debtlist);
	$tmpl->param(LOGIN => $session->param('User'));
	$tmpl->param(TCP => $session->param('IsAdmin'));
	$tmpl->param(ADDTG => $session->param('MayAddEditTGs'));
	$tmpl->param(BANK => $session->param('IsAdmin'));
	$tmpl->param(MEETS => !!valid_fee_cfg);

	return $tmpl;
}

sub gen_accts_disp
{
	my ($nozeros, $by_bal) = @_;
	my $tmpl = load_template('accts_disp.html');

	my %dds = double_drainers;
	my %neg_accts = grep_acct_key('accounts', 'IsNegated');
	my %resolved = resolve_accts(\%dds, \%neg_accts);
	if ($@ || !%resolved || nonfinite(values %resolved)) {
		$tmpl->param(BROKEN => 1);
		return $tmpl;
	}

	my %running;
	foreach my $tg (glob ("$config{Root}/transaction_groups/*")) {
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
	$tmpl->param(SDEBTS => -$sum_debts, SCREDS => $sum_creds);
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
		my @sorteddescs = map ($_->[0], sort { $a->[1] cmp $b->[1] } map ([ $_, $cfg{Description}[$_]], grep (defined $cfg{Fee}[$_] && length $cfg{Fee}[$_] && !($cfg{Fee}[$_] =~ /[A-Z]/ || true($cfg{IsBool}[$_]) || true($cfg{IsDrain}[$_])) && defined $cfg{Account}[$_] && exists $acct_names{$cfg{Account}[$_]} && defined $cfg{Description}[$_] && length $cfg{Description}[$_], 0 .. $#{$cfg{Description}})));	# Schwartzian transform ftw
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
		my @sorteddescs = map ($_->[0], sort { $a->[1] cmp $b->[1] } map ([ $_, $cfg{Description}[$_]], grep (defined $cfg{Fee}[$_] && length $cfg{Fee}[$_] && !($cfg{Fee}[$_] =~ /[A-Z]/ || true($cfg{IsBool}[$_]) || true($cfg{IsDrain}[$_])) && defined $cfg{Account}[$_] && exists $acct_names{$cfg{Account}[$_]} && defined $cfg{Description}[$_] && length $cfg{Description}[$_], 0 .. $#{$cfg{Description}})));	# Schwartzian transform ftw
		@vaccts = map ({ NAME => $cfg{Description}[$_], A => "$cfg{Fee}[$_]" }, @sorteddescs);
	} else {
		@vaccts = map ({ NAME => $vaccts{$_}, A => $_ }, sort_AoH(\%vaccts));
	}

	$tmpl->param(BANK => $bank, VACCT => $vacct, PPL => \@pploptions, NAS => \@nas, CUR => (scalar @units > 1), CURS => \@currencies, VACCTS => \@vaccts);

	return $tmpl;
}

sub gen_manage_tgs
{
	my $session = $_[0];
	my $tmpl = load_template('manage_transactions.html');
	my %acct_names = get_acct_name_map;
	my %dds = double_drainers;
	my %neg_accts = grep_acct_key('accounts', 'IsNegated');
	my %resolved = resolve_accts(\%dds, \%neg_accts);

	my @tglist;
	my %daterates;
	foreach my $tg (date_sorted_htsvs('transaction_groups')) {
		my $tg_fail;
		my %computed = eval { compute_tg_c($tg, undef, \%neg_accts, \%resolved, sub { $tg_fail = $_[0]; die }) };
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
				foreach my $_ ($i .. $#{$tgdetails{Creditor}}) {
					next if $tgdetails{Creditor}[$_] ne $acct;
					if ($tgdetails{Amount}[$_] =~ /^\s*[*]\s*$/) {
						$drained = 1;
					} else {
						my $rate = (scalar keys %rates < 2) ? 1 : $rates{$tgdetails{Currency}[$_]};
						$summary{$acct} += sprintf('%.2f', $tgdetails{Amount}[$_] * $rate);
					}
				}
				push (@sum_str, { FIRST => !(scalar @sum_str), N => $acct_names{$acct}, A => $acct, VAL => ($drained ? 'drained' : (($summary{$acct} < 0) ? '' : '+') . $summary{$acct}) });
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
	my %units_cfg = read_units_cfg("$config{Root}/config_units");
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
	my ($edit_id, $calced, $session, $etoken) = @_;

	my $tmpl = load_template('edit_tg.html', $etoken);

	my %units_cfg = read_units_cfg("$config{Root}/config_units");
	my @units = known_units(%units_cfg);
	my %tgdetails = gen_ft_tg_common($edit_id ? "$config{Root}/transaction_groups/$edit_id" : undef, 1, 10, !$etoken, 'Creditor', $session->param('User'), 'Currency', 5, 100, \@units);

	my %dds;
	if ($calced) {
		my $whinge = sub { whinge("Can't display calculated values: $_[0]", gen_tg($edit_id, undef, $session, $etoken)) };
		validate_tg($edit_id, \%tgdetails, $whinge);
		validate_units(\%units_cfg, $whinge);
		%dds = double_drainers;
		$whinge->("Multiple drains of '$dds{$edit_id}'") if exists $dds{$edit_id};
	}

	my %ppl = grep_acct_key('users', 'Name');
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
			%rates = get_rates($tgdetails{Date});
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
		my $unk_cur = !grep ($_ eq $tgdetails{Currency}[$row], @units);
		my @currencies = map ({ C => $_, S => ($_ eq $tgdetails{Currency}[$row]) }, $unk_cur ? (@units, $tgdetails{Currency}[$row]) : @units);
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

sub despatch
{
	my $session = $_[0];
	my $sessid = $session->id();
	my $cgi = $session->query();
	my $etoken = $cgi->param('etoken');

	return if (defined $cgi->param('logout'));

	emit(gen_manage_tgs($session)) if (defined $cgi->param('manage_tgs'));
	emit(gen_manage_meets($session)) if (defined $cgi->param('manage_meets'));
	emit(gen_ucp($session)) if (defined $cgi->param('to_acct'));
	emit(gen_accts_disp) if (defined $cgi->param('disp_accts'));

	despatch_admin($session) if $session->param('IsAdmin');

	if ($cgi->param('tmpl') eq 'login_nopw') {
		my $tmpl = gen_ucp($session);
		print $tmpl->output;
		exit;
	}
	if ($cgi->param('tmpl') eq 'ucp') {
		if (defined $cgi->param('add_swap') || defined $cgi->param('add_vacct_swap')) {
			my $swap = defined $cgi->param('add_swap');
			emit(gen_add_swap($swap, $session->param('User'), get_edit_token($sessid, $swap ? 'add_swap' : 'add_vacct_swap')));
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
			my $whinge = sub { whinge($_[0], gen_add_swap($swap, $session->param('User'), $etoken)) };

			my %acct_names = grep_acct_key('users', 'Name');
			my @units = known_units();

			$tg{Date} = validate_date(scalar $cgi->param('tg_date'), $whinge);
			push (@{$tg{Creditor}}, validate_acct(scalar $cgi->param('Creditor'), \%acct_names, $whinge));
			push (@{$tg{Amount}}, clean_word($cgi->param('Amount')));
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
				$whinge->('Broken expense type') if true($cf{IsBool}[$row]) || true($cf{IsDrain}[$row]);
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
				my $amnt = validate_decimal(scalar $cgi->param("Cred_$acct"), 'Creditor amount', undef, $whinge);
				$creds{$acct} = $amnt unless $amnt == 0;
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

			my %cf = read_htsv("$config{Root}/config_fees");
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
					my $fee = clean_word($dacct);
					$fee =~ s/^V// if defined $fee;
					$whinge->('Broken expense type') unless defined $fee && !($fee =~ /[A-Z]/);
					my $row = first { defined $cf{Fee}[$_] && $cf{Fee}[$_] eq $fee } 0 .. $#{$cf{Fee}};
					$whinge->('Unknown expense type') unless defined $row;
					$whinge->('Broken expense type') if true($cf{IsBool}[$row]) || true($cf{IsDrain}[$row]);
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

		emit(gen_accts_disp($nozeros, $sort eq 'bal'));
	}
	if ($cgi->param('tmpl') eq 'manage_tgs') {
		my $whinge = sub { whinge($_[0], gen_manage_tgs($session)) };
		if (defined $cgi->param('view') or defined $cgi->param('add')) {
			my $view = valid_edit_id(scalar $cgi->param('view'), "$config{Root}/transaction_groups", 'TG', $whinge);

			emit(gen_tg($view, undef, $session, $view ? undef : get_edit_token($sessid, 'add_tg', $etoken)));
		}
		if (grep (/^del_.*$/, $cgi->param)) {
			my @dels = grep (/^del_.*$/, $cgi->param);
			next unless $dels[0] =~ /^del_(.*)$/;
			my $edit_id = valid_edit_id($1, "$config{Root}/transaction_groups", 'TG', $whinge, 1);
			delete_common("$config{Root}/transaction_groups/$edit_id", "TG \"$edit_id\"", $session, sub { gen_manage_tgs($session) });
		}
	}
	if ($cgi->param('tmpl') eq 'edit_tg') {
		my $whinge = sub { whinge($_[0], gen_manage_tgs($session)) };
		my $edit_id = valid_edit_id(scalar $cgi->param('tg_id'), "$config{Root}/transaction_groups", 'TG', $whinge, (defined $cgi->param('edit')));

		if (defined $cgi->param('showcvs') || defined $cgi->param('hidecvs')) {
			emit(gen_tg($edit_id, (defined $cgi->param('showcvs')), $session, undef));
		}

		whinge('Action not permitted', $edit_id ? gen_tg($edit_id, undef, $session, undef) : gen_manage_tgs($session)) unless $session->param('MayAddEditTGs');
		my $tgfile = $edit_id ? "$config{Root}/transaction_groups/$edit_id" : undef;

		if (defined $cgi->param('edit')) {
			whinge('Editing of generated TGs not allowed', gen_tg($edit_id, undef, $session, undef)) if $edit_id =~ /^[A-Z]/;

			$whinge->("Couldn't get edit lock for transaction group \"$edit_id\"") unless try_lock($tgfile, $sessid);
			unless (-r $tgfile) {
				unlock($tgfile);
				$whinge->("Couldn't edit transaction group \"$edit_id\", file disappeared");
			}
			emit(gen_tg($edit_id, undef, $session, get_edit_token($sessid, "edit_$edit_id")));
		}
		if (defined $cgi->param('delete')) {
			delete_common($tgfile, "TG \"$edit_id\"", $session, sub { gen_manage_tgs($session) });
		}

		# only left with save and cancel now
		my %tg;

		if (defined $cgi->param('save')) {
			$whinge = sub { whinge($_[0], gen_tg($edit_id, undef, $session, $etoken)) };

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
				push (@{$tg{Amount}}, clean_word($cgi->param("Amount_$row")));
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
			unlock($tgfile) if $tgfile;
			redeem_edit_token($sessid, $edit_id ? "edit_$edit_id" : 'add_tg', $etoken);
		}

		$tgfile =~ /\/([^\/]{1,4})[^\/]*$/ if $tgfile;
		if ($edit_id) {
			emit_with_status((defined $cgi->param('save')) ? "Saved edits to \"$tg{Name}\" ($1) transaction group" : 'Edit cancelled', gen_tg($edit_id, undef, $session, undef));
		} else {
			$etoken = pop_session_data($sessid, $etoken);
			redeem_edit_token($sessid, 'add_vacct_swap', $etoken) if $etoken;
			emit_with_status((defined $cgi->param('save')) ? "Added transaction group \"$tg{Name}\" ($1)" : 'Add transaction group cancelled', $etoken ? gen_ucp($session) : gen_manage_tgs($session));
		}
	}
	if ($cgi->param('tmpl') eq 'manage_meets') {
		if (defined $cgi->param('view')) {
			my $whinge = sub { whinge($_[0], gen_manage_meets($session)) };
			my %cf = valid_fee_cfg;
			$whinge->('Cannot view meet: expenses config is broken') unless %cf;
			my $mid = valid_edit_id(scalar $cgi->param('view'), "$config{Root}/meets", 'meet', $whinge, 1);

			emit(gen_edit_meet($mid, \%cf, $session, undef));
		}
	}

	return;
}

set_htsv_encoders(\&read_htsv_encode, \&write_htsv_encode);
my $cgi = CGI->new;

%config = read_simp_cfg('boc_config');

die 'Can\'t find value for "Root" key in ./boc_config' unless defined $config{Root};
die 'Can\'t find value for "TemplateDir" key in ./boc_config' unless defined $config{TemplateDir};
die "The BoC root directory (set as $config{Root} in ./boc_config) must exist and be readable and writable by the webserver --" unless (-r $config{Root} and -w $config{Root});
$ENV{HTML_TEMPLATE_ROOT} = $config{TemplateDir};

emit(load_template($cgi->param('serve') . '.html')) if defined $cgi->param('serve') && !($cgi->param('serve') =~ /\./) && -r "$config{TemplateDir}/" . $cgi->param('serve') . ".html";
emit(load_template($cgi->param('serve') . '.js')) if defined $cgi->param('serve') && !($cgi->param('serve') =~ /\./) && -r "$config{TemplateDir}/" . $cgi->param('serve') . ".js";
emit(load_template($cgi->param('serve') . '.css')) if defined $cgi->param('serve') && !($cgi->param('serve') =~ /\./) && -r "$config{TemplateDir}/" . $cgi->param('serve') . ".css";

$ENV{PATH} = '/bin:/usr/bin';
$git = Git::Wrapper->new($config{Root});
update_global_config(read_simp_cfg("$config{Root}/config", 1));

set_accts_config_root($config{Root});
init_attr_cfg("$config{Root}/config_pers_attrs");
init_units_cfg("$config{Root}/config_units");
set_event_config_root($config{Root});

create_datastore($cgi, "$config{Root} does not appear to be a BoC data store") unless (-d "$config{Root}/users");
create_datastore($cgi, 'No useable administrator account') unless validate_admins;

my $session = CGI::Session->load($cgi) or die CGI::Session->errstr;
$session = get_new_session($session, $cgi) if ($session->is_empty || !(defined $cgi->param('tmpl')) || $cgi->param('tmpl') =~ m/^login(_nopw)?$/ || $session->param('Instance') ne $config{Root});

despatch($session);

# the despatchers fall through if the requested action is unknown: make them log in again!
get_new_session($session, $cgi);
