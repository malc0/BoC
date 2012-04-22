#!/usr/bin/perl -T

use 5.012;
use autodie;
use warnings;
use Fcntl qw(O_RDWR O_WRONLY O_EXCL O_CREAT LOCK_EX LOCK_NB SEEK_SET);
use CGI qw(param);
use CGI::Carp qw(fatalsToBrowser);
use CGI::Session '-ip-match';
use Crypt::Cracklib;
use Crypt::PasswdMD5;
use File::Slurp;
use Git::Wrapper;
use HTML::Entities;
use HTML::Template;
use List::Util qw(first min);
use Time::HiRes qw(usleep);
use Time::ParseDate;
use UUID::Tiny;
use YAML::XS;

use lib '.';
use HeadedTSV ();
use TG ();

our %config;
our $git;

sub update_global_config
{
	my (%append_cfg) = @_;
	@config{keys %append_cfg} = values %append_cfg;	# merge settings
	$config{LongName} = "Set LongName in installation config!" unless defined $config{LongName};
	$config{ShortName} = "Set ShortName in installation config!" unless defined $config{ShortName};
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
	write_file($fh, $data);	# write_file does close() for us
}

sub push_session_data
{
	my ($sessid, $key, $value) = @_;

	my $file = File::Spec->tmpdir() . '/' . sprintf("${CGI::Session::Driver::file::FileName}_bocdata", $sessid);

	my ($fh, %data) = flock_and_read($file);
	if (defined $data{$key} and first { $data{$key}[$_] eq $value } 0 .. $#{$data{$key}}) {
		close ($fh);
		return;
	}

	push(@{$data{$key}}, $value);

	write_and_close($fh, %data);
}

sub pop_session_data
{
	my ($sessid, $key, $value) = @_;

	my $file = File::Spec->tmpdir() . '/' . sprintf("${CGI::Session::Driver::file::FileName}_bocdata", $sessid);

	my ($fh, %data) = flock_and_read($file);
	unless (defined $data{$key}) {
		close ($fh);
		return undef;
	}

	my $index = first { $data{$key}[$_] eq $value } 0 .. $#{$data{$key}};
	unless (defined $index) {
		close ($fh);
		return undef;
	}

	splice(@{$data{$key}}, $index, 1);

	write_and_close($fh, %data);

	return $value;
}

sub get_edit_token
{
	my ($sessid, $add_obj_str) = @_;

	my $pass = create_UUID_as_string(UUID_V4);
	push_session_data($sessid, $add_obj_str, $pass);

	return $pass;
}

sub redeem_edit_token
{
	my $rv = eval { pop_session_data(@_) };
	return ($@ or not $rv) ? undef : $rv;
}

sub try_lock
{
	my ($file, $sessid) = @_;
	my $lockfile = "$file.lock";
	$lockfile =~ s/^(.*\/)([^\/]*)/$1.$2/;	# insert a . to hide file (especially from directory globbing)
	my $lock;

	no autodie qw(sysopen open);	# sysopen and open are intended to fail sometimes
	unless (sysopen ($lock, $lockfile, O_WRONLY | O_EXCL | O_CREAT)) {	# we assume it's not on NFSv2
		my $mtime = (stat($lockfile))[9];

		return undef unless ((not defined $mtime) or (time() - $mtime) > 600);

		return undef unless open ($lock, "+>$lockfile");
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
	unlink $lockfile;
}

sub try_lock_wait
{
	my ($file, $sessid) = @_;

	my $ms_remaining = 1000;
	while ($ms_remaining) {
		return $sessid if (try_lock($file, $sessid) or $ms_remaining == 0);
		usleep(1000);
		$ms_remaining--;
	}
	return undef;
}

sub try_commit_lock
{
	return try_lock_wait("$config{Root}/DSLOCK", $_[0]);
}

sub un_commit_lock
{
	unlink "$config{Root}/.DSLOCK.lock";
}

sub try_tg_lock
{
	my ($file, $sessid) = @_;

	return undef unless try_commit_lock($sessid);
	my $rv = try_lock($file, $sessid);
	un_commit_lock;
	return $rv;
}

sub encode_for_html
{
	return undef unless $_[0];
	my $escaped = encode_entities(decode_entities($_[0]), '^A-Za-z0-9!%^*()\-_=+{}\[\];:@#~,./?\\\ ');
	$escaped =~ s/&#39;/&apos;/g;
	return $escaped;
}

sub encode_for_file
{
	return undef unless $_[0];
	return encode_entities(decode_entities($_[0]), '^A-Za-z0-9¬`!"£\$%^&*()\-_=+{}\[\];:\'@~,.<>/?\\\| ');	# hash not included to avoid getting treated as comment in file!
}

sub read_simp_cfg
{
	my ($filename, $nexist_ok) = @_;

	my %config = HeadedTSV::read_htsv($filename, $nexist_ok);

	foreach my $key (keys %config) {
		next if $key eq 'Password';
		$config{$key} = encode_for_html($config{$key}) if $config{$key};
	}

	return %config;
}

sub write_simp_cfg
{
	my ($file, %config) = @_;

	foreach my $key (keys %config) {
		$config{$key} = encode_for_file($config{$key}) if $config{$key};
	}

	HeadedTSV::write_htsv("$file.new", \%config);
	rename ("$file.new", $file);
}

sub read_tg
{
	my %content = TG::read_tg($_[0]);

	foreach my $key (keys %content) {
		$content{$key} = encode_for_html($content{$key}) unless (ref($content{$key}) or not $content{$key});
	}
	@{$content{Description}} = map (encode_for_html($_), @{$content{Description}});

	return %content;
}

sub write_tg
{
	my ($file, %content) = @_;

	foreach my $key (keys %content) {
		$content{$key} = encode_for_file($content{$key}) unless (ref($content{$key}) or not $content{$key});
	}
	@{$content{Description}} = map (encode_for_file($_), @{$content{Description}});

	TG::write_tg("$file.new", %content);
	rename ("$file.new", $file);
}

sub read_htsv
{
	my ($filename, $nexist_ok) = @_;

	my %content = HeadedTSV::read_htsv($filename, $nexist_ok);

	foreach my $key (keys %content) {
		$content{$key} = encode_for_html($content{$key}) unless (ref($content{$key}) or not $content{$key});
		@{$content{$key}} = map (encode_for_html($_), @{$content{$key}}) if ref ($content{$key});
	}

	return %content;
}

sub write_htsv
{
	my ($file, $content, $ts) = @_;

	foreach my $key (keys %$content) {
		$content->{$key} = encode_for_file($content->{$key}) unless (ref($content->{$key}) or not $content->{$key});
		@{$content->{$key}} = map (encode_for_file($_), @{$content->{$key}}) if ref ($content->{$key});
	}

	HeadedTSV::write_htsv("$file.new", $content, $ts);
	rename ("$file.new", $file);
}

sub add_commit
{
	my ($file, $message, $userdata) = @_;
	my $user = ref $userdata ? $userdata->param('User') : $userdata;
	my $name = ref $userdata ? $userdata->param('Name') : $userdata;
	$git->add($file);
	$git->commit({author => "$name <$user>", message => $message});
}

sub try_commit_and_unlock
{
	my ($sub, $extra_lock) = @_;

	eval { $sub->() };
	my $commit_fail = $@;
	if ($commit_fail) {
		eval { $git->reset({hard => 1}) };
		# die hard, leaving locks, if we can't clean up
		open (my $fh, ">$config{Root}/RepoBroke") if ($@ and not -e "$config{Root}/RepoBroke");
		die "Clean up failed: $@\nOriginally due to: $commit_fail" if $@;
	}
	un_commit_lock;
	unlock($extra_lock) if $extra_lock;
	die $commit_fail if $commit_fail;
}

sub bad_token_whinge
{
	un_commit_lock;
	whinge('Invalid edit token (double submission?)', $_[0]);
}

sub set_status
{
	$_[0]->param(STATUS => "Status: $_[1]");
}

sub clean_username
{
	return undef unless defined $_[0];
	$_[0] =~ /^([a-z0-9\-+_]*)$/;	# these have to exist on a filesystem.  certainly do not permit dots (.), as could get trashed lock files
	return $1;
}

sub clean_email
{
	return undef unless defined $_[0];
	$_[0] =~ /^\s*(.+\@.+)\s*$/;
	return undef unless $1;
	return encode_for_html($1);
}

sub clean_text
{
	return undef unless defined $_[0];
	my $escaped_text = encode_for_html($_[0]);
	$escaped_text =~ /^(.+)$/;
	return $1;
}

sub clean_decimal
{
	return 0 unless defined $_[0];
	return 0 if ($_[0] =~ /^\s*$/);
	$_[0] =~ /^\s*(-?\d*\.?\d*)\s*$/;
	return $1;
}

sub clean_tgid
{
	return undef unless -r "$config{Root}/transaction_groups/$_[0]";
	return untaint($_[0]);
}

sub untaint
{
	$_[0] =~ /^(.*)$/;
	return $1;
}

sub unroot
{
	$_[0] =~ /$config{Root}\/(.*)/;
	return $1;
}

sub load_template
{
	my $tmpl = HTML::Template->new(filename => "$_[0]", global_vars => 1, case_sensitive => 1) or die;
	$tmpl->param(SN => $config{ShortName}) if $tmpl->query(name => 'SN');
	$tmpl->param(LN => $config{LongName}) if $tmpl->query(name => 'LN');
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
	set_status($tmpl, $status);
	print "Content-Type: text/html\n\n", $tmpl->output;
	exit;
}

sub whinge
{
	my ($whinge, $tmpl) = @_;
	$tmpl->param(STATUS => $whinge);
	print "Content-Type: text/html\n\n", $tmpl->output;
	exit;
}

sub gen_cds_p
{
	my $reason = $_[0];
	my $tmpl = load_template('create_ds_p.html');
	$tmpl->param(REASON => $reason);
	$tmpl->param(ROOT => $config{Root});

	return $tmpl;
}

sub create_datastore
{
	my ($cgi, $reason) = @_;

	if (defined $cgi->param('tmpl') and $cgi->param('tmpl') eq 'create_ds_p') {
		my $user_path = "$config{Root}/users";
		my $user = clean_username($cgi->param('user'));
		my $whinge = sub { whinge($_[0], gen_cds_p($reason)) };

		$whinge->('Disallowed characters in username') unless defined $user;
		$whinge->('Username too short') if length $user < 3;
		$whinge->('Username too long') if length $user > 10;
		my $cracklib_rv = fascist_check($cgi->param('pass'));
		$whinge->("Problem with password: $cracklib_rv") unless ($cracklib_rv eq 'ok');

		my $cryptpass = unix_md5_crypt($cgi->param('pass'));
		my %userdetails = (
			Password => $cryptpass,
			IsAdmin => undef,
		);
		(mkdir $user_path or die) unless (-d "$user_path");
		$git->init();
		$whinge->('Unable to get commit lock') unless try_commit_lock($cryptpass);
		# no session so not edit_token protected.  FIXME?
		try_commit_and_unlock(sub {
			write_simp_cfg("$user_path/$user", %userdetails);
			add_commit("$user_path/$user", 'CDS admin creation', $user);
		});
	} else {
		emit(gen_cds_p($reason));
	}
}

sub validate_admins
{
	my @users = glob("$config{Root}/users/*");

	my @valid_admins;
	foreach my $user (@users) {
		my %userdetails = read_simp_cfg($user);
		push(@valid_admins, $user) if (exists $userdetails{IsAdmin} and defined $userdetails{Password});
	}

	return scalar @valid_admins;
}

sub login
{
	my ($cgi, $userdetout) = @_;
	my $user = clean_username($cgi->param('user'));
	my $pass = $cgi->param('pass');
	my $whinge = sub { whinge('Login failed!', load_template('login.html')) };

	$whinge->() unless (-r "$config{Root}/users/$user");
	my %userdetails = read_simp_cfg("$config{Root}/users/$user");
	$whinge->() unless defined $userdetails{Password};

	my ($empty, $id, $salt, $encrypted) = split(/\$/, $userdetails{Password}, 4);

	my $cryptpass = unix_md5_crypt($pass, $salt);

	$whinge->() unless ($cryptpass eq $userdetails{Password});

	$userdetails{User} = $user;
	%{$userdetout} = %userdetails;
}

sub gen_login_nopw
{
	my $tmpl = load_template('login_nopw.html');

	my @users = glob("$config{Root}/users/*");
	my @userlist;

	foreach my $user (@users) {
		$user =~ /.*\/(.*)/;
		my %outputdetails = ( USER => $1 );
		push(@userlist, \%outputdetails);
	}
	$tmpl->param(PPL => \@userlist);

	return $tmpl;
}

sub login_nopw
{
	my ($cgi, $userdetout) = @_;
	my $user = clean_username($cgi->param('user'));

	whinge('Login failed!', gen_login_nopw) unless (-r "$config{Root}/users/$user");
	my %userdetails = read_simp_cfg("$config{Root}/users/$user");
	return 'No PW login on account with password set?' if defined $userdetails{Password};

	$userdetails{User} = $user;
	%{$userdetout} = %userdetails;
	return 'ok';
}

sub clear_old_session_locks
{
	my $sessid = $_[0];
	my @locks = glob("$config{Root}/*/.*.lock");
	push (@locks, "$config{Root}/.DSLOCK.lock");

	no autodie qw(open);	# file may not exist
	foreach my $lockfile (@locks) {
		$lockfile = untaint($lockfile);
		next unless open (my $lock, "$lockfile");

		unlink ($lockfile) if $sessid eq <$lock>;

		close ($lock);
	}
}

sub get_new_session
{
	my ($session, $cgi) = @_;
	my $last_tmpl = (defined $cgi->param('tmpl')) ? $cgi->param('tmpl') : '';

	my $expired = $session->is_expired();
	$session->delete();
	$session->flush();

	if (defined $cgi->cookie(CGI::Session->name())) {
		$cgi->cookie(CGI::Session->name()) =~ /^([a-f0-9]*)$/;	# hex untaint
		my $old_bocdata = File::Spec->tmpdir() . '/' . sprintf("${CGI::Session::Driver::file::FileName}_bocdata", $1);
		unlink $old_bocdata if -r $old_bocdata;
		clear_old_session_locks($1);
	}

	my $tmpl;
	my %userdetails;
	if ($last_tmpl eq 'login_nopw' and exists $config{Passwordless}) {
		$tmpl = load_template('login.html') if (login_nopw($cgi, \%userdetails) eq 'No PW login on account with password set?');
	} elsif ($last_tmpl eq 'login') {
		login($cgi, \%userdetails);
	} else {
		$tmpl = (exists $config{Passwordless}) ? gen_login_nopw : load_template('login.html');
	}
	($expired ? whinge('Session expired', $tmpl) : emit($tmpl)) if $tmpl;

	$session = CGI::Session->new($cgi) or die CGI::Session->errstr;
	print $session->header();
	$session->param('User', $userdetails{User});
	$session->param('Name', exists $userdetails{Name} ? $userdetails{Name} : $userdetails{User});
	$session->param('IsAdmin', (exists $userdetails{IsAdmin}));
	$session->expire('+10m');
	$session->flush();

	return $session;
}

sub gen_manage_accts
{
	my $people = $_[0];
	my $tmpl = load_template('manage_accts.html');
	my @accounts = $people ? glob("$config{Root}/users/*") : glob("$config{Root}/accounts/*");
	my @acctlist;

	foreach my $acct (@accounts) {
		my %acctdetails = read_simp_cfg($acct);
		my %outputdetails;
		$acct =~ /.*\/(.*)/;
		if ($people) {
			%outputdetails = (
				ACCT => $1,
				NAME => $acctdetails{Name},
				EMAIL => $acctdetails{email},
			);
		} else {
			%outputdetails = (
				ACCT => $1,
				NAME => $acctdetails{Name},
			);
		}
		push(@acctlist, \%outputdetails);
	}
	$tmpl->param(ACCTS => \@acctlist);
	$tmpl->param(USER_ACCT => 1) if $people;

	return $tmpl;
}

sub gen_add_edit_acc
{
	my ($edit_acct, $person, $etoken) = @_;
	my $tmpl = load_template('edit_acct.html', $etoken);

	if ($edit_acct) {
		$tmpl->param(EACCT => $edit_acct);
		my %acctdetails = read_simp_cfg($person ? "$config{Root}/users/$edit_acct" : "$config{Root}/accounts/$edit_acct");
		$tmpl->param(ACCT => $edit_acct);
		$tmpl->param(NAME => $acctdetails{Name});
		$tmpl->param(EMAIL => $acctdetails{email});
		$tmpl->param(ADDRESS => $acctdetails{Address});
	}
	$tmpl->param(USER_ACCT => 1) if $person;

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

sub gen_edit_simp_trans
{
	my $tmpl = load_template('edit_simp_trans.html', $_[0]);

	my %vaccts = query_all_htsv_in_path("$config{Root}/accounts", 'Name');
	my %rvaccts = reverse (%vaccts);
	my @sorted_vaccts = map ($rvaccts{$_}, sort keys %rvaccts);

	my %cfg = read_htsv("$config{Root}/config_simp_trans", 1);
	my $num_rows = ($#{$cfg{Description}} >= 0) ? scalar @{$cfg{Description}} + min(5, 30 - scalar @{$cfg{Description}}) : 10;
	my @rows;
	foreach my $row (0 .. ($num_rows - 1)) {
		my @rowoptions = map ({ O => $vaccts{$_}, V => $_, S => (defined $cfg{DebitAcct}[$row]) ? $cfg{DebitAcct}[$row] eq $_ : undef }, @sorted_vaccts);
		push (@rows, { ACCTS => \@rowoptions, D => $cfg{Description}[$row], R => $row });
	}
	$tmpl->param(ROWS => \@rows);

	return $tmpl;
}

sub despatch_admin
{
	my $session = $_[0];
	my $sessid = $session->id();
	my $cgi = $session->query();
	my $etoken = $cgi->param('etoken');

	return if (defined $cgi->param('logout'));

	if ($cgi->param('tmpl') eq 'login') {
		my $tmpl = load_template('treasurer_cp.html');
		print $tmpl->output;
		exit;
	}
	if ($cgi->param('tmpl') eq 'tcp') {
		my $whinge = sub { whinge('Couldn\'t get edit lock for configuration file', load_template('treasurer_cp.html')) };
		emit(gen_manage_accts(1)) if (defined $cgi->param('view_ppl'));
		emit(gen_manage_accts(0)) if (defined $cgi->param('view_accts'));
		if (defined $cgi->param('edit_inst_cfg')) {
			$whinge->() unless try_lock("$config{Root}/config", $sessid);
			emit(gen_edit_inst_cfg(get_edit_token($sessid, 'edit_inst_cfg')));
		}
		if (defined $cgi->param('edit_simp_trans')) {
			$whinge->() unless try_lock("$config{Root}/config_simp_trans", $sessid);
			emit(gen_edit_simp_trans(get_edit_token($sessid, 'edit_simp_trans')));
		}
	}
	if ($cgi->param('tmpl') eq 'edit_acct') {
		my $edit_acct = clean_username($cgi->param('eacct'));
		my $new_acct = clean_username($cgi->param('account'));
		my $person = defined $cgi->param('email');
		my $root = $config{Root};
		my $acct_path = $person ? "$root/users" : "$root/accounts";

		if (defined $cgi->param('save')) {
			my $fullname = clean_text($cgi->param('fullname'));
			my $email = clean_email($cgi->param('email'));
			my $address = clean_text($cgi->param('address'));
			my $rename = ($edit_acct and $edit_acct ne $new_acct);
			my $whinge = sub { whinge($_[0], gen_add_edit_acc($edit_acct, $person, $etoken)) };

			whinge('Account to be edited not found (resubmission after rename?)', gen_manage_accts($person)) if $edit_acct and not -r ("$acct_path/$edit_acct");
			$whinge->('Disallowed characters in short name') unless defined $new_acct;
			$whinge->('Short name too short') if length $new_acct < 3;
			$whinge->('Short name too long') if length $new_acct > 10;
			$whinge->('Short name is already taken') if ((-e "$root/accounts/$new_acct" or -e "$root/users/$new_acct") and ((not defined $edit_acct) or $rename));
			$whinge->('Full name too short') unless defined $fullname;
			$whinge->('Full name too long') if length $fullname > 100;
			if ($person) {
				$whinge->('Not an email address') unless defined $email;
				$whinge->('No real-world contact details given') unless defined $address;
			}

			my %userdetails;
			%userdetails = read_simp_cfg("$acct_path/$edit_acct") if ($edit_acct);
			$userdetails{Name} = $fullname;
			if ($person) {
				$userdetails{email} = $email;
				$userdetails{Address} = $address;
			} else {
				(mkdir $acct_path or die) unless (-d $acct_path);
			}

			$whinge->('Unable to get commit lock') unless try_commit_lock($sessid);
			if ($rename and glob("$config{Root}/transaction_groups/.*.lock")) {
				un_commit_lock;
				$whinge->('Cannot perform account rename at present: transaction groups busy');
			}
			bad_token_whinge(gen_manage_accts($person)) unless redeem_edit_token($sessid, $edit_acct ? "edit_$edit_acct" : $person ? 'add_acct' : 'add_vacct', $etoken);
			if (defined $edit_acct and $edit_acct eq $session->param('User')) {
				$session->param('User', $new_acct);
				$session->param('Name', $userdetails{Name});
				$session->flush();
			}
			try_commit_and_unlock(sub {
				if ($rename) {
					my @tgs = glob("$config{Root}/transaction_groups/*");
					foreach my $tg (@tgs) {
						$tg = untaint($tg);
						my %tgdetails = read_tg($tg);

						@{$tgdetails{Creditor}} = map (($_ eq $edit_acct) ? $new_acct : $_, @{$tgdetails{Creditor}});
						@{$tgdetails{Headings}} = map (($_ eq $edit_acct) ? $new_acct : $_, @{$tgdetails{Headings}});
						$tgdetails{$new_acct} = delete $tgdetails{$edit_acct} if exists $tgdetails{$edit_acct};

						write_tg($tg, %tgdetails);
						$git->add($tg);
					}
					$git->mv("$acct_path/$edit_acct", "$acct_path/$new_acct") if $rename;
				}
				write_simp_cfg("$acct_path/$new_acct", %userdetails);
				if ($rename) {
					add_commit("$acct_path/$new_acct", 'Rename ' . unroot("$acct_path/$edit_acct") . ' to ' . unroot("$acct_path/$new_acct"), $session);
				} else {
					add_commit("$acct_path/$new_acct", unroot("$acct_path/$new_acct") . ': ' . ($edit_acct ? 'modified' : 'created'), $session);
				}
			}, $edit_acct ? "$acct_path/$edit_acct" : undef);
		} else {
			unlock("$acct_path/$edit_acct") if ($edit_acct and -r "$acct_path/$edit_acct");
			redeem_edit_token($sessid, $edit_acct ? "edit_$edit_acct" : $person ? 'add_acct' : 'add_vacct', $etoken);
		}

		if ($edit_acct) {
			emit_with_status((defined $cgi->param('save')) ? "Saved edits to account \"$new_acct\"" : "Edit account cancelled", gen_manage_accts($person));
		} else {
			emit_with_status((defined $cgi->param('save')) ? "Added account \"$new_acct\"" : "Add account cancelled", gen_manage_accts($person));
		}
	}
	if ($cgi->param('tmpl') eq 'view_ppl' or $cgi->param('tmpl') eq 'view_vaccts') {
		if (defined $cgi->param('to_cp')) {
			emit(load_template('treasurer_cp.html'));
		} else {
			my $acct;
			my $delete = 0;
			my $person = $cgi->param('tmpl') eq 'view_ppl';

			foreach my $p ($cgi->param) {
				$p =~ /edit_(.*)/;
				$acct = $1;
				last if defined $acct;
				$p =~ /del_(.*)/;
				$acct = $1;
				$delete = 1 if defined $acct;
				last if defined $acct;
			}

			my $acct_file = $person ? "$config{Root}/users/$acct" : "$config{Root}/accounts/$acct" if $acct;
			unless ($delete) {
				my $whinge = sub { whinge($_[0], gen_manage_accts($person)) };
				if ($acct) {
					$whinge->("Couldn't get edit lock for account \"$acct\"") unless try_lock($acct_file, $sessid);
					unless (-r $acct_file) {
						unlock($acct_file);
						$whinge->("Couldn't edit account \"$acct\", file disappeared");
					}
				}
				my $etoken = get_edit_token($sessid, $acct ? "edit_$acct" : $person ? 'add_acct' : 'add_vacct');
				emit(gen_add_edit_acc($acct, $person, $etoken));
			} else {
				unlink($acct_file) or die;
				emit_with_status("Deleted account \"$acct\"", gen_manage_accts($person));
			}
		}
	}
	if ($cgi->param('tmpl') eq 'edit_inst_cfg') {
		my $cfg_file = "$config{Root}/config";

		if (defined $cgi->param('save')) {
			my %inst_cfg;

			foreach my $param ($cgi->param()) {
				next if ($param eq 'tmpl' or $param eq 'etoken' or $param eq 'save');
				$inst_cfg{$param} = clean_text($cgi->param($param));
			}

			whinge('Unable to get commit lock', gen_edit_inst_cfg($etoken)) unless try_commit_lock($sessid);
			bad_token_whinge(load_template('treasurer_cp.html')) unless redeem_edit_token($sessid, 'edit_inst_cfg', $etoken);
			try_commit_and_unlock(sub {
				write_simp_cfg($cfg_file, %inst_cfg);
				add_commit($cfg_file, 'config: installation config modified', $session);
			}, $cfg_file);
			update_global_config(%inst_cfg);
		} else {
			unlock($cfg_file);
			redeem_edit_token($sessid, 'edit_inst_cfg', $etoken);
		}

		emit_with_status((defined $cgi->param('save')) ? "Saved edits to config" : "Edit config cancelled", load_template('treasurer_cp.html'));
	}
	if ($cgi->param('tmpl') eq 'edit_simp_trans') {
		my $cfg_file = "$config{Root}/config_simp_trans";

		if (defined $cgi->param('save')) {
			my %cfg = ( Headings => [ 'DebitAcct', 'Description' ] );
			my $whinge = sub { whinge($_[0], gen_edit_simp_trans($etoken)) };

			my $max_rows = -1;
			$max_rows++ while ($max_rows < 100 and defined $cgi->param("DebitAcct_" . ($max_rows + 1)));
			$whinge->('No transactions?') unless $max_rows >= 0;

			my %vaccts = query_all_htsv_in_path("$config{Root}/accounts", 'Name');

			@{$cfg{Description}} = ();
			@{$cfg{DebitAcct}} = ();
			foreach my $row (0 .. $max_rows) {
				my $desc = clean_text($cgi->param("Description_$row"));
				my $acct = clean_username($cgi->param("DebitAcct_$row"));
				next unless $desc or $acct;
				$whinge->('Missing account') unless $acct;
				$whinge->('Missing description') unless $desc;
				$whinge->("Non-existent account \"$acct\"") unless exists $vaccts{$acct};
				push (@{$cfg{Description}}, $desc);
				push (@{$cfg{DebitAcct}}, $acct);
			}

			$whinge->('Unable to get commit lock') unless try_commit_lock($sessid);
			bad_token_whinge(load_template('treasurer_cp.html')) unless redeem_edit_token($sessid, 'edit_simp_trans', $etoken);
			try_commit_and_unlock(sub {
				write_htsv($cfg_file, \%cfg, 11);
				add_commit($cfg_file, 'config_simp_trans: simple transaction types modified', $session);
			}, $cfg_file);
		} else {
			unlock($cfg_file);
			redeem_edit_token($sessid, 'edit_simp_trans', $etoken);
		}

		emit_with_status((defined $cgi->param('save')) ? "Saved edits to config" : "Edit config cancelled", load_template('treasurer_cp.html'));
	}
}

sub gen_add_swap
{
	my ($swap, $session, $etoken) = @_;
	my $tmpl = load_template('add_swap.html', $etoken);

	my %accts = query_all_htsv_in_path("$config{Root}/users", 'Name');
	my %raccts = reverse (%accts);
	my @sorted_accts = map ($raccts{$_}, sort keys %raccts);
	my @pploptions = map ({ O => $accts{$_}, V => $_, S => $session->param('User') eq $_ }, @sorted_accts);

	my @debtaccts;
	if ($swap) {
		@debtaccts = map ({ O => $accts{$_}, V => $_ }, @sorted_accts);
	} else {
		my %cfg = read_htsv("$config{Root}/config_simp_trans", 1);
		@debtaccts = map ({ O => $cfg{Description}[$_], V => "$cfg{DebitAcct}[$_]!$cfg{Description}[$_]" }, 0 .. $#{$cfg{Description}});
	}

	$tmpl->param(SWAP => $swap, PPL => \@pploptions, DEBTACCTS => \@debtaccts);

	return $tmpl;
}

sub gen_add_split
{
	my ($session, $etoken) = @_;
	my $tmpl = load_template('add_split.html', $etoken);

	my %accts = query_all_htsv_in_path("$config{Root}/users", 'Name');
	my %raccts = reverse (%accts);
	my @pploptions = map ({ NAME => $accts{$_}, A => $_ }, map ($raccts{$_}, sort keys %raccts));

	$tmpl->param(PPL => \@pploptions);

	return $tmpl;
}

sub query_all_htsv_in_path
{
	my ($path, $key) = @_;

	my @accts = glob("$path/*");
	my %response;

	foreach my $acct (@accts) {
		my %acctdetails = read_htsv($acct);
		$acct =~ /.*\/(.*)/;
		$response{$1} = $acctdetails{$key};
	}

	return %response;
}

sub get_acct_name_map
{
	my %ppl = query_all_htsv_in_path("$config{Root}/users", 'Name');
	my %vaccts = query_all_htsv_in_path("$config{Root}/accounts", 'Name');
	return (%ppl, %vaccts);
}

sub gen_manage_tgs
{
	my $tmpl = load_template('manage_transactions.html');

	my %acct_names = get_acct_name_map;
	my %tg_dates = query_all_htsv_in_path("$config{Root}/transaction_groups", 'Date');
	my %rtgds;
	push (@{$rtgds{$tg_dates{$_}}}, $_) foreach keys %tg_dates;	# arrgh non-unique dates
	my @sorted_tgs = map (@{$rtgds{$_->[0]}}, sort { $a->[1] cmp $b->[1] } map ([ $_, sprintf("%04d%02d%02d", (split '\.', $_)[2,1,0]) ], keys %rtgds));	# Schwartzian transform ftw
	my @tglist;

	foreach my $tg (@sorted_tgs) {
		my %tgdetails = read_tg("$config{Root}/transaction_groups/$tg");

		my %summary;
		my $sum_str = "";
		foreach my $i (0 .. $#{$tgdetails{Creditor}}) {
			my $acct = $tgdetails{Creditor}[$i];
			unless (defined $acct_names{$acct}) {
				$sum_str = "TRANSACTION GROUP REFERENCES UNKNOWN ACCOUNT ($acct)  ";
				last;
			}
			next if exists $summary{$acct};
			$summary{$acct} = 0;
			foreach my $j ($i .. $#{$tgdetails{Creditor}}) {
				next unless $tgdetails{Creditor}[$j] eq $acct;
				$summary{$acct} += $tgdetails{Amount}[$j];
			}
			$sum_str .= "$acct_names{$acct} " . (($summary{$acct} < 0) ? '' : '+') . $summary{$acct} . ", ";
		}
		foreach my $acct (@{$tgdetails{Headings}}[2 .. ($#{$tgdetails{Headings}} - 1)]) {
			$sum_str = "TRANSACTION GROUP REFERENCES UNKNOWN ACCOUNT ($acct)  " unless (defined $acct_names{$acct});
		}

		my %outputdetails = (
				ACC => $tg,
				NAME => $tgdetails{Name},
				DATE => $tgdetails{Date},
				SUMMARY => substr($sum_str, 0, -2),
		);
		push(@tglist, \%outputdetails);
	}
	$tmpl->param(TGS => \@tglist);

	return $tmpl;
}

sub sort_accts(\%\%)
{
	my ($ppl, $vaccts) = @_;

	my @sorted = ( 'Creditor', 'Amount' );
	push (@sorted, map ($ppl->{$_}, sort keys %$ppl));
	push (@sorted, map ($vaccts->{$_}, sort keys %$vaccts));
	push (@sorted, 'Description');

	return @sorted;
}

sub gen_tg
{
	my ($tg_file, $edit_mode, $session, $etoken) = @_;
	my %tgdetails;

	if ($tg_file) {
		%tgdetails = read_tg($tg_file);
		push (@{$tgdetails{Creditor}}, ($session->param('User')) x min(5, 100 - scalar @{$tgdetails{Creditor}})) if $edit_mode;
	} else {
		push (@{$tgdetails{Creditor}}, ($session->param('User')) x 10);
	}

	my $tmpl = load_template('edit_tg.html', $etoken);

	my %ppl = query_all_htsv_in_path("$config{Root}/users", 'Name');
	my %vaccts = query_all_htsv_in_path("$config{Root}/accounts", 'Name');
	my %acct_names = (%ppl, %vaccts);
	my @sorted_accts = sort_accts(%{{reverse %ppl}}, %{{reverse %vaccts}});

	foreach my $acct (@sorted_accts) {
		next if $acct eq 'Description';
		my $lower = exists $tgdetails{$acct} ? scalar(@{$tgdetails{$acct}}) : 0;
		push (@{$tgdetails{$acct}}, (0) x (scalar @{$tgdetails{Creditor}} - $lower));
	}
	@{$tgdetails{Headings}} = @sorted_accts;

	if ($tg_file) {
		$tg_file =~ /\/([^\/]+)$/;
		$tmpl->param(TG_ID => $1);
	}
	$tmpl->param(RO => (!$edit_mode and $tg_file));
	$tmpl->param(NAME => $tgdetails{Name});
	$tmpl->param(DATE => $tgdetails{Date});
	$tmpl->param(NOACCTS => scalar keys %acct_names);
	my @headings;
	foreach my $key (@{$tgdetails{Headings}}) {
		next unless exists $acct_names{$key};
		my %heading = ( H => $acct_names{$key} );
		push(@headings, \%heading);
	}
	$tmpl->param(HEADINGS => \@headings);

	my @rows;
	foreach my $row (0 .. $#{$tgdetails{Creditor}}) {
		my @rowoptions;
		foreach my $key (@{$tgdetails{Headings}}) {
			next unless exists $acct_names{$key};
			my %options = ( O => $acct_names{$key}, V => $key, S => $tgdetails{Creditor}[$row] eq $key );
			push(@rowoptions, \%options);
		}
		my @rowcontents;
		foreach my $key (@{$tgdetails{Headings}}[1 .. $#{$tgdetails{Headings}}]) {
			my %data = ( D => $tgdetails{$key}[$row], N => "${key}_$row" );
			push(@rowcontents, \%data);
		}
		push (@rows, { R => \@rowcontents, CREDS => \@rowoptions, CRNAME => "Creditor_$row" });
	}
	$tmpl->param(ROWS => \@rows);

	return $tmpl;
}

sub new_tgfile
{
	my $id;
	my $tg_path = "$config{Root}/transaction_groups";
	(mkdir "$tg_path" or die) unless (-d $tg_path);
	do {
		$id = create_UUID_as_string(UUID_V4);
	} while (-e "$tg_path/$id");
	return "$tg_path/$id";
}

sub despatch_user
{
	my $session = $_[0];
	my $sessid = $session->id();
	my $cgi = $session->query();
	my $etoken = $cgi->param('etoken');

	return if (defined $cgi->param('logout'));

	if ($cgi->param('tmpl') eq 'login_nopw') {
		my $tmpl = load_template('user_cp.html');
		print $tmpl->output;
		exit;
	}
	if ($cgi->param('tmpl') eq 'ucp') {
		if (defined $cgi->param('add_swap') or defined $cgi->param('add_vacct_expense')) {
			my $swap = defined $cgi->param('add_swap');
			emit(gen_add_swap($swap, $session, get_edit_token($sessid, $swap ? 'add_swap' : 'add_vacct_expense')));
		}
		if (defined $cgi->param('add_split')) {
			emit(gen_add_split($session, get_edit_token($sessid, 'add_split')));
		}
		if (defined $cgi->param('manage_tgs')) {
			emit(gen_manage_tgs);
		}
	}
	if ($cgi->param('tmpl') eq 'add_swap' or $cgi->param('tmpl') eq 'add_vacct_expense') {
		my $swap = ($cgi->param('tmpl') eq 'add_swap');

		if (defined $cgi->param('save')) {
			my %tg;
			my $whinge = sub { whinge($_[0], gen_add_swap($swap, $session, $etoken)) };

			my %acct_names = query_all_htsv_in_path("$config{Root}/users", 'Name');
			my $cred = clean_username($cgi->param('Creditor'));
			$whinge->("Non-existent account \"$cred\"") unless exists $acct_names{$cred};
			push (@{$tg{Creditor}}, $cred);

			my $amnt = clean_decimal($cgi->param('Amount'));
			$whinge->('Non-numerics in amount') unless defined $amnt;
			$whinge->('Missing amount') if $amnt == 0;
			push (@{$tg{Amount}}, $amnt);

			my $date = clean_text($cgi->param('tg_date'));
			my ($pd_secs, $pd_error) = parsedate($date, (FUZZY => 1, UK => 1, DATE_REQUIRED => 1, PREFER_PAST => 1, WHOLE => 1));
			$whinge->('Unparsable date') if $pd_error;
			$tg{Date} = join('.', ((localtime($pd_secs))[3], (localtime($pd_secs))[4] + 1, (localtime($pd_secs))[5] + 1900));

			push (@{$tg{Description}}, clean_text($cgi->param('Description')));

			my $debtor;
			if ($swap) {
				$whinge->('Missing description') unless defined @{$tg{Description}}[0];
				$debtor = clean_username($cgi->param('Debtor'));
				$whinge->("Non-existent account \"$debtor\"") unless exists $acct_names{$debtor};
				my @split_desc = split (' ', @{$tg{Description}}[0]);
				$tg{Name} = "Swap: $acct_names{$debtor}->$acct_names{$cred} for $split_desc[0]...";
			} else {
				my %vacct_names = query_all_htsv_in_path("$config{Root}/accounts", 'Name');
				my $type = clean_text($cgi->param('Debtor'));
				$whinge->('Broken expense type') unless defined $type;
				($debtor, $type) = split('!', $type, 2);
				$whinge->("Non-existent account \"$debtor\"") unless exists $vacct_names{$debtor};
				$whinge->('Broken expense type') unless defined $type;
				$tg{Name} = "Expense: $type";
			}
			push (@{$tg{$debtor}}, 1);

			@{$tg{Headings}} = ('Creditor', 'Amount', $debtor, 'Description');

			$whinge->('Unable to get commit lock') unless try_commit_lock($sessid);
			bad_token_whinge(load_template('user_cp.html')) unless redeem_edit_token($sessid, $swap ? 'add_swap' : 'add_vacct_expense', $etoken);
			try_commit_and_unlock(sub {
				my $tgfile = new_tgfile;
				write_tg($tgfile, %tg);
				my @split_tgf = split('-', unroot($tgfile));
				add_commit($tgfile, "$split_tgf[0]...: TG \"$tg{Name}\" created", $session);
			});
		} else {
			redeem_edit_token($sessid, $swap ? 'add_swap' : 'add_vacct_expense', $etoken);
		}

		if ($swap) {
			emit_with_status((defined $cgi->param('save')) ? "Swap saved" : "Add swap cancelled", load_template('user_cp.html'));
		} else {
			emit_with_status((defined $cgi->param('save')) ? "Expense saved" : "Add expense cancelled", load_template('user_cp.html'));
		}
	}
	if ($cgi->param('tmpl') eq 'add_split') {
		if (defined $cgi->param('save')) {
			my %tg;
			my $whinge = sub { whinge($_[0], gen_add_split($session, $etoken)) };

			$tg{Name} = clean_text($cgi->param('tg_name'));
			$whinge->('No transaction group name supplied') unless defined $tg{Name};

			my $date = clean_text($cgi->param('tg_date'));
			my ($pd_secs, $pd_error) = parsedate($date, (FUZZY => 1, UK => 1, DATE_REQUIRED => 1, PREFER_PAST => 1, WHOLE => 1));
			$whinge->('Unparsable date') if $pd_error;
			$tg{Date} = join('.', ((localtime($pd_secs))[3], (localtime($pd_secs))[4] + 1, (localtime($pd_secs))[5] + 1900));

			my %acct_names = query_all_htsv_in_path("$config{Root}/users", 'Name');
			my @cred_accts = map { s/^Cred_//; $_ } grep (/^Cred_.*$/, $cgi->param);
			my %creds;
			foreach my $acct (@cred_accts) {
				$whinge->("Non-existent account \"$acct\"") unless exists $acct_names{$acct};
				my $amnt = clean_decimal($cgi->param("Cred_$acct"));
				$whinge->('Non-numerics in creditor amount') unless defined $amnt;
				$creds{$acct} = $amnt unless $amnt == 0;
			}
			$whinge->('No creditors?') unless scalar keys %creds > 0;

			if (scalar keys %creds > 1) {
				push (@{$tg{Creditor}}, 'THIS');
				push (@{$tg{Amount}}, 1);
				push (@{$tg{THIS}}, undef);
			}
			foreach my $cred (keys %creds) {
				push (@{$tg{Creditor}}, $cred);
				push (@{$tg{Amount}}, $creds{$cred});
				push (@{$tg{THIS}}, 1) if scalar keys %creds > 1;
			}

			my @debt_accts = map { s/^Debt_//; $_ } grep (/^Debt_.*$/, $cgi->param);
			my %debts;
			foreach my $acct (@debt_accts) {
				$whinge->("Non-existent account \"$acct\"") unless exists $acct_names{$acct};
				my $amnt = clean_decimal($cgi->param("Debt_$acct"));
				$whinge->('Non-numerics in debtor amount') unless defined $amnt;
				$debts{$acct} = $amnt unless $amnt == 0;
			}
			$whinge->('No debtors?') unless scalar keys %debts > 0;

			push (@{$tg{$_}}, $debts{$_}) foreach (keys %debts);

			push (@{$tg{Description}}, clean_text($cgi->param('Description')));

			@{$tg{Headings}} = ('Creditor', 'Amount' );
			push (@{$tg{Headings}}, 'THIS') if scalar keys %creds > 1;
			my %rdebts = reverse %debts;
			push (@{$tg{Headings}}, $_) foreach map ($rdebts{$_}, sort keys %rdebts);
			push (@{$tg{Headings}}, 'Description');

			$whinge->('Unable to get commit lock') unless try_commit_lock($sessid);
			bad_token_whinge(load_template('user_cp.html')) unless redeem_edit_token($sessid, 'add_split', $etoken);
			try_commit_and_unlock(sub {
				my $tgfile = new_tgfile;
				write_tg($tgfile, %tg);
				my @split_tgf = split('-', unroot($tgfile));
				add_commit($tgfile, "$split_tgf[0]...: TG \"$tg{Name}\" created", $session);
			});
		} else {
			redeem_edit_token($sessid, 'add_split', $etoken);
		}

		emit_with_status((defined $cgi->param('save')) ? "Split saved" : "Add split cancelled", load_template('user_cp.html'));
	}
	if ($cgi->param('tmpl') eq 'manage_tgs') {
		if (defined $cgi->param('view') or defined $cgi->param('add')) {
			my $view = $cgi->param('view');
			my $tg;

			if ($view) {
				$tg = "$config{Root}/transaction_groups/" . $view;
				emit(gen_manage_tgs) unless (-r $tg);
			}

			emit(gen_tg($tg, 0, $session, $view ? undef : get_edit_token($sessid, 'add_tg')));
		} elsif (defined $cgi->param('to_cp')) {
			emit(load_template('user_cp.html'));
		}
	}
	if ($cgi->param('tmpl') eq 'edit_tg') {
		my $edit_id = (defined $cgi->param('tg_id') and clean_tgid($cgi->param('tg_id'))) ? clean_tgid($cgi->param('tg_id')) : undef;
		my $tgfile = $edit_id ? "$config{Root}/transaction_groups/$edit_id" : undef;

		if (defined $cgi->param('manage_tgs')) {
			emit(gen_manage_tgs);
		} elsif (defined $cgi->param('edit')) {
			whinge("Couldn't get edit lock for transaction group \"$edit_id\"", gen_manage_tgs) unless try_tg_lock($tgfile, $sessid);
			unless (-r $tgfile) {
				unlock($tgfile);
				whinge("Couldn't edit transaction group \"$edit_id\", file disappeared", gen_manage_tgs);
			}
			emit(gen_tg($tgfile, 1, $session, get_edit_token($sessid, "edit_$edit_id")));
		}

		# only left with save and cancel now
		my %tg;

		if (defined $cgi->param('save')) {
			my $whinge = sub { whinge($_[0], gen_tg($tgfile, 1, $session, $etoken)) };

			$tg{Name} = clean_text($cgi->param('tg_name'));
			$whinge->('No transaction group name supplied') unless defined $tg{Name};
			my $date = clean_text($cgi->param('tg_date'));
			my ($pd_secs, $pd_error) = parsedate($date, (FUZZY => 1, UK => 1, DATE_REQUIRED => 1, NO_RELATIVE => 1));
			$whinge->('Unparsable date') if $pd_error;
			$tg{Date} = join('.', ((localtime($pd_secs))[3], (localtime($pd_secs))[4] + 1, (localtime($pd_secs))[5] + 1900));

			my $max_rows = -1;
			$max_rows++ while ($max_rows < 100 and defined clean_username($cgi->param("Creditor_" . ($max_rows + 1))));
			$whinge->('No transactions?') unless $max_rows >= 0;

			my %acct_names = get_acct_name_map;
			my @accts = map { s/_0$//; $_ } grep ((/^(.*)_0$/ and $1 ne 'Creditor' and $1 ne 'Amount' and $1 ne 'Description'), $cgi->param);
			foreach my $acct (@accts) {
				$whinge->("Non-existent account \"$acct\"") unless exists $acct_names{$acct};
			}

			foreach my $row (0 .. $max_rows) {
				my $cred = clean_username($cgi->param("Creditor_$row"));
				my $amnt = clean_decimal($cgi->param("Amount_$row"));
				my $desc = clean_text($cgi->param("Description_$row"));
				$whinge->("Non-existent account \"$cred\"") unless exists $acct_names{$cred};
				$whinge->('Non-numerics in amount') unless defined $amnt;
				my $set = $amnt == 0 ? 0 : 10000;
				my @rowshares;
				foreach my $acct (@accts) {
					push(@rowshares, clean_decimal($cgi->param("${acct}_$row")));
					$whinge->('Non-numerics in debt share') unless defined $rowshares[$#rowshares];
					$set++ unless $rowshares[$#rowshares] == 0;
				}

				if ($set > 10000) {
					push (@{$tg{Creditor}}, $cred);
					push (@{$tg{Amount}}, $amnt);
					push (@{$tg{Description}}, $desc);
					push (@{$tg{$accts[$_]}}, $rowshares[$_]) foreach (0 .. $#accts);
				} elsif ($set > 0 or $cred ne $session->param('User')) {
					$whinge->('Insufficient values set in row');
				}
			}

			my %all_ppl = query_all_htsv_in_path("$config{Root}/users", 'Name');
			my %all_vaccts = query_all_htsv_in_path("$config{Root}/accounts", 'Name');
			my (%ppl, %vaccts);
			((exists $all_ppl{$_}) ? $ppl{$all_ppl{$_}} : $vaccts{$all_vaccts{$_}}) = $_ foreach (@accts);
			@{$tg{Headings}} = sort_accts(%ppl, %vaccts);

			$whinge->('Unable to get commit lock') unless try_commit_lock($sessid);
			bad_token_whinge(gen_manage_tgs) unless redeem_edit_token($sessid, $edit_id ? "edit_$edit_id" : 'add_tg', $etoken);
			try_commit_and_unlock(sub {
				$tgfile = new_tgfile unless ($tgfile);
				write_tg($tgfile, %tg);
				my @split_tgf = split('-', unroot($tgfile));
				add_commit($tgfile, "$split_tgf[0]...: TG \"$tg{Name}\" " . ($edit_id ? 'modified' : 'created'), $session);
			}, $edit_id ? $tgfile : undef);
		} else {
			unlock($tgfile) if $tgfile;
			redeem_edit_token($sessid, $edit_id ? "edit_$edit_id" : 'add_tg', $etoken);
		}

		$tgfile =~ /.*\/([^\/]{4})[^\/]*$/;
		if ($edit_id) {
			emit_with_status((defined $cgi->param('save')) ? "Saved edits to \"$tg{Name}\" ($1) transaction group" : "Edit cancelled", gen_tg($tgfile, 0, $session, undef));
		} else {
			emit_with_status((defined $cgi->param('save')) ? "Added transaction group \"$tg{Name}\" ($1)" : "Add transaction group cancelled", gen_manage_tgs);
		}
	}
}

my $cgi = CGI->new;

%config = read_simp_cfg('boc_config');

die 'Can\'t find value for "Root" key in ./boc_config' unless defined $config{Root};
die 'Can\'t find value for "TemplateDir" key in ./boc_config' unless defined $config{TemplateDir};
die "The BoC root directory (set as $config{Root} in ./boc_config) must exist and be readable and writable by the webserver --" unless (-r $config{Root} and -w $config{Root});
$ENV{HTML_TEMPLATE_ROOT} = $config{TemplateDir};
$ENV{PATH} = "/bin:/usr/bin";
$git = Git::Wrapper->new($config{Root});
update_global_config(read_simp_cfg("$config{Root}/config", 1));

create_datastore($cgi, "$config{Root} does not appear to be a BoC data store") unless (-d "$config{Root}/users");
create_datastore($cgi, 'No useable administrator account') unless validate_admins;

my $session = CGI::Session->load($cgi) or die CGI::Session->errstr;
$session = get_new_session($session, $cgi) if ($session->is_empty or (not defined $cgi->param('tmpl')) or $cgi->param('tmpl') =~ m/^login(_nopw)?$/);

$session->param('IsAdmin') ? despatch_admin($session) : despatch_user($session);

# the despatchers fall through if the requested action is unknown: make them log in again!
get_new_session($session, $cgi);
