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
use HTML::Entities;
use HTML::Template;
use List::Util qw(first min);
use Time::ParseDate;
use UUID::Tiny;
use YAML::XS;

use lib '.';
use HeadedTSV ();
use TG ();

our %config;

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

sub get_add_token
{
	my ($sessid, $add_obj_str) = @_;

	my $pass = create_UUID_as_string(UUID_V4);
	push_session_data($sessid, $add_obj_str, $pass);

	return $pass;
}

sub redeem_add_token
{
	return pop_session_data(@_);
}

sub try_lock
{
	my ($file, $token, $sessid) = @_;
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

	print $lock "$token\n$sessid";

	close ($lock);

	return $token;
}

sub try_unlock
{
	my ($file, $token) = @_;
	my $lockfile = "$file.lock";
	$lockfile =~ s/^(.*\/)([^\/]*)/$1.$2/;	# insert a . to hide file (especially from directory globbing)
	my $win = 0;

	no autodie qw(open);	# file may not exist
	return 0 unless open (my $lock, "$lockfile");

	$win = unlink ($lockfile) if "$token\n" eq <$lock>;

	close ($lock);

	return $win;
}

sub encode_for_html
{
	my $escaped = encode_entities(decode_entities($_[0]), '^A-Za-z0-9!%^*()\-_=+{}\[\];:@#~,./?\\\ ');
	$escaped =~ s/&#39;/&apos;/g;
	return $escaped;
}

sub encode_for_file
{
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

	HeadedTSV::write_htsv($file, \%config);
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

	TG::write_tg($file, %content);
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

	HeadedTSV::write_htsv($file, $content, $ts);
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

		whinge('Disallowed characters in username', gen_cds_p($reason)) unless defined $user;
		whinge('Username too short', gen_cds_p($reason)) if length $user < 3;
		whinge('Username too long', gen_cds_p($reason)) if length $user > 10;
		my $cracklib_rv = fascist_check($cgi->param('pass'));
		whinge("Problem with password: $cracklib_rv", gen_cds_p($reason)) unless ($cracklib_rv eq 'ok');

		my $cryptpass = unix_md5_crypt($cgi->param('pass'));
		my %userdetails = (
			Password => $cryptpass,
			IsAdmin => undef,
		);
		(mkdir $user_path or die) unless (-d "$user_path");
		write_simp_cfg("$user_path$user", %userdetails);	# no session so not edit_token protected.  FIXME?
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

	whinge('Login failed!', load_template('login.html')) unless (-r "$config{Root}/users/$user");
	my %userdetails = read_simp_cfg("$config{Root}/users/$user");
	whinge('Login failed!', load_template('login.html')) unless defined $userdetails{Password};

	my ($empty, $id, $salt, $encrypted) = split(/\$/, $userdetails{Password}, 4);

	my $cryptpass = unix_md5_crypt($pass, $salt);

	whinge('Login failed!', load_template('login.html')) unless ($cryptpass eq $userdetails{Password});

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

	no autodie qw(open);	# file may not exist
	foreach my $lockfile (@locks) {
		$lockfile = untaint($lockfile);
		next unless open (my $lock, "$lockfile");

		<$lock>;
		unlink ($lockfile) if $sessid eq <$lock>;

		close ($lock);
	}
}

sub get_new_session
{
	my ($session, $cgi) = @_;
	my $last_tmpl = (defined $cgi->param('tmpl')) ? $cgi->param('tmpl') : '';

	$session->delete();
	$session->flush();

	if (defined $cgi->cookie(CGI::Session->name())) {
		$cgi->cookie(CGI::Session->name()) =~ /^([a-f0-9]*)$/;	# hex untaint
		my $old_bocdata = File::Spec->tmpdir() . '/' . sprintf("${CGI::Session::Driver::file::FileName}_bocdata", $1);
		unlink $old_bocdata if -r $old_bocdata;
		clear_old_session_locks($1);
	}

	my %userdetails;
	if ($last_tmpl eq 'login_nopw' and exists $config{Passwordless}) {
		emit(load_template('login.html')) if (login_nopw($cgi, \%userdetails) eq 'No PW login on account with password set?');
	} elsif ($last_tmpl eq 'login') {
		login($cgi, \%userdetails);
	} else {
		emit((exists $config{Passwordless}) ? gen_login_nopw : load_template('login.html'));
	}

	$session = CGI::Session->new($cgi) or die CGI::Session->errstr;
	print $session->header();
	$session->param('User', $userdetails{User});
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

sub gen_edit_simp_trans
{
	my $tmpl = load_template('templates/edit_simp_trans.html', $_[0]);

	my %vaccts = query_all_htsv_in_path("$config{Root}/accounts", 'Name');
	my %rvaccts = reverse (%vaccts);
	my @sorted_vaccts = map ($rvaccts{$_}, sort keys %rvaccts);

	my %cfg = read_htsv("$config{Root}/config_simp_trans", 1);
	my $num_rows = ($#{$cfg{Description}} >= 0) ? scalar @{$cfg{Description}} + min(5, 30 - scalar @{$cfg{Description}}) : 10;
	my @rows;
	foreach my $row (0 .. ($num_rows - 1)) {
		my @rowoptions = ({ O => 'Select account' });
		push (@rowoptions, map ({ O => $vaccts{$_}, V => $_, S => (defined $cfg{DebitAcct}[$row]) ? $cfg{DebitAcct}[$row] eq $_ : undef}, @sorted_vaccts));
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
		my $tmpl = load_template('templates/treasurer_cp.html');
		print $tmpl->output;
		exit;
	}
	if ($cgi->param('tmpl') eq 'tcp') {
		emit(gen_manage_accts(1)) if (defined $cgi->param('view_ppl'));
		emit(gen_manage_accts(0)) if (defined $cgi->param('view_accts'));
		if (defined $cgi->param('edit_inst_cfg')) {
			my $cfg_file = "$config{Root}/config";
			my $etoken = create_UUID_as_string(UUID_V4);
			whinge("Couldn't get edit lock for configuration file", load_template('templates/treasurer_cp.html')) unless try_lock($cfg_file, $etoken, $sessid);
			my %inst_cfg = read_simp_cfg($cfg_file, 1);
			my $tmpl = load_template('templates/edit_inst_cfg.html', $etoken);

			foreach my $param ($tmpl->param()) {
				next if $tmpl->param($param);
				$tmpl->param($param => $inst_cfg{$param});
				$tmpl->param($param => '" data-noop="') if exists $inst_cfg{$param} and not defined $inst_cfg{$param};
			}
			emit($tmpl);
		}
		if (defined $cgi->param('edit_simp_trans')) {
			my $cfg_file = "$config{Root}/config_simp_trans";
			my $etoken = create_UUID_as_string(UUID_V4);
			whinge("Couldn't get edit lock for configuration file", load_template('templates/treasurer_cp.html')) unless try_lock($cfg_file, $etoken, $sessid);
			emit(gen_edit_simp_trans($etoken));
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

			whinge('Disallowed characters in short name', gen_add_edit_acc($edit_acct, $person, $etoken)) unless defined $new_acct;
			whinge('Short name too short', gen_add_edit_acc($edit_acct, $person, $etoken)) if length $new_acct < 3;
			whinge('Short name too long', gen_add_edit_acc($edit_acct, $person, $etoken)) if length $new_acct > 10;
			whinge('Short name is already taken', gen_add_edit_acc($edit_acct, $person, $etoken)) if ((-e "$root/accounts/$new_acct" or -e "$root/users/$new_acct") and (not defined $edit_acct or $edit_acct ne $new_acct));
			whinge('Full name too short', gen_add_edit_acc($edit_acct, $person, $etoken)) unless defined $fullname;
			whinge('Full name too long', gen_add_edit_acc($edit_acct, $person, $etoken)) if length $fullname > 100;
			if ($person) {
				whinge('Not an email address', gen_add_edit_acc($edit_acct, $person, $etoken)) unless defined $email;
				whinge('No real-world contact details given', gen_add_edit_acc($edit_acct, $person, $etoken)) unless defined $address;
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

			if ($edit_acct) {
				whinge('Invalid edit token (double submission?)', gen_manage_accts($person)) unless try_unlock("$acct_path/$edit_acct", $etoken);
			} else {
				whinge('Invalid add token (double submission?)', gen_manage_accts($person)) unless redeem_add_token($sessid, $person ? 'add_acct' : 'add_vacct', $etoken);
			}
			write_simp_cfg("$acct_path/$new_acct", %userdetails);
			# support renaming...
			if ($edit_acct and $edit_acct ne $new_acct) {
				# FIXME: really needs a monster lock across even starting to edit TGs when this is done
				my @tgs = glob("$config{Root}/transaction_groups/*");
				foreach my $tg (@tgs) {
					$tg = untaint($tg);
					my %tgdetails = read_tg($tg);

					@{$tgdetails{Creditor}} = map (($_ eq $edit_acct) ? $new_acct : $_, @{$tgdetails{Creditor}});
					@{$tgdetails{Headings}} = map (($_ eq $edit_acct) ? $new_acct : $_, @{$tgdetails{Headings}});
					$tgdetails{$new_acct} = delete $tgdetails{$edit_acct} if exists $tgdetails{$edit_acct};

					write_tg($tg, %tgdetails);
				}

				unlink("$acct_path/$edit_acct") or die;
			}
		} else {
			$edit_acct ? try_unlock("$acct_path/$edit_acct", $etoken) : redeem_add_token($sessid, $person ? 'add_acct' : 'add_vacct', $etoken);
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
				my $etoken = create_UUID_as_string(UUID_V4);
				if ($acct) {
					whinge("Couldn't get edit lock for account \"$acct\"", gen_manage_accts($person)) unless try_lock($acct_file, $etoken, $sessid);
					unless (-r $acct_file) {
						try_unlock($acct_file, $etoken);
						whinge("Couldn't edit account \"$acct\", file disappeared", gen_manage_accts($person));
					}
				} else {
					$etoken = get_add_token($sessid, $person ? 'add_acct' : 'add_vacct');
				}
				emit(gen_add_edit_acc($acct, $person, $etoken));
			} else {
				unlink($acct_file) or die;
				emit_with_status("Deleted account \"$acct\"", gen_manage_accts($person));
			}
		}
	}
	if ($cgi->param('tmpl') eq 'edit_inst_cfg') {
		my $cfg_file = "$config{Root}/config";
		my $tmpl = load_template('templates/treasurer_cp.html');

		if (defined $cgi->param('save')) {
			my %inst_cfg;

			foreach my $param ($cgi->param()) {
				next if ($param eq 'tmpl' or $param eq 'etoken' or $param eq 'save');
				$inst_cfg{$param} = clean_text($cgi->param($param));
			}

			whinge('Invalid edit token (double submission?)', $tmpl) unless try_unlock($cfg_file, $etoken);
			write_simp_cfg($cfg_file, %inst_cfg);
			update_global_config(%inst_cfg);
			$tmpl = load_template('templates/treasurer_cp.html');	# reload (possibly modified) template
		} else {
			try_unlock($cfg_file, $etoken);
		}

		emit_with_status((defined $cgi->param('save')) ? "Saved edits to config" : "Edit config cancelled", $tmpl);
	}
	if ($cgi->param('tmpl') eq 'edit_simp_trans') {
		my $cfg_file = "$config{Root}/config_simp_trans";

		if (defined $cgi->param('save')) {
			my %cfg = ( Headings => [ 'DebitAcct', 'Description' ] );

			my $max_rows = -1;
			$max_rows++ while ($max_rows < 100 and defined $cgi->param("DebitAcct_" . ($max_rows + 1)));
			whinge('No transactions?', gen_edit_simp_trans($etoken)) unless $max_rows >= 0;

			my %vaccts = query_all_htsv_in_path("$config{Root}/accounts", 'Name');

			@{$cfg{Description}} = ();
			@{$cfg{DebitAcct}} = ();
			foreach my $row (0 .. $max_rows) {
				my $desc = clean_text($cgi->param("Description_$row"));
				my $acct = clean_username($cgi->param("DebitAcct_$row"));
				next unless $desc or $acct;
				whinge('Missing account', gen_edit_simp_trans($etoken)) unless $acct;
				whinge('Missing description', gen_edit_simp_trans($etoken)) unless $desc;
				whinge("Non-existent account \"$acct\"", gen_edit_simp_trans($etoken)) unless exists $vaccts{$acct};
				push (@{$cfg{Description}}, $desc);
				push (@{$cfg{DebitAcct}}, $acct);
			}

			whinge('Invalid edit token (double submission?)', load_template('templates/treasurer_cp.html')) unless try_unlock($cfg_file, $etoken);
			write_htsv($cfg_file, \%cfg, 11);
		} else {
			try_unlock($cfg_file, $etoken);
		}

		emit_with_status((defined $cgi->param('save')) ? "Saved edits to config" : "Edit config cancelled", load_template('templates/treasurer_cp.html'));
	}
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

sub despatch_user
{
	my $session = $_[0];
	my $sessid = $session->id();
	my $cgi = $session->query();
	my $tmpl;

	return if (defined $cgi->param('logout'));

	if ($cgi->param('tmpl') eq 'login_nopw') {
		$tmpl = load_template('templates/user_cp.html');
		print $tmpl->output;
		exit;
	}
	if ($cgi->param('tmpl') eq 'ucp') {
		if (defined $cgi->param('manage_tgs')) {
			emit(gen_manage_tgs);
		}
	}
	if ($cgi->param('tmpl') eq 'manage_tgs') {
		if (defined $cgi->param('view') or defined $cgi->param('add')) {
			my $view = $cgi->param('view');
			my $tg;

			if ($view) {
				$tg = "$config{Root}/transaction_groups/" . $view;
				emit(gen_manage_tgs) unless (-r $tg);
			}

			$tmpl = gen_tg($tg, 0, $session, $view ? undef : get_add_token($sessid, 'add_tg'));
		} elsif (defined $cgi->param('to_cp')) {
			$tmpl = load_template('templates/user_cp.html');
		}
		emit($tmpl);
	}
	if ($cgi->param('tmpl') eq 'edit_tg') {
		my $tgfile = (defined $cgi->param('tg_id') and clean_tgid($cgi->param('tg_id'))) ? "$config{Root}/transaction_groups/" . clean_tgid($cgi->param('tg_id')) : undef;
		my $etoken = $cgi->param('etoken');

		if ($etoken and not defined $cgi->param('save')) {
			$cgi->param('tg_id') ? try_unlock($tgfile, $etoken) : redeem_add_token($sessid, 'add_tg', $etoken);
		}
		if (defined $cgi->param('save') or defined $cgi->param('cancel')) {
			my %tg;

			if (defined $cgi->param('save')) {
				$tg{Name} = clean_text($cgi->param('tg_name'));
				whinge('No transaction group name supplied', gen_tg($tgfile, 1, $session, $etoken)) unless defined $tg{Name};
				my $date = clean_text($cgi->param('tg_date'));
				my ($pd_secs, $pd_error) = parsedate($date, (FUZZY => 1, UK => 1, DATE_REQUIRED => 1, NO_RELATIVE => 1));
				whinge('Unparsable date', gen_tg($tgfile, 1, $session, $etoken)) if $pd_error;
				$tg{Date} = join('.', ((localtime($pd_secs))[3], (localtime($pd_secs))[4] + 1, (localtime($pd_secs))[5] + 1900));

				my $max_rows = -1;
				$max_rows++ while ($max_rows < 100 and defined clean_username($cgi->param("Creditor_" . ($max_rows + 1))));
				whinge('No transactions?', gen_tg($tgfile, 1, $session, $etoken)) unless $max_rows >= 0;

				my %acct_names = get_acct_name_map;
				my @accts = map { s/_0$//; $_ } grep ((/^(.*)_0$/ and $1 ne 'Creditor' and $1 ne 'Amount' and $1 ne 'Description'), $cgi->param);
				foreach my $acct (@accts) {
					whinge("Non-existent account \"$acct\"", gen_tg($tgfile, 1, $session, $etoken)) unless exists $acct_names{$acct};
				}

				foreach my $row (0 .. $max_rows) {
					my $cred = clean_username($cgi->param("Creditor_$row"));
					my $amnt = clean_decimal($cgi->param("Amount_$row"));
					my $desc = clean_text($cgi->param("Description_$row"));
					whinge("Non-existent account \"$cred\"", gen_tg($tgfile, 1, $session, $etoken)) unless exists $acct_names{$cred};
					whinge('Non-numerics in amount', gen_tg($tgfile, 1, $session, $etoken)) unless defined $amnt;
					my $set = $amnt == 0 ? 0 : 10000;
					my @rowshares;
					foreach my $acct (@accts) {
						push(@rowshares, clean_decimal($cgi->param("${acct}_$row")));
						whinge('Non-numerics in debt share', gen_tg($tgfile, 1, $session, $etoken)) unless defined $rowshares[$#rowshares];
						$set++ unless $rowshares[$#rowshares] == 0;
					}

					if ($set > 10000) {
						push (@{$tg{Creditor}}, $cred);
						push (@{$tg{Amount}}, $amnt);
						push (@{$tg{Description}}, $desc);
						push (@{$tg{$accts[$_]}}, $rowshares[$_]) foreach (0 .. $#accts);
					} elsif ($set > 0 or $cred ne $session->param('User')) {
						whinge('Insufficient values set in row', gen_tg($tgfile, 1, $session, $etoken));
					}
				}

				my %all_ppl = query_all_htsv_in_path("$config{Root}/users", 'Name');
				my %all_vaccts = query_all_htsv_in_path("$config{Root}/accounts", 'Name');
				my (%ppl, %vaccts);
				((exists $all_ppl{$_}) ? $ppl{$all_ppl{$_}} : $vaccts{$all_vaccts{$_}}) = $_ foreach (@accts);
				@{$tg{Headings}} = sort_accts(%ppl, %vaccts);

				if ($cgi->param('tg_id')) {
					whinge('Invalid edit token (double submission?)', gen_tg($tgfile, 0, $session, undef)) unless try_unlock($tgfile, $etoken);
				} else {
					my $id;
					my $tg_path = "$config{Root}/transaction_groups";
					(mkdir "$tg_path" or die) unless (-d $tg_path);
					do {
						$id = create_UUID_as_string(UUID_V4);
					} while (-e "$tg_path/$id");
					$tgfile = "$tg_path/$id";
					whinge('Invalid add token (double submission?)', gen_manage_tgs) unless redeem_add_token($sessid, 'add_tg', $etoken);
				}
				write_tg($tgfile, %tg);
			}

			$tgfile =~ /.*\/([^\/]{7})[^\/]*$/;
			if (defined $cgi->param('tg_id')) {
				emit_with_status((defined $cgi->param('save')) ? "Saved edits to \"$tg{Name}\" ($1) transaction group" : "Edit cancelled", gen_tg($tgfile, 0, $session, undef));
			} else {
				emit_with_status((defined $cgi->param('save')) ? "Added transaction group \"$tg{Name}\" ($1)" : "Add transaction group cancelled", gen_manage_tgs);
			}
		} elsif (defined $cgi->param('edit')) {
			$etoken = create_UUID_as_string(UUID_V4);
			whinge("Couldn't get edit lock for transaction group \"" . $cgi->param('tg_id') . "\"", gen_manage_tgs) unless try_lock($tgfile, $etoken, $sessid);
			unless (-r $tgfile) {
				try_unlock($tgfile, $etoken);
				whinge("Couldn't edit transaction group \"" . $cgi->param('tg_id') . "\", file disappeared", gen_manage_tgs);
			}
			$tmpl = gen_tg($tgfile, 1, $session, $etoken);
		} elsif (defined $cgi->param('manage_tgs')) {
			$tmpl = gen_manage_tgs;
		}
		emit($tmpl);
	}
}

my $cgi = CGI->new;

%config = read_simp_cfg('boc_config');

die 'Can\'t find value for "Root" key in ./boc_config' unless defined $config{Root};
die 'Can\'t find value for "TemplateDir" key in ./boc_config' unless defined $config{TemplateDir};
die "The BoC root directory (set as $config{Root} in ./boc_config) must exist and be readable and writable by the webserver --" unless (-r $config{Root} && -w $config{Root});
$ENV{HTML_TEMPLATE_ROOT} = $config{TemplateDir};
update_global_config(read_simp_cfg("$config{Root}/config", 1));

create_datastore($cgi, "$config{Root} does not appear to be a BoC data store") unless (-d "$config{Root}/users");
create_datastore($cgi, 'No useable administrator account') unless validate_admins;

my $session = CGI::Session->load($cgi) or die CGI::Session->errstr;
$session = get_new_session($session, $cgi) if ($session->is_empty or (not defined $cgi->param('tmpl')) or $cgi->param('tmpl') =~ m/^login(_nopw)?$/);

$session->param('IsAdmin') ? despatch_admin($session) : despatch_user($session);

# the despatchers fall through if the requested action is unknown: make them log in again!
get_new_session($session, $cgi);
