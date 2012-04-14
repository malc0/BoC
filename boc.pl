#!/usr/bin/perl -T

#FIXME probably want some sequence number to prevent back button errors

use 5.012;
use autodie;
use warnings;
use CGI qw(param);
use CGI::Carp qw(fatalsToBrowser);
use CGI::Session '-ip-match';
use Crypt::Cracklib;
use Crypt::PasswdMD5;
use HTML::Entities;
use HTML::Template;
use UUID::Tiny;

use lib '.';
use SimpCfg;
use TG;

our %config;

sub set_status
{
	$_[0]->param(STATUS => "<p><b>Status: $_[1]</b></p>");
}

sub clean_username
{
	$_[0] =~ /^([a-z0-9\-+_]*)$/;
	return $1;
}

sub clean_fullname
{
	$_[0] =~ /^([\w.\-+ ]*)$/;
	return $1;
}

sub clean_email
{
	$_[0] =~ /^\s*(.+\@.+)\s*$/;
	return $1;
}

sub clean_text
{
	my $escaped_text = encode_entities($_[0], '^A-Za-z0-9\$%^()\-_=+{}\[\];:@,.?\\');	# hash not included to avoid getting treated as comment in file!
	$escaped_text =~ /^(.*)$/;
	return $1;
}

sub load_template
{
	my $tmpl = HTML::Template->new(filename => "$_[0]", global_vars => 1) or die;
	$tmpl->param(SN => $config{ShortName}) if $tmpl->query(name => 'SN');
	$tmpl->param(LN => $config{LongName}) if $tmpl->query(name => 'LN');
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
	$tmpl->param(STATUS => "<p><b>$whinge</b></p>");
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
		write_simp_cfg("$user_path$user", %userdetails);
	} else {
		emit(gen_cds_p($reason));
	}
}

sub find_admins
{
	my @users = glob("$config{Root}/users/*");
	my @admins;

	foreach my $user (@users) {
		my %userdetails = read_simp_cfg($user);
		push(@admins, $user) if (exists $userdetails{IsAdmin});
	}

	die 'Too many administrators defined (only one permitted)!' if (scalar @admins > 1);

	return @admins;
}

sub login
{
	my ($cgi, $userdetout) = @_;
	my $user = clean_username($cgi->param('user'));
	my $pass = $cgi->param('pass');

	whinge('Login failed!', load_template('login.html')) unless (-r "$config{Root}/users/$user");
	my %userdetails = read_simp_cfg("$config{Root}/users/$user");
	whinge('Login on account with no password set?', load_template('login.html')) unless defined $userdetails{Password};

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

sub get_new_session
{
	my ($session, $cgi) = @_;
	my $last_tmpl = (defined $cgi->param('tmpl')) ? $cgi->param('tmpl') : '';

	$session->delete();
	$session->flush();

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

sub gen_view_accs
{
	my $people = $_[0];
	my $tmpl = load_template($people ? 'view_people.html' : 'view_vaccounts.html');
	my @accounts = $people ? glob("$config{Root}/users/*") : glob("$config{Root}/accounts/*");
	my @acctlist;

	foreach my $acct (@accounts) {
		my %acctdetails = read_simp_cfg($acct);
		my %outputdetails;
		$acct =~ /.*\/(.*)/;
		if ($people) {
			%outputdetails = (
				ACC => $1,
				NAME => $acctdetails{Name},
				EMAIL => $acctdetails{email},
			);
		} else {
			%outputdetails = (
				ACC => $1,
				NAME => $acctdetails{Name},
			);
		}
		push(@acctlist, \%outputdetails);
	}
	$tmpl->param(ACCS => \@acctlist);

	return $tmpl;
}

sub gen_add_edit_acc
{
	my ($edit_acct, $person, $session) = @_;
	my $tmpl;

	unless ($edit_acct) {
		$tmpl = load_template($person ? 'new_account.html' : 'new_vaccount.html');
	} else {
		$tmpl = load_template($person ? 'edit_account.html' : 'edit_vaccount.html');

		$session->param('EditingAcct', $person ? "$config{Root}/users/$edit_acct" : "$config{Root}/accounts/$edit_acct");
		$session->flush();
		my %acctdetails = read_simp_cfg($session->param('EditingAcct'));
		$tmpl->param(ACC => $edit_acct);
		$tmpl->param(NAME => $acctdetails{Name});
		$tmpl->param(EMAIL => $acctdetails{email}) if $person;
		$tmpl->param(ADDRESS => $acctdetails{Address}) if $person;
	}

	return $tmpl;
}

sub despatch_admin
{
	my $session = $_[0];
	my $cgi = $session->query();

	return if (defined $cgi->param('logout'));

	if ($cgi->param('tmpl') eq 'login') {
		my $tmpl = HTML::Template->new(filename => 'templates/treasurer_cp.html') or die;
		print $tmpl->output;
		exit;
	}
	if ($cgi->param('tmpl') eq 'tcp') {
		emit(gen_view_accs(1)) if (defined $cgi->param('view_ppl'));
		emit(gen_view_accs(0)) if (defined $cgi->param('view_accs'));
	}
	if ($cgi->param('tmpl') eq 'add_acc' or $cgi->param('tmpl') eq 'edit_acc' or $cgi->param('tmpl') eq 'add_vacc' or $cgi->param('tmpl') eq 'edit_vacc') {
		my $edit_acct_file = $session->param('EditingAcct');
		$edit_acct_file =~ /\/([^\/]+)$/;
		my $edit_acct = $1;
		my $new_acct = clean_username($cgi->param('account'));
		my $person = ($cgi->param('tmpl') eq 'add_acc' or ((defined $edit_acct_file) and $edit_acct_file =~ m/\/users\/[^\/]+$/));

		if (defined $cgi->param('save')) {
			my $fullname = clean_fullname($cgi->param('fullname'));
			my $email = $person ? clean_email($cgi->param('email')) : undef;
			my $address = $person ? clean_text($cgi->param('address')) : undef;

			whinge('Disallowed characters in short name', gen_add_edit_acc($edit_acct, $person, $session)) unless defined $new_acct;
			whinge('Short name too short', gen_add_edit_acc($edit_acct, $person, $session)) if length $new_acct < 3;
			whinge('Short name too long', gen_add_edit_acc($edit_acct, $person, $session)) if length $new_acct > 10;
			whinge('Disallowed characters in full name', gen_add_edit_acc($edit_acct, $person, $session)) unless defined $fullname;
			whinge('Full name too short', gen_add_edit_acc($edit_acct, $person, $session)) if length $fullname < 1;
			whinge('Full name too long', gen_add_edit_acc($edit_acct, $person, $session)) if length $fullname > 100;
			if ($person) {
				whinge('Not an email address', gen_add_edit_acc($edit_acct, $person, $session)) unless defined $email;
				whinge('No real-world contact details given', gen_add_edit_acc($edit_acct, $person, $session)) unless defined $address;
			}

			my $root = $config{Root};
			my %userdetails;
			%userdetails = read_simp_cfg($edit_acct_file) if ($edit_acct_file);
			$userdetails{Name} = $fullname;
			if ($person) {
				$userdetails{email} = $email;
				$userdetails{Address} = $address;
			} else {
				(mkdir "$root/accounts" or die) unless (-d "$root/accounts");
			}
			write_simp_cfg(($person ? "$root/users/" : "$root/accounts/") . $new_acct, %userdetails);
			# support renaming...
			(unlink($edit_acct_file) or die) if ($edit_acct and $edit_acct ne $new_acct);
		}

		if ($edit_acct) {
			$session->clear('EditingAcct');
			$session->flush();
			emit_with_status((defined $cgi->param('save')) ? "Saved edits to account \"$new_acct\"" : "Edit account cancelled", gen_view_accs($person));
		} else {
			emit_with_status((defined $cgi->param('save')) ? "Added account \"$new_acct\"" : "Add account cancelled", gen_view_accs($person));
		}
	}
	if ($cgi->param('tmpl') eq 'view_ppl' or $cgi->param('tmpl') eq 'view_vaccs') {
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

			unless ($delete) {
				emit(gen_add_edit_acc($acct, $person, $session));
			} else {
				unlink($person ? "$config{Root}/users/$acct" : "$config{Root}/accounts/$acct") or die;
				emit_with_status("Deleted account \"$acct\"", gen_view_accs($person));
			}
		}
	}
}

sub query_all_accts_in_path
{
	my ($path, $key) = @_;

	my @accts = glob("$path/*");
	my %response;

	foreach my $acct (@accts) {
		my %acctdetails = read_simp_cfg($acct);
		$acct =~ /.*\/(.*)/;
		$response{$1} = $acctdetails{$key};
	}

	return %response;
}

sub get_acct_name_map
{
	my %ppl = query_all_accts_in_path("$config{Root}/users", 'Name');
	my %vaccts = query_all_accts_in_path("$config{Root}/accounts", 'Name');
	return (%ppl, %vaccts);
}

sub gen_view_tgs
{
	my $tmpl = load_template('manage_transactions.html');

	my %acct_names = get_acct_name_map;
	my @tgs = glob("$config{Root}/transaction_groups/*");
	my @tglist;

	foreach my $tg (@tgs) {
		my %tgdetails = read_tg($tg);

		my %summary;
		my $sum_str = "";
		foreach my $i (0 .. $#{$tgdetails{Creditor}}) {
			my $acct = $tgdetails{Creditor}[$i];
			next if exists $summary{$acct};
			$summary{$acct} = 0;
			foreach my $j ($i .. $#{$tgdetails{Creditor}}) {
				next unless $tgdetails{Creditor}[$j] eq $acct;
				$summary{$acct} += $tgdetails{Amount}[$j];
			}
			$sum_str .= "$acct_names{$acct} " . (($summary{$acct} < 0) ? '' : '+') . $summary{$acct} . ", ";
		}

		$tg =~ /.*\/(.*)/;
		my %outputdetails = (
				ACC => $1,
				NAME => $tgdetails{Name},
				DATE => $tgdetails{Date},
				SUMMARY => substr($sum_str, 0, -2),
		);
		push(@tglist, \%outputdetails);
	}
	$tmpl->param(TGS => \@tglist);

	return $tmpl;
}

sub merge_tg(\%\%\%)
{
	my ($file_tg, $ppl, $vaccts) = @_;

	my @sort_ppl = sort(keys $ppl);
	my @sort_vaccts = sort(keys $vaccts);
	my @sorted = ( 'Creditor', 'Amount' );
	foreach my $key (@sort_ppl) {
		push (@sorted, $ppl->{$key});
	}
	foreach my $key (@sort_vaccts) {
		push (@sorted, $vaccts->{$key});
	}
	push (@sorted, 'Description');

	foreach my $acct (@sorted) {
		my $lower = exists $file_tg->{$acct} ? scalar(@{$file_tg->{$acct}}) : 0;
		push (@{$file_tg->{$acct}}, ($acct eq 'Description') ? '' : 0) foreach ($lower .. $#{$file_tg->{Creditor}});
	}
	@{$file_tg->{Headings}} = @sorted;

	return %$file_tg;
}

sub gen_tg
{
	my ($tg_file, $edit_mode, $session) = @_;
	my %tgdetails;

	if ($tg_file) {
		%tgdetails = read_tg($tg_file);
		if ($edit_mode) {
			push(@{$tgdetails{Creditor}}, $session->param('User')) foreach (0 .. 4);
		}
	} else {
		push(@{$tgdetails{Creditor}}, $session->param('User')) foreach (0 .. 9);
	}

	my $tmpl = load_template('edit_tg.html');

	my %ppl = query_all_accts_in_path("$config{Root}/users", 'Name');
	my %vaccts = query_all_accts_in_path("$config{Root}/accounts", 'Name');
	my %acct_names = (%ppl, %vaccts);
	my %rppl = reverse(%ppl);
	my %rvaccts = reverse(%vaccts);

	%tgdetails = merge_tg(%tgdetails, %rppl, %rvaccts);

	$tg_file =~ /\/([^\/]+)$/;
	$tmpl->param(TG_ID => $1) if (!$edit_mode and $tg_file);
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
		my %row = ( R => \@rowcontents, CREDS => \@rowoptions, CRNAME => "Creditor_$row" );
		push (@rows, \%row);
	}
	$tmpl->param(ROWS => \@rows);

	return $tmpl;
}

sub despatch_user
{
	my $session = $_[0];
	my $cgi = $session->query();
	my $tmpl;

	return if (defined $cgi->param('logout'));

	if ($cgi->param('tmpl') eq 'login_nopw') {
		$tmpl = gen_view_tgs;
		print $tmpl->output;
		exit;
	}
	if ($cgi->param('tmpl') eq 'view_tgs') {
		if (defined $cgi->param('view') or defined $cgi->param('add')) {
			my $view = $cgi->param('view');
			my $tg;

			if ($view) {
				$tg = "$config{Root}/transaction_groups/" . $view;
				emit(gen_view_tgs) unless (-r $tg);
			}

			$tmpl = gen_tg($tg, 0, $session);
		}
		emit($tmpl);
	}
	if ($cgi->param('tmpl') eq 'edit_tg') {
		if (defined $cgi->param('save') or defined $cgi->param('cancel')) {
			my %tg;

			if (defined $cgi->param('save')) {
				$tg{Name} = clean_text($cgi->param('tg_name'));
				# FIXME want a real date helper
				$tg{Date} = clean_text($cgi->param('tg_date'));

				whinge('No transaction group name supplied', gen_tg($session->param('EditingTG'), 1, $session)) unless defined $tg{Name};
				whinge('No transaction group date supplied', gen_tg($session->param('EditingTG'), 1, $session)) unless defined $tg{Date};

				# FIXME store data!

				if (defined $session->param('EditingTG')) {
					write_tg($session->param('EditingTG'), %tg);
				} else {
					my $id;
					my $tg_path = "$config{Root}/transaction_groups";
					(mkdir "$tg_path" or die) unless (-d $tg_path);
					do {
						$id = create_UUID_as_string(UUID_V4);
					} while (-e "$tg_path/$id");
					write_tg("$tg_path/$id", %tg);
				}
			}

			if (defined $session->param('EditingTG')) {
				$tmpl = gen_tg($session->param('EditingTG'), 0, $session);
				$session->clear('EditingTG');
				$session->flush();
				emit_with_status((defined $cgi->param('save')) ? "Saved edits to \"$tg{Name}\" transaction group" : "Edit cancelled", $tmpl);
			} else {
				emit_with_status((defined $cgi->param('save')) ? "Added transaction group \"$tg{Name}\"" : "Add transaction group cancelled", gen_view_tgs);
			}
		} elsif (defined $cgi->param('edit')) {
			my $tg = "$config{Root}/transaction_groups/" . $cgi->param('tg_id');
			emit(gen_view_tgs) unless (-r $tg);
			$tmpl = gen_tg($tg, 1, $session);
			$session->param('EditingTG', "$config{Root}/transaction_groups/" . $cgi->param('tg_id'));
			$session->flush();
		} elsif (defined $cgi->param('view_tgs')) {
			$tmpl = gen_view_tgs;
		}
		emit($tmpl);
	}
}

my $cgi = CGI->new;

%config = read_simp_cfg('boc_config');

die 'Can\'t find value for "Root" key in ./boc_config' unless defined $config{Root};
die 'Can\'t find value for "TemplateDir" key in ./boc_config' unless defined $config{TemplateDir};
$ENV{HTML_TEMPLATE_ROOT} = $config{TemplateDir};
die 'Can\'t find value for "ShortName" key in ./boc_config' unless defined $config{ShortName};
die 'Can\'t find value for "LongName" key in ./boc_config' unless defined $config{LongName};

die "The BoC root directory (set as $config{Root} in ./boc_config) must exist and be readable and writable by the webserver --" unless (-r $config{Root} && -w $config{Root});

create_datastore($cgi, "$config{Root} does not appear to be a BoC data store") unless (-d "$config{Root}/users");

my @admins = find_admins;

if (scalar @admins == 0) {
	create_datastore($cgi, 'No administrator account defined?');
	@admins = find_admins;
}

my %userdetails = read_simp_cfg($admins[0]);
die 'Admininstrator account with no password set?' unless defined $userdetails{Password};

my $session = CGI::Session->load($cgi) or die CGI::Session->errstr;

$session = get_new_session($session, $cgi) if ($session->is_empty or (not defined $cgi->param('tmpl')) or $cgi->param('tmpl') =~ m/^login(_nopw)?$/);

$session->clear('EditingAcct') unless ($cgi->param('tmpl') =~ m/^edit_v?acc$/);
$session->clear('EditingTG') unless ($cgi->param('tmpl') eq 'edit_tg');
$session->flush();
$session->param('IsAdmin') ? despatch_admin($session) : despatch_user($session);

# the despatchers fall through if the requested action is unknown: make them log in again!
get_new_session($session, $cgi);
