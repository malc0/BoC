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
use HTML::Template;
use UUID::Tiny;

use lib '.';
use SimpCfg;
use TG;

our %config;

sub format_whinge
{
	return ($_[0] eq '') ? '' : "<p><b>$_[0]</b></p>";
}

sub format_status
{
	return ($_[0] eq '') ? '' : "<p><b>Status: $_[0]</b></p>";
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

sub load_template
{
	my $tmpl = HTML::Template->new(filename => "$_[0]", global_vars => 1) or die;
	$tmpl->param(SN => $config{ShortName}) if $tmpl->query(name => 'SN');
	$tmpl->param(LN => $config{LongName}) if $tmpl->query(name => 'LN');
	return $tmpl;
}

sub create_datastore_p
{
	my ($reason, $whinge) = @_;
	my $create_ds_tmpl = load_template('create_ds_p.html');

	$create_ds_tmpl->param(REASON => $reason);
	$create_ds_tmpl->param(ROOT => $config{Root});
	$create_ds_tmpl->param(WHINGE => format_whinge($whinge));

	print "Content-Type: text/html\n\n", $create_ds_tmpl->output;

	exit;
}

sub create_datastore
{
	my ($user, $pass) = @_;
	my $root = $config{Root};

	return 'Disallowed characters in username' unless defined clean_username($user);
	return 'Username too short' if length $user < 3;
	return 'Username too long' if length $user > 10;
	$user = clean_username($user);

	(mkdir "$root/users" or die) unless (-d "$root/users");

	my $cracklib_rv = fascist_check($pass);
#	return "Problem with password: $cracklib_rv" unless ($cracklib_rv eq 'ok');
	my $cryptpass = unix_md5_crypt($pass);
	my %userdetails = (
		Password => $cryptpass,
		IsAdmin => undef,
	);
	write_simp_cfg("$root/users/$user", %userdetails);

	return 'ok';
}

sub cds_handler
{
	my ($cgi, $reason) = @_;
	my $whinge = '';

	if (defined $cgi->param('tmpl') and $cgi->param('tmpl') eq 'create_ds_p') {
		$whinge = create_datastore($cgi->param('user'), $cgi->param('pass'));
	}
	create_datastore_p($reason, $whinge) unless ($whinge eq 'ok');
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

sub verify_login
{
	my ($cgi, $userdetout) = @_;
	my $user = clean_username($cgi->param('user'));
	my $pass = $cgi->param('pass');

	return 'Login failed!' unless (-r "$config{Root}/users/$user");
	my %userdetails = read_simp_cfg("$config{Root}/users/$user");
	return 'Login on account with no password set?' unless defined $userdetails{Password};

	my ($empty, $id, $salt, $encrypted) = split(/\$/, $userdetails{Password}, 4);

	my $cryptpass = unix_md5_crypt($pass, $salt);

	return 'Login failed!' unless ($cryptpass eq $userdetails{Password});

	$userdetails{User} = $user;
	%{$userdetout} = %userdetails;
	return 'ok';
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

sub verify_login_nopw
{
	my ($cgi, $userdetout) = @_;
	my $user = clean_username($cgi->param('user'));

	return 'Login failed!' unless (-r "$config{Root}/users/$user");
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
	my $whinge = '';
	my $tmpl;
	if ($last_tmpl eq 'login_nopw' and exists $config{Passwordless}) {
		$whinge = verify_login_nopw($cgi, \%userdetails);
		if ($whinge eq 'No PW login on account with password set?') {
			$tmpl = load_template('login.html');
			$whinge = '';
		} elsif ($whinge ne 'ok') {
			$tmpl = gen_login_nopw;
		}
	} elsif ($last_tmpl eq 'login') {
		$whinge = verify_login($cgi, \%userdetails);
		$tmpl = load_template('login.html') unless ($whinge eq 'ok');
	} else {
		$tmpl = (exists $config{Passwordless}) ? gen_login_nopw : load_template('login.html');
	}

	if (defined $tmpl) {
		$tmpl->param(WHINGE => format_whinge($whinge));
		print "Content-Type: text/html\n\n", $tmpl->output;
		exit;
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
	my ($edit, $person, $acct, $session) = @_;
	my $tmpl;

	unless ($edit) {
		$tmpl = load_template($person ? 'new_account.html' : 'new_vaccount.html');
	} else {
		$tmpl = load_template($person ? 'edit_account.html' : 'edit_vaccount.html') or die;

		$session->param('EditingAcct', $person ? "$config{Root}/users/$acct" : "$config{Root}/accounts/$acct");
		$session->flush();
		my %acctdetails = read_simp_cfg($session->param('EditingAcct'));
		$tmpl->param(ACC => $acct);
		$tmpl->param(NAME => $acctdetails{Name});
		$tmpl->param(EMAIL => $acctdetails{email}) if $person;
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
		my $tmpl;
		if (defined $cgi->param('view_ppl')) {
			$tmpl = gen_view_accs(1);
		}
		if (defined $cgi->param('view_accs')) {
			$tmpl = gen_view_accs(0);
		}
		print "Content-Type: text/html\n\n", $tmpl->output;
		exit;
	}
	if ($cgi->param('tmpl') eq 'add_acc' or $cgi->param('tmpl') eq 'edit_acc' or $cgi->param('tmpl') eq 'add_vacc' or $cgi->param('tmpl') eq 'edit_vacc') {
		my $edit_acct = $session->param('EditingAcct');
		my $user = clean_username($cgi->param('account'));
		my $edit = (defined $edit_acct);
		my $person = ($cgi->param('tmpl') eq 'add_acc' or ($edit and $edit_acct =~ m/\/users\/[^\/]+$/));

		if (defined $cgi->param('save')) {
			my $whinge = '';

			if ($person) {
				$whinge = 'Not an email address' unless defined clean_email($cgi->param('email'));
			}
			$whinge = 'Disallowed characters in full name' unless defined clean_fullname($cgi->param('fullname'));
			$whinge = 'Full name too short' if length $cgi->param('fullname') < 1;
			$whinge = 'Full name too long' if length $cgi->param('fullname') > 100;
			$whinge = 'Disallowed characters in short name' unless defined $user;
			$whinge = 'Short name too short' if length $user < 3;
			$whinge = 'Short name too long' if length $user > 10;
			if ($whinge ne '') {
				my $tmpl = gen_add_edit_acc($edit, $person, $user, $session);
				$tmpl->param(WHINGE => format_whinge($whinge));
				print "Content-Type: text/html\n\n", $tmpl->output;
				exit;
			}

			my $root = $config{Root};
			my %userdetails;
			%userdetails = read_simp_cfg($edit_acct) if ($edit);
			$userdetails{Name} = clean_fullname($cgi->param('fullname'));
			if ($person) {
				$userdetails{email} = clean_email($cgi->param('email'));
				# FIXME: need to deal with, and validate, this field.  Somehow.
				#$userdetails{Address} = $cgi->param('address');
			} else {
				(mkdir "$root/accounts" or die) unless (-d "$root/accounts");
			}
			write_simp_cfg(($person ? "$root/users/" : "$root/accounts/") . $user, %userdetails);
			if ($edit) {
				# support renaming...
				$edit_acct =~ /\/([^\/]+)$/;
				(unlink($edit_acct) or die) unless ($1 eq $user);
			}	
		}
		$session->clear('EditingAcct');
		$session->flush();

		my $tmpl = gen_view_accs($person);
		if ($edit) {
			$tmpl->param(STATUS => format_status((defined $cgi->param('save')) ? "Saved edits to account \"$user\"" : "Edit account cancelled"));
		} else {
			$tmpl->param(STATUS => format_status((defined $cgi->param('save')) ? "Added account \"$user\"" : "Add account cancelled"));
		}
		print "Content-Type: text/html\n\n", $tmpl->output;
		exit;
	}
	if ($cgi->param('tmpl') eq 'view_ppl' or $cgi->param('tmpl') eq 'view_vaccs') {
		my $tmpl;
		if (defined $cgi->param('to_cp')) {
			$tmpl = load_template('treasurer_cp.html');
		} else {
			my $acct;
			my $edit = 1;
			my $person = $cgi->param('tmpl') eq 'view_ppl';

			foreach my $p ($cgi->param) {
				$p =~ /edit_(.*)/;
				$acct = $1;
				last if defined $acct;
				$p =~ /del_(.*)/;
				$acct = $1;
				$edit = 0 if defined $acct;
				last if defined $acct;
			}

			if ($edit) {
				$tmpl = gen_add_edit_acc((defined $cgi->param('edit_acc') or defined $cgi->param('edit_vacc')), $person, $acct, $session);
			} else {
				unlink($person ? "$config{Root}/users/$acct" : "$config{Root}/accounts/$acct") or die;
				$tmpl = gen_view_accs($person);
				$tmpl->param(STATUS => format_status("Deleted account \"$acct\""));
			}
		}
		print "Content-Type: text/html\n\n", $tmpl->output;
		exit;
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

sub gen_view_tgs
{
	my $tmpl = load_template('manage_transactions.html');

	my @tgs = glob("$config{Root}/transaction_groups/*");
	my @tglist;

	foreach my $tg (@tgs) {
		my %tgdetails = read_tg($tg);
		$tg =~ /.*\/(.*)/;
		my %outputdetails = (
				ACC => $1,
				NAME => $tgdetails{Name},
				DATE => $tgdetails{Date},
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

	my @zerocol;
	foreach my $row (0 .. $#{$file_tg->{Creditor}}) {
		push(@zerocol, 0);
	}

	foreach my $acct (@sorted) {
		@{$file_tg->{$acct}} = @zerocol unless exists $file_tg->{$acct};
	}
	@{$file_tg->{Headings}} = @sorted;

	return %$file_tg;
}

sub gen_tg
{
	my ($tgref, $view) = @_;
	my %tgdetails = %$tgref;

	my $tmpl = load_template('edit_tg.html');

	my %ppl = query_all_accts_in_path("$config{Root}/users", 'Name');
	my %vaccts = query_all_accts_in_path("$config{Root}/accounts", 'Name');
	my %acct_names = (%ppl, %vaccts);
	my %rppl = reverse(%ppl);
	my %rvaccts = reverse(%vaccts);

	%tgdetails = merge_tg(%tgdetails, %rppl, %rvaccts);

	$tmpl->param(NAME => $tgdetails{Name});
	$tmpl->param(RO => $view);
	$tmpl->param(DATE => $tgdetails{Date});
	my @headings;
	foreach my $key (@{$tgdetails{Headings}}) {
		my $h = (exists $acct_names{$key}) ? $acct_names{$key} : $key;
		my %heading = ( H => $h );
		push(@headings, \%heading);
	}
	$tmpl->param(HEADINGS => \@headings);

	my @rows;
	foreach my $row (0 .. $#{$tgdetails{Creditor}}) {
		$tmpl->param(CRNAME => "Creditor_$row");
		my $options = "<option>Select creditor</option>";
		foreach my $key (@{$tgdetails{Headings}}) {
			next unless exists $acct_names{$key};
			if ((defined $tgdetails{Creditor}[$row]) and $tgdetails{Creditor}[$row] eq $key) {
				$options .= "<option value=\"$key\" selected=\"selected\">$acct_names{$key}</option>"
			} else {
				$options .= "<option value=\"$key\">$acct_names{$key}</option>"
			}
		}

		my @rowcontents;
		foreach my $key (@{$tgdetails{Headings}}[1 .. $#{$tgdetails{Headings}}]) {
			my %data = ( D => $tgdetails{$key}[$row], N => "${key}_$row" );
			push(@rowcontents, \%data);
		}
		my %row = ( R => \@rowcontents, CROPTIONS => $options );
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
			my %tgdetails;

			if ($view) {
				my $tg = "$config{Root}/transaction_groups/" . $view;

				unless (-r $tg) {
					$tmpl = gen_view_tgs;
					print "Content-Type: text/html\n\n", $tmpl->output;
					exit;
				}

				%tgdetails = read_tg($tg);
			} else {
				push(@{$tgdetails{Creditor}}, undef) foreach (0 .. 9);
			}

			$tmpl = gen_tg(\%tgdetails, $view);
		}
		print "Content-Type: text/html\n\n", $tmpl->output;
		exit;
	}
	if ($cgi->param('tmpl') eq 'edit_tg') {
		if (defined $cgi->param('save')) {
			my %tg;
			# FIXME ha ha

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
		if (defined $cgi->param('save') or defined $cgi->param('cancel')) {
			if (defined $session->param('EditingTG')) {
				$session->clear('EditingTG');
				$session->flush();
#				$tmpl = gen_tg(\$tgdetails, 1);
#				$tmpl->param(STATUS => format_status((defined $cgi->param('save')) ? "Saved edits to \"$user\" transaction group" : "Edit cancelled"));
			} else {
				$tmpl = gen_view_tgs;
#				$tmpl->param(STATUS => format_status((defined $cgi->param('save')) ? "Added transaction group \"$user\"" : "Add transaction group cancelled"));
			}
		} elsif (defined $cgi->param('edit')) {
#			$session->param('EditingTG', $config{Root}/transaction_groups/$UUID);
			$session->flush();
			# need a tgdetails for edit -- FIXME
#			$tmpl = gen_tg(\%tgdetails, undef);
		} elsif (defined $cgi->param('view_tgs')) {
			$tmpl = gen_view_tgs;
		}
		print "Content-Type: text/html\n\n", $tmpl->output;
		exit;
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

cds_handler($cgi, "$config{Root} does not appear to be a BoC data store") unless (-d "$config{Root}/users");

my @admins = find_admins;

if (scalar @admins == 0) {
	cds_handler($cgi, 'No administrator account defined?');
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
