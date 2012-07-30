#!/usr/bin/perl -T

use 5.014;	# get guaranteed correct exception handling
use autodie;
use warnings;

use Fcntl qw(O_RDWR O_WRONLY O_EXCL O_CREAT LOCK_EX LOCK_NB SEEK_SET);
use CGI qw(param);
use CGI::Carp qw(fatalsToBrowser);
use File::Find;
use List::Util qw(first min);
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
use CleanData qw(untaint encode_for_file encode_for_html clean_email clean_filename clean_text clean_unit clean_username clean_word clean_words validate_acct validate_acctname validate_date validate_decimal validate_unitname validate_unit);
use HeadedTSV;
use TG;
use Units;

my %config;
my $git;

sub update_global_config
{
	my (%append_cfg) = @_;
	@config{keys %append_cfg} = values %append_cfg;	# merge settings
	$config{LongName} = 'Set LongName in installation config!' unless defined $config{LongName};
	$config{ShortName} = 'Set ShortName in installation config!' unless defined $config{ShortName};
	return;
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

sub try_lock
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
	return unlink "$config{Root}/.DSLOCK.lock";
}

sub try_tg_lock
{
	my ($file, $sessid) = @_;

	return undef unless try_commit_lock($sessid);
	my $rv = try_lock($file, $sessid);
	un_commit_lock;
	return $rv;
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

sub read_htsv_encode
{
	my $content = $_[0];

	foreach my $key (keys %$content) {
		$content->{$key} = encode_for_html($content->{$key}) unless (ref($content->{$key}) or not $content->{$key});
		@{$content->{$key}} = map (encode_for_html($_), @{$content->{$key}}) if ref ($content->{$key});
	}

	return;
}

sub write_htsv_encode
{
	my $content = $_[0];

	foreach my $key (keys %$content) {
		$content->{$key} = encode_for_file($content->{$key}) unless (ref($content->{$key}) or not $content->{$key});
		@{$content->{$key}} = map (encode_for_file($_), @{$content->{$key}}) if ref ($content->{$key});
	}

	return;
}

sub commit
{
	my ($message, $userdata) = @_;
	my $user = ref $userdata ? $userdata->param('User') : $userdata;
	my $name = ref $userdata ? $userdata->param('Name') : $userdata;
	return $git->commit({author => "$name <$user>", message => $message});
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

sub set_status
{
	$_[0]->param(STATUS => encode_for_html("Status: $_[1]"));
	return;
}

sub unroot
{
	return undef unless $_[0] =~ /$config{Root}\/(.*)/;
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
		# no session so not edit_token protected.  FIXME?
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
	my @users = glob("$config{Root}/users/*");

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

	my @users = glob("$config{Root}/users/*");
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
	my @locks = glob("$config{Root}/*/.*.lock");
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
	my $last_tmpl = (defined $cgi->param('tmpl')) ? $cgi->param('tmpl') : '';

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

	$session = CGI::Session->new($cgi) or die CGI::Session->errstr;
	print $session->header();
	$session->param('User', $userdetails{User});
	$session->param('Name', exists $userdetails{Name} ? $userdetails{Name} : $userdetails{User});
	$session->param('IsAdmin', (exists $userdetails{IsAdmin}));
	$session->expire('+10m');
	$session->flush();

	return $session;
}

sub gen_tcp
{
	my $tmpl = load_template('treasurer_cp.html');

	my %vaccts = query_all_htsv_in_path("$config{Root}/accounts", 'Name');
	$tmpl->param(VACCTS => scalar keys %vaccts);

	return $tmpl;
}

sub query_pers_attrs
{
	my %attr_cfg = read_htsv("$config{Root}/config_pers_attrs", 1);
	return map ($attr_cfg{Type}[$_] . $attr_cfg{Attribute}[$_], 0 .. $#{$attr_cfg{Type}});
}

sub gen_manage_accts
{
	my $people = $_[0];
	my $tmpl = load_template('manage_accts.html');
	my @accounts = $people ? glob("$config{Root}/users/*") : glob("$config{Root}/accounts/*");
	my @acctlist;
	my @attrs_list = query_pers_attrs;

	foreach my $acct (@accounts) {
		my %acctdetails = read_simp_cfg($acct);
		my %outputdetails;
		next unless $acct =~ /.*\/(.*)/;
		if ($people) {
			my @attrs = map ({ C => (exists $acctdetails{$_}) }, @attrs_list);
			%outputdetails = (
				ACCT => $1,
				NAME => $acctdetails{Name},
				EMAIL => $acctdetails{email},
				ATTRS => \@attrs,
			);
		} else {
			%outputdetails = (
				ACCT => $1,
				NAME => $acctdetails{Name},
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

sub gen_add_edit_acc
{
	my ($edit_acct, $person, $etoken) = @_;
	my $tmpl = load_template('edit_acct.html', $etoken);
	my %acctdetails;

	if ($edit_acct) {
		$tmpl->param(EACCT => $edit_acct);
		%acctdetails = read_simp_cfg($person ? "$config{Root}/users/$edit_acct" : "$config{Root}/accounts/$edit_acct");
		$tmpl->param(ACCT => $edit_acct);
		$tmpl->param(NAME => $acctdetails{Name});
		$tmpl->param(EMAIL => $acctdetails{email});
		$tmpl->param(ADDRESS => $acctdetails{Address});
		$tmpl->param(IS_NEGATED => 1) if exists $acctdetails{IsNegated};
	}
	my @attr_set = map ({ A => $_, C => (exists $acctdetails{$_}) }, query_pers_attrs);
	$tmpl->param(ATTRS => \@attr_set);
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
	my @sorted_vaccts = sort_AoH(\%vaccts);

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

sub gen_manage_fee_tmpls
{
	my $tmpl = load_template('manage_fee_tmpls.html');

	my %fts = query_all_htsv_in_path("$config{Root}/fee_tmpls", 'Name');
	my @list = map ({ TMPL => $_, NAME => $fts{$_} }, keys %fts);
	$tmpl->param(TMPLS => \@list);

	return $tmpl;
}

sub gen_edit_fee_tmpl
{
	my ($file, $view_mode, $session, $etoken) = @_;

	my %ft;
	my $init_rows = 0;
	my $max_rows = 5;

	if ($file) {
		%ft = read_htsv($file);
		$init_rows = scalar @{$ft{Fee}};
		$max_rows = $init_rows + ($view_mode ? 0 : min(2, 10 - $init_rows));
	}

	my $tmpl = load_template('edit_fee_tmpl.html', $etoken);

	my %units_cfg = read_units_cfg("$config{Root}/config_units");
	my @units = known_units(%units_cfg);

	push (@{$ft{Fee}}, (0) x ($max_rows - scalar @{$ft{Fee}}));
	push (@{$ft{Unit}}, ('') x ($init_rows - scalar @{$ft{Unit}})) if scalar @units > 1;
	push (@{$ft{Unit}}, ($units_cfg{Default}) x ($max_rows - scalar @{$ft{Unit}})) if scalar @units;
	push (@{$ft{Condition}}, ('') x ($max_rows - scalar @{$ft{Condition}}));

	my @allunits = @units;
	foreach my $cur (@{$ft{Unit}}) {
		push (@allunits, $cur) if defined $cur and not grep (/^$cur$/, @allunits);
	}
	my @attrs = map ({ A => $_ }, query_pers_attrs);

	$tmpl->param(FT_ID => $1) if ($file and $file =~ /\/([^\/]+)$/);
	$tmpl->param(RO => $view_mode);
	$tmpl->param(NAME => $ft{Name});
	$tmpl->param(NATTRS => scalar @attrs);
	$tmpl->param(CUROPTS => scalar @allunits > 1);

	my @fees;
	foreach my $row (0 .. $max_rows - 1) {
		my $unk_cur = (not defined $ft{Unit}[$row] or not grep (/^$ft{Unit}[$row]$/, @units));
		my @currencies = map ({ C => $_, S => ((defined $ft{Unit}[$row]) ? ($_ eq $ft{Unit}[$row]) : (not defined $_)) }, $unk_cur ? (@units, $ft{Unit}[$row]) : @units);
		my @fattrs;
		foreach (query_pers_attrs) {
			my $cond = '';
			($cond = $ft{Condition}[$row]) =~ s/\s*//g if defined $ft{Condition}[$row];
			$cond =~ s/&amp;/&/g;
			$cond = '&&' . $cond . '&&';
			my $if = ($cond =~ /&&$_&&/);
			my $unless = ($cond =~ /&&!$_&&/);
			$unless = 0 if $if;
			my $dc = !($if or $unless);
			push (@fattrs, { A => $_, I => $if, U => $unless, D => $dc });
		}
		push (@fees, { F => $ft{Fee}[$row], N => $row, CURS => \@currencies, FATTRS => \@fattrs });
	}

	$tmpl->param(ATTRS => \@attrs, FEES => \@fees);
	$tmpl->param(DEFCUR => (scalar @allunits == 1) ? "$units_cfg{$units_cfg{Default}} ($units_cfg{Default})" : undef);

	return $tmpl;
}

sub gen_edit_pers_attrs
{
	my $tmpl = load_template('edit_pers_attrs.html', $_[0]);

	my @types = ( 'Has', 'Is' );

	my %cfg = read_htsv("$config{Root}/config_pers_attrs", 1);
	foreach my $type (@{$cfg{Type}}) {
		push (@types, $type) unless grep (/^$type$/, @types);
	}
	my $num_rows = ($#{$cfg{Type}} >= 0) ? scalar @{$cfg{Type}} + min(5, 30 - scalar @{$cfg{Type}}) : 10;
	my @rows;
	foreach my $row (0 .. ($num_rows - 1)) {
		my @rowoptions = map ({ T => $_, S => (defined $cfg{Type}[$row]) ? $cfg{Type}[$row] eq $_ : undef }, @types);
		push (@rows, { TYPES => \@rowoptions, A => $cfg{Attribute}[$row], R => $row });
	}
	$tmpl->param(ROWS => \@rows);

	return $tmpl;
}

sub gen_edit_units
{
	my $tmpl = load_template('edit_units.html', $_[0]);

	my %cfg = read_units_cfg("$config{Root}/config_units");
	my @units = known_units(%cfg);
	my $num_rows = (scalar @units > 0) ? (scalar @units) + 3 : 5;
	my @rows = map ({ D => $cfg{$_}, C => $_, A => !!($cfg{Commodities} =~ /(^|;)$_($|;)/), B => ($cfg{Anchor} eq $_), P => ($cfg{Default} eq $_), R => $_ }, @units);
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
	$curs{$_} = 1 foreach (grep (!($cfg{Commodities} =~ /(^|;)$_($|;)/), @units));

	@units = grep (!/^$cfg{Anchor}$/, @units);	# exclude self-referencing rate henceforth

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

sub commit_config_units
{
	my ($whinge, $session, $etoken, $rename, $cfg) = @_;
	my $sessid = $session->id();
	my $cfg_file = "$config{Root}/config_units";

	$whinge->('Unable to get commit lock') unless try_commit_lock($sessid);
	bad_token_whinge(gen_tcp) unless redeem_edit_token($sessid, 'edit_units', $etoken);
	return try_commit_and_unlock(sub {
		my $commit_msg = 'config_units: units/rates modified';

		if (keys %$rename) {
			my @tgs = glob("$config{Root}/transaction_groups/*");
			foreach my $tg (@tgs) {
				$tg = untaint($tg);
				my %tgdetails = read_tg($tg);

				foreach my $old (keys %$rename) {
					s/^$old$/$rename->{$old}/ foreach (@{$tgdetails{Currency}});
				}

				write_tg($tg, %tgdetails);
				$git->add($tg);
			}
			$commit_msg .= ' AND RENAMED';
		}

		write_units_cfg($cfg_file, $cfg);
		add_commit($cfg_file, $commit_msg, $session);
		unlink "$cfg_file.p1" if -e "$cfg_file.p1";
		unlink "$cfg_file.rename" if -e "$cfg_file.rename";
	}, $cfg_file);
}

sub despatch_admin
{
	my $session = $_[0];
	my $sessid = $session->id();
	my $cgi = $session->query();
	my $etoken = $cgi->param('etoken');

	return if (defined $cgi->param('logout'));

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
		if (defined $cgi->param('edit_inst_cfg')) {
			$whinge->() unless try_lock("$config{Root}/config", $sessid);
			emit(gen_edit_inst_cfg(get_edit_token($sessid, 'edit_inst_cfg')));
		}
		if (defined $cgi->param('edit_simp_trans')) {
			$whinge->() unless try_lock("$config{Root}/config_simp_trans", $sessid);
			emit(gen_edit_simp_trans(get_edit_token($sessid, 'edit_simp_trans')));
		}
		emit(gen_manage_fee_tmpls) if (defined $cgi->param('manage_fee_tmpls'));
		if (defined $cgi->param('edit_pers_attrs')) {
			$whinge->() unless try_lock("$config{Root}/config_pers_attrs", $sessid);
			emit(gen_edit_pers_attrs(get_edit_token($sessid, 'edit_pers_attrs')));
		}
		if (defined $cgi->param('edit_units')) {
			$whinge->() unless try_lock("$config{Root}/config_units", $sessid);
			emit(gen_edit_units(get_edit_token($sessid, 'edit_units')));
		}
	}
	if ($cgi->param('tmpl') eq 'edit_acct') {
		my $edit_acct = clean_username($cgi->param('eacct'));
		my $person = defined $cgi->param('email');
		my $whinge = sub { whinge($_[0], gen_add_edit_acc($edit_acct, $person, $etoken)) };
		my $new_acct;
		my $root = $config{Root};
		my $acct_path = $person ? "$root/users" : "$root/accounts";

		if (defined $cgi->param('save')) {
			$new_acct = validate_acctname(scalar $cgi->param('account'), $whinge);
			my $fullname = clean_words($cgi->param('fullname'));
			my $email = clean_email($cgi->param('email'));
			my $address = clean_text($cgi->param('address'));
			my $rename = ($edit_acct and $edit_acct ne $new_acct);

			whinge('Account to be edited not found (resubmission after rename?)', gen_manage_accts($person)) if $edit_acct and not -r ("$acct_path/$edit_acct");
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
				(defined $cgi->param($_)) ? $userdetails{$_} = undef : delete $userdetails{$_} foreach (query_pers_attrs);
			} else {
				(mkdir $acct_path or die) unless (-d $acct_path);
				(defined $cgi->param('is_negated')) ? $userdetails{IsNegated} = undef : delete $userdetails{IsNegated};
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
			emit_with_status((defined $cgi->param('save')) ? "Saved edits to account \"$new_acct\"" : 'Edit account cancelled', gen_manage_accts($person));
		} else {
			emit_with_status((defined $cgi->param('save')) ? "Added account \"$new_acct\"" : 'Add account cancelled', gen_manage_accts($person));
		}
	}
	if ($cgi->param('tmpl') eq 'view_ppl' or $cgi->param('tmpl') eq 'view_vaccts') {
		my $acct;
		my $delete = 0;
		my $person = $cgi->param('tmpl') eq 'view_ppl';
		my $whinge = sub { whinge($_[0], gen_manage_accts($person)) };

		foreach my $p ($cgi->param) {
			if ($p =~ /^edit_(.*)$/) {
				$acct = $1;
				last;
			}
			if ($p =~ /^del_(.*)$/) {
				$acct = $1;
				$delete = 1;
				last;
			}
		}

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
			$whinge->('Unable to get commit lock') unless try_commit_lock($sessid);
			try_commit_and_unlock(sub {
				$git->rm($acct_file);
				commit(unroot($acct_file) . ': deleted', $session);
			});
			emit_with_status("Deleted account \"$acct\"", gen_manage_accts($person));
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
			unlock($cfg_file);
			redeem_edit_token($sessid, 'edit_inst_cfg', $etoken);
		}

		emit_with_status((defined $cgi->param('save')) ? 'Saved edits to installation config' : 'Edit installation config cancelled', gen_tcp);
	}
	if ($cgi->param('tmpl') eq 'edit_simp_trans') {
		my $cfg_file = "$config{Root}/config_simp_trans";

		if (defined $cgi->param('save')) {
			my %cfg;
			my $whinge = sub { whinge($_[0], gen_edit_simp_trans($etoken)) };

			my $max_rows = -1;
			$max_rows++ while ($max_rows < 100 and defined $cgi->param('DebitAcct_' . ($max_rows + 1)));
			$whinge->('No transactions?') unless $max_rows >= 0;

			my %vaccts = query_all_htsv_in_path("$config{Root}/accounts", 'Name');

			foreach my $row (0 .. $max_rows) {
				my $desc = clean_words($cgi->param("Description_$row"));
				my $acct = clean_username($cgi->param("DebitAcct_$row"));
				next unless $desc or $acct;
				$whinge->('Missing account') unless $acct;
				$whinge->('Missing description') unless $desc;
				validate_acct($acct, \%vaccts, $whinge);
				push (@{$cfg{Description}}, $desc);
				push (@{$cfg{DebitAcct}}, $acct);
			}
			@{$cfg{Headings}} = ( 'DebitAcct', 'Description' ) if exists $cfg{DebitAcct};

			$whinge->('Unable to get commit lock') unless try_commit_lock($sessid);
			bad_token_whinge(gen_tcp) unless redeem_edit_token($sessid, 'edit_simp_trans', $etoken);
			try_commit_and_unlock(sub {
				write_htsv($cfg_file, \%cfg, 11);
				add_commit($cfg_file, 'config_simp_trans: simple transaction types modified', $session);
			}, $cfg_file);
		} else {
			unlock($cfg_file);
			redeem_edit_token($sessid, 'edit_simp_trans', $etoken);
		}

		emit_with_status((defined $cgi->param('save')) ? 'Saved edits to transaction config' : 'Edit transaction config cancelled', gen_tcp);
	}
	if ($cgi->param('tmpl') eq 'manage_fee_tmpls') {
		if (defined $cgi->param('view') or defined $cgi->param('add')) {
			my $view = $cgi->param('view');
			my $ft;

			if ($view) {
				$ft = "$config{Root}/fee_tmpls/$view";
				emit_with_status("No such FT \"$view\"", gen_manage_fee_tmpls) unless (-r $ft);
			}

			emit(gen_edit_fee_tmpl($ft, $view, $session, $view ? undef : get_edit_token($sessid, 'add_ft')));
		}
	}
	if ($cgi->param('tmpl') eq 'edit_fee_tmpl') {
		emit(gen_manage_fee_tmpls) if (defined $cgi->param('manage_fee_tmpls'));

		my $edit_id = clean_filename(scalar $cgi->param('ft_id'), "$config{Root}/fee_tmpls");
		my $file = $edit_id ? "$config{Root}/fee_tmpls/$edit_id" : undef;

		emit_with_status("No such fee template \"$edit_id\"", gen_manage_fee_tmpls) if $edit_id and ! -r $file;

		if (defined $cgi->param('edit')) {
			whinge("Couldn't get edit lock for fee template \"$edit_id\"", gen_manage_fee_tmpls) unless try_lock($file, $sessid);
			unless (-r $file) {
				unlock($file);
				whinge("Couldn't edit fee template \"$edit_id\", file disappeared", gen_manage_fee_tmpls);
			}
			emit(gen_edit_fee_tmpl($file, 0, $session, get_edit_token($sessid, "edit_$edit_id")));
		}

		# only left with save and cancel now
		my %ft;

		if (defined $cgi->param('save')) {
			my $whinge = sub { whinge($_[0], gen_edit_fee_tmpl($file, 0, $session, $etoken)) };

			$ft{Name} = clean_words($cgi->param('name'));
			$whinge->('Missing fee template name') unless $ft{Name};
			my %fts = query_all_htsv_in_path("$config{Root}/fee_tmpls", 'Name');
			delete $fts{$edit_id} if $edit_id;	# remove self!
			$whinge->('Template name already taken') if grep (/^$ft{Name}$/, values %fts);

			my $max_rows = -1;
			$max_rows++ while ($max_rows < 10 and defined $cgi->param('Fee_' . ($max_rows + 1)));
			$whinge->('No fees?') unless $max_rows >= 0;

			my %units_cfg = read_units_cfg("$config{Root}/config_units");	# FIXME hilarity if not existing/no commods?
			my @units = known_units(%units_cfg);
			my @commods = grep ($units_cfg{Commodities} =~ /(^|;)$_($|;)/, @units);
			my %curs;

			foreach my $row (0 .. $max_rows) {
				my $amnt = validate_decimal(scalar $cgi->param("Fee_$row"), 'Fee amount', undef, $whinge);
				my $cur;
				($cur = (scalar @units > 1) ? validate_unit(scalar $cgi->param("Unit_$row"), \@units, $whinge) : $units[0]) if scalar @units;
				my $cond;
				foreach (query_pers_attrs) {
					if ($cgi->param("${_}_$row") eq 'if') {
						$cond .= " && $_";
					} elsif ($cgi->param("${_}_$row") eq 'unless') {
						$cond .= " && !$_";
					}
				}
				$cond = substr ($cond, 4) if length $cond;

				$whinge->('Missing fee amount') if length $cond and $amnt == 0;
				next if $amnt == 0;

				push (@{$ft{Fee}}, $amnt);
				if (scalar @units) {
					push (@{$ft{Unit}}, $cur);
					$curs{$cur} = 1 unless grep (/^$cur$/, @commods);
				}
				push (@{$ft{Condition}}, $cond);
			}
			$whinge->('No fees?') unless exists $ft{Fee};
			$whinge->('More than one currency in use') if scalar keys %curs > 1;

			@{$ft{Headings}} = ( 'Fee', 'Condition' );
			splice (@{$ft{Headings}}, 1, 0, 'Unit') if exists $ft{Unit};

			$whinge->('Unable to get commit lock') unless try_commit_lock($sessid);
			bad_token_whinge(gen_manage_fee_tmpls) unless redeem_edit_token($sessid, $edit_id ? "edit_$edit_id" : 'add_ft', $etoken);
			try_commit_and_unlock(sub {
				$file = new_uuidfile("$config{Root}/fee_tmpls") unless ($file);
				write_htsv($file, \%ft);
				my @split_f = split('-', unroot($file));
				add_commit($file, "$split_f[0]...: Fee template \"$ft{Name}\" " . ($edit_id ? 'modified' : 'created'), $session);
			}, $edit_id ? $file : undef);
		} else {
			unlock($file) if $file;
			redeem_edit_token($sessid, $edit_id ? "edit_$edit_id" : 'add_fee_tmpl', $etoken);
		}

		if ($edit_id) {
			emit_with_status((defined $cgi->param('save')) ? "Saved edits to \"$ft{Name}\" fee template" : 'Edit cancelled', gen_edit_fee_tmpl($file, 1, $session, undef));
		} else {
			emit_with_status((defined $cgi->param('save')) ? "Added fee template \"$ft{Name}\"" : 'Add fee template cancelled', gen_manage_fee_tmpls);
		}
	}
	if ($cgi->param('tmpl') eq 'edit_pers_attrs') {
		my $cfg_file = "$config{Root}/config_pers_attrs";

		if (defined $cgi->param('save')) {
			my %cfg;
			my $whinge = sub { whinge($_[0], gen_edit_pers_attrs($etoken)) };

			my $max_rows = -1;
			$max_rows++ while ($max_rows < 100 and defined $cgi->param('Type_' . ($max_rows + 1)));
			$whinge->('No attributes?') unless $max_rows >= 0;

			foreach my $row (0 .. $max_rows) {
				my $type = clean_word($cgi->param("Type_$row"));
				my $attr = clean_words($cgi->param("Attr_$row"));
				next unless $attr;
				$whinge->('Attributes cannot have spaces') unless clean_word($attr);
				$whinge->('Missing type') unless $type;

				push (@{$cfg{Type}}, ucfirst ($type));
				push (@{$cfg{Attribute}}, ucfirst ($attr));
			}
			@{$cfg{Headings}} = ( 'Type', 'Attribute' ) if exists $cfg{Type};

			$whinge->('Unable to get commit lock') unless try_commit_lock($sessid);
			bad_token_whinge(gen_tcp) unless redeem_edit_token($sessid, 'edit_pers_attrs', $etoken);
			try_commit_and_unlock(sub {
				write_htsv($cfg_file, \%cfg);
				add_commit($cfg_file, 'config_pers_attrs: personal attribute types modified', $session);
			}, $cfg_file);
		} else {
			unlock($cfg_file);
			redeem_edit_token($sessid, 'edit_pers_attrs', $etoken);
		}

		emit_with_status((defined $cgi->param('save')) ? 'Saved edits to attribute config' : 'Edit attribute config cancelled', gen_tcp);
	}
	if ($cgi->param('tmpl') eq 'edit_units') {
		my $cfg_file = "$config{Root}/config_units";

		if (defined $cgi->param('rates')) {
			my $whinge = sub { whinge($_[0], gen_edit_units($etoken)) };
			my @rows = map {/^Description_(.*)/; $1} grep (/^Description_.+$/, $cgi->param);

			$whinge->('No currencies?') unless scalar @rows;

			my %cfg = read_units_cfg($cfg_file, 1);
			delete $cfg{$_} foreach (grep (!ref $cfg{$_}, keys %cfg));

			$cfg{Commodities} = '';
			my $anchor_set = 0;
			my $pres_set = 0;
			my $nunits = 0;
			my %rename;

			foreach my $row (@rows) {
				my $code = clean_unit($cgi->param("Code_$row"));
				my $desc = clean_words($cgi->param("Description_$row"));
				next unless $code or $desc;
				$whinge->('Missing/invalid short code') unless $code;
				validate_unitname($code, $whinge);
				unless ($row =~ /^\d+$/ or $code eq $row) {
					# renaming!
					foreach my $key (keys %cfg) {
						if (ref $cfg{$key} and $key =~ /^$row\/(.*)$/) {
							my $new = "$code/$1";
							s/^$key$/$new/ foreach (@{$cfg{Headings}});
							$cfg{$new} = $cfg{$key};
							delete $cfg{$key};
						}
						if (ref $cfg{$key} and $key =~ /^(.*)\/$row$/) {
							my $new = "$1/$code";
							s/^$key$/$new/ foreach (@{$cfg{Headings}});
							$cfg{$new} = $cfg{$key};
							delete $cfg{$key};
						}
					}

					$rename{$row} = $code;
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

			my $max_rows = -1;
			$max_rows++ while ($max_rows < 100 and defined $cgi->param('Date_' . ($max_rows + 1)));
			$whinge->('No rates?') unless $max_rows >= 0;

			my %cfg = read_units_cfg("$cfg_file.p1");	# presume we got here having successfully just defined units
			delete $cfg{$_} foreach (grep (ref $cfg{$_}, keys %cfg));

			my @units = known_units(%cfg);
			my %curs;
			$curs{$_} = 1 foreach (grep (!($cfg{Commodities} =~ /(^|;)$_($|;)/), @units));

			@{$cfg{Headings}} = ( 'Date' );
			foreach (sort @units) {
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
			foreach my $row (0 .. $max_rows) {
				my $rate_found = 0;
				my %row;
				foreach (@{$cfg{Headings}}) {
					next if $_ eq 'Date';
					(my $unit = $_) =~ s/.*\///;
					($unit = $_) =~ s/\/.*// if $unit eq $cfg{Anchor};
					my $ex = $cgi->param("Rate_${row}_$unit");	# I have precisely no idea why this intermediate is necessary
					my $rate = validate_decimal($ex, 'Exchange rate', undef, $whinge);
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

sub query_all_htsv_in_path
{
	my ($path, $key, $all) = @_;

	my @accts = glob("$path/*");
	my %response;

	foreach my $acct (@accts) {
		my %acctdetails = read_htsv($acct);
		next unless $acct =~ /.*\/(.*)/;
		$response{$1} = $acctdetails{$key} if ($all or exists $acctdetails{$key});
	}

	return %response;
}

sub get_acct_name_map
{
	my %ppl = query_all_htsv_in_path("$config{Root}/users", 'Name');
	my %vaccts = query_all_htsv_in_path("$config{Root}/accounts", 'Name');
	return (%ppl, %vaccts);
}

sub date_sorted_htsvs
{
	my %dates = query_all_htsv_in_path("$config{Root}/$_[0]", 'Date', 1);
	my %rds;
	foreach (keys %dates) {
		$dates{$_} = '0.0.0' unless defined $dates{$_} and $dates{$_} =~ /^\s*\d+\s*[.]\s*\d+\s*[.]\s*\d+\s*$/;
		push (@{$rds{$dates{$_}}}, $_);	# non-unique dates
	}
	return map (@{$rds{$_->[0]}}, sort { $a->[1] cmp $b->[1] } map ([ $_, sprintf('%04d%02d%02d', (split /[.]/, $_)[2,1,0]) ], keys %rds));	# Schwartzian transform ftw
}

sub gen_ucp
{
	my ($session, $acct) = @_;
	my $tmpl = load_template('user_cp.html');
	my $user = (defined $acct) ? $acct : $session->param('User');

	# I'm prepared to believe this could get horribly slow.  Caching FIXME?
	my (@credlist, @debtlist);
	foreach my $tg (date_sorted_htsvs('transaction_groups')) {
		my %tgdetails = read_tg("$config{Root}/transaction_groups/$tg");
		my %neg_accts = query_all_htsv_in_path("$config{Root}/accounts", 'IsNegated');
		my %computed = eval { compute_tg(\%tgdetails, \%neg_accts) };
		my $tg_broken = ($@ ne '');
		next unless exists $computed{$user} or $tg_broken;

		my %outputdetails = (
			ACC => $tg,
			TG_CL => (exists $tgdetails{Omit}) ? 'omitted' : '',
			NAME => $tgdetails{Name},
			DATE => $tgdetails{Date},
			SUMMARY_CL => $tg_broken ? 'broken' : '',
			SUMMARY => encode_for_html($tg_broken ? 'TG BROKEN' : ($computed{$user} > 0 ? '+' : '') . $computed{$user}),
		);
		push ((($tg_broken or $computed{$user} >= 0) ? \@credlist : \@debtlist), \%outputdetails);
	}
	my %acct_names = get_acct_name_map;
	$tmpl->param(ACCT => (exists $acct_names{$acct}) ? $acct_names{$acct} : $acct) if defined $acct;
	my @units = known_units();
	$tmpl->param(DEFCUR => (scalar @units) ? $units[0] : undef);
	$tmpl->param(CREDITS => \@credlist);
	$tmpl->param(DEBITS => \@debtlist);
	$tmpl->param(LOGIN => $session->param('User'));

	return $tmpl;
}

sub gen_accts_disp
{
	my $session = $_[0];
	my $tmpl = load_template('accts_disp.html');

	# I'm prepared to believe this could get horribly slow.  Caching FIXME?
	my %running;
	foreach my $tg (glob("$config{Root}/transaction_groups/*")) {
		my %tgdetails = read_tg($tg);
		next if exists $tgdetails{Omit};
		my %neg_accts = query_all_htsv_in_path("$config{Root}/accounts", 'IsNegated');
		my %computed = eval { compute_tg(\%tgdetails, \%neg_accts) };
		if ($@) {
			$tmpl->param(BROKEN => 1);
			return $tmpl;
		}
		foreach (keys %computed) {
			$running{$_} = 0 unless exists $running{$_};
			$running{$_} += $computed{$_};
		}
	}

	my %ppl = query_all_htsv_in_path("$config{Root}/users", 'Name');
	my %vaccts = query_all_htsv_in_path("$config{Root}/accounts", 'Name');
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
	my (@unklist, @ppllist, @vacctslist);
	foreach ((sort @unknown), sort_AoH(\%ppl, \%vaccts)) {
		next unless exists $running{$_};

		my $pc;
		if (exists $ppl{$_}) {
			$pc = 100 / $maxp * abs $running{$_};
		} elsif (exists $vaccts{$_}) {
			$pc = 100 / $maxv * abs $running{$_};
		} else {
			$pc = 100 / $maxu * abs $running{$_};
		}
		my ($r, $g, $b) = (255, 255, 0);
		$r = 255 * 2 * $pc / 100 if $pc < 50;
		$g -= 255 * 2 * ($pc - 50) / 100 if $pc > 50;

		my %outputdetails = (
			ACC => $_,
			NAME => (exists $acct_names{$_}) ? $acct_names{$_} : $_,
			VAL => ($running{$_} > 0 ? '+' : '') . $running{$_},
			C => sprintf('#%02x%02x%02x', $r, $g, $b),
			L => $running{$_} > 0 ? 0 : $pc,
			R => $running{$_} <= 0 ? 0 : $pc,
		);
		if (exists $acct_names{$_}) {
			push ((exists $ppl{$_}) ? \@ppllist : \@vacctslist, \%outputdetails);
		} else {
			push (@unklist, \%outputdetails);
		}
	}
	$tmpl->param(UNKNOWN => \@unklist) if scalar @unklist;
	$tmpl->param(PPL => \@ppllist) if scalar @ppllist;
	$tmpl->param(VACCTS => \@vacctslist) if scalar @vacctslist;
	my %units_cfg = read_units_cfg("$config{Root}/config_units");
	my @units = known_units(%units_cfg);
	$tmpl->param(DEFCUR => (scalar @units) ? "$units_cfg{$units_cfg{Default}} ($units_cfg{Default})" : undef);

	return $tmpl;
}

sub gen_add_swap
{
	my ($swap, $session, $etoken) = @_;
	my $tmpl = load_template('add_swap.html', $etoken);

	my %accts = query_all_htsv_in_path("$config{Root}/users", 'Name');
	my @sorted_accts = sort_AoH(\%accts);
	my @pploptions = map ({ O => $accts{$_}, V => $_, S => $session->param('User') eq $_ }, @sorted_accts);
	my %units_cfg = read_units_cfg("$config{Root}/config_units");
	my @units = known_units(%units_cfg);
	my @currencies = map ({ C => $_, D => $units_cfg{$_}, S => $units_cfg{Default} eq $_ }, @units);

	my @debtaccts;
	if ($swap) {
		@debtaccts = map ({ O => $accts{$_}, V => $_ }, @sorted_accts);
	} else {
		my %cfg = read_htsv("$config{Root}/config_simp_trans", 1);
		@debtaccts = map ({ O => $cfg{Description}[$_], V => "$cfg{DebitAcct}[$_]!$cfg{Description}[$_]" }, 0 .. $#{$cfg{Description}});
	}

	$tmpl->param(SWAP => $swap, PPL => \@pploptions, CUR => (scalar @units > 1), CURS => \@currencies, DEBTACCTS => \@debtaccts);

	return $tmpl;
}

sub gen_add_split
{
	my ($session, $etoken) = @_;
	my $tmpl = load_template('add_split.html', $etoken);

	my %accts = query_all_htsv_in_path("$config{Root}/users", 'Name');
	my @pploptions = map ({ NAME => $accts{$_}, A => $_ }, sort_AoH(\%accts));
	my %units_cfg = read_units_cfg("$config{Root}/config_units");
	my @units = known_units(%units_cfg);
	my @currencies = map ({ C => $_, D => $units_cfg{$_}, S => $units_cfg{Default} eq $_ }, @units);

	$tmpl->param(PPL => \@pploptions, CUR => (scalar @units > 1), CURS => \@currencies);

	return $tmpl;
}

sub gen_manage_tgs
{
	my $tmpl = load_template('manage_transactions.html');
	my %acct_names = get_acct_name_map;

	my @tglist;
	foreach my $tg (date_sorted_htsvs('transaction_groups')) {
		my %tgdetails = read_tg("$config{Root}/transaction_groups/$tg");
		my $tg_fail;
		eval { validate_tg(\%tgdetails, sub { $tg_fail = $_[0]; die }, \%acct_names) };
		my %rates = eval { get_rates($tgdetails{Date}, sub { $tg_fail = "Currency config: $_[0]"; die }) } unless $@;

		my $sum_str = '';
		unless ($tg_fail) {
			my %summary;
			foreach my $i (0 .. $#{$tgdetails{Creditor}}) {
				my $acct = $tgdetails{Creditor}[$i];
				next if $acct =~ /^TrnsfrPot\d$/;
				next if exists $summary{$acct};
				$summary{$acct} = 0;
				foreach my $_ ($i .. $#{$tgdetails{Creditor}}) {
					next if $tgdetails{Creditor}[$_] ne $acct;
					my $rate = (scalar keys %rates < 2) ? 1 : $rates{$tgdetails{Currency}[$_]};
					$summary{$acct} += sprintf('%.2f', $tgdetails{Amount}[$_] * $rate);
				}
				$sum_str .= "$acct_names{$acct} " . (($summary{$acct} < 0) ? '' : '+') . $summary{$acct} . ', ';
			}
		}

		my %outputdetails = (
			ACC => $tg,
			TG_CL => (exists $tgdetails{Omit}) ? 'omitted' : '',
			NAME => $tgdetails{Name},
			DATE => $tgdetails{Date},
			SUMMARY_CL => $tg_fail ? 'broken' : '',
			SUMMARY => encode_for_html($tg_fail ? $tg_fail : substr($sum_str, 0, -2)),
		);
		push (@tglist, \%outputdetails);
	}
	my %units_cfg = read_units_cfg("$config{Root}/config_units");
	my @units = known_units(%units_cfg);
	$tmpl->param(TGS => \@tglist, DEFCUR => (scalar @units) ? "$units_cfg{$units_cfg{Default}} ($units_cfg{Default})" : undef);

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
	my ($tg_file, $view_mode, $session, $etoken) = @_;
	my %tgdetails;
	my $init_creds = 0;

	if ($tg_file) {
		%tgdetails = read_tg($tg_file);
		$init_creds = scalar @{$tgdetails{Creditor}};
		push (@{$tgdetails{Creditor}}, ($session->param('User')) x min(5, 100 - scalar @{$tgdetails{Creditor}})) unless $view_mode;
	} else {
		push (@{$tgdetails{Creditor}}, ($session->param('User')) x 10);
	}

	my $tmpl = load_template('edit_tg.html', $etoken);

	my %ppl = query_all_htsv_in_path("$config{Root}/users", 'Name');
	my %vaccts = query_all_htsv_in_path("$config{Root}/accounts", 'Name');
	my %unknown;
	my @tps_in_use;
	foreach my $acct (@{$tgdetails{Headings}}[2 .. ($#{$tgdetails{Headings}} - 1)], @{$tgdetails{Creditor}}) {
		next if $acct eq 'Currency';
		$unknown{$acct} = $acct unless $acct =~ /^TrnsfrPot\d?$/ or exists $ppl{$acct} or exists $vaccts{$acct};
		$tps_in_use[$1] = 1 if ($acct =~ /^TrnsfrPot(\d)$/);
	}
	my %tps;
	my $tps_to_add = 3;
	foreach my $i (1 .. 9) {
		unless (defined $tps_in_use[$i] or $tps_to_add == 0) {
			$tps_in_use[$i] = 1;
			$tps_to_add--;
		}
		$tps{"TrnsfrPot$i"} = "Transfer Pot $i" if $tps_in_use[$i];
	}
	my %acct_names = (%unknown, %ppl, %vaccts, %tps);
	my @sorted_accts = sort_AoH(\%unknown, \%ppl, \%vaccts);
	my %units_cfg = read_units_cfg("$config{Root}/config_units");
	my @units = known_units(%units_cfg);

	push (@{$tgdetails{$_}}, (0) x (scalar @{$tgdetails{Creditor}} - scalar @{$tgdetails{$_}})) foreach ('Amount', @sorted_accts);
	push (@{$tgdetails{Currency}}, ('') x ($init_creds - scalar @{$tgdetails{Currency}})) if scalar @units > 1;
	push (@{$tgdetails{Currency}}, ($units_cfg{Default}) x (scalar @{$tgdetails{Creditor}} - scalar @{$tgdetails{Currency}})) if scalar @units;

	my @allunits = @units;
	foreach my $cur (@{$tgdetails{Currency}}) {
		push (@allunits, $cur) if defined $cur and not grep (/^$cur$/, @allunits);
	}

	$tmpl->param(TG_ID => $1) if ($tg_file and $tg_file =~ /\/([^\/]+)$/);
	$tmpl->param(RO => $view_mode);
	$tmpl->param(NAME => $tgdetails{Name});
	$tmpl->param(DATE => $tgdetails{Date});
	$tmpl->param(OMIT => 1) if exists $tgdetails{Omit};
	$tmpl->param(CURCOL => scalar @allunits > 1);
	$tmpl->param(NOACCTS => scalar @sorted_accts);
	my %negated = query_all_htsv_in_path("$config{Root}/accounts", 'IsNegated');
	my @heads;
	foreach (@sorted_accts) {
		my $class = (exists $negated{$_}) ? 'negated' : '';
		$class .= ' unknown_d' if exists $unknown{$_};
		push (@heads, { H => $acct_names{$_}, HEAD_CL => $class });
	}
	$tmpl->param(HEADINGS => \@heads);

	my @rows;
	foreach my $row (0 .. $#{$tgdetails{Creditor}}) {
		my @creditors = map ({ O => $acct_names{$_}, V => $_, S => $tgdetails{Creditor}[$row] eq $_, CR_CL => (exists $tps{$_}) ? 'tp' : '' }, (@sorted_accts, sort_AoH(\%tps)));
		my $unk_cur = (not defined $tgdetails{Currency}[$row] or not grep (/^$tgdetails{Currency}[$row]$/, @units));
		my @currencies = map ({ C => $_, S => ((defined $tgdetails{Currency}[$row]) ? ($_ eq $tgdetails{Currency}[$row]) : (not defined $_)) }, $unk_cur ? (@units, $tgdetails{Currency}[$row]) : @units);
		my @rowcontents = map ({ D => $tgdetails{$_}[$row], N => "${_}_$row", D_CL => (exists $unknown{$_}) ? 'unknown_d' : '' }, ( @sorted_accts, 'TrnsfrPot', 'Description' ));
		push (@rows, { ROW_CL => (exists $unknown{@{$tgdetails{Creditor}}[$row]}) ? 'unknown_c' : '',
			       R => $row,
			       CREDS => \@creditors,
			       CUR_CL => (not exists $tps{@{$tgdetails{Creditor}}[$row]} and (not $tgdetails{Currency}[$row] or not grep (/^$tgdetails{Currency}[$row]$/, @units))) ? 'unknown_u' : '',
			       CURS => \@currencies,
			       A => $tgdetails{Amount}[$row],
			       RC => \@rowcontents });
	}
	$tmpl->param(ROWS => \@rows);
	$tmpl->param(DEFCUR => (scalar @allunits == 1) ? "$units_cfg{$units_cfg{Default}} ($units_cfg{Default})" : undef);

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
		if ($tg->{Creditor}[$row] =~ /^TrnsfrPot[1-9]$/) {
			$tg->{Amount}[$row] = '*';
			$tg->{Currency}[$row] = '';
		}
		push (@{$newtg{$_}}, $tg->{$_}[$row]) foreach (@{$tg->{Headings}});
	}

	$newtg{Headings} = $tg->{Headings};

	return %newtg;
}

sub despatch_user
{
	my $session = $_[0];
	my $sessid = $session->id();
	my $cgi = $session->query();
	my $etoken = $cgi->param('etoken');

	return if (defined $cgi->param('logout'));

	emit(gen_manage_tgs) if (defined $cgi->param('manage_tgs'));
	emit(gen_ucp($session)) if (defined $cgi->param('to_cp'));
	emit(gen_accts_disp) if (defined $cgi->param('disp_accts'));

	if ($cgi->param('tmpl') eq 'login_nopw') {
		my $tmpl = gen_ucp($session);
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
	}
	if ($cgi->param('tmpl') eq 'add_swap' or $cgi->param('tmpl') eq 'add_vacct_expense') {
		my $swap = ($cgi->param('tmpl') eq 'add_swap');
		my $tgfile;

		if (defined $cgi->param('save')) {
			my %tg;
			my $whinge = sub { whinge($_[0], gen_add_swap($swap, $session, $etoken)) };

			my %acct_names = query_all_htsv_in_path("$config{Root}/users", 'Name');
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
				my @split_desc = split (' ', @{$tg{Description}}[0]);
				$tg{Name} = "Swap: $acct_names{$debtor}->$acct_names{@{$tg{Creditor}}[0]} for $split_desc[0]";
				$tg{Name} .= ' [...]' if scalar @split_desc > 1;
			} else {
				my %vacct_names = query_all_htsv_in_path("$config{Root}/accounts", 'Name');
				my $type = clean_words($cgi->param('Debtor'));
				$whinge->('Broken expense type') unless defined $type;
				($debtor, $type) = split('!', $type, 2);
				validate_acct($debtor, \%vacct_names, $whinge);
				$whinge->('Broken expense type') unless defined $type;
				$tg{Name} = "Expense: $type";
			}
			push (@{$tg{$debtor}}, 1);

			@{$tg{Headings}} = ( 'Creditor', 'Amount', $debtor, 'Description' );
			splice (@{$tg{Headings}}, 2, 0, 'Currency') if exists $tg{Currency};

			validate_tg(\%tg, $whinge);

			$whinge->('Unable to get commit lock') unless try_commit_lock($sessid);
			bad_token_whinge(gen_ucp($session)) unless redeem_edit_token($sessid, $swap ? 'add_swap' : 'add_vacct_expense', $etoken);
			try_commit_and_unlock(sub {
				$tgfile = new_uuidfile("$config{Root}/transaction_groups");
				write_tg($tgfile, %tg);
				my @split_tgf = split('-', unroot($tgfile));
				add_commit($tgfile, "$split_tgf[0]...: TG \"$tg{Name}\" created", $session);
			});
		} else {
			redeem_edit_token($sessid, $swap ? 'add_swap' : 'add_vacct_expense', $etoken);
		}

		$tgfile =~ /\/([^\/]{4})[^\/]*$/ if $tgfile;
		if ($swap) {
			emit_with_status((defined $cgi->param('save')) ? "Swap saved ($1)" : 'Add swap cancelled', gen_ucp($session));
		} else {
			emit_with_status((defined $cgi->param('save')) ? "Expense saved ($1)" : 'Add expense cancelled', gen_ucp($session));
		}
	}
	if ($cgi->param('tmpl') eq 'add_split') {
		my $tgfile;

		if (defined $cgi->param('save')) {
			my %tg;
			my $whinge = sub { whinge($_[0], gen_add_split($session, $etoken)) };

			$tg{Name} = clean_words($cgi->param('tg_name'));
			$tg{Date} = validate_date(scalar $cgi->param('tg_date'), $whinge);

			my %acct_names = query_all_htsv_in_path("$config{Root}/users", 'Name');
			my %creds;
			foreach my $acct (map { /^Cred_(.*)/; $1 } grep (/^Cred_.+$/, $cgi->param)) {
				validate_acct($acct, \%acct_names, $whinge);
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

			my %debts;
			foreach my $acct (map { /^Debt_(.*)/; $1 } grep (/^Debt_.+$/, $cgi->param)) {
				validate_acct($acct, \%acct_names, $whinge);
				my $amnt = validate_decimal(scalar $cgi->param("Debt_$acct"), 'Debt share', 1, $whinge);
				$debts{$acct} = $amnt unless $amnt == 0;
			}
			push (@{$tg{$_}}, $debts{$_}) foreach (keys %debts);

			push (@{$tg{Description}}, clean_text($cgi->param('Description')));

			@{$tg{Headings}} = ( 'Creditor', 'Amount' );
			push (@{$tg{Headings}}, 'Currency') if exists $tg{Currency};
			push (@{$tg{Headings}}, 'TrnsfrPot') if scalar keys %creds > 1;
			push (@{$tg{Headings}}, sort_AoH(\%debts, 'Description'));

			validate_tg(\%tg, $whinge);

			$whinge->('Unable to get commit lock') unless try_commit_lock($sessid);
			bad_token_whinge(gen_ucp($session)) unless redeem_edit_token($sessid, 'add_split', $etoken);
			try_commit_and_unlock(sub {
				$tgfile = new_uuidfile("$config{Root}/transaction_groups");
				write_tg($tgfile, %tg);
				my @split_tgf = split('-', unroot($tgfile));
				add_commit($tgfile, "$split_tgf[0]...: TG \"$tg{Name}\" created", $session);
			});
		} else {
			redeem_edit_token($sessid, 'add_split', $etoken);
		}

		$tgfile =~ /\/([^\/]{4})[^\/]*$/ if $tgfile;
		emit_with_status((defined $cgi->param('save')) ? "Split saved ($1)" : 'Add split cancelled', gen_ucp($session));
	}
	if ($cgi->param('tmpl') eq 'accts_disp') {
		if (defined $cgi->param('view')) {
			emit(gen_ucp($session, scalar $cgi->param('view')));
		}
	}
	if ($cgi->param('tmpl') eq 'manage_tgs') {
		if (defined $cgi->param('view') or defined $cgi->param('add')) {
			my $view = $cgi->param('view');
			my $tg;

			if ($view) {
				$tg = "$config{Root}/transaction_groups/$view";
				emit_with_status("No such TG \"$view\"", gen_manage_tgs) unless (-r $tg);
			}

			my $tmpl = gen_tg($tg, $view, $session, $view ? undef : get_edit_token($sessid, 'add_tg', $etoken));
			emit($tmpl);
		}
	}
	if ($cgi->param('tmpl') eq 'edit_tg') {
		my $edit_id = clean_filename(scalar $cgi->param('tg_id'), "$config{Root}/transaction_groups");
		my $tgfile = $edit_id ? "$config{Root}/transaction_groups/$edit_id" : undef;

		emit_with_status("No such TG \"$edit_id\"", gen_manage_tgs) if $edit_id && ! -r $tgfile;

		if (defined $cgi->param('edit')) {
			whinge("Couldn't get edit lock for transaction group \"$edit_id\"", gen_manage_tgs) unless try_tg_lock($tgfile, $sessid);
			unless (-r $tgfile) {
				unlock($tgfile);
				whinge("Couldn't edit transaction group \"$edit_id\", file disappeared", gen_manage_tgs);
			}
			emit(gen_tg($tgfile, 0, $session, get_edit_token($sessid, "edit_$edit_id")));
		}

		# only left with save and cancel now
		my %tg;

		if (defined $cgi->param('save')) {
			my $whinge = sub { whinge($_[0], gen_tg($tgfile, 0, $session, $etoken)) };

			$tg{Name} = clean_words($cgi->param('tg_name'));
			$tg{Date} = validate_date(scalar $cgi->param('tg_date'), $whinge);
			(defined $cgi->param('omit')) ? $tg{Omit} = undef : delete $tg{Omit};

			my $max_rows = -1;
			$max_rows++ while ($max_rows < 100 and defined $cgi->param('Creditor_' . ($max_rows + 1)));
			$whinge->('No transactions?') unless $max_rows >= 0;

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

			my @cred_accts = validate_tg(\%tg, $whinge, \%acct_names, $session->param('User'));

			%tg = clean_tg(\%tg, \@cred_accts);
			$whinge->('No transactions?') unless exists $tg{Creditor};

			my %neg_accts = query_all_htsv_in_path("$config{Root}/accounts", 'IsNegated');
			eval { compute_tg(\%tg, \%neg_accts, $whinge) };

			$whinge->('Unable to get commit lock') unless try_commit_lock($sessid);
			bad_token_whinge(gen_manage_tgs) unless redeem_edit_token($sessid, $edit_id ? "edit_$edit_id" : 'add_tg', $etoken);
			try_commit_and_unlock(sub {
				$tgfile = new_uuidfile("$config{Root}/transaction_groups") unless ($tgfile);
				write_tg($tgfile, %tg);
				my @split_tgf = split('-', unroot($tgfile));
				add_commit($tgfile, "$split_tgf[0]...: TG \"$tg{Name}\" " . ($edit_id ? 'modified' : 'created'), $session);
			}, $edit_id ? $tgfile : undef);
		} else {
			unlock($tgfile) if $tgfile;
			redeem_edit_token($sessid, $edit_id ? "edit_$edit_id" : 'add_tg', $etoken);
		}

		$tgfile =~ /\/([^\/]{4})[^\/]*$/ if $tgfile;
		if ($edit_id) {
			emit_with_status((defined $cgi->param('save')) ? "Saved edits to \"$tg{Name}\" ($1) transaction group" : 'Edit cancelled', gen_tg($tgfile, 1, $session, undef));
		} else {
			$etoken = pop_session_data($sessid, $etoken);
			redeem_edit_token($sessid, 'add_vacct_expense', $etoken) if $etoken;
			emit_with_status((defined $cgi->param('save')) ? "Added transaction group \"$tg{Name}\" ($1)" : 'Add transaction group cancelled', $etoken ? gen_ucp($session) : gen_manage_tgs);
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
$ENV{PATH} = '/bin:/usr/bin';
$git = Git::Wrapper->new($config{Root});
update_global_config(read_simp_cfg("$config{Root}/config", 1));

init_units_cfg("$config{Root}/config_units");

create_datastore($cgi, "$config{Root} does not appear to be a BoC data store") unless (-d "$config{Root}/users");
create_datastore($cgi, 'No useable administrator account') unless validate_admins;

emit(load_template($cgi->param('serve') . '.html')) if (defined $cgi->param('serve'));

my $session = CGI::Session->load($cgi) or die CGI::Session->errstr;
$session = get_new_session($session, $cgi) if ($session->is_empty or (not defined $cgi->param('tmpl')) or $cgi->param('tmpl') =~ m/^login(_nopw)?$/);

$session->param('IsAdmin') ? despatch_admin($session) : despatch_user($session);

# the despatchers fall through if the requested action is unknown: make them log in again!
get_new_session($session, $cgi);
