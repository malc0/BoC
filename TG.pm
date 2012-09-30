package TG;

use 5.012;
use strict;
use warnings;

use Carp;
use List::Util qw(sum);

use CleanData qw(clean_date clean_decimal clean_text clean_username clean_words validate_acct validate_acctname validate_decimal validate_unit);
use HeadedTSV;
use Units qw(known_units get_rates);

our $VERSION = '1.00';

use base 'Exporter';

our @EXPORT = qw(read_tg write_tg validate_tg tg_tp_amnt_per_share compute_tg);

my (%valid, %vavalid);

sub read_tg
{
	my %content = read_htsv($_[0], undef, [ 'Creditor', 'Amount', 'Currency', 'TrnsfrPot', 'Description' ]);

	($content{Headings}[0] eq 'Creditor') or confess "tg data is broken ($content{Headings}[0])";
	($content{Headings}[1] eq 'Amount') or confess "tg data is broken ($content{Headings}[1])";
	($content{Headings}[$#{$content{Headings}}] eq 'Description') or confess "tg data is broken ($content{Headings}[$#{$content{Headings}}])";

	$content{Amount}[$_] = ((defined $content{Creditor}[$_] && $content{Creditor}[$_] =~ /^TrnsfrPot\d$/) ? '*' : 0) foreach (grep (!$content{Amount}[$_], 0 .. $#{$content{Amount}}));

	return %content;
}

sub write_tg
{
	my ($file, %content) = @_;

	($content{Headings}[0] eq 'Creditor') or confess "tg data is broken ($content{Headings}[0])";
	($content{Headings}[1] eq 'Amount') or confess "tg data is broken ($content{Headings}[1])";
	($content{Headings}[$#{$content{Headings}}] eq 'Description') or confess "tg data is broken ($content{Headings}[$#{$content{Headings}}])";

	foreach my $col (@{$content{Headings}}) {
		next if $col eq 'Creditor';
		next if $col eq 'Description';
		@{$content{$col}} = map ((!(defined $_) || ($_ =~ /^-?\d*[.]?\d*$/ && ($_ eq '' || $_ == 0))) ? undef : $_, @{$content{$col}});
	}

	return write_htsv($file, \%content, 11);
}

sub validate_tg
{
	my ($id, $tgref, $whinge, $valid_accts, $drained_accts) = @_;
	my %tg = %$tgref;

	if ($id) {
		return @{$vavalid{$id}} if exists $vavalid{$id};
		return @{$valid{$id}} if exists $valid{$id} && !$valid_accts;
	}

	$whinge->("Unknown heading \"$_\"") foreach (grep (!(exists $tg{$_}), @{$tg{Headings}}));
	foreach my $key (keys %tg) {
		next if $key eq 'Headings' or not ref $tg{$key};
		$whinge->("Unlisted heading \"$key\"") unless scalar grep ($_ eq $key, @{$tg{Headings}}) == 1;
	}

	$whinge->('Missing transaction group name') unless clean_words($tg{Name});
	$whinge->('Unparsable date') unless clean_date($tg{Date});
	$whinge->('\'Omit\' keyword should not have a value') if defined $tg{Omit};

	my @all_head_accts = grep ((/^(.*)$/ and $1 ne 'Creditor' and $1 ne 'Amount' and $1 ne 'Currency' and $1 ne 'TrnsfrPot' and $1 ne 'Description'), @{$tg{Headings}});
	foreach (@all_head_accts) {
		validate_acctname($_, $whinge);
		validate_acct($_, $valid_accts, $whinge) if $valid_accts;
	}
	foreach (@{$tg{Creditor}}) {
		validate_acctname($_, $whinge) unless defined $_ && $_ =~ /^TrnsfrPot[1-9]$/;
		validate_acct($_, $valid_accts, $whinge) if $valid_accts && !(defined $_ && $_ =~ /^TrnsfrPot[1-9]$/);
	}

	$whinge->('No creditors defined') unless exists $tg{Creditor};

	my @valid_units = known_units();
	$whinge->('No currency data') if scalar @valid_units > 1 and not exists $tg{Currency};

	my %drained;
	my @compact_creds = @{$tg{Creditor}};
	foreach my $row (0 .. $#{$tg{Creditor}}) {
		my $debtors = 0;
		foreach my $head (@all_head_accts) {
			my $val = validate_decimal($tg{$head}[$row], 'Debt share', 1, $whinge);
			$debtors = 1 unless $val == 0;
		}
		if (grep ($_ eq 'TrnsfrPot', @{$tg{Headings}}) && defined $tg{TrnsfrPot}[$row]) {
			$whinge->('Invalid transfer pot') unless $tg{TrnsfrPot}[$row] =~ /^\s*([1-9]?)\s*$/;
			if ($1 ne '') {
				$whinge->('Cannot have a transfer pot creditor and debtor set in same row') unless clean_username($tg{Creditor}[$row]);
				$debtors = 1;
			}
		}

		my $amnt = $tg{Amount}[$row];
		if ($tg{Creditor}[$row] =~ /^TrnsfrPot[1-9]$/) {
			$whinge->('Amount must be empty or \'*\' for a transfer pot creditor') unless (not defined $amnt) or $amnt =~ /^\s*[*]?\s*$/;
			$whinge->('Transfer pot creditor lacks debtor(s)') if $debtors == 0;
		} else {
			if (defined clean_decimal($amnt)) {
				$amnt = clean_decimal($amnt);
			} elsif ($amnt =~ /^\s*[*]\s*$/) {
				$whinge->("Account $tg{Creditor}[$row] drained more than once in this TG") if exists $drained{$tg{Creditor}[$row]};
				$drained{$tg{Creditor}[$row]} = 1;
				$whinge->("Account $tg{Creditor}[$row] already drained by TG(s): " . join (',', @{$drained_accts->{$tg{Creditor}[$row]}})) if exists $drained_accts->{$tg{Creditor}[$row]};
			} else {
				$whinge->('Amount must be a decimal value or \'*\'');
			}

			$whinge->('Missing debtor(s)') if ($amnt =~ /^\s*[*]\s*$/ || $amnt != 0) && $debtors == 0;
			$whinge->('Missing amount') if !($amnt =~ /^\s*[*]\s*$/) && $amnt == 0 && $debtors == 1;
			validate_unit($tg{Currency}[$row], \@valid_units, $whinge) if exists $tg{Currency} && !($amnt =~ /^\s*[*]\s*$/);
			if (!($amnt =~ /^\s*[*]\s*$/) && $amnt == 0 and $debtors == 0) {
				$whinge->('Description but no amount or debtor(s)') if clean_text($tg{Description}[$row]);
				$compact_creds[$row] = undef;
			}
		}
	}

	foreach my $cred (@{$tg{Creditor}}) {
		next unless $cred =~ /^TrnsfrPot(\d)$/;
		$whinge->("Missing creditor for transfer pot $1") unless exists $tg{TrnsfrPot} and grep (($_ and /^\s*$1\s*$/), @{$tg{TrnsfrPot}});
	}
	foreach my $pot (@{$tg{TrnsfrPot}}) {
		next unless $pot and $pot =~ /^\s*(\d)\s*$/;
		$whinge->("Missing debtor(s) for transfer pot $1") unless grep (($_ and /^TrnsfrPot$1$/), @{$tg{Creditor}}) or scalar grep (($_ and /^\s*$1\s*$/), @{$tg{TrnsfrPot}}) > 1;
	}

	if ($id) {
		$vavalid{$id} = \@compact_creds if $valid_accts;
		$valid{$id} = \@compact_creds;
	}

	return @compact_creds;
}

sub stround
{
	my ($n, $places) = @_;
	my $sign = ($n < 0) ? '-' : '';
	my $abs = abs $n;

	return $sign . substr ($abs + ('0.' . '0' x $places . '5'), 0, $places + length (int ($abs)) + 1);
}

sub tg_tp_amnt_per_share
{
	my ($head_accts, $cred_accts, $tg, $rates, $resolved, $neg_accts) = @_;

	my @tp_net = (0) x 10;
	my @tp_shares = (0) x 10;

	foreach my $row (grep (defined $$cred_accts[$_], 0 .. $#$cred_accts)) {
		next unless ($tg->{Creditor}[$row] =~ /^TrnsfrPot(\d)$/ || (defined $tg->{TrnsfrPot}[$row] && $tg->{TrnsfrPot}[$row] =~ /^\s*(\d)\s*$/));
		my $tp = $1;

		my $amnt;
		if ($tg->{Amount}[$row] =~ /^\s*[*]\s*$/) {
			$amnt = (exists $resolved->{$tg->{Creditor}[$row]} && abs $resolved->{$tg->{Creditor}[$row]} != 0+'inf') ? -$resolved->{$tg->{Creditor}[$row]} : 0+'inf';
		} else {
			$amnt = $tg->{Amount}[$row] * ((scalar keys %$rates < 2) ? 1 : $rates->{$tg->{Currency}[$row]});
		}

		$tp_net[$tp] += (exists $neg_accts->{$tg->{Creditor}[$row]}) ? -$amnt : $amnt if (defined $tg->{TrnsfrPot}[$row] && $tg->{TrnsfrPot}[$row] =~ /^\s*(\d)\s*$/);
		$tp_shares[$tp] += clean_decimal($tg->{$$head_accts[$_]}[$row]) foreach (0 .. $#$head_accts);
	}

	return map ($tp_shares[$_] ? $tp_net[$_] / $tp_shares[$_] : 0, (0 .. 9));
}

sub compute_tg
{
	my ($id, $tgr, $valid_accts, $nar, $rsr, $die) = @_;
	my %tg = %{$tgr};
	my %neg_accts = %{$nar};
	my %resolved = $rsr ? %{$rsr} : ();
	$die = sub { confess $_[0] } unless $die;

	my @cred_accts = validate_tg($id, \%tg, $die, $valid_accts);
	my %rates = get_rates($tg{Date}, sub { $die->("Currency config: $_[0]"); });

	my @all_head_accts = grep ((/^(.*)$/ and $1 ne 'Creditor' and $1 ne 'Amount' and $1 ne 'Currency' and $1 ne 'TrnsfrPot' and $1 ne 'Description'), @{$tg{Headings}});
	my %relevant_accts;

	foreach my $row (0 .. $#cred_accts) {
		next unless defined $cred_accts[$row];
		foreach my $head (@all_head_accts) {
			$relevant_accts{$head} = 0 if clean_decimal($tg{$head}[$row]) != 0;
		}
	}
	my @head_accts = keys %relevant_accts;
	foreach my $row (0 .. $#cred_accts) {
		next unless defined $cred_accts[$row];
		next if $tg{Creditor}[$row] =~ /^TrnsfrPot\d$/;
		$relevant_accts{$tg{Creditor}[$row]} = 0;
	}

	my @taps = tg_tp_amnt_per_share(\@head_accts, \@cred_accts, $tgr, \%rates, \%resolved, $nar);
	my $neg_error = 0;
	foreach my $row (0 .. $#cred_accts) {
		next unless defined $cred_accts[$row];

		my $amnt;
		if ($tg{Amount}[$row] =~ /^\s*[*]\s*$/ && !($tg{Creditor}[$row] =~ /^TrnsfrPot\d$/)) {
			$amnt = (exists $resolved{$tg{Creditor}[$row]} && abs $resolved{$tg{Creditor}[$row]} != 0+'inf') ? -$resolved{$tg{Creditor}[$row]} : 0+'inf';
		} elsif (!($tg{Creditor}[$row] =~ /^TrnsfrPot\d$/)) {
			$amnt = $tg{Amount}[$row] * ((scalar keys %rates < 2) ? 1 : $rates{$tg{Currency}[$row]});
		}

		$relevant_accts{$tg{Creditor}[$row]} += $amnt unless $tg{Creditor}[$row] =~ /^TrnsfrPot\d$/ || $amnt == 0+'inf';
		if (exists $neg_accts{$tg{Creditor}[$row]}) {
			$neg_error += 2 * $amnt;
			$amnt *= -1;
		}

		my @shares = map (clean_decimal($tg{$_}[$row]), @head_accts);
		my $per_share;
		if ($tg{Creditor}[$row] =~ /^TrnsfrPot(\d)$/ || (defined $tg{TrnsfrPot}[$row] && $tg{TrnsfrPot}[$row] =~ /^\s*(\d)\s*$/)) {
			$per_share = $taps[$1];
		} else {
			$per_share = $amnt / sum @shares;
		}
		foreach (0 .. $#head_accts) {
			next if abs $relevant_accts{$head_accts[$_]} == 0+'inf';	# avoid inf-inf=nan cases
			# inf * 0 = nan, not 0
			my $samnt = $shares[$_] ? $per_share * $shares[$_] : 0;
			# allow self-draining accts.  not exporting inf is ok, since other shares will still cause drain detection,
			# and if there are no other shares self-draining is a no-op
			$samnt = 0 if $tg{Creditor}[$row] eq $head_accts[$_] && abs $amnt == 0+'inf';
			if (exists $neg_accts{$head_accts[$_]}) {
				$neg_error += 2 * $samnt;
				$samnt *= -1;
			}
			$relevant_accts{$head_accts[$_]} -= $samnt;
		}
	}

	my $imbalance = $neg_error - sum values %relevant_accts;

	return %relevant_accts if abs $imbalance == 0+'inf';

	$die->("TG does not compute -- probably due to impossible transfer pot (imbalance $imbalance)") if abs ($imbalance) > .000000001;

	my (%pennies, %resid);
	@pennies{keys %relevant_accts} = map (stround($_, 2), values %relevant_accts);
	$neg_error = stround($neg_error, 2);
	for (my $loops = scalar keys %pennies; abs ($neg_error - sum values %pennies) > .0001 and $loops; $loops--) {
		@resid{keys %relevant_accts} = map ($relevant_accts{$_} - $pennies{$_}, keys %relevant_accts);

		my $maxkey;
		my $max = 0;
		foreach (keys %resid) {
			if (abs $resid{$_} > $max) {
				$max = abs $resid{$_};
				$maxkey = $_;
			}
		}
		$pennies{$maxkey} += $resid{$maxkey} < 0 ? -.01 : .01;
		$relevant_accts{$maxkey} = $pennies{$maxkey};
	}
	confess 'Couldn\'t balance TG' if abs ($neg_error - sum values %pennies) > .0001;

	return %pennies;
}

1;
