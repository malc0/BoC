package TG;

use 5.012;
use strict;
use warnings;

use Carp;
use List::Util qw(sum);

use CleanData qw(clean_date clean_decimal clean_text clean_username validate_acct validate_acctname validate_decimal validate_unit);
use HeadedTSV;
use Units qw(known_units get_rates);

our $VERSION = '1.00';

use base 'Exporter';

our @EXPORT = qw(read_tg write_tg validate_tg compute_tg);

sub read_tg
{
	my %content = read_htsv($_[0]);

	($content{Headings}[0] eq 'Creditor') or die "tg data is broken ($content{Headings}[0])";
	($content{Headings}[1] eq 'Amount') or die "tg data is broken ($content{Headings}[1])";
	($content{Headings}[$#{$content{Headings}}] eq 'Description') or die "tg data is broken ($content{Headings}[$#{$content{Headings}}])";

	foreach my $col (@{$content{Headings}}) {
		next if $col eq 'Creditor';
		next if $col eq 'Currency';
		next if $col eq 'Description';
		next if $col eq 'TrnsfrPot';
		if ($col eq 'Amount') {
			foreach my $i (0 .. $#{$content{Amount}}) {
				$content{Amount}[$i] = ($content{Creditor}[$i] =~ /^TrnsfrPot\d$/ ? '*' : 0) unless $content{Amount}[$i];
			}
		} else {
			@{$content{$col}} = map ($_ ? $_ : 0, @{$content{$col}});
		}
	}

	return %content;
}

sub write_tg
{
	my ($file, %content) = @_;

	($content{Headings}[0] eq 'Creditor') or die "tg data is broken ($content{Headings}[0])";
	($content{Headings}[1] eq 'Amount') or die "tg data is broken ($content{Headings}[1])";
	($content{Headings}[$#{$content{Headings}}] eq 'Description') or die "tg data is broken ($content{Headings}[$#{$content{Headings}}])";

	foreach my $col (@{$content{Headings}}) {
		next if $col eq 'Creditor';
		next if $col eq 'Description';
		@{$content{$col}} = map (((not defined $_) or ($_ =~ /^-?\d*\.?\d*$/ and ($_ eq '' or $_ == 0))) ? undef : $_, @{$content{$col}});
	}

	write_htsv($file, \%content, 11);
}

sub validate_tg
{
	my ($tgref, $whinge, $valid_accts, $unset_cred) = @_;
	my %tg = %$tgref;
	$unset_cred = '' unless defined $unset_cred;

	foreach (@{$tg{Headings}}) {
		$whinge->("Unknown heading \"$_\"") unless exists $tg{$_};
	}
	foreach my $key (keys %tg) {
		next if $key eq 'Headings' or not ref $tg{$key};
		$whinge->("Unlisted heading \"$key\"") unless scalar grep (/^$key$/, @{$tg{Headings}}) == 1;
	}

	$whinge->('Missing transaction group name') unless clean_text($tg{Name});
	$whinge->('Unparsable date') unless clean_date($tg{Date});
	$whinge->('\'Omit\' keyword should not have a value') if defined $tg{Omit};

	my @all_head_accts = grep ((/^(.*)$/ and $1 ne 'Creditor' and $1 ne 'Amount' and $1 ne 'Currency' and $1 ne 'TrnsfrPot' and $1 ne 'Description'), @{$tg{Headings}});
	foreach (@all_head_accts) {
		validate_acctname($_, $whinge);
		validate_acct($_, $valid_accts, $whinge) if $valid_accts;
	}
	my @cred_accts = my @compact_creds = @{$tg{Creditor}};
	foreach (@cred_accts) {
		validate_acctname($_, $whinge) unless $_ =~ /^TrnsfrPot[1-9]$/;
		validate_acct($_, $valid_accts, $whinge) if $valid_accts and not $_ =~ /^TrnsfrPot[1-9]$/;
	}

	my @valid_units = known_units();
	$whinge->('No currency data') if scalar @valid_units > 1 and not exists $tg{Currency};

	foreach my $row (0 .. $#cred_accts) {
		my $debtors = 0;
		foreach my $head (@all_head_accts) {
			my $val = validate_decimal($tg{$head}[$row], 'Debt share', 1, $whinge);
			$debtors = 1 unless $val == 0;
		}
		if (grep (/^TrnsfrPot$/, @{$tg{Headings}}) and defined $tg{TrnsfrPot}[$row]) {
			$whinge->('Invalid transfer pot') unless $tg{TrnsfrPot}[$row] =~ /^\s*([1-9]?)\s*$/;
			if ($1 ne '') {
				$whinge->('Cannot have a transfer pot creditor and debtor set in same row') unless clean_username($tg{Creditor}[$row]);
				$debtors = 1;
			}
		}

		if ($tg{Creditor}[$row] =~ /^TrnsfrPot[1-9]$/) {
			my $amnt = $tg{Amount}[$row];
			$whinge->('Amount must be empty or \'*\' for a transfer pot creditor') unless (not defined $amnt) or $amnt =~ /^\s*[\*]?\s*$/;
			$whinge->('Transfer pot creditor lacks debtor(s)') if $debtors == 0;
		} else {
			my $amnt = validate_decimal($tg{Amount}[$row], 'Amount', undef, $whinge);
			$whinge->('Missing debtor(s)') if $amnt != 0 and $debtors == 0;
			$whinge->('Missing amount') if $amnt == 0 and $debtors == 1;
			validate_unit($tg{Currency}[$row], \@valid_units, $whinge) if exists $tg{Currency};
			if ($amnt == 0 and $debtors == 0) {
				$whinge->('Creditor but no amount or debtor(s)') if $tg{Creditor}[$row] ne $unset_cred;
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

	return @compact_creds;
}

sub stround
{
	my ($n, $places) = @_;
	my $sign = ($n < 0) ? '-' : '';
	my $abs = abs $n;
	$sign . substr ($abs + ('0.' . '0' x $places . '5'), 0, $places + length (int ($abs)) + 1);
}

sub compute_tg
{
	my %tg = %{$_[0]};
	my %neg_accts = %{$_[1]};
	my $die = sub { confess $_[0] };

	my @cred_accts = validate_tg(\%tg, $die);
	my %rates = get_rates($tg{Date}, $die);

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

	my @tp_net = (0) x 10;
	my @tp_shares = ([(0) x scalar @head_accts]) x 10;
	my $neg_error = 0;
	foreach my $row (0 .. $#cred_accts) {
		next unless defined $cred_accts[$row];

		my $amnt = $tg{Amount}[$row] * ((scalar keys %rates < 2) ? 1 : $rates{$tg{Currency}[$row]}) unless $tg{Creditor}[$row] =~ /^TrnsfrPot\d$/;

		$relevant_accts{$tg{Creditor}[$row]} += $amnt unless $tg{Creditor}[$row] =~ /^TrnsfrPot\d$/;
		if (exists $neg_accts{$tg{Creditor}[$row]}) {
			$neg_error += 2 * $amnt;
			$amnt *= -1;
		}
		if ($tg{Creditor}[$row] =~ /^TrnsfrPot(\d)$/ or (defined $tg{TrnsfrPot}[$row] and $tg{TrnsfrPot}[$row] =~ /^\s*(\d)\s*$/)) {
			$tp_net[$1] += $amnt if defined $tg{TrnsfrPot}[$row] and $tg{TrnsfrPot}[$row] =~ /^\s*(\d)\s*$/;
			$tp_shares[$1][$_] += $tg{$head_accts[$_]}[$row] foreach (0 .. $#head_accts);
		} else {
			my @shares = map (clean_decimal($tg{$_}[$row]), @head_accts);
			my $share_sum = sum @shares;
			foreach (0 .. $#head_accts) {
				my $samnt = $amnt * $shares[$_] / $share_sum;
				if (exists $neg_accts{$head_accts[$_]}) {
					$neg_error += 2 * $samnt;
					$samnt *= -1;
				}
				$relevant_accts{$head_accts[$_]} -= $samnt;
			}
		}
	}
	foreach my $tp (1 .. 9) {
		next if $tp_net[$tp] == 0;
		my $share_sum = sum @{$tp_shares[$tp]};
		foreach (0 .. $#head_accts) {
			my $amnt = $tp_net[$tp] * $tp_shares[$tp][$_] / $share_sum;
			if (exists $neg_accts{$head_accts[$_]}) {
				$neg_error += 2 * $amnt;
				$amnt *= -1;
			}
			$relevant_accts{$head_accts[$_]} -= $amnt;
		}
	}

	my $imbalance = $neg_error - sum values %relevant_accts;
	die 'TG does not compute -- probably due to impossible transfer pot' if abs ($imbalance) > .000000001;

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
	die 'Couldn\'t balance TG' if abs ($neg_error - sum values %pennies) > .0001;

	return %pennies;
}
