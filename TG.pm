package TG;

use 5.012;
use strict;
use warnings;

use CleanData qw(clean_date clean_text clean_username validate_acct validate_acctname validate_decimal);
use HeadedTSV;

our $VERSION = '1.00';

use base 'Exporter';

our @EXPORT = qw(read_tg write_tg validate_tg);

sub read_tg
{
	my %content = read_htsv($_[0]);

	($content{Headings}[0] eq 'Creditor') or die "tg data is broken ($content{Headings}[0])";
	($content{Headings}[1] eq 'Amount') or die "tg data is broken ($content{Headings}[1])";
	($content{Headings}[$#{$content{Headings}}] eq 'Description') or die "tg data is broken ($content{Headings}[$#{$content{Headings}}])";

	foreach my $col (@{$content{Headings}}) {
		next if $col eq 'Creditor';
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
		next if $key eq 'Date' or $key eq 'Name' or $key eq 'Headings';
		$whinge->("Unlisted heading \"$key\"") unless scalar grep (/^$key$/, @{$tg{Headings}}) == 1;
	}

	$whinge->('Missing transaction group name') unless clean_text($tg{Name});
	$whinge->('Unparsable date') unless clean_date($tg{Date});

	my @all_head_accts = grep ((/^(.*)$/ and $1 ne 'Creditor' and $1 ne 'Amount' and $1 ne 'TrnsfrPot' and $1 ne 'Description'), @{$tg{Headings}});
	foreach (@all_head_accts) {
		validate_acctname($_, $whinge);
		validate_acct($_, $valid_accts, $whinge) if $valid_accts;
	}
	my @cred_accts = my @compact_creds = @{$tg{Creditor}};
	foreach (@cred_accts) {
		validate_acctname($_, $whinge) unless $_ =~ /^TrnsfrPot[1-9]$/;
		validate_acct($_, $valid_accts, $whinge) if $valid_accts and not $_ =~ /^TrnsfrPot[1-9]$/;
	}

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
