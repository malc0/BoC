package Units;

use 5.012;
use strict;
use warnings;

use CleanData qw(validate_date validate_decimal);
use HeadedTSV;

our $VERSION = '1.00';

use base 'Exporter';

our @EXPORT = qw(init_units_cfg read_units_cfg write_units_cfg known_units validate_units);

my $cfg_file;

sub init_units_cfg
{
	$cfg_file = $_[0];
}

sub read_units_cfg
{
	my ($file, $nofix) = @_;
	my %cfg = read_htsv($file, 1);

	return %cfg if $nofix;

	$cfg{Commodities} = '' unless exists $cfg{Commodities} and defined $cfg{Commodities};
	unless ($cfg{Anchor} and exists $cfg{$cfg{Anchor}}) {
		foreach (keys %cfg) {
			next if ref $cfg{$_} or $_ eq 'Anchor' or $_ eq 'Default' or $_ eq 'Commodities';
			# this will still work if more than one real currency -- it's up to the validator to fix that
			$cfg{Anchor} = $_ unless $cfg{Commodities} =~ /(^|;)$_($|;)/;
		}
	}
	$cfg{Default} = $cfg{Anchor} unless ($cfg{Default} and exists $cfg{$cfg{Default}}) or not exists $cfg{Anchor};

	return %cfg;
}

sub write_units_cfg
{
	my ($file, $cfg) = @_;

	my $ncurr = 0;
	foreach (keys %$cfg) {
		next if ref $cfg->{$_} or $_ eq 'Anchor' or $_ eq 'Default' or $_ eq 'Commodities';
		$ncurr++ if not $cfg->{Commodities} =~ /(^|;)$_($|;)/;
	}
	delete $cfg->{Anchor} if $ncurr < 2;
	delete $cfg->{Default} if $ncurr < 2;
	delete $cfg->{Commodities} unless length $cfg->{Commodities};

	unless (exists $cfg->{Anchor} or exists $cfg->{Commodities}) {
		foreach (keys %$cfg) {
			delete $cfg->{$_} if ref $cfg->{$_};
		}
	}

	write_htsv($file, $cfg, 12);
}

sub known_units
{
	my %cfg = @_;
	%cfg = read_units_cfg($cfg_file) unless $_[0];

	return unless $cfg{Default};

	my @units;
	foreach (keys %cfg) {
		push (@units, $_) unless ref $cfg{$_} or $_ eq 'Anchor' or $_ eq 'Default' or $_ eq 'Commodities';
	}

	return ($cfg{Default}, sort grep (!/^$cfg{Default}$/, @units));	# presentation unit returned first
}

sub validate_units
{
	my ($uref, $whinge, $defs_only) = @_;
	my %cfg = %$uref;

	my $ncommods = 0;
	foreach ('Anchor', 'Default', 'Commodities') {
		next unless exists $cfg{$_};
		$whinge->("$_ key has undefined value") unless defined $cfg{$_};
		$whinge->("$_ key is a reference!?") if ref $cfg{$_};
		if ($_ eq 'Commodities') {
			foreach (split (';', $cfg{Commodities})) {
				$ncommods++;
				$whinge->("Commodities references unknown unit \"$_\"") unless exists $cfg{$_};
				$whinge->("A commodity ($_) cannot be used as the anchor currency") if exists $cfg{Anchor} and $cfg{Anchor} eq $_;
			}
		} else {
			$whinge->("$_ references unknown unit \"$cfg{$_}\"") unless exists $cfg{$cfg{$_}};
		}
	}
	my @units = known_units(%cfg);
	my $nunits = scalar @units;
	foreach (@units) {
		$whinge->("$_ unit has no description") unless defined $cfg{$_};
	}
	$whinge->('No currency defined') if $nunits and $nunits - $ncommods == 0;
	$whinge->('Anchor currency not set with multiple currencies defined') if $nunits - $ncommods > 1 and not exists $cfg{Anchor};
	$whinge->('Presentation currency not set with multiple currencies defined') if $nunits - $ncommods > 1 and not exists $cfg{Default};

	return if $defs_only;

	$whinge->('No rates defined when more than one currency') if $nunits > 1 and not exists $cfg{Headings};

	return unless exists $cfg{Headings};

	$whinge->('Exchange rate section defined when less than two units') if $nunits < 2;

	foreach (@{$cfg{Headings}}) {
		$whinge->("Unknown heading \"$_\"") unless exists $cfg{$_};
	}
	foreach my $key (keys %cfg) {
		next if $key eq 'Headings' or not ref $cfg{$key};
		$whinge->("Unlisted heading \"$key\"") unless scalar grep (/^$key$/, @{$cfg{Headings}}) == 1;
	}

	foreach my $unit (@units) {
		my $match = ($cfg{Commodities} =~ /(^|;)$unit($|;)/) ? "\/$unit\$" : "^$unit\/";
		my @allex = grep (/$match/, @{$cfg{Headings}});
		my @ex;
		foreach (@allex) {
			(my $in = $_) =~ s/$match//;
			push (@ex, $_) unless $cfg{Commodities} =~ /(^|;)$in($|;)/;
		}

		if ($unit eq $cfg{Anchor}) {
			$whinge->("Anchor currency ($cfg{Anchor}) should not have an exchange rate") if scalar @ex;
			next;
		}
		$whinge->("$unit has no currency-based exchange rate") unless scalar @ex;
		$whinge->("$unit has more than one exchange rate") if scalar @ex > 1;

		(my $in = $ex[0]) =~ s/$match//;
		$whinge->("$unit must be defined in terms of the anchor currency ($cfg{Anchor})") unless $in eq $cfg{Anchor} or $cfg{Commodities} =~ /(^|;)$unit($|;)/;
	}

	my %dates;
	foreach my $row (0 .. $#{$cfg{Date}}) {
		my $date = validate_date($cfg{Date}[$row], $whinge);
		$whinge->("Duplicated date ($cfg{Date}[$row])") if exists $dates{$date};
		$dates{$date} = 1;
		my $rate_found = 0;
		foreach (@{$cfg{Headings}}) {
			next if $_ eq 'Date';
			my $rate = validate_decimal($cfg{$_}[$row], "Exchange rate (date $cfg{Date}[$row])", 1, $whinge);
			$rate_found = 1 unless $rate == 0;
		}
		$whinge->("No valid rates found for $cfg{Date}[$row]") unless $rate_found;
	}
	foreach my $ex (@{$cfg{Headings}}) {
		next if $ex eq 'Date';
		my $rate_found = 0;
		foreach (0 .. $#{$cfg{Date}}) {
			my $rate = validate_decimal($cfg{$ex}[$_], "Exchange rate (date $cfg{Date}[$_])", 1, $whinge);
			$rate_found = 1 unless $rate == 0;
		}
		$whinge->("No valid rates found for $ex") unless $rate_found;
	}
}

1;