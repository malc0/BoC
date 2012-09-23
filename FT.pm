package FT;

use 5.012;
use strict;
use warnings;

use CleanData qw(clean_decimal);
use HeadedTSV qw(read_htsv);
use Units qw(known_currs known_units read_units_cfg validate_units);

our $VERSION = '1.00';

use base 'Exporter';

our @EXPORT = qw(get_ft_currency get_ft_fees set_ft_config_root valid_ft);

my $root;

sub set_ft_config_root
{
	$root = $_[0];
	return;
}

sub get_ft_currency
{
	my (%ft) = @_;

	return '' if exists $ft{Fee} && scalar @{$ft{Fee}} && !(exists $ft{Unit} && scalar @{$ft{Unit}});

	my @curs = known_currs(read_units_cfg("$root/config_units"));

	foreach my $ft_unit (grep (defined, @{$ft{Unit}})) {
		return $ft_unit if grep ($_ eq $ft_unit, @curs);
	}

	return undef;
}

sub get_ft_fees
{
	my ($acct, %ft) = @_;

	my %user = read_htsv("$root/users/$acct");
	my %def_fees;

	foreach (0 .. $#{$ft{Fee}}) {
		my $relevant = 1;

		if (defined $ft{Condition}[$_]) {
			$ft{Condition}[$_] =~ s/\s*//g;
			foreach (split (/&amp;&amp;/, $ft{Condition}[$_])) {
				next unless /^(!?)(.+)$/;
				$relevant = 0 if ($1 ? exists $user{$2} : !(exists $user{$2}));
			}
		}

		$def_fees{$ft{Unit}[$_] ? $ft{Unit}[$_] : ''} += $ft{Fee}[$_] if $relevant;
	}

	return %def_fees;
}

sub valid_ft
{
	my ($ft_file) = @_;
	local $_;

	return unless defined $ft_file;
	return unless -r $ft_file;

	my %ft = read_htsv($ft_file, undef, [ 'Unit', 'Condition' ]);

	return ( Empty => 1 ) unless exists $ft{Headings};

	foreach my $hd ('Fee', 'Condition') {
		return unless grep ($_ eq $hd, @{$ft{Headings}});
		return unless exists $ft{$hd};
	}
	return if grep ($_ eq 'Unit', @{$ft{Headings}}) && !(exists $ft{Unit});

	my %units_cfg = read_units_cfg("$root/config_units");
	my $bad = 0;
	my $whinge = sub { $bad = 1 };
	validate_units(\%units_cfg, $whinge, 1);
	return if $bad;

	my @units = known_units(%units_cfg);
	my @curs = known_currs(%units_cfg);
	my $unitcol = (exists $ft{Unit});
	return if scalar @units && !$unitcol;

	my %attrs = read_htsv("$root/config_pers_attrs", 1);

	my %curs_in_use;
	foreach my $row (0 .. $#{$ft{Fee}}) {
		return unless defined $ft{Fee}[$row];
		return unless defined clean_decimal($ft{Fee}[$row]);

		if ($unitcol) {
			return unless (defined $ft{Unit}[$row] && length $ft{Unit}[$row]) || !(scalar @units);
			return unless grep ($_ eq $ft{Unit}[$row], @units);
			$curs_in_use{$ft{Unit}[$row]} = 1 if grep ($_ eq $ft{Unit}[$row], @curs);
		}

		next unless defined $ft{Condition}[$row];
		(my $cond = $ft{Condition}[$row]) =~ s/\s*//g;
		my @conds = split ('&amp;&amp;', $cond);
		foreach (@conds) {
			s/^!//;
			return unless length $_;
			return unless exists $attrs{$_};
		}
	}

	return if scalar keys %curs_in_use > 1;

	return %ft;
}

1;
