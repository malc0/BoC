package FT;

use 5.012;
use strict;
use warnings;

use Attrs;
use CleanData qw(clean_decimal);
use HeadedTSV qw(read_htsv);
use Units qw(known_commod_descs read_units_cfg validate_units);

our $VERSION = '1.00';

use base 'Exporter';

our @EXPORT = qw(get_ft_fees set_ft_config_root valid_ft);

my $root;

sub set_ft_config_root
{
	$root = $_[0];
	return;
}

sub get_ft_fees
{
	my ($acct, %ft) = @_;

	my %attr_syns = get_attr_synonyms;
	my %user = read_htsv("$root/users/$acct");
	my %def_fees;

	foreach (0 .. $#{$ft{Fee}}) {
		my $relevant = 1;

		if (defined $ft{Condition}[$_]) {
			$ft{Condition}[$_] =~ s/\s*//g;
			foreach (split (/&amp;&amp;/, $ft{Condition}[$_])) {
				next unless /^(!?)(.+)$/;
				my $attr_set = grep (exists $user{$_}, @{$attr_syns{$2}});
				$relevant = 0 if ($1 ? $attr_set : !$attr_set);
			}
		}

		$def_fees{$ft{Unit}[$_]} += $ft{Fee}[$_] if $relevant;
	}

	return %def_fees;
}

sub valid_ft
{
	my ($ft_file) = @_;
	local $_;

	return unless defined $ft_file;
	return unless -r $ft_file;

	(my $ft_id = $ft_file) =~ s/.*\/([^\/]+)/$1/;
	return if $ft_id eq 'none';

	my %ft = read_htsv($ft_file, undef, [ 'Unit', 'Condition' ]);

	return ( Empty => 1 ) unless exists $ft{Headings};

	foreach my $hd ('Fee', 'Unit', 'Condition') {
		return unless grep ($_ eq $hd, @{$ft{Headings}});
		return unless exists $ft{$hd};
	}

	my $bad = 0;
	my $whinge = sub { $bad = 1 };
	validate_units(\%{{read_units_cfg("$root/config_units")}}, $whinge, 1);
	return if $bad;

	my %cds = known_commod_descs;
	my @attrs = get_attrs;

	foreach my $row (0 .. $#{$ft{Fee}}) {
		return unless defined $ft{Fee}[$row];
		return unless defined clean_decimal($ft{Fee}[$row]);

		return unless defined $ft{Unit}[$row];
		return unless exists $cds{$ft{Unit}[$row]};

		next unless defined $ft{Condition}[$row];
		(my $cond = $ft{Condition}[$row]) =~ s/\s*//g;
		my @conds = split ('&amp;&amp;', $cond);
		foreach my $attr (@conds) {
			$attr =~ s/^!//;
			return unless length $attr;
			return unless grep ($_ eq $attr, @attrs);
		}
	}

	return %ft;
}

1;
