package Attrs;

use 5.012;
use strict;
use warnings;

use HeadedTSV;

our $VERSION = '1.00';

use base 'Exporter';

our @EXPORT = qw(init_attr_cfg get_attrs get_attr_synonyms);

my $cfg_file;

sub init_attr_cfg
{
	$cfg_file = $_[0];
	return;
}

sub get_attrs
{
	return sort keys %{{read_htsv($cfg_file, 1)}};
}

sub get_attr_synonyms
{
	my %attrs = read_htsv($cfg_file, 1);
	my %syns;

	foreach my $syn (keys %attrs) {
		push (@{$syns{$syn}}, $syn);
		next unless $attrs{$syn};

		(my $implieds = $attrs{$syn}) =~ s/\s*//g;
		
		foreach my $imp (split (':', $implieds)) {
			push (@{$syns{$imp}}, $syn) unless grep ($_ eq $imp, @{$syns{$imp}});
		}
	}

	return %syns;
}

1;
