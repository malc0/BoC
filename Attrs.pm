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

sub expand_syns
{
	my ($syns, $want, $stop) = @_;

	$stop->{$want} = 1;
	return ($want, map ((exists $syns->{$_}) ? expand_syns($syns, $_, $stop) : $_, grep (!(exists $stop->{$_}), @{$syns->{$want}})));
}

sub uniq {
	return keys %{{ map { $_ => 1 } @_ }};
}

sub get_attr_synonyms
{
	my %attrs = read_htsv($cfg_file, 1);
	my %implied;
	my %syns1;
	my %synsx;

	foreach my $syn (keys %attrs) {
		next unless $attrs{$syn};

		(my $implieds = $attrs{$syn}) =~ s/\s*//g;
		
		push (@{$syns1{$_}}, $syn) foreach (split (':', $implieds));
	}

	foreach my $syn (keys %syns1) {
		@{$synsx{$syn}} = map (expand_syns(\%syns1, $_, { $syn => 1 }), @{$syns1{$syn}});
	}
	push (@{$synsx{$_}}, $_) foreach (keys %attrs);

	@{$synsx{$_}} = uniq(@{$synsx{$_}}) foreach (keys %synsx);

	return %synsx;
}

1;
