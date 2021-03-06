package Attrs;

use 5.012;
use strict;
use warnings;

use HeadedTSV;

our $VERSION = '1.00';

use base 'Exporter';

our @EXPORT = qw(init_attr_cfg get_sys_attrs get_attrs get_attrs_full get_attr_synonyms attr_condition_met);

my $cfg_file;

sub init_attr_cfg
{
	$cfg_file = $_[0];
	return;
}

sub get_sys_attrs
{
	return sort ( 'IsAdmin', 'IsAuthed', 'IsPleb', 'MayAddEditTGs', 'MayEditOwnEvents', 'MayStewardEvents' );
}

sub get_attrs_full
{
	my ($no_sys, $no_combs) = @_;
	my @sys_attrs = get_sys_attrs;
	my %cfg = read_htsv($cfg_file, 1);

	if ($no_combs) {
		delete $cfg{$_} foreach (grep (/&amp;&amp;/, keys %cfg));
	}

	$cfg{$_} = undef foreach (grep (!(exists $cfg{$_}), @sys_attrs));
	$cfg{IsAdmin} = join (':', grep ($_ ne 'IsAdmin', @sys_attrs));
	if ($no_sys) {
		delete $cfg{$_} foreach (@sys_attrs);
	}

	return %cfg;
}

sub get_attrs
{
	return sort keys %{{get_attrs_full($_[0], 1)}};
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
	my %attrs = get_attrs_full;
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

sub attr_condition_met
{
	my ($cond, $authed, %attrs) = @_;

	$cond =~ s/\s*//g;
	foreach (split ('&amp;&amp;', $cond)) {
		next if $_ eq 'IsPleb';
		next if $_ eq 'IsAuthed' && $authed;
		next if exists $attrs{$_};
		return 0;
	}

	return 1;
}

1;
