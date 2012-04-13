package SimpCfg;

use strict;
use warnings;

our $VERSION = '1.00';

use base 'Exporter';

our @EXPORT = qw(read_simp_cfg write_simp_cfg);

sub read_simp_cfg
{
	my $file = $_[0];
	my %config;

	open(FH, "<$file") or die;
	while (<FH>) {
		chomp;			# no newline
		s/#.*//;		# no comments
		s/^\s+//;		# no leading white
		s/\s+$//;		# no trailing white
		next unless length;	# anything left?
		my ($key, $value) = split(' ', $_, 2);
		# forcably untaint file input.  if it's bad it shouldn't have got there.
		if (defined $value) {
			($config{$key}) = ($value =~ /^(.*)$/g);
		} else {
			$config{$key} = undef;
		}
	}
	close(FH);

	return %config;
}

sub write_simp_cfg
{
	my ($file, %config) = @_;

	open(FH, ">$file") or die;
	foreach my $key (keys %config) {
		say FH ((exists $config{$key}) ? "$key	$config{$key}" : "$key");
	}
	close(FH);
}
