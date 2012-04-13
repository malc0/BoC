package TG;

use strict;
use warnings;

our $VERSION = '1.00';

use base 'Exporter';

our @EXPORT = qw(read_tg write_tg);

sub read_tg
{
	my $file = $_[0];
	my %content;
	my $in_header = 1;
	my @headings;

	open(FH, "<$file") or die;
	while (<FH>) {
		chomp;			# no newline
		s/#.*//;		# no comments
		s/^\s+//;		# no leading white
		s/\s+$//;		# no trailing white
		next unless length;	# anything left?
		($_) = (/^(.*)$/);	# forcably untaint file input.  if it's bad it shouldn't have got there.

		$in_header = 0 if m/^===/;

		if ($in_header) {
			my ($key, $value) = split(' ', $_, 2);
			$content{$key} = $value;
		} else {
			next if m/^===/;
			unless (@headings) {
				@headings = split;
			} else {
				my @line = split(' ', $_, scalar(@headings));
				foreach my $i (0 .. $#headings) {
					push(@{$content{$headings[$i]}}, $line[$i]) if exists $line[$i];
				}
			}
		}
	}
	close(FH);

	return %content;
}

sub write_tg
{
	my ($file, %content) = @_;
	my $cols = 0;

	open(FH, ">$file") or die;
	foreach my $key (keys %content) {
		ref($content{$key}) ? $cols += 1 : say FH ((exists $content{$key}) ? "$key	$content{$key}" : "$key");
	}

	print FH '==========	' foreach (2 .. $cols);
	say FH '==================================================';

	print FH 'Creditor	Amount	';
	foreach my $key (keys %content) {
		next unless ref($content{$key});
		next if $key eq 'Creditor';
		next if $key eq 'Amount';
		next if $key eq 'Description';
		print FH "$key	";
	}
	say FH 'Description';

	print FH '==========	' foreach (2 .. $cols);
	say FH '==================================================';

	foreach my $row (0 .. $#{$content{Creditor}}) {
		print FH "$content{Creditor}[$row]	$content{Amount}[$row]	";
		foreach my $key (keys %content) {
			next unless ref($content{$key});
			next if $key eq 'Creditor';
			next if $key eq 'Amount';
			next if $key eq 'Description';
			print FH "$content{$key}[$row]	";
		}
		say FH "$content{Description}[$row]";
	}

	say FH "\n# vim: ts=11";

	close(FH);
}
