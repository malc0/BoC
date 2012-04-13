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
			unless ($content{Headings}) {
				$content{Headings} = [ split ];
			} else {
				my @line = split(' ', $_, scalar(@{$content{Headings}}));
				foreach my $i (0 .. $#{$content{Headings}}) {
					push(@{$content{$content{Headings}[$i]}}, $line[$i]) if exists $line[$i];
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

	($content{Headings}[0] eq 'Creditor') or die "tg data is broken ($content{Headings}[0])";
	($content{Headings}[1] eq 'Amount') or die "tg data is broken ($content{Headings}[1])";
	($content{Headings}[$#{$content{Headings}}] eq 'Description') or die "tg data is broken ($content{Headings}[$#{$content{Headings}}])";

	open(FH, ">$file") or die;
	foreach my $key (keys %content) {
		say FH ((exists $content{$key}) ? "$key	$content{$key}" : "$key") unless ref($content{$key});
	}

	my $cols = scalar(@{$content{Headings}});

	print FH '==========	' foreach (2 .. $cols);
	say FH '==================================================';

	foreach my $key (@{$content{Headings}}) {
		print FH "$key	";
	}
	print FH "\n";

	print FH '==========	' foreach (2 .. $cols);
	say FH '==================================================';

	foreach my $row (0 .. $#{$content{Creditor}}) {
		foreach my $key (@{$content{Headings}}) {
			print FH "$content{$key}[$row]	";
		}
		print FH "\n";
	}

	say FH "\n# vim: ts=11";

	close(FH);
}
