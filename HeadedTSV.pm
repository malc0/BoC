package HeadedTSV;

use autodie;
use strict;
use warnings;
use Carp;

our $VERSION = '1.00';

use base 'Exporter';

our @EXPORT = qw(set_htsv_encoders read_htsv write_htsv);

my $read_encoder;
my $write_encoder;

sub set_htsv_encoders
{
	($read_encoder, $write_encoder) = @_;
}

sub read_htsv
{
	my ($file, $nexist_ok, $hdg_key) = @_;
	$hdg_key = 'Headings' unless defined $hdg_key;
	my %content;
	my $in_header = 1;

	if ($nexist_ok) {
		no autodie qw(open);
		open(FH, "<$file") or return %content;
	} else {
		open(FH, "<$file") or confess "$file: $!";
	}
	while (<FH>) {
		chomp;			# no newline
		s/^#.*//;		# no leading comments
		s/\s#.*//;		# no whitespace prefixed comments
		s/^[ \r\n\v\f]+//;	# no leading white, except tab
		s/\s+$//;		# no trailing white
		next unless length;	# anything left?
		($_) = (/^(.*)$/);	# forcably untaint file input.  if it's bad it shouldn't have got there.

		$in_header = 0 if m/^===/;

		if ($in_header) {
			my ($key, $value) = split(' ', $_, 2);
			$content{$key} = $value;
		} else {
			next if m/^===/;
			unless ($content{$hdg_key}) {
				$content{$hdg_key} = [ split ];
			} else {
				my @line = split('	', $_, scalar(@{$content{$hdg_key}}));
				foreach my $i (0 .. $#{$content{$hdg_key}}) {
					push (@{$content{$content{$hdg_key}[$i]}}, $line[$i]);
				}
			}
		}
	}
	close(FH);

	$read_encoder->(\%content) if ($read_encoder);

	return %content;
}

sub write_htsv
{
	my ($file, $content, $given_ts, $hdg_key, $max_rows) = @_;
	my $ts = $given_ts ? $given_ts : 8;
	$hdg_key = 'Headings' unless defined $hdg_key;
	my $heading_only = 1;

	$write_encoder->($content) if ($write_encoder);

	open (FH, ">$file.new") or confess "$file.new: $!";
	foreach my $key (keys $content) {
		unless (ref ($content->{$key})) {
			# check if non-white exists (since trailing white killed on read anyway)
			say FH ((defined $content->{$key} and $content->{$key} =~ /\S/) ? "$key	$content->{$key}" : "$key");
		} else {
			$heading_only = 0;
		}
	}

	unless ($heading_only) {
		$max_rows = scalar @{$content->{$content->{$hdg_key}[0]}} unless defined $max_rows;
		my $col_line = '=' x ($ts - 1) . '	';
		my $cols = scalar(@{$content->{$hdg_key}});

		print FH $col_line foreach (2 .. $cols);
		say FH '==================================================';

		foreach my $key (@{$content->{$hdg_key}}) {
			print FH "$key	";
		}
		print FH "\n";

		print FH $col_line foreach (2 .. $cols);
		say FH '==================================================';

		foreach my $row (0 .. ($max_rows - 1)) {
			foreach my $key (@{$content->{$hdg_key}}) {
				print FH $content->{$key}[$row] ? "$content->{$key}[$row]	" : '	';
			}
			print FH "\n";
		}
	}

	say FH "\n# vim: ts=$ts" unless ($heading_only and not defined $given_ts);;

	close (FH);

	rename ("$file.new", $file) or confess "$file: $!";
}

1;
