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
	return;
}

sub dedup_headings {
	my $hds = $_[0];

	my %seen;
	$seen{$_}++ foreach (@$hds);
	return if scalar keys %seen == scalar @$hds;

	my %count;
	foreach (@$hds) {
		$_ = "${_}__HTSV" . $count{$_}++ . '__' if $seen{$_} > 1;
	}
}

sub read_htsv
{
	my ($file, $nexist_ok, $hdg_key) = @_;
	$hdg_key = 'Headings' unless defined $hdg_key;
	my $fh;
	my %content;
	my $in_header = 1;

	if ($nexist_ok) {
		no autodie qw(open);
		open ($fh, '<', $file) or return %content;
	} else {
		open ($fh, '<', $file) or confess "$file: $!";
	}
	while (<$fh>) {
		chomp;			# no newline
		s/^#.*//;		# no leading comments
		s/\s#.*//;		# no whitespace prefixed comments
		s/^[ \r\n\v\f]+//;	# no leading white, except tab
		s/\s+$//;		# no trailing white
		next unless length;	# anything left?
		($_) = (/^(.*)$/);	# forcably untaint file input.  if it's bad it shouldn't have got there.

		$in_header = 0 if m/^===/;

		if ($in_header) {
			my ($key, $value) = split (' ', $_, 2);
			$content{$key} = $value;
		} else {
			next if m/^===/;
			unless ($content{$hdg_key}) {
				$content{$hdg_key} = [ split ];
				dedup_headings(\@{$content{$hdg_key}});
			} else {
				my @line = split ('	', $_, scalar(@{$content{$hdg_key}}));
				foreach my $i (0 .. $#{$content{$hdg_key}}) {
					push (@{$content{$content{$hdg_key}[$i]}}, $line[$i]);
				}
			}
		}
	}
	close $fh;

	$read_encoder->(\%content) if ($read_encoder);

	return %content;
}

sub write_htsv
{
	my ($file, $content, $given_ts, $hdg_key, $max_rows) = @_;
	my $ts = $given_ts ? $given_ts : 8;
	$hdg_key = 'Headings' unless defined $hdg_key;
	my $heading_only = not exists $content->{$hdg_key};

	$write_encoder->($content) if ($write_encoder);

	open (my $fh, '>', "$file.new") or confess "$file.new: $!";
	foreach my $key (sort keys %$content) {
		# check if non-white exists (since trailing white killed on read anyway)
		say $fh ((defined $content->{$key} and $content->{$key} =~ /\S/) ? "$key	$content->{$key}" : "$key") unless ref $content->{$key};
	}

	unless ($heading_only) {
		$max_rows = scalar @{$content->{$content->{$hdg_key}[0]}} unless defined $max_rows;
		my $col_line = '=' x ($ts - 1) . '	';
		my $cols = scalar(@{$content->{$hdg_key}});

		print $fh $col_line foreach (2 .. $cols);
		say $fh '==================================================';

		foreach my $key (@{$content->{$hdg_key}}) {
			print $fh "$key	";
		}
		print $fh "\n";

		print $fh $col_line foreach (2 .. $cols);
		say $fh '==================================================';

		foreach my $row (0 .. ($max_rows - 1)) {
			foreach my $key (@{$content->{$hdg_key}}) {
				print $fh $content->{$key}[$row] ? "$content->{$key}[$row]	" : '	';
			}
			print $fh "\n";
		}
	}

	say $fh "\n# vim: ts=$ts" unless ($heading_only and not defined $given_ts);

	close $fh;

	rename ("$file.new", $file) or confess "$file: $!";

	return;
}

1;
