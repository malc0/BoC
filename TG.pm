package TG;

use strict;
use warnings;
use HeadedTSV;

our $VERSION = '1.00';

use base 'Exporter';

our @EXPORT = qw(read_tg write_tg);

sub read_tg
{
	my %content = read_htsv($_[0]);

	($content{Headings}[0] eq 'Creditor') or die "tg data is broken ($content{Headings}[0])";
	($content{Headings}[1] eq 'Amount') or die "tg data is broken ($content{Headings}[1])";
	($content{Headings}[$#{$content{Headings}}] eq 'Description') or die "tg data is broken ($content{Headings}[$#{$content{Headings}}])";

	foreach my $col (@{$content{Headings}}) {
		next if $col eq 'Creditor';
		next if $col eq 'Description';
		@{$content{$col}} = map ($_ ? $_ : 0, @{$content{$col}});
	}

	return %content;
}

sub write_tg
{
	my ($file, %content) = @_;

	($content{Headings}[0] eq 'Creditor') or die "tg data is broken ($content{Headings}[0])";
	($content{Headings}[1] eq 'Amount') or die "tg data is broken ($content{Headings}[1])";
	($content{Headings}[$#{$content{Headings}}] eq 'Description') or die "tg data is broken ($content{Headings}[$#{$content{Headings}}])";

	foreach my $col (@{$content{Headings}}) {
		next if $col eq 'Creditor';
		next if $col eq 'Description';
		@{$content{$col}} = map (((not defined $_) or ($_ =~ /^-?\d*\.?\d*$/ and ($_ eq '' or $_ == 0))) ? undef : $_, @{$content{$col}});
	}

	write_htsv($file, \%content, 11);
}
