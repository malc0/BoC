package Attrs;

use 5.012;
use strict;
use warnings;

use HeadedTSV;

our $VERSION = '1.00';

use base 'Exporter';

our @EXPORT = qw(init_attr_cfg get_attrs);

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

1;
