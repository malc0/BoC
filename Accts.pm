package Accts;

use 5.010;
use strict;
use warnings;

use CleanData qw(clean_username);
use HeadedTSV qw(grep_htsv_key);

our $VERSION = '1.00';

use base 'Exporter';

our @EXPORT = qw(set_accts_config_root grep_acct_key get_acct_name_map);

my $root;

sub set_accts_config_root
{
	$root = $_[0];
	return;
}

sub grep_acct_key
{
	my ($flavour, $key) = @_;

	my %raw = grep_htsv_key("$root/$flavour/*", $key);
	my %response;
	$response{$_} = $raw{$_} foreach (grep (clean_username($_), keys %raw));
	return %response;
}

sub get_acct_name_map
{
	my %ppl = grep_acct_key('users', 'Name');
	my %vaccts = grep_acct_key('accounts', 'Name');
	return (%ppl, %vaccts);
}

1;
