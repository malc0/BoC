package Accts;

use 5.010;
use strict;
use warnings;

use CleanData qw(clean_username);
use HeadedTSV qw(read_htsv);

our $VERSION = '1.00';

use base 'Exporter';

our @EXPORT = qw(set_accts_config_root grep_acct_key get_acct_name_map clear_cache_accts);

my $root;
my %accts;

sub set_accts_config_root
{
	$root = $_[0];
	return;
}

sub grep_acct_key
{
	my ($flavour, $key, $ret_key) = @_;

	$ret_key //= $key;
	my %response;
	foreach (grep (-f, glob ("$root/$flavour/*"))) {
		(my $acct = $_) =~ s/^.*\///;
		$accts{$acct} = \%{{read_htsv($_)}} unless exists $accts{$acct};
		$response{$acct} = $accts{$acct}->{$ret_key} if clean_username($acct) && exists $accts{$acct}->{$key};
	}
	return %response;
}

sub get_acct_name_map
{
	my %ppl = grep_acct_key('users', 'Name');
	my %vaccts = grep_acct_key('accounts', 'Name');
	return (%ppl, %vaccts);
}

sub clear_cache_accts
{
	undef %accts;
	return;
}

1;
