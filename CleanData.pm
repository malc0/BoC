package CleanData;

use 5.012;
use strict;
use warnings;

use HTML::Entities;

our $VERSION = '1.00';

use base 'Exporter';

our @EXPORT = qw(untaint encode_for_file encode_for_html clean_decimal clean_email clean_text clean_username);

sub untaint
{
	return undef unless defined $_[0];
	$_[0] =~ /^(.*)$/;
	return $1;
}

sub encode_for_file
{
	return undef unless $_[0];
	return encode_entities(decode_entities($_[0]), '^A-Za-z0-9¬`!"£\$%^&*()\-_=+{}\[\];:\'@~,.<>/?\\\| ');	# hash not included to avoid getting treated as comment in file!
}

sub encode_for_html
{
	return undef unless $_[0];
	my $escaped = encode_entities(decode_entities($_[0]), '^A-Za-z0-9!%^*()\-_=+{}\[\];:@#~,./?\\\ ');
	$escaped =~ s/&#39;/&apos;/g;
	return $escaped;
}

sub clean_decimal
{
	return 0 unless defined $_[0];
	return 0 if ($_[0] =~ /^\s*$/);
	return undef unless $_[0] =~ /^\s*(-?\d*[\.,·]?\d*)\s*$/;
	my $num_str = $1;
	$num_str =~ tr/,·/../;
	return $num_str;
}

sub clean_email
{
	return undef unless defined $_[0];
	return undef unless $_[0] =~ /^\s*(.+\@.+)\s*$/;
	return encode_for_html($1);
}

sub clean_text
{
	return undef unless defined $_[0];
	return undef if $_[0] eq '';
	my $escaped_text = encode_for_html($_[0]);
	return undef unless $escaped_text =~ /^(.+)$/;
	return $1;
}

sub clean_username
{
	return undef unless defined $_[0];
	# don't allow upper case to give special TG columns (Creditor, TrnsfrPot etc.) their own namespace
	return undef unless $_[0] =~ /^([a-z0-9\-+_]*)$/;	# these have to exist on a filesystem.  certainly do not permit dots (.), as could get trashed lock files
	return $1;
}
