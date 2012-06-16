package CleanData;

use 5.012;
use strict;
use warnings;

use HTML::Entities;
use Time::ParseDate;

our $VERSION = '1.00';

use base 'Exporter';

our @EXPORT_OK = qw(untaint encode_for_file encode_for_html clean_date clean_decimal clean_email clean_text clean_unit clean_username clean_word clean_words validate_acct validate_acctname validate_date validate_decimal validate_unitname validate_unit);

sub untaint
{
	return undef unless defined $_[0];
	return undef unless $_[0] =~ /^(.*)$/s;
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
	my $escaped = encode_entities(decode_entities($_[0]), '^A-Za-z0-9`!\$%^*()\-_=+{}\[\];:@#~,./?\\\| ');
	$escaped =~ s/&#39;/&apos;/g;
	return $escaped;
}

sub clean_date
{
	return undef unless defined $_[0];
	my ($pd_secs, $pd_error) = parsedate($_[0], (FUZZY => 1, UK => 1, DATE_REQUIRED => 1, PREFER_PAST => 1, WHOLE => 1));
	return $pd_error ? undef : $pd_secs;
}

sub clean_decimal
{
	return 0 unless defined $_[0];
	return 0 if ($_[0] =~ /^\s*$/);
	return undef unless $_[0] =~ /^\s*(-?\d*[.,·]?\d*)\s*$/;
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
	return undef unless $_[0] =~ /^\s*(.+?)\s*$/s;
	return encode_for_html($1);
}

sub clean_unit
{
	return undef unless defined $_[0];
	my $UNIT = uc ($_[0]);
	return undef unless $UNIT =~ /^([A-Z\-+_.]*)$/;
	return $1;
}

sub clean_username
{
	return undef unless defined $_[0];
	# don't allow upper case to give special TG columns (Creditor, TrnsfrPot etc.) their own namespace
	return undef unless $_[0] =~ /^([a-z0-9\-+_]*)$/;	# these have to exist on a filesystem.  certainly do not permit dots (.), as could get trashed lock files
	return $1;
}

sub clean_word
{
	return undef unless defined $_[0];
	return undef unless $_[0] =~ /^\s*(\S*)\s*$/;
	return encode_for_html($1);
}

sub clean_words
{
	return undef unless defined $_[0];
	return undef unless $_[0] =~ /^\s*([^\n\r\v\f]+?)\s*$/;
	return encode_for_html($1);
}

sub validate_acctname
{
	my ($acct, $whinge) = @_;

	$acct = clean_username($acct);

	$whinge->('Disallowed characters in account name') unless defined $acct;
	$whinge->('Account name too short') if length $acct < 3;
	$whinge->('Account name too long') if length $acct > 10;

	return $acct;
}

sub validate_acct
{
	my ($acct, $valid_hash, $whinge) = @_;

	$acct = clean_username($acct);

	$whinge->('Disallowed characters in account name') unless defined $acct;
	$whinge->("Non-existent account \"$acct\"") unless exists $valid_hash->{$acct};

	return $acct;
}

sub validate_date
{
	my ($input, $whinge) = @_;

	$whinge->('Missing date') unless defined $input;

	my $pd_secs = clean_date($input);

	$whinge->("Unparsable date \"$input\"") unless defined $pd_secs;

	return join ('.', ((localtime ($pd_secs))[3], (localtime ($pd_secs))[4] + 1, (localtime ($pd_secs))[5] + 1900));
}

sub validate_decimal
{
	my ($val, $type, $neg_test, $whinge) = @_;

	$val = clean_decimal($val);

	$whinge->("$type non-numeric") unless defined $val;
	$whinge->("$type negative") if $neg_test and $val < 0;

	return $val;
}

sub validate_unitname
{
	my ($unit, $whinge) = @_;

	$unit = clean_unit($unit);

	$whinge->('Disallowed characters in short code') unless defined $unit;
	$whinge->('Short code too short') if length $unit < 1;
	$whinge->('Short code too long') if length $unit > 4;

	return $unit;
}

sub validate_unit
{
	my ($unit, $valid_ref, $whinge) = @_;

	$unit = clean_unit($unit);

	$whinge->('Disallowed characters in currency code') unless defined $unit;
	$whinge->("Non-existent unit \"$unit\"") unless grep (/^$unit$/, @$valid_ref);

	return $unit;
}

1;
