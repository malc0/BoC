package Meets;

use 5.012;
use strict;
use warnings;

use Accts qw(grep_acct_key);
use Attrs;
use CleanData qw(clean_date clean_decimal true);
use HeadedTSV qw(read_htsv);
use Units qw(known_commod_descs known_units read_units_cfg validate_units);

our $VERSION = '1.00';

use base 'Exporter';

our @EXPORT = qw(set_meet_config_root get_ft_fees valid_ft meet_valid);

my $root;

sub set_meet_config_root
{
	$root = $_[0];
	return;
}

sub get_ft_fees
{
	my ($acct, %ft) = @_;

	my %attr_syns = get_attr_synonyms;
	my %user = read_htsv("$root/users/$acct");
	my %def_fees;

	foreach (0 .. $#{$ft{Fee}}) {
		my $relevant = 1;

		if (defined $ft{Condition}[$_]) {
			$ft{Condition}[$_] =~ s/\s*//g;
			foreach (split (/&amp;&amp;/, $ft{Condition}[$_])) {
				next unless /^(!?)(.+)$/;
				my $attr_set = grep (exists $user{$_}, @{$attr_syns{$2}});
				$relevant = 0 if ($1 ? $attr_set : !$attr_set);
			}
		}

		$def_fees{$ft{Unit}[$_]} += $ft{Fee}[$_] if $relevant;
	}

	return %def_fees;
}

sub valid_ft
{
	my ($ft_file, $cf) = @_;
	local $_;

	return unless defined $ft_file;
	return unless -r $ft_file;

	(my $ft_id = $ft_file) =~ s/.*\/([^\/]+)/$1/;
	return if $ft_id eq 'none';

	my %ft = read_htsv($ft_file, undef, [ 'Unit', 'Condition' ]);

	return ( Empty => 1 ) unless exists $ft{Headings};

	foreach my $hd ('Fee', 'Unit', 'Condition') {
		return unless grep ($_ eq $hd, @{$ft{Headings}});
		return unless exists $ft{$hd};
	}

	my $bad = 0;
	my $whinge = sub { $bad = 1 };
	validate_units(\%{{read_units_cfg("$root/config_units")}}, $whinge, 1);
	return if $bad;

	my %cds = known_commod_descs;
	my @attrs = get_attrs;

	# duplicates get_cf_drains
	my %drains;
	$drains{$cf->{Fee}[$_]} = 1 foreach (grep (!($cf->{Fee}[$_] =~ /[A-Z]/) && true($cf->{IsDrain}[$_]), 0 .. $#{$cf->{Fee}}));

	foreach my $row (0 .. $#{$ft{Fee}}) {
		return unless defined $ft{Fee}[$row];
		return unless defined clean_decimal($ft{Fee}[$row]);

		return unless defined $ft{Unit}[$row];
		return unless exists $cds{$ft{Unit}[$row]} || exists $drains{$ft{Unit}[$row]};

		next unless defined $ft{Condition}[$row];
		(my $cond = $ft{Condition}[$row]) =~ s/\s*//g;
		my @conds = split ('&amp;&amp;', $cond);
		foreach my $attr (@conds) {
			$attr =~ s/^!//;
			return unless length $attr;
			return unless grep ($_ eq $attr, @attrs);
		}
	}

	return %ft;
}

sub meet_valid
{
	my ($mt, $cf, $skip_ppl_chk) = @_;
	my %meet = %$mt;

	# no check on Leader or Template -- gen_manage_meets is sufficient for now

	foreach (@{$meet{Headings}}) {
		return 0 unless exists $meet{$_};
	}
	foreach my $hd (grep (ref $meet{$_} && $_ ne 'Headings', keys %meet)) {
		return 0 unless grep ($_ eq $hd, @{$meet{Headings}});
	}

	return 0 unless defined clean_date($meet{Date});

	my @units = known_units;
	return 0 if scalar @units > 1 && !(defined $meet{Currency}) && exists $meet{Headings} && scalar grep (!/^(Person|Notes)$/, @{$meet{Headings}});
	return 0 if !(scalar @units) && defined $meet{Currency} && length $meet{Currency};
	return 0 if scalar @units && exists $meet{Currency} && !(defined $meet{Currency} && grep ($_ eq $meet{Currency}, @units));

	return 0 unless %$cf;

	foreach my $hd (grep (!/^(Person|Notes)$/, @{$meet{Headings}})) {
		return 0 unless $hd eq 'CustomFee' || grep ($_ eq $hd, grep (defined, @{$cf->{Fee}}));
		foreach (@{$meet{$hd}}) {
			return 0 unless defined clean_decimal($_);
		}
	}

	my %ppl;
	%ppl = grep_acct_key('users', 'Name') unless $skip_ppl_chk;
	my %seen;
	foreach (@{$meet{Person}}) {
		return 0 unless defined;
		return 0 unless $skip_ppl_chk || exists $ppl{$_};
		$seen{$_}++
	}
	return 0 if grep ($_ > 1, values %seen);

	return 1;
}

1;
