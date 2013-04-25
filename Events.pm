package Events;

use 5.012;
use strict;
use warnings;

use List::Util qw(sum);
use Scalar::Util qw(looks_like_number);

use Accts qw(grep_acct_key);
use Attrs;
use CleanData qw(clean_date clean_decimal true);
use HeadedTSV qw(read_htsv);
use Units qw(known_commod_descs known_units read_units_cfg validate_units);

our $VERSION = '1.00';

use base 'Exporter';

our @EXPORT = qw(set_event_config_root valid_event_type get_event_types get_ft_fees valid_ft event_valid);

my $root;

sub set_event_config_root
{
	$root = $_[0];
	return;
}

sub valid_event_type
{
	my ($et_f, $cf) = @_;
	local $_;

	return unless $et_f;
	return unless -r $et_f;

	(my $et_id = $et_f) =~ s/.*\/([^\/]+)/$1/;
	return if $et_id eq 'none' || $et_id =~ /[.]/;

	my %cf_fees;
	$cf_fees{$_} = 1 foreach (@{$cf->{Fee}});

	my %et = read_htsv($et_f, undef, [ 'Unit' ]);
	return ( Empty => 1 ) unless exists $et{Headings};
	return if scalar grep (!(exists $cf_fees{$_}), @{$et{Unit}});

	my %vaccts = grep_acct_key('accounts', 'Name');
	return if exists $et{LinkedAcct} && !($et{LinkedAcct} && exists $vaccts{$et{LinkedAcct}});
	$et{LinkedAcct} = $cf->{DefaultAccount} unless exists $et{LinkedAcct};

	@{$et{Column}} = () unless exists $et{Column};
	@{$et{Unusual}} = () unless exists $et{Unusual};
	return %et;
}

sub get_event_types
{
	my ($et, $drains, $rows) = @_;

	my @fees = map ($_->[0], sort { (looks_like_number($a->[1]) && looks_like_number($b->[1])) ? $a->[1] <=> $b->[1] : $a->[1] cmp $b->[1] } map ([ $rows ? $_ : $et->{Unit}[$_], $et->{Column}[$_] // 99999998 ], grep (!(defined $et->{Column}[$_] && looks_like_number($et->{Column}[$_]) && $et->{Column}[$_] < 0) && (defined $et->{Unit}[$_]) && ($et->{Unit}[$_] =~ /[A-Z]/ || exists $drains->{$et->{Unit}[$_]}), 0 .. $#{$et->{Unit}})));	# Schwartzian transform ftw.  Magic number sorts columns with missing ordering to just before 99999999 magic number...
	my @exps = map ($_->[0], sort { (looks_like_number($a->[1]) && looks_like_number($b->[1])) ? $a->[1] <=> $b->[1] : $a->[1] cmp $b->[1] } map ([ $rows ? $_ : $et->{Unit}[$_], $et->{Column}[$_] // 99999998 ], grep (!(defined $et->{Column}[$_] && looks_like_number($et->{Column}[$_]) && $et->{Column}[$_] < 0) && (defined $et->{Unit}[$_]) && !($et->{Unit}[$_] =~ /[A-Z]/ || exists $drains->{$et->{Unit}[$_]}), 0 .. $#{$et->{Unit}})));

	return (\@fees, \@exps);
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
				my $attr_set = grep (attr_condition_met($_, 0, %user), @{$attr_syns{$2}});
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

	my %et;
	if ($ft_id =~ /([^.]+)\.(.+)/) {
		return if $2 eq 'none';
		return if $2 =~ /[.]/;
		%et = valid_event_type("$root/event_types/$1", $cf);
		return unless %et;
	} else {
		return if $ft_id =~ /[.]/;
	}

	my %ft = read_htsv($ft_file, undef, [ 'Unit', 'Condition' ]);

	return ( Empty => 1 ) unless exists $ft{Headings};

	foreach my $hd ('Fee', 'Unit', 'Condition') {
		return unless grep ($_ eq $hd, @{$ft{Headings}});
		return unless exists $ft{$hd};
	}

	my $whinge = sub { goto whingefail };
	validate_units(\%{{read_units_cfg("$root/config_units")}}, $whinge, 1, "$root/config_units");

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
		return unless !(exists $et{Unit}) || grep ($ft{Unit}[$row] eq $_, @{$et{Unit}});

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

whingefail:
	return;
}

sub event_valid
{
	my ($e, $cf, $skip_ppl_chk) = @_;
	my %evnt = %$e;

	# no check on Leader or Template -- gen_manage_events is sufficient for now

	foreach (@{$evnt{Headings}}) {
		return 0 unless exists $evnt{$_};
	}
	foreach my $hd (grep (ref $evnt{$_} && $_ ne 'Headings', keys %evnt)) {
		return 0 unless grep ($_ eq $hd, @{$evnt{Headings}});
	}

	return 0 unless defined clean_date($evnt{Date});

	my @units = known_units;
	my %cds = known_commod_descs;
	return 0 if scalar @units > 1 && !(defined $evnt{Currency}) && exists $evnt{Headings} && scalar grep (!(/^(Person|Notes)$/ || ($_ eq 'CustomFee' && (sum map (abs (clean_decimal($_)), @{$evnt{CustomFee}})) == 0) || exists $cds{$_}), @{$evnt{Headings}});
	return 0 if !(scalar @units) && defined $evnt{Currency} && length $evnt{Currency};
	return 0 if scalar @units && exists $evnt{Currency} && !(defined $evnt{Currency} && grep ($_ eq $evnt{Currency}, @units));

	return 0 unless %$cf;

	my (%split_exp_sum, %split_shr_sum);
	foreach my $hd (grep (!/^(Person|Notes)$/, @{$evnt{Headings}})) {
		return 0 unless $hd eq 'CustomFee' || grep ($_ eq $hd, grep (defined, @{$cf->{Fee}})) || $hd =~ /^Split[1-9](Exps|Shrs)$/;
		foreach (@{$evnt{$hd}}) {
			return 0 unless defined clean_decimal($_);
			if ($hd =~ /^Split([1-9])Shrs$/) {
				return 0 if clean_decimal($_) < 0;
				$split_shr_sum{$1} += $_;
			}
			if ($hd =~ /^Split([1-9])Exps$/) {
				$split_exp_sum{$1} += $_ 
			}
		}
	}
	foreach (1 .. 9) {
		return 0 if $split_exp_sum{$_} && !$split_shr_sum{$_};
	}

	my (%ppl, %seen);
	%ppl = (grep_acct_key('users', 'Name'), grep_acct_key('accounts', 'IsNegated')) unless $skip_ppl_chk;
	foreach (@{$evnt{Person}}) {
		return 0 unless defined;
		return 0 unless $skip_ppl_chk || exists $ppl{$_};
		$seen{$_}++
	}
	return 0 if grep ($_ > 1, values %seen);

	return 1;
}

1;
