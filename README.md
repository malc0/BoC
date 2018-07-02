# BoC

An online share-based accounting system, suitable for communally incurred expenses.

## About

BoC was originally designed for expedition use, where expenses are distributed by number of nights/car-passengers/beers.  Being online helps accounting transparency, allows real-time review of creditors/debtors, and, if input permissions are devolved, reduces the burden on the treasurer.  Due to its expedition origins it correctly handles exchange rates changing over time.

The system has since accommodated student outdoor club use, handling accounts for events (e.g. away weekends, club dinners), and supports accounts-within-accounts, where ring-fenced pools are maintained and members run tabs.  While the core is share-based, exact accountancy is easily accomplished by using currency values for shares.

All edits are auditable, the backing store being a git repository.

## Documentation

A brief manual is included in doc/boc.pdf.

## Example

A read-only installation using many of BoC's features may be seen at https://sb476.user.srcf.net/boc14/boc.pl (login as `pwithnall`).

## Dependencies

BoC is written in PERL.  You need the following non-core packages:

* CGI::Session,
* Crypt::Cracklib (or comment three lines in boc.pl with the substring `rack`),
* Crypt::PasswdMD5,
* File::Slurp,
* Git::Wrapper,
* HTML::Entities
* HTML::Template,
* HTML::Template::Pro,
* JSON::XS,
* MIME::Lite,
* Text::Password::Pronounceable,
* Time::ParseDate,
* URI::Escape, and
* UUID::Tiny.

## Installation

1. Put all the files somewhere your webserver will interpret as cgi-bin.
2. Edit `boc_config` so the `Root` path points to a directory you wish to use as the datastore.
3. Give the webserver user/group read/write permission to the datastore.  On Debian this would be `chown -R www-data:www-data <datastore path>`.  On OpenSuSE replace `www-data:www-data` with `wwwrun:www`.
4. Go to http://\<wherever-you-put-it\>/boc.pl.

## License

AGPL-1.0 (see LICENSE).

## Thanks

Aiora Zabala originally contributed the default CSS, which makes the interface much less ugly.
