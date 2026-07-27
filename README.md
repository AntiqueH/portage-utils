# Gentoo Portage Utilities

| What     | How                                                       |
| -------- | --------------------------------------------------------- |
| HOMEPAGE | https://wiki.gentoo.org/wiki/Q_applets                    |
| UPSTREAM | https://github.com/gentoo/portage-utils                   |
| FORK     | https://github.com/AntiqueH/portage-utils                 |
| STATUS   | [![Code Sanity](https://github.com/AntiqueH/portage-utils/actions/workflows/code-sanity.yml/badge.svg?branch=upgrade-utils-part-2)](https://github.com/AntiqueH/portage-utils/actions/workflows/code-sanity.yml) |

> This is the antiq fork, focused on prebuilt binary-package support in
> `qmerge`.  For who we are and why this exists, see the
> [qmerge(-next?) fork: the happenings](#qmerge-next-fork--the-happenings) section below; for what works today, see
> [qmerge: prebuilt binary package support](#qmerge-prebuilt-binary-package-support).

portage-utils is a small set of utilities for working with Portage, Gentoo
ebuilds, Gentoo ebuild overlays, installed packages (vdb), and similar sources
of information.  The focus is on size and speed, so everything is in C.

## Building

Run `configure` followed by `make`.  If you're using git-sources, run
`configure` with `--disable-maintainer-mode` or run autoreconf to get
various timestamps correct.

## Helping out

There's a large [TODO](./TODO.md) list with various ideas for
improvements.  There's also a [HACKING](./HACKING.md) doc to help you get
started, and [RESOLVER-DESIGN.md](./RESOLVER-DESIGN.md) documents the qmerge
resolver and binpkg-consumer design.

## Examples

* find elf files linking to old openssl (using app-misc/pax-utils)<br>
  `qlist -Cao | scanelf -BqgN libssl.so.0.9.6 -f -`

* produce a package.use file for currently installed packages<br>
  `qlist -UCq | grep ' ' > package.use`

* find orphan files not owned by any package in /lib and /usr/lib<br>
  `qfile -o {,/usr}/lib/*`

* get PORTDIR and see where it is defined<br>
  `q -ev PORTDIR`

* verify all packages<br>
  `qcheck`

* check validity of the Manifest files for the main tree<br>
  `qmanifest`

* get an overview of what the last emerge call did<br>
  `qlop -E`

## Contact

### Bugs

Please file bugs against the fork at:
	https://github.com/AntiqueH/portage-utils/issues

### Developers

Upstream portage-utils authors:

* solar@gentoo.org
* vapier@gentoo.org
* grobian@gentoo.org

## qmerge(-next?) fork : the happenings

So, one day some 5 old farts were kinda terrified of death, and started to
think what else could we do with our lives, so we started out a *tiny* (lol)
project about 4 years ago. Since we're all longtime Gentoo users, and the
unlucky professional choice we had was information technology, we all agreed
that we would finally bring some help to Gentoo guys.
The effort that we've seen going on in Gentoo these last years I think
inspired us, and both brought us a tons of technical pain (which we tahnk you for).

Why? Well, portage is a whole sh$t of a beautiful monster. It acquired helltons of
features over 20 years. Understanding the whole architecture behind is
beyond what a single mortal human life can. We appreciate this whole technical
pain which happened in the last years, because it's the best thing Gentoo
devs actually added in Gentoo world: a working prebuilt binary system.
Alright, not feature-full. But working, at least. And at last.
So in the last 2 years (ONLY!) portage developed from strictly source
to a very fair prebuilt binary package manager.

I / we not only applaud this, but this has brought us a lot of courage to come forth with our work.
And damn, we're old. If we ever would be public, probably some of our old
friends from Gentoo would probably *recognize* some of us.

But we don't want that. We want this forkie to:

- either be taken into full ownership by Gentoo Council, and implementation
by Fabian Groffen (grobian@gentoo.org)

- either serve as a example to derive from, for future implementations

Original idea pitched by herr me, Antiq ,and each of us rewrote parts of
qmerge over that time (yes, those 4 years).
Since our kids and nephews convinced us to play on Discord with them, we actually created
our own discord server called Gentoo MySea, which we will soon clean before
inviting anyone else.

Signed off: antiq, francoisb, xx36x, marbit, 0times

### Build

By default the bundled libcurl in `src/curl` is compiled in statically; pass
`--with-system-libcurl` to link the system libcurl instead. Before opening a
pull request, we CRUCIALLY recommend going through `./testmycode.sh` from the source root: it runs the gcc/clang
warnings gates (`--enable-werror` plus the modern-C flags), an ASan+UBSan
`make check`, and cppcheck, all from a clean tree.
Yes, we know this libcurl in the source directly has been somewhat of a overhaul, but honestly
maintaining dependencies in Gentoo has been a terrifying experience.
We don't want that again happening with libcurl. Hopefully this is the only one problematic.
Hence, the --system-libcurl from above.

## Some details regarding the expansion of portage-utils for qmerge

Our work here extends portage-utils with a near-complete rewrite of the `qmerge`
applet into a proper consumer and installer for Portage's binary prebuilt
package (binpkg) repositories.
The rest of the applets (qlist, qfile, qcheck, qmanifest, qlop, ...)
mostly track upstream; we didn't change them.

We rather insist on Gentoo taking this over simply because `we do not know` when
will be the next commit feature-add happening. It takes us a lot of time, and probably would
still take a lot of time to adapt whatever Portage has added since our last
parity with 3.0.81.2.

But we do have a few very important warnings here:

> ## ⚠️  qmerge(fork) is still experimental!  ⚠️
> ## ⚠️  qmerge only installs packages, we do not have proper unmerging/depclean yet!  ⚠️
> ## ⚠️  qmerge only installs packages, we do not have proper upgrading/with bdeps yet!  ⚠️

Currently we're working on them, but reverse resolution is by far more painful than
direct resolution.
It can remove one single package via `qmerge -U <pkg>` successfully and **safely** very much
like --depclean, but if you add 2 more, you're going to have to take a walk. For now.

## qmerge: prebuilt binary package support

The goal is parity with `emerge -K and/or -g` (`--usepkgonly --getbinpkg`) across the
whole install path, plus the relevant GLEPs.

Below, ~~struck-through~~ items are implemented and covered in this fork; plain
items are still open.

### Portage binpkg `-K` / `-g` parity

* ~~Binary package selection and dependency (depgraph, deptree) resolution against the binhost `Packages` index~~
* ~~Both container formats: legacy tbz2/XPAK and GLEP 78 `gpkg` (magic-sniffed, not extension-trusted)~~
* ~~Fetch over libcurl with resume, multi-binhost priority fallback, and `QFETCHCOMMAND`/`QRESUMECOMMAND`~~
* ~~Index refresh niceties: `Packages.gz`, `If-Modified-Since` (304), TTL~~
* ~~GLEP 78/63/79 OpenPGP signature verification (Manifest + per-member `.sig`), refuse-before-extract~~
* ~~Byte-identical VDB recording (CONTENTS, environment, DEFINED_PHASES, INSTALL_MASK, ...)~~
* ~~`--usepkg-exclude` / `--usepkg-exclude-live` (and `QMERGE_USEPKG_EXCLUDE`)~~
* ~~`--binpkg-respect-use`~~
* ~~`--rebuilt-binaries` / `--rebuilt-binaries-timestamp`~~
* ~~`-u` update, `-D` deep, `-N` newuse, and a backtracking resolver~~
* ~~`INSTALL_MASK`, `CONFIG_PROTECT`, `CONFIG_PROTECT_MASK`~~
* ~~Package moves (`profiles/updates`) applied client-side from a binhost-published `Moves` file~~
* ~~GLEP 42 news transport, plus the `qnews` reader applet~~
* ~~Binpkg trust-keyring bootstrap via the new `qetuto` applet (a getuto port), auto-invoked when signatures are required~~
* ~~Multi-binhost with distinct per-repo catalogs, priority policy, and provenance tags~~
* ~~Slot / subslot / source-repo provenance in the merge listing (`cat/pf:slot/sub::repo`)~~
* ~~`PKG_INSTALL_MASK` at install time (binpkg-only mask, combined with `INSTALL_MASK`)~~
* ~~Soft-blocker auto-unmerge (`QMERGE_BLOCKERS`, designed, not yet enabled)~~
* Long-tail resolver constructs (PDEPEND blockers, `^^` antislot, perl `:=` generalization)? Needed?

### GLEP parity

We audited 37 GLEPs for what a binhost consumer must honor.
Implemented:

* ~~GLEP 78 : gpkg binary package format~~
* ~~GLEP 74 : Manifest checksum verification~~
* ~~GLEP 63 / 79 : OpenPGP authority and signed packages~~
* ~~GLEP 59 / 61 : Manifest hashes and compression~~
* ~~GLEP 42 : news items (transport + reader)~~
* ~~GLEP 23 : licenses (`ACCEPT_LICENSE` gating)~~
* ~~GLEP 53 : keywords~~
* ~~GLEP 64 : VDB (installed-package database) layout~~
* ~~GLEP 81 : `acct-user` / `acct-group` packages~~
* ~~GLEP 84 : `package.mask` / `package.unmask`~~

The rest are probably much less relevant for binary host & prebuilt stuff.

## How to use?

Well, this one is the easiest.

Everything runs through the `qmerge` applet; `qmerge --help` lists every flag.
Here's what we've implemented so far.

**Actions**


* installs locally downloaded $PKGDIR packages, with deps resolution, gpg verification <br>
  `qmerge <pkg>`

* fetch the newest Packages index (with names) and installs pkg<br>
  `qmerge -f <pkg>`

* pretend: resolve and print the plan without fetching or merging<br>
  `qmerge -p <pkg>`

* search the binhost catalog by name (regex; `-v` also lists non-installable)<br>
  `qmerge -s <regex>`

* search the multibinhost catalog by name (shows *FLAGS as well) <br>
  `qmerge -sv <regex>`

* force-fetch the package itself, skipping the index<br>
  `qmerge -F <pkg>`

* fetch packages (and their deps) into PKGDIR without merging<br>
  `qmerge --fetchonly <pkg>`

* rebuild the Packages index from PKGDIR (binhost side; `-F` = full rebuild); also publishes Moves and News<br>
  `qmerge -i`

* print the pkg_* phase functions a binpkg would run at merge time<br>
  `qmerge --show-phases <pkg>`

**Resolution modifiers**

* update only (skip when the installed version is already newest)<br>
  `qmerge -uK <pkg>`

* deep: consider the whole dependency tree for updates (with `-u` = `emerge -uD`)<br>
  `qmerge -uDK <pkg>`

* newuse: reinstall binpkgs whose built USE (incl. `*_TARGETS`) differs from installed<br>
  `qmerge -NK <pkg>`

* rebuilt-binaries: reinstall same-version binpkgs rebuilt remotely (newer BUILD_TIME)<br>
  `qmerge --rebuilt-binaries -K <pkg>`

* only accept rebuilds at or after an epoch timestamp<br>
  `qmerge --rebuilt-binaries --rebuilt-binaries-timestamp <epoch> -K <pkg>`

* do not merge dependencies (this package only)<br>
  `qmerge -OK <pkg>`

* conflict-repair backtracking rounds during resolution (default 20, 0 disables)<br>
  `qmerge --backtrack <n> -K <pkg>`

**Binpkg selection**

* never satisfy these atoms from binpkgs (refuses, no source fallback)<br>
  `qmerge --usepkg-exclude '<atom> ...' -K <pkg>`

* reject binpkgs built from live ebuilds (`PROPERTIES=live`)<br>
  `qmerge --usepkg-exclude-live -K <pkg>`

* USE gate for candidates: `y` = all repos incl. local, `n` = off (default: foreign only)<br>
  `qmerge --binpkg-respect-use y -K <pkg>`

**Other**

* answer yes: do not prompt before merging<br>
  `qmerge -yK <pkg>`

* parallel download jobs: N, `0` = one per CPU, `y` = max, `n` = serial (default 4)<br>
  `qmerge -j <n> -K <pkg>`

* keep the unpacked binpkgs in the qmerge tempdir (do not clean up)<br>
  `qmerge --keepwork -K <pkg>`

* debug: run the shell phase funcs with `set -x`<br>
  `qmerge --debug -K <pkg>`

* the common flags also apply: `-v` verbose, `-q` quiet, `-C`/`--color`, `-h` help, `-V` version<br>
  `qmerge -vK <pkg>`

### make.conf settings

These go in `/etc/portage/make.conf`, same format as the general usual flags from make.conf*.

* colorless qmerge output, independent of the global `NOCOLOR`<br>
  `QMERGE_NOCOLOR=1`

* default parallel download jobs, same values as `-j`: N, `0` = one per CPU, `y` = max, `n` = serial (default 4)<br>
  `QMERGE_JOBS=8`

* prefetch upcoming binpkgs while merging (on by default; set `0` to disable)<br>
  `QMERGE_PREFETCH=0`

* replace the built-in libcurl downloader with a shell fetcher, portage-style with `${URI}` `${DISTDIR}` `${FILE}` (`QRESUMECOMMAND` is the resume variant; unset = built-in libcurl)<br>
  `QFETCHCOMMAND='wget -O "${DISTDIR}/${FILE}" "${URI}"'`

* package-moves policy: `repo` (local `profiles/updates` wins, the default), `binhost` (fetched `Moves` wins), `repo-only`, `binhost-only`, or `none`<br>
  `QMERGE_MOVES="repo"`

* enable the GLEP 42 news transport (fetch/emit/apply); off by default, the `qnews` reader works regardless<br>
  `QNEWS_ENABLE=1`

* keyservers `qetuto` refreshes the binpkg trust keyring from (space/comma list; default: keys.openpgp.org + keys.gentoo.org)<br>
  `QETUTO_KEYSERVERS="hkps://keys.gentoo.org"`

* release key file(s) `qetuto` imports into the keyring (default: `/usr/share/openpgp-keys/gentoo-release.asc`)<br>
  `QETUTO_KEYS="/usr/share/openpgp-keys/openpgp-keys-argent.asc"`

The per-invocation knobs mirror their command-line flags but are read from the
**environment only** (not make.conf): `QMERGE_USEPKG_EXCLUDE`,
`QMERGE_USEPKG_EXCLUDE_LIVE`, `QMERGE_BINPKG_RESPECT_USE`, `QMERGE_BACKTRACK`,
`QMERGE_IGNORE_TTL`, and `QMERGE_TRUST_HELPER`.

### TODO

* Soon probably a wiki passing through all the depgraph architecture
* Documenting the main differences between qmerge(-next?) and old qmerge
* man page, francoisb will love this one
* Fil-C implementation of memory safety option. We already have something
going, we successfully produced a 16mb memory safe binary, it worked really
swell, but unfortunately gpg verification can't happen yet. Hopefully in
the nearby future.
* Yeah, we overdid it with qnews and qetuto, we should probably be less
a34u243143stic. We should probably let users choose to use getuto and eselect
instead.
* Add some benchmarks comparison with Portage
* Tackle per pkg pkg_* properly
* Although everything here is architecturally ideally correct, we still have
to take a deeper dive in sanitizations