# Historical native API reference

[API.md](API.md) retains a historical native reference for four normalized-factor
declarations in two mathematical leaves, three production modules (including the
root import) and six private test/example modules: nine analyzed modules total.
It is **not** the complete API of this checkout: the current library has eleven
public declarations in four mathematical leaves, five production modules and
eight test modules (thirteen total). Its principal-quotient theorem
[`Ideal.associatedPrimes_quotient_span_singleton_eq_minimalPrimes`](../MinimalPrimes/AssociatedPrincipal.lean)
identifies the associated primes of `R ⧸ Ideal.span {f}` as an `R`-module with
the minimal primes over `(f)` for every `f : R` under `[CommRing R]` and
`[UniqueFactorizationMonoid R]`, including `f = 0` and subsingleton rings.
The [scalar-restriction leaf](../MinimalPrimes/AssociatedRestrictScalars.lean)
adds colon contraction for compatible scalar actions and associated-prime transport
over commutative semirings: contraction needs no surjectivity, while reflection
requires it. The [principal-quotient leaf](../MinimalPrimes/AssociatedPrincipal.lean)
also gives quotient-spectrum criteria under the same ring hypotheses for every generator:
association over the quotient ring and, separately, being the exact annihilator of
an element are each equivalent to minimality of the forward ideal comap above `(f)`.
The historical reference retains native displayed signatures, including implicit
assumptions, and the original project docstrings. Source links navigate the
files shipped in this checkout, but the preserved historical root docstring
does not describe the expanded current root import.
The reference is not an interactive dependency website and bundles no JavaScript,
fonts, remote styles, mathematical source PDF or external documentation text.

## Reproduction

The historical native reference records its exact analyzed Lean/configuration
inputs by full revision and SHA256 in [api-manifest.json](api-manifest.json).
The manifest's `api_sha256` identifies the **original generated Markdown**,
not the current `API.md`: its scope and navigation framing was edited by hand
while preserving all historical native signatures, module sections, docstrings
and source anchors. Five original-project Lean file headers normalized after the
analysis have different **whole-file** hashes in this checkout. All five still
have a four-line header and `module` at line 5, but only the two historical
mathematical leaves and the direct-import test leaf have identical bytes from
`module` onward. The root now imports the new leaf and has an expanded docstring;
the aggregate test module also changed beyond its header. The preserved
historical root docstring is not the current root's docstring.
The old signatures and their leaf-source anchors remain navigable, but the old
input hashes do **not** describe the current source files. This editorial change
neither regenerates native output nor extends the historical manifest to the new
theorem and modules.

For exact reproduction of the *original* analyzed inputs, use a **separate**
checkout of the already official, privately published GitHub `main` commit
`ecbfde70a2a8b4b93098c5b31b3fc033b98fbbb2` (tree
`e40f6833bd8a9ddce99758cc3d6e096e812c906b`), with authorized private
repository access. Its original Lean files and `api-manifest.json` agree with
the analyzed revision `4910cb2e42997cc6ebc4445a6607cf972c93a61b`.
For example, with authorized GitHub access, prepare that distinct checkout:

```sh
git clone https://github.com/FormalFrontier/minimal-primes.git /tmp/minimal-primes-original
git -C /tmp/minimal-primes-original checkout --detach ecbfde70a2a8b4b93098c5b31b3fc033b98fbbb2
```

The header-edited development checkout is **not** that original input checkout.
Binding a *new* native reference to changed source/pins requires new native
generation and affected verification; this historical reference is not a new
generation. Its current framing and relative source links are hand-edited and
are not identified by the manifest's original-output hash.

When the analyzed development commit is available locally, its Git source objects
are authoritative and every input must match. A parentless release checkout or
later release-only history can lack that development ancestry. Only when the
selected full commit object is absent does the adapter instead require the
original release's committed manifest to
equal the freshly reproduced manifest byte-for-byte, including all twelve source/pin
hashes, nine native-record hashes, module/public inventories, tool revision and
output hash. Its source inputs must also equal the release's own committed files.
A present wrong object, stale input, altered native record or uncommitted manifest
is refused. This exact committed-input fallback applies to the original official
checkout above; it does **not** make the five changed-header files in the current
development tree match the original inputs. This is source/output binding, not
native-run attestation or a claim that the old development revision is available
at GitHub; it also does not identify the manually edited current `API.md` as the
original generated output.

Build the unchanged native doc-gen4 tool at
`97d4ecdfc8e09e7f511724c25e303d448de6a3db`, with its committed dependency manifest
and Lean `v4.34.0-rc2`, in a separate checkout using `lake build doc-gen4`.
This core-only tool must not change this library's mathematical dependencies.
First fetch the original checkout's matching mathlib cache and build its nine
modules using that checkout's root README. The [current root README](../README.md)
instead describes the expanded thirteen-module build.

Use the following historical native commands in the separate original checkout's
pinned Lake environment.
Replace the absolute tool/output paths and `FULL_SOURCE_COMMIT` with the actual
full analyzed source revision, not a moving branch. Use a new database/output
directory for each generation. Create its parent directories before `single`:
the native SQLite opener does not create them. Repeat `single` for each of the nine modules
listed in `scripts/generate_api.py`, using its matching path in the source URI:

```sh
mkdir /tmp/minimal-analysis /tmp/minimal-render
lake env /path/to/doc-gen4 single --build /tmp/minimal-analysis MinimalPrimes.Principal api.db https://github.com/FormalFrontier/minimal-primes/blob/FULL_SOURCE_COMMIT/MinimalPrimes/Principal.lean
lake env /path/to/doc-gen4 bibPrepass --build /tmp/minimal-render --none
lake env /path/to/doc-gen4 fromDb --build /tmp/minimal-render --manifest /tmp/minimal-render/manifest.json /tmp/minimal-analysis/api.db
python3 -B scripts/generate_api.py --native-data /tmp/minimal-render/doc-data --source-revision FULL_SOURCE_COMMIT
python3 -B scripts/generate_api.py --native-data /tmp/minimal-render/doc-data --source-revision FULL_SOURCE_COMMIT --check
python3 -B scripts/test_generate_api.py
```

These commands reproduce and check the original output in the separate original
checkout, not the manually framed `API.md` or expanded sources here.

Only the Markdown reference and its manifest are shipped, not the intermediate
HTML, scripts/assets or dependency pages. A source URI is an immutable analysis
identifier, not proof that an unpublished development commit is remotely available
at that GitHub URL. Distributed source hyperlinks instead resolve relatively.

## Scope, checks and provenance

For the historical nine-module inputs, the bounded adapter requires every module
record and exactly the expected four public names/kinds/origins. It refuses
source/pin drift, missing docstrings, malformed header markup and missing
essential assumptions. It retains every native
header text token, normalizing whitespace only. Module comments are extracted
from this library's simple, single module-doc block per source. The adapter is
not a general Lean parser, native-output attestation, proof checker or release
certificate; source/output consistency alone does not attest execution of the
native commands or recheck stored proof bodies.

Atlas adapted the documentation adapter through Integral Closure's documentation
assembly from Anchor's original Formal Frontier Ideal Completion recipe. Collective
credit and Apache-2.0 terms are preserved. Original library docstrings and generated
mathematical signatures are covered by the library's provenance record. Lean,
mathlib and doc-gen4 remain separately credited declared tools/dependencies; their
implementation or external documentation is not copied into this reference.
