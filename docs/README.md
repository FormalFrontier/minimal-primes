# Generated API reference

[API.md](API.md) is the release-local reference for all four public declarations, the
three production modules and six private test/example modules. It retains
native displayed signatures, including implicit assumptions, and the original
project docstrings. Source links point to the files shipped in this checkout.
The reference is not an interactive dependency website and bundles no JavaScript,
fonts, remote styles, mathematical source PDF or external documentation text.

## Reproduction

The historical native reference records its exact analyzed Lean/configuration
inputs by full revision and SHA256 in [api-manifest.json](api-manifest.json).
Its `API.md` output is unchanged here. The five original-project Lean file
headers normalized after that analysis have different **whole-file** hashes in
this checkout, but retain the same four-line header, the same `module` at line 5
and identical bytes from `module` onward. Thus the old signatures, docstrings
and line anchors remain navigable in this checkout; the old input hashes do
**not** describe these five current whole files. Do not rehash the old native
manifest or claim this cleanup regenerates or verifies new native output.

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
When binding a *new* native reference to changed source/pins, obtain new native
generation and affected verification; this historical reference itself is not
a new generation. Final release review still binds the unchanged manifest and
reference to the actual candidate commit/tree and checks the navigation.

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
at GitHub.

Build the unchanged native doc-gen4 tool at
`97d4ecdfc8e09e7f511724c25e303d448de6a3db`, with its committed dependency manifest
and Lean `v4.34.0-rc2`, in a separate checkout using `lake build doc-gen4`.
This core-only tool must not change this library's mathematical dependencies.
First fetch the original checkout's matching mathlib cache and build its nine
modules, as described in the [root README](../README.md).

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

Only the Markdown reference and its manifest are shipped, not the intermediate
HTML, scripts/assets or dependency pages. A source URI is an immutable analysis
identifier, not proof that an unpublished development commit is remotely available
at that GitHub URL. Distributed source hyperlinks instead resolve relatively.

## Scope, checks and provenance

The bounded adapter requires every module record and exactly the expected four
public names/kinds/origins. It refuses source/pin drift, missing docstrings,
malformed header markup and missing essential assumptions. It retains every native
header text token, normalizing whitespace only. Module comments are extracted
from this library's simple, single module-doc block per source. The adapter is
not a general Lean parser, native-output attestation, proof checker or release
certificate; retained native command receipts and independent review are required.

The adapter was adapted by Atlas from the Integral Closure first-release
assembly, itself adapted from Anchor's original Formal Frontier Ideal Completion
recipe. Exact original internal revision mapping remains in the nonshipping
publication-readiness research report and immutable predecessor.
Both recipes were unreviewed when reused; no approval transfers with them. Collective
credit and Apache-2.0 terms are preserved. Original library docstrings and generated
mathematical signatures are covered by the library's provenance record. Lean,
mathlib and doc-gen4 remain separately credited declared tools/dependencies; their
implementation or external documentation is not copied into this reference.
