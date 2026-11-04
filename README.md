# Minimal primes

Lean theory of minimal and associated prime ideals, localization, Krull
dimension, finite-height prime chains and prime ideals of products of semifields.
The results include semiring versions
of principal-ideal factorization and localization criteria, and ring-theoretic
dimension and associated-prime comparisons.

## Headline results

### Coordinate maps and zero-reflection of dependent filter products

For any filter `D` and independently universed dependent type families `R` and `S`,
coordinate functions `φ i : R i → S i` induce the canonical
[`Filter.Product.map`](MinimalPrimes/Order/Filter/Product/Map.lean)
from `D.Product R` to `D.Product S`. Its representative law uniquely characterizes
it, with identity and composition laws and agreement with the existing semiring
and constant-family germ maps. No algebra, points or proper-filter hypothesis is
needed for the coordinate map.

If the coordinate functions preserve selected total sections `a` and `b`
eventually, the induced map reflects the represented point `b` to `a` exactly
when the coordinate functions reflect these points eventually. For fibrewise
`ZeroHom`s this gives zero-reflection using only the **same selected fibre zeros**:
`Filter.Product.zeroPoint` is the class of that zero section, not a new Product
zero instance. No multiplication, addition or scalar zero is required.

`Filter.Product.map_surjective_iff` retains the exact global-section alternatives:
the total target section type is empty, or the total source section type is
nonempty and the coordinate maps are surjective eventually. An empty source fibre
ignored by the filter cannot be silently filled. The
[dependent controls](MinimalPrimesTest/Order/Filter/Product/Map.lean) include varying
`Fin (n + 3) → Fin (n + 4)` maps that reflect zero but are neither injective nor
additive, and a frequent bad locus giving a genuine nonzero kernel class.

### Reindexing dependent filter products

For independently universed indices and fibres, a map `u : ι → κ` with
`Tendsto u F G` induces
[`Filter.Product.compTendsto`](MinimalPrimes/Order/Filter/Product/CompTendsto.lean)
from `G.Product R` to `F.Product (fun i => R (u i))`. It sends a section to its
precomposition, respects identity and composition, and agrees with the existing
`Filter.Germ.compTendsto` on constant families. No algebra, total-section existence
or proper-filter assumption is needed. The full criterion
`compTendsto_injective_iff` says that pullback is injective exactly when the original
total-section type is empty or
`Filter.map u F ⊓ principal {j | Nontrivial (R j)} =
G ⊓ principal {j | Nontrivial (R j)}`. Exact filter-image equality therefore suffices
(`compTendsto_injective_of_map_eq`), without injectivity of `u`, but is not necessary
for a fixed family. An index equivalence makes pullback surjective with only forward
convergence (`compTendsto_surjective_of_equiv`), but not necessarily injective.
Convergence in both directions gives `Filter.Product.compTendstoEquiv`, whose inverse
uses canonical dependent Pi reindexing. The
[dependent Bool client](MinimalPrimesTest/Order/Filter/Product/CompTendsto.lean)
contrasts a four-to-two noninjective pullback with a two-to-two injective pullback
for the same unequal filters, by making the ignored fibre a singleton. It also
exhibits an injective, non-surjective diagonal.

The underlying
[`Filter.forall_eventually_eq_iff`](MinimalPrimes/Order/Filter/Basic.lean) works for
fibres in any independently universed `Sort`: two filters give the same eventual
equality on all pairs of total sections exactly when there is no total section or
their restrictions to `{i | ∃ x y : R i, x ≠ y}` agree. For Type-valued families,
[`Filter.productSetoid_eq_iff`](MinimalPrimes/Order/Filter/Product.lean) expresses
this using the existing section setoids and stock `Nontrivial` support. An empty
fibre ignored by a filter still prevents total sections; eventual inhabitation
cannot replace the empty-total-section alternative.

### Centers of dependent filter products

For any filter and an independently universed family with multiplication, a section
represents an element of the full intrinsic center exactly when it is central
eventually. With a two-sided identity in each fibre,
[`Filter.Product.centerEquiv`](MinimalPrimes/Order/Filter/Product/Center.lean)
identifies the product of the fibre centers with the center of the product.
Neither associativity nor a proper filter is required. The representative API
selects a total center-valued section agreeing eventually, not canonically at
ignored indices. The [varying-family client](MinimalPrimesTest/Order/Filter/Germ/Center.lean)
uses retained fibres of sizes four and sixteen with nonassociative multiplication;
the existing constant-germ API and its client remain available.

### Reduced filter germs

For independent index and value universes, any filter `D`, and a value type `M`
with only zero and natural-number powers,
[`Filter.Germ.isReduced_iff_eventually`](MinimalPrimes/Order/Filter/Germ/Reduced.lean)
characterizes reducedness of `Germ D M` by eventual reducedness of `M`.
Equivalently, `D = ⊥` or `M` is reduced. No power laws or properness assumption
are needed. The same module characterizes nilpotence by one exponent whose
power is zero eventually, and supplies reducedness for germs of reduced values.

### Nontrivial dependent reduced products

For an arbitrary filter `D` and an independently universed dependent type family `R`,
[`Filter.Product.nontrivial_iff`](MinimalPrimes/Order/Filter/Product/Nontrivial.lean)
characterizes nontriviality of the existing total-section product by
`Nonempty (∀ i, R i)` and frequent nontriviality of the fibres. No algebraic,
fibre-inhabitation or proper-filter hypothesis is required. The section condition is
essential: an empty fibre outside the filter's support still makes the product empty.
The same module gives nonemptiness and subsingleton criteria, and the constant-family
characterization for `Filter.Germ`. The
[varying-fibre clients](MinimalPrimesTest/FilterProductNontrivial.lean) contrast a
trivial default fibre with an empty off-support fibre.

### Reduced ranges of iterated Frobenius

For a commutative semiring of exponential characteristic `p`, the original image
of the `n`th Frobenius iterate is reduced exactly when every nilpotent element
has zero `p ^ n`th power. If the semiring is Noetherian and `p` is prime,
all sufficiently high iterates have reduced images. The
[reduced-image API](MinimalPrimes/RingTheory/Frobenius/Reduced.lean) also gives the
corresponding original subring-range statement for a given commutative ring.
No field, perfectness, or reducedness of the ambient semiring is assumed.

### No zero divisors in ultrafilter products

For an ultrafilter `U` and an independently universed dependent family `R`,
[`Filter.Product.noZeroDivisors_iff_eventually`](MinimalPrimes/Order/Filter/Product/NoZeroDivisors.lean)
characterizes no zero divisors in the product by eventual no zero divisors in the
fibres. It requires only `Zero` and `Mul` on each fibre and uses the existing
`Con.hasMul` and `Con.zero` operations on the existing product carrier. No
associativity, unit, absorption by zero, addition, commutativity or nontriviality
hypothesis is needed. For monoids with zero,
`Filter.Product.noZeroDivisors_iff` uses the canonical product instances; the
operation-agreement lemmas identify the same zero and multiplication.
The [varying finite client](MinimalPrimesTest/Order/Filter/Product/NoZeroDivisors.lean)
has no zero divisors even though zero is not absorbing.

The [constant-family bridge](MinimalPrimes/Order/Filter/Germ/NoZeroDivisors.lean)
compares the congruence zero and multiplication records with the existing germ
operations for every filter. At an ultrafilter, `Filter.Germ.noZeroDivisors_iff`
therefore characterizes no zero divisors in the germ by no zero divisors in the
value type, still with only `Zero` and `Mul`. The same nonabsorbing client exercises
this specialization. These generic criteria are Mathlib-upstream candidates.

The ultrafilter hypothesis is essential: at the proper top filter on a two-point
index type, complementary nonzero sections over a domain multiply to zero.

### Reduced dependent filter products

For an arbitrary filter and an independently universed dependent family of
monoids with zero, the filter product is reduced exactly when its reduced
fibres form a member of the filter. The
[criterion](MinimalPrimes/Order/Filter/Product/Reduced.lean) uses a uniform
square-zero test, not an exchange of a varying nilpotence exponent with
eventual equality. A representative is nilpotent exactly when one uniform
natural-number exponent makes its power zero eventually; the exponent may be
zero. No addition, commutativity, proper-filter or nontriviality hypothesis is
needed.

If the filter contains a finite set, nilpotence of a represented section is
also equivalent to eventual fibrewise nilpotence, by
[`Filter.Product.isNilpotent_coe_iff_of_finite_mem`](MinimalPrimes/Order/Filter/Product/Reduced.lean).
The whole index type need not be finite. The same module gives finite-index
and finite-principal criteria; the latter tests exactly the values on the
generating set, including the empty set. These results reuse the
[finite-member exponent bound](MinimalPrimes/Order/Filter/Product/Nilpotent.lean).
For **monoid-with-zero coefficients**, the
[constant-germ specialization](MinimalPrimes/Order/Filter/Germ/Reduced.lean)
uses the existing germ zero and power operations; the earlier germ results
still need only zero and natural-number powers. The
[dependent client](MinimalPrimesTest/Order/Filter/Product/Nilpotent.lean) gives
a nonzero nilpotent quotient element on an infinite index type with varying
nonadditive fibres.

### Regular elements of dependent filter products

For an arbitrary filter `D` and an independently universed family `K` with only
fibrewise multiplication, a total section represents a left-regular, right-regular,
or regular element of `D.Product K` exactly when its values have that property
eventually. The [criteria](MinimalPrimes/Order/Filter/Product/Regular.lean) require
neither associativity, an identity, nor a proper filter. The existing
[Germ criteria](MinimalPrimes/Order/Filter/Germ/Regular.lean) are their constant-family
specializations. The [varying finite example](MinimalPrimesTest/Order/Filter/Product/Regular.lean)
separates left and right regularity in noncommutative magmas with no identity.

### Other headline results

The following interfaces are implemented in this library. See the [reader guide](docs/Guide.md)
and the linked module documentation for statements, examples, proof ideas and Mathlib dependencies.

- **All ideals of products and standard filters**
  ([module](MinimalPrimes/RingTheory/Ideal/PiFilter.lean)). For a dependent family
  `K : ι → Type v` of division semirings, `Ideal.piOrderIsoFilter K` identifies
  `Ideal (Π i, K i)` with the order dual of `Filter ι`; in particular it applies
  to semifields. Its characteristic law is
  `{i | f i = 0} ∈ I.piFilter K ↔ f ∈ I`. Both constructors already work for
  semirings, but division is used to recover every ideal. The improper filter
  gives the whole ideal, a principal filter gives functions vanishing on its
  generating set, and the cofinite filter gives finite support. The API includes
  germ kernels, singly generated ideals, and compatibility with Mathlib's finite
  coordinate-ideal classification. Index and factor universes are independent;
  empty products are included without a nontrivial-product assumption.
  For arbitrary semiring fibres, coordinate ideals `I i` and a filter `D`,
  `Filter.pi_sup_piIdeal_eq_top_iff` says that `Ideal.pi I ⊔ D.piIdeal R` is
  the whole ideal exactly when `{i | I i = ⊤} ∈ D`. The properness criterion
  `Filter.pi_sup_piIdeal_ne_top_iff` is nonmembership of this set, not membership
  of its complement unless `D` is an ultrafilter. Zero fibres and improper
  filters are allowed.
  ([examples](MinimalPrimesTest/RingTheory/Ideal/PiFilter.lean)).
- **Ultrafilter coordinate-locus criteria**
  ([module](MinimalPrimes/RingTheory/Ideal/PrimePiUltrafilter.lean)). For dependent
  semirings `R i` and left ideals `I i`, `Ultrafilter.isPrime_pi_sup_piIdeal_iff`
  and `Ultrafilter.isMaximal_pi_sup_piIdeal_iff` characterize the sum
  `Ideal.pi I ⊔ (U : Filter ι).piIdeal R` as prime or maximal exactly when the
  respective coordinate locus belongs to `U`. The criteria need no commutativity,
  nontrivial-factor or subtractivity assumption.
- **Prime ideals of arbitrary products of semifields**
  ([module](MinimalPrimes/RingTheory/Ideal/PrimePiUltrafilter.lean)). For any dependent
  family `K : ι → Type v` of semifields, `PrimeSpectrum.piEquivUltrafilter K`
  identifies every prime ideal of `Π i, K i` with an ultrafilter on `ι`.
  A function belongs to the ideal for `U` exactly when `{i | f i = 0} ∈ U`.
  Already for **division-semiring** fibres, `Ultrafilter.piIdeal_isMaximal` makes
  every such ultrafilter zero-set ideal maximal, via the ideal/filter order isomorphism.
  The index universe is independent of `v`, and no additive cancellation, ring,
  finite-index or nonempty-index hypothesis is imposed. The forward ideal construction
  works already for semiring factors, with evaluation-kernel and constant-family
  germ-kernel bridges. Finite products have uniquely labelled coordinate kernels;
  the cofinite ultrafilter gives non-coordinate primes on infinite index types.
  The [topological extension](MinimalPrimes/RingTheory/Spectrum/Prime/PiUltrafilter.lean)
  `PrimeSpectrum.piHomeomorphUltrafilter K` retains this exact equivalence as a
  homeomorphism for the Zariski and existing Stone topologies. Its basis pullback
  laws use the nonzero locus and the function one on a subset and zero off it.
  Coordinate primes are dense, even when non-coordinate primes occur; the topology
  is not in general discrete. For an arbitrary index map `g : κ → ι` and fibrewise
  semifield homomorphisms `φ j : K (g j) →+* L j`, spectral pullback along the stock
  product homomorphism corresponds to `Ultrafilter.map g`. The API includes the
  inverse square, index precomposition and same-index family-map specializations;
  the index and fibre universes are independent, with no injectivity or finiteness assumption.
- **Residue fields of dependent products of fields**
  ([module](MinimalPrimes/RingTheory/Ideal/ResidueFieldPiUltrafilter.lean)). For a
  dependent family `K : ι → Type v` of fields and `U : Ultrafilter ι`,
  `Ultrafilter.residueFieldProductEquiv K U` canonically identifies
  `(U.piIdeal K).ResidueField` with the existing `(U : Filter ι).Product K`.
  This is a ring equivalence over the section ring `R = Π i, K i`: for **every
  section** `r`, it sends `algebraMap R (U.piIdeal K).ResidueField r` to the
  reduced-product class of `r`. The API includes the inverse equation, uniqueness
  from this property and its equality-of-homomorphisms form. Fibrewise field
  homomorphisms give a commuting square with `Ideal.ResidueField.map` and
  `Filter.Product.mapRingHom`. Index and fibre universes are independent; no
  common characteristic, finite-index or nonempty-index hypothesis, or global
  field instance on the Product, is required. The
  [examples](MinimalPrimesTest/ResidueFieldPiUltrafilter.lean) check the principal
  coordinate kernel and a dependent `ZMod 2`/`ZMod 3` family with distinct residue
  characteristics and opposite-characteristic nonzero controls.
- **Minimal primes of finite products**
  ([module](MinimalPrimes/RingTheory/Ideal/MinimalPrimePi.lean)). For commutative
  semirings `R i` and a finite index type, `Ideal.mem_minimalPrimes_pi_iff`
  identifies minimal primes over any ideal of the product with unique labelled coordinate
  minimal primes. `Ideal.minimalPrimesPiEquiv` gives the corresponding equivalence
  with the dependent sum of the minimal primes over `Ideal.piOrderIso I i`.
  Its inverse is evaluation comap, with forward/comap and evaluation-image laws.
  The transport theorem `Ideal.comap_eval_mem_minimalPrimes_iff` works even for
  infinite index types; it does not classify all primes of an infinite product.
  No nonempty-index, nontrivial-factor, proper-base-ideal or ring assumptions
  are needed. Equal factors retain distinct coordinate labels.
- **Minimal primes and radical membership detected by localization**
  ([module](MinimalPrimes/RingTheory/Ideal/MinimalPrimeLocalization.lean)).
  In a commutative semiring `R`, an element belongs to `I.radical` exactly when its
  canonical image belongs to the radical of the extension of `I` in
  `Localization.AtPrime q` for every minimal prime `q` over `I`
  (`Ideal.mem_radical_iff_forall_minimalPrimes_localization`). The unit ideal is included.
  The [natural-number client](MinimalPrimesTest/RingTheory/Ideal/MinimalPrimeLocalization.lean)
  shows that `2` passes these tests for `(4)` despite not belonging to `(4)`, while `1` fails.
  For commutative semirings `R`, `A` with `[Algebra R A]`, a prime ideal `q`
  and `[IsLocalization.AtPrime A q]`, any ideal `I` also satisfies
  `(I.map (algebraMap R A)).radical = q.map (algebraMap R A)` iff `q ∈ I.minimalPrimes`.
  No separate `I ≤ q` is needed. Mathlib supplies the implication from minimality.
- **Multipliers outside a minimal prime** ([module](MinimalPrimes/RingTheory/Ideal/MinimalPrimeMultipliers.lean)).
  For ideals `I`, `q` in a commutative semiring, `q ∈ I.minimalPrimes` and `x ∈ q`
  imply `∃ s ∉ q, s * x ∈ I.radical`. Over the zero ideal, the product is nilpotent.
- **Ideal contraction and positive powers in the image**
  ([ideals](MinimalPrimes/RingTheory/Ideal/PositivePowerRange.lean),
  [prime spectra](MinimalPrimes/RingTheory/Spectrum/Prime/PositivePowerRange.lean)).
  For a homomorphism from a semiring `R` to a commutative semiring `S`, suppose
  every `x : S` has some positive power in `Set.range f`. Then
  `I.comap f ≤ J.comap f ↔ I ≤ J` for arbitrary `I` and radical `J`.
  For every target ideal `I`,
  `Ideal.radical_map_comap_of_pos_pow_mem_range` also gives
  `(Ideal.map f (Ideal.comap f I)).radical = I.radical`.
  The map may have any type with `FunLike` and `RingHomClass` instances, in an
  independent universe. No surjectivity, uniform exponent or radicality of `I`
  is assumed. For commutative semirings on both sides and a bundled homomorphism,
  `PrimeSpectrum.isEmbedding_comap_of_pos_pow_mem_range` proves that the existing
  `PrimeSpectrum.comap f` is a topological embedding, with independent source and
  target universes. Its image need not be closed or the whole spectrum.
- **Dimension under field extension.** For fields `K` and `L`, a given
  `[Algebra K L]`, and a commutative `K`-algebra `A` with
  `[Algebra.FiniteType K A]`, the
  [field-extension leaf](MinimalPrimes/RingTheory/KrullDimension/FieldExtension.lean)
  proves `Algebra.ringKrullDim_tensorProduct_of_finiteType`:
  `ringKrullDim (A ⊗[K] L) = ringKrullDim A`. All three types may lie in
  independent universes. The extension need not be algebraic, and `A` need not
  be a domain, reduced or nontrivial. Dimension takes values in `WithBot ℕ∞`;
  the zero algebra has dimension `⊥`.
- **Dimension under integral maps** ([module](MinimalPrimes/RingTheory/KrullDimension/Integral.lean)).
  For integral maps `f : R →+* S` of commutative rings, target Krull dimension is
  at most source dimension, with equality if `f` is injective. Without injectivity,
  `ringKrullDim S = ringKrullDim (R ⧸ RingHom.ker f)`. A faithful integral algebra
  has equal source and target dimensions using its given algebra structure.
  Dimensions lie in `WithBot ℕ∞`, including zero rings and infinite dimension.
- **When a prime localization is a field** ([module](MinimalPrimes/RingTheory/Localization/AtPrime.lean)).
  For commutative semirings `R`, `A` with their given `R`-algebra structure,
  any prime `q` and `[IsLocalization.AtPrime A q]` satisfy
  `IsField A ↔ q ∈ minimalPrimes R ∧ IsReduced A`.
  Reducedness of `R` gives the reduced-base corollary: arbitrary localization
  preserves reducedness. For semirings `IsField` includes semifields.
- **Principal prime witnesses and contraction** ([module](MinimalPrimes/Principal.lean)).
  In a commutative semiring, a proper principal ideal avoids at least one of two
  relatively prime (`IsRelPrime`) elements.
  In a commutative semiring with unique factorization, every nonunit, including
  zero, belongs to a principal prime ideal with this disjunctive avoidance.
  No normalization or nonzero assumption is needed. Contraction from any semiring
  gives a prime two-sided source ideal, not necessarily a principal ideal.
- **Minimal primes of a principal ideal** ([module](MinimalPrimes/Principal.lean)).
  For `[CommSemiring R]`, `[UniqueFactorizationMonoid R]`, the caller's
  `[NormalizationMonoid R]` and `f ≠ 0`, the minimal primes over `(f)` are exactly
  the principal ideals generated by normalized irreducible factor values.
  Their factor equivalence sends `p` to `span {p}`; multiplicities do not add primes.
- **Irreducible components of a principal zero locus** ([module](MinimalPrimes/IrreducibleComponents.lean)).
  Under those same semiring, factorization, normalization and nonzero hypotheses,
  the factor values are equivalent to the **order-dual subtype** of irreducible
  components of the subspace `V((f))` in `PrimeSpectrum R`. This is an `Equiv`,
  not an order-equivalence or homeomorphism, and does not classify arbitrary ideals.
- **Associated primes of a principal quotient** ([module](MinimalPrimes/AssociatedPrincipal.lean)).
  For every `f` in a commutative ring with unique factorization,
  `associatedPrimes R (R ⧸ Ideal.span {f}) = (Ideal.span {f}).minimalPrimes`,
  using base-ring `R` scalars. No normalization, nonzero or Noetherian hypothesis
  is needed; the zero ring is included.
- **Scalar restriction and quotient points** ([scalar restriction](MinimalPrimes/AssociatedRestrictScalars.lean),
  [quotients](MinimalPrimes/AssociatedPrincipal.lean)). Colon ideals of arbitrary
  submodules contract under compatible algebra/module towers with commutative
  source and semiring target. Associated primes of a compatible module contract
  along algebra maps of commutative semirings and reflect along surjective ones.
  For every principal quotient
  of a commutative ring with unique factorization, quotient-spectrum associated
  points and exact singleton-annihilator criteria correspond by ideal comap to
  minimal primes over the generator.
- **Height of a principal prime** ([module](MinimalPrimes/RingTheory/Ideal/PrincipalPrimeHeight.lean)).
  In a commutative ring with `[WfDvdMonoid R]` and `Prime p`, `span {p}` has height
  at most one. Its height is one if `p ∈ nonZeroDivisors R`, in particular in a domain.
  This uses well-founded strict divisibility, not a Noetherian or UFM assumption,
  and concerns prime generators, not arbitrary principal ideals.
- **Descending prime chains at finite initial height**
  ([order](MinimalPrimes/Order/FiniteHeightChain.lean), [prime chains](MinimalPrimes/RingTheory/Ideal/FiniteHeightChain.lean)).
  In a preorder, finite ambient height of `x` makes the strict order on `Set.Iic x`
  well-founded. An antitone spectrum sequence over a commutative semiring with
  finite initial ambient height stabilizes. So does an antitone ideal sequence
  over a commutative ring when **every term is prime** and the initial ideal has
  `Ideal.FiniteHeight`. One common index gives both tail constancy and the
  **all-index** ideal infimum; no global dimension or chain-condition hypothesis
  is added. Spectrum height is not height in the full lattice of ideals.
- **Zero-dimensional Zariski spectra** ([module](MinimalPrimes/RingTheory/Spectrum/Prime/ZeroDimensional.lean)).
  For any commutative semiring, T₁ and Hausdorffness of `PrimeSpectrum R` are each
  equivalent to `Ring.KrullDimLE 0 R`, including the empty spectrum; under this
  bound all basic opens are clopen. Mathlib supplies total separation and total
  disconnectedness from the Hausdorff spectrum. For a **reduced, nontrivial
  commutative ring**, this bound and preconnectedness of its spectrum imply `IsField R`.

### Non-zero-divisor loci of germs

For an arbitrary filter `D` and a monoid with zero `M`, the
[non-zero-divisor criteria](MinimalPrimes/Order/Filter/Germ/NonZeroDivisors.lean)
identify intrinsic left, right and two-sided non-zero-divisors of `Filter.Germ D M`
with eventual coordinate membership in the corresponding submonoids of `M`.
The index and coefficient universes are independent; improper filters, empty indices
and trivial monoids are included. These are zero-annihilator criteria, not full
multiplicative cancellation criteria. The generic API is a Mathlib-upstream candidate.

### Topological dimension on open covers

The [open-cover leaf](MinimalPrimes/Topology/KrullDimension/OpenCover.lean) proves
`topologicalKrullDim_eq_iSup_of_isOpenEmbedding_cover`: the dimension of a space is
the supremum of the dimensions of any jointly surjective family of open-embedding
charts, with independent universes for the space, index type and chart domains.
Its open-subspace form, `topologicalKrullDim_eq_iSup_of_isOpen_cover`, applies to
any family of open sets whose union is the whole space, with their induced topologies.
Both equalities use `WithBot ℕ∞`, including bottom for an empty-index cover of the
empty space and infinite or unbounded dimensions. No separation, sobriety,
Noetherianity, quasi-compactness, finiteness or nonemptiness assumption is needed.

## Using the library

Add the public library to your `lakefile.toml`:

```toml
[[require]]
name = "minimal-primes"
git = "https://github.com/FormalFrontier/minimal-primes.git"
rev = "main"
```

GitHub `main` contains reviewed releases. Lake resolves a release when you first add
or update the dependency; `lake-manifest.json` retains that commit until the next
update. To pin a specific release, replace `main` with a commit from that history.
Use the compatible toolchain and dependency versions recorded by that release.

```lean
import MinimalPrimes
```

Import a leaf from [Contents](#contents) for a smaller API. The following
**illustrative Lean snippet**
uses the exported integer normalization instance. Maintained integer examples
are in [`MinimalPrimes/PrincipalExamples/Algebra.lean`](MinimalPrimes/PrincipalExamples/Algebra.lean).

```lean
/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import MinimalPrimes.Principal
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.RingTheory.PrincipalIdealDomain

/-! # README examples: integers with their exported normalization -/

open UniqueFactorizationMonoid

noncomputable section

private theorem readme_integerClassification {f : ℤ} (hf : f ≠ 0) :
    (Ideal.span {f}).minimalPrimes =
      {P | ∃ p ∈ normalizedFactors f, P = Ideal.span {p}} :=
  Ideal.minimalPrimes_span_singleton_eq_normalizedFactors hf

private def readme_integerMinimalPrimes {f : ℤ} (hf : f ≠ 0) :
    {p // p ∈ normalizedFactors f} ≃ (Ideal.span {f}).minimalPrimes :=
  Ideal.normalizedFactorsEquivMinimalPrimes hf
```

## Public API and examples

The [reader guide](docs/Guide.md#public-api-and-examples) contains the declaration
table, all four complete examples, generic normalization choices and boundary cases.
For a concrete nonring semiring, [`NatSix.lean`](MinimalPrimesTest/NatSix.lean)
classifies the minimal primes over `(6)` in `ℕ` as exactly `(2)` and `(3)`.
The [API snapshot](docs/API.md), [input manifest](docs/api-manifest.json) and
[reproduction instructions](docs/README.md) describe an older selection of four
normalized-factor declarations and nine modules, not the complete current API.

### Dependent reduced products

[`Order/Filter/Product.lean`](MinimalPrimes/Order/Filter/Product.lean) equips the existing
`Filter.Product F K` with pointwise monoid operations for arbitrary filters and dependent
monoid fibres in an independent universe. `Filter.productCon F K` uses the stock
`Filter.productSetoid`, and `Filter.Product.coeMulHom F` is the section projection.
Monoid-with-zero and semiring fibres give the corresponding quotient structures.
`Filter.productRingCon F K` extends the same congruence, so `RingCon.mk'`, its
surjectivity/equality API, and `RingCon.lift` with its computation and uniqueness laws
apply directly. Fibrewise homomorphisms descend through `Filter.Product.mapRingHom`,
preserving identity and composition. For constant families the section homomorphisms
are the existing `Filter.Germ.coeMulHom` and `Filter.Germ.coeRingHom`.

[`Product/Units.lean`](MinimalPrimes/Order/Filter/Product/Units.lean) proves
`Filter.Product.isUnit_coe_iff`: a represented element is a unit exactly when its
section is a unit on a filter-large set. Only monoid fibres are required, with no
commutativity, properness or nontriviality assumptions. Bottom filters, empty indices
and trivial fibres are included. `Filter.Product.units_map_coeMulHom_surjective`
states that every quotient unit has an everywhere-unit section representative.
`Filter.Product.associated_coe_iff` characterizes right-unit association of represented
elements by eventual right-unit association of their values: the witness multiplies
on the right, `f i * u = g i`. This criterion has the same monoid-only hypotheses.
The corresponding `Filter.Germ.isUnit_coe_iff` and
`Filter.Germ.units_map_coeMulHom_surjective` remain constant-family specializations;
the germ units equivalence and its projection laws are unchanged.
The [dependent-product examples](MinimalPrimesTest/Order/Filter/Product.lean) use
varying noncommutative endomorphism monoids to contrast identity and nonunit sections,
and the same section at the top and bottom filters. They also check that distinct
constant endomorphisms are not right-unit associated at the top filter, while the
bottom filter forgets that distinction.

The quotient is trivial exactly when `{i | (0 : K i) = 1}` belongs to the filter.
Thus nontrivial fibres and a proper filter give a nontrivial quotient, whereas the
improper quotient is trivial. The top-filter section map is bijective, including for
an empty index. `Filter.Product.principalRingEquiv` identifies the principal-filter
quotient with sections on the generating set. Restriction is unital; extension by zero
is only the surjectivity witness. Ultrafilter products of division semirings and
semifields inherit those structures with pointwise inversion, without assuming fields.

For example, on a two-point index take `K 0 = ℚ≥0` and `K 1 = ℝ≥0`.
These are semifields, not fields with their usual operations. At the principal filter
generated by `{1}` (the pure filter at `1`), the restriction comparison is `q(f) ↦ f 1` into `ℝ≥0`.
At the top filter the quotient instead retains the full dependent product: the
nonzero sections `(1, 0)` and `(0, 1)` multiply to zero. Thus the ultrafilter hypothesis
for the division structure is essential even in this nonring example.

`Filter.piIdeal_eq_ker_productMk` and `Ultrafilter.piIdeal_eq_ker_productMk` identify the
kernel with the existing zero-set ideals, retaining the constant-germ kernel results.
No semiring ideal-quotient isomorphism is asserted. The generic Product API is a
Mathlib-upstream candidate; these ideal bridges remain specific to this library.

### Varying application on germs

[`Order/Filter/Germ/Map.lean`](MinimalPrimes/Order/Filter/Germ/Map.lean) proves
`Filter.Germ.injective_map₂_apply_coe_iff`: the existing `Germ.map₂` specialized to
evaluation by a family `F : ι → A → B` is injective exactly when `F i` is injective
eventually. Index, domain and codomain universes are independent. No algebra,
proper-filter or inhabitedness assumption is imposed, including at empty types.
The [cofinite-sequence example](MinimalPrimesTest/Order/Filter/Germ/Map.lean)
uses a constant-zero map at index zero and `k ↦ n + k` at positive indices: the
induced germ action is injective despite its noninjective zero fibre.
This generic criterion is a Mathlib-upstream candidate.

### Intrinsic centers of filter germs

[`Order/Filter/Germ/Center.lean`](MinimalPrimes/Order/Filter/Germ/Center.lean) proves
`Filter.Germ.mem_center_coe_iff` at `Mul`: a represented germ belongs to the existing
magma center exactly when its values are central eventually. All three
`IsMulCentral` fields are retained, not only commutation. The companion
`mem_submonoid_center_coe_iff` needs only `MulOneClass`, not associativity.
The filter is arbitrary and the index and codomain universes are independent;
no properness or inhabitedness assumptions are added. At `MulOneClass`,
`Filter.Germ.centerEquiv` identifies germs of center-valued functions with central
germs, and `centerRepresentative` lifts a central germ to a total center-valued
function agreeing with any supplied representative eventually.
The [single finite client](MinimalPrimesTest/Order/Filter/Germ/Center.lean) uses a
noncommutative, nonassociative multiplication and a genuinely varying central germ
with an ignored noncentral fibre. Its total central lift preserves the two
retained values but cannot agree everywhere with the original function.
See the [center guide](docs/FilterGermCenter.md)
for the interface and proof idea. This generic API is a Mathlib-upstream candidate.

## Build and audit

The toolchain is pinned in `lean-toolchain`; `lake-manifest.json` records the complete
dependency graph. Obtain the matching Mathlib cache before building:

```sh
lake exe cache get
```

Build the default production and test targets, including the maintained example modules:

```sh
lake build
```

See the [build and audit guide](docs/Guide.md#build-and-audit) for focused module
commands, maintained examples and transitive-axiom coverage and limitations.
The allowed transitive axioms are `propext`, `Classical.choice` and `Quot.sound`.

## Contents

`MinimalPrimes` re-exports all production leaves.

| Module | Contents |
| --- | --- |
| [`MinimalPrimes.Principal`](MinimalPrimes/Principal.lean) | Principal prime witnesses and normalized-factor classification. |
| [`MinimalPrimes.IrreducibleComponents`](MinimalPrimes/IrreducibleComponents.lean) | Factor equivalence with order-dual components of a principal zero locus. |
| [`MinimalPrimes.AssociatedRestrictScalars`](MinimalPrimes/AssociatedRestrictScalars.lean) | Colon contraction and associated-prime transport. |
| [`MinimalPrimes.AssociatedPrincipal`](MinimalPrimes/AssociatedPrincipal.lean) | Base-ring and quotient-spectrum comparisons; exact annihilators. |
| [`MinimalPrimes.Order.FiniteHeightChain`](MinimalPrimes/Order/FiniteHeightChain.lean) | Well-founded lower intervals at finite ambient height. |
| [`MinimalPrimes.Order.Filter.Basic`](MinimalPrimes/Order/Filter/Basic.lean) | Sort-general section reflection and comparison of filters on fibres with distinct values. |
| [`MinimalPrimes.Order.Filter.Product`](MinimalPrimes/Order/Filter/Product.lean) | Section-setoid comparison on nontrivial fibres and algebra on dependent reduced products. |
| [`MinimalPrimes.Order.Filter.Product.CompTendsto`](MinimalPrimes/Order/Filter/Product/CompTendsto.lean) | Dependent index pullback, full injectivity criterion, equivalence-index surjectivity and two-way reindexing equivalence. |
| [`MinimalPrimes.Order.Filter.Germ.Map`](MinimalPrimes/Order/Filter/Germ/Map.lean) | Varying germ application is injective exactly for eventually injective fibre maps. |
| [`MinimalPrimes.Order.Filter.Germ.NonZeroDivisors`](MinimalPrimes/Order/Filter/Germ/NonZeroDivisors.lean) | Left, right and two-sided non-zero-divisor membership is equivalent to eventual coordinate membership. |
| [`MinimalPrimes.Order.Filter.Germ.Reduced`](MinimalPrimes/Order/Filter/Germ/Reduced.lean) | Nilpotence and reducedness with only zero and natural-number powers; finite-member eventual nilpotence for monoid-with-zero coefficients. |
| [`MinimalPrimes.Order.Filter.Product.Map`](MinimalPrimes/Order/Filter/Product/Map.lean) | Canonical coordinate maps with representative/identity/composition/uniqueness and exact onto laws; selected-section and Zero-only reflection. |
| [`MinimalPrimes.Order.Filter.Germ.NoZeroDivisors`](MinimalPrimes/Order/Filter/Germ/NoZeroDivisors.lean) | Weak-data comparison with constant products and no zero divisors in ultrafilter germs exactly for no-zero-divisor coefficients. |
| [`MinimalPrimes.Order.Filter.Product.NoZeroDivisors`](MinimalPrimes/Order/Filter/Product/NoZeroDivisors.lean) | No zero divisors in ultrafilter products exactly for eventually no-zero-divisor fibres, with only zero and multiplication. |
| [`MinimalPrimes.Order.Filter.Product.Nilpotent`](MinimalPrimes/Order/Filter/Product/Nilpotent.lean) | A uniform vanishing exponent for eventually nilpotent dependent sections when the filter contains a finite set. |
| [`MinimalPrimes.Order.Filter.Product.Reduced`](MinimalPrimes/Order/Filter/Product/Reduced.lean) | Reducedness by the reduced-fibre locus; uniform-exponent nilpotence and finite-member, finite-index and finite-principal nilpotence criteria. |
| [`MinimalPrimes.Order.Filter.Germ.Regular`](MinimalPrimes/Order/Filter/Germ/Regular.lean) | Constant-family specializations of eventual regularity. |
| [`MinimalPrimes.Order.Filter.Product.Regular`](MinimalPrimes/Order/Filter/Product/Regular.lean) | Left, right and two-sided regularity at fibrewise multiplication, characterized by eventual regularity. |
| [`MinimalPrimes.Order.Filter.Product.Center`](MinimalPrimes/Order/Filter/Product/Center.lean) | Full intrinsic centers at fibrewise multiplication; the equivalence of fibre-center products and product centers needs only two-sided identities. |
| [`MinimalPrimes.RingTheory.Ideal.FiniteHeightChain`](MinimalPrimes/RingTheory/Ideal/FiniteHeightChain.lean) | Stabilizing prime chains and their all-index infima. |
| [`MinimalPrimes.RingTheory.Ideal.PrincipalPrimeHeight`](MinimalPrimes/RingTheory/Ideal/PrincipalPrimeHeight.lean) | Height bound and regular/domain equalities for prime generators. |
| [`MinimalPrimes.RingTheory.Ideal.MinimalPrimeMultipliers`](MinimalPrimes/RingTheory/Ideal/MinimalPrimeMultipliers.lean) | Multipliers outside a minimal prime into a radical. |
| [`MinimalPrimes.RingTheory.Ideal.MinimalPrimeLocalization`](MinimalPrimes/RingTheory/Ideal/MinimalPrimeLocalization.lean) | Minimality and radical membership detected by localization. |
| [`MinimalPrimes.RingTheory.Ideal.PrimePiUltrafilter`](MinimalPrimes/RingTheory/Ideal/PrimePiUltrafilter.lean) | Maximal ultrafilter ideals for division semirings; prime ideals of dependent products of semifields classified by ultrafilters. |
| [`MinimalPrimes.RingTheory.Ideal.ResidueFieldPiUltrafilter`](MinimalPrimes/RingTheory/Ideal/ResidueFieldPiUltrafilter.lean) | Canonical residue-field/dependent-Product comparison over the section ring, with characteristic equations, uniqueness and fibrewise naturality. |
| [`MinimalPrimes.RingTheory.Ideal.PositivePowerRange`](MinimalPrimes/RingTheory/Ideal/PositivePowerRange.lean) | Contraction reflects containment in radical ideals, and extension–contraction preserves radicals, when positive powers lie in the image. |
| [`MinimalPrimes.RingTheory.KrullDimension.Integral`](MinimalPrimes/RingTheory/KrullDimension/Integral.lean) | Integral-map dimension bound, injective equality, kernel quotient and faithful algebra. |
| [`MinimalPrimes.RingTheory.KrullDimension.FieldExtension`](MinimalPrimes/RingTheory/KrullDimension/FieldExtension.lean) | Dimension preserved under base-field extension for finite-type commutative algebras. |
| [`MinimalPrimes.RingTheory.Localization.AtPrime`](MinimalPrimes/RingTheory/Localization/AtPrime.lean) | Field criterion for prime localizations. |
| [`MinimalPrimes.RingTheory.Localization.Reduced`](MinimalPrimes/RingTheory/Localization/Reduced.lean) | Reducedness preserved by localization. |
| [`MinimalPrimes.RingTheory.RingHom.ULift`](MinimalPrimes/RingTheory/RingHom/ULift.lean) | Finite type preserved and reflected by canonical universe lifting of commutative-ring homomorphisms. |
| [`MinimalPrimes.RingTheory.Spectrum.Prime.PiUltrafilter`](MinimalPrimes/RingTheory/Spectrum/Prime/PiUltrafilter.lean) | Stone homeomorphism for arbitrary dependent products of semifields, basis transport and dense coordinate primes. |
| [`MinimalPrimes.RingTheory.Spectrum.Prime.ZeroDimensional`](MinimalPrimes/RingTheory/Spectrum/Prime/ZeroDimensional.lean) | Clopen basis, separation equivalences and the preconnected field criterion. |
| [`MinimalPrimes.RingTheory.Spectrum.Prime.PositivePowerRange`](MinimalPrimes/RingTheory/Spectrum/Prime/PositivePowerRange.lean) | Injectivity and topological embedding of spectrum pullback from the positive-power criterion. |
| [`MinimalPrimes.Topology.KrullDimension.OpenCover`](MinimalPrimes/Topology/KrullDimension/OpenCover.lean) | Topological dimension on open covers. |

## Conventions and limitations

- Results are universe-polymorphic; localization and integral-map results allow
  independent source and target universes. No implicit domain, Noetherian, finite-
  dimension or nontriviality assumption is added to the statements above.
- The normalized-factor interfaces use the caller's normalization data. Changing it
  can change the factor subtype; no equality of differently normalized subtypes is
  asserted. Both factor equivalences are noncomputable. Nonzero units give empty
  factor and minimal-prime sets; the excluded zero generator has no normalized factors.
- Principal quotients use the stated scalar ring: an `R`-module comparison is not a
  change to quotient-ring scalars. Localization at `(2)` in `ℤ` is not `ℤ / 2ℤ`;
  reducedness of the target in the field criterion cannot be dropped.
- All spectrum topology here is Zariski. Separation equivalences do not create reverse
  typeclass instances. Dimension uses `WithBot ℕ∞`: the zero ring has dimension bottom,
  so the zero-dimensional results use `Ring.KrullDimLE 0 R`, not equality with zero.
- The [guide](docs/Guide.md) gives integral-dimension models, full hypotheses and proof
  explanations; the finite-height infinite-variable discussion distinguishes checked
  clients from a mathematical sketch. Infinite Krull dimension alone is not a
  non-Noetherianity certificate.

## References

- The finite-member nilpotence criteria compose the dependent-product and
  constant-germ uniform-exponent APIs with Mathlib's `nilpotencyClass`, upward
  propagation of zero powers and finite-set order bounds; see the
  [bound module](MinimalPrimes/Order/Filter/Product/Nilpotent.lean) and
  [CREDITS.md](CREDITS.md).
- The germ non-zero-divisor criteria use Mathlib's filter-germ, filter witness-selection
  and monoid-with-zero non-zero-divisor APIs; see the module's references and
  [CREDITS.md](CREDITS.md).
- Mathlib's factorization, ideal, spectrum, localization and dimension APIs; exact
  pinned module references and the related `SchemeProperties` ring formulations
  are in the [guide](docs/Guide.md#references).
- The dependent-product residue comparison reuses Mathlib's
  [filter germs and dependent Product](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/Order/Filter/Germ/Basic.lean),
  [ultraproduct inversion](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/Order/Filter/FilterProduct.lean),
  [quotient first-isomorphism theorem](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/RingTheory/Ideal/Quotient/Operations.lean)
  and [ideal residue-field maps](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/RingTheory/LocalRing/ResidueField/Ideal.lean).
  Further algebraic dependencies are listed in the
  [comparison module](MinimalPrimes/RingTheory/Ideal/ResidueFieldPiUltrafilter.lean).
- Ravi Vakil, *Foundations of Algebraic Geometry*, October 21, 2025 draft, Exercise 3.7.H;
  *The Rising Sea*, Exercise 6.6.F: mathematical motivation, not authorship or endorsement.
- Stacks Project, [Tag 00HY](https://stacks.math.columbia.edu/tag/00HY) and
  [Tag 00OW](https://stacks.math.columbia.edu/tag/00OW), through Mathlib.

## Credits and license

Authors: Formal Frontier Agents. This library builds on Mathlib (including Andrew
Yang's minimal-prime and reducedness formalizations) and prior Formal Frontier
approaches. AI agents developed the Lean code and examples. Complete mathematical,
formalization and tool credits are in [CREDITS.md](CREDITS.md).
Original project code is licensed under Apache-2.0; see [LICENSE](LICENSE).
