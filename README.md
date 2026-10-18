# Minimal primes

Reusable Lean theory of prime ideals, associated primes and finite-height prime
chains. The library classifies minimal primes over principal ideals and the
irreducible components of principal zero loci in commutative semirings with unique
factorization, and compares associated primes of principal quotients in commutative
rings with unique factorization. Independently of factorization, finite initial
height gives well-founded lower intervals and stabilization of descending prime chains.
For prime generators in commutative rings with well-founded strict divisibility,
the library bounds the height of the principal ideal by one, with equality for
regular generators and in domains. For arbitrary ideals of commutative semirings,
localization at a prime detects minimality by equality of the localized radical
with the extended prime ideal. For arbitrary commutative semirings, elements
of a minimal prime over an ideal can be multiplied into its radical by a multiplier
outside that same prime.

## Integral homomorphisms and dimension

The [integral-homomorphism leaf](MinimalPrimes/RingTheory/KrullDimension/Integral.lean)
implements `RingHom.IsIntegral.ringKrullDim_eq`: an injective integral map
`f : A →+* B` of commutative rings preserves `ringKrullDim`,
without a domain, Noetherianity, nontriviality, or finite-dimension assumption.
The two rings may lie in independent universes. Dimension takes values in
`WithBot ℕ∞`: the zero ring has dimension bottom, and infinite dimension
is included.

For an arbitrary integral `f : R →+* S`, the kernel-quotient statement
`RingHom.IsIntegral.ringKrullDim_eq_quotient_ker` compares the actual target
with the source modulo its kernel:
`ringKrullDim S = ringKrullDim (R ⧸ RingHom.ker f)`.
The algebra form `Algebra.IsIntegral.ringKrullDim_eq R S` uses the given
`[Algebra R S]`, `[Algebra.IsIntegral R S]` and `[FaithfulSMul R S]` to express
`ringKrullDim R = ringKrullDim S`. Both forms allow independent universes and
the full dimension codomain, with no domain or finiteness restriction.

The upper bound `RingHom.IsIntegral.ringKrullDim_le` needs only integrality:
incomparability makes contraction strictly monotone on prime spectra.
For the reverse inequality, lying-over and Mathlib's going-up chain-lifting
lemma lift each finite strict prime chain without changing its length.
Taking the defining supremum of chain lengths covers infinite dimension and
also the empty spectrum: the supremum of no chains is bottom. No equality
of individual prime heights or going-down hypothesis is used.

The models give the nonsurjective diagonal `ZMod 4 →+* ZMod 4 × ZMod 4`,
with nonzero square-zero elements in both rings; the empty-spectrum boundary;
ring equivalences between independent universe lifts; and the infinite
dimension of `MvPolynomial ℕ ℚ`. Mathlib supplies the product-integrality
witness, ring-equivalence dimension invariance, and polynomial dimension formula.
The proper-diagonal dimension equality is a client of the public general theorem;
the existing model proofs and boundary controls remain separate Mathlib arguments.
The [integer-diagonal clients](MinimalPrimesTest/RingTheory/KrullDimension/Integral.lean)
use the canonical `ℤ →+* ℤ × ℤ`. Finite generation and faithful coordinate
scaling give its hypotheses independently of dimension. Both rings have dimension
one: the product upper bound comes from its principal-ideal-ring structure, and
the lower bound from its first projection. The target is not a domain, and the
diagonal misses `(0, 1)`. The quotient of `ℤ` by its unit ideal has dimension
bottom and total kernel, showing why arbitrary integral maps need the kernel quotient.

## Headline results

- **Minimal primes detected by localization.** The
  [localization leaf](MinimalPrimes/RingTheory/Ideal/MinimalPrimeLocalization.lean)
  proves `IsLocalization.AtPrime.radical_map_eq_iff_mem_minimalPrimes`: for
  `[CommSemiring R]`, `[CommSemiring A]`, `[Algebra R A]`, a prime ideal `q`,
  `[IsLocalization.AtPrime A q]`, and any ideal `I`,
  `(I.map (algebraMap R A)).radical = q.map (algebraMap R A)` if and only if
  `q ∈ I.minimalPrimes`. The two semirings may lie in independent universes.
  There is no separate `I ≤ q` hypothesis: the equality forces containment.
  No ring, Noetherian, reduced, domain or finiteness assumption is needed, and
  no separate nontriviality assumption is added. Mathlib supplies the implication
  from minimality; the converse uses its minimal-prime localization correspondence.
  The [integer client](MinimalPrimesTest/RingTheory/Ideal/MinimalPrimeLocalization.lean)
  applies the criterion to `(4)` in the canonical localization of `ℤ` at `(2)`
  and excludes the unit ideal as a boundary case.
- **Multipliers outside a minimal prime.** The
  [multiplier leaf](MinimalPrimes/RingTheory/Ideal/MinimalPrimeMultipliers.lean)
  proves `Ideal.exists_mul_mem_radical_of_mem_minimalPrimes`: for ideals `I`, `q`
  in any commutative semiring, `q ∈ I.minimalPrimes` and `x ∈ q` imply
  `∃ s ∉ q, s * x ∈ I.radical`. Its zero-ideal specialization,
  `Ideal.exists_isNilpotent_mul_of_mem_minimalPrimes`, gives a nilpotent product.
  Neither theorem needs a ring, Noetherianity, finiteness, reducedness or a
  separate primeness assumption. The
  [examples](MinimalPrimesTest/RingTheory/Ideal/PrincipalPrimeRegularity.lean)
  apply the first theorem to `I = q = (2)` in `ℤ`, and the specialization to the
  nonzero element `2` of the minimal prime `(2)` in `ZMod 4`.
- **Integral-map dimension.** The
  [integral leaf](MinimalPrimes/RingTheory/KrullDimension/Integral.lean) gives the
  dimension upper bound for integral ring maps and equality for injective ones.
  Its kernel-quotient statement compares the target with the source modulo the
  kernel without injectivity; its faithful-algebra statement uses the given
  algebra structure. All forms concern arbitrary commutative rings in independent
  universes, including zero rings and infinite dimension.
- **Principal prime witnesses and contraction.** The
  [principal-ideal leaf](MinimalPrimes/Principal.lean) proves that a proper
  principal ideal avoids at least one of two relatively prime elements, without
  requiring unique factorization or primeness. In a commutative semiring with
  unique factorization, every nonunit, including zero, belongs to a principal
  prime ideal, with the same disjunctive avoidance. These witnesses need no
  normalization or nonzero hypothesis. Contraction along a homomorphism from
  any semiring gives a prime two-sided source ideal; source principality and
  simultaneous avoidance are not asserted. The
  [examples](MinimalPrimesTest/PrincipalPrimeWitness.lean) include natural numbers,
  field zero, and a noninjective projection from a semiring with zero divisors.
- **Minimal primes of a principal ideal.** The
  [classification](docs/API.md#idealminimalprimes_span_singleton_eq_normalizedfactors)
  identifies the minimal primes over `(f)` for `f ≠ 0` with the principal ideals
  generated by normalized irreducible factor *values*. The
  [factor equivalence](docs/API.md#idealnormalizedfactorsequivminimalprimes)
  maps each factor `p` to `span {p}`; the
  [simp lemma](docs/API.md#idealnormalizedfactorsequivminimalprimes_apply)
  states this forward map by definitional equality, while the inverse is
  noncomputable. Multiplicities do not give additional minimal primes.
- **Components of the principal zero locus.** The
  [component equivalence](docs/API.md#idealnormalizedfactorsequivirreduciblecomponents)
  identifies those factor values with the **order-dual subtype** of irreducible
  components of the zero-locus subspace `V((f))` in `PrimeSpectrum R`. This is an
  `Equiv`, not an order-equivalence, a homeomorphism or a classification of
  arbitrary ideals.
- **Associated primes of a principal quotient.** The
  [principal-quotient comparison](MinimalPrimes/AssociatedPrincipal.lean) identifies
  `associatedPrimes R (R ⧸ Ideal.span {f})`, using base-ring `R`-module scalars,
  with `(Ideal.span {f}).minimalPrimes` for every `f : R` under `[CommRing R]`
  and `[UniqueFactorizationMonoid R]`. It requires no normalization, nonzero or
  Noetherian hypothesis and includes the zero ring.
- **Scalar restriction and quotient points.** The
  [scalar-restriction leaf](MinimalPrimes/AssociatedRestrictScalars.lean) contracts
  arbitrary submodule colon ideals over compatible scalar actions; associated
  primes contract without surjectivity and reflect along a surjective algebra
  map. The [quotient leaf](MinimalPrimes/AssociatedPrincipal.lean) identifies
  associated primes of the *quotient ring* at spectrum points with minimal
  primes over `(f)` via forward ideal comap, and gives the same criterion for
  an *exact* singleton annihilator in that quotient ring, for every `f`.
- **Height of a principal prime ideal.** The
  [principal-prime height leaf](MinimalPrimes/RingTheory/Ideal/PrincipalPrimeHeight.lean)
  gives `Ideal.height_span_singleton_le_one_of_prime`: under `[CommRing R]`,
  `[WfDvdMonoid R]` and `Prime p`, the ideal `span {p}` has height at most one.
  `Ideal.height_span_singleton_eq_one_of_prime_of_mem_nonZeroDivisors` gives
  height one when also `p ∈ nonZeroDivisors R`.
  `Ideal.height_span_singleton_eq_one_of_prime` specializes this equality to
  `[IsDomain R]`, using the prime element's nonzero property for regularity.
  The upper bound needs no domain, UFM, Noetherian or separate nontriviality
  hypothesis. These statements concern prime generators, not arbitrary
  principal ideals.
- **Descending prime chains at finite initial height.** The
  [order leaf](MinimalPrimes/Order/FiniteHeightChain.lean) proves
  `Order.wellFoundedLT_Iic_of_height_lt_top`: in a **preorder**, finite ambient
  height of `x` makes the strict order on `Set.Iic x` well-founded. The
  [prime-chain leaf](MinimalPrimes/RingTheory/Ideal/FiniteHeightChain.lean) proves
  `PrimeSpectrum.exists_stable_of_antitone_of_height_lt_top` for an antitone
  sequence in the spectrum of a **commutative semiring** with finite initial
  ambient order height, and `Ideal.exists_stable_of_antitone_of_finiteHeight`
  for an antitone ideal sequence in a **commutative ring**, with **every term
  prime** and only the initial `Ideal.FiniteHeight` instance. Each chain result
  supplies one common index `N` for tail constancy and for the **all-index**
  ideal infimum to equal the ideal at that same `N`.
  Initial primeness excludes the finite-height class's unit-ideal exception.
  No UFD, domain, global finite-dimension, ambient well-foundedness, Noetherian,
  Artinian or nontriviality assumption is added. The
  [order clients](MinimalPrimesTest/Order/FiniteHeightChain.lean) and
  [ring clients](MinimalPrimesTest/RingTheory/Ideal/FiniteHeightChain.lean)
  include delayed strict drops, a nonring semiring and a zero-ring boundary.

The principal-ideal normalized-factor results and the component equivalence work
at arbitrary universe levels with `[CommSemiring R]`, `[UniqueFactorizationMonoid R]`,
the caller's `[NormalizationMonoid R]`, and `f ≠ 0`. None adds a separate
`[IsDomain R]` assumption. They build on
mathlib's factorization, ideal, spectrum and component correspondence, while
the principal-ideal classification and factor interfaces are project results.

The height results instead use `[WfDvdMonoid R]`, Mathlib's well-foundedness
class for `DvdNotUnit`. In domains this is equivalent to the ascending chain
condition for principal ideals; it is stronger than merely having irreducible
factorizations. The proofs use maximal-power factorization, not unique
factorization or the assertion that irreducible elements are prime. Mathlib's
Noetherian principal-ideal height bound is a separate theorem for arbitrary
nonunit generators; the results here require a prime generator and make no
Noetherian assumption.

The nonzero hypothesis in the normalized-factor classification is essential.
The normalized factor multiset of zero is empty, whereas the zero ideal of a
domain is its unique minimal prime. Nonzero
units have no normalized factors and generate the unit ideal, so both sides of
the classification are empty. Repeated factors appear with multiplicity in
`normalizedFactors`, but the set equality and factor subtype identify each
normalized value only once.

## Normalization and imports

The normalized-factor declarations explicitly require the caller's
`[NormalizationMonoid R]` and `[UniqueFactorizationMonoid R]`. The principal-ideal
and component APIs need `[CommSemiring R]`. Thus their
`normalizedFactors` types use the same normalization data as the caller. Standard
concrete types such as `ℤ` export an instance already. A generic development, or
a type such as `MvPolynomial` that does not export a global normalization choice,
can use the conventional noncomputable local choice:

The following complete native module is stored in
[`MinimalPrimesTest/ReadmeNormalization.lean`](MinimalPrimesTest/ReadmeNormalization.lean).
The named local instance is private to this module.

```lean
/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import MinimalPrimes.Principal

/-! # README example: a caller's local normalization choice -/

noncomputable local instance readmeNormalization (M : Type*) [CommMonoidWithZero M]
    [UniqueFactorizationMonoid M] : StrongNormalizationMonoid M :=
  UniqueFactorizationMonoid.strongNormalizationMonoid
```

Changing normalization data can change the chosen representatives and hence the
literal factor subtype. Associated representatives generate the same principal
ideals, but this API is stated relative to the supplied normalization instance;
it does not assert an instance-independent equality between factor subtypes.

Import `MinimalPrimes.Principal` for the classification, factor equivalence and
its `@[simp]` forward-map lemma. Import `MinimalPrimes.IrreducibleComponents` for
the equivalence with the components of the prime-spectrum zero locus. Import
`MinimalPrimes.AssociatedRestrictScalars` for colon contraction and associated-
prime transport. Import `MinimalPrimes.AssociatedPrincipal` for the base-ring and
quotient-spectrum comparisons and exact annihilators. Import
`MinimalPrimes.Order.FiniteHeightChain` for the preorder lower-interval theorem,
or `MinimalPrimes.RingTheory.Ideal.FiniteHeightChain` for both prime-chain
interfaces; the latter re-exports the order leaf. Import
`MinimalPrimes.RingTheory.Ideal.PrincipalPrimeHeight` for the principal-prime
height bound and equalities. Import
`MinimalPrimes.RingTheory.Ideal.MinimalPrimeMultipliers` for multipliers outside a
chosen minimal prime and the nilpotent-product specialization. Import
`MinimalPrimes.RingTheory.Ideal.MinimalPrimeLocalization` for the localized-radical
criterion and its converse. Import `MinimalPrimes.RingTheory.KrullDimension.Integral`
for integral-homomorphism dimension bounds and equality. `MinimalPrimes` re-exports
all ten production leaves. The component equivalence has an order-dual codomain,
as required by the underlying topology API. The tests live in
`MinimalPrimesTest.Audit` (aggregate and boundary cases),
`MinimalPrimesTest.LeafClient` (direct algebraic import),
`MinimalPrimesTest.AssociatedRestrictScalars` (including a nonsurjective
diagonal), and `MinimalPrimesTest.AssociatedPrincipal` (quotient and zero-ring
examples). The finite-height clients live in
`MinimalPrimesTest.Order.FiniteHeightChain` and
`MinimalPrimesTest.RingTheory.Ideal.FiniteHeightChain`; none of these test modules
is part of the production API.
No assertion here identifies differently normalized literal factor subtypes.

This repository is organized around reusable mathematics rather than any one
source. Source interpretation, correspondence, coverage, and completion claims
remain in their source repositories.

## Public API and examples

The [historical native API reference](docs/API.md) preserves display signatures
for the four normalized-factor declarations and docstrings from nine originally
analyzed modules; it is not the complete API of this checkout.
The added associated-prime, scalar-restriction, exact-annihilator, principal-prime
height, minimal-prime multiplier, finite-height, localized-radical and integral-dimension
results below are not in that historical snapshot.
The [historical input manifest](docs/api-manifest.json) and
[reproduction instructions](docs/README.md) identify the original analyzed
source, pins and documentation tool, not a generation from the expanded library.

The principal and quotient declarations are in namespace `Ideal`; scalar
restriction uses namespaces `Submodule` and `IsAssociatedPrime`. Principal-prime
height and minimal-prime multiplier results use `Ideal`; finite-height results
use `Order`, `PrimeSpectrum` and `Ideal`.
The localized-radical criterion uses `IsLocalization.AtPrime`; integral dimension uses
`RingHom.IsIntegral` and `Algebra.IsIntegral`:

| Declaration | Canonical import | Result |
| --- | --- | --- |
| [`IsLocalization.AtPrime.mem_minimalPrimes_of_radical_map_eq`](MinimalPrimes/RingTheory/Ideal/MinimalPrimeLocalization.lean) | `MinimalPrimes.RingTheory.Ideal.MinimalPrimeLocalization` | Equality of the extended radical with the extended prime ideal implies minimality over the original ideal, without a containment assumption. |
| [`IsLocalization.AtPrime.radical_map_eq_iff_mem_minimalPrimes`](MinimalPrimes/RingTheory/Ideal/MinimalPrimeLocalization.lean) | `MinimalPrimes.RingTheory.Ideal.MinimalPrimeLocalization` | The extended radical equals the extended prime ideal exactly when that prime is minimal over the original ideal, for arbitrary commutative semirings. |
| [`Ideal.exists_mul_mem_radical_of_mem_minimalPrimes`](MinimalPrimes/RingTheory/Ideal/MinimalPrimeMultipliers.lean) | `MinimalPrimes.RingTheory.Ideal.MinimalPrimeMultipliers` | For `q ∈ I.minimalPrimes` and `x ∈ q` in a commutative semiring, some `s ∉ q` satisfies `s * x ∈ I.radical`. |
| [`Ideal.exists_isNilpotent_mul_of_mem_minimalPrimes`](MinimalPrimes/RingTheory/Ideal/MinimalPrimeMultipliers.lean) | `MinimalPrimes.RingTheory.Ideal.MinimalPrimeMultipliers` | For an element of a minimal prime over zero in a commutative semiring, some multiplier outside that prime gives a nilpotent product. |
| `RingHom.IsIntegral.ringKrullDim_le` | `MinimalPrimes.RingTheory.KrullDimension.Integral` | An integral ring map bounds target dimension by source dimension. |
| `RingHom.IsIntegral.ringKrullDim_eq` | `MinimalPrimes.RingTheory.KrullDimension.Integral` | An injective integral ring map gives `ringKrullDim R = ringKrullDim S`. |
| `RingHom.IsIntegral.ringKrullDim_eq_quotient_ker` | `MinimalPrimes.RingTheory.KrullDimension.Integral` | An integral ring map gives `ringKrullDim S = ringKrullDim (R ⧸ RingHom.ker f)` without injectivity. |
| `Algebra.IsIntegral.ringKrullDim_eq` | `MinimalPrimes.RingTheory.KrullDimension.Integral` | A faithful integral algebra gives `ringKrullDim R = ringKrullDim S` using its given algebra structure. |
| `minimalPrimes_span_singleton_eq_normalizedFactors` | `MinimalPrimes.Principal` | Minimal primes over `(f)` equal the **set** of principal ideals generated by normalized factor values of nonzero `f`. |
| `normalizedFactorsEquivMinimalPrimes` | `MinimalPrimes.Principal` | Equivalence from `{p // p ∈ normalizedFactors f}` to `(span {f}).minimalPrimes`; its forward map is `p ↦ span {p.1}`. |
| `normalizedFactorsEquivMinimalPrimes_apply` | `MinimalPrimes.Principal` | `@[simp]` forward-map equality, definitional (`rfl`) despite the noncomputable inverse. |
| `normalizedFactorsEquivIrreducibleComponents` | `MinimalPrimes.IrreducibleComponents` | Equivalence from normalized factor values to the **order-dual** irreducible components of the zero-locus subspace in `PrimeSpectrum R`. |
| `associatedPrimes_quotient_span_singleton_eq_minimalPrimes` | `MinimalPrimes.AssociatedPrincipal` | Associated primes of `R ⧸ (f)` as an `R`-module equal the minimal primes over `(f)` for every generator in a commutative ring with unique factorization. |
| `colon_quotient_mk_mul_eq_span_singleton` | `MinimalPrimes.AssociatedPrincipal` | Over a cancel-multiplication-by-nonzero commutative ring, the `R`-annihilator of `[witness]` modulo `(factor * witness)` equals `(factor)` when `witness ≠ 0`. |
| `isAssociatedPrime_quotient_iff_minimalPrimes` | `MinimalPrimes.AssociatedPrincipal` | A quotient-spectrum point is radical-associated over the quotient ring iff its forward comap image is minimal over `(f)`, for every `f` in a commutative UFD. |
| `exists_colon_quotient_iff_minimalPrimes` | `MinimalPrimes.AssociatedPrincipal` | The same all-generator criterion for an exact singleton annihilator over the quotient ring. |
| `Submodule.colon_restrictScalars` | `MinimalPrimes.AssociatedRestrictScalars` | Contracts the colon ideal of any submodule and set under a compatible algebra and module tower, with commutative source and semiring target; no surjectivity is needed. |
| `IsAssociatedPrime.comap_algebraMap` | `MinimalPrimes.AssociatedRestrictScalars` | Contracts radical-associated primes along an algebra map of commutative semirings without surjectivity. |
| `IsAssociatedPrime.comap_algebraMap_iff` | `MinimalPrimes.AssociatedRestrictScalars` | Reflects radical-associated primes when that algebra map is surjective; the converse is not valid for arbitrary maps. |
| [`Ideal.height_span_singleton_le_one_of_prime`](MinimalPrimes/RingTheory/Ideal/PrincipalPrimeHeight.lean) | `MinimalPrimes.RingTheory.Ideal.PrincipalPrimeHeight` | A prime element in a commutative ring with `WfDvdMonoid` generates an ideal of height at most one. |
| [`Ideal.height_span_singleton_eq_one_of_prime_of_mem_nonZeroDivisors`](MinimalPrimes/RingTheory/Ideal/PrincipalPrimeHeight.lean) | `MinimalPrimes.RingTheory.Ideal.PrincipalPrimeHeight` | The principal-prime height is one when the generator also belongs to `nonZeroDivisors R`. |
| [`Ideal.height_span_singleton_eq_one_of_prime`](MinimalPrimes/RingTheory/Ideal/PrincipalPrimeHeight.lean) | `MinimalPrimes.RingTheory.Ideal.PrincipalPrimeHeight` | In a commutative domain with `WfDvdMonoid`, a prime element generates an ideal of height one. |
| [`Order.wellFoundedLT_Iic_of_height_lt_top`](MinimalPrimes/Order/FiniteHeightChain.lean) | `MinimalPrimes.Order.FiniteHeightChain` | Finite ambient height of `x` in a preorder gives `WellFoundedLT (Set.Iic x)`. |
| [`PrimeSpectrum.exists_stable_of_antitone_of_height_lt_top`](MinimalPrimes/RingTheory/Ideal/FiniteHeightChain.lean) | `MinimalPrimes.RingTheory.Ideal.FiniteHeightChain` | An antitone spectrum sequence over a commutative semiring with finite initial ambient height has a constant tail and all-index ideal infimum at one common index. |
| [`Ideal.exists_stable_of_antitone_of_finiteHeight`](MinimalPrimes/RingTheory/Ideal/FiniteHeightChain.lean) | `MinimalPrimes.RingTheory.Ideal.FiniteHeightChain` | An antitone ideal sequence over a commutative ring, with every term prime and only initial `FiniteHeight`, has a constant tail and all-index infimum at one common index. |

For the prime-chain interfaces, the order-height bound is on the prime spectrum,
not on the full lattice of ideals: `Ideal.height` is not the ambient `Order.height`
of that lattice.
Primeness at every index is essential. The ring clients include a delayed
`span {Polynomial.X} → ⊥` drop with independently supplied primeness and height
one, and a private Noetherian client using Mathlib's existing finite-height
instance, rather than another production wrapper. The order clients use `ℕ ⊕ ℤ`
with infinite ambient dimension and a non-well-founded ambient strict order.
The [infinite-variable principal-prime client](MinimalPrimesTest/RingTheory/Ideal/PrincipalPrimeHeight.lean)
uses all three principal-prime height results on `(X₀)` in `K[X₀, X₁, ...]`
for any field `K`. It derives initial `FiniteHeight` from height one and applies
the ideal chain interface to a sequence that stays at `(X₀)` through any index
`d` and genuinely drops to zero at `d+1`. The interface supplies one common
index for tail constancy and the all-index infimum, while the ambient ring has
infinite Krull dimension. The separate argument in the finite-height ring
client's module documentation remains a mathematical sketch. The principal-prime
client proves no negative-Noetherianity certificate; infinite Krull dimension
alone does not establish non-Noetherianity.

The classification does not count repeated factors. Both equivalences are
noncomputable; no topological homeomorphism or arbitrary-ideal classification is
asserted. Here is a caller-supplied generic normalization, with classification,
equivalence, and forward-map use through the algebraic leaf alone:

This complete module is stored in
[`MinimalPrimesTest/ReadmeGeneric.lean`](MinimalPrimesTest/ReadmeGeneric.lean).
The Equiv-valued construction is a definition, not a proposition.

```lean
/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import MinimalPrimes.Principal

/-! # README examples: generic classification and the forward map -/

open UniqueFactorizationMonoid

noncomputable section
universe u

noncomputable local instance readmeGenericNormalization (M : Type*) [CommMonoidWithZero M]
    [UniqueFactorizationMonoid M] : StrongNormalizationMonoid M :=
  UniqueFactorizationMonoid.strongNormalizationMonoid

variable {R : Type u} [CommSemiring R] [UniqueFactorizationMonoid R]

private theorem readme_classification {f : R} (hf : f ≠ 0) :
    (Ideal.span {f}).minimalPrimes =
      {P | ∃ p ∈ normalizedFactors f, P = Ideal.span {p}} :=
  Ideal.minimalPrimes_span_singleton_eq_normalizedFactors hf

private def readme_minimalPrimes {f : R} (hf : f ≠ 0) :
    {p // p ∈ normalizedFactors f} ≃ (Ideal.span {f}).minimalPrimes :=
  Ideal.normalizedFactorsEquivMinimalPrimes hf

private theorem readme_forwardMap {f : R} (hf : f ≠ 0)
    (p : {p // p ∈ normalizedFactors f}) :
    (Ideal.normalizedFactorsEquivMinimalPrimes hf p).1 = Ideal.span {p.1} := by
  simp
```

For a concrete semiring that is not a ring,
[`MinimalPrimesTest/NatSix.lean`](MinimalPrimesTest/NatSix.lean) classifies the
minimal primes over `(6)` in `ℕ` as exactly `span {2}` and `span {3}`. It checks
that these are distinct proper prime ideals and that the factor equivalence sends
`2` to `span {2}`. Here `6` is nonzero, nonunit and nonprime.

For ordinary integers, use the exported normalization instance; there is no
local override in this separate client:

This complete module is stored in
[`MinimalPrimesTest/ReadmeInteger.lean`](MinimalPrimesTest/ReadmeInteger.lean).

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

Import the geometric leaf (or the re-exporting root) for the actual order-dual
codomain. This client uses the ordinary integer normalization as well:

This complete module is stored in
[`MinimalPrimesTest/ReadmeComponents.lean`](MinimalPrimesTest/ReadmeComponents.lean).

```lean
/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import MinimalPrimes.IrreducibleComponents
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.RingTheory.PrincipalIdealDomain

/-! # README example: order-dual components of the integer zero locus -/

open UniqueFactorizationMonoid TopologicalSpace

noncomputable section

private def readme_integerComponents {f : ℤ} (hf : f ≠ 0) :
    {p // p ∈ normalizedFactors f} ≃
      (irreducibleComponents
        (PrimeSpectrum.zeroLocus (Ideal.span {f} : Set ℤ)))ᵒᵈ :=
  Ideal.normalizedFactorsEquivIrreducibleComponents hf
```

## Provenance and credits

This library builds on Mathlib and prior Formal Frontier formalizations of
principal-ideal, associated-prime and finite-height prime-chain results. The
principal-prime height proofs use Mathlib's maximal-power factorization,
prime-ideal height criterion and regular-element height lower bound.
The localized-radical criterion uses Mathlib's minimal-prime localization,
radical invariance of minimal primes and prime-ideal correspondence; the implication
from minimality is Mathlib's theorem, formalized by Andrew Yang.
The minimal-prime multiplier proof uses Mathlib's radical equality after localization
at a minimal prime, localization of radicals and denominator clearing for ideals.
The integral-dimension proof uses Mathlib's incomparability, lying-over and
going-up finite-chain lifting. Its supremum argument also follows the approach
in Formal Frontier's finite-subset capture dimension bound. The kernel-quotient
form uses Mathlib's integral and injective kernel lift; the faithful-algebra
form uses its algebra-map integrality and faithfulness bridges. The integer-diagonal
hypotheses and independent dimension calculations use Mathlib's finite-module,
product, principal-ideal-ring and surjective-map APIs. AI agents
developed the Lean code and examples.

Ravi Vakil's *Foundations of Algebraic Geometry*, October 21, 2025 draft,
Exercise 3.7.H, and *The Rising Sea*, Exercise 6.6.F, are mathematical
motivation, not Lean authorship, endorsement or evidence of source coverage.
Mathlib supplies the factorization, colon, associated-prime, radical/comap and
spectrum-correspondence APIs used here, as well as ambient order height, strict-monotone
well-foundedness transport, the antitone chain condition and ideal finite-height
instances. No source text or assets are redistributed here.
The original project code is available under Apache License 2.0 (see `LICENSE`),
with `Authors: Formal Frontier Agents`. Lean, mathlib and doc-gen4 are separately
credited tools and infrastructure, not original project implementations.

## Build and audit

The exact Lean toolchain is in `lean-toolchain`, and `lake-manifest.json` pins
the complete dependency graph. Obtain the matching precompiled mathlib cache
before any build with:

```sh
lake exe cache get
```

Build the default library targets, including the production, test and
README-example modules:

```sh
lake build
```

For focused checks, individual modules can be built explicitly (the commands
below are optional and may overlap the default build):

```sh
lake build MinimalPrimes.Principal MinimalPrimes.IrreducibleComponents MinimalPrimes.AssociatedRestrictScalars MinimalPrimes.AssociatedPrincipal MinimalPrimes
lake build MinimalPrimesTest.Audit MinimalPrimesTest.LeafClient MinimalPrimesTest.AssociatedRestrictScalars MinimalPrimesTest.AssociatedPrincipal
lake build MinimalPrimesTest.ReadmeNormalization MinimalPrimesTest.ReadmeGeneric MinimalPrimesTest.ReadmeInteger MinimalPrimesTest.ReadmeComponents MinimalPrimesTest.NatSix
lake build MinimalPrimes.Order.FiniteHeightChain MinimalPrimes.RingTheory.Ideal.FiniteHeightChain
lake build MinimalPrimes.RingTheory.Ideal.PrincipalPrimeHeight
lake build MinimalPrimesTest.Order.FiniteHeightChain MinimalPrimesTest.RingTheory.Ideal.FiniteHeightChain
```

The prescribed linters report nonfatal "The current module only contains private
declarations" warnings in `MinimalPrimesTest/{Audit,LeafClient,ReadmeComponents,
ReadmeGeneric,ReadmeInteger,ReadmeNormalization,NatSix}.lean`. These modules retain
private test clients; the full build and axiom audit include them without `--wfail`.

The four Lean fences above are exact copies of their named source modules and are
included by the default test-library glob. Their stored declarations, including
local instances and Equiv-valued definitions, are part of the full proof audit.

The audit file retains stored private generic and integer tests and
unit/repeated/zero boundaries; it has no `#print axioms` commands. The complete
standard-axiom audit loads the compiled private module parts and checks transitive
axioms of stored private clients and generated declarations, including proof-field
declarations. It does not independently replay stored proof bodies.
Transitive axioms must be restricted to `propext`, `Classical.choice`, and
`Quot.sound`.
The production library and completed examples contain no admissions or custom
axioms.

Unless stated otherwise in a file, original code in this repository is made
available under the Apache License 2.0.
