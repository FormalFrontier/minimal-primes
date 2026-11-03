# Credits and license

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
product, principal-ideal-ring and surjective-map APIs. The localization field
criterion uses Andrew Yang's Mathlib minimal-prime correspondence. Reducedness under
localization generalizes Andrew Yang's Mathlib theorem and the prior Formal Frontier
formalization in `SchemeProperties.Reduced`; its proof composes the existing radical
and nilradical APIs rather than repeating the denominator argument.
The zero-dimensional spectrum argument uses Mathlib's closed-point criterion,
away-localization image and specialization-stable spectrum-map range theorem,
which Mathlib attributes to the [Stacks Project, Tag 00HY](https://stacks.math.columbia.edu/tag/00HY).
Its field criterion uses Mathlib's preconnected/totally-disconnected subsingleton
theorem and Andrew Yang's reduced-ring singleton-spectrum field criterion.
The separation characterizations factor the closed-point/maximal-ideal argument
of Mathlib's `PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero`,
reusing this library's clopen-basis Hausdorff proof. For finite spectra the
T₁ characterization recovers Mathlib's discrete criterion; under `IsDomain R`
it agrees with `PrimeSpectrum.t1Space_iff_isField` and
`Ring.KrullDimLE.isField_of_isDomain`. The zero ring has dimension bottom, so
these statements use the bound rather than equality of dimension with zero.
The field-extension dimension proof uses Mathlib's Noether normalization
theorem ([Stacks Project, Tag 00OW](https://stacks.math.columbia.edu/tag/00OW)),
flatness over fields, finite tensor-product maps, polynomial base change and
polynomial Krull dimension, together with this library's integral-injection
dimension comparison.
The finite-product minimal-prime classification uses Andrew Yang's Mathlib
minimal-prime localization correspondence, Mathlib's idempotent-localization
criterion, product-ideal order isomorphism, finite-intersection prime criterion
and injective labelled spectrum map. Its finite-intersection argument follows
the Formal Frontier Agents' formalization of prime spectra of finite products
of commutative semirings. The evaluation transport is a specialization of the
existing localization engine, not a new generic minimality engine.
The classification of primes of products of semifields uses Mathlib's ideal,
prime-spectrum, ultrafilter and germ interfaces, including its cofinite ultrafilter
and constant-family ultraproduct. The zero-set test argument is expressed directly
for semifields, without introducing another quotient construction.
The all-ideal/filter correspondence generalizes that predecessor's zero-set tests,
disjoint-piece sum and pointwise-inverse argument: the constructors work for
semirings, and the classification for division semirings uses Mathlib's left ideals.
Its finite-product comparison and germ-kernel client reuse Mathlib's existing APIs.
The topological extension follows that classification and uses Reid Barton's Mathlib
ultrafilter Stone topology (whose general Stone–Čech construction also credits
Marius Stekelenburg), Johan Commelin's prime-spectrum topology and basic-open basis,
and Mathlib's homeomorphism and dense-embedding interfaces. Both topologies are the
existing ones; the new proofs compare their bases and transport density of pure
ultrafilters to coordinate primes.

The canonical residue comparison composes Mathlib's quotient first-isomorphism
formalization by Kenny Lau and Patrick Massot with Andrew Yang's ideal-residue-field
and induced-map APIs, built on Mathlib's local-ring residue fields and prime
localizations. Its dependent Product carrier and pointwise inversion follow the
filter-germ and ultraproduct formalizations of Abhimanyu Pallavi Sudhir and Yury
Kudryashov; the quotient algebra and descended maps reuse Antoine Chambert-Loir's
ring-congruence interfaces. Maximality transports ultrafilter extremality through
the existing division-semiring ideal/filter correspondence.

The varying-application injectivity criterion uses the existing germ carrier,
`Germ.map₂`, quotient induction and eventual-equality API of Yury Kudryashov and
Abhimanyu Pallavi Sudhir in Mathlib. Its proof chooses fibrewise collision witnesses
and applies injectivity on the existing quotient; it defines no additional carrier
or descended map. The cofinite example uses Mathlib's eventual-inequality and
natural-number cancellation interfaces. Related multiplication-regularity criteria
were developed by Formal Frontier Agents/Almanac; the general function criterion
introduces no dependency on that specialization.

The germ non-zero-divisor criteria use Mathlib's germ representation and multiplication
APIs by Yury Kudryashov and Abhimanyu Pallavi Sudhir, and its non-zero-divisor
submonoids and annihilator witnesses by Kenny Lau, Devon Tuma and Oliver Nash.
Witness selection uses Mathlib's `Filter.skolem`. The bad-coordinate annihilator
argument follows the corresponding regularity argument by Formal Frontier Agents;
the proofs test all varying representatives, not just constant germs.

AI agents developed the Lean code and examples.

Ravi Vakil's *Foundations of Algebraic Geometry*, October 21, 2025 draft,
Exercise 3.7.H, and *The Rising Sea*, Exercise 6.6.F, are mathematical
motivation, not Lean authorship or endorsement.
Mathlib supplies the factorization, colon, associated-prime, radical/comap and
spectrum-correspondence APIs used here, as well as ambient order height, strict-monotone
well-foundedness transport, the antitone chain condition and ideal finite-height
instances. No source text or assets are redistributed here.
The original project code is available under Apache License 2.0 (see [LICENSE](LICENSE)),
with `Authors: Formal Frontier Agents`. Lean, mathlib and doc-gen4 are separately
credited tools and infrastructure, not original project implementations.

