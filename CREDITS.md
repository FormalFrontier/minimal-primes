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

