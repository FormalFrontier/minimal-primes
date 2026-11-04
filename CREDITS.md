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
The coordinate-ideal sum criterion applies the existing membership law to one and
uses Mathlib's ideal one-test; the ultrafilter properness result specializes this
criterion using Mathlib's ultrafilter complement law.
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

The comparison with small products uses the existing dependent reduced-product
carrier and canonical fibrewise map. Representative choice and finite eventual
quantification reuse Mathlib's quotient and finite-filter modules, credited to
Johannes Hölzl and Jeremy Avigad; equivalence packaging uses the interfaces credited
to Leonardo de Moura and Mario Carneiro. The cardinal-small generalization of the
original injectivity argument uses Josha Dekker's cardinal-intersection filter
API, Yury Kudryashov's countable-intersection API and Joël Riou's `HasCardinalLT`
surjection and finite-size bridges. The cardinal/countability normalization APIs
are credited to Johannes Hölzl, Mario Carneiro, Floris van Doorn and Violeta
Hernández Palacios. The germ/product antecedents are credited to Yury Kudryashov
and Abhimanyu Pallavi Sudhir. The comparison, representative and naturality proofs
define no additional quotient or representative-choice engine.

The dependent-product unit-locus criterion generalizes the germ unit-locus proof by
Formal Frontier Agents, retaining its constant-family API and the germ units
equivalence. It uses Andrew Yang's Mathlib `Pi.isUnit_iff` and `MulEquiv.piUnits`,
the units homomorphism APIs formalized by Johan Commelin, Chris Hughes and Kevin
Buzzard, and the germ carrier and quotient APIs by Yury Kudryashov and Abhimanyu
Pallavi Sudhir. Everywhere-unit representative choice uses the filter API developed
by Johannes Hölzl and Jeremy Avigad. The right-unit association criterion uses this
unit lifting and Mathlib's association formalization by Johannes Hölzl and Jens Wagemaker.

The germ non-zero-divisor criteria use Mathlib's germ representation and multiplication
APIs by Yury Kudryashov and Abhimanyu Pallavi Sudhir, and its non-zero-divisor
submonoids and annihilator witnesses by Kenny Lau, Devon Tuma and Oliver Nash.
Witness selection uses Mathlib's `Filter.skolem`. The bad-coordinate annihilator
argument follows the corresponding regularity argument by Formal Frontier Agents;
the proofs test all varying representatives, not just constant germs.

The ultrafilter-product no-zero-divisor criterion uses Johan Commelin's
`NoZeroDivisors` class, the ultrafilter alternative developed by Johannes Hölzl,
Jeremy Avigad and Yury Kudryashov, and the existing dependent-section reflection
criterion by Formal Frontier Agents. Its quotient operations use Amelia Livingston's
multiplicative congruences on the dependent filter-product carrier of Yury Kudryashov
and Abhimanyu Pallavi Sudhir. The constant-germ criterion specializes the dependent
result after identifying these congruence records with Mathlib's germ zero and
binary-map multiplication; no second quotient or witness-selection construction
is introduced.

Constant-germ reducedness uses Mathlib's quotient, power and eventual-equality
interfaces, and Johan Commelin's zero-and-power definitions of nilpotence and
reducedness. The finite-member bound for eventual nilpotence uses Oliver Nash's
nilpotency-class API, Mathlib's upward propagation of vanishing powers, and the
finite-set order bounds developed by Peter Nelson, Yaël Dillies, Mario Carneiro
and Kenny Lau. The dependent-product finite-member nilpotence criterion composes
that shared bound with the uniform-exponent quotient criterion developed by
Formal Frontier Agents, using the existing dependent Product algebra and coercion
API. Its constant-germ specialization instead composes the same bound with the
existing germ zero-and-power criterion; no carrier or operation comparison is
needed. The finite-principal client uses Mathlib's `ZMod`, free monoids and
`WithZero` formalizations.

The intrinsic germ-center criterion uses Mathlib's magma-center formalization by
Eric Wieser and Jireh Loreaux, Eric Wieser's bundled submonoid center, and the germ
representation, quotient induction and multiplication interfaces of Yury Kudryashov
and Abhimanyu Pallavi Sudhir. Commutation uses the interfaces formalized by Neil
Strickland and Yury Kudryashov. The varying-witness argument follows the existing
multiplication-regularity pattern developed by Formal Frontier Agents, retaining
all three intrinsic centrality fields. The four-element client and its varying
representative are original finite data; no additional center or quotient is defined.
The multiplicative center equivalence reuses the existing varying-application
injectivity API and Mathlib's equivalence interfaces, formalized by Johannes Hölzl,
Callum Sutton, Yury Kudryashov, Leonardo de Moura and Mario Carneiro. Its total
central lift extends the same nonassociative client.

The comparison of two filters by eventual equality of dependent sections uses
Mathlib's filter extensionality and principal-restriction APIs, by Johannes Hölzl
and Jeremy Avigad. Its locally masked sections reuse the original project
section-reflection theorem, rather than a second witness-selection construction.
The Sort-general comparison and its nontrivial-fibre interpretation are original
project arguments. The Type-valued setoid bridge uses Mathlib's setoid extensionality
and Sébastien Gouëzel's nontriviality API.

The dependent index-pullback properties reuse Mathlib's complete quotient-kernel
injectivity criterion in `Data.Setoid.Basic`, by Amelia Livingston and Bryan Gin-ge
Chen, and `eventually_map` in `Order.Filter.Map`, by Johannes Hölzl and Jeremy Avigad.
The full injectivity criterion composes that kernel comparison with the section
setoid criterion. Surjectivity uses the complete `Quotient.map_surjective` API
in `Data.Quot`, whose quotient interface was developed by Johannes Hölzl, and the
dependent Pi equivalence in `Logic.Equiv.Basic`, by Leonardo de Moura and Mario
Carneiro. The existing filter-product carrier and pullback remain those described
in the module references; no second quotient is introduced.

The maximal-spectrum pullback restricts Mathlib's ideal order embedding, contraction
maximality and ideal correspondence for surjective homomorphisms. Its integral
extension uses the maximality and kernel-containment lying-over theorems in Anne
Baanen and Yongle Hu's `Mathlib.RingTheory.Ideal.GoingUp`, including the prime-over-ideal
and reverse-maximality theorems for images of ideal zero loci. It uses David Kurniadi
Angdinata's maximal-spectrum formalization and the prime-spectrum pullback
formalization of Johan Commelin, Filippo A. E. Nuccio and Andrew Yang. Continuity and
closedness use the existing induced Zariski topology and Mathlib's integral
prime-spectrum closed-map theorem in Johan Commelin's prime-spectrum topology module;
identity, composition and the surjective specialization reuse Mathlib's ring-map
integrality witnesses. The canonical restriction and infinitude-transfer approach
follows the mathematical argument developed by Formal Frontier Agents.

The dimension-at-most-two unique-factorization classification builds on Mathlib's
nonzero-prime prime-element extraction and finite strict-chain dimension bound.
Its ideals, prime spectrum and relation series are the existing Mathlib objects;
these earlier formalizations supply the factorization and dimension interfaces.
The irreducible-generator dimension criterion is formulated using Mathlib's
`Irreducible.dvd_symm` for monoids, singleton-span inclusion and divisibility for
commutative semirings, and the order-theoretic finite-chain dimension criterion.
The dimension-two comparison interfaces use Mathlib's order Krull dimension,
height/coheight and minimal/maximal-point predicates, and its canonical prime spectrum.
The semiring formulation uses Andrew Yang's minimal-prime avoidance of non-zero-divisors
in Mathlib. The regular-ideal closed-locus bound uses the same minimal-prime avoidance,
this library's nonminimal-locus dimension comparison and finite-bound criterion,
and Mathlib's canonical zero locus with its inherited spectrum order. The extended
inequality uses finite addition in `WithBot ℕ∞`, including bottom and infinite values.
Its ring specialization agrees with
Andrew Yang's quotient-dimension bounds through Mathlib's quotient-spectrum order
isomorphism.
The finite-bound boundary-deletion family uses the order Krull dimension formalization
of Jujian Zhang, Fangming Li and Joachim Breitner, and the relation-series interfaces
of Jujian Zhang and Fangming Li in Mathlib. The one-boundary characterization relates
finite strict chains by adjoining a predecessor or deleting the first point; the
maximal-boundary version follows by order duality. The two-boundary formulation uses
Mathlib's ambient extremum predicates and inherited subtype orders, with upward closure
of the nonminimal locus identifying its maximal points with ambient maximal points.
The full `WithBot ℕ∞` boundary inequalities combine these finite-bound interfaces
with Mathlib's empty-order, zero- and one-dimensional criteria, order duality and
extended-natural arithmetic. They are source-independent order results; no
additional correspondence with the motivating algebraic-geometry exercises is asserted.

The dependent semimodule data use Amelia Livingston's additive congruence quotient
machinery, Eric Wieser's ring-congruence factories, Johannes Hölzl's quotient maps,
and the germ interfaces of Yury Kudryashov and Abhimanyu Pallavi Sudhir. Module and
Pi-module interfaces are credited to Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl,
Mario Carneiro, Simon Hudon and Patrick Massot. The record comparisons use the
algebraic extensionality interfaces of Bryan Gin-ge Chen, Yury Kudryashov and
Raghuram Sundararajan.
Regular scalar actions use Damiano Testa's regularity definitions, and the modern
torsion-free class is Yaël Dillies's formalization. Their represented-scalar readout
composes the existing Formal Frontier dependent coordinate-map injectivity theorem;
no new quotient, representative-choice or collision engine is introduced.
The dependent-product annihilator and faithfulness interfaces use Kenny Lau's
Mathlib ideal and module-annihilator formalization and the faithful scalar-action
interfaces of Chris Hughes and Yury Kudryashov, together with the existing Formal
Frontier semimodule and dependent-section interfaces.

The common finite-basis construction composes the existing Formal Frontier
dependent Product module, varying-map and finite-coordinate interfaces. It uses
Mathlib's basis interfaces of Johannes Hölzl, Mario Carneiro and Alexander Bentkamp,
Johannes Hölzl's finite Finsupp/function and standard-basis interfaces, and the
Pi-module interfaces of Simon Hudon and Patrick Massot. It retains the given fibre
bases and the existing whole coordinate equivalence, without a new quotient,
coordinate or basis-choice construction.

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

