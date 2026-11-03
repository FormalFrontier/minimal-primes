/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MinimalPrimes.RingTheory.Frobenius.Reduced
public import MinimalPrimes.IrreducibleComponents
public import MinimalPrimes.Principal
public import MinimalPrimes.AssociatedRestrictScalars
public import MinimalPrimes.AssociatedPrincipal
public import MinimalPrimes.Order.FiniteHeightChain
public import MinimalPrimes.Order.Filter.Germ.Center
public import MinimalPrimes.Order.Filter.Germ.Map
public import MinimalPrimes.Order.Filter.Germ.NonZeroDivisors
public import MinimalPrimes.Order.Filter.Germ.Regular
public import MinimalPrimes.Order.Filter.Germ.Reduced
public import MinimalPrimes.Order.Filter.Germ.SMul
public import MinimalPrimes.Order.Filter.Germ.Units
public import MinimalPrimes.Order.Filter.Product.Center
public import MinimalPrimes.Order.Filter.Product.Reduced
public import MinimalPrimes.Order.Filter.Product.Regular
public import MinimalPrimes.Order.Filter.Product.Units
public import MinimalPrimes.RingTheory.Ideal.FiniteHeightChain
public import MinimalPrimes.RingTheory.Ideal.PrincipalPrimeHeight
public import MinimalPrimes.RingTheory.Ideal.MinimalPrimeLocalization
public import MinimalPrimes.RingTheory.Ideal.MinimalPrimePi
public import MinimalPrimes.RingTheory.Ideal.PiFilter
public import MinimalPrimes.RingTheory.Ideal.PrimePiUltrafilter
public import MinimalPrimes.RingTheory.Ideal.ResidueFieldPiUltrafilter
public import MinimalPrimes.RingTheory.Ideal.MinimalPrimeMultipliers
public import MinimalPrimes.RingTheory.Ideal.PositivePowerRange
public import MinimalPrimes.RingTheory.KrullDimension.FieldExtension
public import MinimalPrimes.RingTheory.KrullDimension.Integral
public import MinimalPrimes.RingTheory.Localization.AtPrime
public import MinimalPrimes.RingTheory.Localization.Reduced
public import MinimalPrimes.RingTheory.Spectrum.Prime.PiUltrafilter
public import MinimalPrimes.RingTheory.Spectrum.Prime.ZeroDimensional
public import MinimalPrimes.RingTheory.Spectrum.Prime.PositivePowerRange
public import MinimalPrimes.Topology.KrullDimension.OpenCover
public import MinimalPrimes.RingTheory.RingHom.ULift

/-!
# Minimal primes

Root import re-exporting the principal-ideal classification, its normalized-factor
equivalence, the associated-prime comparison for principal quotients, and the
equivalence with order-dual irreducible components of the prime-spectrum zero-locus
subspace. The scalar-restriction leaf supplies colon contraction and associated-
prime transport, and the principal-quotient leaf relates quotient-spectrum points
to minimal primes and exact annihilators. The finite-height leaves give well-founded
lower intervals in preorders and stabilization of antitone prime chains with their
all-index ideal infimum at a common index, using only finite initial height.
The principal-prime height leaf bounds height by one under well-founded strict divisibility,
with height one for regular prime generators and, in particular, prime elements in domains.
The finite-product leaf classifies minimal primes over arbitrary ideals by labelled
coordinate minimal primes, and transports evaluation comaps at arbitrary index types.
The minimal-prime multiplier leaf clears an element of a minimal prime into the radical
by a multiplier outside that same prime, over any commutative semiring.
The integral-homomorphism leaf gives dimension equality for integral injections
without finiteness or nontriviality hypotheses. The minimal-prime localization leaf detects
minimality over an arbitrary ideal by equality of radicals after localization at a prime,
for commutative semirings and without a separate containment hypothesis.
The localization leaves characterize field localizations at arbitrary primes of
commutative semirings by minimality and target reducedness, and show that reducedness
is preserved by arbitrary localization.
The positive-power leaves show that contraction reflects containment in a radical
right-hand ideal when every target element has a positive power in the image, and
deduce injectivity of pullback on prime spectra of commutative semirings.
The product-semifield spectrum leaf upgrades the ultrafilter classification to a
homeomorphism for the existing Zariski and Stone topologies, with basis-transport laws
and density of coordinate primes. Ultrafilter zero-set ideals are maximal already
for division semiring fibres; for field fibres, the residue-field leaf identifies
their stock residue fields with dependent reduced products over the section ring,
compatibly with fibrewise field homomorphisms.
The zero-dimensional spectrum leaf provides clopenness of basic opens, Hausdorffness
and the reduced, nontrivial, preconnected-spectrum field criterion.
The germ-regularity leaf characterizes intrinsic left, right and two-sided regularity
by eventual regularity of representatives, for arbitrary filters and codomains with
only multiplication.
The germ-reducedness leaf needs only zero and natural-number powers: reducedness is
equivalent to eventual reducedness of the value type, or to the filter being bottom
or the value type being reduced.
The monoid-germ leaf characterizes invertibility by the representative's filter-large
unit locus, for arbitrary filters and potentially noncommutative monoids.
The germ-map leaf characterizes injectivity of varying pointwise application by eventual
injectivity of the fibre maps, without properness or inhabitedness assumptions. Its pointed
fibre criterion needs only eventual preservation of the specified points for the converse.
The germ-scalar leaf specializes zero-reflection to a selected zero-preserving action,
without scalar-zero or additive assumptions.
The non-zero-divisor leaf characterizes intrinsic left, right and two-sided
non-zero-divisors by their eventual coordinate loci, over arbitrary monoids with zero,
and gives the scalar submonoid criterion under an explicit eventual zero-preservation law.
The germ-center leaf characterizes the full intrinsic magma center by eventual
coordinate centrality, with a submonoid-center bridge requiring only a two-sided identity.
Import a leaf directly for a smaller API.
-/
