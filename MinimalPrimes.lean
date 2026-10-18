/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MinimalPrimes.IrreducibleComponents
public import MinimalPrimes.Principal
public import MinimalPrimes.AssociatedRestrictScalars
public import MinimalPrimes.AssociatedPrincipal
public import MinimalPrimes.Order.FiniteHeightChain
public import MinimalPrimes.RingTheory.Ideal.FiniteHeightChain
public import MinimalPrimes.RingTheory.Ideal.PrincipalPrimeHeight
public import MinimalPrimes.RingTheory.Ideal.MinimalPrimeLocalization
public import MinimalPrimes.RingTheory.Ideal.MinimalPrimeMultipliers
public import MinimalPrimes.RingTheory.KrullDimension.Integral

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
The minimal-prime multiplier leaf clears an element of a minimal prime into the radical
by a multiplier outside that same prime, over any commutative semiring.
The integral-homomorphism leaf gives dimension equality for integral injections
without finiteness or nontriviality hypotheses. The minimal-prime localization leaf detects
minimality over an arbitrary ideal by equality of radicals after localization at a prime,
for commutative semirings and without a separate containment hypothesis.
Import a leaf directly for a smaller API.
-/
