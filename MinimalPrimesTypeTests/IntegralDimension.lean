/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import MinimalPrimes.RingTheory.KrullDimension.Integral

/-!
# Dimension under injective integral homomorphisms

A signature client of the public theorem for commutative rings in independent
universes. The equality includes the empty spectrum and infinite dimension.
-/

universe u v

namespace MinimalPrimesTypeTests.IntegralDimension

/-- The public dimension theorem has no finiteness, domain, or nontriviality premise. -/
private theorem integral_injection_dimension {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] {f : A →+* B} (hf : f.IsIntegral)
    (hinj : Function.Injective f) : ringKrullDim A = ringKrullDim B :=
  RingHom.IsIntegral.ringKrullDim_eq hf hinj

end MinimalPrimesTypeTests.IntegralDimension
