/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import MinimalPrimes.RingTheory.Ideal.PrimePiUltrafilter

/-!
# A pure ultrafilter detects one coordinate

The maximality criterion at a pure ultrafilter ignores every other coordinate,
including top ideals and trivial semirings at those coordinates.
-/

universe u v

example {ι : Type u} (R : ι → Type v) [∀ i, Semiring (R i)]
    (I : ∀ i, Ideal (R i)) (i : ι) :
    (Ideal.pi I ⊔ (pure i : Filter ι).piIdeal R).IsMaximal ↔ (I i).IsMaximal := by
  simpa using Ultrafilter.isMaximal_pi_sup_piIdeal_iff R I (pure i)
