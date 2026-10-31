/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Ideal.Maps

/-!
# Ideal contraction along maps with positive powers in the image

If every target element has a positive power in the image of a semiring
homomorphism, contraction reflects containment in a radical ideal. The ideal on
the left of the containment need not be radical. The source semiring need not be
commutative, and the exponents may depend on the target element.
-/

@[expose] public section

universe u v w

namespace Ideal

variable {R : Type u} {S : Type v} {F : Type w}
variable [Semiring R] [CommSemiring S] [FunLike F R S] [RingHomClass F R S]

/-- If every target element has a positive power in the image, contraction
reflects containment in a radical right-hand ideal. -/
theorem comap_le_comap_iff_of_pos_pow_mem_range (f : F)
    (hf : ∀ x : S, ∃ n : ℕ, 0 < n ∧ x ^ n ∈ Set.range f)
    (I J : Ideal S) (hJ : J.IsRadical) :
    I.comap f ≤ J.comap f ↔ I ≤ J := by
  constructor
  · intro h x hx
    obtain ⟨n, hn, a, ha⟩ := hf x
    have haI : a ∈ I.comap f := by
      apply mem_comap.mpr
      rw [ha]
      exact I.pow_mem_of_mem hx n hn
    have hpow : x ^ n ∈ J := by
      rw [← ha]
      exact mem_comap.mp (h haI)
    have hxrad : x ∈ J.radical := mem_radical_iff.mpr ⟨n, hpow⟩
    simpa only [radical_eq_iff.mpr hJ] using hxrad
  · exact comap_mono

end Ideal
