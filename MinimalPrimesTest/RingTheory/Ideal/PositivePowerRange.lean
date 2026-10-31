/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MinimalPrimes.RingTheory.Ideal.PositivePowerRange

/-!
# Surjective compatibility for radical extension–contraction

For every target ideal, the positive-power criterion recovers the radical
consequence of extension–contraction along a surjective homomorphism by taking
exponent one.
-/

@[expose] public section

universe u v w

example {R : Type u} {S : Type v} {F : Type w}
    [Semiring R] [CommSemiring S] [FunLike F R S] [RingHomClass F R S]
    (f : F) (hf : Function.Surjective f) (I : Ideal S) :
    Ideal.radical (Ideal.map f (Ideal.comap f I)) = I.radical := by
  apply Ideal.radical_map_comap_of_pos_pow_mem_range f
  intro x
  obtain ⟨a, ha⟩ := hf x
  refine ⟨1, Nat.zero_lt_one, a, ?_⟩
  simpa only [pow_one] using ha
