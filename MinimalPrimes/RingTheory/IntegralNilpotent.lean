/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Nilpotent.Lemmas

/-!
# Integral relations modulo nil ideals

A monic relation whose value is nilpotent becomes a vanishing monic relation
by taking a power. Consequently integrality lifts across a quotient by a nil
ideal, without finite generation or uniform nilpotence of that ideal.

## References

* Mathlib's monic polynomial and integral-element APIs.
-/

@[expose] public section

open Polynomial

/-- A nilpotent value of a monic polynomial gives an integral element. -/
lemma IsIntegral.of_aeval_isNilpotent {R B : Type*} [CommRing R] [Ring B] [Algebra R B]
    {x : B} {f : R[X]} (hf : f.Monic) (hx : IsNilpotent (aeval x f)) : IsIntegral R x := by
  obtain ⟨n, hn⟩ := hx
  exact ⟨f ^ n, hf.pow n, by simpa only [← aeval_def, map_pow] using hn⟩

/-- Integrality lifts from a quotient by an ideal consisting of nilpotent elements. -/
lemma IsIntegral.of_quotient_of_le_nilradical {R B : Type*} [CommRing R] [CommRing B]
    [Algebra R B] (I : Ideal B) (hI : I ≤ nilradical B) {x : B}
    (hx : IsIntegral R (Ideal.Quotient.mk I x)) : IsIntegral R x := by
  obtain ⟨f, hf, hx⟩ := hx
  apply IsIntegral.of_aeval_isNilpotent hf
  apply (mem_nilradical).mp (hI ?_)
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  exact (aeval_algHom_apply (Ideal.Quotient.mkₐ R I) x f).symm.trans hx
