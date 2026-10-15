/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Ideal.HasGoingUp

/-!
# Krull dimension under integral homomorphisms

An integral homomorphism does not increase dimension in the target. If it is
also injective, lying-over and going-up give equality. The rings may lie in
independent universes, and dimension takes values in `WithBot ℕ∞`.

The proof uses the defining supremum over finite strict chains, including the
empty-spectrum case. It does not require finite dimension or equality of the
heights of individual primes.

## References

The incomparability, lying-over, and finite-chain lifting results are Mathlib's
`Ideal.IsIntegral.under_lt_under`, `RingHom.IsIntegral.comap_surjective`, and
`Ideal.exists_ltSeries_of_hasGoingUp`. The supremum argument uses Mathlib's
`Order.krullDim` and follows the finite-chain approach also used in Formal
Frontier's finite-subset capture dimension bound.
-/

@[expose] public section

universe u v

namespace RingHom.IsIntegral

/-- An integral homomorphism bounds the dimension of its target by that of its source.
Injectivity is not required for this inequality. -/
theorem ringKrullDim_le {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    {f : A →+* B} (hf : f.IsIntegral) : ringKrullDim B ≤ ringKrullDim A := by
  letI : Algebra A B := f.toAlgebra
  letI : Algebra.IsIntegral A B := ⟨hf⟩
  apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap f)
  intro P Q hPQ
  change P.asIdeal.under A < Q.asIdeal.under A
  exact Ideal.IsIntegral.under_lt_under hPQ

/-- Injective integral homomorphisms preserve Krull dimension, including bottom
for the zero ring and top for infinite dimension. -/
theorem ringKrullDim_eq {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    {f : A →+* B} (hf : f.IsIntegral) (hinj : Function.Injective f) :
    ringKrullDim A = ringKrullDim B := by
  letI : Algebra A B := f.toAlgebra
  letI : Algebra.IsIntegral A B := ⟨hf⟩
  refine le_antisymm ?_ hf.ringKrullDim_le
  change Order.krullDim (PrimeSpectrum A) ≤ _
  -- Unlike the nonempty-spectrum reformulation, this supremum also covers bottom.
  refine iSup_le fun l => ?_
  obtain ⟨P, hP⟩ := hf.comap_surjective hinj l.head
  haveI : P.asIdeal.LiesOver l.head.asIdeal := ⟨by
    change l.head.asIdeal = Ideal.comap f P.asIdeal
    exact congrArg PrimeSpectrum.asIdeal hP.symm⟩
  obtain ⟨L, hL, _, _⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P.asIdeal
  rw [← hL]
  exact Order.LTSeries.length_le_krullDim L

end RingHom.IsIntegral
