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
also injective, lying-over and going-up give equality. Without injectivity,
the target has the dimension of the source modulo the kernel. A faithful
integral algebra has the dimension of its base ring. The rings may lie in
independent universes, and dimension takes values in `WithBot ℕ∞`.

The proof uses the defining supremum over finite strict chains, including the
empty-spectrum case. It does not require finite dimension or equality of the
heights of individual primes.

## References

The incomparability, lying-over, and finite-chain lifting results are Mathlib's
`Ideal.IsIntegral.under_lt_under`, `RingHom.IsIntegral.comap_surjective`, and
`Ideal.exists_ltSeries_of_hasGoingUp`. The supremum argument uses Mathlib's
`Order.krullDim` and follows the finite-chain approach also used in Formal
Frontier's finite-subset capture dimension bound. The kernel-quotient form
uses Mathlib's `RingHom.IsIntegral.kerLift` and `RingHom.kerLift_injective`.
The faithful-algebra form uses `algebraMap_isIntegral_iff` and
`FaithfulSMul.algebraMap_injective` for the given algebra structure.
-/

@[expose] public section

universe u v

namespace RingHom.IsIntegral

/-- An integral homomorphism bounds the dimension of its target by that of its source.
Injectivity is not required for this inequality. -/
theorem ringKrullDim_le {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    {f : A →+* B} (hf : f.IsIntegral) : ringKrullDim B ≤ ringKrullDim A := by
  let : Algebra A B := f.toAlgebra
  let : Algebra.IsIntegral A B := ⟨hf⟩
  apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap f)
  intro P Q hPQ
  change P.asIdeal.under A < Q.asIdeal.under A
  exact Ideal.IsIntegral.under_lt_under hPQ

/-- Injective integral homomorphisms preserve Krull dimension, including bottom
for the zero ring and top for infinite dimension. -/
theorem ringKrullDim_eq {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    {f : A →+* B} (hf : f.IsIntegral) (hinj : Function.Injective f) :
    ringKrullDim A = ringKrullDim B := by
  let : Algebra A B := f.toAlgebra
  let : Algebra.IsIntegral A B := ⟨hf⟩
  refine le_antisymm ?_ hf.ringKrullDim_le
  change Order.krullDim (PrimeSpectrum A) ≤ _
  -- Unlike the nonempty-spectrum reformulation, this supremum also covers bottom.
  refine iSup_le fun l => ?_
  obtain ⟨P, hP⟩ := hf.comap_surjective hinj l.head
  have : P.asIdeal.LiesOver l.head.asIdeal := ⟨by
    change l.head.asIdeal = Ideal.comap f P.asIdeal
    exact congrArg PrimeSpectrum.asIdeal hP.symm⟩
  obtain ⟨L, hL, _, _⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P.asIdeal
  rw [← hL]
  exact Order.LTSeries.length_le_krullDim L

/-- The dimension of the target of an integral homomorphism equals the dimension
of the source modulo its kernel. This includes bottom for a zero target and top
for infinite dimension. Mathlib's integral, injective `RingHom.kerLift` reduces
this form to dimension invariance under injective integral homomorphisms. -/
theorem ringKrullDim_eq_quotient_ker {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    {f : R →+* S} (hf : f.IsIntegral) :
    ringKrullDim S = ringKrullDim (R ⧸ RingHom.ker f) := by
  exact (hf.kerLift.ringKrullDim_eq (RingHom.kerLift_injective f)).symm

end RingHom.IsIntegral

namespace Algebra.IsIntegral

/-- A faithful integral algebra has the same Krull dimension as its base ring,
including bottom for the zero ring and top for infinite dimension. The map is
that of the given algebra structure; Mathlib's `algebraMap_isIntegral_iff` and
`FaithfulSMul.algebraMap_injective` connect its hypotheses to the ring-map form. -/
theorem ringKrullDim_eq (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.IsIntegral R S] [FaithfulSMul R S] :
    ringKrullDim R = ringKrullDim S := by
  exact RingHom.IsIntegral.ringKrullDim_eq
    (algebraMap_isIntegral_iff.mpr (inferInstance : Algebra.IsIntegral R S))
    (FaithfulSMul.algebraMap_injective R S)

end Algebra.IsIntegral
