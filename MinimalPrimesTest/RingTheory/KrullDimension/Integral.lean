/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import MinimalPrimes.RingTheory.KrullDimension.Integral
import Mathlib.Algebra.Algebra.Prod
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.RingTheory.Ideal.Prod
import Mathlib.RingTheory.KrullDimension.PID

/-!
# Integral dimension on an integer diagonal

The family is the canonical algebra map `ℤ →+* ℤ × ℤ`, taking `n` to `(n, n)`.
Finite generation of the product module gives integrality, and the faithful
coordinate action gives injectivity. Neither hypothesis uses dimension equality.

Independently, `ℤ` has dimension one because it is a principal ideal domain but
not a field. The product is a principal ideal ring, so has dimension at most one;
its surjective first projection gives the reverse bound. These arguments do not
use any integral-dimension theorem. The target is not a domain:
`(1, 0) * (0, 1) = 0` with both factors nonzero. The diagonal is not surjective,
since `(0, 1)` is not in its image, so it is not a ring isomorphism.

The total quotient of `ℤ` supplies a noninjective integral map with total kernel
and target dimension bottom, in contrast to the source's dimension one. The same
zero ring has a faithful, injective identity map, despite its empty spectrum.
The dimension codomain in the general statements also retains infinite dimension;
no finite-dimension instance is assumed by these clients.

## References

The hypotheses and independent dimension calculations use Mathlib's
`Module.Finite.prod`, `Algebra.IsIntegral.of_finite`, `Prod.faithfulSMulLeft`,
`IsPrincipalIdealRing.ringKrullDim_eq_one`, `Int.not_isField`, the product
principal-ideal-ring instance, and `ringKrullDim_le_of_surjective`.
-/

private theorem integer_dimension : ringKrullDim ℤ = 1 :=
  IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField

private theorem product_dimension : ringKrullDim (ℤ × ℤ) = 1 := by
  apply le_antisymm
  · simpa only [Nat.cast_one] using
      (Ring.krullDimLE_iff (R := ℤ × ℤ) (n := 1)).mp inferInstance
  · rw [← integer_dimension]
    exact ringKrullDim_le_of_surjective (RingHom.fst ℤ ℤ) Prod.fst_surjective

example : Module.Finite ℤ (ℤ × ℤ) := inferInstance

example : FaithfulSMul ℤ (ℤ × ℤ) := inferInstance

private theorem diagonal_integral : (algebraMap ℤ (ℤ × ℤ)).IsIntegral :=
  algebraMap_isIntegral_iff.mpr (inferInstance : Algebra.IsIntegral ℤ (ℤ × ℤ))

private theorem diagonal_injective : Function.Injective (algebraMap ℤ (ℤ × ℤ)) :=
  FaithfulSMul.algebraMap_injective ℤ (ℤ × ℤ)

-- The positive dimension calculations precede, and do not use, these API applications.
example : ringKrullDim (ℤ × ℤ) =
    ringKrullDim (ℤ ⧸ RingHom.ker (algebraMap ℤ (ℤ × ℤ))) :=
  diagonal_integral.ringKrullDim_eq_quotient_ker

example : ringKrullDim ℤ = ringKrullDim (ℤ × ℤ) :=
  Algebra.IsIntegral.ringKrullDim_eq ℤ (ℤ × ℤ)

-- The injective endpoint is reused under its existing name, without an alias.
example : ringKrullDim ℤ = ringKrullDim (ℤ × ℤ) :=
  diagonal_integral.ringKrullDim_eq diagonal_injective

example : RingHom.ker (algebraMap ℤ (ℤ × ℤ)) = ⊥ :=
  (RingHom.injective_iff_ker_eq_bot _).mp diagonal_injective

example :
    (Ideal.Quotient.mk (⊤ : Ideal ℤ)).IsIntegral ∧
    RingHom.ker (Ideal.Quotient.mk (⊤ : Ideal ℤ)) = ⊤ ∧
    ringKrullDim (ℤ ⧸ (⊤ : Ideal ℤ)) = ⊥ := by
  exact ⟨RingHom.isIntegral_of_surjective _ Ideal.Quotient.mk_surjective,
    Ideal.mk_ker, ringKrullDim_eq_bot_of_subsingleton⟩

example : ringKrullDim (ℤ ⧸ RingHom.ker (Ideal.Quotient.mk (⊤ : Ideal ℤ))) = ⊥ := by
  rw [Ideal.mk_ker]
  exact ringKrullDim_eq_bot_of_subsingleton

example :
    (RingHom.id (ℤ ⧸ (⊤ : Ideal ℤ))).IsIntegral ∧
    FaithfulSMul (ℤ ⧸ (⊤ : Ideal ℤ)) (ℤ ⧸ (⊤ : Ideal ℤ)) ∧
    Function.Injective (RingHom.id (ℤ ⧸ (⊤ : Ideal ℤ))) ∧
    ringKrullDim (ℤ ⧸ (⊤ : Ideal ℤ)) = ⊥ := by
  exact ⟨RingHom.isIntegral_of_surjective _ Function.surjective_id,
    inferInstance, Function.injective_id, ringKrullDim_eq_bot_of_subsingleton⟩
