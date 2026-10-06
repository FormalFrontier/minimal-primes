/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MinimalPrimes.AssociatedRestrictScalars
import Mathlib.RingTheory.Ideal.Prod
import Mathlib.Algebra.Algebra.Prod
import Mathlib.Data.Rat.Defs

/-!
# Restriction-of-scalars examples

For the diagonal map from `ℚ` into `ℚ × ℚ`, let the product act on `ℚ`
through the first projection. The two coordinate prime ideals have the same
contraction, but only the kernel of the first projection is associated.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.mathlibStandardSet true
set_option linter.style.header false

@[expose] public section

universe u v w

namespace MinimalPrimesTest

private theorem colon_restrictScalars_annihilator
    {R : Type u} {S : Type v} {M : Type w}
    [CommSemiring R] [Semiring S] [Algebra R S]
    [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower R S M] :
    (Module.annihilator S M).comap (algebraMap R S) = Module.annihilator R M ∧
      (Module.annihilator S M).comap (algebraMap R S) =
        (⊥ : Submodule R M).colon (Set.univ : Set M) := by
  have hTarget : (⊥ : Submodule S M).colon (Set.univ : Set M) =
      Module.annihilator S M := by
    simpa only [Submodule.top_coe, Submodule.annihilator_top] using
      (Submodule.bot_colon (N := (⊤ : Submodule S M)))
  have hSource : (⊥ : Submodule R M).colon (Set.univ : Set M) =
      Module.annihilator R M := by
    rw [Submodule.bot_colon', Submodule.span_univ, Submodule.annihilator_top]
  constructor
  · calc
      (Module.annihilator S M).comap (algebraMap R S) =
          ((⊥ : Submodule S M).colon (Set.univ : Set M)).comap
            (algebraMap R S) := by rw [hTarget]
      _ = (⊥ : Submodule R M).colon (Set.univ : Set M) := by
        simpa only [Submodule.restrictScalars_bot] using
          (Submodule.colon_restrictScalars (R := R)
            (N := (⊥ : Submodule S M)) (Set.univ : Set M)).symm
      _ = Module.annihilator R M := hSource
  · calc
      (Module.annihilator S M).comap (algebraMap R S) =
          Module.annihilator R M := Module.comap_annihilator
      _ = (⊥ : Submodule R M).colon (Set.univ : Set M) := hSource.symm

scoped instance firstProjectionModule : Module (ℚ × ℚ) ℚ :=
  Module.compHom ℚ (RingHom.fst ℚ ℚ)

scoped instance firstProjectionTower : IsScalarTower ℚ (ℚ × ℚ) ℚ :=
  IsScalarTower.of_algebraMap_smul (fun scalar witness => by
    change scalar * witness = scalar * witness
    rfl)

private theorem first_projection_colon_one :
    (⊥ : Submodule (ℚ × ℚ) ℚ).colon {(1 : ℚ)} =
      Ideal.prod (⊥ : Ideal ℚ) (⊤ : Ideal ℚ) := by
  ext ⟨first, second⟩
  simp only [Submodule.mem_colon_singleton, Submodule.mem_bot, Ideal.mem_prod,
    Submodule.mem_bot, Submodule.mem_top, and_true]
  change first * 1 = 0 ↔ first = 0
  simp

private theorem first_projection_module_annihilator_comap :
    (Module.annihilator (ℚ × ℚ) ℚ).comap (algebraMap ℚ (ℚ × ℚ)) =
      (⊥ : Ideal ℚ) := by
  rw [(colon_restrictScalars_annihilator (R := ℚ) (S := ℚ × ℚ) (M := ℚ)).1]
  ext scalar
  rw [Module.mem_annihilator]
  constructor
  · intro h
    simpa using h (1 : ℚ)
  · rintro rfl witness
    simp

private theorem diagonal_other_comap :
    (Ideal.prod (⊤ : Ideal ℚ) (⊥ : Ideal ℚ)).comap
      (algebraMap ℚ (ℚ × ℚ)) = ⊥ := by
  ext scalar
  simp [Ideal.mem_comap, Ideal.mem_prod]

theorem diagonal_base_associated_other_not :
    (Ideal.prod (⊤ : Ideal ℚ) (⊥ : Ideal ℚ)).IsPrime ∧
      IsAssociatedPrime
        ((Ideal.prod (⊤ : Ideal ℚ) (⊥ : Ideal ℚ)).comap
          (algebraMap ℚ (ℚ × ℚ))) ℚ ∧
      ¬ IsAssociatedPrime (Ideal.prod (⊤ : Ideal ℚ) (⊥ : Ideal ℚ)) ℚ := by
  refine ⟨Ideal.isPrime_ideal_prod_top', ?_, ?_⟩
  · rw [diagonal_other_comap]
    refine ⟨inferInstance, ⟨1, ?_⟩⟩
    have hAnn : (⊥ : Submodule ℚ ℚ).colon {(1 : ℚ)} = ⊥ := by
      ext scalar
      simp [Submodule.mem_colon_singleton]
    rw [hAnn]
    exact (inferInstance : (⊥ : Ideal ℚ).IsPrime).radical.symm
  · rintro ⟨_, ⟨witness, hWitness⟩⟩
    have hMem : ((0, 1) : ℚ × ℚ) ∈ Ideal.prod (⊤ : Ideal ℚ) (⊥ : Ideal ℚ) := by
      rw [hWitness]
      apply Ideal.le_radical
      rw [Submodule.mem_colon_singleton, Submodule.mem_bot]
      change (0 : ℚ) * witness = 0
      simp
    simp at hMem

private theorem diagonal_not_surjective :
    ¬ Function.Surjective (algebraMap ℚ (ℚ × ℚ)) := by
  intro hSurj
  obtain ⟨scalar, hScalar⟩ := hSurj ((0, 1) : ℚ × ℚ)
  have hZero : scalar = 0 := by
    have h := congrArg Prod.fst hScalar
    simpa using h
  have hOne : scalar = 1 := by
    have h := congrArg Prod.snd hScalar
    simpa using h
  exact zero_ne_one (hZero.symm.trans hOne)

private theorem first_projection_associated_contracts :
    IsAssociatedPrime
      ((Ideal.prod (⊥ : Ideal ℚ) (⊤ : Ideal ℚ)).comap
        (algebraMap ℚ (ℚ × ℚ))) ℚ := by
  have hPrime : (Ideal.prod (⊥ : Ideal ℚ) (⊤ : Ideal ℚ)).IsPrime :=
    Ideal.isPrime_ideal_prod_top
  exact IsAssociatedPrime.comap_algebraMap
    ⟨hPrime, ⟨1, by rw [first_projection_colon_one, hPrime.radical]⟩⟩

end MinimalPrimesTest
