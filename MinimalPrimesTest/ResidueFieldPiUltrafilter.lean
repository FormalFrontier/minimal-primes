/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MinimalPrimes.RingTheory.Ideal.ResidueFieldPiUltrafilter
public import Mathlib.Algebra.CharP.Basic
public import Mathlib.Algebra.Field.ZMod

/-!
# Controls for the dependent residue comparison

At a principal ultrafilter the comparison detects vanishing at the selected
coordinate. A genuinely dependent family with fibres of characteristics two and
three has residue fields of those same, distinct characteristics. The computation
uses the stock coordinate kernel and residue algebra map, not a common ambient
field or another reduced-product carrier.
-/

public section

open Filter

universe u v

namespace DependentResidueControls

section Principal

variable {ι : Type u} (K : ι → Type v) [∀ i, Field (K i)]

example (i : ι) :
    (pure i : Ultrafilter ι).piIdeal K = RingHom.ker (Pi.evalRingHom K i) :=
  Ultrafilter.piIdeal_pure K i

/-- The canonical principal comparison has exactly the selected coordinate kernel. -/
theorem comparison_pure_eq_zero_iff (i : ι) (r : ∀ i, K i) :
    Ultrafilter.residueFieldProductEquiv K (pure i)
      (algebraMap _ ((pure i : Ultrafilter ι).piIdeal K).ResidueField r) = 0 ↔
        r i = 0 := by
  have hzero :
      Ultrafilter.residueFieldProductEquiv K (pure i)
        (algebraMap _ ((pure i : Ultrafilter ι).piIdeal K).ResidueField r) = 0 ↔
          algebraMap _ ((pure i : Ultrafilter ι).piIdeal K).ResidueField r = 0 := by
    constructor
    · intro h
      apply (Ultrafilter.residueFieldProductEquiv K (pure i)).injective
      simpa only [map_zero] using h
    · intro h
      rw [h, map_zero]
  rw [hzero, Ideal.algebraMap_residueField_eq_zero, Ultrafilter.piIdeal_pure]
  simp [RingHom.mem_ker]

end Principal

private def mixedField : Bool → Type
  | false => ZMod 2
  | true => ZMod 3

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

private instance (b : Bool) : Field (mixedField b) := by
  cases b <;> dsimp [mixedField] <;> infer_instance

private abbrev ResidueAt (b : Bool) :=
  ((pure b : Ultrafilter Bool).piIdeal mixedField).ResidueField

private theorem natCast_eq_zero_iff (b : Bool) (n : ℕ) :
    (n : ResidueAt b) = 0 ↔ (n : mixedField b) = 0 := by
  rw [← map_natCast (algebraMap (∀ b, mixedField b) (ResidueAt b)) n,
    Ideal.algebraMap_residueField_eq_zero]
  simp only [Ultrafilter.piIdeal_pure, RingHom.mem_ker, map_natCast]

example : ringChar (ResidueAt false) = 2 := by
  apply CharP.ringChar_of_prime_eq_zero Nat.prime_two
  exact (natCast_eq_zero_iff false 2).2 (by
    change (2 : ZMod 2) = 0
    decide)

example : ringChar (ResidueAt true) = 3 := by
  apply CharP.ringChar_of_prime_eq_zero Nat.prime_three
  exact (natCast_eq_zero_iff true 3).2 (by
    change (3 : ZMod 3) = 0
    decide)

example : (2 : ResidueAt true) ≠ 0 := by
  intro h
  have hv := (natCast_eq_zero_iff true 2).1 h
  exact (by decide : (2 : ZMod 3) ≠ 0) hv

example : (3 : ResidueAt false) ≠ 0 := by
  intro h
  have hv := (natCast_eq_zero_iff false 3).1 h
  exact (by decide : (3 : ZMod 2) ≠ 0) hv

end DependentResidueControls
