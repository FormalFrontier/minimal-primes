/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MinimalPrimes.RingTheory.Spectrum.Prime.PiUltrafilter
public import Mathlib.Algebra.Field.Rat

/-!
# Stone topology through the product-spectrum interface

The algebraic examples already cover the empty index and distinct heterogeneous
coordinate kernels. Here a two-point product of non-ring semifields has a basic
open isolating a specified coordinate. For an infinite product of the same non-ring
semifield, the cofinite prime is not isolated: its every basic neighborhood contains
a coordinate point. Thus the canonical topology is not discrete on all primes.
-/

@[expose] public section

open Set Filter PrimeSpectrum

example :
    (piHomeomorphUltrafilter (fun _ : Bool ↦ ℚ≥0)).symm ⁻¹'
        (basicOpen (fun b : Bool ↦ if b then (0 : ℚ≥0) else 1) :
          Set (PrimeSpectrum (Bool → ℚ≥0))) =
      {pure false} := by
  rw [piHomeomorphUltrafilter_symm_preimage_basicOpen]
  have hs : {b : Bool | (if b then (0 : ℚ≥0) else 1) ≠ 0} = {false} := by
    ext b
    cases b <;> simp
  rw [hs]
  ext U
  change ({false} : Set Bool) ∈ U ↔ U = pure false
  constructor
  · intro h
    obtain ⟨b, hb, hU⟩ := Ultrafilter.eq_pure_of_finite_mem (finite_singleton false) h
    have hb' : b = false := mem_singleton_iff.mp hb
    simpa only [hb'] using hU
  · rintro rfl
    simp

example :
    ¬IsOpen ({(piHomeomorphUltrafilter (fun _ : ℕ ↦ ℚ≥0)).symm (Filter.hyperfilter ℕ)} :
      Set (PrimeSpectrum (ℕ → ℚ≥0))) := by
  intro h
  have he : (piHomeomorphUltrafilter (fun _ : ℕ ↦ ℚ≥0)).symm ⁻¹'
      {(piHomeomorphUltrafilter (fun _ : ℕ ↦ ℚ≥0)).symm (Filter.hyperfilter ℕ)} =
        {Filter.hyperfilter ℕ} := by
    ext U
    simp
  have ho : IsOpen ({Filter.hyperfilter ℕ} : Set (Ultrafilter ℕ)) := by
    rw [← he]
    exact h.preimage (piHomeomorphUltrafilter (fun _ : ℕ ↦ ℚ≥0)).symm.continuous
  obtain ⟨_, ⟨s, rfl⟩, hs, hsub⟩ :=
    ultrafilterBasis_is_basis.exists_subset_of_mem_open
      (by simp : Filter.hyperfilter ℕ ∈ ({Filter.hyperfilter ℕ} : Set (Ultrafilter ℕ))) ho
  obtain ⟨n, hn⟩ := Ultrafilter.nonempty_of_mem hs
  have hnp : (pure n : Ultrafilter ℕ) = Filter.hyperfilter ℕ :=
    mem_singleton_iff.mp (hsub (by simpa using hn))
  have hmem : ({n} : Set ℕ) ∈ Filter.hyperfilter ℕ := by
    rw [← hnp]
    simp
  exact Filter.notMem_hyperfilter_of_finite (finite_singleton n) hmem
