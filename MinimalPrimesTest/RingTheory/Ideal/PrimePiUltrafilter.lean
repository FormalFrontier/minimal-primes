/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MinimalPrimes.RingTheory.Ideal.PrimePiUltrafilter
public import Mathlib.Algebra.Field.Rat

/-!
# Product-prime classification through its public API

The empty-index control needs no chosen coordinate. A heterogeneous two-factor product
includes a non-ring semifield and retains distinct coordinate labels. On the natural
numbers, coordinate unit functions witness that the cofinite prime is nonzero and differs
from every coordinate kernel; its unit function is excluded.
-/

@[expose] public section

open Set Filter

namespace PrimePiUltrafilterExamples

/-- The empty product has no prime ideals, without choosing a coordinate. -/
theorem empty_index : IsEmpty (PrimeSpectrum (Empty → ℚ≥0)) := by
  constructor
  intro p
  have h : (Set.univ : Set Empty).Nonempty :=
    Ultrafilter.nonempty_of_mem
      (f := p.piUltrafilter (fun _ : Empty => ℚ≥0)) Filter.univ_mem
  obtain ⟨i, _⟩ := h
  cases i

private instance (b : Bool) : Semifield (if b then ℚ else ℚ≥0) := by
  cases b <;> dsimp <;> infer_instance

example :
    ((PrimeSpectrum.piEquivUltrafilter (fun b : Bool => if b then ℚ else ℚ≥0)).symm
      (pure false)).asIdeal ≠
    ((PrimeSpectrum.piEquivUltrafilter (fun b : Bool => if b then ℚ else ℚ≥0)).symm
      (pure true)).asIdeal := by
  simp only [PrimeSpectrum.piEquivUltrafilter_symm_asIdeal]
  intro h
  have hb : (false : Bool) = true := Ultrafilter.pure_injective
    (PrimeSpectrum.piIdeal_injective (fun b : Bool => if b then ℚ else ℚ≥0) h)
  cases hb

example (j : ℕ) :
    let p := (PrimeSpectrum.piEquivUltrafilter (fun _ : ℕ => ℚ)).symm (Filter.hyperfilter ℕ)
    let e : ℕ → ℚ := fun n => if n = j then 1 else 0
    e ≠ 0 ∧ e ∈ p.asIdeal ∧ e ∉ RingHom.ker (Pi.evalRingHom (fun _ : ℕ => ℚ) j) ∧
      (1 : ℕ → ℚ) ∉ p.asIdeal := by
  dsimp only
  simp only [PrimeSpectrum.piEquivUltrafilter_symm_asIdeal]
  refine ⟨?_, ?_, ?_, Ideal.one_notMem _⟩
  · intro h
    have hj := congrFun h j
    simp at hj
  · apply Ultrafilter.mem_piIdeal_hyperfilter_of_finite_support
    apply (Set.finite_singleton j).subset
    intro n hn
    by_contra hnj
    change n ≠ j at hnj
    exact hn (by simp [hnj])
  · simp [RingHom.mem_ker]

end PrimePiUltrafilterExamples
