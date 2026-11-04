/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MinimalPrimes.Order.Filter.Product.Nilpotent
public import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Reducedness of dependent filter products

A dependent filter product of monoids with zero is reduced exactly when the
reduced fibres form a member of the filter. The criterion allows arbitrary
filters, independently universed fibres and trivial monoids.

A section represents a nilpotent element exactly when one uniform exponent
makes its power zero eventually. When the filter contains a finite set, this is
equivalent to eventual fibrewise nilpotence, even on an infinite index type.
The reducedness proof uses the fixed-square characterization: choosing square-zero
witnesses on the nonreduced fibres avoids interchanging an unbounded nilpotence
exponent with eventual equality.

## References

The uniform square criterion is Mathlib's `isReduced_iff_pow_one_lt` at exponent
two. The quotient, congruence transport, pointwise operations and nilpotence
predicate use Mathlib's `Filter.Product`, `Con`, `Pi` and `IsNilpotent` APIs.
The uniform-exponent criterion follows the constant-family analogue
`Filter.Germ.isNilpotent_coe_iff` in `MinimalPrimes.Order.Filter.Germ.Reduced`.
The finite-member criterion composes this uniform-exponent criterion with
`Filter.Eventually.exists_pow_eq_zero_of_finite_mem`.
-/

@[expose] public section

universe u v

namespace Filter.Product

variable {ι : Type u} {D F : Filter ι} {R : ι → Type v}
variable [∀ i, MonoidWithZero (R i)]

/-- A section represents a nilpotent element exactly when one uniform exponent
makes its power zero eventually. The exponent may be zero. -/
@[simp]
theorem isNilpotent_coe_iff (f : ∀ i, R i) :
    @IsNilpotent (F.Product R) _ _ (f : F.Product R) ↔
      ∃ n : ℕ, ∀ᶠ i in F, f i ^ n = 0 := by
  have hzero : ((0 : ∀ i, R i) : F.Product R) = (0 : F.Product R) := coe_zero
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, (coe_eq (F := F) (f ^ n) 0).1 ?_⟩
    exact (coe_pow (F := F) f n).trans (hn.trans hzero.symm)
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    exact (coe_pow (F := F) f n).symm.trans
      (((coe_eq (F := F) (f ^ n) 0).2 hn).trans hzero)

/-- If a filter contains a finite set, a section represents a nilpotent element
exactly when its values are nilpotent eventually. The index type may be infinite,
and neither the filter nor the fibres need be nontrivial. -/
theorem isNilpotent_coe_iff_of_finite_mem (f : ∀ i, R i) {s : Set ι}
    (hs : s.Finite) (hsD : s ∈ D) :
    @IsNilpotent (D.Product R) _ _ (f : D.Product R) ↔
      ∀ᶠ i in D, IsNilpotent (f i) := by
  rw [isNilpotent_coe_iff]
  constructor
  · rintro ⟨n, hn⟩
    exact hn.mono fun i hi => ⟨n, hi⟩
  · intro hf
    exact hf.exists_pow_eq_zero_of_finite_mem hs hsD

/-- On a finite index type, nilpotence of a represented section is equivalent to
eventual fibrewise nilpotence for every filter, including the bottom filter. -/
theorem isNilpotent_coe_iff_of_finite [Finite ι] (f : ∀ i, R i) :
    @IsNilpotent (D.Product R) _ _ (f : D.Product R) ↔
      ∀ᶠ i in D, IsNilpotent (f i) :=
  isNilpotent_coe_iff_of_finite_mem f Set.finite_univ Filter.univ_mem

/-- In the product at a finite principal filter, a section is nilpotent exactly
when all its values on the generating set are nilpotent. The set may be empty. -/
theorem isNilpotent_coe_principal_iff (f : ∀ i, R i) {s : Set ι} (hs : s.Finite) :
    @IsNilpotent ((Filter.principal s).Product R) _ _ (f : (Filter.principal s).Product R) ↔
      ∀ i ∈ s, IsNilpotent (f i) := by
  rw [isNilpotent_coe_iff_of_finite_mem (D := Filter.principal s) f hs (by simp),
    Filter.eventually_principal]

/-- A dependent filter product is reduced exactly when its reduced fibres form
a member of the filter. No properness or nontriviality assumption is needed. -/
theorem isReduced_iff : IsReduced (D.Product R) ↔ ∀ᶠ i in D, IsReduced (R i) := by
  classical
  let π : (∀ i, R i) →* D.Product R := coeMulHom D
  have hzero : π 0 = 0 := coe_zero
  constructor
  · intro h
    have hw (i : ι) (hi : ¬IsReduced (R i)) :
        ∃ x : R i, x ^ 2 = 0 ∧ x ≠ 0 := by
      simpa only [isReduced_iff_pow_one_lt 2 one_lt_two, not_forall,
        not_imp, exists_prop] using hi
    let f : ∀ i, R i := fun i =>
      if hi : IsReduced (R i) then 0 else Classical.choose (hw i hi)
    have hsq (i : ι) : f i ^ 2 = 0 := by
      dsimp only [f]
      split_ifs with hi
      · simp
      · exact (Classical.choose_spec (hw i hi)).1
    have hsq' : (π f) ^ 2 = 0 := by
      calc
        (π f) ^ 2 = π (f ^ 2) := (map_pow π f 2).symm
        _ = π 0 := (coe_eq (f ^ 2) 0).2 (Eventually.of_forall hsq)
        _ = 0 := hzero
    have hz : π f = 0 := (isReduced_iff_pow_one_lt 2 one_lt_two).1 h _ hsq'
    have he : ∀ᶠ i in D, f i = 0 := (coe_eq f 0).1 (hz.trans hzero.symm)
    exact he.mono fun i hi => by
      by_contra hbad
      have hn : f i ≠ 0 := by
        simpa only [f, dite_eq_right hbad] using (Classical.choose_spec (hw i hbad)).2
      exact hn hi
  · intro h
    constructor
    intro q
    refine Quotient.inductionOn q ?_
    intro f hf
    obtain ⟨n, hn⟩ := (isNilpotent_coe_iff f).1 hf
    have hz : ∀ᶠ i in D, f i = 0 := (h.and hn).mono fun i hi => by
      let _ := hi.1
      exact eq_zero_of_pow_eq_zero hi.2
    exact ((coe_eq f 0).2 hz).trans hzero

end Filter.Product
