/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MinimalPrimes.Order.Filter.Product
public import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Reducedness of dependent filter products

A dependent filter product of monoids with zero is reduced exactly when the
reduced fibres form a member of the filter. The criterion allows arbitrary
filters, independently universed fibres and trivial monoids.

The proof uses the fixed-square characterization of reducedness. Choosing
square-zero witnesses on the nonreduced fibres avoids interchanging an
unbounded nilpotence exponent with eventual equality.

## References

The uniform square criterion is Mathlib's `isReduced_iff_pow_one_lt` at exponent
two. The quotient and its characteristic representative API are those of
`Filter.Product`.
-/

@[expose] public section

universe u v

namespace Filter.Product

variable {ι : Type u} {D : Filter ι} {R : ι → Type v}
variable [∀ i, MonoidWithZero (R i)]

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
    refine (isReduced_iff_pow_one_lt 2 one_lt_two).2 ?_
    intro q
    refine Quotient.inductionOn q ?_
    intro f hf
    have he' : π (f ^ 2) = π 0 := by
      calc
        π (f ^ 2) = (π f) ^ 2 := map_pow π f 2
        _ = 0 := hf
        _ = π 0 := hzero.symm
    have he : ∀ᶠ i in D, f i ^ 2 = 0 := (coe_eq (f ^ 2) 0).1 he'
    have hz : ∀ᶠ i in D, f i = 0 := (h.and he).mono fun i hi =>
      (isReduced_iff_pow_one_lt 2 one_lt_two).1 hi.1 _ hi.2
    exact ((coe_eq f 0).2 hz).trans hzero

end Filter.Product
