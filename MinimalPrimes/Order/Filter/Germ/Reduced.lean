/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Order.Filter.Germ.Basic

/-!
# Reducedness of filter germs

For a fixed value type with zero and natural-number powers, its germ is reduced
exactly when the value type is reduced eventually. Equivalently, the filter is
improper or the value type is reduced. No power laws or multiplication are needed.

A representative is nilpotent in the germ precisely when one natural-number
exponent makes its power zero on a filter-large set. This does not mean merely
that its values are eventually nilpotent with possibly different exponents.

## References

This uses Mathlib's filter-germ API of Yury Kudryashov and Abhimanyu Pallavi Sudhir,
and the nilpotence and reducedness definitions in `Mathlib.Algebra.GroupWithZero.Basic`.
-/

@[expose] public section

universe u v

namespace Filter.Germ

variable {ι : Type u} {M : Type v} [Zero M] [Pow M ℕ]

/-- A representative is nilpotent in the germ exactly when one exponent makes
its power zero eventually. The exponent may be zero. -/
@[simp]
theorem isNilpotent_coe_iff (D : Filter ι) (f : ι → M) :
    IsNilpotent (f : Germ D M) ↔ ∃ n : ℕ, ∀ᶠ i in D, f i ^ n = 0 := by
  simp only [IsNilpotent, ← coe_pow, ← coe_zero, coe_eq]
  rfl

/-- A constant-fibre germ is reduced exactly when its value type is reduced
on a filter-large set. This includes the improper filter and empty index types. -/
theorem isReduced_iff_eventually (D : Filter ι) :
    IsReduced (Germ D M) ↔ ∀ᶠ _ : ι in D, IsReduced M := by
  constructor
  · intro h
    classical
    by_cases hD : D = ⊥
    · subst D
      exact eventually_bot
    · let _ : NeBot D := ⟨hD⟩
      let _ : IsReduced (Germ D M) := h
      have hM : IsReduced M := by
        constructor
        intro x hx
        obtain ⟨n, hn⟩ := hx
        have hx' : IsNilpotent (const (l := D) x) :=
          (isNilpotent_coe_iff D (fun _ : ι => x)).2
            ⟨n, Eventually.of_forall fun _ => hn⟩
        exact const_inj.mp hx'.eq_zero
      exact Eventually.of_forall fun _ => hM
  · intro h
    constructor
    intro g
    refine inductionOn g ?_
    intro f hf
    obtain ⟨n, hn⟩ := (isNilpotent_coe_iff D f).1 hf
    apply coe_eq.mpr
    exact (h.and hn).mono fun i hi => by
      let _ := hi.1
      exact eq_zero_of_pow_eq_zero hi.2

/-- A germ is reduced iff the filter is bottom or its value type is reduced. -/
theorem isReduced_iff_eq_bot_or (D : Filter ι) :
    IsReduced (Germ D M) ↔ D = ⊥ ∨ IsReduced M := by
  rw [isReduced_iff_eventually]
  constructor
  · intro h
    classical
    by_cases hM : IsReduced M
    · exact Or.inr hM
    · exact Or.inl (eventually_false_iff_eq_bot.mp (h.mono fun _ hi => hM hi))
  · rintro (rfl | hM)
    · exact eventually_bot
    · exact Eventually.of_forall fun _ => hM

/-- Germs with reduced coefficients are reduced, for every filter. -/
instance instIsReduced (D : Filter ι) [IsReduced M] : IsReduced (Germ D M) :=
  (isReduced_iff_eventually D).2 (Eventually.of_forall fun _ => inferInstance)

/-- At a proper filter, reducedness of germs detects reducedness of the value type. -/
@[simp]
theorem isReduced_iff (D : Filter ι) [NeBot D] :
    IsReduced (Germ D M) ↔ IsReduced M :=
  (isReduced_iff_eventually D).trans eventually_const

end Filter.Germ
