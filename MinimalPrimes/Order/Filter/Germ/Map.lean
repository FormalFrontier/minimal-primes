/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Order.Filter.Germ.Basic
public import MinimalPrimes.Order.Filter.Basic

/-!
# Varying application and pointed fibres on germs

A family of functions acts on Mathlib's existing germs by `Filter.Germ.map₂` specialized
to evaluation. This action is injective exactly when the functions are eventually
injective. It reflects a specified constant germ if the coordinate functions eventually
reflect the specified points; the converse requires only eventual point preservation.
The filters and universes are arbitrary. No properness assumption is needed.

## References

The carrier, quotient induction, evaluation and eventual-equality interfaces are
Mathlib's filter-germ API, formalized by Yury Kudryashov and Abhimanyu Pallavi Sudhir.
The pointed-fibre argument generalizes the annihilator witnesses in
`MinimalPrimes.Order.Filter.Germ.NonZeroDivisors`. Its criterion is now the
constant-family bridge to the dependent selected-section criterion in
`MinimalPrimes.Order.Filter.Basic`.
-/

@[expose] public section

universe u v w z

namespace Filter.Germ

variable {ι : Type u} {A : Type v} {B : Type w}

/-- Varying pointwise application on germs is injective exactly when the functions are
injective eventually. This includes empty types and the improper filter. -/
theorem injective_map₂_apply_coe_iff (D : Filter ι) (F : ι → A → B) :
    Function.Injective
      (map₂ (fun (φ : A → B) (a : A) => φ a) (F : Germ D (A → B))) ↔
      ∀ᶠ i in D, Function.Injective (F i) := by
  constructor
  · intro h
    have hreflect := (Filter.forall_eventually_eq_of_map_eq_iff D F).1
      (fun a b hab => coe_eq.mp (h (by
        simpa only [map₂_coe, coe_eq, Filter.EventuallyEq] using hab)))
    rcases hreflect with hempty | hF
    · exact Eventually.of_forall fun _ a _ _ => (hempty.false (fun _ => a)).elim
    · exact hF
  · intro h x y
    refine inductionOn₂ x y ?_
    intro a b hab
    apply coe_eq.mpr
    apply (Filter.forall_eventually_eq_of_map_eq_iff D F).2 (Or.inr h) a b
    simpa only [map₂_coe, coe_eq, Filter.EventuallyEq] using hab

/-- Evaluation after mapping a curried operation agrees with its binary germ map. -/
theorem map₂_apply_map {C : Type z} (D : Filter ι) (op : A → B → C)
    (a : Germ D A) (b : Germ D B) :
    map₂ (fun (φ : B → C) (x : B) => φ x) (map op a) b = map₂ op a b := by
  exact inductionOn₂ a b fun _ _ => rfl

/-- Binary mapping of multiplication agrees with the stock product of germs. -/
@[simp]
theorem map₂_mul [Mul A] (D : Filter ι) (x y : Germ D A) :
    map₂ (fun (a b : A) => a * b) x y = x * y := by
  refine inductionOn₂ x y ?_
  intro f g
  rw [map₂_coe, ← coe_mul]
  rfl

/-- Equality of a represented germ with a constant is eventual equality to that point. -/
@[simp]
theorem coe_eq_const (D : Filter ι) (f : ι → A) (a : A) :
    (f : Germ D A) = const a ↔ ∀ᶠ i in D, f i = a := by
  change (f : Germ D A) = ((fun _ : ι => a) : Germ D A) ↔ _
  exact coe_eq

/-- The constant zero germ agrees with the stock zero on germs. -/
@[simp]
theorem const_zero [Zero A] (D : Filter ι) :
    const (0 : A) = (0 : Germ D A) := by
  change ((fun _ : ι => (0 : A)) : Germ D A) = 0
  exact coe_zero

/-- Eventual reflection of a pointed fibre implies reflection of the constant germs.
No point-preservation law is needed in this direction. -/
theorem forall_map₂_apply_eq_const_imp_of_eventually (D : Filter ι)
    (F : ι → A → B) (a₀ : A) (b₀ : B)
    (h : ∀ᶠ i in D, ∀ a, F i a = b₀ → a = a₀) :
    ∀ x : Germ D A,
      map₂ (fun (φ : A → B) (a : A) => φ a) (F : Germ D (A → B)) x = const b₀ →
        x = const a₀ := by
  intro x
  refine inductionOn x ?_
  intro g hg
  apply (coe_eq_const D g a₀).mpr
  have heq : ∀ᶠ i in D, F i (g i) = b₀ := by
    simpa only [map₂_coe, coe_eq_const] using hg
  exact (h.and heq).mono fun _ hi => hi.1 _ hi.2

/-- Under eventual point preservation, varying application reflects a constant germ
exactly when the coordinate functions eventually reflect that point. -/
theorem forall_map₂_apply_eq_const_imp_iff (D : Filter ι) (F : ι → A → B)
    (a₀ : A) (b₀ : B) (h₀ : ∀ᶠ i in D, F i a₀ = b₀) :
    (∀ x : Germ D A,
      map₂ (fun (φ : A → B) (a : A) => φ a) (F : Germ D (A → B)) x = const b₀ →
        x = const a₀) ↔ ∀ᶠ i in D, ∀ a, F i a = b₀ → a = a₀ := by
  constructor
  · intro h
    apply (Filter.forall_eventually_map_eq_imp_iff D F
      (fun _ => a₀) (fun _ => b₀) h₀).1
    intro f hf
    exact (coe_eq_const D f a₀).mp (h (f : Germ D A) (by
      simpa only [map₂_coe, coe_eq_const] using hf))
  · exact forall_map₂_apply_eq_const_imp_of_eventually D F a₀ b₀

end Filter.Germ
