/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MinimalPrimes.Order.Filter.Germ.Map

/-!
# Reflection of scalar zero fibres on germs

A fixed represented scalar reflects zero on all target germs whenever its coordinate
operators eventually reflect zero. The converse needs only eventual preservation of zero
by that same action. The weak `SMulZeroClass` specialization selects the action supplied
by that class; it needs neither scalar zero nor an additive structure.

This concerns one fixed scalar, not `NoZeroSMulDivisors` for two varying germs.

## References

The germ action and representative interfaces are Mathlib's filter-germ API by
Yury Kudryashov and Abhimanyu Pallavi Sudhir. The zero-preserving action hierarchy is
Mathlib's `Algebra.GroupWithZero.Action.Defs`, by Chris Hughes and Yury Kudryashov.
The pointed criterion is the `MinimalPrimes.Order.Filter.Germ.Map` generalization of
the existing germ witness arguments.
-/

@[expose] public section

universe u v w

namespace Filter.Germ

variable {ι : Type u} {R : Type v} {M : Type w}

private theorem map₂_apply_smul_coe [SMul R M] (D : Filter ι) (f : ι → R)
    (x : Germ D M) :
    map₂ (fun (φ : M → M) (m : M) => φ m)
      ((fun (i : ι) (m : M) => f i • m) : Germ D (M → M)) x =
        (f : Germ D R) • x := by
  refine inductionOn x ?_
  intro g
  rw [map₂_coe, ← coe_smul']
  rfl

variable [Zero M]

/-- Preservation of the zero germ by a represented scalar is exactly eventual
preservation of coordinate zero by the selected action. -/
theorem smul_coe_zero_eq_zero_iff [SMul R M] (D : Filter ι) (f : ι → R) :
    (f : Germ D R) • (0 : Germ D M) = 0 ↔ ∀ᶠ i in D, f i • (0 : M) = 0 := by
  simp only [← coe_zero, ← coe_smul', coe_eq, Filter.EventuallyEq, Pi.zero_apply]
  rfl

/-- Eventual coordinate zero-reflection implies zero-reflection by the represented scalar.
This direction does not require the action to preserve zero. -/
theorem forall_smul_coe_eq_zero_imp_of_eventually [SMul R M] (D : Filter ι) (f : ι → R)
    (h : ∀ᶠ i in D, ∀ m : M, f i • m = 0 → m = 0) :
    ∀ x : Germ D M, (f : Germ D R) • x = 0 → x = 0 := by
  simpa only [map₂_apply_smul_coe, const_zero] using
    forall_map₂_apply_eq_const_imp_of_eventually D (fun i m => f i • m) (0 : M) (0 : M) h

/-- If this represented action eventually preserves zero, zero-reflection on germs is
exactly eventual coordinate zero-reflection. -/
theorem forall_smul_coe_eq_zero_imp_iff_of_eventually_smul_zero [SMul R M]
    (D : Filter ι) (f : ι → R) (h₀ : ∀ᶠ i in D, f i • (0 : M) = 0) :
    (∀ x : Germ D M, (f : Germ D R) • x = 0 → x = 0) ↔
      ∀ᶠ i in D, ∀ m : M, f i • m = 0 → m = 0 := by
  simpa only [map₂_apply_smul_coe, const_zero] using
    forall_map₂_apply_eq_const_imp_iff D (fun i m => f i • m) (0 : M) (0 : M) h₀

/-- For the action supplied by `SMulZeroClass`, a represented scalar reflects zero on
germs exactly when its coordinate operators eventually reflect zero. -/
theorem forall_smul_coe_eq_zero_imp_iff [SMulZeroClass R M] (D : Filter ι) (f : ι → R) :
    (∀ x : Germ D M, (f : Germ D R) • x = 0 → x = 0) ↔
      ∀ᶠ i in D, ∀ m : M, f i • m = 0 → m = 0 := by
  exact forall_smul_coe_eq_zero_imp_iff_of_eventually_smul_zero D f
    (Eventually.of_forall fun i => smul_zero (f i))

end Filter.Germ
