/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Group.Action.Faithful
public import Mathlib.RingTheory.Ideal.Maps
public import MinimalPrimes.Order.Filter.Product.Module

/-!
# Annihilators and faithful actions on dependent reduced products

The annihilator membership criterion concerns the whole reduced-product semimodule
with its given fibre actions. The faithfulness criterion compares two scalars on
all vectors, rather than testing injectivity of the action of a fixed scalar.
The module criteria use the named semimodule over the existing scalar semiring and
the named vector additive monoid, retaining the given structure records on each fibre.
The named-action faithfulness criterion needs only scalar and vector zeros and the
given fibre scalar actions. The zeros supply total sections, without requiring
preservation of zero by the actions.

These criteria allow arbitrary filters, including the bottom filter, and independent
scalar and vector universes. No additive inverses or commutativity of scalars are
required. At the semiring level, a zero annihilator does not characterize faithful
scalar action.

Equality of represented actions is detected by testing every total vector section
and applying the existing quantified-section reflection theorem. Stock annihilator
membership uses the same representative action and the zero of the named additive
record. For faithfulness, the existing eventual-equality reflection theorem applies
to fibre action functions. Its empty-total-scalar-section alternative is excluded
by the scalar-zero section; fibre injectivity is precisely `FaithfulSMul`.

## References

The annihilator and faithful-action interfaces are Mathlib's
`Mathlib.RingTheory.Ideal.Maps` and `Mathlib.Algebra.Group.Action.Faithful`.
The dependent semimodule and quantified-section interfaces are those of
`MinimalPrimes.Order.Filter.Product.Module` and `MinimalPrimes.Order.Filter.Basic`.
-/

@[expose] public section

universe u v w

namespace Filter.Product

variable {ι : Type u} (F : Filter ι) (R : ι → Type v) (M : ι → Type w)

/-- The binary quotient action is faithful exactly when the given fibre actions are
faithful eventually. Scalar and vector zeros supply total sections; the actions
need not preserve zero. -/
theorem faithfulSMul_smul_iff [zR : ∀ i, Zero (R i)] [zM : ∀ i, Zero (M i)]
    [σ : ∀ i, SMul (R i) (M i)] :
    @FaithfulSMul (F.Product R) (F.Product M) (@smul ι F M R σ) ↔
      ∀ᶠ i in F, @FaithfulSMul (R i) (M i) (σ i) := by
  let := @smul ι F M R σ
  have hfibre (i : ι) :
      Function.Injective (fun r : R i => fun m : M i => r • m) ↔
        FaithfulSMul (R i) (M i) := by
    constructor
    · intro h
      exact ⟨fun hrt => h (funext hrt)⟩
    · intro h
      let := h
      exact smul_left_injective'
  have hcriterion := forall_eventually_eq_of_map_eq_iff F
    (fun i (r : R i) => fun m : M i => r • m)
  constructor
  · intro h
    have hsections : ∀ r t : ∀ i, R i,
        (∀ᶠ i in F, (fun m : M i => r i • m) = (fun m : M i => t i • m)) →
          ∀ᶠ i in F, r i = t i := by
      intro r t hrt
      apply (coe_eq (F := F) r t).mp
      exact h.eq_of_smul_eq_smul (congrFun
        ((smul_coe_eq_smul_coe_iff F M R r t).mpr
          (hrt.mono fun i hi m => congrFun hi m)))
    rcases hcriterion.mp hsections with hempty | hinj
    · exact (hempty.false (fun _ => 0)).elim
    · exact hinj.mono fun i hi => (hfibre i).mp hi
  · intro h
    have hsections := hcriterion.mpr
      (Or.inr (h.mono fun i hi => (hfibre i).mpr hi))
    constructor
    intro r t hrt
    obtain ⟨r, rfl⟩ := coe_surjective F R r
    obtain ⟨t, rfl⟩ := coe_surjective F R t
    apply (coe_eq (F := F) r t).mpr
    apply hsections r t
    exact ((smul_coe_eq_smul_coe_iff F M R r t).mp
      (funext hrt)).mono fun i hi => funext hi

variable [s : ∀ i, Semiring (R i)] [a : ∀ i, AddCommMonoid (M i)]
    [p : ∀ i, Module (R i) (M i)]

/-- A represented scalar annihilates the whole reduced-product semimodule exactly
when it annihilates each fibre semimodule eventually, for the given fibre modules. -/
theorem coe_mem_annihilator_iff (r : ∀ i, R i) :
    (r : F.Product R) ∈
      @Module.annihilator (F.Product R) (F.Product M)
        (@instSemiring ι F R s) (@addCommMonoid ι F M a)
        (module (s := s) (a := a) (p := p) F M R) ↔
      ∀ᶠ i in F,
        r i ∈ @Module.annihilator (R i) (M i) (s i) (a i) (p i) := by
  let := @addCommMonoid ι F M a
  let := module (s := s) (a := a) (p := p) F M R
  constructor
  · intro h
    have hzero := (Module.mem_annihilator
      (R := F.Product R) (M := F.Product M)).mp h
    have hfibre : ∀ᶠ i in F, ∀ m : M i, r i • m = 0 := by
      apply (eventually_forall_iff_forall_section (fun i => (0 : M i))).mpr
      intro m
      apply (coe_eq (F := F) (fun i => r i • m i) (fun _ => 0)).mp
      exact (coe_smul F M R r m).symm.trans
        ((hzero (m : F.Product M)).trans (coe_zero_add F M).symm)
    exact hfibre.mono fun i hi => Module.mem_annihilator.mpr hi
  · intro h
    apply (Module.mem_annihilator (R := F.Product R) (M := F.Product M)).mpr
    intro x
    obtain ⟨m, rfl⟩ := coe_surjective F M x
    exact (coe_smul F M R r m).trans
      (((coe_eq (F := F) _ _).mpr
        (h.mono fun i hi => Module.mem_annihilator.mp hi (m i))).trans
          (coe_zero_add F M))

/-- The given reduced-product semimodule action is faithful exactly when the given
fibre semimodule actions are faithful eventually. -/
theorem faithfulSMul_iff :
    @FaithfulSMul (F.Product R) (F.Product M)
      (module (s := s) (a := a) (p := p) F M R).toSMul ↔
      ∀ᶠ i in F, @FaithfulSMul (R i) (M i) (p i).toSMul := by
  simpa only [module_toSMul] using
    (faithfulSMul_smul_iff F R M
      (zR := fun i => (s i).toZero) (zM := fun i => (a i).toZero)
      (σ := fun i => (p i).toSMul))

end Filter.Product
