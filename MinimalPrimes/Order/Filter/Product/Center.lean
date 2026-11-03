/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.GroupTheory.Submonoid.Center
public import MinimalPrimes.Order.Filter.Center
public import MinimalPrimes.Order.Filter.Product

/-!
# Centers of dependent filter products

A section represents a central element of a dependent filter product exactly when
it is central eventually. Centrality includes commutation and both associativity
laws, so the criterion needs only multiplication, not associativity.

`centerEquiv` identifies the product of the fibre centers with the center of the
product, using only a two-sided unit in each fibre. Its forward map forgets the
subtype pointwise. `centerRepresentative` selects a total center-valued section
representing the inverse; only its product class, not its values at ignored
indices, is canonical. All filters and independently universed families are allowed.

## References

The intrinsic magma center and submonoid center follow Mathlib's formalizations by
Eric Wieser and Jireh Loreaux. The quotient carrier and operations reuse the filter
product formalization by Yury Kudryashov and Abhimanyu Pallavi Sudhir and the
congruence interfaces by Amelia Livingston. The equivalence generalizes the existing
filter-germ center equivalence; eventual reflection reuses `Filter.eventually_mem_center_iff`.
-/

@[expose] public section

universe u v

namespace Filter.Product

variable {ι : Type u} {K : ι → Type v}

/-- A represented element is central precisely when its section is central eventually.
All three intrinsic centrality laws are retained, without associativity assumptions. -/
theorem mem_center_coe_iff [∀ i, Mul (K i)] (F : Filter ι) (f : ∀ i, K i) :
    (f : F.Product K) ∈ Set.center (F.Product K) ↔
      ∀ᶠ i in F, f i ∈ Set.center (K i) := by
  constructor
  · intro h
    apply (Filter.eventually_mem_center_iff F f).2
    refine ⟨?_, ?_, ?_⟩
    · intro a
      exact ((coe_eq (f * a) (a * f)).1 (h.comm (a : F.Product K)).eq).mono
        fun i hi => (commute_iff_eq _ _).2 hi
    · intro a b
      exact (coe_eq (f * (a * b)) ((f * a) * b)).1
        (h.left_assoc (a : F.Product K) (b : F.Product K))
    · intro a b
      exact (coe_eq ((a * b) * f) (a * (b * f))).1
        (h.right_assoc (a : F.Product K) (b : F.Product K))
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro a
      refine Quotient.inductionOn a ?_
      intro a
      apply (commute_iff_eq _ _).2
      exact (coe_eq (f * a) (a * f)).2 (h.mono fun i hi => (hi.comm (a i)).eq)
    · intro a b
      refine Quotient.inductionOn₂ a b ?_
      intro a b
      exact (coe_eq (f * (a * b)) ((f * a) * b)).2
        (h.mono fun i hi => hi.left_assoc (a i) (b i))
    · intro a b
      refine Quotient.inductionOn₂ a b ?_
      intro a b
      exact (coe_eq ((a * b) * f) (a * (b * f))).2
        (h.mono fun i hi => hi.right_assoc (a i) (b i))

/-- The submonoid-center criterion needs only multiplication with a two-sided unit. -/
theorem mem_submonoid_center_coe_iff [∀ i, MulOneClass (K i)]
    (F : Filter ι) (f : ∀ i, K i) :
    (f : F.Product K) ∈ Submonoid.center (F.Product K) ↔
      ∀ᶠ i in F, f i ∈ Submonoid.center (K i) :=
  mem_center_coe_iff F f

/-- The product of the fibre centers is multiplicatively equivalent to the center
of the product. Neither associative multiplication nor a proper filter is required. -/
noncomputable def centerEquiv [∀ i, MulOneClass (K i)] (F : Filter ι) :
    F.Product (fun i => ↥(Submonoid.center (K i))) ≃*
      ↥(Submonoid.center (F.Product K)) := by
  classical
  let h : F.Product (fun i => ↥(Submonoid.center (K i))) →ₙ*
      ↥(Submonoid.center (F.Product K)) :=
    { toFun := fun x => Quotient.liftOn x
        (fun g : ∀ i, ↥(Submonoid.center (K i)) =>
          ⟨((fun i => (g i : K i)) : F.Product K),
            (mem_submonoid_center_coe_iff F (fun i => (g i : K i))).2
              (Filter.Eventually.of_forall fun i => (g i).property)⟩)
        (fun f g hfg => Subtype.ext ((coe_eq _ _).2
          (hfg.mono fun i hi => congrArg Subtype.val hi)))
      map_mul' := by
        intro x y
        refine Quotient.inductionOn₂ x y ?_
        intro f g
        exact Subtype.ext rfl }
  refine MulEquiv.ofBijective h ⟨?_, ?_⟩
  · intro x y
    refine Quotient.inductionOn₂ x y ?_
    intro f g hfg
    apply (coe_eq f g).2
    have hv := congrArg Subtype.val hfg
    change ((fun i => (f i : K i)) : F.Product K) =
      ((fun i => (g i : K i)) : F.Product K) at hv
    exact ((coe_eq _ _).1 hv).mono fun i hi => Subtype.ext hi
  · rintro ⟨z, hz⟩
    revert hz
    refine Quotient.inductionOn z ?_
    intro f hf
    have hfc := (mem_submonoid_center_coe_iff F f).1 hf
    -- The central unit repairs exceptional values without choosing new fibre data.
    let g : ∀ i, ↥(Submonoid.center (K i)) := fun i =>
      if hi : f i ∈ Submonoid.center (K i) then ⟨f i, hi⟩ else 1
    refine ⟨(g : F.Product (fun i => ↥(Submonoid.center (K i)))), Subtype.ext ?_⟩
    change ((fun i => (g i : K i)) : F.Product K) = (f : F.Product K)
    exact (coe_eq _ _).2 (hfc.mono fun i hi => by simp [g, hi])

/-- On a center-valued section the equivalence forgets the subtype pointwise. -/
@[simp]
theorem coe_centerEquiv_coe [∀ i, MulOneClass (K i)]
    (F : Filter ι) (g : ∀ i, ↥(Submonoid.center (K i))) :
    (↑((centerEquiv (K := K) F)
      (g : F.Product (fun i => ↥(Submonoid.center (K i))))) : F.Product K) =
      ((fun i => (g i : K i)) : F.Product K) := rfl

/-- Any center-valued section representing a central element represents its inverse. -/
theorem centerEquiv_symm_eq_coe [∀ i, MulOneClass (K i)]
    (F : Filter ι) (z : ↥(Submonoid.center (F.Product K)))
    (g : ∀ i, ↥(Submonoid.center (K i)))
    (hg : ((fun i => (g i : K i)) : F.Product K) = (z : F.Product K)) :
    (centerEquiv (K := K) F).symm z =
      (g : F.Product (fun i => ↥(Submonoid.center (K i)))) := by
  apply (centerEquiv F).injective
  rw [MulEquiv.apply_symm_apply]
  apply Subtype.ext
  exact hg.symm.trans (coe_centerEquiv_coe F g).symm

/-- Select a total center-valued section representing the inverse of a central element.
The product class is canonical, but the section need not be canonical pointwise. -/
noncomputable def centerRepresentative [∀ i, MulOneClass (K i)]
    (F : Filter ι) (z : ↥(Submonoid.center (F.Product K))) :
    ∀ i, ↥(Submonoid.center (K i)) :=
  Classical.choose (show ∃ g : ∀ i, ↥(Submonoid.center (K i)),
      (g : F.Product (fun i => ↥(Submonoid.center (K i)))) = (centerEquiv F).symm z from
    Quotient.inductionOn ((centerEquiv F).symm z) fun g => ⟨g, rfl⟩)

/-- The selected total section represents the inverse center-valued product. -/
@[simp]
theorem coe_centerRepresentative [∀ i, MulOneClass (K i)]
    (F : Filter ι) (z : ↥(Submonoid.center (F.Product K))) :
    (centerRepresentative (K := K) F z :
      F.Product (fun i => ↥(Submonoid.center (K i)))) =
        (centerEquiv (K := K) F).symm z := by
  unfold centerRepresentative
  exact Classical.choose_spec (show ∃ g : ∀ i, ↥(Submonoid.center (K i)),
      (g : F.Product (fun i => ↥(Submonoid.center (K i)))) = (centerEquiv F).symm z from
    Quotient.inductionOn ((centerEquiv F).symm z) fun g => ⟨g, rfl⟩)

/-- A central represented element has a total center-valued representative agreeing
with the supplied section eventually, including for filters which ignore some indices. -/
theorem centerRepresentative_eventuallyEq [∀ i, MulOneClass (K i)]
    (F : Filter ι) (f : ∀ i, K i)
    (hf : (f : F.Product K) ∈ Submonoid.center (F.Product K)) :
    ∀ᶠ i in F, (centerRepresentative (K := K) F
      ⟨(f : F.Product K), hf⟩ i : K i) = f i := by
  have h := congrArg Subtype.val
    ((centerEquiv (K := K) F).apply_symm_apply ⟨(f : F.Product K), hf⟩)
  rw [← coe_centerRepresentative (K := K) F ⟨(f : F.Product K), hf⟩,
    coe_centerEquiv_coe] at h
  exact (coe_eq _ _).1 h

end Filter.Product
