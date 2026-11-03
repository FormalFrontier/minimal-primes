/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.GroupTheory.Submonoid.Center
public import Mathlib.Order.Filter.Germ.Basic
public import MinimalPrimes.Order.Filter.Germ.Map

/-!
# Centers of filter germs

A represented germ belongs to the intrinsic center precisely when its values belong
to the center eventually. The primary criterion needs only multiplication: it retains
commutation and both associativity fields of `IsMulCentral`. The submonoid-center
criterion is its carrier bridge at `MulOneClass`, without assuming associativity.

`centerEquiv` identifies germs of center-valued functions with the center of the
germ space. Its forward map forgets the subtype, and its inverse is characterized
at the germ level. `centerRepresentative` selects a total center-valued function
representing the inverse. This selected function is not canonical pointwise;
only its germ is determined, including on filters with ignored indices.

For necessity, test centrality against varying representatives chosen to witness a
failed field at each bad coordinate. The supplied representative provides fallback
values, so neither an inhabitant of the codomain nor a proper filter is needed.

## References

Mathlib's intrinsic magma center was formalized by Eric Wieser and Jireh Loreaux,
its submonoid center by Eric Wieser, and its filter-germ representation and
multiplication interfaces by Yury Kudryashov and Abhimanyu Pallavi Sudhir.
-/

@[expose] public section

universe u v

namespace Filter.Germ

variable {ι : Type u} {M : Type v}

/-- A germ belongs to the intrinsic magma center exactly when its representative
is central eventually. This includes improper filters and empty types. -/
theorem mem_center_coe_iff [Mul M] (D : Filter ι) (f : ι → M) :
    (f : Germ D M) ∈ Set.center (Germ D M) ↔ ∀ᶠ i in D, f i ∈ Set.center M := by
  classical
  -- A diagonal choice turns tests against all varying arguments into eventual
  -- universal quantification. A supplied function handles empty codomains too.
  have diagonal {A : Type v} (a : ι → A) (P : ι → A → Prop)
      (h : ∀ b : ι → A, ∀ᶠ i in D, P i (b i)) : ∀ᶠ i in D, ∀ b, P i b := by
    have hex (i : ι) : ∃ b : A, P i b → ∀ c, P i c := by
      by_cases hi : ∀ b, P i b
      · exact ⟨a i, fun _ => hi⟩
      · obtain ⟨b, hb⟩ := not_forall.mp hi
        exact ⟨b, fun h => (hb h).elim⟩
    choose b hb using hex
    exact (h b).mono fun i hi => hb i hi
  simp only [Set.mem_center_iff]
  constructor
  · intro h
    have hc : ∀ᶠ i in D, ∀ a, Commute (f i) a := by
      apply diagonal f
      intro a
      simpa only [commute_iff_eq] using (coe_eq.mp (h.comm (a : Germ D M)).eq).eventually
    have hl : ∀ᶠ i in D, ∀ p : M × M,
        f i * (p.1 * p.2) = (f i * p.1) * p.2 := by
      apply diagonal (fun i => (f i, f i))
      intro a
      exact coe_eq.mp
        (h.left_assoc ((fun i => (a i).1) : Germ D M) ((fun i => (a i).2) : Germ D M))
    have hr : ∀ᶠ i in D, ∀ p : M × M,
        (p.1 * p.2) * f i = p.1 * (p.2 * f i) := by
      apply diagonal (fun i => (f i, f i))
      intro a
      exact coe_eq.mp
        (h.right_assoc ((fun i => (a i).1) : Germ D M) ((fun i => (a i).2) : Germ D M))
    filter_upwards [hc, hl, hr] with i hc hl hr
    exact ⟨hc, fun a b => hl (a, b), fun a b => hr (a, b)⟩
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro a
      refine inductionOn a ?_
      intro a
      apply (commute_iff_eq _ _).mpr
      exact coe_eq.mpr (h.mono fun i hi => (hi.comm (a i)).eq)
    · intro a b
      refine inductionOn₂ a b ?_
      intro a b
      exact coe_eq.mpr (h.mono fun i hi => hi.left_assoc (a i) (b i))
    · intro a b
      refine inductionOn₂ a b ?_
      intro a b
      exact coe_eq.mpr (h.mono fun i hi => hi.right_assoc (a i) (b i))

/-- A germ belongs to the submonoid center exactly when its representative does
eventually. A multiplication with a two-sided identity suffices; it need not be associative. -/
theorem mem_submonoid_center_coe_iff [MulOneClass M] (D : Filter ι) (f : ι → M) :
    (f : Germ D M) ∈ Submonoid.center (Germ D M) ↔
      ∀ᶠ i in D, f i ∈ Submonoid.center M := by
  change (f : Germ D M) ∈ (Submonoid.center (Germ D M) : Set (Germ D M)) ↔
    ∀ᶠ i in D, f i ∈ (Submonoid.center M : Set M)
  rw [Submonoid.coe_center, Submonoid.coe_center]
  exact mem_center_coe_iff D f

/-- Germs of elements of the center are multiplicatively equivalent to central
germs. The filter is arbitrary and multiplication need not be associative. -/
noncomputable def centerEquiv [MulOneClass M] (D : Filter ι) :
    Germ D ↥(Submonoid.center M) ≃* ↥(Submonoid.center (Germ D M)) := by
  classical
  let F : Germ D ↥(Submonoid.center M) →ₙ* ↥(Submonoid.center (Germ D M)) :=
    { toFun := fun x => ⟨map Subtype.val x, by
        refine inductionOn x ?_
        intro f
        exact (mem_submonoid_center_coe_iff D (fun i => (f i : M))).2
          (Eventually.of_forall fun i => (f i).property)⟩
      map_mul' := fun x y => Subtype.ext (inductionOn₂ x y fun _ _ => rfl) }
  refine MulEquiv.ofBijective F ⟨?_, ?_⟩
  · -- Reuse varying-application injectivity for the constant subtype inclusion.
    have hi := (injective_map₂_apply_coe_iff D
      (fun _ : ι => (Subtype.val : ↥(Submonoid.center M) → M))).2
      (Eventually.of_forall fun _ => Subtype.val_injective)
    have happ (x : Germ D ↥(Submonoid.center M)) :
        map₂ (fun (φ : ↥(Submonoid.center M) → M) a => φ a)
          ((fun _ : ι => (Subtype.val : ↥(Submonoid.center M) → M)) :
            Germ D (↥(Submonoid.center M) → M)) x = map Subtype.val x :=
      inductionOn x fun _ => rfl
    intro x y h
    apply hi
    have hval := congrArg Subtype.val h
    change map Subtype.val x = map Subtype.val y at hval
    simpa only [happ] using hval
  · rintro ⟨z, hz⟩
    induction z using inductionOn with
    | h f =>
      have hf := (mem_submonoid_center_coe_iff D f).1 hz
      -- The central unit repairs every exceptional value, without a properness assumption.
      let g : ι → ↥(Submonoid.center M) := fun i =>
        if h : f i ∈ Submonoid.center M then ⟨f i, h⟩ else 1
      refine ⟨(g : Germ D ↥(Submonoid.center M)), Subtype.ext ?_⟩
      change ((fun i => (g i : M)) : Germ D M) = (f : Germ D M)
      exact coe_eq.mpr (hf.mono fun i hi => by simp [g, hi])

/-- The forward equivalence is the germ map of the center's subtype inclusion. -/
@[simp]
theorem coe_centerEquiv [MulOneClass M] (D : Filter ι)
    (x : Germ D ↥(Submonoid.center M)) :
    (↑((centerEquiv D) x) : Germ D M) = map Subtype.val x := rfl

/-- On a center-valued representative the equivalence forgets the subtype pointwise. -/
theorem coe_centerEquiv_coe [MulOneClass M] (D : Filter ι)
    (g : ι → ↥(Submonoid.center M)) :
    (↑((centerEquiv D) (g : Germ D ↥(Submonoid.center M))) : Germ D M) =
      ((fun i => (g i : M)) : Germ D M) := rfl

/-- Forgetting the subtype after taking the inverse recovers the central germ. -/
@[simp]
theorem map_subtype_centerEquiv_symm [MulOneClass M] (D : Filter ι)
    (z : ↥(Submonoid.center (Germ D M))) :
    map Subtype.val ((centerEquiv D).symm z) = (z : Germ D M) := by
  simpa only [coe_centerEquiv] using
    congrArg Subtype.val ((centerEquiv D).apply_symm_apply z)

/-- Any total center-valued representative of a central germ represents its inverse. -/
theorem centerEquiv_symm_eq_coe [MulOneClass M] (D : Filter ι)
    (z : ↥(Submonoid.center (Germ D M))) (g : ι → ↥(Submonoid.center M))
    (hg : ((fun i => (g i : M)) : Germ D M) = (z : Germ D M)) :
    (centerEquiv D).symm z = (g : Germ D ↥(Submonoid.center M)) := by
  apply (centerEquiv D).injective
  rw [MulEquiv.apply_symm_apply]
  apply Subtype.ext
  simpa only [coe_centerEquiv_coe] using hg.symm

/-- Select a total center-valued representative of the inverse of a central germ.
Its germ is canonical, but its values at ignored indices need not be. -/
noncomputable def centerRepresentative [MulOneClass M] (D : Filter ι)
    (z : ↥(Submonoid.center (Germ D M))) : ι → ↥(Submonoid.center M) :=
  Classical.choose (show ∃ g : ι → ↥(Submonoid.center M),
      (g : Germ D ↥(Submonoid.center M)) = (centerEquiv D).symm z from
    inductionOn ((centerEquiv D).symm z) fun g => ⟨g, rfl⟩)

/-- The selected total function represents the inverse center-valued germ. -/
@[simp]
theorem coe_centerRepresentative [MulOneClass M] (D : Filter ι)
    (z : ↥(Submonoid.center (Germ D M))) :
    (centerRepresentative D z : Germ D ↥(Submonoid.center M)) =
      (centerEquiv D).symm z := by
  unfold centerRepresentative
  exact Classical.choose_spec (show ∃ g : ι → ↥(Submonoid.center M),
      (g : Germ D ↥(Submonoid.center M)) = (centerEquiv D).symm z from
    inductionOn ((centerEquiv D).symm z) fun g => ⟨g, rfl⟩)

/-- A central represented germ lifts to a total center-valued function agreeing
with the original function eventually, even when exceptional values are noncentral. -/
theorem centerRepresentative_eventuallyEq [MulOneClass M] (D : Filter ι)
    (f : ι → M) (hf : (f : Germ D M) ∈ Submonoid.center (Germ D M)) :
    (fun i => (centerRepresentative D ⟨(f : Germ D M), hf⟩ i : M)) =ᶠ[D] f := by
  apply coe_eq.mp
  change map Subtype.val
    (centerRepresentative D ⟨(f : Germ D M), hf⟩ : Germ D ↥(Submonoid.center M)) = _
  rw [coe_centerRepresentative, map_subtype_centerEquiv_symm]

end Filter.Germ
