/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.GroupTheory.Submonoid.Center
public import Mathlib.Order.Filter.Germ.Basic

/-!
# Centers of filter germs

A represented germ belongs to the intrinsic center precisely when its values belong
to the center eventually. The primary criterion needs only multiplication: it retains
commutation and both associativity fields of `IsMulCentral`. The submonoid-center
criterion is its carrier bridge at `MulOneClass`, without assuming associativity.

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

end Filter.Germ
