/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Order.Filter.Basic

/-!
# Quantifying over dependent sections eventually

A total section supplies fallback values when choosing a witness in each fibre.
Consequently, testing a predicate along every section detects whether it holds
for all elements of the fibres eventually. The fibres may belong to any sort.

A family of coordinate maps lifts every total target section up to eventual equality
exactly when the target has no total section, or the source has a total section and
the coordinate maps are eventually surjective.

The witness argument generalizes the diagonal argument for centers of filter germs.
-/

@[expose] public section

universe u v w

namespace Filter

variable {ι : Type u} {R : ι → Sort v} {D : Filter ι} {P : ∀ i, R i → Prop}

/-- A predicate holds throughout the fibres eventually exactly when it holds
along every total section eventually. The supplied section provides fallback
values; no properness or separate inhabitance assumption is needed. -/
theorem eventually_forall_iff_forall_section (s : ∀ i, R i) :
    (∀ᶠ i in D, ∀ x : R i, P i x) ↔ ∀ f : ∀ i, R i, ∀ᶠ i in D, P i (f i) := by
  classical
  constructor
  · intro h f
    exact h.mono fun i hi => hi (f i)
  · intro h
    have hex (i : ι) : ∃ x : R i, P i x → ∀ y, P i y := by
      by_cases hi : ∀ x, P i x
      · exact ⟨s i, fun _ => hi⟩
      · obtain ⟨x, hx⟩ := not_forall.mp hi
        exact ⟨x, fun h => (hx h).elim⟩
    choose f hf using hex
    exact (h f).mono fun i hi => hf i hi

/-- A family of maps reflects eventual equality of total sections exactly when
there is no total source section or the coordinate maps are eventually injective.
The emptiness disjunct concerns the whole dependent function sort: an empty fibre
ignored by the filter still prevents every total source section. -/
theorem forall_eventually_eq_of_map_eq_iff {K : ι → Sort v} {L : ι → Sort w}
    (D : Filter ι) (φ : ∀ i, K i → L i) :
    (∀ f g : ∀ i, K i, (∀ᶠ i in D, φ i (f i) = φ i (g i)) → ∀ᶠ i in D, f i = g i) ↔
      IsEmpty (∀ i, K i) ∨ ∀ᶠ i in D, Function.Injective (φ i) := by
  constructor
  · intro h
    rcases isEmpty_or_nonempty (∀ i, K i) with hK | ⟨s⟩
    · exact Or.inl hK
    · obtain ⟨s⟩ := s
      right
      let R (i : ι) := Σ' a : K i, Σ' b : K i, φ i a = φ i b
      have hR : ∀ᶠ i in D, ∀ p : R i, p.1 = p.2.1 := by
        apply (eventually_forall_iff_forall_section (D := D)
          (P := fun i (p : R i) => p.1 = p.2.1)
          (fun i => ⟨s i, ⟨s i, rfl⟩⟩)).2
        intro p
        exact h (fun i => (p i).1) (fun i => (p i).2.1)
          (Eventually.of_forall fun i => (p i).2.2)
      exact hR.mono fun i hi a b hab => hi ⟨a, ⟨b, hab⟩⟩
  · rintro (hK | hφ) f g hfg
    · exact (hK.false f).elim
    · exact (hφ.and hfg).mono fun i hi => hi.1 hi.2

end Filter

namespace Filter

/-- Every total target section has an eventual lift exactly when there are no total
target sections, or there is a total source section and the coordinate maps are
eventually surjective. Source totality supplies fallback values outside the set
where surjectivity holds, so no properness assumption on the filter is needed. -/
theorem forall_exists_eventually_eq_iff
    {ι : Type u} {K : ι → Sort v} {L : ι → Sort w}
    (D : Filter ι) (φ : ∀ i, K i → L i) :
    (∀ g : (∀ i, L i), ∃ f : (∀ i, K i),
      ∀ᶠ i in D, φ i (f i) = g i) ↔
      IsEmpty (∀ i, L i) ∨
        (Nonempty (∀ i, K i) ∧
          ∀ᶠ i in D, Function.Surjective (φ i)) := by
  classical
  constructor
  · intro h
    by_cases hL : Nonempty (∀ i, L i)
    · obtain ⟨g₀⟩ := hL
      obtain ⟨f₀, _⟩ := h g₀
      refine Or.inr ⟨⟨f₀⟩, ?_⟩
      apply (eventually_forall_iff_forall_section
        (D := D) (P := fun i y => ∃ x : K i, φ i x = y) g₀).2
      intro g
      obtain ⟨f, hf⟩ := h g
      exact hf.mono fun i hi => ⟨f i, hi⟩
    · exact Or.inl ⟨fun g => hL ⟨g⟩⟩
  · rintro (hL | ⟨⟨f₀⟩, hφ⟩) g
    · obtain ⟨hL⟩ := hL
      exact (hL g).elim
    · have hex (i : ι) : ∃ x : K i, Function.Surjective (φ i) → φ i x = g i := by
        by_cases hi : Function.Surjective (φ i)
        · obtain ⟨x, hx⟩ := hi (g i)
          exact ⟨x, fun _ => hx⟩
        · exact ⟨f₀ i, fun h => (hi h).elim⟩
      choose f hf using hex
      exact ⟨f, hφ.mono fun i hi => hf i hi⟩

end Filter
