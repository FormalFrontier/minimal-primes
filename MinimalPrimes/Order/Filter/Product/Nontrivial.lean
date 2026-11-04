/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Data.Quot
public import Mathlib.Order.Filter.Germ.Basic
public import MinimalPrimes.Order.Filter.Basic

/-!
# Nontrivial dependent reduced products

A dependent reduced product is nontrivial exactly when it has a total section and
nontrivial fibres occur frequently. An empty fibre outside the filter's support
still prevents every total section, so the section condition cannot be omitted.
No algebraic structure or properness hypothesis is required.

The proof applies `Filter.eventually_forall_iff_forall_section` twice to reflect
subsingletonness from all pairs of sections to the fibres. The nontriviality
criterion follows by negation. Thus the classical witness argument is shared with
the existing total-section API, rather than implemented again for this quotient.
Constant families recover the existing nontriviality instance for `Filter.Germ`.

## References

The carrier and coercion reuse Mathlib's `Filter.Product`, due to Yury Kudryashov
and Abhimanyu Pallavi Sudhir. The proofs use Mathlib's quotient API, developed by
Johannes Hölzl, and its nontriviality API, developed by Sébastien Gouëzel. The
section-reflection argument and the nontriviality criterion are original project
contributions. This formalization was developed with AI assistance.
-/

@[expose] public section

universe u v

namespace Filter
namespace Product

variable {ι : Type u} {F : Filter ι} {K : ι → Type v}

/-- The existing total-section quotient is inhabited exactly when a total section
exists, including when an empty fibre is outside the filter's support. -/
@[simp]
theorem nonempty_iff : Nonempty (F.Product K) ↔ Nonempty (∀ i, K i) :=
  nonempty_quotient_iff (productSetoid F K)

/-- When a total section exists, the reduced product is subsingleton exactly when
subsingleton fibres occur eventually. The supplied section permits the canonical
section-reflection theorem to test all pairs of fibre elements. -/
theorem subsingleton_iff_of_nonempty (hK : Nonempty (∀ i, K i)) :
    Subsingleton (F.Product K) ↔ ∀ᶠ i in F, Subsingleton (K i) := by
  obtain ⟨s⟩ := hK
  constructor
  · intro h
    have hsections : ∀ f : ∀ i, K i, ∀ᶠ i in F, ∀ y : K i, f i = y := by
      intro f
      apply (eventually_forall_iff_forall_section
        (D := F) (P := fun i y => f i = y) s).2
      intro g
      exact Quotient.exact
        (@Subsingleton.elim (F.Product K) h (f : F.Product K) (g : F.Product K))
    have hfibres : ∀ᶠ i in F, ∀ x y : K i, x = y :=
      (eventually_forall_iff_forall_section
        (D := F) (P := fun i x => ∀ y : K i, x = y) s).2 hsections
    exact hfibres.mono fun _ hi => ⟨hi⟩
  · intro h
    constructor
    intro x y
    refine Quotient.inductionOn₂' x y ?_
    intro f g
    apply Quotient.sound
    exact h.mono fun i hi => @Subsingleton.elim (K i) hi (f i) (g i)

/-- A dependent reduced product has two distinct elements exactly when a total
section exists and nontrivial fibres occur frequently. In particular, frequent
nontriviality alone does not suffice if a fibre away from the filter is empty. -/
theorem nontrivial_iff :
    Nontrivial (F.Product K) ↔
      Nonempty (∀ i, K i) ∧ ∃ᶠ i in F, Nontrivial (K i) := by
  constructor
  · intro h
    let := h
    have hK : Nonempty (∀ i, K i) :=
      (nonempty_iff (F := F) (K := K)).mp inferInstance
    refine ⟨hK, ?_⟩
    intro heventually
    have hsub : Subsingleton (F.Product K) :=
      (subsingleton_iff_of_nonempty hK).2
        (heventually.mono fun _ hi => not_nontrivial_iff_subsingleton.mp hi)
    exact (not_nontrivial_iff_subsingleton.mpr hsub) h
  · rintro ⟨hK, hfrequent⟩
    apply not_subsingleton_iff_nontrivial.mp
    intro hsub
    exact hfrequent (((subsingleton_iff_of_nonempty hK).1 hsub).mono
      fun _ hi => not_nontrivial_iff_subsingleton.mpr hi)

/-- A proper filter and nontrivial fibres give a nontrivial dependent reduced
product without requiring any algebraic structure. -/
theorem nontrivial_of_nontrivial [∀ i, Nontrivial (K i)] [NeBot F] :
    Nontrivial (F.Product K) := by
  refine nontrivial_iff.mpr ⟨Classical.nonempty_pi.mpr (fun i => inferInstance), ?_⟩
  intro h
  obtain ⟨i, hi⟩ := h.exists
  exact hi inferInstance

end Product

namespace Germ

variable {ι : Type u} {F : Filter ι} {R : Type v}

/-- A constant-family germ is nontrivial exactly when its value type is nontrivial
and its filter is proper. The reverse implication uses Mathlib's existing instance. -/
theorem nontrivial_iff : Nontrivial (F.Germ R) ↔ Nontrivial R ∧ NeBot F := by
  constructor
  · intro h
    change Nontrivial (F.Product (fun _ => R)) at h
    have hfrequent := (Product.nontrivial_iff.mp h).2
    obtain ⟨i, hi⟩ := hfrequent.exists
    refine ⟨hi, ⟨?_⟩⟩
    intro hbot
    subst F
    exact frequently_bot hfrequent
  · rintro ⟨hR, hF⟩
    let := hR
    let := hF
    infer_instance

end Germ
end Filter
