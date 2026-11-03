/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Group.Center
public import MinimalPrimes.Order.Filter.Basic

/-!
# Eventual centrality in dependent families

Centrality of a section can be tested against all varying sections. This retains
commutation and both associativity laws of the intrinsic magma center, without
assuming associative multiplication. Paired fibres give the simultaneous tests
needed by the two associativity laws.

## References

The intrinsic magma center follows Mathlib's formalization by Eric Wieser and
Jireh Loreaux. The witness argument generalizes the one for centers of filter germs.
-/

@[expose] public section

universe u v

namespace Filter

variable {ι : Type u} {R : ι → Type v}

/-- A section is central eventually if and only if it commutes and associates
on both sides with every pair of varying sections eventually. -/
theorem eventually_mem_center_iff [∀ i, Mul (R i)] (D : Filter ι) (f : ∀ i, R i) :
    (∀ᶠ i in D, f i ∈ Set.center (R i)) ↔
      (∀ a : ∀ i, R i, ∀ᶠ i in D, Commute (f i) (a i)) ∧
      (∀ a b : ∀ i, R i, ∀ᶠ i in D, f i * (a i * b i) = (f i * a i) * b i) ∧
      (∀ a b : ∀ i, R i, ∀ᶠ i in D, (a i * b i) * f i = a i * (b i * f i)) := by
  simp only [Set.mem_center_iff]
  constructor
  · intro h
    exact ⟨fun a => h.mono fun i hi => hi.comm (a i),
      fun a b => h.mono fun i hi => hi.left_assoc (a i) (b i),
      fun a b => h.mono fun i hi => hi.right_assoc (a i) (b i)⟩
  · rintro ⟨hc, hl, hr⟩
    have hc' : ∀ᶠ i in D, ∀ a, Commute (f i) a :=
      (eventually_forall_iff_forall_section f).2 hc
    have hl' : ∀ᶠ i in D, ∀ p : R i × R i,
        f i * (p.1 * p.2) = (f i * p.1) * p.2 := by
      apply (eventually_forall_iff_forall_section (fun i => (f i, f i))).2
      intro p
      exact hl (fun i => (p i).1) (fun i => (p i).2)
    have hr' : ∀ᶠ i in D, ∀ p : R i × R i,
        (p.1 * p.2) * f i = p.1 * (p.2 * f i) := by
      apply (eventually_forall_iff_forall_section (fun i => (f i, f i))).2
      intro p
      exact hr (fun i => (p i).1) (fun i => (p i).2)
    filter_upwards [hc', hl', hr'] with i hc hl hr
    exact ⟨hc, fun a b => hl (a, b), fun a b => hr (a, b)⟩

end Filter
