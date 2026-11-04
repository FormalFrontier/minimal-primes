/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MinimalPrimes.Order.Filter.Product.CompTendsto

/-!
# Dependent pullback and its boundaries

Restriction to a constant Bool index gives a diagonal from a genuinely dependent
product with two classes to the four-class top product. It is injective but not
surjective. An index equivalence tending in one direction induces a surjection
but need not induce an injection, even with both filters proper. The final check
distinguishes an ignored empty fibre from an empty index type: the quotient still
uses total sections.
-/

@[expose] public section

open Filter

namespace FilterProductCompTendstoExamples

private def fibre : Bool → Type
  | false => Bool
  | true => Unit

private theorem tendsto_false :
    Tendsto (fun _ : Bool => false) ⊤ (principal {false}) :=
  tendsto_principal.mpr (Eventually.of_forall fun _ => Set.mem_singleton false)

private def diagonal : (principal {false}).Product fibre →
    (⊤ : Filter Bool).Product (fun _ => Bool) :=
  fun x => x.compTendsto (fun _ => false) tendsto_false

-- The source remembers only its Bool fibre, and the image misses the off-diagonal section.
example : Function.Injective diagonal ∧ ¬ Function.Surjective diagonal := by
  constructor
  · exact Product.compTendsto_injective_of_map_eq (R := fibre) (fun _ : Bool => false)
      (by simp)
  · intro hsurj
    obtain ⟨x, hx⟩ := hsurj
      (((fun b : Bool => b) : Bool → Bool) : (⊤ : Filter Bool).Product (fun _ => Bool))
    refine Quotient.inductionOn' x ?_ hx
    intro f hf
    have h := eventually_top.mp
      ((Product.coe_eq (fun _ => f false) (fun b : Bool => b)).mp hf)
    exact Bool.false_ne_true ((h false).symm.trans (h true))

-- Identity indices, but only one Tendsto direction: four classes collapse onto two.
-- Both the top filter on Bool and the singleton principal filter are proper.
example : Function.Surjective
    (fun x : (⊤ : Filter Bool).Product (fun _ => Bool) =>
      x.compTendsto id (show Tendsto id (principal {false}) ⊤ from tendsto_top)) ∧
    ¬ Function.Injective
      (fun x : (⊤ : Filter Bool).Product (fun _ => Bool) =>
        x.compTendsto id (show Tendsto id (principal {false}) ⊤ from tendsto_top)) := by
  constructor
  · exact Product.compTendsto_surjective_of_equiv (Equiv.refl Bool) tendsto_top
  · intro hinj
    have h := hinj
      (a₁ := (((fun b : Bool => b) : Bool → Bool) :
        (⊤ : Filter Bool).Product (fun _ => Bool)))
      (a₂ := (((fun _ : Bool => false) : Bool → Bool) :
        (⊤ : Filter Bool).Product (fun _ => Bool)))
      ((Product.coe_eq _ _).mpr (by
        intro b hb
        have hb' : b = false := Set.mem_singleton_iff.mp hb
        subst b
        rfl))
    exact Bool.false_ne_true (eventually_top.mp ((Product.coe_eq _ _).mp h) true).symm

-- The Unit fibre contributes no distinction: both quotients retain two classes,
-- so the full criterion gives injectivity despite unequal image and target filters.
example : Function.Injective
    (fun x : (⊤ : Filter Bool).Product fibre =>
      x.compTendsto id (show Tendsto id (principal {false}) ⊤ from tendsto_top)) ∧
    Filter.map id (principal ({false} : Set Bool)) ≠ ⊤ := by
  constructor
  · apply (Product.compTendsto_injective_iff (R := fibre) id tendsto_top).2
    right
    have hs : {b | Nontrivial (fibre b)} = ({false} : Set Bool) := by
      ext b
      cases b
      · change Nontrivial Bool ↔ false = false
        exact iff_of_true inferInstance rfl
      · change Nontrivial Unit ↔ true = false
        exact iff_of_false (not_nontrivial_iff_subsingleton.mpr inferInstance)
          (fun h => Bool.false_ne_true h.symm)
    simp [hs]
  · rw [Filter.map_id]
    intro h
    have h' : ∀ b : Bool, b ∈ ({false} : Set Bool) :=
      eventually_top.mp (h ▸ mem_principal_self {false})
    exact Bool.false_ne_true (Set.mem_singleton_iff.mp (h' true)).symm

private def emptyFibre : Bool → Type
  | false => Unit
  | true => Empty

-- An ignored empty fibre still empties the source, unlike the empty index type.
example : IsEmpty ((principal {false}).Product emptyFibre) ∧
    Nonempty ((⊤ : Filter Bool).Product (fun i => emptyFibre ((fun _ => false) i))) ∧
    Nonempty ((⊤ : Filter Empty).Product (fun _ => Empty)) := by
  refine ⟨⟨fun x => ?_⟩, ⟨((fun _ : Bool => ()) : (⊤ : Filter Bool).Product (fun _ => Unit))⟩,
    ⟨((Empty.elim : Empty → Empty) : (⊤ : Filter Empty).Product (fun _ => Empty))⟩⟩
  obtain ⟨s⟩ := (Product.nonempty_iff.mp (show Nonempty
    ((principal {false}).Product emptyFibre) from ⟨x⟩))
  exact (s true).elim

end FilterProductCompTendstoExamples
