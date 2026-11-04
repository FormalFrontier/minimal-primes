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
surjective. Even an index equivalence tending in one direction need not induce an
injection, with both filters proper. The final check distinguishes an ignored empty
fibre from an empty index type: the quotient still uses total sections.
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
  · intro x y
    refine Quotient.inductionOn₂' x y ?_
    intro f g h
    have hfalse : f false = g false :=
      eventually_top.mp ((Product.coe_eq (fun _ => f false) (fun _ => g false)).mp h) false
    apply Quotient.sound
    intro j hj
    have hj' : j = false := Set.mem_singleton_iff.mp hj
    subst j
    exact hfalse
  · intro hsurj
    obtain ⟨x, hx⟩ := hsurj ((fun b : Bool => b) : (⊤ : Filter Bool).Product (fun _ => Bool))
    refine Quotient.inductionOn' x ?_ hx
    intro f hf
    have h := eventually_top.mp
      ((Product.coe_eq (fun _ => f false) (fun b : Bool => b)).mp hf)
    exact Bool.false_ne_true ((h false).symm.trans (h true))

-- Identity indices, but only one Tendsto direction: four classes collapse to two.
-- Both the top filter on Bool and the singleton principal filter are proper.
example : ¬ Function.Injective
    (fun x : (⊤ : Filter Bool).Product (fun _ => Bool) =>
      x.compTendsto id (show Tendsto id (principal {false}) ⊤ from tendsto_top)) := by
  intro hinj
  have h := hinj (a₁ := ((fun b : Bool => b) : (⊤ : Filter Bool).Product (fun _ => Bool)))
    (a₂ := ((fun _ : Bool => false) : (⊤ : Filter Bool).Product (fun _ => Bool)))
    ((Product.coe_eq _ _).mpr (by
      intro b hb
      have hb' : b = false := Set.mem_singleton_iff.mp hb
      subst b
      rfl))
  exact Bool.false_ne_true (eventually_top.mp ((Product.coe_eq _ _).mp h) true).symm

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
