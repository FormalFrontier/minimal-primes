/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Order.Filter.Cofinite
import MinimalPrimes.Order.Filter.Product.Pi

/-!
# Finite-product comparison boundary examples

These examples check nontrivial Boolean coordinates, a genuinely varying family,
empty coordinates, empty row indices, and bottom with an empty global-section
type. Naturality is checked for varying target fibres and infinite coordinates.
The cofinite Boolean diagonal shows why arbitrary coordinates do not in general
give injectivity.
-/

namespace MinimalPrimesTest.FilterProductPi

open Filter

private def boolRows (b : Bool) : Unit → Bool → Bool := fun _ _ => b

-- The finite Boolean comparison distinguishes two concrete represented matrices.
example :
    Product.piComparison (pure () : Filter Unit) (fun (_ : Unit) (_ : Bool) => Bool)
        (boolRows false : (pure () : Filter Unit).Product (fun _ => Bool → Bool)) ≠
      Product.piComparison (pure () : Filter Unit) (fun (_ : Unit) (_ : Bool) => Bool)
        (boolRows true : (pure () : Filter Unit).Product (fun _ => Bool → Bool)) := by
  intro h
  have hcol := congrFun h true
  have heventually : ∀ᶠ _ in (pure () : Filter Unit), false = true := by
    apply (Product.coe_eq (fun _ : Unit => false) (fun _ : Unit => true)).1
    exact (Product.piComparison_coe (pure () : Filter Unit)
      (fun (_ : Unit) (_ : Bool) => Bool) (boolRows false) true).symm.trans
        (hcol.trans (Product.piComparison_coe (pure () : Filter Unit)
          (fun (_ : Unit) (_ : Bool) => Bool) (boolRows true) true))
  simp at heventually

private def varying (i : ℕ) : Bool → Type
  | false => Bool
  | true => Fin (i + 2)

private def varyingColumns : (j : Bool) → (i : ℕ) → varying i j
  | false, _ => true
  | true, i => Fin.last (i + 1)

private def varyingMap (i : ℕ) : (j : Bool) → Bool → varying i j
  | false, b => b
  | true, b => if b then Fin.last (i + 1) else ⟨0, Nat.zero_lt_succ (i + 1)⟩

-- The inverse API assembles columns whose true-coordinate types vary with i.
example :
    (Product.piEquiv (cofinite : Filter ℕ) varying).symm
        (fun j => (varyingColumns j : (cofinite : Filter ℕ).Product (fun i => varying i j))) =
      (((fun i j => varyingColumns j i) : ∀ i j, varying i j) :
        (cofinite : Filter ℕ).Product (fun i => ∀ j, varying i j)) := by
  exact Product.piEquiv_symm_coe (cofinite : Filter ℕ) varying varyingColumns

-- The inverse square applies to arbitrary column classes and varying target types.
example (y : Bool → (cofinite : Filter ℕ).Product (fun _ => Bool)) :
    Product.map (cofinite : Filter ℕ)
        (fun i (f : Bool → Bool) j => varyingMap i j (f j))
        ((Product.piEquiv (cofinite : Filter ℕ) (fun (_ : ℕ) (_ : Bool) => Bool)).symm y) =
      (Product.piEquiv (cofinite : Filter ℕ) varying).symm
        (fun j => Product.map (cofinite : Filter ℕ) (fun i => varyingMap i j) (y j)) := by
  exact Product.map_piEquiv_symm (cofinite : Filter ℕ)
    (fun (_ : ℕ) (_ : Bool) => Bool) varying varyingMap y

private def emptyCoordinateMatrix : ∀ _ : ℕ, ∀ _ : Empty, Empty := fun _ j => j.elim

-- Empty coordinates need no coordinate or fibre default, even with Empty fibres.
example :
    (Product.piEquiv (cofinite : Filter ℕ) (fun (_ : ℕ) (_ : Empty) => Empty)).symm
        (fun j => j.elim) =
      (emptyCoordinateMatrix :
        (cofinite : Filter ℕ).Product (fun _ => Empty → Empty)) := by
  apply (Product.piEquiv (cofinite : Filter ℕ) (fun (_ : ℕ) (_ : Empty) => Empty)).injective
  funext j
  exact j.elim

-- Empty row indices still permit an infinite coordinate family, without defaults.
example :
    ∃ x : (⊥ : Filter Empty).Product (fun _ => ℕ → Empty),
      Product.piComparison (⊥ : Filter Empty) (fun (_ : Empty) (_ : ℕ) => Empty) x =
        fun _ => (((fun i : Empty => i.elim) : Empty → Empty) :
          (⊥ : Filter Empty).Product (fun _ => Empty)) := by
  exact Product.piComparison_surjective (⊥ : Filter Empty)
    (fun (_ : Empty) (_ : ℕ) => Empty) _

private def missingColumn (_ : Unit) : Bool → Type
  | false => Unit
  | true => Empty

-- Bottom does not create a representative. The combined target is empty, while
-- the false-coordinate quotient is inhabited: an individual projection is not onto.
example :
    IsEmpty ((⊥ : Filter Unit).Product (fun i => ∀ j, missingColumn i j)) ∧
      Nonempty ((⊥ : Filter Unit).Product (fun i => missingColumn i false)) ∧
        IsEmpty (∀ j, (⊥ : Filter Unit).Product (fun i => missingColumn i j)) := by
  let c : ∀ i : Unit, missingColumn i false := fun _ => ()
  refine ⟨⟨?_⟩, ⟨(c : (⊥ : Filter Unit).Product (fun i => missingColumn i false))⟩, ⟨?_⟩⟩
  · intro x
    refine Quotient.inductionOn' x ?_
    intro f
    exact (f () true).elim
  · intro y
    refine Quotient.inductionOn' (y true) ?_
    intro f
    exact (f ()).elim

-- The forward square needs no finite coordinate index, even for an opaque row class.
example (x : (cofinite : Filter ℕ).Product (fun _ => ℕ → Bool)) :
    Product.piComparison (cofinite : Filter ℕ) (fun (_ : ℕ) (_ : ℕ) => Bool)
        (Product.map (cofinite : Filter ℕ)
          (fun i (f : ℕ → Bool) j => if i = j then !(f j) else f j) x) =
      fun j => Product.map (cofinite : Filter ℕ) (fun i (b : Bool) => if i = j then !b else b)
        (Product.piComparison (cofinite : Filter ℕ) (fun (_ : ℕ) (_ : ℕ) => Bool) x j) := by
  exact Product.piComparison_map (cofinite : Filter ℕ)
    (fun (_ : ℕ) (_ : ℕ) => Bool) (fun (_ : ℕ) (_ : ℕ) => Bool)
    (fun i j b => if i = j then !b else b) x

-- Each diagonal column differs from false at one point, but no diagonal row is false.
example :
    ¬Function.Injective
      (Product.piComparison (cofinite : Filter ℕ) (fun (_ : ℕ) (_ : ℕ) => Bool)) := by
  intro hinjective
  let f : ℕ → ℕ → Bool := fun i j => decide (i = j)
  let g : ℕ → ℕ → Bool := fun _ _ => false
  have hcolumns :
      Product.piComparison (cofinite : Filter ℕ) (fun (_ : ℕ) (_ : ℕ) => Bool)
          (f : (cofinite : Filter ℕ).Product (fun _ => ℕ → Bool)) =
        Product.piComparison (cofinite : Filter ℕ) (fun (_ : ℕ) (_ : ℕ) => Bool)
          (g : (cofinite : Filter ℕ).Product (fun _ => ℕ → Bool)) := by
    funext j
    simp only [Product.piComparison_coe]
    apply (Product.coe_eq (fun i => f i j) (fun i => g i j)).2
    filter_upwards [Filter.eventually_cofinite_ne j] with i hi
    simp [f, g, hi]
  have hrows : ∀ᶠ i in (cofinite : Filter ℕ), f i = g i :=
    (Product.coe_eq f g).1 (hinjective hcolumns)
  obtain ⟨i, hi⟩ := hrows.exists
  have hdiagonal := congrFun hi i
  simp [f, g] at hdiagonal

end MinimalPrimesTest.FilterProductPi
