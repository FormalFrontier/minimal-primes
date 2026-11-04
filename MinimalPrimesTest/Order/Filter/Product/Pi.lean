/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.Group.Even
import Mathlib.Order.Filter.Cocardinal
import Mathlib.Order.Filter.Cofinite
import MinimalPrimes.Order.Filter.Product.Pi

/-!
# Product comparison examples and boundaries

These examples check nontrivial Boolean coordinates, genuinely varying families,
empty coordinates, empty row indices, and bottom with an empty global-section
type. Naturality is checked for varying target fibres and infinite coordinates.
Countable products are tested on the principal filter of even naturals and on the
proper nonprincipal cocountable filter on `Set ℕ`. The cofinite Boolean diagonal
shows why arbitrary coordinates do not in general give injectivity.
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

private abbrev evenPrincipal : Filter ℕ := 𝓟 {n : ℕ | Even n}

private def natFibres (i j : ℕ) : Type := Fin (i + j + 2)

private def natColumns (j i : ℕ) : natFibres i j := Fin.last (i + j + 1)

private def natZeros (i j : ℕ) : natFibres i j :=
  ⟨0, Nat.zero_lt_succ (i + j + 1)⟩

private def natOnes (i j : ℕ) : natFibres i j :=
  ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ (i + j))⟩

-- Both the support and the coordinate type are infinite, and the fibres vary in both indices.
-- The inverse transposes the supplied columns without choosing new representatives.
example :
    (Product.piEquivOfCountable evenPrincipal natFibres).symm
        (fun j => (natColumns j : evenPrincipal.Product (fun i => natFibres i j))) =
      (((fun i j => natColumns j i) : ∀ i j, natFibres i j) :
        evenPrincipal.Product (fun i => ∀ j, natFibres i j)) := by
  apply (Product.piEquivOfCountable evenPrincipal natFibres).symm_apply_eq.2
  exact ((Product.piEquivOfCountable_apply evenPrincipal natFibres _).trans
    (funext fun j => Product.piComparison_coe evenPrincipal natFibres
      (fun i j => natColumns j i) j)).symm

-- Zero and one give different source points and comparison images, already at i = j = 0.
example :
    (natZeros : evenPrincipal.Product (fun i => ∀ j, natFibres i j)) ≠
        (natOnes : evenPrincipal.Product (fun i => ∀ j, natFibres i j)) ∧
      Product.piComparison evenPrincipal natFibres
          (natZeros : evenPrincipal.Product (fun i => ∀ j, natFibres i j)) ≠
        Product.piComparison evenPrincipal natFibres
          (natOnes : evenPrincipal.Product (fun i => ∀ j, natFibres i j)) := by
  have hne :
      (natZeros : evenPrincipal.Product (fun i => ∀ j, natFibres i j)) ≠
        (natOnes : evenPrincipal.Product (fun i => ∀ j, natFibres i j)) := by
    intro h
    have hrows := (Product.coe_eq natZeros natOnes).1 h
    have hzero := Filter.eventually_principal.1 hrows 0 (show Even (0 : ℕ) from ⟨0, rfl⟩)
    have hzerozero : (0 : ℕ) = 1 := congrArg Fin.val (congrFun hzero 0)
    exact Nat.zero_ne_one hzerozero
  exact ⟨hne, fun h => hne (Product.piComparison_injective_of_countable
    evenPrincipal natFibres h)⟩

-- Changing only odd rows does not change the represented class.
example (f g : ∀ i j : ℕ, natFibres i j) (h : ∀ i, Even i → f i = g i) :
    (f : evenPrincipal.Product (fun i => ∀ j, natFibres i j)) =
      (g : evenPrincipal.Product (fun i => ∀ j, natFibres i j)) := by
  exact (Product.coe_eq f g).2 (Filter.eventually_principal.2 h)

section Cocountable

local instance : CountableInterFilter (cocountable : Filter (Set ℕ)) :=
  cardinalInterFilter_aleph_one_iff.1 inferInstance

local instance : Uncountable (Set ℕ) := by
  apply Cardinal.aleph0_lt_mk_iff.1
  rw [Cardinal.mk_set, Cardinal.mk_nat]
  exact Cardinal.cantor _

local instance : NeBot (cocountable : Filter (Set ℕ)) := by
  rw [Filter.neBot_iff, ne_eq, ← Filter.empty_mem_iff_bot, Filter.mem_cocountable, Set.compl_empty]
  exact Set.not_countable_univ

private def singletonRow (j : ℕ) : Set ℕ := {j}

private noncomputable def singletonDiagonal (A : Set ℕ) (j : ℕ) : Bool := by
  classical
  exact decide (A = singletonRow j)

private def setBoolRows (b : Bool) : Set ℕ → ℕ → Bool := fun _ _ => b

-- The total exceptional range is countable, so these matrices agree as source classes.
-- Each supplied column has just one exceptional row; its inverse is the same source point.
example :
    (singletonDiagonal : (cocountable : Filter (Set ℕ)).Product (fun _ => ℕ → Bool)) =
        (setBoolRows false : (cocountable : Filter (Set ℕ)).Product (fun _ => ℕ → Bool)) ∧
      (Product.piEquivOfCountable (cocountable : Filter (Set ℕ))
          (fun (_ : Set ℕ) (_ : ℕ) => Bool)).symm
        (fun j => ((fun A => singletonDiagonal A j) :
          (cocountable : Filter (Set ℕ)).Product (fun _ => Bool))) =
        (setBoolRows false : (cocountable : Filter (Set ℕ)).Product (fun _ => ℕ → Bool)) := by
  classical
  constructor
  · apply (Product.coe_eq singletonDiagonal (setBoolRows false)).2
    have hsmall : (Set.range singletonRow)ᶜ ∈ (cocountable : Filter (Set ℕ)) := by
      apply Filter.mem_cocountable.2
      simpa only [compl_compl] using Set.countable_range singletonRow
    filter_upwards [hsmall] with A hA
    funext j
    have hAj : A ≠ singletonRow j := fun h => hA ⟨j, h.symm⟩
    simp [singletonDiagonal, setBoolRows, hAj]
  · apply (Product.piEquivOfCountable (cocountable : Filter (Set ℕ))
      (fun (_ : Set ℕ) (_ : ℕ) => Bool)).symm_apply_eq.2
    refine Eq.trans ?_ (Product.piEquivOfCountable_apply (cocountable : Filter (Set ℕ))
      (fun (_ : Set ℕ) (_ : ℕ) => Bool) _).symm
    funext j
    refine Eq.trans ?_ (Product.piComparison_coe (cocountable : Filter (Set ℕ))
      (fun (_ : Set ℕ) (_ : ℕ) => Bool) (setBoolRows false) j).symm
    apply (Product.coe_eq (fun A => singletonDiagonal A j) (fun A => setBoolRows false A j)).2
    filter_upwards [Filter.eventually_cocardinal_ne
      (hreg := Cardinal.isRegular_aleph_one) (singletonRow j)] with A hA
    simp [singletonDiagonal, setBoolRows, hA]

-- Properness keeps false and true distinct, and omitting any singleton rules out principalness.
example :
    (∀ s : Set (Set ℕ), (cocountable : Filter (Set ℕ)) ≠ 𝓟 s) ∧
      (setBoolRows false : (cocountable : Filter (Set ℕ)).Product (fun _ => ℕ → Bool)) ≠
        (setBoolRows true : (cocountable : Filter (Set ℕ)).Product (fun _ => ℕ → Bool)) := by
  constructor
  · intro s h
    have hs : NeBot (𝓟 s) := h ▸ inferInstanceAs (NeBot (cocountable : Filter (Set ℕ)))
    obtain ⟨A, hA⟩ := Filter.principal_neBot_iff.1 hs
    have hne : ∀ᶠ B in (cocountable : Filter (Set ℕ)), B ≠ A :=
      Filter.eventually_cocardinal_ne (hreg := Cardinal.isRegular_aleph_one) A
    exact (Filter.eventually_principal.1 (h ▸ hne) A hA) rfl
  · intro h
    have hrows := (Product.coe_eq (setBoolRows false) (setBoolRows true)).1 h
    obtain ⟨_, hA⟩ := hrows.exists
    have hzero := congrFun hA 0
    simp [setBoolRows] at hzero

end Cocountable

end MinimalPrimesTest.FilterProductPi
