/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MinimalPrimes.Order.Filter.Product.Map
public import MinimalPrimes.Order.Filter.Germ.SMul
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Tactic

/-!
# Zero-only dependent product-map controls

These clients exercise independent Pi-row universes, bottom and empty indices,
trivial fibres, a genuinely varying noninjective/nonadditive compression, the
frequent-but-not-eventual parity boundary, and failure without preservation.
-/

@[expose] public section

open Filter

namespace Filter.Product

universe u v w

/-- Evaluation of a Pi row needs neither points nor equal row/coordinate universes. -/
def rowEvaluation {ι : Type u} {κ : Type w} (D : Filter ι)
    (R : ι → κ → Type v) (j : κ) :
    D.Product (fun i => ∀ k, R i k) → D.Product (fun i => R i j) :=
  Product.map D (fun _ r => r j)

example {ι : Type u} {R : ι → Type v} {S : ι → Type w}
    [∀ i, Zero (R i)] [∀ i, Zero (S i)] (g : ∀ i, ZeroHom (R i) (S i)) :
    ∀ x : (⊥ : Filter ι).Product R,
      Product.map ⊥ (fun i => (g i : R i → S i)) x = Product.zeroPoint ⊥ S →
        x = Product.zeroPoint ⊥ R :=
  (Product.forall_map_eq_zeroPoint_imp_iff ⊥ g).2 (by simp)

example (D : Filter Empty) {R : Empty → Type v} {S : Empty → Type w}
    [∀ i, Zero (R i)] [∀ i, Zero (S i)] (g : ∀ i, ZeroHom (R i) (S i)) :
    ∀ x : D.Product R,
      Product.map D (fun i => (g i : R i → S i)) x = Product.zeroPoint D S →
        x = Product.zeroPoint D R := by
  apply (Product.forall_map_eq_zeroPoint_imp_iff D g).2
  exact Eventually.of_forall fun i => nomatch i

private def holeSource : Bool → Type
  | false => PUnit
  | true => Empty

private def holeMap (b : Bool) : holeSource b → PUnit := fun _ => PUnit.unit

/-- An ignored empty fibre still prevents every global source section. -/
example :
    (∀ᶠ b in (pure false : Filter Bool), Function.Surjective (holeMap b)) ∧
      ¬Function.Surjective (Product.map (pure false) holeMap) := by
  constructor
  · change Function.Surjective (holeMap false)
    intro y
    exact ⟨PUnit.unit, Subsingleton.elim _ _⟩
  · intro h
    rcases (Product.map_surjective_iff (pure false) holeMap).1 h with hS | ⟨⟨f⟩, _⟩
    · exact hS.false (fun _ => PUnit.unit)
    · exact nomatch f true

/-- Empty total target sections make onto vacuous, without a source-default hypothesis. -/
example (D : Filter PUnit) :
    Function.Surjective (Product.map D (fun _ : PUnit => (id : Empty → Empty))) := by
  apply (Product.map_surjective_iff D _).2
  exact Or.inl ⟨fun f => nomatch f PUnit.unit⟩

private inductive OnePoint where
  | point

private instance : Zero OnePoint := ⟨OnePoint.point⟩

example {ι : Type u} (D : Filter ι) {S : ι → Type v} [∀ i, Zero (S i)]
    (g : ∀ i, ZeroHom OnePoint (S i)) :
    ∀ x : D.Product (fun _ : ι => OnePoint),
      Product.map D (fun i => (g i : OnePoint → S i)) x = Product.zeroPoint D S →
        x = Product.zeroPoint D (fun _ : ι => OnePoint) := by
  apply (Product.forall_map_eq_zeroPoint_imp_iff D g).2
  exact Eventually.of_forall fun _ r _ => by cases r; rfl

private def oneR (n : ℕ) : Fin (n + 3) := ⟨1, by omega⟩
private def twoR (n : ℕ) : Fin (n + 3) := ⟨2, by omega⟩
private def oneS (n : ℕ) : Fin (n + 4) := ⟨1, by omega⟩
private def twoS (n : ℕ) : Fin (n + 4) := ⟨2, by omega⟩

private theorem oneR_ne_zero (n : ℕ) : oneR n ≠ 0 := by
  intro h
  have hv := congrArg Fin.val h
  norm_num [oneR] at hv

private theorem twoR_ne_zero (n : ℕ) : twoR n ≠ 0 := by
  intro h
  have hv := congrArg Fin.val h
  norm_num [twoR] at hv

private theorem oneS_ne_zero (n : ℕ) : oneS n ≠ 0 := by
  intro h
  have hv := congrArg Fin.val h
  norm_num [oneS] at hv

/-- Both fibre cardinalities vary; every nonzero point is compressed to one. -/
private def compression (n : ℕ) : ZeroHom (Fin (n + 3)) (Fin (n + 4)) where
  toFun r := if r = 0 then 0 else oneS n
  map_zero' := by simp

private theorem compression_reflects (n : ℕ) (r : Fin (n + 3))
    (h : compression n r = 0) : r = 0 := by
  by_cases hr : r = 0
  · exact hr
  · change (if r = 0 then 0 else oneS n) = 0 at h
    rw [ite_eq_right hr] at h
    exact (oneS_ne_zero n h).elim

private theorem compression_one (n : ℕ) : compression n (oneR n) = oneS n := by
  change (if oneR n = 0 then 0 else oneS n) = oneS n
  rw [ite_eq_right (oneR_ne_zero n)]

private theorem compression_two (n : ℕ) : compression n (twoR n) = oneS n := by
  change (if twoR n = 0 then 0 else oneS n) = oneS n
  rw [ite_eq_right (twoR_ne_zero n)]

/-- The varying pointed compression reflects the zero point for every filter. -/
private theorem compression_product_reflects (D : Filter ℕ) :
    ∀ x : D.Product (fun n => Fin (n + 3)),
      Product.map D (fun n => (compression n : Fin (n + 3) → Fin (n + 4))) x =
          Product.zeroPoint D (fun n => Fin (n + 4)) →
        x = Product.zeroPoint D (fun n => Fin (n + 3)) :=
  (Product.forall_map_eq_zeroPoint_imp_iff D compression).2
    (Eventually.of_forall compression_reflects)

/-- The two distinct nonzero sections have the same image over the cofinite filter. -/
private theorem compression_identifies_sections :
    (oneR : (cofinite : Filter ℕ).Product (fun n => Fin (n + 3))) ≠
        (twoR : (cofinite : Filter ℕ).Product (fun n => Fin (n + 3))) ∧
      Product.map cofinite (fun n => (compression n : Fin (n + 3) → Fin (n + 4)))
          (oneR : (cofinite : Filter ℕ).Product (fun n => Fin (n + 3))) =
        Product.map cofinite (fun n => (compression n : Fin (n + 3) → Fin (n + 4)))
          (twoR : (cofinite : Filter ℕ).Product (fun n => Fin (n + 3))) := by
  constructor
  · intro h
    have hf : ∀ᶠ n in (cofinite : Filter ℕ), False := by
      apply ((Product.coe_eq oneR twoR).mp h).mono
      intro n hn
      have hv := congrArg Fin.val hn
      norm_num [oneR, twoR] at hv
    exact hf.exists.elim fun _ hFalse => hFalse
  · rw [Product.map_coe, Product.map_coe]
    apply (Product.coe_eq _ _).mpr
    exact Eventually.of_forall fun n => (compression_one n).trans (compression_two n).symm

/-- Its usual cyclic additions are not preserved: one plus one is sent to one, not two. -/
private theorem compression_nonadditive (n : ℕ) :
    compression n (oneR n + oneR n) ≠ compression n (oneR n) + compression n (oneR n) := by
  have hR : oneR n + oneR n = twoR n := by
    apply Fin.ext
    change 2 % (n + 3) = 2
    exact Nat.mod_eq_of_lt (by omega)
  have hS : oneS n + oneS n = twoS n := by
    apply Fin.ext
    change 2 % (n + 4) = 2
    exact Nat.mod_eq_of_lt (by omega)
  rw [hR, compression_two, compression_one, hS]
  intro h
  have hv := congrArg Fin.val h
  norm_num [oneS, twoS] at hv

private inductive Bit where
  | zero
  | one
  deriving DecidableEq

private instance : Zero Bit := ⟨Bit.zero⟩

private abbrev oneZero : Zero Bit := ⟨Bit.one⟩

/-- An alternative Zero record selects the corresponding section point. -/
example {ι : Type u} (D : Filter ι) :
    @Product.zeroPoint ι D (fun _ : ι => Bit) (fun _ => oneZero) =
      ((fun _ : ι => Bit.one) : D.Product (fun _ : ι => Bit)) :=
  rfl

/-- A proposition-valued target distinguishes the Sort-general section criterion
from the Type-valued quotient API: constant proof maps do not reflect the source point. -/
example :
    ¬(∀ x : ℕ → Bit,
      (∀ᶠ _n in (cofinite : Filter ℕ), (True.intro : True) = True.intro) →
        ∀ᶠ n in (cofinite : Filter ℕ), x n = Bit.zero) := by
  intro h
  have hc := (Filter.forall_eventually_map_eq_imp_iff (cofinite : Filter ℕ)
    (fun (_ : ℕ) (_ : Bit) => (True.intro : True))
    (fun _ => Bit.zero) (fun _ => (True.intro : True))
    (Eventually.of_forall fun _ => rfl)).1 h
  have hf : ∀ᶠ _n in (cofinite : Filter ℕ), False := hc.mono fun _ hn => by
    have hbad : Bit.one = Bit.zero := hn Bit.one rfl
    cases hbad
  exact hf.exists.elim fun _ hFalse => hFalse

private lemma not_eventually_even : ¬∀ᶠ n in (cofinite : Filter ℕ), n % 2 = 0 := by
  intro h
  rw [Nat.cofinite_eq_atTop] at h
  obtain ⟨N, hN⟩ := eventually_atTop.1 h
  have hodd := hN (2 * N + 1) (by omega)
  omega

private lemma not_eventually_odd : ¬∀ᶠ n in (cofinite : Filter ℕ), n % 2 ≠ 0 := by
  intro h
  rw [Nat.cofinite_eq_atTop] at h
  obtain ⟨N, hN⟩ := eventually_atTop.1 h
  have heven := hN (2 * N) (by omega)
  omega

private def parityMap (n : ℕ) : ZeroHom Bit Bit where
  toFun b := if n % 2 = 0 then 0 else b
  map_zero' := by split_ifs <;> rfl

private def parityWitness (n : ℕ) : Bit := if n % 2 = 0 then Bit.one else 0

private theorem parity_witness_image_zero :
    Product.map cofinite (fun n => (parityMap n : Bit → Bit))
        (parityWitness : (cofinite : Filter ℕ).Product (fun _ => Bit)) =
      Product.zeroPoint cofinite (fun _ : ℕ => Bit) := by
  rw [Product.map_coe]
  apply (Product.coe_eq_zeroPoint_iff cofinite _).mpr
  exact Eventually.of_forall fun n => by
    by_cases hn : n % 2 = 0 <;> simp [parityMap, parityWitness, hn]

private theorem parity_witness_ne_zero :
    (parityWitness : (cofinite : Filter ℕ).Product (fun _ => Bit)) ≠
      Product.zeroPoint cofinite (fun _ : ℕ => Bit) := by
  intro h
  apply not_eventually_odd
  exact ((Product.coe_eq_zeroPoint_iff cofinite parityWitness).mp h).mono fun n hn he => by
    simp [parityWitness, he] at hn

/-- Both parity loci are frequent; the bad locus gives a genuine nonzero kernel class. -/
private theorem parity_boundary :
    (∃ᶠ n in (cofinite : Filter ℕ), n % 2 = 0) ∧
      (∃ᶠ n in (cofinite : Filter ℕ), n % 2 ≠ 0) ∧
      ¬(∀ x : (cofinite : Filter ℕ).Product (fun _ => Bit),
        Product.map cofinite (fun n => (parityMap n : Bit → Bit)) x =
            Product.zeroPoint cofinite (fun _ : ℕ => Bit) →
          x = Product.zeroPoint cofinite (fun _ : ℕ => Bit)) := by
  refine ⟨not_eventually_odd, ?_, ?_⟩
  · simpa only [Filter.Frequently, not_not] using not_eventually_even
  · intro h
    exact parity_witness_ne_zero (h _ parity_witness_image_zero)

private def unpreserved (n : ℕ) (_b : Bit) : Bit :=
  if n % 2 = 0 then 0 else Bit.one

/-- Without preservation, global reflection is vacuous but coordinate reflection fails. -/
private theorem preservation_is_necessary :
    (∀ x : (cofinite : Filter ℕ).Product (fun _ => Bit),
      Product.map cofinite unpreserved x = Product.zeroPoint cofinite (fun _ : ℕ => Bit) →
        x = Product.zeroPoint cofinite (fun _ : ℕ => Bit)) ∧
      ¬(∀ᶠ n in (cofinite : Filter ℕ), ∀ b : Bit, unpreserved n b = 0 → b = 0) := by
  constructor
  · intro x
    obtain ⟨r, rfl⟩ := Product.coe_surjective cofinite (fun _ : ℕ => Bit) x
    intro hr
    have he : ∀ᶠ n in (cofinite : Filter ℕ), n % 2 = 0 := by
      have hm : ∀ᶠ n in (cofinite : Filter ℕ), unpreserved n (r n) = 0 := by
        apply (Product.coe_eq_zeroPoint_iff cofinite _).mp
        exact (Product.map_coe cofinite unpreserved r).symm.trans hr
      exact hm.mono fun n hn => by
        by_contra hne
        simp [unpreserved, hne] at hn
    exact (not_eventually_even he).elim
  · intro h
    apply not_eventually_odd
    exact h.mono fun n hn he => by
      have hbad : Bit.one = Bit.zero := hn Bit.one (by simp [unpreserved, he])
      cases hbad

private inductive Scalar where
  | keep
  | erase

private instance : SMulZeroClass Scalar Bit where
  smul c b := match c with
    | Scalar.keep => b
    | Scalar.erase => 0
  smul_zero c := by cases c <;> rfl

/-- A selected action uses no zero on the scalar type and no additive data. -/
example {ι : Type u} (D : Filter ι) (f : ι → Scalar) :
    (∀ x : Germ D Bit, (f : Germ D Scalar) • x = 0 → x = 0) ↔
      ∀ᶠ i in D, ∀ b : Bit, f i • b = 0 → b = 0 :=
  Germ.forall_smul_coe_eq_zero_imp_iff D f

/-- The class-free map agrees with the selected represented action on germs. -/
example {ι : Type u} (D : Filter ι) (f : ι → Scalar) (x : Germ D Bit) :
    Product.map D (fun i b => f i • b) x = (f : Germ D Scalar) • x := by
  obtain ⟨r, rfl⟩ := Product.coe_surjective D (fun _ : ι => Bit) x
  rfl

example {ι : Type u} (D : Filter ι) :
    Product.map D (fun _ : ι => (RingHom.id ℕ : ℕ → ℕ)) =
      (Product.mapRingHom D (fun _ : ι => RingHom.id ℕ) :
        D.Product (fun _ : ι => ℕ) → D.Product (fun _ : ι => ℕ)) :=
  Product.map_eq_mapRingHom D _

/-- The strong bridge uses the existing inherited zero, not a separately chosen one. -/
example {ι : Type u} (D : Filter ι) :
    Product.zeroPoint D (fun _ : ι => ℕ) = (0 : D.Product (fun _ : ι => ℕ)) :=
  Product.zeroPoint_eq_zero D _

end Filter.Product
