/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MinimalPrimes.Order.Filter.Product.Units
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.GroupWithZero.WithZero

/-!
# Multiplicative dependent products

The structure comparisons check full data, including natural powers, along the named
semiring and ultrafilter constructions. Varying endomorphism monoids then exercise
composition without addition, commutativity or inverses. The unit-locus criterion
distinguishes identity sections from constant endomorphisms and the top filter from
the bottom filter in this same family. Adjoining zero gives nonzero elements without
right inverses even after taking the top-filter product.
-/

@[expose] public section

open Filter

universe u v

namespace FilterProductExamples

section Coherence

variable {ι : Type u} {K : ι → Type v} (F : Filter ι)

/-- The product's monoid-with-zero structure restricts to its monoid structure. -/
theorem monoidWithZero_toMonoid [∀ i, MonoidWithZero (K i)] :
    (Product.instMonoidWithZero (F := F) (K := K)).toMonoid =
      Product.instMonoid (F := F) (K := K) := rfl

example [∀ i, Semiring (K i)] :
    (Product.instSemiring (F := F) (K := K)).toMonoid =
      Product.instMonoid (F := F) (K := K) := rfl

example [∀ i, Semiring (K i)] :
    (Product.instSemiring (F := F) (K := K)).toMonoidWithZero =
      Product.instMonoidWithZero (F := F) (K := K) := rfl

example [∀ i, CommSemiring (K i)] :
    (Product.instCommSemiring (F := F) (K := K)).toSemiring =
      Product.instSemiring (F := F) (K := K) := rfl

example [∀ i, CommSemiring (K i)] :
    (Product.instCommSemiring (F := F) (K := K)).toCommMonoid =
      Con.commMonoid (productCon F K) := rfl

example [∀ i, CommSemiring (K i)] :
    (Product.instCommSemiring (F := F) (K := K)).toMonoid =
      Product.instMonoid (F := F) (K := K) := rfl

example [∀ i, CommSemiring (K i)] :
    (Product.instCommSemiring (F := F) (K := K)).toSemiring.toMonoidWithZero =
      Product.instMonoidWithZero (F := F) (K := K) := rfl

example (R : Type v) [Monoid R] :
    Product.instMonoid (F := F) (K := fun _ : ι => R) =
      Germ.instMonoid (l := F) (M := R) := rfl

variable (U : Ultrafilter ι)

example [∀ i, DivisionSemiring (K i)] :
    (Product.instDivisionSemiring (K := K) U).toSemiring =
      Product.instSemiring (F := (U : Filter ι)) (K := K) := rfl

example [∀ i, DivisionSemiring (K i)] :
    (Product.instDivisionSemiring (K := K) U).toSemiring.toMonoidWithZero =
      Product.instMonoidWithZero (F := (U : Filter ι)) (K := K) := rfl

example [∀ i, DivisionSemiring (K i)] :
    (Product.instDivisionSemiring (K := K) U).toGroupWithZero.toMonoidWithZero =
      Product.instMonoidWithZero (F := (U : Filter ι)) (K := K) := rfl

example [∀ i, DivisionSemiring (K i)] :
    (Product.instDivisionSemiring (K := K) U).toGroupWithZero.toInv =
      Product.instInv (F := (U : Filter ι)) (K := K) := rfl

example [∀ i, Semifield (K i)] :
    (Product.instSemifield (K := K) U).toCommSemiring =
      Product.instCommSemiring (F := (U : Filter ι)) (K := K) := rfl

example [∀ i, Semifield (K i)] :
    (Product.instSemifield (K := K) U).toDivisionSemiring =
      Product.instDivisionSemiring (K := K) U := rfl

example [∀ i, Semifield (K i)] :
    (Product.instSemifield (K := K) U).toCommGroupWithZero.toCommMonoidWithZero.toCommMonoid =
      Con.commMonoid (productCon (U : Filter ι) K) := rfl

example [∀ i, Semifield (K i)] :
    (Product.instSemifield (K := K) U).toCommGroupWithZero.toCommMonoidWithZero.toMonoidWithZero =
      Product.instMonoidWithZero (F := (U : Filter ι)) (K := K) := rfl

example [∀ i, Semifield (K i)] :
    (Product.instSemifield (K := K) U).toCommGroupWithZero.toGroupWithZero.toMonoidWithZero =
      Product.instMonoidWithZero (F := (U : Filter ι)) (K := K) := rfl

example [∀ i, Semifield (K i)] :
    (Product.instSemifield (K := K) U).toCommGroupWithZero.toGroupWithZero.toInv =
      Product.instInv (F := (U : Filter ι)) (K := K) := rfl

end Coherence

private abbrev EndFamily (n : ℕ) := Function.End (Fin (n + 2))

private def leftConstant : ∀ n, EndFamily n := fun _ _ => 0

private def rightConstant : ∀ n, EndFamily n := fun _ _ => 1

-- Opposite products are distinct constant maps, so composition has not become commutative.
example :
    let a := Product.coeMulHom (⊤ : Filter ℕ) leftConstant
    let b := Product.coeMulHom (⊤ : Filter ℕ) rightConstant
    a * b = a ∧ b * a = b ∧ a ≠ b := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · rw [← map_mul]
    rfl
  · rw [← map_mul]
    rfl
  · intro h
    have h₀ := Filter.mem_top_iff_forall.1 ((Product.coe_eq leftConstant rightConstant).1 h) 0
    exact (by decide : (0 : Fin 2) ≠ 1) (congrFun h₀ 0)

-- Natural powers in the quotient are iterates of endomorphisms, not pointwise powers of values.
example (f : ∀ n, EndFamily n) (m : ℕ) :
    Product.coeMulHom (K := EndFamily) (⊤ : Filter ℕ) (fun n => (f n)^[m]) =
      Product.coeMulHom (K := EndFamily) (⊤ : Filter ℕ) f ^ m :=
  map_pow (Product.coeMulHom (K := EndFamily) (⊤ : Filter ℕ)) f m

-- A constant endomorphism cannot acquire a right inverse in the top-filter product.
private theorem leftConstant_no_right_inverse : ¬ ∃ q : (⊤ : Filter ℕ).Product EndFamily,
    Product.coeMulHom (K := EndFamily) (⊤ : Filter ℕ) leftConstant * q = 1 := by
  obtain ⟨e, he, _⟩ := Product.existsUnique_monoidHom
    (F := (⊤ : Filter ℕ)) (K := EndFamily) (Pi.evalMonoidHom EndFamily 0)
    (by
      intro f g hfg
      exact Filter.mem_top_iff_forall.1 hfg 0)
  have he₀ : e (Product.coeMulHom (K := EndFamily) (⊤ : Filter ℕ) leftConstant) =
      leftConstant 0 :=
    congrArg (fun h : (∀ n, EndFamily n) →* EndFamily 0 => h leftConstant) he
  rintro ⟨q, hq⟩
  have h₀ : leftConstant 0 * e q = 1 := by
    simpa only [map_mul, map_one, he₀] using congrArg e hq
  exact (by decide : (0 : Fin 2) ≠ 1) (congrFun h₀ 1)

-- The same nonunit section becomes a unit at bottom; the identity is a unit already at top.
example :
    @IsUnit ((⊥ : Filter ℕ).Product EndFamily) inferInstance leftConstant ∧
      ¬ @IsUnit ((⊤ : Filter ℕ).Product EndFamily) inferInstance leftConstant ∧
      @IsUnit ((⊤ : Filter ℕ).Product EndFamily) inferInstance (1 : ∀ n, EndFamily n) := by
  refine ⟨(Product.isUnit_coe_iff _ _).2 (by simp), ?_, ?_⟩
  · intro h
    obtain ⟨q, hq, _⟩ := isUnit_iff_exists.mp h
    exact leftConstant_no_right_inverse ⟨q, hq⟩
  · exact (Product.isUnit_coe_iff _ _).2 (Eventually.of_forall fun _ => isUnit_one)

private def withZeroLeft : ∀ n, WithZero (EndFamily n) :=
  fun n => (leftConstant n : WithZero (EndFamily n))

-- Adjoining zero uses only a monoid; the nonzero constant maps still have no right inverse.
example :
    Product.coeMulHom (K := fun n => WithZero (EndFamily n)) (⊤ : Filter ℕ) withZeroLeft ≠ 0 ∧
      ¬ ∃ q : (⊤ : Filter ℕ).Product (fun n => WithZero (EndFamily n)),
        Product.coeMulHom (K := fun n => WithZero (EndFamily n))
          (⊤ : Filter ℕ) withZeroLeft * q = 1 := by
  constructor
  · intro h
    have h' := (Product.coe_eq (F := (⊤ : Filter ℕ))
      (K := fun n => WithZero (EndFamily n)) withZeroLeft 0).1 h
    exact WithZero.coe_ne_zero (Filter.mem_top_iff_forall.1 h' 0)
  · obtain ⟨e, he, _⟩ := Product.existsUnique_monoidHom
      (F := (⊤ : Filter ℕ)) (K := fun n => WithZero (EndFamily n))
      (Pi.evalMonoidHom (fun n => WithZero (EndFamily n)) 0)
      (by
        intro f g hfg
        exact Filter.mem_top_iff_forall.1 hfg 0)
    have he₀ : e (Product.coeMulHom (K := fun n => WithZero (EndFamily n))
        (⊤ : Filter ℕ) withZeroLeft) = withZeroLeft 0 :=
      congrArg (fun h : (∀ n, WithZero (EndFamily n)) →* WithZero (EndFamily 0) =>
        h withZeroLeft) he
    rintro ⟨q, hq⟩
    have h₀ : (leftConstant 0 : WithZero (EndFamily 0)) * e q = 1 := by
      simpa only [map_mul, map_one, he₀, withZeroLeft] using congrArg e hq
    have hn : ∀ z : WithZero (EndFamily 0), (leftConstant 0 : WithZero (EndFamily 0)) * z ≠ 1 := by
      refine WithZero.recZeroCoe ?_ ?_
      · simpa only [mul_zero] using (zero_ne_one : (0 : WithZero (EndFamily 0)) ≠ 1)
      · intro e he
        have he' : leftConstant 0 * e = 1 := WithZero.coe_injective he
        exact (by decide : (0 : Fin 2) ≠ 1) (congrFun he' 1)
    exact hn (e q) h₀

-- No properness assumption excludes collapse at the bottom filter.
example {ι : Type u} {K : ι → Type v} [∀ i, MonoidWithZero (K i)] :
    (0 : (⊥ : Filter ι).Product K) = 1 :=
  (Product.coe_eq (F := (⊥ : Filter ι)) (0 : ∀ i, K i) 1).2 (by simp)

-- Empty indices and trivial fibres also allow zero to equal one.
example {K : Empty → Type v} [∀ i, MonoidWithZero (K i)] (F : Filter Empty) :
    (0 : F.Product K) = 1 :=
  (Product.coe_eq (F := F) (0 : ∀ i, K i) 1).2
    (Eventually.of_forall fun i => nomatch i)

example {ι : Type u} {K : ι → Type v} [∀ i, MonoidWithZero (K i)]
    [∀ i, Subsingleton (K i)] (F : Filter ι) : (0 : F.Product K) = 1 :=
  (Product.coe_eq (F := F) (0 : ∀ i, K i) 1).2
    (Eventually.of_forall fun _ => Subsingleton.elim _ _)

-- These unit-locus consequences need only monoids, not the zero operations above.
example {K : Empty → Type v} [∀ i, Monoid (K i)] (F : Filter Empty) (f : ∀ i, K i) :
    @IsUnit (F.Product K) inferInstance f :=
  (Product.isUnit_coe_iff F f).2 (Eventually.of_forall fun i => nomatch i)

example {ι : Type u} {K : ι → Type v} [∀ i, Monoid (K i)]
    [∀ i, Subsingleton (K i)] (F : Filter ι) (f : ∀ i, K i) :
    @IsUnit (F.Product K) inferInstance f :=
  (Product.isUnit_coe_iff F f).2 (Eventually.of_forall fun _ => isUnit_of_subsingleton _)

end FilterProductExamples
