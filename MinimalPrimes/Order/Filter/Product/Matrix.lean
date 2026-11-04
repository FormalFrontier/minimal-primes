/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MinimalPrimes.Order.Filter.Product.Pi
public import MinimalPrimes.Order.Filter.Product.Units
public import Mathlib.Data.Matrix.Basic

/-!
# Matrix rings over dependent reduced products

For an arbitrary filter and a family of semirings, finite square matrices commute
with the dependent reduced product. The comparison retains the given fibre
semirings and the stock matrix semiring, whose multiplication is a finite row-column
sum and whose identity is diagonal. It is not the pointwise semiring on functions.

`Filter.Product.matrixRingEquiv` has representative and all-point entry readouts
in both directions. `Filter.Product.isUnit_matrix_coe_iff` concerns invertibility
of the same represented matrices, not invertibility of their individual entries.
The index, coefficient and matrix-index universes are independent. Bottom filters,
empty index types, empty matrices and zero semirings are included.

## References

The carrier comparison composes this library's `Filter.Product.piEquiv` with
Mathlib's `Equiv.piCongrRight` and `Matrix.of`. Algebra preservation uses
Mathlib's `Matrix.piRingEquiv`, `RingHom.mapMatrix` and the existing product ring
congruence. The unit criterion uses the released dependent-product unit criterion
and Mathlib's equivalence transport of units. See `CREDITS.md` for formalization
credits, separately from the license of original project code.
-/

@[expose] public section

universe uι uR uJ

namespace Filter.Product

variable {ι : Type uι} {J : Type uJ}
variable (F : Filter ι) (R : ι → Type uR)
variable [s : ∀ i, Semiring (R i)] [fJ : Fintype J] [dJ : DecidableEq J]

omit s fJ dJ in
private noncomputable def matrixCarrierEquiv [Finite J] :
    F.Product (fun i => Matrix J J (R i)) ≃ Matrix J J (F.Product R) :=
  (piEquiv F (fun i (_ : J) => J → R i)).trans
    ((Equiv.piCongrRight (fun _ : J => piEquiv F (fun i (_ : J) => R i))).trans
      Matrix.of)

omit s fJ dJ in
private theorem matrixEquiv_coe [Finite J] (A : ∀ i, Matrix J J (R i)) :
    matrixCarrierEquiv (J := J) F R (A : F.Product (fun i => Matrix J J (R i))) =
      Matrix.of (fun j k => ((fun i => A i j k) : F.Product R)) := by
  ext j k
  change piEquiv F (fun i (_ : J) => R i)
    (piEquiv F (fun i (_ : J) => J → R i)
      (A : F.Product (fun i => Matrix J J (R i))) j) k = _
  have hrow :
      piEquiv F (fun i (_ : J) => J → R i)
          (A : F.Product (fun i => Matrix J J (R i))) j =
        ((fun i => A i j) : F.Product (fun i => J → R i)) :=
    (congrFun (piEquiv_apply F (fun i (_ : J) => J → R i)
      (A : F.Product (fun i => Matrix J J (R i)))) j).trans
        (piComparison_coe F (fun i (_ : J) => J → R i) A j)
  exact (congrArg (fun z => piEquiv F (fun i (_ : J) => R i) z k) hrow).trans
    ((congrFun (piEquiv_apply F (fun i (_ : J) => R i)
      ((fun i => A i j) : F.Product (fun i => J → R i))) k).trans
        (piComparison_coe F (fun i (_ : J) => R i) (fun i => A i j) k))

-- This is the existing matrix/Pi and coefficient-homomorphism square before descent.
private def matrixSectionRingHom :
    (∀ i, Matrix J J (R i)) →+* Matrix J J (F.Product R) :=
  (RingHom.mapMatrix (productRingCon F R).mk').comp
    (Matrix.piRingEquiv (n := J) (β := R)).symm.toRingHom

private theorem matrixEquiv_coe_eq_sectionHom (A : ∀ i, Matrix J J (R i)) :
    matrixCarrierEquiv (J := J) F R (A : F.Product (fun i => Matrix J J (R i))) =
      matrixSectionRingHom (J := J) F R A := by
  rw [matrixEquiv_coe]
  rfl

private theorem matrixEquiv_mk' (A : ∀ i, Matrix J J (R i)) :
    matrixCarrierEquiv (J := J) F R
        ((productRingCon F (fun i => Matrix J J (R i))).mk' A) =
      matrixSectionRingHom (J := J) F R A := by
  have hqM : (productRingCon F (fun i => Matrix J J (R i))).mk' A =
      (A : F.Product (fun i => Matrix J J (R i))) :=
    congrFun (RingCon.coe_mk' (c := productRingCon F (fun i => Matrix J J (R i)))) A
  exact (congrArg (matrixCarrierEquiv (J := J) F R) hqM).trans
    (matrixEquiv_coe_eq_sectionHom F R A)

/-- The reduced product of finite square matrix rings is the matrix ring over the
scalar reduced product, with the same given semiring records and matrix indices. -/
noncomputable def matrixRingEquiv :
    @RingEquiv (F.Product (fun i => Matrix J J (R i))) (Matrix J J (F.Product R))
      (@instSemiring ι F (fun i => Matrix J J (R i))
        (fun i => @Matrix.semiring (α := R i) (n := J) (s i) fJ dJ)).toMul
      (@Matrix.semiring (α := F.Product R) (n := J)
        (@instSemiring ι F R s) fJ dJ).toMul
      (@instSemiring ι F (fun i => Matrix J J (R i))
        (fun i => @Matrix.semiring (α := R i) (n := J) (s i) fJ dJ)).toAdd
      (@Matrix.semiring (α := F.Product R) (n := J)
        (@instSemiring ι F R s) fJ dJ).toAdd where
  toEquiv :=
    (piEquiv F (fun i (_ : J) => J → R i)).trans
      ((Equiv.piCongrRight (fun _ : J => piEquiv F (fun i (_ : J) => R i))).trans
        Matrix.of)
  map_mul' x y := by
    change matrixCarrierEquiv (J := J) F R (x * y) =
      matrixCarrierEquiv (J := J) F R x * matrixCarrierEquiv (J := J) F R y
    let qM : (∀ i, Matrix J J (R i)) →+* F.Product (fun i => Matrix J J (R i)) :=
      (productRingCon F (fun i => Matrix J J (R i))).mk'
    have hE (A : ∀ i, Matrix J J (R i)) :
        matrixCarrierEquiv (J := J) F R (qM A) =
          matrixSectionRingHom (J := J) F R A := matrixEquiv_mk' F R A
    have hsurj : Function.Surjective qM :=
      (productRingCon F (fun i => Matrix J J (R i))).mk'_surjective
    obtain ⟨A, rfl⟩ := hsurj x
    obtain ⟨B, rfl⟩ := hsurj y
    calc
      matrixCarrierEquiv (J := J) F R (qM A * qM B) =
          matrixCarrierEquiv (J := J) F R (qM (A * B)) :=
        congrArg (matrixCarrierEquiv (J := J) F R) (qM.map_mul A B).symm
      _ = matrixSectionRingHom (J := J) F R (A * B) := hE (A * B)
      _ = matrixSectionRingHom (J := J) F R A *
          matrixSectionRingHom (J := J) F R B :=
        (matrixSectionRingHom (J := J) F R).map_mul A B
      _ = matrixCarrierEquiv (J := J) F R (qM A) *
          matrixCarrierEquiv (J := J) F R (qM B) :=
        congrArg₂ (fun U V : Matrix J J (F.Product R) => U * V) (hE A).symm (hE B).symm
  map_add' x y := by
    change matrixCarrierEquiv (J := J) F R (x + y) =
      matrixCarrierEquiv (J := J) F R x + matrixCarrierEquiv (J := J) F R y
    let qM : (∀ i, Matrix J J (R i)) →+* F.Product (fun i => Matrix J J (R i)) :=
      (productRingCon F (fun i => Matrix J J (R i))).mk'
    have hE (A : ∀ i, Matrix J J (R i)) :
        matrixCarrierEquiv (J := J) F R (qM A) =
          matrixSectionRingHom (J := J) F R A := matrixEquiv_mk' F R A
    have hsurj : Function.Surjective qM :=
      (productRingCon F (fun i => Matrix J J (R i))).mk'_surjective
    obtain ⟨A, rfl⟩ := hsurj x
    obtain ⟨B, rfl⟩ := hsurj y
    calc
      matrixCarrierEquiv (J := J) F R (qM A + qM B) =
          matrixCarrierEquiv (J := J) F R (qM (A + B)) :=
        congrArg (matrixCarrierEquiv (J := J) F R) (qM.map_add A B).symm
      _ = matrixSectionRingHom (J := J) F R (A + B) := hE (A + B)
      _ = matrixSectionRingHom (J := J) F R A +
          matrixSectionRingHom (J := J) F R B :=
        (matrixSectionRingHom (J := J) F R).map_add A B
      _ = matrixCarrierEquiv (J := J) F R (qM A) +
          matrixCarrierEquiv (J := J) F R (qM B) :=
        congrArg₂ (fun U V : Matrix J J (F.Product R) => U + V) (hE A).symm (hE B).symm

/-- The comparison sends a represented matrix section to its matrix of entry classes. -/
theorem matrixRingEquiv_coe (A : ∀ i, Matrix J J (R i)) :
    matrixRingEquiv (J := J) F R (A : F.Product (fun i => Matrix J J (R i))) =
      Matrix.of (fun j k => ((fun i => A i j k) : F.Product R)) := by
  exact matrixEquiv_coe F R A

/-- Every entry of the comparison is the existing product map given by entry evaluation. -/
theorem matrixRingEquiv_apply
    (x : F.Product (fun i => Matrix J J (R i))) (j k : J) :
    matrixRingEquiv (J := J) F R x j k =
      map F (fun i (A : Matrix J J (R i)) => A j k) x := by
  obtain ⟨A, rfl⟩ := coe_surjective F (fun i => Matrix J J (R i)) x
  exact (congrArg (fun M : Matrix J J (F.Product R) => M j k)
    (matrixRingEquiv_coe (J := J) F R A)).trans
      (map_coe F (fun i (M : Matrix J J (R i)) => M j k) A).symm

/-- The inverse comparison assembles simultaneously represented entries into matrices. -/
theorem matrixRingEquiv_symm_coe (a : J → J → ∀ i, R i) :
    (matrixRingEquiv (J := J) F R).symm
        (Matrix.of (fun j k => (a j k : F.Product R))) =
      ((fun i => Matrix.of (fun j k => a j k i)) :
        F.Product (fun i => Matrix J J (R i))) := by
  apply (matrixRingEquiv (J := J) F R).injective
  exact ((matrixRingEquiv (J := J) F R).apply_symm_apply _).trans
    (matrixRingEquiv_coe (J := J) F R (fun i => Matrix.of (fun j k => a j k i))).symm

/-- Entry evaluation after the inverse comparison recovers each entry of the given matrix. -/
theorem matrixRingEquiv_symm_apply (B : Matrix J J (F.Product R)) (j k : J) :
    map F (fun i (A : Matrix J J (R i)) => A j k)
        ((matrixRingEquiv (J := J) F R).symm B) = B j k := by
  exact (matrixRingEquiv_apply (J := J) F R
    ((matrixRingEquiv (J := J) F R).symm B) j k).symm.trans
      (congrArg (fun M : Matrix J J (F.Product R) => M j k)
        ((matrixRingEquiv (J := J) F R).apply_symm_apply B))

/-- A represented matrix over the scalar reduced product is invertible exactly when
those same fibre matrices are invertible on a filter-large set. -/
theorem isUnit_matrix_coe_iff (A : ∀ i, Matrix J J (R i)) :
    @IsUnit (Matrix J J (F.Product R))
        (@Matrix.semiring (α := F.Product R) (n := J)
          (@instSemiring ι F R s) fJ dJ).toMonoid
        (Matrix.of (fun j k => ((fun i => A i j k) : F.Product R))) ↔
      ∀ᶠ i in F, @IsUnit (Matrix J J (R i))
        (@Matrix.semiring (α := R i) (n := J) (s i) fJ dJ).toMonoid (A i) := by
  have h :
      @IsUnit (Matrix J J (F.Product R))
          (@Matrix.semiring (α := F.Product R) (n := J)
            (@instSemiring ι F R s) fJ dJ).toMonoid
          (Matrix.of (fun j k => ((fun i => A i j k) : F.Product R))) ↔
        @IsUnit (F.Product (fun i => Matrix J J (R i)))
          (@instSemiring ι F (fun i => Matrix J J (R i))
            (fun i => @Matrix.semiring (α := R i) (n := J) (s i) fJ dJ)).toMonoid
          (A : F.Product (fun i => Matrix J J (R i))) := by
    have hmap := @MulEquiv.isUnit_map
      (@MulEquiv (F.Product (fun i => Matrix J J (R i))) (Matrix J J (F.Product R))
        (@instSemiring ι F (fun i => Matrix J J (R i))
          (fun i => @Matrix.semiring (α := R i) (n := J) (s i) fJ dJ)).toMul
        (@Matrix.semiring (α := F.Product R) (n := J)
          (@instSemiring ι F R s) fJ dJ).toMul)
      (F.Product (fun i => Matrix J J (R i))) (Matrix J J (F.Product R))
      (@instSemiring ι F (fun i => Matrix J J (R i))
        (fun i => @Matrix.semiring (α := R i) (n := J) (s i) fJ dJ)).toMonoid
      (@Matrix.semiring (α := F.Product R) (n := J)
        (@instSemiring ι F R s) fJ dJ).toMonoid
      inferInstance inferInstance (matrixRingEquiv (J := J) F R).toMulEquiv
      (A : F.Product (fun i => Matrix J J (R i)))
    exact Eq.mp (congrArg (fun B : Matrix J J (F.Product R) =>
      IsUnit B ↔ @IsUnit (F.Product (fun i => Matrix J J (R i)))
        (@instSemiring ι F (fun i => Matrix J J (R i))
          (fun i => @Matrix.semiring (α := R i) (n := J) (s i) fJ dJ)).toMonoid
        (A : F.Product (fun i => Matrix J J (R i))))
      (matrixRingEquiv_coe (J := J) F R A)) hmap
  exact h.trans (isUnit_coe_iff F A)

end Filter.Product
