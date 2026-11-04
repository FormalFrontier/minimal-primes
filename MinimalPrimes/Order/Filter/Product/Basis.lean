/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.StdBasis
public import MinimalPrimes.Order.Filter.Product.Module
public import MinimalPrimes.Order.Filter.Product.Pi

/-!
# Common finite bases of dependent reduced products

A given family of bases with one common finite index induces a basis of the
reduced-product semimodule over the existing reduced-product scalar semiring.
The vector additive and module records are those of the given fibres, including
when the scalar and vector families have the same carriers. The basis index may
be empty and the filter need not be proper.

The construction composes the existing varying map of the fibre coordinate
equivalences with `Filter.Product.piEquiv`, then uses `Module.Basis.ofEquivFun`.
The vector and coefficient equations characterize the resulting basis, and the
standard function bases recover `Filter.Product.piComparison` on all quotient
points. Stock basis extensionality and reconstruction apply to this basis.

## References

This construction uses the dependent Product module and finite-coordinate APIs
of Formal Frontier, Mathlib's basis interfaces of Johannes Hölzl, Mario Carneiro
and Alexander Bentkamp, the finite Finsupp/function and standard-basis interfaces
of Johannes Hölzl, and the Pi-module interfaces of Simon Hudon and Patrick Massot.
-/

@[expose] public section

universe uι uR uM uJ

namespace Filter.Product

variable {ι : Type uι} {J : Type uJ}
variable (F : Filter ι) (M : ι → Type uM) (R : ι → Type uR)
variable [s : ∀ i, Semiring (R i)] [a : ∀ i, AddCommMonoid (M i)]
variable [p : ∀ i, @Module (R i) (M i) (s i) (a i)] [Finite J]

private noncomputable def basisEquivFun
    (b : ∀ i, @Module.Basis J (R i) (M i) (s i) (a i) (p i)) :
    @LinearEquiv (F.Product R) (F.Product R)
      (@instSemiring ι F R s) (@instSemiring ι F R s)
      (RingHom.id (F.Product R)) (RingHom.id (F.Product R)) inferInstance inferInstance
      (F.Product M) (J → F.Product R)
      (@addCommMonoid ι F M a)
      (@Pi.addCommMonoid J (fun _ : J => F.Product R)
        (fun _ => (@instSemiring ι F R s).toAddCommMonoid))
      (module (s := s) (a := a) (p := p) F M R)
      (@Pi.module J (fun _ : J => F.Product R) (F.Product R)
        (@instSemiring ι F R s)
        (fun _ => (@instSemiring ι F R s).toAddCommMonoid)
        (fun _ => @Semiring.toModule (F.Product R) (@instSemiring ι F R s))) := by
  let C := fun i => J → R i
  let aC : ∀ i, AddCommMonoid (C i) := fun i =>
    @Pi.addCommMonoid J (fun _ : J => R i) (fun _ => (s i).toAddCommMonoid)
  let pC : ∀ i, @Module (R i) (C i) (s i) (aC i) := fun i =>
    @Pi.module J (fun _ : J => R i) (R i) (s i)
      (fun _ => (s i).toAddCommMonoid) (fun _ => @Semiring.toModule (R i) (s i))
  letI AF_M : AddCommMonoid (F.Product M) := @addCommMonoid ι F M a
  letI PF_M : Module (F.Product R) (F.Product M) :=
    module (s := s) (a := a) (p := p) F M R
  letI AF_C : AddCommMonoid (F.Product C) := @addCommMonoid ι F C aC
  letI PF_C : Module (F.Product R) (F.Product C) :=
    module (s := s) (a := aC) (p := pC) F C R
  let e : ∀ i, M i ≃ₗ[R i] C i := fun i => (b i).equivFun
  let E : F.Product M ≃ₗ[F.Product R] F.Product C :=
    { toFun := map F (fun i => (e i : M i → C i))
      invFun := map F (fun i => ((e i).symm : C i → M i))
      left_inv := by
        intro x
        have h : (fun i (m : M i) => (e i).symm (e i m)) =
            (fun i (m : M i) => m) := by
          funext i m
          exact (e i).symm_apply_apply m
        rw [map_map, h, map_id]
        rfl
      right_inv := by
        intro x
        have h : (fun i (c : C i) => e i ((e i).symm c)) =
            (fun i (c : C i) => c) := by
          funext i c
          exact (e i).apply_symm_apply c
        rw [map_map, h, map_id]
        rfl
      map_add' := by
        let qM : (∀ i, M i) →+ F.Product M := coeAddMonoidHom F M
        let qC : (∀ i, C i) →+ F.Product C := coeAddMonoidHom F C
        have hmap (m : ∀ i, M i) :
            map F (fun i => (e i : M i → C i)) (qM m) =
              qC (fun i => e i (m i)) := map_coe F (fun i => (e i : M i → C i)) m
        intro x y
        obtain ⟨m, rfl⟩ := coe_surjective F M x
        obtain ⟨n, rfl⟩ := coe_surjective F M y
        change map F (fun i => (e i : M i → C i)) (qM m + qM n) =
          map F (fun i => (e i : M i → C i)) (qM m) +
            map F (fun i => (e i : M i → C i)) (qM n)
        rw [← qM.map_add, hmap, hmap, hmap, ← qC.map_add]
        apply congrArg qC
        funext i
        exact (e i).map_add (m i) (n i)
      map_smul' := by
        let qR : (∀ i, R i) →+* F.Product R := (productRingCon F R).mk'
        let qM : (∀ i, M i) →+ F.Product M := coeAddMonoidHom F M
        let qC : (∀ i, C i) →+ F.Product C := coeAddMonoidHom F C
        have hM (r : ∀ i, R i) (m : ∀ i, M i) :
            qR r • qM m = qM (fun i => r i • m i) := coe_smul F M R r m
        have hC (r : ∀ i, R i) (c : ∀ i, C i) :
            qR r • qC c = qC (fun i => r i • c i) := coe_smul F C R r c
        have hmap (m : ∀ i, M i) :
            map F (fun i => (e i : M i → C i)) (qM m) =
              qC (fun i => e i (m i)) := map_coe F (fun i => (e i : M i → C i)) m
        intro r x
        obtain ⟨r, rfl⟩ := coe_surjective F R r
        obtain ⟨m, rfl⟩ := coe_surjective F M x
        change map F (fun i => (e i : M i → C i)) (qR r • qM m) =
          qR r • map F (fun i => (e i : M i → C i)) (qM m)
        rw [hM, hmap, hmap, hC]
        apply congrArg qC
        funext i
        exact (e i).map_smul (r i) (m i) }
  let qR : (∀ i, R i) →+* F.Product R := (productRingCon F R).mk'
  let qC : (∀ i, C i) →+ F.Product C := coeAddMonoidHom F C
  have hPi (m : ∀ i, C i) (j : J) :
      piEquiv F (fun i (_ : J) => R i) (qC m) j = qR (fun i => m i j) :=
    (congrFun (piEquiv_apply F (fun i (_ : J) => R i) (qC m)) j).trans
      (piComparison_coe F (fun i (_ : J) => R i) m j)
  let P : F.Product C ≃ₗ[F.Product R] (J → F.Product R) :=
    { toEquiv := piEquiv F (fun i (_ : J) => R i)
      map_add' := by
        intro x y
        obtain ⟨m, rfl⟩ := coe_surjective F C x
        obtain ⟨n, rfl⟩ := coe_surjective F C y
        change piEquiv F (fun i (_ : J) => R i) (qC m + qC n) =
          piEquiv F (fun i (_ : J) => R i) (qC m) +
            piEquiv F (fun i (_ : J) => R i) (qC n)
        rw [← qC.map_add]
        funext j
        simp only [hPi, Pi.add_apply]
        change qR ((fun i => m i j) + (fun i => n i j)) =
          qR (fun i => m i j) + qR (fun i => n i j)
        exact qR.map_add (fun i => m i j) (fun i => n i j)
      map_smul' := by
        have hC (r : ∀ i, R i) (c : ∀ i, C i) :
            qR r • qC c = qC (fun i => r i • c i) := coe_smul F C R r c
        intro r x
        obtain ⟨r, rfl⟩ := coe_surjective F R r
        obtain ⟨m, rfl⟩ := coe_surjective F C x
        change piEquiv F (fun i (_ : J) => R i) (qR r • qC m) =
          qR r • piEquiv F (fun i (_ : J) => R i) (qC m)
        rw [hC]
        funext j
        simp only [hPi, Pi.smul_apply, smul_eq_mul]
        change qR (r * (fun i => m i j)) = qR r * qR (fun i => m i j)
        exact qR.map_mul r (fun i => m i j) }
  exact E.trans P

attribute [local instance] addCommMonoid module

/-- The basis induced by given fibre bases with a common finite index, in the
semimodule with the given additive and scalar-action records. -/
@[no_expose]
noncomputable def basis
    (b : ∀ i, @Module.Basis J (R i) (M i) (s i) (a i) (p i)) :
    @Module.Basis J (F.Product R) (F.Product M)
      (@instSemiring ι F R s) (@addCommMonoid ι F M a)
      (module (s := s) (a := a) (p := p) F M R) :=
  Module.Basis.ofEquivFun (basisEquivFun F M R b)

section Characteristic

variable (b : ∀ i, @Module.Basis J (R i) (M i) (s i) (a i) (p i))

private theorem basis_equivFun_apply (x : F.Product M) :
    (basis F M R b).equivFun x =
      piComparison F (fun i (_ : J) => R i)
        (map F (fun i => ((b i).equivFun : M i → J → R i)) x) := by
  rw [basis, Module.Basis.equivFun_ofEquivFun]
  change piEquiv F (fun i (_ : J) => R i) _ = _
  exact piEquiv_apply F (fun i (_ : J) => R i) _

/-- The coefficient of a represented vector is represented by its fibre coefficients. -/
theorem basis_repr_coe (m : ∀ i, M i) (j : J) :
    (basis F M R b).repr (m : F.Product M) j =
      ((fun i => (b i).repr (m i) j) : F.Product R) := by
  calc
    _ = (basis F M R b).equivFun (m : F.Product M) j := rfl
    _ = _ := by
      simpa only [map_coe, piComparison_coe, Module.Basis.equivFun_apply] using
        congrFun (basis_equivFun_apply F M R b (m : F.Product M)) j

/-- Coefficients on every quotient vector agree with the existing varying map. -/
theorem basis_repr_apply (x : F.Product M) (j : J) :
    (basis F M R b).repr x j =
      map F (fun i (m : M i) => (b i).repr m j) x := by
  obtain ⟨m, rfl⟩ := coe_surjective F M x
  rw [basis_repr_coe, map_coe]

/-- Each induced basis vector is represented by the corresponding fibre basis vectors. -/
theorem basis_apply (j : J) :
    basis F M R b j = ((fun i => b i j) : F.Product M) := by
  classical
  apply (basis F M R b).ext_elem
  intro k
  rw [basis_repr_coe F M R b (fun i => b i j) k]
  by_cases h : j = k
  · simp only [Module.Basis.repr_self_apply, h, ↓reduceIte]
    erw [coe_one (F := F) (K := R)]
  · simp only [Module.Basis.repr_self_apply, h, ↓reduceIte]
    erw [coe_zero (F := F) (K := R)]

end Characteristic

/-- For standard function bases the whole coordinate function is the existing
finite-coordinate comparison, including on opaque quotient points. -/
theorem basis_piBasisFun_equivFun
    (x : F.Product (fun i => J → R i)) :
    (basis (s := s)
      (a := fun i => @Pi.addCommMonoid J (fun _ : J => R i)
        (fun _ => (s i).toAddCommMonoid))
      (p := fun i => @Pi.module J (fun _ : J => R i) (R i) (s i)
        (fun _ => (s i).toAddCommMonoid) (fun _ => @Semiring.toModule (R i) (s i)))
      F (fun i => J → R i) R (fun i => Pi.basisFun (R i) J)).equivFun x =
      piComparison F (fun i (_ : J) => R i) x := by
  rw [basis_equivFun_apply]
  simp only [Pi.basisFun_equivFun]
  change piComparison F (fun i (_ : J) => R i)
    (map F (fun i (m : J → R i) => m) x) = _
  rw [map_id]
  rfl

end Filter.Product
