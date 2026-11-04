/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import CoherentModules.FinitePresentation
import MinimalPrimes.Order.Filter.Product.Basis
import MinimalPrimes.Order.Filter.Product.Finite

public import Mathlib.Algebra.Module.FinitePresentation
public import MinimalPrimes.Order.Filter.Product.Exact

/-!
# Uniform finite presentations of dependent reduced products

For families of possibly noncommutative rings and their given modules, the
criterion below asks for one pair of finite free sizes bounding generators and
relations on one eventual locus. The additive and module records on the vector
fibres are retained, even when scalar and vector carriers coincide.

The scalar semiring is the existing `Filter.Product.instSemiring`. Its addition,
multiplication and zero are represented coordinatewise; represented coordinate
negation gives each scalar an additive inverse. Thus this ring-family scope has
the ordinary generators-and-relations meaning. A module over a ring already has
additive inverses with its given addition and action; no additional additive-group
hypothesis is needed. The coefficient function spaces alone use standard
self-actions.

## Limitations

Mathlib defines `Module.FinitePresentation` already over semirings by a finite
spanning set with finitely generated zero kernel. For general semirings that is
not a congruence presentation. The ring hypotheses here are intentional: additive
inverses identify equal-image relations with differences in the zero kernel.

## References

The proof uses Andrew Yang's Mathlib finite-presentation interfaces and the
finite-free presentation theorems in Formal Frontier's
[coherent-module library](https://github.com/FormalFrontier/coherent-modules/blob/33941aae67dfb0df15b6e325dba9c86b9f649893/CoherentModules/FinitePresentation.lean).
It combines Antoine Chambert-Loir's `Function.Exact` with the existing dependent
Product module, finite-basis, finite-combination and exactness interfaces.
It introduces no new presentation data.
-/

@[expose] public section

universe uι uR uM

namespace Filter.Product

variable {ι : Type uι}
variable (F : Filter ι) (M : ι → Type uM) (R : ι → Type uR)
variable [r : ∀ i, Ring (R i)] [a : ∀ i, AddCommMonoid (M i)]
variable [p : ∀ i, @Module (R i) (M i) (r i).toSemiring (a i)]

private theorem linearCombination_basis
    {A : Type*} {N : Type*} [Semiring A] [AddCommMonoid N] [Module A N]
    (n : ℕ) (f : (Fin n → A) →ₗ[A] N) :
    Fintype.linearCombination A (fun j => f (Pi.basisFun A (Fin n) j)) = f := by
  classical
  apply (Pi.basisFun A (Fin n)).ext
  intro j
  simp only [Pi.basisFun_apply, Fintype.linearCombination_apply_single, one_smul]

private theorem finite_free_exact_iff (n m : ℕ)
    (v : Fin n → ∀ i, M i) (w : Fin m → ∀ i, Fin n → R i) :
    let : AddCommMonoid (F.Product M) := @addCommMonoid ι F M a
    let : Module (F.Product R) (F.Product M) :=
      module (s := fun i => (r i).toSemiring) (a := a) (p := p) F M R
    let C := fun i => Fin n → R i
    let aC : ∀ i, AddCommMonoid (C i) := fun _ => inferInstance
    let pC : ∀ i, Module (R i) (C i) := fun _ => inferInstance
    let : AddCommMonoid (F.Product C) := @addCommMonoid ι F C aC
    let : Module (F.Product R) (F.Product C) :=
      module (s := fun i => (r i).toSemiring) (a := aC) (p := pC) F C R
    let E := (basis (s := fun i => (r i).toSemiring) (a := aC) (p := pC)
      F C R (fun i => Pi.basisFun (R i) (Fin n))).equivFun
    let L := Fintype.linearCombination (M := F.Product M) (F.Product R)
      (fun j => (v j : F.Product M))
    let H := Fintype.linearCombination (M := F.Product C) (F.Product R)
      (fun k => (w k : F.Product C))
    (Function.Surjective L ∧ Function.Exact (E.toLinearMap.comp H) L) ↔
      ∀ᶠ i in F,
        Function.Surjective (Fintype.linearCombination (R i) (fun j => v j i)) ∧
        Function.Exact (Fintype.linearCombination (R i) (fun k => w k i))
          (Fintype.linearCombination (R i) (fun j => v j i)) := by
  classical
  let : AddCommMonoid (F.Product M) := @addCommMonoid ι F M a
  let : Module (F.Product R) (F.Product M) :=
    module (s := fun i => (r i).toSemiring) (a := a) (p := p) F M R
  let C := fun i => Fin n → R i
  let aC : ∀ i, AddCommMonoid (C i) := fun _ => inferInstance
  let pC : ∀ i, Module (R i) (C i) := fun _ => inferInstance
  let : AddCommMonoid (F.Product C) := @addCommMonoid ι F C aC
  let : Module (F.Product R) (F.Product C) :=
    module (s := fun i => (r i).toSemiring) (a := aC) (p := pC) F C R
  let E := (basis (s := fun i => (r i).toSemiring) (a := aC) (p := pC)
    F C R (fun i => Pi.basisFun (R i) (Fin n))).equivFun
  let L := Fintype.linearCombination (M := F.Product M) (F.Product R)
      (fun j => (v j : F.Product M))
  let H := Fintype.linearCombination (M := F.Product C) (F.Product R)
      (fun k => (w k : F.Product C))
  let f := fun i => Fintype.linearCombination (R i) (fun j => v j i)
  let g := fun i => Fintype.linearCombination (R i) (fun k => w k i)
  let χ := piComparison F (fun i (_ : Fin m) => R i)
  have hE : (E : F.Product C → Fin n → F.Product R) =
      piComparison F (fun i (_ : Fin n) => R i) := by
    funext x
    exact basis_piBasisFun_equivFun (s := fun i => (r i).toSemiring) F R x
  have hf : map F (fun i => (f i : C i → M i)) = L ∘ E := by
    rw [hE]
    exact linearCombination_comparison (s := fun i => (r i).toSemiring)
      (a := a) (p := p) F M R v
  have hg : map F (fun i => (g i : (Fin m → R i) → C i)) = H ∘ χ :=
    linearCombination_comparison (s := fun i => (r i).toSemiring)
      (a := aC) (p := pC) F C R w
  have hsurj : Function.Surjective L ↔ ∀ᶠ i in F, Function.Surjective (f i) := by
    have heq : Function.Surjective L ↔
        Function.Surjective (map F (fun i => (f i : C i → M i))) := by
      rw [hf]
      exact (Function.Surjective.of_comp_iff L E.surjective).symm
    refine heq.trans ?_
    constructor
    · intro h
      rcases (map_surjective_iff F (fun i => (f i : C i → M i))).1 h with h | ⟨_, h⟩
      · exact False.elim (h.false (fun i => (0 : M i)))
      · exact h
    · intro h
      exact (map_surjective_iff F (fun i => (f i : C i → M i))).2
        (Or.inr ⟨⟨fun i => (0 : C i)⟩, h⟩)
  have hexact : Function.Exact (E.toLinearMap.comp H) L ↔
      Function.Exact (map F (fun i => (g i : (Fin m → R i) → C i)))
        (map F (fun i => (f i : C i → M i))) := by
    rw [hf, hg]
    have hconj := LinearEquiv.conj_exact_iff_exact H (L.comp E.toLinearMap) E
    have hsimp : (L.comp E.toLinearMap).comp E.symm.toLinearMap = L := by
      apply LinearMap.ext
      intro x
      exact congrArg L (E.apply_symm_apply x)
    rw [hsimp] at hconj
    exact hconj.trans (by
      apply forall_congr'
      intro y
      exact iff_congr Iff.rfl (by
        rw [(piComparison_surjective F (fun i (_ : Fin m) => R i)).range_comp H]))
  let : Nonempty (∀ i, Fin m → R i) := ⟨fun i => 0⟩
  have hpoint := map_exact_iff_of_addZeroClass F
    (fun i => (g i : (Fin m → R i) → C i)) (fun i => (f i : C i → M i))
  exact (and_congr hsurj (hexact.trans hpoint)).trans Filter.eventually_and.symm

/-- A reduced product of the given ring modules is finitely presented exactly
when one pair of finite free sizes gives surjective exact presentations of the
fibres on one eventual locus. -/
theorem moduleFinitePresentation_iff :
    @Module.FinitePresentation (F.Product R) (F.Product M)
        (@instSemiring ι F R (fun i => (r i).toSemiring))
        (@addCommMonoid ι F M a)
        (module (s := fun i => (r i).toSemiring) (a := a) (p := p) F M R) ↔
      ∃ n m : ℕ, ∀ᶠ i in F,
        ∃ f : @LinearMap (R i) (R i) (r i).toSemiring (r i).toSemiring
          (@RingHom.id (R i) (r i).toNonAssocSemiring) (Fin n → R i) (M i)
          (@Pi.addCommMonoid (Fin n) (fun _ => R i)
            (fun _ => (r i).toAddCommMonoid)) (a i)
          (@Pi.module (Fin n) (fun _ => R i) (R i) (r i).toSemiring
            (fun _ => (r i).toAddCommMonoid)
            (fun _ => @Semiring.toModule (R i) (r i).toSemiring)) (p i),
        ∃ g : @LinearMap (R i) (R i) (r i).toSemiring (r i).toSemiring
          (@RingHom.id (R i) (r i).toNonAssocSemiring) (Fin m → R i) (Fin n → R i)
          (@Pi.addCommMonoid (Fin m) (fun _ => R i)
            (fun _ => (r i).toAddCommMonoid))
          (@Pi.addCommMonoid (Fin n) (fun _ => R i)
            (fun _ => (r i).toAddCommMonoid))
          (@Pi.module (Fin m) (fun _ => R i) (R i) (r i).toSemiring
            (fun _ => (r i).toAddCommMonoid)
            (fun _ => @Semiring.toModule (R i) (r i).toSemiring))
          (@Pi.module (Fin n) (fun _ => R i) (R i) (r i).toSemiring
            (fun _ => (r i).toAddCommMonoid)
            (fun _ => @Semiring.toModule (R i) (r i).toSemiring)),
          Function.Surjective f ∧
            @Function.Exact (Fin m → R i) (Fin n → R i) (M i) g f (a i).toZero := by
  classical
  let : AddCommMonoid (F.Product M) := @addCommMonoid ι F M a
  let : Module (F.Product R) (F.Product M) :=
    module (s := fun i => (r i).toSemiring) (a := a) (p := p) F M R
  constructor
  · intro h
    let : Module.FinitePresentation (F.Product R) (F.Product M) := h
    obtain ⟨n, m, f, g, hf, hg⟩ :=
      Module.FinitePresentation.exists_fin_exact (F.Product R) (F.Product M)
    obtain ⟨v, hv⟩ :=
      (Function.Surjective.piMap (fun _ : Fin n => coe_surjective F M))
        (fun j => f (Pi.basisFun (F.Product R) (Fin n) j))
    let C := fun i => Fin n → R i
    let aC : ∀ i, AddCommMonoid (C i) := fun _ => inferInstance
    let pC : ∀ i, Module (R i) (C i) := fun _ => inferInstance
    let : AddCommMonoid (F.Product C) := @addCommMonoid ι F C aC
    let : Module (F.Product R) (F.Product C) :=
      module (s := fun i => (r i).toSemiring) (a := aC) (p := pC) F C R
    let E := (basis (s := fun i => (r i).toSemiring) (a := aC) (p := pC)
      F C R (fun i => Pi.basisFun (R i) (Fin n))).equivFun
    obtain ⟨w, hw⟩ :=
      (Function.Surjective.piMap (fun _ : Fin m => coe_surjective F C))
        (fun k => E.symm (g (Pi.basisFun (F.Product R) (Fin m) k)))
    have hL : Fintype.linearCombination (M := F.Product M) (F.Product R)
        (fun j => (v j : F.Product M)) = f := by
      rw [show (fun j => (v j : F.Product M)) =
        (fun j => f (Pi.basisFun (F.Product R) (Fin n) j)) from hv]
      exact linearCombination_basis n f
    have hG : E.toLinearMap.comp
        (Fintype.linearCombination (M := F.Product C) (F.Product R)
          (fun k => (w k : F.Product C))) = g := by
      apply (Pi.basisFun (F.Product R) (Fin m)).ext
      intro k
      have hvalue :
          Fintype.linearCombination (M := F.Product C) (F.Product R)
            (fun k => (w k : F.Product C))
            (Pi.basisFun (F.Product R) (Fin m) k) = (w k : F.Product C) := by
        simpa only [Pi.basisFun_apply] using
          (Fintype.linearCombination_apply_single (M := F.Product C)
            (F.Product R) (fun k => (w k : F.Product C)) k 1).trans
              (one_smul (α := F.Product C) (F.Product R) (w k : F.Product C))
      change E (Fintype.linearCombination (M := F.Product C) (F.Product R)
        (fun k => (w k : F.Product C)) (Pi.basisFun (F.Product R) (Fin m) k)) = _
      exact (congrArg E hvalue).trans
        ((congrArg E (congrFun hw k)).trans (E.apply_symm_apply _))
    have hrow := (finite_free_exact_iff F M R n m v w).1 (by
      rw [hL, hG]
      exact ⟨hf, hg⟩)
    refine ⟨n, m, hrow.mono ?_⟩
    intro i hi
    exact ⟨_, _, hi⟩
  · rintro ⟨n, m, h⟩
    let B := fun i => ((Fin n → R i) →ₗ[R i] M i) ×
      ((Fin m → R i) →ₗ[R i] (Fin n → R i))
    let : ∀ i, Nonempty (B i) := fun i => ⟨(0, 0)⟩
    obtain ⟨q, hq⟩ := (Filter.skolem (F := F)
      (P := fun i (q : B i) => Function.Surjective q.1 ∧ Function.Exact q.2 q.1)).1
        (h.mono fun i ⟨f, g, hf, hg⟩ => ⟨(f, g), hf, hg⟩)
    let v : Fin n → ∀ i, M i := fun j i => (q i).1 (Pi.basisFun (R i) (Fin n) j)
    let w : Fin m → ∀ i, Fin n → R i :=
      fun k i => (q i).2 (Pi.basisFun (R i) (Fin m) k)
    have hpoint : ∀ᶠ i in F,
        Function.Surjective (Fintype.linearCombination (R i) (fun j => v j i)) ∧
        Function.Exact (Fintype.linearCombination (R i) (fun k => w k i))
          (Fintype.linearCombination (R i) (fun j => v j i)) := by
      simpa only [v, w, linearCombination_basis] using hq
    have hrow := (finite_free_exact_iff F M R n m v w).2 hpoint
    let L := Fintype.linearCombination (M := F.Product M) (F.Product R)
      (fun j => (v j : F.Product M))
    exact Module.FinitePresentation.of_free_of_surjective L hrow.1 (by
      rw [hrow.2.linearMap_ker_eq]
      exact Submodule.fg_range _)

end Filter.Product
