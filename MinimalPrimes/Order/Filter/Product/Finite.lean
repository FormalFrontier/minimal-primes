/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

public import Mathlib.RingTheory.Finiteness.Defs
public import MinimalPrimes.Order.Filter.Product.Module
public import MinimalPrimes.Order.Filter.Product.Pi

/-!
# Uniform finite generators of dependent reduced products

The finite-spanning criterion compares the germs of a given finite family of
sections with that same family's pointwise spans on one eventual locus. The
finite-generation criterion asks for one natural-number bound on the number of
fibre generators, not just eventual finite generation of the individual fibres.
Both statements use the given additive and module records, including when the
scalar and vector carrier families coincide. No properness assumption is imposed
on the filter, and either index type may be empty.

The proof compares the existing finite linear-combination maps through the
Product map and Pi comparison. The representative equation follows from the
given scalar action and the additive homomorphism on section germs; only
surjectivity of the Pi comparison is needed.

## References

The criteria use Mathlib's finite-generation and span interfaces and Formal
Frontier's dependent Product semimodule data. The finite-spanning formulation is
informed by Mathlib's Finsupp linear-combination and finite-function interfaces
of Johannes Hölzl, together with the existing Product map and Pi comparison.
-/

@[expose] public section

universe uι uR uM uJ

namespace Filter.Product

variable {ι : Type uι} {J : Type uJ}
variable (F : Filter ι) (M : ι → Type uM) (R : ι → Type uR)
variable [s : ∀ i, Semiring (R i)] [a : ∀ i, AddCommMonoid (M i)]
variable [p : ∀ i, @Module (R i) (M i) (s i) (a i)]

private theorem linearCombination_coe
    [fJ : Fintype J] (g : J → ∀ i, M i) (c : ∀ i, J → R i) :
    @Fintype.linearCombination J (F.Product M) (F.Product R) fJ
        (@instSemiring ι F R s) (@addCommMonoid ι F M a)
        (module (s := s) (a := a) (p := p) F M R)
        (fun j => (g j : F.Product M))
        (fun j => ((fun i => c i j) : F.Product R)) =
      ((fun i =>
        @Fintype.linearCombination J (M i) (R i) fJ (s i) (a i) (p i)
          (fun j => g j i) (c i)) : F.Product M) := by
  let AM : AddCommMonoid (F.Product M) := @addCommMonoid ι F M a
  let q : (∀ i, M i) →+ F.Product M := @coeAddMonoidHom ι F M a
  have hq (m : ∀ i, M i) : q m = (m : F.Product M) :=
    @coeAddMonoidHom_apply ι F M a m
  have hsmul (r : ∀ i, R i) (m : ∀ i, M i) :
      @SMul.smul (F.Product R) (F.Product M)
          (module (s := s) (a := a) (p := p) F M R).toSMul
          (r : F.Product R) (m : F.Product M) =
        ((fun i => r i • m i) : F.Product M) := by
    exact (congrArg
      (fun t : SMul (F.Product R) (F.Product M) =>
        @SMul.smul (F.Product R) (F.Product M) t
          (r : F.Product R) (m : F.Product M))
      (module_toSMul (s := s) (a := a) (p := p) F M R)).trans
        (@coe_smul ι F M R (fun i => (p i).toSMul) r m)
  have hsum :
      (∑ j, (fun i => c i j • g j i)) =
        (fun i =>
          @Fintype.linearCombination J (M i) (R i) fJ (s i) (a i) (p i)
            (fun j => g j i) (c i)) := by
    funext i
    calc
      (∑ j, (fun k => c k j • g j k)) i = ∑ j, c i j • g j i :=
        Finset.sum_apply i Finset.univ (fun j k => c k j • g j k)
      _ = _ :=
        (Fintype.linearCombination_apply (R i) (fun j => g j i) (c i)).symm
  have hlinear :
      @Fintype.linearCombination J (F.Product M) (F.Product R) fJ
          (@instSemiring ι F R s) (@addCommMonoid ι F M a)
          (module (s := s) (a := a) (p := p) F M R)
          (fun j => (g j : F.Product M))
          (fun j => ((fun i => c i j) : F.Product R)) =
        ∑ j, @SMul.smul (F.Product R) (F.Product M)
          (module (s := s) (a := a) (p := p) F M R).toSMul
          ((fun i => c i j) : F.Product R) (g j : F.Product M) :=
    @Fintype.linearCombination_apply J (F.Product M) (F.Product R) fJ
      (@instSemiring ι F R s) (@addCommMonoid ι F M a)
      (module (s := s) (a := a) (p := p) F M R)
      (fun j => (g j : F.Product M))
      (fun j => ((fun i => c i j) : F.Product R))
  have hpointwise :
      (∑ j, @SMul.smul (F.Product R) (F.Product M)
        (module (s := s) (a := a) (p := p) F M R).toSMul
        ((fun i => c i j) : F.Product R) (g j : F.Product M)) =
        ∑ j, q (fun i => c i j • g j i) := by
    apply Finset.sum_congr rfl
    intro j _
    exact (hsmul (fun i => c i j) (g j)).trans (hq _).symm
  have hmap :
      q (∑ j, (fun i => c i j • g j i)) =
        ∑ j, q (fun i => c i j • g j i) :=
    _root_.map_sum q (fun j => (fun i => c i j • g j i)) Finset.univ
  exact hlinear.trans
    (hpointwise.trans (hmap.symm.trans ((congrArg q hsum).trans (hq _))))

/-- The coordinate map of finite linear combinations factors through the
existing finite-coordinate comparison and the combination of vector germs. -/
theorem linearCombination_comparison
    [fJ : Fintype J] (g : J → ∀ i, M i) :
    map F (fun i =>
        (@Fintype.linearCombination J (M i) (R i) fJ (s i) (a i) (p i)
          (fun j => g j i) : (J → R i) → M i)) =
      (@Fintype.linearCombination J (F.Product M) (F.Product R) fJ
        (@instSemiring ι F R s) (@addCommMonoid ι F M a)
        (module (s := s) (a := a) (p := p) F M R)
        (fun j => (g j : F.Product M)) :
          (J → F.Product R) → F.Product M) ∘
        piComparison F (fun i (_ : J) => R i) := by
  symm
  refine map_unique F _ _ ?_
  intro c
  have hc :
      piComparison F (fun i (_ : J) => R i)
          (c : F.Product (fun i => J → R i)) =
        (fun j => ((fun i => c i j) : F.Product R)) := by
    funext j
    exact piComparison_coe F (fun i (_ : J) => R i) c j
  exact
    (congrArg
      (@Fintype.linearCombination J (F.Product M) (F.Product R) fJ
        (@instSemiring ι F R s) (@addCommMonoid ι F M a)
        (module (s := s) (a := a) (p := p) F M R)
        (fun j => (g j : F.Product M)) :
          (J → F.Product R) → F.Product M) hc).trans
      (linearCombination_coe F M R g c)

/-- Germs of a given finite family span the reduced-product semimodule if and
only if the same pointwise family spans on one eventual locus. -/
theorem span_range_coe_eq_top_iff [Finite J] (g : J → ∀ i, M i) :
    @Submodule.span (F.Product R) (F.Product M)
        (@instSemiring ι F R s) (@addCommMonoid ι F M a)
        (module (s := s) (a := a) (p := p) F M R)
        (Set.range fun j => (g j : F.Product M)) = ⊤ ↔
      ∀ᶠ i in F,
        @Submodule.span (R i) (M i) (s i) (a i) (p i)
          (Set.range fun j => g j i) = ⊤ := by
  classical
  let fJ : Fintype J := Fintype.ofFinite J
  let ℓ : ∀ i, (J → R i) → M i := fun i =>
    ((@Fintype.linearCombination J (M i) (R i) fJ
        (s i) (a i) (p i) (fun j => g j i)) :
      (J → R i) → M i)
  let L : (J → F.Product R) → F.Product M :=
    ((@Fintype.linearCombination J (F.Product M) (F.Product R) fJ
        (@instSemiring ι F R s) (@addCommMonoid ι F M a)
        (module (s := s) (a := a) (p := p) F M R)
        (fun j => (g j : F.Product M))) :
      (J → F.Product R) → F.Product M)
  let Δ : F.Product (fun i => J → R i) → F.Product M := map F ℓ
  let χ : F.Product (fun i => J → R i) → (J → F.Product R) :=
    piComparison F (fun i (_ : J) => R i)
  have hΔ : Δ = L ∘ χ :=
    linearCombination_comparison (s := s) (a := a) (p := p)
      (fJ := fJ) F M R g
  have hχ : Function.Surjective χ :=
    piComparison_surjective F (fun i (_ : J) => R i)
  have hspan :
      @Submodule.span (F.Product R) (F.Product M)
          (@instSemiring ι F R s) (@addCommMonoid ι F M a)
          (module (s := s) (a := a) (p := p) F M R)
          (Set.range fun j => (g j : F.Product M)) = ⊤ ↔
        Function.Surjective L :=
    @span_range_eq_top_iff_surjective_fintypeLinearCombination
      J (F.Product M) (F.Product R) fJ
      (@instSemiring ι F R s) (@addCommMonoid ι F M a)
      (module (s := s) (a := a) (p := p) F M R)
      (fun j => (g j : F.Product M))
  have hLΔ : Function.Surjective L ↔ Function.Surjective Δ := by
    rw [hΔ]
    exact (Function.Surjective.of_comp_iff L hχ).symm
  have hmap : Function.Surjective Δ ↔
      ∀ᶠ i in F, Function.Surjective (ℓ i) := by
    constructor
    · intro hsurj
      rcases (map_surjective_iff F ℓ).1 hsurj with hEmpty | ⟨_, hgood⟩
      · exact False.elim
          (hEmpty.false (fun i => @Zero.zero (M i) (a i).toZero))
      · exact hgood
    · intro hgood
      exact (map_surjective_iff F ℓ).2
        (Or.inr ⟨⟨fun i (_ : J) => @Zero.zero (R i) (s i).toZero⟩, hgood⟩)
  have hpoint (i : ι) :
      @Submodule.span (R i) (M i) (s i) (a i) (p i)
          (Set.range fun j => g j i) = ⊤ ↔
        Function.Surjective (ℓ i) :=
    @span_range_eq_top_iff_surjective_fintypeLinearCombination
      J (M i) (R i) fJ (s i) (a i) (p i) (fun j => g j i)
  have hfibres :
      (∀ᶠ i in F, Function.Surjective (ℓ i)) ↔
        ∀ᶠ i in F,
          @Submodule.span (R i) (M i) (s i) (a i) (p i)
            (Set.range fun j => g j i) = ⊤ := by
    constructor
    · intro hgood
      exact hgood.mono fun i hi => (hpoint i).2 hi
    · intro hgood
      exact hgood.mono fun i hi => (hpoint i).1 hi
  exact hspan.trans (hLΔ.trans (hmap.trans hfibres))

/-- The reduced-product semimodule is finitely generated if and only if the
fibre semimodules have a uniform finite bound on generators on one eventual locus. -/
theorem moduleFinite_iff :
    @Module.Finite (F.Product R) (F.Product M)
        (@instSemiring ι F R s) (@addCommMonoid ι F M a)
        (module (s := s) (a := a) (p := p) F M R) ↔
      ∃ n : ℕ, ∀ᶠ i in F, ∃ v : Fin n → M i,
        @Submodule.span (R i) (M i) (s i) (a i) (p i) (Set.range v) = ⊤ := by
  classical
  let AF_M : AddCommMonoid (F.Product M) := @addCommMonoid ι F M a
  let PF_M : Module (F.Product R) (F.Product M) :=
    module (s := s) (a := a) (p := p) F M R
  constructor
  · intro h
    obtain ⟨n, v, hv⟩ :=
      @Module.Finite.exists_fin (F.Product R) (F.Product M)
        (@instSemiring ι F R s) (@addCommMonoid ι F M a)
        (module (s := s) (a := a) (p := p) F M R) h
    have hrep : Function.Surjective
        (Pi.map (fun _ : Fin n =>
          fun m : ∀ i, M i => (m : F.Product M))) :=
      Function.Surjective.piMap (fun _ : Fin n => coe_surjective F M)
    obtain ⟨g, hg⟩ := hrep v
    have hfamily : (fun j : Fin n => (g j : F.Product M)) = v := hg
    have hspan :
        @Submodule.span (F.Product R) (F.Product M)
          (@instSemiring ι F R s) (@addCommMonoid ι F M a)
          (module (s := s) (a := a) (p := p) F M R)
          (Set.range fun j : Fin n => (g j : F.Product M)) = ⊤ := by
      exact (congrArg (fun v : Fin n → F.Product M =>
        @Submodule.span (F.Product R) (F.Product M)
          (@instSemiring ι F R s) (@addCommMonoid ι F M a)
          (module (s := s) (a := a) (p := p) F M R) (Set.range v)) hfamily).trans hv
    have hev :=
      (span_range_coe_eq_top_iff (s := s) (a := a) (p := p) F M R g).1 hspan
    exact ⟨n, hev.mono (fun i hi => ⟨fun j => g j i, hi⟩)⟩
  · rintro ⟨n, hn⟩
    let : ∀ i, Nonempty (Fin n → M i) :=
      fun i => ⟨fun _ => (0 : M i)⟩
    obtain ⟨v, hv⟩ :=
      (Filter.skolem (F := F)
        (P := fun i (v : Fin n → M i) =>
          @Submodule.span (R i) (M i) (s i) (a i) (p i)
            (Set.range v) = ⊤)).1 hn
    let g : Fin n → ∀ i, M i := fun j i => v i j
    have hspan :
        @Submodule.span (F.Product R) (F.Product M)
          (@instSemiring ι F R s) (@addCommMonoid ι F M a)
          (module (s := s) (a := a) (p := p) F M R)
          (Set.range fun j : Fin n => (g j : F.Product M)) = ⊤ :=
      (span_range_coe_eq_top_iff (s := s) (a := a) (p := p) F M R g).2 hv
    exact (Module.finite_def (R := F.Product R) (M := F.Product M)).2
      (Submodule.fg_iff_exists_fin_generating_family.2
        ⟨n, fun j : Fin n => (g j : F.Product M), hspan⟩)

end Filter.Product
