/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MinimalPrimes.RingTheory.Ideal.PrimePiUltrafilter
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Data.ZMod.Basic

/-!
# Clients of the product-ideal/filter correspondence

These examples use independent universes, an empty product, ordinary semiring
constructors, principal filters, and the finite-support ideal on the natural
numbers. Nonnegative reals give genuine non-ring semifield coefficients; this
example does not claim that their addition is noncancellative.
-/

@[expose] public section

open Set Filter

universe u v

noncomputable example {ι : Type u} (K : ι → Type v) [∀ i, DivisionSemiring (K i)] :
    Ideal (Π i, K i) ≃o (Filter ι)ᵒᵈ := Ideal.piOrderIsoFilter K

noncomputable example (K : Empty → Type v) [∀ i, Semifield (K i)] :
    Ideal (Π i, K i) ≃o (Filter Empty)ᵒᵈ := Ideal.piOrderIsoFilter K

example {ι : Type u} (A : ι → Type v) [∀ i, Semiring (A i)] (s : Set ι) (f : Π i, A i) :
    f ∈ (principal s).piIdeal A ↔ ∀ i ∈ s, f i = 0 :=
  Filter.mem_piIdeal_principal A s f

-- A principal filter tests only the first coordinate, unlike the coordinate product ideal.
example :
    (![0, 1] : Fin 2 → ℕ) ∈
        Ideal.pi (fun _ : Fin 2 => (⊥ : Ideal ℕ)) ⊔
          (principal {0} : Filter (Fin 2)).piIdeal (fun _ => ℕ) ∧
      (![0, 1] : Fin 2 → ℕ) ∉ Ideal.pi (fun _ : Fin 2 => (⊥ : Ideal ℕ)) := by
  constructor
  · rw [Filter.mem_pi_sup_piIdeal]
    simp
  · intro h
    have h₁ := (Ideal.mem_pi _ _).mp h 1
    simp at h₁

-- Properness at a non-ultrafilter is not membership of the complementary locus.
example :
    let I : Fin 2 → Ideal ℕ := ![⊥, ⊤]
    Ideal.pi I ⊔ (⊤ : Filter (Fin 2)).piIdeal (fun _ => ℕ) ≠ ⊤ ∧
      {i | I i ≠ ⊤} ∉ (⊤ : Filter (Fin 2)) := by
  dsimp only
  constructor
  · rw [Filter.pi_sup_piIdeal_ne_top_iff, Filter.mem_top_iff_forall]
    intro h
    simpa using h 0
  · rw [Filter.mem_top_iff_forall]
    intro h
    simpa using h 1

-- A principal filter distinguishes the zero fibre from the nontrivial fibre.
example :
    let R : Bool → Type := fun b => ZMod (if b then 2 else 1)
    Ideal.pi (fun b => (⊥ : Ideal (R b))) ⊔ (principal {false}).piIdeal R = ⊤ ∧
      Ideal.pi (fun b => (⊥ : Ideal (R b))) ⊔ (principal {true}).piIdeal R ≠ ⊤ := by
  dsimp only
  constructor
  · rw [Filter.pi_sup_piIdeal_eq_top_iff, Filter.mem_principal]
    intro b hb
    have hb' : b = false := by simpa using hb
    subst b
    apply (Ideal.eq_top_iff_one _).mpr
    change (1 : ZMod 1) ∈ (⊥ : Ideal (ZMod 1))
    rw [Subsingleton.elim (1 : ZMod 1) 0]
    exact (⊥ : Ideal (ZMod 1)).zero_mem
  · rw [Filter.pi_sup_piIdeal_ne_top_iff, Filter.mem_principal]
    intro h
    have htrue := h (by simp : true ∈ ({true} : Set Bool))
    simp at htrue

example {ι : Type u} (R : Type v) [Semiring R] (F : Filter ι) :
    F.piIdeal (fun _ : ι => R) = RingHom.ker (Filter.Germ.coeRingHom (R := R) F) :=
  Filter.piIdeal_eq_ker_coeRingHom R F

example {ι : Type u} (K : ι → Type v) [∀ i, DivisionSemiring (K i)]
    (I : Ideal (Π i, K i)) (f : Π i, K i) :
    {i | f i = 0} ∈ I.piFilter K ↔ f ∈ I := by simp

example {ι : Type u} (K : ι → Type v) [∀ i, Semifield (K i)]
    (f : Π i, K i) :
    (Ideal.span {f}).piFilter K = principal {i | f i = 0} := by simp

example (f : Fin 2 → NNReal) :
    f ∈ (principal {0}).piIdeal (fun _ : Fin 2 => NNReal) ↔ f 0 = 0 := by simp

example (i : Fin 2) (x : NNReal) :
    x ∈ (Ideal.piOrderIso
      ((principal {0}).piIdeal (fun _ : Fin 2 => NNReal))) i ↔ (i = 0 → x = 0) := by
  simpa using Filter.mem_piOrderIso_piIdeal_principal
    (fun _ : Fin 2 => NNReal) {0} i x

example : (Pi.single 0 1 : ℕ → NNReal) ∈
    (cofinite : Filter ℕ).piIdeal (fun _ : ℕ => NNReal) := by
  rw [Filter.mem_piIdeal_cofinite]
  apply Set.Finite.subset (Set.finite_singleton 0)
  intro i hi
  by_contra hn
  have hne : i ≠ 0 := by simpa using hn
  exact hi (by simp [hne])

example : (Pi.single 0 1 : ℕ → NNReal) ≠ 0 := by
  intro h
  have := congrFun h 0
  simp at this

example : (1 : ℕ → NNReal) ∉ (cofinite : Filter ℕ).piIdeal (fun _ : ℕ => NNReal) := by
  rw [Filter.mem_piIdeal_cofinite]
  simpa using (Set.infinite_univ : Set.Infinite (Set.univ : Set ℕ))

example (f : ℕ → NNReal) :
    (cofinite : Filter ℕ).piIdeal (fun _ : ℕ => NNReal) ≠ Ideal.span {f} :=
  Ideal.piIdeal_cofinite_ne_span_singleton _ f

example {ι : Type u} (K : ι → Type v) [∀ i, Semifield (K i)] (U : Ultrafilter ι) :
    U.piIdeal K = (U : Filter ι).piIdeal K := Ultrafilter.piIdeal_eq_filter_piIdeal K U

example {ι : Type u} (K : ι → Type v) [∀ i, Semifield (K i)]
    (p : PrimeSpectrum (Π i, K i)) :
    (p.piUltrafilter K : Filter ι) = p.asIdeal.piFilter K := by simp
