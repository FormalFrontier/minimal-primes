/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MinimalPrimes.RingTheory.Ideal.FiniteHeightChain
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Data.Fin.Basic
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# A nonstabilizing prime chain of infinite initial height

For a field `K`, let `P n` be the kernel of Mathlib's `MvPolynomial.killCompl` for
`Fin.val : Fin n → ℕ`. This map retains the first `n` variables of `K[X₀, X₁, ...]`
and kills the rest. Its codomain `MvPolynomial (Fin n) K` is a domain, so every
`P n` is prime. The coefficient formula for `killCompl` gives antitonicity.
The variable `X n` belongs to `P n` but not to `P (n + 1)`, giving a strict drop
at every successor and ruling out any constant tail.

The finite-initial-height stabilization theorem then proves that `P 0` does not
have `Ideal.FiniteHeight`. Mathlib's numerical criterion converts this to
`(P 0).height = ⊤` in `ENat`; the initial prime is proper and nonzero. The ring is
not Noetherian, since the canonical Noetherian finite-height instance would
contradict this same obstruction. No ambient dimension computation is used.
The rational-coefficient example instantiates all of these conclusions.

## References

* `MinimalPrimes.RingTheory.Ideal.FiniteHeightChain`: the finite-initial-height
  prime-chain stabilization theorem and its proof via a well-founded lower interval
  in the prime spectrum.
* Mathlib, `Mathlib.Algebra.MvPolynomial.Rename`: `killCompl`, `coeff_killCompl`,
  the monomial vanishing formula, and the left inverse to `rename`.
* Mathlib, `Mathlib.RingTheory.Ideal.Maps`: primeness of a kernel with domain codomain.
* Mathlib, `Mathlib.RingTheory.Ideal.Height` and
  `Mathlib.RingTheory.Ideal.KrullsHeightTheorem`: the numerical finite-height
  criterion and the Noetherian finite-height instance.
-/

public section

universe u

noncomputable section

namespace InfiniteHeightPrimeChainExamples

variable (K : Type u) [Field K]

private def tailPrime (n : ℕ) : Ideal (MvPolynomial ℕ K) :=
  RingHom.ker (MvPolynomial.killCompl
    (Fin.val_injective : Function.Injective (Fin.val : Fin n → ℕ))).toRingHom

private theorem mem_tailPrime_iff (n : ℕ) (p : MvPolynomial ℕ K) :
    p ∈ tailPrime K n ↔
      MvPolynomial.killCompl
        (Fin.val_injective : Function.Injective (Fin.val : Fin n → ℕ)) p = 0 :=
  RingHom.mem_ker

private theorem tailPrime_isPrime (n : ℕ) : (tailPrime K n).IsPrime :=
  RingHom.ker_isPrime (MvPolynomial.killCompl
    (Fin.val_injective : Function.Injective (Fin.val : Fin n → ℕ))).toRingHom

private theorem tailPrime_ne_top (n : ℕ) : tailPrime K n ≠ ⊤ :=
  (tailPrime_isPrime K n).ne_top

private theorem mem_tailPrime_iff_coeff (n : ℕ) (p : MvPolynomial ℕ K) :
    p ∈ tailPrime K n ↔
      ∀ s : Fin n →₀ ℕ, p.coeff (s.mapDomain Fin.val) = 0 := by
  rw [mem_tailPrime_iff]
  constructor
  · intro hp s
    simpa only [MvPolynomial.coeff_killCompl, AddMonoidAlgebra.coeff_zero,
      Finsupp.zero_apply] using
      congrArg (fun q : MvPolynomial (Fin n) K => q.coeff s) hp
  · intro hp
    apply MvPolynomial.ext
    intro s
    simpa only [MvPolynomial.coeff_killCompl, AddMonoidAlgebra.coeff_zero,
      Finsupp.zero_apply] using hp s

private theorem tailPrime_antitone : Antitone (tailPrime K) := by
  intro m n hmn p hp
  apply (mem_tailPrime_iff_coeff K m p).mpr
  intro s
  have hs := (mem_tailPrime_iff_coeff K n p).mp hp (s.mapDomain (Fin.castLE hmn))
  rw [← Finsupp.mapDomain_comp] at hs
  simpa only [Function.comp_def, Fin.val_castLE] using hs

private theorem X_mem_tailPrime (n : ℕ) :
    (MvPolynomial.X n : MvPolynomial ℕ K) ∈ tailPrime K n := by
  classical
  apply (mem_tailPrime_iff K n _).mpr
  have hn : n ∉ Set.range (Fin.val : Fin n → ℕ) := by
    rintro ⟨i, hi⟩
    exact (ne_of_lt i.isLt) hi
  simpa only [← MvPolynomial.X_pow_eq_monomial, pow_one] using
    (MvPolynomial.killCompl_monomial_eq_zero_of_notMem_range
      (Fin.val_injective : Function.Injective (Fin.val : Fin n → ℕ)) (1 : K)
      (show n ∈ (Finsupp.single n 1 : ℕ →₀ ℕ).support by simp) hn)

private theorem X_notMem_tailPrime_succ (n : ℕ) :
    (MvPolynomial.X n : MvPolynomial ℕ K) ∉ tailPrime K (n + 1) := by
  intro hx
  have hzero := (mem_tailPrime_iff K (n + 1) _).mp hx
  let i : Fin (n + 1) := ⟨n, Nat.lt_succ_self n⟩
  have hkeep :
      MvPolynomial.killCompl
        (Fin.val_injective : Function.Injective (Fin.val : Fin (n + 1) → ℕ))
        (MvPolynomial.X n : MvPolynomial ℕ K) = MvPolynomial.X i := by
    simpa only [MvPolynomial.rename_X] using
      (MvPolynomial.killCompl_rename_app
        (Fin.val_injective : Function.Injective (Fin.val : Fin (n + 1) → ℕ))
        (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) K))
  exact MvPolynomial.X_ne_zero i (hkeep.symm.trans hzero)

private theorem tailPrime_succ_lt (n : ℕ) : tailPrime K (n + 1) < tailPrime K n := by
  refine lt_of_le_of_ne (tailPrime_antitone K (Nat.le_succ n)) ?_
  intro heq
  exact X_notMem_tailPrime_succ K n (heq.symm ▸ X_mem_tailPrime K n)

private theorem tailPrime_initial_ne_bot : tailPrime K 0 ≠ ⊥ := by
  intro h
  have hX : (MvPolynomial.X 0 : MvPolynomial ℕ K) ∈ (⊥ : Ideal (MvPolynomial ℕ K)) :=
    h ▸ X_mem_tailPrime K 0
  simp only [Ideal.mem_bot] at hX
  exact MvPolynomial.X_ne_zero (R := K) 0 hX

private theorem tailPrime_not_eventually_constant :
    ∀ N : ℕ, ∃ n ≥ N, tailPrime K n ≠ tailPrime K N := by
  intro N
  exact ⟨N + 1, Nat.le_succ N, ne_of_lt (tailPrime_succ_lt K N)⟩

private theorem tailPrime_initial_not_finiteHeight : ¬ (tailPrime K 0).FiniteHeight := by
  intro hfin
  let : (tailPrime K 0).FiniteHeight := hfin
  obtain ⟨N, hN, -⟩ := Ideal.exists_stable_of_antitone_of_finiteHeight
    (tailPrime K) (tailPrime_antitone K) (tailPrime_isPrime K)
  obtain ⟨n, hn, hne⟩ := tailPrime_not_eventually_constant K N
  exact hne (hN n hn)

private theorem tailPrime_initial_height_eq_top : (tailPrime K 0).height = ⊤ := by
  classical
  by_contra hheight
  exact tailPrime_initial_not_finiteHeight K
    (Ideal.finiteHeight_iff_lt.mpr (Or.inr (lt_top_iff_ne_top.mpr hheight)))

private theorem not_isNoetherianRing : ¬ IsNoetherianRing (MvPolynomial ℕ K) := by
  intro hnoeth
  let : IsNoetherianRing (MvPolynomial ℕ K) := hnoeth
  exact tailPrime_initial_not_finiteHeight K
    (Ideal.finiteHeight_of_isNoetherianRing (tailPrime K 0))

/-- Countably many variables over `ℚ` admit a prime chain with a strict drop at every
successor and no constant tail. Its initial ideal is proper, nonzero and of infinite height;
the polynomial ring is not Noetherian. -/
theorem exists_nonstabilizing_prime_chain :
    ∃ J : ℕ → Ideal (MvPolynomial ℕ ℚ),
      (∀ n, (J n).IsPrime) ∧ Antitone J ∧
        (∀ n, J (n + 1) < J n) ∧
        (∀ N, ∃ n ≥ N, J n ≠ J N) ∧
        J 0 ≠ ⊤ ∧ J 0 ≠ ⊥ ∧
        ¬ (J 0).FiniteHeight ∧ (J 0).height = ⊤ ∧
        ¬ IsNoetherianRing (MvPolynomial ℕ ℚ) :=
  ⟨tailPrime ℚ, tailPrime_isPrime ℚ, tailPrime_antitone ℚ, tailPrime_succ_lt ℚ,
    tailPrime_not_eventually_constant ℚ, tailPrime_ne_top ℚ 0,
    tailPrime_initial_ne_bot ℚ, tailPrime_initial_not_finiteHeight ℚ,
    tailPrime_initial_height_eq_top ℚ, not_isNoetherianRing ℚ⟩

end InfiniteHeightPrimeChainExamples
