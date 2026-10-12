/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import MinimalPrimes.RingTheory.Ideal.PrincipalPrimeHeight
import MinimalPrimes.RingTheory.Ideal.FiniteHeightChain
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Principal prime ideals in infinite-variable polynomial rings

For a field `K`, the variable `X₀` in `K[X₀, X₁, ...]` is prime and a non-zero-divisor.
All three principal-prime height results apply to its proper, nonzero principal ideal,
whose height is one. Mathlib supplies unique factorization and well-founded strict
divisibility for polynomial rings in arbitrary sets of variables. The zero ideal is
prime of height zero, while the ambient ring has infinite Krull dimension.

An ideal chain which stays at `(X₀)` through index `d` and then drops to zero is antitone
and consists of prime ideals. Its initial height one supplies `Ideal.FiniteHeight` through
Mathlib's numerical criterion. The ideal prime-chain interface then supplies a common
index for tail constancy and the all-index ideal infimum. For `d ≥ 1`, equality at the
first two indices coexists with a later genuine drop. No Noetherian hypothesis is used.

## References

The principal-prime height results are in
`MinimalPrimes.RingTheory.Ideal.PrincipalPrimeHeight`; the stabilization result is
`Ideal.exists_stable_of_antitone_of_finiteHeight` from
`MinimalPrimes.RingTheory.Ideal.FiniteHeightChain`. The constructions also use Mathlib's
polynomial unique-factorization and variable-prime APIs, principal-ideal primeness and
height lower bounds, numerical finite-height criterion, and infinite-variable
Krull-dimension API.
-/

universe u v

noncomputable section

namespace PrincipalPrimeHeightExamples

section PolynomialInstances

variable (σ : Type v) (K : Type u) [Field K]

example : CommRing (MvPolynomial σ K) := inferInstance

example : IsDomain (MvPolynomial σ K) := inferInstance

example : UniqueFactorizationMonoid (MvPolynomial σ K) := inferInstance

example : WfDvdMonoid (MvPolynomial σ K) := inferInstance

end PolynomialInstances

section InfinitePolynomial

variable (K : Type u) [Field K]

private theorem X_zero_prime : Prime (MvPolynomial.X 0 : MvPolynomial ℕ K) :=
  MvPolynomial.X_prime

private theorem span_X_zero_isPrime :
    (Ideal.span {MvPolynomial.X 0} : Ideal (MvPolynomial ℕ K)).IsPrime :=
  Ideal.isPrime_span_singleton_of_prime (X_zero_prime K)

private theorem span_X_zero_ne_top :
    (Ideal.span {MvPolynomial.X 0} : Ideal (MvPolynomial ℕ K)) ≠ ⊤ :=
  (span_X_zero_isPrime K).ne_top

private theorem span_X_zero_ne_bot :
    (Ideal.span {MvPolynomial.X 0} : Ideal (MvPolynomial ℕ K)) ≠ ⊥ := by
  intro h
  exact MvPolynomial.X_ne_zero 0 (Ideal.span_singleton_eq_bot.mp h)

private theorem X_zero_mem_nonZeroDivisors :
    (MvPolynomial.X 0 : MvPolynomial ℕ K) ∈ nonZeroDivisors (MvPolynomial ℕ K) :=
  mem_nonZeroDivisors_of_ne_zero (MvPolynomial.X_ne_zero 0)

private theorem height_span_X_zero_le_one :
    (Ideal.span {MvPolynomial.X 0} : Ideal (MvPolynomial ℕ K)).height ≤ 1 :=
  Ideal.height_span_singleton_le_one_of_prime (X_zero_prime K)

private theorem height_span_X_zero_eq_one_of_nonZeroDivisors :
    (Ideal.span {MvPolynomial.X 0} : Ideal (MvPolynomial ℕ K)).height = 1 :=
  Ideal.height_span_singleton_eq_one_of_prime_of_mem_nonZeroDivisors
    (X_zero_prime K) (X_zero_mem_nonZeroDivisors K)

private theorem height_span_X_zero_eq_one :
    (Ideal.span {MvPolynomial.X 0} : Ideal (MvPolynomial ℕ K)).height = 1 :=
  Ideal.height_span_singleton_eq_one_of_prime (X_zero_prime K)

private theorem one_le_height_span_X_zero :
    1 ≤ (Ideal.span {MvPolynomial.X 0} : Ideal (MvPolynomial ℕ K)).height :=
  Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors
    (X_zero_mem_nonZeroDivisors K)

private theorem bot_isPrime : (⊥ : Ideal (MvPolynomial ℕ K)).IsPrime :=
  inferInstance

private theorem bot_height : (⊥ : Ideal (MvPolynomial ℕ K)).height = 0 :=
  Ideal.height_bot

private theorem ringKrullDim_eq_top : ringKrullDim (MvPolynomial ℕ K) = ⊤ :=
  ringKrullDim_mvPolynomial_of_infinite

private noncomputable def variableDrop (d n : ℕ) : Ideal (MvPolynomial ℕ K) :=
  if n ≤ d then Ideal.span {MvPolynomial.X 0} else ⊥

private theorem variableDrop_isPrime (d n : ℕ) : (variableDrop K d n).IsPrime := by
  unfold variableDrop
  split_ifs
  · exact span_X_zero_isPrime K
  · exact bot_isPrime K

private theorem variableDrop_antitone (d : ℕ) : Antitone (variableDrop K d) := by
  intro i j hij
  by_cases hj : j ≤ d
  · have hi : i ≤ d := hij.trans hj
    simp only [variableDrop, ite_eq_left hj, ite_eq_left hi]
    exact le_rfl
  · simp only [variableDrop, ite_eq_right hj]
    exact bot_le

private theorem variableDrop_initial_height (d : ℕ) :
    (variableDrop K d 0).height = 1 := by
  simpa only [variableDrop, ite_eq_left (Nat.zero_le d)] using height_span_X_zero_eq_one K

private theorem variableDrop_initial_finiteHeight (d : ℕ) :
    (variableDrop K d 0).FiniteHeight := by
  refine Ideal.finiteHeight_iff_lt.mpr (Or.inr ?_)
  rw [variableDrop_initial_height K d]
  exact ENat.natCast_lt_top 1

private theorem variableDrop_initial_one_le_height (d : ℕ) :
    1 ≤ (variableDrop K d 0).height := by
  simpa only [variableDrop, ite_eq_left (Nat.zero_le d)] using one_le_height_span_X_zero K

private theorem variableDrop_ne_initial (d : ℕ) :
    variableDrop K d (d + 1) ≠ variableDrop K d 0 := by
  simp only [variableDrop, ite_eq_right (Nat.not_succ_le_self d), ite_eq_left (Nat.zero_le d)]
  exact (span_X_zero_ne_bot K).symm

private theorem variableDrop_adjacent_eq_then_ne {d : ℕ} (hd : 1 ≤ d) :
    variableDrop K d 0 = variableDrop K d 1 ∧
      variableDrop K d (d + 1) ≠ variableDrop K d 1 := by
  have hfirst : variableDrop K d 0 = variableDrop K d 1 := by
    simp only [variableDrop, ite_eq_left (Nat.zero_le d), ite_eq_left hd]
  refine ⟨hfirst, ?_⟩
  rw [← hfirst]
  exact variableDrop_ne_initial K d

-- Initial finite height comes from the numerical height result, not from a chain hypothesis.
private theorem variableDrop_height_and_exists_stable (d : ℕ) :
    (variableDrop K d 0).height = 1 ∧
      ∃ N : ℕ, (∀ n : ℕ, N ≤ n → variableDrop K d n = variableDrop K d N) ∧
        (⨅ n, variableDrop K d n) = variableDrop K d N := by
  let : (variableDrop K d 0).FiniteHeight := variableDrop_initial_finiteHeight K d
  exact ⟨variableDrop_initial_height K d,
    Ideal.exists_stable_of_antitone_of_finiteHeight (variableDrop K d)
      (variableDrop_antitone K d) (variableDrop_isPrime K d)⟩

end InfinitePolynomial

end PrincipalPrimeHeightExamples
