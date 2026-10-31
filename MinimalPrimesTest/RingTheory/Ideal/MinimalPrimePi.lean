/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import MinimalPrimes.RingTheory.Ideal.MinimalPrimePi

/-!
# Repeated semiring factors retain distinct minimal primes

The two equal factors of `ℕ × ℕ`, written as a dependent product, give distinct
minimal primes. This uses the public equivalence in a semiring that is not a ring.
-/

/-- Repeated natural-number factors contribute two distinct labelled minimal primes. -/
example : ∃ p q : (⊥ : Ideal (Fin 2 → ℕ)).minimalPrimes, p ≠ q := by
  let I : Ideal (Fin 2 → ℕ) := ⊥
  have h (i : Fin 2) : (⊥ : Ideal ℕ) ∈ (Ideal.piOrderIso I i).minimalPrimes := by
    change (⊥ : Ideal ℕ) ∈ ((⊥ : Ideal (Fin 2 → ℕ)).map _).minimalPrimes
    simp [Ideal.minimalPrimes_eq_subsingleton_self]
  let a : Σ i, (Ideal.piOrderIso I i).minimalPrimes := ⟨0, ⟨⊥, h 0⟩⟩
  let b : Σ i, (Ideal.piOrderIso I i).minimalPrimes := ⟨1, ⟨⊥, h 1⟩⟩
  refine ⟨(Ideal.minimalPrimesPiEquiv I).symm a,
    (Ideal.minimalPrimesPiEquiv I).symm b, ?_⟩
  intro hab
  have hab' := (Ideal.minimalPrimesPiEquiv I).symm.injective hab
  have hi := congrArg Sigma.fst hab'
  exact Fin.zero_ne_one hi
