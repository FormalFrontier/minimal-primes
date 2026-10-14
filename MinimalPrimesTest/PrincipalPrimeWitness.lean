/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MinimalPrimes.Principal
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Ring.Prod
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.RingTheory.UniqueFactorizationDomain.Nat
public import Mathlib.Tactic.NormNum

/-!
# Applications of principal prime ideal witnesses

The explicit principal prime ideal `(2)` contains `6` and `2`, but avoids `3`.
The proper nonprime ideal `(6)` tests avoidance without primality. For inputs `2, 3, 6`
in `ℕ`, every prime witness contains at least one input, so disjunctive avoidance is sharp.
Over a field, inputs `1, 0, 0` yield bottom rather than a prime zero element. First projection
from the commutative semiring `ℕ × ℕ` illustrates contraction with zero divisors
and a nonzero kernel element, hence without injectivity.
-/

@[expose] public section

universe v

/-- A genuinely semiring example: the principal prime ideal `(2)` contains `6` and `2` but
avoids `3`, while `2` and `3` are relatively prime and `6` is a nonunit. -/
private theorem nat_two_prime_ideal_witness :
    let Q : Ideal ℕ := Ideal.span {2}
    IsRelPrime (2 : ℕ) 3 ∧ ¬ IsUnit (6 : ℕ) ∧ Q.IsPrime ∧ Q.IsPrincipal ∧
      (6 : ℕ) ∈ Q ∧ (2 : ℕ) ∈ Q ∧ ((2 : ℕ) ∉ Q ∨ (3 : ℕ) ∉ Q) := by
  dsimp only
  refine ⟨Nat.coprime_iff_isRelPrime.mp (by decide), ?_,
    Ideal.isPrime_span_singleton_of_prime Nat.prime_two.prime,
    inferInstance, ?_, Ideal.mem_span_singleton_self 2, Or.inr ?_⟩
  · norm_num [Nat.isUnit_iff]
  · norm_num [Ideal.mem_span_singleton]
  · norm_num [Ideal.mem_span_singleton]

/-- Avoidance for the proper nonprime ideal `(6)` forces `5` to lie outside it. -/
private theorem nat_six_avoids_five :
    let Q : Ideal ℕ := Ideal.span {6}
    Q ≠ ⊤ ∧ ¬ Q.IsPrime ∧ (6 : ℕ) ∈ Q ∧ (5 : ℕ) ∉ Q := by
  dsimp only
  have hproper : Ideal.span ({6} : Set ℕ) ≠ ⊤ := by
    intro htop
    have hunit : IsUnit (6 : ℕ) := Ideal.span_singleton_eq_top.mp htop
    norm_num [Nat.isUnit_iff] at hunit
  have h6 := Ideal.mem_span_singleton_self (6 : ℕ)
  have havoid := Ideal.not_mem_or_not_mem_of_isPrincipal_of_isRelPrime
    (Ideal.span ({6} : Set ℕ)) hproper
    (Nat.coprime_iff_isRelPrime.mp (by decide : Nat.Coprime 6 5))
  refine ⟨hproper, ?_, h6, havoid.resolve_left (fun h => h h6)⟩
  intro hprime
  have hmul : (2 : ℕ) * 3 ∈ Ideal.span ({6} : Set ℕ) := by
    norm_num [Ideal.mem_span_singleton]
  rcases hprime.mem_or_mem hmul with h2 | h3
  · norm_num [Ideal.mem_span_singleton] at h2
  · norm_num [Ideal.mem_span_singleton] at h3

/-- A prime witness for `6` must contain `2` or `3`; it cannot avoid both. -/
private theorem nat_six_prime_witness_contains_two_or_three :
    ∃ Q : Ideal ℕ, Q.IsPrime ∧ Q.IsPrincipal ∧ (6 : ℕ) ∈ Q ∧
      ((2 : ℕ) ∈ Q ∨ (3 : ℕ) ∈ Q) := by
  obtain ⟨Q, hprime, hprincipal, h6⟩ :=
    Ideal.exists_mem_principal_prime_of_not_isUnit
      (by norm_num [Nat.isUnit_iff] : ¬ IsUnit (6 : ℕ))
  exact ⟨Q, hprime, hprincipal, h6,
    hprime.mem_or_mem (show (2 : ℕ) * 3 ∈ Q from h6)⟩

/-- The paired witness for `2, 3, 6` contains exactly one of `2` and `3`. -/
private theorem nat_two_three_six_paired_witness :
    ∃ Q : Ideal ℕ, Q.IsPrime ∧ Q.IsPrincipal ∧ (6 : ℕ) ∈ Q ∧
      (((2 : ℕ) ∈ Q ∧ (3 : ℕ) ∉ Q) ∨ ((3 : ℕ) ∈ Q ∧ (2 : ℕ) ∉ Q)) := by
  obtain ⟨Q, hprime, hprincipal, h6, havoid⟩ :=
    Ideal.exists_mem_principal_prime_of_isRelPrime
      (Nat.coprime_iff_isRelPrime.mp (by decide : Nat.Coprime 2 3))
      (by norm_num [Nat.isUnit_iff] : ¬ IsUnit (6 : ℕ))
  have hmem := hprime.mem_or_mem (show (2 : ℕ) * 3 ∈ Q from h6)
  rcases havoid with h2 | h3
  · exact ⟨Q, hprime, hprincipal, h6, Or.inr ⟨hmem.resolve_left h2, h2⟩⟩
  · exact ⟨Q, hprime, hprincipal, h6, Or.inl ⟨hmem.resolve_right h3, h3⟩⟩

/-- Over a field, `1, 0, 0` give bottom with a zero generator that is not prime. -/
private theorem field_zero_witness_eq_bot (K : Type v) [Field K] :
    ∃ Q : Ideal K, Q = ⊥ ∧ Q.IsPrime ∧ Q.IsPrincipal ∧
      (0 : K) ∈ Q ∧ (1 : K) ∉ Q ∧ Ideal.span ({0} : Set K) = Q ∧ ¬ Prime (0 : K) := by
  obtain ⟨Q, hprime, hprincipal, h0, havoid⟩ :=
    Ideal.exists_mem_principal_prime_of_isRelPrime
      (isRelPrime_one_left : IsRelPrime (1 : K) 0) (by simp : ¬ IsUnit (0 : K))
  have hbottom : Q = ⊥ := (Ideal.eq_bot_or_top Q).resolve_right hprime.ne_top
  exact ⟨Q, hbottom, hprime, hprincipal, h0,
    havoid.resolve_right (fun h => h h0),
    Ideal.span_singleton_zero.trans hbottom.symm, fun h => h.ne_zero rfl⟩

/-- A zero-image input lies in a nonbottom contracted prime, even with source zero divisors. -/
private theorem nat_prod_first_projection_nonbot_witness :
    ∃ Q : Ideal ℕ, Q.IsPrime ∧ Q.IsPrincipal ∧
      (Q.comap (RingHom.fst ℕ ℕ)).IsPrime ∧ (Q.comap (RingHom.fst ℕ ℕ)).IsTwoSided ∧
      ((0, 1) : ℕ × ℕ) ∈ Q.comap (RingHom.fst ℕ ℕ) ∧
      (((2, 1) : ℕ × ℕ) ∉ Q.comap (RingHom.fst ℕ ℕ) ∨
        ((3, 1) : ℕ × ℕ) ∉ Q.comap (RingHom.fst ℕ ℕ)) ∧
      Q.comap (RingHom.fst ℕ ℕ) ≠ ⊥ ∧
      ((0, 1) : ℕ × ℕ) ∈ RingHom.ker (RingHom.fst ℕ ℕ) ∧
      ((1, 0) : ℕ × ℕ) ≠ 0 ∧ ((0, 1) : ℕ × ℕ) ≠ 0 ∧
      ((1, 0) : ℕ × ℕ) * (0, 1) = 0 := by
  have hab : IsRelPrime ((RingHom.fst ℕ ℕ) (2, 1)) ((RingHom.fst ℕ ℕ) (3, 1)) :=
    Nat.coprime_iff_isRelPrime.mp (by decide : Nat.Coprime 2 3)
  have hr : ¬ IsUnit ((RingHom.fst ℕ ℕ) (0, 1)) := by
    change ¬ IsUnit (0 : ℕ)
    simp
  obtain ⟨Q, hprime, hprincipal, hcomap, htwoSided, hmem, havoid⟩ :=
    Ideal.exists_comap_principal_prime_of_isRelPrime (RingHom.fst ℕ ℕ)
      (a := (2, 1)) (b := (3, 1)) (r := (0, 1)) hab hr
  refine ⟨Q, hprime, hprincipal, hcomap, htwoSided, hmem, havoid, ?_, ?_,
    by decide, by decide, by decide⟩
  · intro hbot
    have heq : ((0, 1) : ℕ × ℕ) = 0 := by
      simpa only [hbot, Submodule.mem_bot] using hmem
    exact (by decide : ((0, 1) : ℕ × ℕ) ≠ 0) heq
  · exact RingHom.mem_ker.mpr rfl
