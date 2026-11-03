/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.Data.Nat.Log
public import Mathlib.RingTheory.Noetherian.Nilpotent

/-!
# Reduced images of iterated Frobenius

An iterate of Frobenius has reduced semiring range if and only if it annihilates
every nilpotent element. For a Noetherian commutative semiring in positive prime
characteristic, all sufficiently high iterates have reduced ranges. The ranges
carry their inherited semiring or ring structures.

## References

The proof uses Mathlib's radical-kernel criterion
`RingHom.ker_isRadical_iff_reduced_of_surjective`, its restriction of a ring
homomorphism to its semiring range, and its nilpotent-power lemmas. The eventual
result uses `IsNoetherianRing.isNilpotent_nilradical`.
-/

@[expose] public section

universe u

/-- The semiring range of an iterate of Frobenius is reduced exactly when that
iterate kills every nilpotent element. -/
theorem isReduced_rangeS_iterateFrobenius_iff
    {R : Type u} [CommSemiring R] (p n : ℕ) [ExpChar R p] :
    IsReduced (iterateFrobenius R p n).rangeS ↔
      ∀ x : R, IsNilpotent x → x ^ (p ^ n) = 0 := by
  rw [← RingHom.ker_isRadical_iff_reduced_of_surjective
      (iterateFrobenius R p n).rangeSRestrict_surjective,
    RingHom.ker_rangeSRestrict]
  constructor
  · intro h x hx
    have hxker : x ∈ RingHom.ker (iterateFrobenius R p n) := by
      apply h
      rcases hx with ⟨m, hm⟩
      exact Ideal.mem_radical_iff.mpr
        ⟨m, RingHom.mem_ker.mpr (by rw [hm, map_zero])⟩
    simpa only [iterateFrobenius_def] using RingHom.mem_ker.mp hxker
  · intro h x hx
    have hxnil : IsNilpotent x := by
      apply IsNilpotent.of_pow (m := p ^ n)
      rcases Ideal.mem_radical_iff.mp hx with ⟨m, hm⟩
      refine ⟨m, ?_⟩
      simpa only [map_pow, iterateFrobenius_def] using RingHom.mem_ker.mp hm
    exact RingHom.mem_ker.mpr (by
      simpa only [iterateFrobenius_def] using h x hxnil)

/-- In a Noetherian commutative semiring of positive prime exponential
characteristic, every sufficiently high Frobenius iterate has reduced semiring
range. -/
theorem exists_forall_isReduced_rangeS_iterateFrobenius
    {R : Type u} [CommSemiring R] [IsNoetherianRing R]
    (p : ℕ) [ExpChar R p] [Fact p.Prime] :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      IsReduced (iterateFrobenius R p n).rangeS := by
  obtain ⟨k, hk⟩ := IsNoetherianRing.isNilpotent_nilradical R
  have hp : p.Prime := Fact.out
  refine ⟨(Nat.log p k).succ, ?_⟩
  intro n hn
  have hkpow : k ≤ p ^ n :=
    (Nat.lt_pow_succ_log_self hp.one_lt k).le.trans
      (pow_le_pow_right' hp.one_lt.le hn)
  apply (isReduced_rangeS_iterateFrobenius_iff p n).mpr
  intro x hx
  exact Ideal.pow_eq_zero_of_mem hk hkpow (mem_nilradical.mpr hx)

/-- In a Noetherian commutative ring of positive prime exponential
characteristic, every sufficiently high Frobenius iterate has reduced subring
range. -/
theorem exists_forall_isReduced_range_iterateFrobenius
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (p : ℕ) [ExpChar R p] [Fact p.Prime] :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      IsReduced (iterateFrobenius R p n).range := by
  obtain ⟨n₀, hn₀⟩ := exists_forall_isReduced_rangeS_iterateFrobenius (R := R) p
  exact ⟨n₀, hn₀⟩
