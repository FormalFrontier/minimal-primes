/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MinimalPrimes.Principal
import MinimalPrimes.IrreducibleComponents
import Mathlib.RingTheory.UniqueFactorizationDomain.Nat

/-!
# Minimal primes and irreducible components of `(6)` in the natural-number semiring

The standard normalization of `ℕ` gives two distinct proper prime ideals over
`(6)`, although `6` is neither zero nor a unit nor prime. The classification and
forward map are used through the principal-ideal API. The component equivalence
constructs two distinct irreducible components from the factor values `2` and `3`,
using a semiring without additive inverses.
-/

open UniqueFactorizationMonoid

section GenericClassification

/-! ## Generic principal-ideal examples: generic classification and the forward map -/

open UniqueFactorizationMonoid

universe u

noncomputable local instance readmeGenericNormalization (M : Type*) [CommMonoidWithZero M]
    [UniqueFactorizationMonoid M] : StrongNormalizationMonoid M :=
  UniqueFactorizationMonoid.strongNormalizationMonoid

variable {R : Type u} [CommSemiring R] [UniqueFactorizationMonoid R]

private theorem readme_classification {f : R} (hf : f ≠ 0) :
    (Ideal.span {f}).minimalPrimes =
      {P | ∃ p ∈ normalizedFactors f, P = Ideal.span {p}} :=
  Ideal.minimalPrimes_span_singleton_eq_normalizedFactors hf

private noncomputable def readme_minimalPrimes {f : R} (hf : f ≠ 0) :
    {p // p ∈ normalizedFactors f} ≃ (Ideal.span {f}).minimalPrimes :=
  Ideal.normalizedFactorsEquivMinimalPrimes hf

private theorem readme_forwardMap {f : R} (hf : f ≠ 0)
    (p : {p // p ∈ normalizedFactors f}) :
    (Ideal.normalizedFactorsEquivMinimalPrimes hf p).1 = Ideal.span {p.1} := by
  simp

end GenericClassification

section LocalNormalization

/-! ## Local normalization: a caller's local normalization choice -/

noncomputable local instance readmeNormalization (M : Type*) [CommMonoidWithZero M]
    [UniqueFactorizationMonoid M] : StrongNormalizationMonoid M :=
  UniqueFactorizationMonoid.strongNormalizationMonoid

end LocalNormalization

noncomputable section

private theorem natSix_ne_zero : (6 : ℕ) ≠ 0 := by decide

private theorem natSix_not_unit : ¬ IsUnit (6 : ℕ) := by
  rw [Nat.isUnit_iff]
  decide

private theorem natSix_not_prime : ¬ Nat.Prime 6 := by decide

private theorem natSix_normalizedFactors :
    normalizedFactors (6 : ℕ) = (([2, 3] : List ℕ) : Multiset ℕ) := by
  have hprod : ((([2, 3] : List ℕ) : Multiset ℕ).prod) = 6 := by rfl
  rw [← hprod]
  apply Nat.factors_multiset_prod_of_irreducible
  intro p hp
  simp only [Multiset.mem_coe, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact Nat.irreducible_iff_prime.mpr Nat.prime_two.prime
  · exact Nat.irreducible_iff_prime.mpr Nat.prime_three.prime

/-- The minimal primes over the natural-number ideal `(6)` are `(2)` and `(3)`. -/
public theorem Ideal.minimalPrimes_span_nat_six :
    (Ideal.span {(6 : ℕ)}).minimalPrimes =
      {Ideal.span {(2 : ℕ)}, Ideal.span {(3 : ℕ)}} := by
  rw [Ideal.minimalPrimes_span_singleton_eq_normalizedFactors natSix_ne_zero,
    natSix_normalizedFactors]
  ext P
  simp [or_and_right, exists_or]

private theorem natSix_two_mem :
    Ideal.span {(2 : ℕ)} ∈ (Ideal.span {(6 : ℕ)}).minimalPrimes := by
  rw [Ideal.minimalPrimes_span_nat_six]
  simp

private theorem natSix_three_mem :
    Ideal.span {(3 : ℕ)} ∈ (Ideal.span {(6 : ℕ)}).minimalPrimes := by
  rw [Ideal.minimalPrimes_span_nat_six]
  simp

private theorem natSix_distinct : Ideal.span {(2 : ℕ)} ≠ Ideal.span {(3 : ℕ)} := by
  intro h
  have hthree : (3 : ℕ) ∈ Ideal.span {(2 : ℕ)} := by
    rw [h]
    exact Ideal.mem_span_singleton_self _
  exact (by decide : ¬ (2 : ℕ) ∣ 3) (Ideal.mem_span_singleton.mp hthree)

private theorem natSix_proper_primes :
    (Ideal.span {(2 : ℕ)}).IsPrime ∧ (Ideal.span {(3 : ℕ)}).IsPrime ∧
      Ideal.span {(2 : ℕ)} ≠ ⊤ ∧ Ideal.span {(3 : ℕ)} ≠ ⊤ := by
  exact ⟨natSix_two_mem.isPrime, natSix_three_mem.isPrime,
    natSix_two_mem.isPrime.ne_top, natSix_three_mem.isPrime.ne_top⟩

private theorem natSix_two_factor : (2 : ℕ) ∈ normalizedFactors (6 : ℕ) := by
  rw [natSix_normalizedFactors]
  simp

private theorem natSix_forward_two :
    (Ideal.normalizedFactorsEquivMinimalPrimes natSix_ne_zero
      ⟨2, natSix_two_factor⟩).1 = Ideal.span {(2 : ℕ)} :=
  Ideal.normalizedFactorsEquivMinimalPrimes_apply natSix_ne_zero ⟨2, natSix_two_factor⟩

private theorem natSix_three_factor : (3 : ℕ) ∈ normalizedFactors (6 : ℕ) := by
  rw [natSix_normalizedFactors]
  simp

private theorem natSix_components_distinct :
    Ideal.normalizedFactorsEquivIrreducibleComponents natSix_ne_zero
        ⟨2, natSix_two_factor⟩ ≠
      Ideal.normalizedFactorsEquivIrreducibleComponents natSix_ne_zero
        ⟨3, natSix_three_factor⟩ := by
  intro h
  have hvalues : (2 : ℕ) = 3 :=
    congrArg Subtype.val
      ((Ideal.normalizedFactorsEquivIrreducibleComponents natSix_ne_zero).injective h)
  exact (by decide : (2 : ℕ) ≠ 3) hvalues
