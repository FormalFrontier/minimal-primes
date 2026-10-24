/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MinimalPrimes.PrincipalExamples.Algebra
public import MinimalPrimes.IrreducibleComponents
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Tactic.NormNum

/-!
# Factors, minimal primes, and components over the integers

Twelve has three normalized factors counted with multiplicity, but two minimal
primes and two irreducible components of its principal zero-locus subspace.
Zero and one have the same empty factor multiset and different minimal-prime
sets; the unit zero locus has no irreducible components.

## References

The proofs use Mathlib's normalized-factor and minimal-prime APIs and the
factor-to-component equivalence in `MinimalPrimes.IrreducibleComponents`.
-/

noncomputable section

open UniqueFactorizationMonoid TopologicalSpace

universe u

namespace MinimalPrimes.PrincipalExamples

section GenericNormalization

variable {R : Type u} [CommRing R] [UniqueFactorizationMonoid R]
  [NormalizationMonoid R]

private theorem unit_boundary {u : R} (hu : IsUnit u) :
    (Ideal.span {u}).minimalPrimes = ∅ ∧ normalizedFactors u = 0 := by
  exact ⟨by rw [Ideal.span_singleton_eq_top.mpr hu, Ideal.minimalPrimes_top],
    UniqueFactorizationMonoid.normalizedFactors_of_isUnit hu⟩

private theorem repeated_factor_boundary {p : R} (hp : Irreducible p) (n : ℕ) :
    normalizedFactors (p ^ n) = Multiset.replicate n (normalize p) :=
  hp.normalizedFactors_pow n

private theorem zero_boundary [IsDomain R] :
    (Ideal.span ({0} : Set R)).minimalPrimes = {⊥} ∧
      normalizedFactors (0 : R) = 0 := by
  exact ⟨by simpa using (IsDomain.minimalPrimes_eq_singleton_bot (R := R)),
    UniqueFactorizationMonoid.normalizedFactors_zero⟩

end GenericNormalization

/-- The zero locus of `(12)` has exactly two irreducible components, indexed by
the two distinct normalized factor values. The algebraic prefix records the
repeated factor and the two distinct minimal primes. The component target is
the full order-dual component subtype of the zero-locus subspace. -/
public theorem integer_twelve_factor_geometry (h12 : (12 : ℤ) ≠ 0) :
    normalizedFactors (12 : ℤ) =
      Multiset.cons 2 (Multiset.cons 2 (Multiset.cons 3 0)) ∧
    (Ideal.span {(12 : ℤ)}).minimalPrimes =
      {Ideal.span {(2 : ℤ)}, Ideal.span {(3 : ℤ)}} ∧
    (Ideal.span {(2 : ℤ)} : Ideal ℤ) ≠ Ideal.span {(3 : ℤ)} ∧
    ∃ (h2 : (2 : ℤ) ∈ normalizedFactors (12 : ℤ))
      (h3 : (3 : ℤ) ∈ normalizedFactors (12 : ℤ)),
      Ideal.normalizedFactorsEquivIrreducibleComponents h12 ⟨2, h2⟩ ≠
        Ideal.normalizedFactorsEquivIrreducibleComponents h12 ⟨3, h3⟩ ∧
      ∀ Z : (irreducibleComponents
        (PrimeSpectrum.zeroLocus (Ideal.span {(12 : ℤ)} : Set ℤ)))ᵒᵈ,
        Z = Ideal.normalizedFactorsEquivIrreducibleComponents h12 ⟨2, h2⟩ ∨
        Z = Ideal.normalizedFactorsEquivIrreducibleComponents h12 ⟨3, h3⟩ := by
  obtain ⟨hF, hM, hD, h2old, h3, hE2, hE3⟩ :=
    MinimalPrimes.PrincipalExamples.integer_twelve_factor_algebra h12
  have hp2 : Prime (2 : ℤ) := Int.prime_two
  have hpow := repeated_factor_boundary hp2.irreducible 2
  have h2pow : (2 : ℤ) ∈ normalizedFactors ((2 : ℤ) ^ 2) := by
    rw [hpow, Int.normalize_of_nonneg (by norm_num : 0 ≤ (2 : ℤ))]
    simp
  have hmul := normalizedFactors_mul
    (by norm_num : (2 : ℤ) ^ 2 ≠ 0) (by norm_num : (3 : ℤ) ≠ 0)
  rw [show (2 : ℤ) ^ 2 * 3 = 12 by norm_num] at hmul
  have h2 : (2 : ℤ) ∈ normalizedFactors (12 : ℤ) := by
    rw [hmul]
    exact Multiset.mem_add.mpr (Or.inl h2pow)
  have hne : (⟨2, h2old⟩ : {p : ℤ // p ∈ normalizedFactors (12 : ℤ)}) ≠
      ⟨3, h3⟩ := by
    intro h
    apply hD
    calc
      Ideal.span {(2 : ℤ)} =
          (Ideal.normalizedFactorsEquivMinimalPrimes h12 ⟨2, h2old⟩).1 := hE2.symm
      _ = (Ideal.normalizedFactorsEquivMinimalPrimes h12 ⟨3, h3⟩).1 :=
        congrArg (fun p ↦ (Ideal.normalizedFactorsEquivMinimalPrimes h12 p).1) h
      _ = Ideal.span {(3 : ℤ)} := hE3
  refine ⟨hF, hM, hD, h2, h3, ?_, ?_⟩
  · intro h
    exact hne ((Ideal.normalizedFactorsEquivIrreducibleComponents h12).injective h)
  · intro Z
    obtain ⟨p, hpZ⟩ :=
      (Ideal.normalizedFactorsEquivIrreducibleComponents h12).surjective Z
    have hp : p.1 = 2 ∨ p.1 = 3 := by simpa [hF, or_assoc] using p.2
    rcases hp with hp | hp
    · left
      calc
        Z = Ideal.normalizedFactorsEquivIrreducibleComponents h12 p := hpZ.symm
        _ = Ideal.normalizedFactorsEquivIrreducibleComponents h12 ⟨2, h2⟩ :=
          congrArg (Ideal.normalizedFactorsEquivIrreducibleComponents h12)
            (Subtype.ext hp)
    · right
      calc
        Z = Ideal.normalizedFactorsEquivIrreducibleComponents h12 p := hpZ.symm
        _ = Ideal.normalizedFactorsEquivIrreducibleComponents h12 ⟨3, h3⟩ :=
          congrArg (Ideal.normalizedFactorsEquivIrreducibleComponents h12)
            (Subtype.ext hp)

/-- Zero has one minimal prime and one has none, although both normalized
factor multisets are empty. The full component target for the unit zero locus
is empty; zero is never an input to the nonzero factor equivalence. -/
public theorem integer_zero_unit_boundary :
    (Ideal.span {(0 : ℤ)}).minimalPrimes = {⊥} ∧
    normalizedFactors (0 : ℤ) = 0 ∧
    (Ideal.span {(1 : ℤ)}).minimalPrimes = ∅ ∧
    normalizedFactors (1 : ℤ) = 0 ∧
    IsEmpty ((irreducibleComponents
      (PrimeSpectrum.zeroLocus (Ideal.span {(1 : ℤ)} : Set ℤ)))ᵒᵈ) := by
  obtain ⟨hZ, hFZ⟩ := zero_boundary (R := ℤ)
  obtain ⟨hU, hFU⟩ := unit_boundary (u := (1 : ℤ)) isUnit_one
  refine ⟨hZ, hFZ, hU, hFU, ⟨?_⟩⟩
  intro Z
  have hmem := ((Ideal.normalizedFactorsEquivIrreducibleComponents
    (f := (1 : ℤ)) (by norm_num)).symm Z).2
  simp [hFU] at hmem

end MinimalPrimes.PrincipalExamples
