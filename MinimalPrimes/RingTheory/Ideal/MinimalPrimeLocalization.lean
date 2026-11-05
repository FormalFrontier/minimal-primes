/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Localization.Away.AdjoinRoot
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.RingHom.Finite
public import MinimalPrimes.RingTheory.IntegralNilpotent

/-!
# Minimal primes, localized radicals and finite algebras

For an arbitrary ideal `I` of a commutative semiring, localization at a prime ideal `q`
identifies the radical of the extended ideal with the extension of `q` exactly when `q`
is minimal over `I`. No containment hypothesis is required: the equality itself forces
`I ≤ q` through the prime-ideal correspondence for localization.

An element belongs to `I.radical` if and only if its image belongs to the radical of
the extension of `I` in the canonical localization at every minimal prime over `I`.
This membership criterion includes the unit ideal, whose family of minimal primes is empty.

A finite-type algebra with module-finite residue-field fibre at a minimal prime
becomes finite after inverting an element outside that prime. This includes
nonreduced bases and zero algebras. The proof lifts monic relations through a
nil ideal in the prime localization, then clears denominators for finitely many
algebra generators; no finite generation or uniform nilpotence of the nil ideal
is required.

## References

This module uses Mathlib's `IsLocalization.minimalPrimes_map`,
`Ideal.radical_minimalPrimes`, and the prime-ideal correspondence for localization at a
prime. The implication from minimality is Mathlib's
`IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes`, formalized by Andrew Yang.
The global membership criterion combines this with Mathlib's `Ideal.sInf_minimalPrimes`
and `Ideal.under_map_of_isLocalizationAtPrime`.

The finite-localization theorem also uses Mathlib's `Ideal.Fiber.algEquivQuotient`,
`IsIntegral.exists_multiple_integral_of_isLocalization`, and
`IsLocalization.exists_isIntegral_smul_of_isIntegral_map`.
-/

@[expose] public section

universe u v

namespace IsLocalization.AtPrime

variable {R : Type u} {A : Type v} [CommSemiring R] [CommSemiring A] [Algebra R A]

/-- If the radical of an extended ideal in the localization at `q` equals the extension
of `q`, then `q` is minimal over the original ideal. In particular, the equality forces
containment in `q`. This uses Mathlib's minimal-prime and prime-ideal correspondences. -/
theorem mem_minimalPrimes_of_radical_map_eq
    (q : Ideal R) [q.IsPrime] [IsLocalization.AtPrime A q] (I : Ideal R)
    (h : (I.map (algebraMap R A)).radical = q.map (algebraMap R A)) :
    q ∈ I.minimalPrimes := by
  have : (q.map (algebraMap R A)).IsPrime :=
    Ideal.isPrime_map_of_isLocalizationAtPrime (S := A) q le_rfl
  have hmin : q.map (algebraMap R A) ∈ (I.map (algebraMap R A)).minimalPrimes := by
    rw [← Ideal.radical_minimalPrimes, h, Ideal.minimalPrimes_eq_subsingleton_self]
    exact Set.mem_singleton _
  simpa only [IsLocalization.minimalPrimes_map q.primeCompl A I, Set.mem_preimage,
    Ideal.under_map_of_isLocalizationAtPrime (S := A) q le_rfl] using hmin

/-- The radical of an extended ideal in the localization at `q` equals the extension
of `q` if and only if `q` is minimal over that ideal. The forward implication needs no
separate containment hypothesis; the reverse implication is Mathlib's
`IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes`. -/
theorem radical_map_eq_iff_mem_minimalPrimes
    (q : Ideal R) [q.IsPrime] [IsLocalization.AtPrime A q] (I : Ideal R) :
    (I.map (algebraMap R A)).radical = q.map (algebraMap R A) ↔ q ∈ I.minimalPrimes :=
  ⟨mem_minimalPrimes_of_radical_map_eq q I, radical_map_of_mem_minimalPrimes A q I⟩

end IsLocalization.AtPrime

namespace Ideal

/-- An element belongs to the radical of an ideal exactly when its image belongs to the
radical of the extended ideal at every minimal prime over that ideal. This includes the
unit ideal and uses Mathlib's intersection of minimal primes and prime contraction under
localization. -/
theorem mem_radical_iff_forall_minimalPrimes_localization
    {R : Type u} [CommSemiring R] (I : Ideal R) (x : R) :
    x ∈ I.radical ↔
      ∀ (q : Ideal R) [q.IsPrime], q ∈ I.minimalPrimes →
        algebraMap R (Localization.AtPrime q) x ∈
          (Ideal.map (algebraMap R (Localization.AtPrime q)) I).radical := by
  constructor
  · intro hx q _ _
    exact Ideal.map_radical_le _ (Ideal.mem_map_of_mem _ hx)
  · intro h
    rw [← Ideal.sInf_minimalPrimes, Ideal.mem_sInf]
    intro q hq
    let : q.IsPrime := hq.isPrime
    have hx := h q hq
    rw [IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes
      (Localization.AtPrime q) q I hq] at hx
    have hx' : x ∈ (q.map (algebraMap R (Localization.AtPrime q))).under R := hx
    simpa only [Ideal.under_map_of_isLocalizationAtPrime q le_rfl] using hx'

end Ideal

private lemma exists_finite_awayMap_of_integral_multiples
    {R : Type u} {B : Type v} [CommRing R] [CommRing B] [Algebra R B]
    [Algebra.FiniteType R B] (M : Submonoid R)
    (h : ∀ x : B, ∃ m : M, IsIntegral R ((m : R) • x)) :
    ∃ r ∈ M, (Localization.awayMap (algebraMap R B) r).Finite := by
  classical
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := R) (A := B)
  choose m hm using h
  let r := ∏ x ∈ s, (m x : R)
  have hr : r ∈ M := M.prod_mem fun x _ ↦ (m x).property
  let Rr := Localization.Away r
  let Br := Localization.Away (algebraMap R B r)
  let : Algebra Rr Br := (Localization.awayMap (algebraMap R B) r).toAlgebra
  have : IsScalarTower R Rr Br := IsScalarTower.of_algebraMap_eq'
    (IsLocalization.map_comp (Submonoid.powers r).le_comap_map).symm
  have hgen (x : B) (hx : x ∈ s) : IsIntegral Rr (algebraMap B Br x) := by
    obtain ⟨u, hu⟩ := isUnit_iff_exists_inv.mp
      (IsLocalization.Away.isUnit_of_dvd (S := Rr) r
        (Finset.dvd_prod_of_mem (fun x ↦ (m x : R)) hx))
    have hi : IsIntegral Rr (algebraMap B Br ((m x : R) • x)) :=
      ((hm x).algebraMap (B := Br)).tower_top
    have heq : algebraMap Rr Br u * algebraMap B Br ((m x : R) • x) =
        algebraMap B Br x := by
      rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply R B Br,
        IsScalarTower.algebraMap_apply R Rr Br,
        ← mul_assoc, ← map_mul, mul_comm u, hu, map_one, one_mul]
    rw [← heq]
    exact isIntegral_algebraMap.mul hi
  have hall (x : B) : IsIntegral Rr (algebraMap B Br x) := by
    have hin : x ∈ Algebra.adjoin R (s : Set B) := hs ▸ trivial
    induction hin using Algebra.adjoin_induction with
    | mem x hx => exact hgen x hx
    | algebraMap a =>
        rw [← IsScalarTower.algebraMap_apply R B Br,
          IsScalarTower.algebraMap_apply R Rr Br]
        exact isIntegral_algebraMap
    | add x y _ _ hx hy => simpa only [map_add] using hx.add hy
    | mul x y _ _ hx hy => simpa only [map_mul] using hx.mul hy
  have : Algebra.IsIntegral Rr Br := by
    constructor
    intro z
    obtain ⟨⟨b, t⟩, hz⟩ := IsLocalization.surj (Submonoid.powers (algebraMap R B r)) z
    obtain ⟨n, hn⟩ := t.property
    obtain ⟨u, hu⟩ := isUnit_iff_exists_inv.mp
      ((IsLocalization.Away.algebraMap_isUnit (S := Rr) r).pow n)
    have heq : z = algebraMap B Br b * algebraMap Rr Br u := by
      have he : algebraMap B Br (t : B) * algebraMap Rr Br u = 1 := by
        rw [← hn, map_pow, ← IsScalarTower.algebraMap_apply R B Br,
          IsScalarTower.algebraMap_apply R Rr Br, ← map_pow, ← map_mul, hu, map_one]
      calc z = z * (algebraMap B Br (t : B) * algebraMap Rr Br u) := by rw [he, mul_one]
           _ = algebraMap B Br b * algebraMap Rr Br u := by
             rw [← mul_assoc, hz]
    rw [heq]
    exact (hall b).mul isIntegral_algebraMap
  have : Algebra.FiniteType Rr Br := .of_restrictScalars_finiteType R _ _
  exact ⟨r, hr, Algebra.IsIntegral.finite⟩

private lemma isIntegral_atPrime_of_finite_fiber
    {R : Type u} {B : Type v} [CommRing R] [CommRing B] [Algebra R B]
    (p : PrimeSpectrum R) (hp : p.asIdeal ∈ minimalPrimes R)
    [Module.Finite p.asIdeal.ResidueField (p.asIdeal.Fiber B)] (x : B) :
    IsIntegral (Localization.AtPrime p.asIdeal)
      (algebraMap B (Localization (Algebra.algebraMapSubmonoid B p.asIdeal.primeCompl)) x) := by
  let Rp := Localization.AtPrime p.asIdeal
  let Bp := Localization (Algebra.algebraMapSubmonoid B p.asIdeal.primeCompl)
  let I := (IsLocalRing.maximalIdeal Rp).map (algebraMap Rp Bp)
  have hnil : IsLocalRing.maximalIdeal Rp = nilradical Rp := by
    simpa only [nilradical, Ideal.zero_eq_bot, Ideal.map_bot,
      IsLocalization.AtPrime.map_eq_maximalIdeal]
      using (IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes
        (A := Rp) p.asIdeal ⊥ hp).symm
  have hI : I ≤ nilradical Bp := by
    dsimp [I]
    rw [hnil]
    simpa only [nilradical, Ideal.zero_eq_bot, Ideal.map_bot] using
      (Ideal.map_radical_le (f := algebraMap Rp Bp) (I := ⊥))
  let : Algebra B (p.asIdeal.Fiber B) := Algebra.TensorProduct.rightAlgebra
  let e : p.asIdeal.Fiber B ≃ₐ[Rp] Bp ⧸ I :=
    ((Ideal.Fiber.algEquivQuotient p.asIdeal).restrictScalars R).extendScalarsOfIsLocalization
      Rp p.asIdeal.primeCompl
  have : Module.Finite Rp (p.asIdeal.Fiber B) :=
    Module.Finite.trans p.asIdeal.ResidueField _
  have : Module.Finite Rp (Bp ⧸ I) := Module.Finite.equiv e.toLinearEquiv
  exact IsIntegral.of_quotient_of_le_nilradical I hI (.of_finite Rp _)

/-- A finite-type algebra with module-finite residue-field fibre at a minimal
prime becomes finite after localizing the base away from an element outside
that prime. No domain or Noetherian hypothesis is required. -/
theorem Algebra.FiniteType.exists_finite_awayMap_of_mem_minimalPrimes
    {R : Type u} {B : Type v} [CommRing R] [CommRing B] [Algebra R B]
    [Algebra.FiniteType R B] (p : PrimeSpectrum R)
    (hp : p.asIdeal ∈ minimalPrimes R)
    [Module.Finite p.asIdeal.ResidueField (p.asIdeal.Fiber B)] :
    ∃ r : R, r ∉ p.asIdeal ∧ (Localization.awayMap (algebraMap R B) r).Finite := by
  let M := p.asIdeal.primeCompl
  let Bp := Localization (Algebra.algebraMapSubmonoid B M)
  have h (x : B) : ∃ m : M, IsIntegral R ((m : R) • x) := by
    have hx := isIntegral_atPrime_of_finite_fiber p hp x
    obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization M
      (algebraMap B Bp x) hx
    have hm' : IsIntegral R (algebraMap B Bp ((m : R) • x)) := by
      simpa only [Submonoid.smul_def, Algebra.smul_def, map_mul,
        ← IsScalarTower.algebraMap_apply R B Bp] using hm
    obtain ⟨n, hn, hnx⟩ := IsLocalization.exists_isIntegral_smul_of_isIntegral_map M hm'
    exact ⟨⟨n, hn⟩ * m, by simpa only [Submonoid.coe_mul, Subtype.coe_mk, mul_smul] using hnx⟩
  obtain ⟨r, hr, hfin⟩ := exists_finite_awayMap_of_integral_multiples M h
  exact ⟨r, hr, hfin⟩
