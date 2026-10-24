/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MinimalPrimes.RingTheory.Spectrum.Prime.ZeroDimensional
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.Topology.Connected.Clopen

/-!
# Fields, two-point product spectra, and nilpotent boundaries

An arbitrary given field `K` supplies the hypotheses of the field criterion.
The product ring `K × K` supplies a different use of the topology statements:
its two projection kernels are distinct prime-spectrum points, and `D((1, 0))`
contains the first but not the second. Mathlib's Artinian product instances
supply its dimension bound independently of the spectrum statements.

The product's failure of preconnectedness is proved separately using Mathlib's
clopen theorem for complementary idempotents, not the field criterion.
The zero ring has empty preconnected spectrum but is not a field. In `ZMod 4`,
the nonzero nilpotent `2` shows why reducedness matters at the field endpoint.
All rings and points here use their usual product and quotient structures.

## References

These examples use Mathlib's field singleton-spectrum, Artinian product,
projection-kernel, complementary-idempotent and finite quotient APIs.
-/

@[expose] public section

universe u

namespace ZeroDimensionalSpectrumExamples

-- The finite-and-T₁ factor is precisely Mathlib's original discrete criterion.
-- Finite T₁ spaces are discrete; compact discrete spectra are finite.
private theorem discrete_comparison {R : Type u} [CommSemiring R] :
    DiscreteTopology (PrimeSpectrum R) ↔
      Finite (PrimeSpectrum R) ∧ T1Space (PrimeSpectrum R) := by
  rw [PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero,
    PrimeSpectrum.t1Space_iff_krullDimLE_zero]

-- Compare with both the original domain criterion and its algebraic endpoint.
private theorem domain_comparison {R : Type u} [CommSemiring R] [IsDomain R] :
    Ring.KrullDimLE 0 R ↔ IsField R := by
  constructor
  · intro h
    let : Ring.KrullDimLE 0 R := h
    exact Ring.KrullDimLE.isField_of_isDomain
  · intro h
    exact PrimeSpectrum.t1Space_iff_krullDimLE_zero.mp
      (PrimeSpectrum.t1Space_iff_isField.mpr h)

variable (K : Type u) [Field K]

private theorem field_criterion : IsField K := by
  let : Ring.KrullDimLE 0 K := inferInstance
  let : PreconnectedSpace (PrimeSpectrum K) :=
    ⟨Set.subsingleton_univ.isPreconnected⟩
  exact PrimeSpectrum.isField_of_isReduced_of_preconnectedSpace K

private theorem field_separation :
    T1Space (PrimeSpectrum K) ∧ T2Space (PrimeSpectrum K) := by
  have hdim : Ring.KrullDimLE 0 K :=
    PrimeSpectrum.t1Space_iff_krullDimLE_zero.mp
      (PrimeSpectrum.t1Space_iff_isField.mpr (field_criterion K))
  exact ⟨PrimeSpectrum.t1Space_iff_krullDimLE_zero.mpr hdim,
    PrimeSpectrum.t2Space_iff_krullDimLE_zero.mpr hdim⟩

private def firstPrime : PrimeSpectrum (K × K) :=
  ⟨RingHom.ker (RingHom.fst K K), RingHom.ker_isPrime (RingHom.fst K K)⟩

private def secondPrime : PrimeSpectrum (K × K) :=
  ⟨RingHom.ker (RingHom.snd K K), RingHom.ker_isPrime (RingHom.snd K K)⟩

private theorem firstPrime_mem :
    firstPrime K ∈ PrimeSpectrum.basicOpen ((1, 0) : K × K) := by
  change (1 : K) ≠ 0
  exact one_ne_zero

private theorem secondPrime_notMem :
    secondPrime K ∉ PrimeSpectrum.basicOpen ((1, 0) : K × K) := by
  change ¬ ¬ (0 : K) = 0
  exact fun h ↦ h rfl

private theorem projection_primes_ne : firstPrime K ≠ secondPrime K := by
  intro h
  exact secondPrime_notMem K (h ▸ firstPrime_mem K)

private theorem product_dimension : Ring.KrullDimLE 0 (K × K) := by
  let : IsArtinianRing (K × K) := inferInstance
  infer_instance

private theorem product_clopen_separates :
    IsClopen (PrimeSpectrum.basicOpen ((1, 0) : K × K) : Set (PrimeSpectrum (K × K))) ∧
      firstPrime K ∈ PrimeSpectrum.basicOpen ((1, 0) : K × K) ∧
      secondPrime K ∉ PrimeSpectrum.basicOpen ((1, 0) : K × K) := by
  let : Ring.KrullDimLE 0 (K × K) := product_dimension K
  exact ⟨PrimeSpectrum.isClopen_basicOpen_of_krullDimLE_zero _,
    firstPrime_mem K, secondPrime_notMem K⟩

private theorem product_hausdorff : T2Space (PrimeSpectrum (K × K)) := by
  let : Ring.KrullDimLE 0 (K × K) := product_dimension K
  exact PrimeSpectrum.t2Space_of_krullDimLE_zero (K × K)

private theorem product_dimension_from_separation :
    Ring.KrullDimLE 0 (K × K) ∧ T1Space (PrimeSpectrum (K × K)) :=
  ⟨PrimeSpectrum.t2Space_iff_krullDimLE_zero.mp (product_hausdorff K),
    PrimeSpectrum.t1Space_iff_krullDimLE_zero.mpr (product_dimension K)⟩

private theorem split_clopen :
    IsClopen (PrimeSpectrum.basicOpen ((1, 0) : K × K) : Set (PrimeSpectrum (K × K))) :=
  PrimeSpectrum.isClopen_basicOpen_of_mul_add ((1, 0) : K × K) ((0, 1) : K × K)
    (by ext <;> simp) (by ext <;> simp)

private theorem product_not_preconnected : ¬ PreconnectedSpace (PrimeSpectrum (K × K)) := by
  intro h
  let : PreconnectedSpace (PrimeSpectrum (K × K)) := h
  have hwhole := (split_clopen K).eq_univ ⟨firstPrime K, firstPrime_mem K⟩
  apply secondPrime_notMem K
  change secondPrime K ∈
    (PrimeSpectrum.basicOpen ((1, 0) : K × K) : Set (PrimeSpectrum (K × K)))
  rw [hwhole]
  trivial

private theorem product_not_field : ¬ IsField (K × K) := by
  intro h
  have he : ((1, 0) : K × K) ≠ 0 := by
    intro he
    exact one_ne_zero (congrArg Prod.fst he)
  obtain ⟨b, hb⟩ := h.mul_inv_cancel he
  apply (zero_ne_one : (0 : K) ≠ 1)
  simpa using congrArg Prod.snd hb

/-- A product of two fields is reduced and zero-dimensional, but is not a field and has
disconnected spectrum. -/
public theorem field_prod_zero_dimensional :
    IsReduced (K × K) ∧ Nontrivial (K × K) ∧ Ring.KrullDimLE 0 (K × K) ∧
      ¬ PreconnectedSpace (PrimeSpectrum (K × K)) ∧ ¬ IsField (K × K) :=
  ⟨inferInstance, inferInstance, product_dimension K,
    product_not_preconnected K, product_not_field K⟩

/-- The zero ring is reduced and zero-dimensional, with empty spectrum, but is not a field. -/
public theorem zmod_one_zero_dimensional :
    IsReduced (ZMod 1) ∧ Ring.KrullDimLE 0 (ZMod 1) ∧
      IsEmpty (PrimeSpectrum (ZMod 1)) ∧ PreconnectedSpace (PrimeSpectrum (ZMod 1)) ∧
      ¬ IsField (ZMod 1) :=
  ⟨inferInstance, inferInstance, inferInstance,
    ⟨Set.subsingleton_univ.isPreconnected⟩, not_isField_of_subsingleton _⟩

private theorem zeroRing_hausdorff : T2Space (PrimeSpectrum (ZMod 1)) :=
  PrimeSpectrum.t2Space_of_krullDimLE_zero (ZMod 1)

private theorem zeroRing_separation :
    T1Space (PrimeSpectrum (ZMod 1)) ∧ Ring.KrullDimLE 0 (ZMod 1) :=
  ⟨PrimeSpectrum.t1Space_iff_krullDimLE_zero.mpr zmod_one_zero_dimensional.2.1,
    PrimeSpectrum.t2Space_iff_krullDimLE_zero.mp zeroRing_hausdorff⟩

private theorem zmod_four_nonzero_nilpotent :
    (2 : ZMod 4) ≠ 0 ∧ IsNilpotent (2 : ZMod 4) :=
  ⟨by decide, ⟨2, by decide⟩⟩

/-- The ring of integers modulo four is not reduced. -/
public theorem zmod_four_not_isReduced : ¬ IsReduced (ZMod 4) := by
  intro h
  let : IsReduced (ZMod 4) := h
  exact zmod_four_nonzero_nilpotent.1 zmod_four_nonzero_nilpotent.2.eq_zero

end ZeroDimensionalSpectrumExamples
