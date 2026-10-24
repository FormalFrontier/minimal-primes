/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Spectral.Prespectral
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.Separation.Profinite

/-!
# Zero-dimensional prime spectra

For a commutative semiring of Krull dimension at most zero, the Zariski basic
opens are clopen and the prime spectrum is Hausdorff. Mathlib then supplies total
separation and total disconnectedness from its prespectral structure.
For a reduced nontrivial commutative ring, preconnectedness of this spectrum
therefore implies `IsField` for the original ring.

The T₁ and Hausdorff conditions are each equivalent to this dimension bound.

## Implementation notes

The topological statements need neither reducedness nor nontriviality and include
the empty spectrum.
The field criterion concludes a proposition, not a choice of a field structure.

## References

The topological argument uses Mathlib's closed-point/maximal-ideal criterion,
its description of a basic open as an away-localization image, and
`PrimeSpectrum.isClosed_range_of_stableUnderSpecialization`, which Mathlib
attributes to the Stacks Project, Tag 00HY. Clopen basic opens separate points
by Mathlib's Zariski basis theorem. The field criterion combines Mathlib's
`subsingleton_of_preconnected_totallyDisconnected` with Andrew Yang's
`PrimeSpectrum.subsingleton_iff_isField_of_isReduced`.

The separation characterizations factor the closed-singleton/maximal-ideal
argument in Mathlib's `PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero`
through `Ring.krullDimLE_zero_iff`, reusing the Hausdorff result above.
-/

@[expose] public section

universe u

namespace PrimeSpectrum

/-- Every Zariski basic open of a commutative semiring of Krull dimension at most
zero is clopen. The proof uses Mathlib's localization-image description and its
specialization-stable range theorem (Stacks Project, Tag 00HY). -/
theorem isClopen_basicOpen_of_krullDimLE_zero {R : Type u} [CommSemiring R]
    [Ring.KrullDimLE 0 R] (a : R) :
    IsClopen (basicOpen a : Set (PrimeSpectrum R)) := by
  have : T1Space (PrimeSpectrum R) := ⟨fun x ↦
    (isClosed_singleton_iff_isMaximal x).mpr (Ideal.isMaximal_of_isPrime x.asIdeal)⟩
  refine ⟨?_, isOpen_basicOpen⟩
  rw [← localization_away_comap_range (Localization (Submonoid.powers a)) a]
  refine isClosed_range_of_stableUnderSpecialization _ ?_
  intro x y hxy hx
  exact hxy.eq ▸ hx

/-- The Zariski prime spectrum of a commutative semiring of Krull dimension at
most zero is Hausdorff. Its clopen basic-open basis separates distinct points. -/
instance t2Space_of_krullDimLE_zero (R : Type u) [CommSemiring R]
    [Ring.KrullDimLE 0 R] : T2Space (PrimeSpectrum R) := by
  have hclopen : TopologicalSpace.IsTopologicalBasis
      {s : Set (PrimeSpectrum R) | IsClopen s} :=
    (isTopologicalBasis_basic_opens (R := R)).of_isOpen_of_subset
      (fun _ hs => hs.isOpen) (by
        rintro _ ⟨a, rfl⟩
        exact isClopen_basicOpen_of_krullDimLE_zero a)
  exact @TotallySeparatedSpace.t2Space (PrimeSpectrum R) _
    (totallySeparatedSpace_of_t0_of_basis_clopen hclopen)

/-- The Zariski prime spectrum of a commutative semiring is T₁ exactly when its
Krull dimension is at most zero, including the empty spectrum. This factors the
closed-point argument of Mathlib's discrete-spectrum criterion through its
closed-singleton/maximal-ideal and dimension-zero criteria. -/
theorem t1Space_iff_krullDimLE_zero {R : Type u} [CommSemiring R] :
    T1Space (PrimeSpectrum R) ↔ Ring.KrullDimLE 0 R := by
  constructor
  · intro h
    let : T1Space (PrimeSpectrum R) := h
    apply Ring.krullDimLE_zero_iff.mpr
    intro I hI
    exact (isClosed_singleton_iff_isMaximal ⟨I, hI⟩).mp isClosed_singleton
  · intro h
    let : Ring.KrullDimLE 0 R := h
    let : T2Space (PrimeSpectrum R) := t2Space_of_krullDimLE_zero R
    infer_instance

/-- The Zariski prime spectrum of a commutative semiring is Hausdorff exactly
when its Krull dimension is at most zero, including the empty spectrum. This
combines the T₁ characterization with `t2Space_of_krullDimLE_zero`. -/
theorem t2Space_iff_krullDimLE_zero {R : Type u} [CommSemiring R] :
    T2Space (PrimeSpectrum R) ↔ Ring.KrullDimLE 0 R := by
  constructor
  · intro h
    let : T2Space (PrimeSpectrum R) := h
    exact t1Space_iff_krullDimLE_zero.mp inferInstance
  · intro h
    let : Ring.KrullDimLE 0 R := h
    exact t2Space_of_krullDimLE_zero R

/-- A reduced nontrivial commutative ring of Krull dimension at most zero with
preconnected Zariski prime spectrum is a field in the sense of `IsField`.
This combines Mathlib's preconnected/totally-disconnected subsingleton theorem
with its reduced-ring singleton-spectrum field criterion. -/
theorem isField_of_isReduced_of_preconnectedSpace (R : Type u) [CommRing R]
    [IsReduced R] [Nontrivial R] [Ring.KrullDimLE 0 R]
    [PreconnectedSpace (PrimeSpectrum R)] : IsField R := by
  have : T2Space (PrimeSpectrum R) := t2Space_of_krullDimLE_zero R
  exact (subsingleton_iff_isField_of_isReduced (R := R)).mp
    (subsingleton_of_preconnected_totallyDisconnected (α := PrimeSpectrum R))

end PrimeSpectrum
