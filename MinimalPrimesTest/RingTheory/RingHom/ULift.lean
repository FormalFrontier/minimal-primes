/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MinimalPrimes.RingTheory.RingHom.ULift

/-!
# Examples of finite-type universe lifting

The polynomial coefficient map gives a finite-type scalar map with a nontrivial target.
The identity map gives the boundary case, with independent source and target lift levels.
-/

@[expose] public section

universe u w z

/-- The canonical coefficient map into integer polynomials remains finite type after lifting. -/
example :
    (RingHom.ulift.{w, z} (algebraMap ℤ (Polynomial ℤ))).FiniteType := by
  have h : (algebraMap ℤ (Polynomial ℤ)).FiniteType :=
    RingHom.finiteType_algebraMap.mpr
      (inferInstance : Algebra.FiniteType ℤ (Polynomial ℤ))
  exact h.ulift

/-- Lifting an identity scalar map preserves finite type, even at different lift levels. -/
example (R : Type u) [CommRing R] :
    (RingHom.ulift.{w, z} (RingHom.id R)).FiniteType :=
  (RingHom.finiteType_ulift_iff _).mpr (RingHom.FiniteType.id R)
