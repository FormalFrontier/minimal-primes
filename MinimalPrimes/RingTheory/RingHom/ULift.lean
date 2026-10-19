/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Ring.ULift
public import Mathlib.RingTheory.FiniteType

/-!
# Finite-type ring homomorphisms under universe lifting

The canonical universe lift of a ring homomorphism is finite type exactly when the
original homomorphism is finite type. The source ring, target ring and their two
lift levels are independent. The scalar map is the original homomorphism, transported
through the canonical up and down ring equivalences.

The characteristic theorem `RingHom.finiteType_ulift_iff` removes the canonical lifts
from a finite-type proposition. Its forward-lifting form is `RingHom.FiniteType.ulift`.
-/

@[expose] public section

universe u v w z

namespace RingHom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- Canonical universe lifting preserves and reflects finite type, independently in the
source and target lift levels. -/
@[simp] theorem finiteType_ulift_iff (f : R →+* S) :
    (RingHom.ulift.{w, z} f).FiniteType ↔ f.FiniteType := by
  let eR : ULift.{w} R ≃+* R := ULift.ringEquiv
  let eS : ULift.{z} S ≃+* S := ULift.ringEquiv
  let fL : ULift.{w} R →+* ULift.{z} S := RingHom.ulift f
  have hUpR : eR.symm.toRingHom.FiniteType :=
    RingHom.FiniteType.of_surjective _
      (fun y => ⟨eR y, eR.symm_apply_apply y⟩)
  constructor
  · intro hL
    have h : (eS.toRingHom.comp (fL.comp eR.symm.toRingHom)).FiniteType :=
      (hL.comp hUpR).comp_surjective
        (fun y => ⟨eS.symm y, eS.apply_symm_apply y⟩)
    simpa only [eR, eS, fL, RingHom.comp_ulift_eq] using h
  · intro hf
    have h : (eS.toRingHom.comp (fL.comp eR.symm.toRingHom)).FiniteType := by
      simpa only [eR, eS, fL, RingHom.comp_ulift_eq] using hf
    have h' : (eS.toRingHom.comp fL).FiniteType :=
      RingHom.FiniteType.of_comp_finiteType
        (f := eR.symm.toRingHom) (g := eS.toRingHom.comp fL) (by
          simpa only [RingHom.comp_assoc] using h)
    have h'' : (eS.symm.toRingHom.comp (eS.toRingHom.comp fL)).FiniteType :=
      h'.comp_surjective
        (fun y => ⟨eS y, eS.symm_apply_apply y⟩)
    simpa only [← RingHom.comp_assoc,
      RingEquiv.symm_toRingHom_comp_toRingHom, RingHom.id_comp] using h''

/-- A finite-type ring homomorphism remains finite type under canonical universe lifting. -/
theorem FiniteType.ulift {f : R →+* S} (hf : f.FiniteType) :
    (RingHom.ulift.{w, z} f).FiniteType :=
  (finiteType_ulift_iff f).2 hf

end RingHom
