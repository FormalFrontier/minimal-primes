/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Minimal primes in products of commutative semirings

Coordinate evaluation transports minimality over an arbitrary ideal, even for an
infinite product. For a finite product, minimal primes are classified by a unique
coordinate and a minimal prime over its evaluation-image ideal. The coordinates are
exactly those of `Ideal.piOrderIso`.

The equivalence retains coordinate labels, including for repeated isomorphic factors.
No nontriviality of the factors or nonemptiness of the index is required.

## References

* Mathlib's minimal-prime localization theory, formalized by Andrew Yang, supplies
  `IsLocalization.minimalPrimes_map`.
* Mathlib's idempotent-localization criterion realizes evaluation as a localization.
* Mathlib's `Ideal.piOrderIso`, finite-intersection prime criterion, and
  `PrimeSpectrum.sigmaToPi_injective` supply the finite classification and uniqueness.
* The finite-intersection argument follows the Formal Frontier formalization of
  prime spectra of finite products of commutative semirings.
-/

@[expose] public section

universe u v

namespace Ideal

variable {ι : Type u} {R : ι → Type v} [∀ i, CommSemiring (R i)]

/-- Evaluation at a coordinate transports minimal primes over any ideal of a product.
Only the finite classification, not this transport, requires a finite index. -/
theorem comap_eval_mem_minimalPrimes_iff (I : Ideal (∀ i, R i)) (i : ι)
    (q : Ideal (R i)) :
    q.comap (Pi.evalRingHom R i) ∈ I.minimalPrimes ↔
      q ∈ (I.map (Pi.evalRingHom R i)).minimalPrimes := by
  classical
  let := (Pi.evalRingHom R i).toAlgebra
  let e : ∀ j, R j := Pi.single i 1
  have he : IsIdempotentElem e := by
    ext j
    by_cases h : j = i
    · subst j; simp [e]
    · simp [e, h]
  let : IsLocalization.Away e (R i) :=
    IsLocalization.away_of_isIdempotentElem_of_mul he (fun x y ↦ by
      change x i = y i ↔ e * x = e * y
      constructor
      · intro h
        ext j
        by_cases hj : j = i
        · subst j; simpa [e] using h
        · simp [e, hj]
      · intro h
        simpa [e] using congrFun h i) (Function.surjective_eval i)
  change q.comap (algebraMap (∀ j, R j) (R i)) ∈ I.minimalPrimes ↔
    q ∈ (I.map (algebraMap (∀ j, R j) (R i))).minimalPrimes
  rw [IsLocalization.minimalPrimes_map (Submonoid.powers e) (R i)]
  rfl

/-- On an ideal already pulled back from a coordinate, evaluation transport recovers
that coordinate's minimal primes. For commutative rings this is the membership form of
`Ideal.comap_minimalPrimes_eq_of_surjective`, using injectivity of evaluation comap. -/
theorem comap_eval_mem_minimalPrimes_comap_iff (i : ι) (J q : Ideal (R i)) :
    q.comap (Pi.evalRingHom R i) ∈ (J.comap (Pi.evalRingHom R i)).minimalPrimes ↔
      q ∈ J.minimalPrimes := by
  rw [comap_eval_mem_minimalPrimes_iff,
    map_comap_of_surjective _ (Function.surjective_eval i)]

/-- Evaluation comap distinguishes labelled coordinate minimal primes. -/
theorem minimalPrimesPi_comap_injective [Finite ι] (I : Ideal (∀ i, R i)) :
    Function.Injective (fun a : Σ i, ((piOrderIso (R := R)) I i).minimalPrimes ↦
      a.2.val.comap (Pi.evalRingHom R a.1)) := by
  rintro ⟨i, a⟩ ⟨j, b⟩ h
  have hab : (⟨i, ⟨a.val, a.property.isPrime⟩⟩ : Σ i, PrimeSpectrum (R i)) =
      ⟨j, ⟨b.val, b.property.isPrime⟩⟩ :=
    PrimeSpectrum.sigmaToPi_injective R (PrimeSpectrum.ext h)
  have hij : i = j := congrArg Sigma.fst hab
  subst j
  have hab' : (⟨a.val, a.property.isPrime⟩ : PrimeSpectrum (R i)) =
      ⟨b.val, b.property.isPrime⟩ := eq_of_heq (Sigma.mk.inj hab).2
  have hab'' : a = b := Subtype.ext (congrArg PrimeSpectrum.asIdeal hab')
  subst b
  rfl

/-- A minimal prime over an ideal in a finite product has a unique labelled coordinate
minimal prime. Its coordinate ideals are exactly those supplied by `Ideal.piOrderIso`. -/
theorem mem_minimalPrimes_pi_iff [Finite ι] (I P : Ideal (∀ i, R i)) :
    P ∈ I.minimalPrimes ↔
      ∃! a : Σ i, ((piOrderIso (R := R)) I i).minimalPrimes,
        P = a.2.val.comap (Pi.evalRingHom R a.1) := by
  classical
  constructor
  · intro hP
    let := Fintype.ofFinite ι
    let J : ∀ i, Ideal (R i) := piOrderIso P
    have hpi : Ideal.pi J = P := piOrderIso.symm_apply_apply P
    have hinf : Finset.univ.inf (fun i ↦ (J i).comap (Pi.evalRingHom R i)) = P := by
      rw [← hpi]
      ext x
      simp only [Submodule.mem_finsetInf, Finset.mem_univ, forall_const,
        mem_comap, Pi.evalRingHom_apply, mem_pi]
    have hprime : (Finset.univ.inf (fun i ↦ (J i).comap (Pi.evalRingHom R i))).IsPrime :=
      hinf.symm ▸ hP.isPrime
    obtain ⟨i, _, hi⟩ := eq_inf_of_isPrime_inf hprime
    have hcomap : (P.map (Pi.evalRingHom R i)).comap (Pi.evalRingHom R i) = P :=
      hi.trans hinf
    have hq : P.map (Pi.evalRingHom R i) ∈ (I.map (Pi.evalRingHom R i)).minimalPrimes :=
      (comap_eval_mem_minimalPrimes_iff I i _).mp (hcomap.symm ▸ hP)
    refine ⟨⟨i, ⟨_, hq⟩⟩, hcomap.symm, ?_⟩
    intro b hb
    exact minimalPrimesPi_comap_injective I (hb.symm.trans hcomap.symm)
  · rintro ⟨a, rfl, _⟩
    exact (comap_eval_mem_minimalPrimes_iff I a.1 a.2.val).mpr a.2.property

/-- Minimal primes over an ideal of a finite product correspond to the dependent sum
of the minimal primes over its coordinate ideals. The inverse is evaluation comap. -/
noncomputable def minimalPrimesPiEquiv [Finite ι] (I : Ideal (∀ i, R i)) :
    I.minimalPrimes ≃ Σ i, ((piOrderIso (R := R)) I i).minimalPrimes :=
  (Equiv.ofBijective
    (fun a : Σ i, ((piOrderIso (R := R)) I i).minimalPrimes ↦
      (⟨a.2.val.comap (Pi.evalRingHom R a.1),
        (comap_eval_mem_minimalPrimes_iff I a.1 a.2.val).mpr a.2.property⟩ : I.minimalPrimes))
    ⟨fun _ _ h ↦ minimalPrimesPi_comap_injective I (congrArg Subtype.val h), by
      intro p
      obtain ⟨a, ha, _⟩ := (mem_minimalPrimes_pi_iff I p.val).mp p.property
      exact ⟨a, Subtype.ext ha.symm⟩⟩).symm

/-- The inverse classification map is evaluation comap on underlying ideals. -/
@[simp]
theorem minimalPrimesPiEquiv_symm_apply_coe [Finite ι] (I : Ideal (∀ i, R i))
    (a : Σ i, ((piOrderIso (R := R)) I i).minimalPrimes) :
    ((minimalPrimesPiEquiv I).symm a).val = a.2.val.comap (Pi.evalRingHom R a.1) :=
  rfl

/-- Evaluating the inverse ideal recovers the chosen coordinate ideal. -/
theorem minimalPrimesPiEquiv_map_symm_apply [Finite ι] (I : Ideal (∀ i, R i))
    (a : Σ i, ((piOrderIso (R := R)) I i).minimalPrimes) :
    (((minimalPrimesPiEquiv I).symm a).val).map (Pi.evalRingHom R a.1) = a.2.val := by
  rw [minimalPrimesPiEquiv_symm_apply_coe,
    map_comap_of_surjective _ (Function.surjective_eval a.1)]

/-- Classifying a coordinate comap retains that coordinate and minimal prime. -/
@[simp]
theorem minimalPrimesPiEquiv_apply_comap [Finite ι] (I : Ideal (∀ i, R i)) (i : ι)
    (q : ((piOrderIso (R := R)) I i).minimalPrimes) :
    minimalPrimesPiEquiv I
      ⟨q.val.comap (Pi.evalRingHom R i),
        (comap_eval_mem_minimalPrimes_iff I i q.val).mpr q.property⟩ = ⟨i, q⟩ :=
  (minimalPrimesPiEquiv I).apply_symm_apply ⟨i, q⟩

/-- The labelled coordinate returned by classification pulls back to the original ideal. -/
@[simp]
theorem minimalPrimesPiEquiv_comap_apply [Finite ι] (I : Ideal (∀ i, R i))
    (p : I.minimalPrimes) :
    (minimalPrimesPiEquiv I p).2.val.comap
      (Pi.evalRingHom R (minimalPrimesPiEquiv I p).1) = p.val :=
  congrArg Subtype.val ((minimalPrimesPiEquiv I).symm_apply_apply p)

end Ideal
