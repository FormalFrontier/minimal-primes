/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Spectrum.Maximal.Basic
public import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# Pullback of maximal spectra along integral homomorphisms

An integral homomorphism of commutative rings induces the canonical function
`MaximalSpectrum.comapOfIsIntegral` by contraction of ideals. Its image consists
exactly of the maximal ideals containing the kernel, and it is surjective when
the ring homomorphism is injective. It agrees with prime-spectrum pullback and
respects identity and contravariant composition.

For surjective ring homomorphisms, the same function gives the embedding
`MaximalSpectrum.comapEmbeddingOfSurjective`. No nontriviality hypothesis is
required: the maximal spectrum of the zero ring is empty. The ring hypothesis
is essential even for contraction under a surjection; maximality need not be
preserved for arbitrary commutative semirings.

## References

The integral construction uses Mathlib's maximality theorem
`Ideal.isMaximal_comap_of_isIntegral_of_isMaximal` and its kernel-containment
lying-over theorem `Ideal.exists_ideal_over_maximal_of_isIntegral` in
`Mathlib.RingTheory.Ideal.GoingUp`. The surjective embedding restricts Mathlib's
ideal order embedding in `Mathlib.RingTheory.Ideal.Maps`. Both use the existing
maximal spectrum and prime-spectrum pullback interfaces.
-/

@[expose] public section

universe u v w

namespace MaximalSpectrum

variable {R : Type u} {S : Type v} {T : Type w}
variable [CommRing R] [CommRing S] [CommRing T]

/-- Contraction of maximal ideals along an integral ring homomorphism. -/
def comapOfIsIntegral (f : R →+* S) (hf : f.IsIntegral) :
    MaximalSpectrum S → MaximalSpectrum R :=
  fun x => ⟨Ideal.comap f x.asIdeal,
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal f hf x.asIdeal⟩

/-- The underlying ideal of integral pullback is its contraction. -/
@[simp]
theorem comapOfIsIntegral_asIdeal (f : R →+* S) (hf : f.IsIntegral)
    (x : MaximalSpectrum S) :
    (comapOfIsIntegral f hf x).asIdeal = Ideal.comap f x.asIdeal :=
  rfl

/-- Integral maximal-spectrum pullback agrees with prime-spectrum pullback. -/
@[simp]
theorem toPrimeSpectrum_comapOfIsIntegral (f : R →+* S) (hf : f.IsIntegral)
    (x : MaximalSpectrum S) :
    (comapOfIsIntegral f hf x).toPrimeSpectrum =
      PrimeSpectrum.comap f x.toPrimeSpectrum :=
  rfl

/-- Integral pullback along the identity is the identity function. -/
@[simp]
theorem comapOfIsIntegral_id :
    comapOfIsIntegral (RingHom.id R)
      ((RingHom.id R).isIntegral_of_surjective Function.surjective_id) =
        (fun x : MaximalSpectrum R => x) :=
  rfl

/-- Integral pullback reverses composition of ring homomorphisms. -/
@[simp]
theorem comapOfIsIntegral_comp (f : R →+* S) (g : S →+* T)
    (hf : f.IsIntegral) (hg : g.IsIntegral) :
    comapOfIsIntegral (g.comp f) (RingHom.IsIntegral.trans f g hf hg) =
      (comapOfIsIntegral f hf).comp (comapOfIsIntegral g hg) :=
  rfl

/-- A maximal ideal is an integral pullback exactly when it contains the kernel.
This uses Mathlib's maximal lying-over theorem with kernel containment. -/
theorem mem_range_comapOfIsIntegral (f : R →+* S) (hf : f.IsIntegral)
    (M : MaximalSpectrum R) :
    M ∈ Set.range (comapOfIsIntegral f hf) ↔ RingHom.ker f ≤ M.asIdeal := by
  constructor
  · rintro ⟨x, rfl⟩
    exact Ideal.ker_le_comap f
  · intro hM
    let : Algebra R S := f.toAlgebra
    let : Algebra.IsIntegral R S := ⟨hf⟩
    obtain ⟨Q, hQ, hQM⟩ :=
      Ideal.exists_ideal_over_maximal_of_isIntegral (S := S) M.asIdeal hM
    refine ⟨⟨Q, hQ⟩, ?_⟩
    apply MaximalSpectrum.ext
    exact hQM

/-- Contraction along an injective integral homomorphism is surjective on maximal spectra. -/
theorem surjective_comapOfIsIntegral (f : R →+* S) (hf : f.IsIntegral)
    (hinj : Function.Injective f) : Function.Surjective (comapOfIsIntegral f hf) := by
  intro M
  apply (mem_range_comapOfIsIntegral f hf M).2
  rw [(RingHom.injective_iff_ker_eq_bot f).mp hinj]
  exact bot_le

/-- Contraction along a surjective ring homomorphism, as an embedding of maximal spectra. -/
def comapEmbeddingOfSurjective (f : R →+* S) (hf : Function.Surjective f) :
    MaximalSpectrum S ↪ MaximalSpectrum R where
  toFun := comapOfIsIntegral f (f.isIntegral_of_surjective hf)
  inj' _ _ h := MaximalSpectrum.ext <|
    (Ideal.orderEmbeddingOfSurjective f hf).injective (congrArg asIdeal h)

/-- The surjective pullback embedding has the integral pullback as its underlying function. -/
@[simp]
theorem coe_comapEmbeddingOfSurjective (f : R →+* S) (hf : Function.Surjective f) :
    (comapEmbeddingOfSurjective f hf : MaximalSpectrum S → MaximalSpectrum R) =
      comapOfIsIntegral f (f.isIntegral_of_surjective hf) :=
  rfl

/-- The underlying ideal of a pulled-back maximal-spectrum point is its contraction. -/
@[simp]
theorem comapEmbeddingOfSurjective_asIdeal (f : R →+* S) (hf : Function.Surjective f)
    (x : MaximalSpectrum S) :
    (comapEmbeddingOfSurjective f hf x).asIdeal = Ideal.comap f x.asIdeal :=
  rfl

/-- Maximal-spectrum pullback agrees with the existing prime-spectrum pullback. -/
@[simp]
theorem toPrimeSpectrum_comapEmbeddingOfSurjective (f : R →+* S)
    (hf : Function.Surjective f) (x : MaximalSpectrum S) :
    (comapEmbeddingOfSurjective f hf x).toPrimeSpectrum =
      PrimeSpectrum.comap f x.toPrimeSpectrum :=
  rfl

/-- Pullback along the identity is the identity embedding. -/
@[simp]
theorem comapEmbeddingOfSurjective_id :
    comapEmbeddingOfSurjective (RingHom.id R) Function.surjective_id =
      Function.Embedding.refl (MaximalSpectrum R) :=
  rfl

/-- Pullback reverses composition of surjective homomorphisms. -/
@[simp]
theorem comapEmbeddingOfSurjective_comp (f : R →+* S) (g : S →+* T)
    (hf : Function.Surjective f) (hg : Function.Surjective g) :
    comapEmbeddingOfSurjective (g.comp f) (hg.comp hf) =
      (comapEmbeddingOfSurjective g hg).trans (comapEmbeddingOfSurjective f hf) :=
  rfl

/-- A maximal ideal is a pullback exactly when it contains the kernel. -/
theorem mem_range_comapEmbeddingOfSurjective (f : R →+* S) (hf : Function.Surjective f)
    (M : MaximalSpectrum R) :
    M ∈ Set.range (comapEmbeddingOfSurjective f hf) ↔ RingHom.ker f ≤ M.asIdeal :=
  mem_range_comapOfIsIntegral f (f.isIntegral_of_surjective hf) M

end MaximalSpectrum
