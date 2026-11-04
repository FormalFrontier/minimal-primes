/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Spectrum.Maximal.Basic
public import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# Pullback embeddings of maximal spectra

A surjective homomorphism of commutative rings induces the canonical embedding
`MaximalSpectrum.comapEmbeddingOfSurjective` by contraction of ideals. Its image
consists exactly of the maximal ideals containing the kernel. The embedding agrees
with prime-spectrum pullback and respects identity and contravariant composition.

No nontriviality hypothesis is required: the maximal spectrum of the zero ring is
empty. The ring hypothesis is essential for contraction to preserve maximality
under a surjection; this does not hold for arbitrary commutative semirings.

## References

This construction restricts Mathlib's ideal order embedding and ideal correspondence
for surjective homomorphisms in `Mathlib.RingTheory.Ideal.Maps`, using the existing
maximal spectrum and prime-spectrum pullback interfaces.
-/

@[expose] public section

universe u v w

namespace MaximalSpectrum

variable {R : Type u} {S : Type v} {T : Type w}
variable [CommRing R] [CommRing S] [CommRing T]

/-- Contraction along a surjective ring homomorphism, as an embedding of maximal spectra. -/
def comapEmbeddingOfSurjective (f : R →+* S) (hf : Function.Surjective f) :
    MaximalSpectrum S ↪ MaximalSpectrum R where
  toFun x := ⟨Ideal.comap f x.asIdeal, Ideal.comap_isMaximal_of_surjective f hf⟩
  inj' _ _ h := MaximalSpectrum.ext <|
    (Ideal.orderEmbeddingOfSurjective f hf).injective (congrArg asIdeal h)

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
    M ∈ Set.range (comapEmbeddingOfSurjective f hf) ↔ RingHom.ker f ≤ M.asIdeal := by
  constructor
  · rintro ⟨x, rfl⟩
    exact Ideal.ker_le_comap f
  · intro hM
    refine ⟨⟨M.asIdeal.map f, Ideal.IsMaximal.map_of_surjective_of_ker_le hf hM⟩, ?_⟩
    apply MaximalSpectrum.ext
    exact congrArg Subtype.val <|
      (Ideal.relIsoOfSurjective f hf).apply_symm_apply ⟨M.asIdeal, hM⟩

end MaximalSpectrum
