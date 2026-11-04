/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import MinimalPrimes.RingTheory.Spectrum.Maximal.Map

/-!
# Infinitude transported along a product projection

If one factor has infinitely many maximal ideals, so does the product ring: pullback
along the first projection embeds its maximal spectrum into that of the product.
-/

universe u v

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

private theorem infinite_maximalSpectrum_prod [Infinite (MaximalSpectrum R)] :
    Infinite (MaximalSpectrum (R × S)) :=
  Infinite.of_injective
    (MaximalSpectrum.comapEmbeddingOfSurjective (RingHom.fst R S) Prod.fst_surjective)
    (MaximalSpectrum.comapEmbeddingOfSurjective (RingHom.fst R S)
      Prod.fst_surjective).injective
