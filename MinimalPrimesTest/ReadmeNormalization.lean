/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import MinimalPrimes.Principal

/-! # README example: a caller's local normalization choice -/

noncomputable local instance readmeNormalization (M : Type*) [CommMonoidWithZero M]
    [UniqueFactorizationMonoid M] : StrongNormalizationMonoid M :=
  UniqueFactorizationMonoid.strongNormalizationMonoid
