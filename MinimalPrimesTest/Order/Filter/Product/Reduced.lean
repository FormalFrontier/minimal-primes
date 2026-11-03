/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import MinimalPrimes.Order.Filter.Product.Reduced
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Algebra.GroupWithZero.WithZero

/-!
# A reduced product of varying nonadditive fibres

The free-monoid fibres vary with the index and need no semiring structure.
-/

example (D : Filter ℕ) :
    IsReduced (D.Product (fun n => WithZero (FreeMonoid (Fin (n + 2))))) := by
  apply Filter.Product.isReduced_iff.2
  exact Filter.Eventually.of_forall fun _ => inferInstance
