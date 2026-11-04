/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.Module.Torsion.Pi
import Mathlib.Algebra.Ring.Prod
import Mathlib.Data.ZMod.Defs
import Mathlib.Order.Filter.Cofinite
import MinimalPrimes.Order.Filter.Product.Torsion

/-!
# A client of the inherited reduced-product semimodule action

This checks the action inherited by the named `Module`, on an opaque vector,
with all three fibre records supplied independently. In particular it does not
replace the fibre modules when scalar and vector carrier families specialize.

A second client applies the torsion-free criterion along the cofinite filter to
free pointwise semimodules of varying finite ranks over `ℕ × ZMod (n + 2)`.
These scalar semirings have zero divisors, and the vectors need not form groups.
-/

universe u v w

open Filter

variable {ι : Type u} (F : Filter ι) (R : ι → Type v) (M : ι → Type w)
    [s : ∀ i, Semiring (R i)] [a : ∀ i, AddCommMonoid (M i)]
    [p : ∀ i, Module (R i) (M i)]

example (r : ∀ i, R i) (x : F.Product M) :
    @SMul.smul (F.Product R) (F.Product M)
      (Product.module (s := s) (a := a) (p := p) F M R).toSMul
      (r : F.Product R) x = Product.map F (fun i m => r i • m) x :=
  congrFun (Product.smul_coe_eq_map F M R r) x

private abbrev varyingScalar (n : ℕ) := ℕ × ZMod (n + 2)

private abbrev varyingVector (n : ℕ) := Fin (n + 1) → varyingScalar n

/-- Varying free semimodules over semirings with zero divisors remain torsion-free
in their cofinite reduced product, with both scalar types and ranks varying. -/
private theorem cofinite_varying_free_isTorsionFree :
    @Module.IsTorsionFree
      ((cofinite : Filter ℕ).Product varyingScalar)
      ((cofinite : Filter ℕ).Product varyingVector)
      (Product.instSemiring (F := cofinite) (K := varyingScalar))
      (Product.addCommMonoid cofinite varyingVector)
      (Product.module cofinite varyingVector varyingScalar) := by
  apply (Product.isTorsionFree_iff cofinite varyingScalar varyingVector).mpr
  exact Eventually.of_forall fun _ => inferInstance
