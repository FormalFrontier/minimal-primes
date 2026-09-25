/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import MinimalPrimes.IrreducibleComponents
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.RingTheory.PrincipalIdealDomain

/-! # README example: order-dual components of the integer zero locus -/

open UniqueFactorizationMonoid TopologicalSpace

noncomputable section

private def readme_integerComponents {f : ℤ} (hf : f ≠ 0) :
    {p // p ∈ normalizedFactors f} ≃
      (irreducibleComponents
        (PrimeSpectrum.zeroLocus (Ideal.span {f} : Set ℤ)))ᵒᵈ :=
  Ideal.normalizedFactorsEquivIrreducibleComponents hf
