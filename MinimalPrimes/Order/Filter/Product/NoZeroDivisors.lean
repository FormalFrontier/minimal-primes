/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MinimalPrimes.Order.Filter.Basic
public import MinimalPrimes.Order.Filter.Product

/-!
# Zero divisors in ultrafilter products

An ultrafilter product has no zero divisors exactly when its fibres have no zero
divisors eventually. The criterion uses only zero and multiplication on the fibres,
with the quotient operations supplied by their multiplicative congruence. It does
not require a unit, associativity, absorption by zero or nontriviality.

Congruence multiplication agrees with canonical product multiplication using only
multiplication on the fibres. For monoids with zero, the congruence zero also agrees
with the canonical product zero. The final criterion uses those structures without
adding a zero or multiplication instance.

## References

The quotient operations reuse Amelia Livingston's multiplicative-congruence API
and the dependent filter product of Yury Kudryashov and Abhimanyu Pallavi Sudhir.
The proof uses the existing total-section reflection theorem and Mathlib's
ultrafilter alternative, rather than a separate choice construction.
-/

@[expose] public section

universe u v

namespace Filter
namespace Product

variable {ι : Type u} {R : ι → Type v}

section ZeroMul

variable [∀ i, Zero (R i)] [∀ i, Mul (R i)]

private theorem coe_eq_con_zero_iff (F : Filter ι) (f : ∀ i, R i) :
    (f : F.Product R) = @Zero.zero (F.Product R) (Con.zero (productCon F R)) ↔
      ∀ᶠ i in F, f i = 0 :=
  coe_eq f (0 : ∀ i, R i)

/-- The primitive congruence operations on an ultrafilter product have no zero
    divisors exactly when the fibre operations have no zero divisors eventually. -/
theorem noZeroDivisors_iff_eventually (U : Ultrafilter ι) :
    @NoZeroDivisors ((U : Filter ι).Product R)
        (Con.hasMul (productCon (U : Filter ι) R))
        (Con.zero (productCon (U : Filter ι) R)) ↔
      ∀ᶠ i in (U : Filter ι),
        @NoZeroDivisors (R i) (inferInstance : Mul (R i)) (inferInstance : Zero (R i)) := by
  constructor
  · intro h
    have hsections (f g : ∀ i, R i) :
        ∀ᶠ i in (U : Filter ι), f i * g i = 0 → f i = 0 ∨ g i = 0 := by
      rcases U.em (fun i => f i * g i = 0) with hmul | hmul
      · have hquot := (coe_eq_con_zero_iff (U : Filter ι) (f * g)).2 hmul
        rcases @NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero
            ((U : Filter ι).Product R) (Con.hasMul (productCon (U : Filter ι) R))
            (Con.zero (productCon (U : Filter ι) R)) h
            (f : (U : Filter ι).Product R) (g : (U : Filter ι).Product R) hquot with hf | hg
        · exact ((coe_eq_con_zero_iff (U : Filter ι) f).1 hf).mono
            fun _ hi _ => Or.inl hi
        · exact ((coe_eq_con_zero_iff (U : Filter ι) g).1 hg).mono
            fun _ hi _ => Or.inr hi
      · exact hmul.mono fun _ hi hzero => (hi hzero).elim
    have hright (f : ∀ i, R i) :
        ∀ᶠ i in (U : Filter ι), ∀ b : R i,
          f i * b = 0 → f i = 0 ∨ b = 0 :=
      (eventually_forall_iff_forall_section
        (D := (U : Filter ι)) (P := fun i b => f i * b = 0 → f i = 0 ∨ b = 0)
        (0 : ∀ i, R i)).2 (hsections f)
    have hfibres : ∀ᶠ i in (U : Filter ι), ∀ a b : R i,
        a * b = 0 → a = 0 ∨ b = 0 :=
      (eventually_forall_iff_forall_section
        (D := (U : Filter ι)) (P := fun i a => ∀ b : R i, a * b = 0 → a = 0 ∨ b = 0)
        (0 : ∀ i, R i)).2 hright
    exact hfibres.mono fun _ hi => by
      constructor
      intro a b hab
      exact hi a b hab
  · intro h
    refine @NoZeroDivisors.mk ((U : Filter ι).Product R)
      (Con.hasMul (productCon (U : Filter ι) R))
      (Con.zero (productCon (U : Filter ι) R)) ?_
    intro a b
    refine Quotient.inductionOn₂' a b ?_
    intro f g hmul
    have hzero : ∀ᶠ i in (U : Filter ι), f i * g i = 0 :=
      (coe_eq_con_zero_iff (U : Filter ι) (f * g)).1 hmul
    have hor : ∀ᶠ i in (U : Filter ι), f i = 0 ∨ g i = 0 :=
      (h.and hzero).mono fun _ hi => by
        let := hi.1
        exact eq_zero_or_eq_zero_of_mul_eq_zero hi.2
    rcases Ultrafilter.eventually_or.1 hor with hf | hg
    · exact Or.inl ((coe_eq_con_zero_iff (U : Filter ι) f).2 hf)
    · exact Or.inr ((coe_eq_con_zero_iff (U : Filter ι) g).2 hg)

end ZeroMul

/-- Primitive congruence multiplication is canonical product multiplication. -/
theorem con_mul_eq_mul [∀ i, Mul (R i)] (F : Filter ι) (a b : F.Product R) :
    @Mul.mul (F.Product R) (Con.hasMul (productCon F R)) a b = a * b := rfl

section MonoidWithZero

variable [∀ i, MonoidWithZero (R i)]

/-- The primitive congruence zero is the canonical product zero. -/
theorem con_zero_eq_zero (F : Filter ι) :
    @Zero.zero (F.Product R) (Con.zero (productCon F R)) = (0 : F.Product R) := rfl

/-- An ultrafilter product of monoids with zero has no zero divisors exactly when
    the fibres have no zero divisors eventually. -/
theorem noZeroDivisors_iff (U : Ultrafilter ι) :
    NoZeroDivisors ((U : Filter ι).Product R) ↔
      ∀ᶠ i in (U : Filter ι), NoZeroDivisors (R i) :=
  noZeroDivisors_iff_eventually U

end MonoidWithZero

end Product
end Filter
