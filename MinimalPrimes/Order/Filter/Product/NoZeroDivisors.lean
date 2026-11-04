/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MinimalPrimes.Order.Filter.Basic
public import MinimalPrimes.Order.Filter.Product

/-!
# Zero divisors in dependent filter products

An ultrafilter product has no zero divisors exactly when its fibres have no zero
divisors eventually. The criterion uses only zero and multiplication on the fibres,
with the quotient operations supplied by their multiplicative congruence. It does
not require a unit, associativity, absorption by zero or nontriviality.

For an arbitrary filter and fibres with two-sided absorbing zero, no zero divisors
is equivalent to eventual fibrewise no zero divisors together with the condition
that the filter restricted to nontrivial fibres is bottom or an atom. This criterion
needs neither a unit nor associativity, and allows singleton fibres and improper filters.

Congruence multiplication agrees with canonical product multiplication using only
multiplication on the fibres. For monoids with zero, the congruence zero also agrees
with the canonical product zero. The monoid-with-zero criteria use those structures
without adding a zero or multiplication instance.

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

/-- The primitive congruence operations on a dependent filter product with absorbing zero
have no zero divisors exactly when the fibres have no zero divisors eventually and the
restriction of the filter to nontrivial fibres is bottom or an atom. No unit, associativity,
properness or nontriviality hypothesis is required. -/
theorem noZeroDivisors_iff_eventually_and_trace [∀ i, MulZeroClass (R i)] (F : Filter ι) :
    @NoZeroDivisors (F.Product R)
        (Con.hasMul (Filter.productCon F R))
        (Con.zero (Filter.productCon F R)) ↔
      (∀ᶠ i in F,
        @NoZeroDivisors (R i)
          (inferInstance : Mul (R i)) (inferInstance : Zero (R i))) ∧
      (F ⊓ Filter.principal {i | Nontrivial (R i)} = ⊥ ∨
        IsAtom (F ⊓ Filter.principal {i | Nontrivial (R i)})) := by
  classical
  let T : Set ι := {i | Nontrivial (R i)}
  let D : Filter ι := F ⊓ principal T
  have hfibre (i : ι) (hi : i ∉ T) : NoZeroDivisors (R i) :=
    @Subsingleton.to_noZeroDivisors (R i)
      (inferInstance : Mul (R i)) (inferInstance : Zero (R i))
      (not_nontrivial_iff_subsingleton.mp hi)
  have heventually :
      (∀ᶠ i in F, NoZeroDivisors (R i)) ↔ ∀ᶠ i in D, NoZeroDivisors (R i) := by
    simp only [D, eventually_inf_principal]
    constructor
    · exact fun h => h.mono fun _ hi _ => hi
    · intro h
      exact h.mono fun i hi => by
        by_cases hT : i ∈ T
        · exact hi hT
        · exact hfibre i hT
  -- The trace leaves the section relation unchanged. Transport the entire predicate,
  -- including its carrier and both operation records, along congruence equality.
  have hcon : productCon F R = productCon D R := by
    apply Con.toSetoid_injective
    exact (productSetoid_eq_iff F D).2
      (Or.inr (by simp only [D, T, inf_assoc, inf_idem]))
  have hquot :
      @NoZeroDivisors (F.Product R)
          (Con.hasMul (productCon F R)) (Con.zero (productCon F R)) ↔
        @NoZeroDivisors (D.Product R)
          (Con.hasMul (productCon D R)) (Con.zero (productCon D R)) :=
    (congrArg (fun c : Con (∀ i, R i) =>
      @NoZeroDivisors c.Quotient (Con.hasMul c) (Con.zero c)) hcon).to_iff
  have hbottom (hD : D = ⊥) :
      @NoZeroDivisors (F.Product R)
          (Con.hasMul (productCon F R)) (Con.zero (productCon F R)) ∧
        ∀ᶠ i in F, NoZeroDivisors (R i) := by
    have hnot : ∀ᶠ i in F, i ∉ T := inf_principal_eq_bot.1 hD
    have hsingle : ∀ᶠ i in F, Subsingleton (R i) :=
      hnot.mono fun _ hi => not_nontrivial_iff_subsingleton.mp hi
    have hsub : Subsingleton (F.Product R) :=
      (subsingleton_iff_of_nonempty (F := F) (K := R) ⟨fun i => 0⟩).2 hsingle
    exact ⟨@Subsingleton.to_noZeroDivisors (F.Product R)
        (Con.hasMul (productCon F R)) (Con.zero (productCon F R)) hsub,
      hsingle.mono fun i hi => @Subsingleton.to_noZeroDivisors (R i)
        (inferInstance : Mul (R i)) (inferInstance : Zero (R i)) hi⟩
  have hatom (hD : IsAtom D) :
      @NoZeroDivisors (F.Product R)
          (Con.hasMul (productCon F R)) (Con.zero (productCon F R)) ↔
        ∀ᶠ i in F, NoZeroDivisors (R i) :=
    hquot.trans ((noZeroDivisors_iff_eventually (Ultrafilter.ofAtom D hD)).trans
      heventually.symm)
  have htrace
      (h : @NoZeroDivisors (F.Product R)
        (Con.hasMul (productCon F R)) (Con.zero (productCon F R))) :
      D = ⊥ ∨ IsAtom D := by
    have hvanish (S : Set ι)
        (hS : ∀ f : ∀ i, R i, ∀ᶠ i in F, i ∈ S → f i = 0) : Sᶜ ∈ D := by
      apply mem_inf_principal.2
      have hall : ∀ᶠ i in F, ∀ x : R i, i ∈ S → x = 0 :=
        (eventually_forall_iff_forall_section
          (D := F) (P := fun i x => i ∈ S → x = 0) (fun i => 0)).2 hS
      exact hall.mono fun i hi hT hiS => by
        have hsub : Subsingleton (R i) :=
          ⟨fun x y => (hi x hiS).trans (hi y hiS).symm⟩
        exact (not_nontrivial_iff_subsingleton.mpr hsub) hT
    have hpartition (S : Set ι) : S ∈ D ∨ Sᶜ ∈ D := by
      have hsections (f g : ∀ i, R i) :
          (∀ᶠ i in F, i ∈ S → f i = 0) ∨ (∀ᶠ i in F, i ∉ S → g i = 0) := by
        let a : ∀ i, R i := fun i => if i ∈ S then f i else 0
        let b : ∀ i, R i := fun i => if i ∈ S then 0 else g i
        have hmul :
            @Mul.mul (F.Product R) (Con.hasMul (productCon F R))
                (a : F.Product R) (b : F.Product R) =
              @Zero.zero (F.Product R) (Con.zero (productCon F R)) := by
          apply (coe_eq_con_zero_iff F (a * b)).2
          exact Eventually.of_forall fun i => by
            change a i * b i = 0
            by_cases hi : i ∈ S
            · simp only [a, b, ite_eq_left hi, mul_zero]
            · simp only [a, b, ite_eq_right hi, zero_mul]
        rcases @NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero
            (F.Product R) (Con.hasMul (productCon F R))
            (Con.zero (productCon F R)) h (a : F.Product R) (b : F.Product R) hmul
            with ha | hb
        · exact Or.inl (((coe_eq_con_zero_iff F a).1 ha).mono fun i hi hiS => by
            simpa only [a, ite_eq_left hiS] using hi)
        · exact Or.inr (((coe_eq_con_zero_iff F b).1 hb).mono fun i hi hiS => by
            simpa only [b, ite_eq_right hiS] using hi)
      -- The masks use independent sections: separating their universal quantifiers
      -- needs no choice of an everywhere-nonzero section on the nontrivial locus.
      have hseparated :
          (∀ f : ∀ i, R i, ∀ᶠ i in F, i ∈ S → f i = 0) ∨
            (∀ g : ∀ i, R i, ∀ᶠ i in F, i ∉ S → g i = 0) :=
        forall_or_right.mp (fun f => forall_or_left.mp (hsections f))
      rcases hseparated with hS | hSc
      · exact Or.inr (hvanish S hS)
      · exact Or.inl (by simpa only [compl_compl] using hvanish Sᶜ hSc)
    by_cases hD : D = ⊥
    · exact Or.inl hD
    · let : NeBot D := ⟨hD⟩
      exact Or.inr (Ultrafilter.ofComplNotMemIff D (fun S =>
        ⟨fun hSc => (hpartition S).resolve_right hSc,
          fun hS => Filter.compl_notMem hS⟩)).isAtom
  constructor
  · intro h
    have hD := htrace h
    refine ⟨?_, hD⟩
    rcases hD with hD | hD
    · exact (hbottom hD).2
    · exact (hatom hD).1 h
  · rintro ⟨hfibres, hD | hD⟩
    · exact (hbottom hD).1
    · exact (hatom hD).2 hfibres

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

/-- A dependent filter product of monoids with zero has no zero divisors exactly when
the fibres have no zero divisors eventually and the filter restricted to nontrivial
fibres is bottom or an atom. This uses the canonical product operations for every filter. -/
theorem noZeroDivisors_iff_eventually_and_trace_of_monoidWithZero (F : Filter ι) :
    NoZeroDivisors (F.Product R) ↔
      (∀ᶠ i in F, NoZeroDivisors (R i)) ∧
      (F ⊓ Filter.principal {i | Nontrivial (R i)} = ⊥ ∨
        IsAtom (F ⊓ Filter.principal {i | Nontrivial (R i)})) :=
  noZeroDivisors_iff_eventually_and_trace F

end MonoidWithZero

end Product
end Filter
