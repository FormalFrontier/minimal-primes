/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.GroupWithZero.InjSurj
public import Mathlib.RingTheory.Congruence.Defs

/-!
# Monoids with zero modulo multiplicative congruences

A multiplicative congruence on a monoid with zero gives its quotient a monoid-with-zero
structure. Its zero is the class of the source zero, and multiplication, one and natural
powers are the existing `Con.Quotient` operations. The monoid structure agrees with
`Con.monoid`; for a ring congruence it also agrees with the monoid-with-zero structure
underlying the quotient semiring.

## References

The construction follows Amelia Livingston's congruence quotient formalization in
`Mathlib.GroupTheory.Congruence.Defs` and uses Johan Commelin's surjective transports in
`Mathlib.Algebra.GroupWithZero.InjSurj`. The semiring comparison uses Eric Wieser's ring
congruence quotient formalization in `Mathlib.RingTheory.Congruence.Defs`.
-/

@[expose] public section

universe a

namespace Con

variable {A : Type a}

section Zero

variable [Mul A] [Zero A] (c : Con A)

/-- The zero of a multiplicative congruence quotient is the class of the source zero. -/
instance zero : Zero c.Quotient where
  zero := Quotient.mk'' (0 : A)

variable {c}

/-- The quotient projection preserves zero. -/
@[simp]
theorem coe_zero : ((0 : A) : c.Quotient) = 0 := rfl

end Zero

section MonoidWithZero

variable [MonoidWithZero A] (c : Con A)

/-- A multiplicative congruence quotient of a monoid with zero is a monoid with zero. -/
instance monoidWithZero : MonoidWithZero c.Quotient :=
  Function.Surjective.monoidWithZero (Quotient.mk'' : A → c.Quotient)
    Quotient.mk''_surjective rfl rfl (fun _ _ => rfl) fun _ _ => rfl

/-- The underlying monoid is the existing multiplicative congruence quotient monoid. -/
theorem monoidWithZero_toMonoid : (monoidWithZero c).toMonoid = monoid c := rfl

end MonoidWithZero

end Con

namespace RingCon

/-- The multiplicative congruence quotient structure agrees with the monoid-with-zero
structure underlying the ring congruence quotient semiring, including natural powers.

The right side uses the `RingCon.Quotient` semiring instance, rather than selecting a
monoid-with-zero instance independently. -/
theorem toCon_monoidWithZero {A : Type a} [Semiring A] (c : RingCon A) :
    Con.monoidWithZero c.toCon =
      (inferInstance : Semiring c.Quotient).toMonoidWithZero := rfl

end RingCon
