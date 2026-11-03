/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Group.Pi.Units
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Order.Filter.Germ.Basic

/-!
# Units in monoids of filter germs

A germ is a unit exactly when its representative is a unit on a filter-large set.
The coefficient monoid need not be commutative, and the filter need not be proper.
Germs of units are multiplicatively equivalent to units of germs, and every unit
of the germ monoid has an everywhere-unit representative.

## Implementation notes

The forward implication uses both inverse identities on a common filter-large set.
For the converse, replacing nonunit values by `1` gives a unit in the total function
monoid, whose image under `Filter.Germ.coeMulHom` is the original germ.
The equivalence bundles the coefficientwise value map and lifts it with
`MonoidHom.toHomUnits`. The unit-locus criterion and `Filter.skolem` supply a
unit-valued representative for surjectivity.

## References

The proof uses Mathlib's germ quotient and coercion monoid homomorphism, formalized
by Yury Kudryashov and Abhimanyu Pallavi Sudhir, and Andrew Yang's total-product
unit criterion `Pi.isUnit_iff`. The equivalence uses Mathlib's lift of a monoid
homomorphism from a group to units, formalized by Johan Commelin, Chris Hughes and
Kevin Buzzard, and Andrew Yang's total-product equivalence `MulEquiv.piUnits`.
The representative choice uses the filter API developed by Johannes Hölzl and
Jeremy Avigad.
-/

@[expose] public section

universe u v

namespace Filter.Germ

variable {ι : Type u} {M : Type v} [Monoid M]

/-- A germ in a monoid is a unit if and only if its representative is eventually a unit. -/
theorem isUnit_coe_iff (D : Filter ι) (f : ι → M) :
    IsUnit (f : Filter.Germ D M) ↔ ∀ᶠ i in D, IsUnit (f i) := by
  constructor
  · intro hf
    obtain ⟨g, hfg, hgf⟩ := isUnit_iff_exists.mp hf
    revert hfg hgf
    refine inductionOn g fun g hfg hgf => ?_
    have hfg' : ∀ᶠ i in D, f i * g i = 1 := coe_eq.mp hfg
    have hgf' : ∀ᶠ i in D, g i * f i = 1 := coe_eq.mp hgf
    filter_upwards [hfg', hgf'] with i hfg hgf
    exact isUnit_iff_exists.mpr ⟨g i, hfg, hgf⟩
  · intro hf
    classical
    let g : ι → M := fun i => if IsUnit (f i) then f i else 1
    have hg : IsUnit g := Pi.isUnit_iff.mpr fun i => by
      by_cases hi : IsUnit (f i) <;> simp [g, hi]
    have hgf : (g : Filter.Germ D M) = f :=
      coe_eq.mpr <| hf.mono fun i hi => by simp [g, hi]
    exact hgf ▸ IsUnit.map (coeMulHom D) hg

private def unitsValHom (D : Filter ι) : Germ D Mˣ →* Germ D M where
  toFun := map (Units.coeHom M)
  map_one' := rfl
  map_mul' g h := inductionOn₂ g h fun _ _ => rfl

private theorem unitsValHom_injective (D : Filter ι) :
    Function.Injective (unitsValHom D : Germ D Mˣ → Germ D M) := by
  intro g h
  refine inductionOn₂ g h fun _ _ hfg => ?_
  exact coe_eq.mpr <| (coe_eq.mp hfg).mono fun _ hi => Units.ext hi

private theorem exists_units_map_eq (D : Filter ι) (g : Germ D M) (hg : IsUnit g) :
    ∃ u : Germ D Mˣ, map (Units.coeHom M) u = g := by
  revert hg
  refine inductionOn g ?_
  intro f hf
  have hf' : ∀ᶠ i in D, ∃ u : Mˣ, (u : M) = f i :=
    (isUnit_coe_iff D f).mp hf
  obtain ⟨u, hu⟩ : ∃ u : ι → Mˣ, ∀ᶠ i in D, (u i : M) = f i :=
    Filter.skolem.mp hf'
  refine ⟨(u : Germ D Mˣ), ?_⟩
  rw [map_coe]
  exact coe_eq.mpr hu

private theorem unitsValHom_toHomUnits_bijective (D : Filter ι) :
    Function.Bijective ((unitsValHom (M := M) D).toHomUnits) := by
  constructor
  · intro g h hgh
    exact unitsValHom_injective D (congrArg Units.val hgh)
  · intro u
    obtain ⟨g, hg⟩ := exists_units_map_eq D (u : Germ D M) u.isUnit
    exact ⟨g, Units.ext hg⟩

/-- The multiplicative equivalence between germs of units and units of germs. -/
@[no_expose]
noncomputable def unitsMulEquiv (D : Filter ι) : Germ D Mˣ ≃* (Germ D M)ˣ :=
  MulEquiv.ofBijective (unitsValHom (M := M) D).toHomUnits
    (unitsValHom_toHomUnits_bijective (M := M) D)

/-- The value of a unit germ is obtained by mapping the values of its unit coefficients. -/
@[simp]
theorem coe_unitsMulEquiv (D : Filter ι) (g : Germ D Mˣ) :
    (unitsMulEquiv D g : Germ D M) = map (Units.coeHom M) g := by
  have hforward : unitsMulEquiv D g = (unitsValHom D).toHomUnits g :=
    congrFun (Equiv.coe_ofBijective (unitsValHom (M := M) D).toHomUnits
      (unitsValHom_toHomUnits_bijective D)) g
  exact (congrArg Units.val hforward).trans
    (MonoidHom.coe_toHomUnits (unitsValHom D) g)

/-- Mapping unit values over the inverse equivalence recovers the given germ. -/
@[simp]
theorem map_coeHom_unitsMulEquiv_symm (D : Filter ι) (u : (Germ D M)ˣ) :
    map (Units.coeHom M) ((unitsMulEquiv D).symm u) = (u : Germ D M) := by
  rw [← coe_unitsMulEquiv, MulEquiv.apply_symm_apply]

/-- The germ equivalence commutes with the total-product unit equivalence and section map. -/
@[simp]
theorem unitsMulEquiv_coe_piUnits (D : Filter ι) (w : (ι → M)ˣ) :
    unitsMulEquiv D ((MulEquiv.piUnits w : ι → Mˣ) : Germ D Mˣ) =
      Units.map (coeMulHom D) w := by
  apply Units.ext
  rw [coe_unitsMulEquiv]
  rfl

/-- Every unit of a germ monoid has a representative that is a unit in the function monoid. -/
theorem units_map_coeMulHom_surjective (D : Filter ι) :
    Function.Surjective (Units.map (coeMulHom D : (ι → M) →* Germ D M)) := by
  intro u
  obtain ⟨v, hv⟩ := Quotient.mk_surjective ((unitsMulEquiv D).symm u)
  refine ⟨MulEquiv.piUnits.symm v, ?_⟩
  rw [← unitsMulEquiv_coe_piUnits, MulEquiv.apply_symm_apply]
  exact (congrArg (unitsMulEquiv D) hv).trans ((unitsMulEquiv D).apply_symm_apply u)

end Filter.Germ
