/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Data.Quot
public import MinimalPrimes.Order.Filter.Basic
public import MinimalPrimes.Order.Filter.Product

/-!
# Maps and selected fibres of dependent filter products

Coordinate functions descend along the existing quotient of total dependent
sections. No point, algebra or properness assumption is needed for this map.
Selected-section reflection is the dependent whole-section criterion from
`MinimalPrimes.Order.Filter.Basic`. Its zero specialization uses exactly the
chosen fibre zeros, without installing a zero instance on the product.

## References

The dependent carrier and representative-equality API are from
`MinimalPrimes.Order.Filter.Product` (Formal Frontier Agents). The construction
specializes `Quotient.map`; it introduces no new carrier or equality relation.
Constant-family comparisons use Mathlib's filter-germ API, developed by Yury
Kudryashov, Abhimanyu Pallavi Sudhir and the Mathlib contributors.
-/

@[expose] public section

universe u v w z

namespace Filter.Product

/-- The canonical map induced by a family of coordinate functions. -/
def map {ι : Type u} (D : Filter ι)
    {R : ι → Type v} {S : ι → Type w}
    (φ : ∀ i, R i → S i) : D.Product R → D.Product S :=
  Quotient.map (fun x i => φ i (x i)) fun {x y} h =>
    (Filter.productSetoid_apply D S _ _).2
      (((Filter.productSetoid_apply D R x y).1 h).mono
        (fun i hi => congrArg (φ i) hi))

/-- The class of the section of the selected fibre zeros. This is a point,
not a new zero instance on the product. -/
def zeroPoint {ι : Type u} (D : Filter ι) (R : ι → Type v)
    [∀ i, Zero (R i)] : D.Product R :=
  ((fun i => (0 : R i)) : D.Product R)

variable {ι : Type u} {R : ι → Type v} {S : ι → Type w} {T : ι → Type z}

/-- Equality of a represented class with the selected zero point is eventual zero.
Only the selected fibre Zero data are required. -/
@[simp]
theorem coe_eq_zeroPoint_iff (D : Filter ι) [∀ i, Zero (R i)] (r : ∀ i, R i) :
    (r : D.Product R) = zeroPoint D R ↔ ∀ᶠ i in D, r i = 0 :=
  coe_eq r (fun i => (0 : R i))

/-- Mapping a represented class is coordinatewise application. -/
@[simp]
theorem map_coe (D : Filter ι) (φ : ∀ i, R i → S i) (r : ∀ i, R i) :
    map D φ (r : D.Product R) = ((fun i => φ i (r i)) : D.Product S) :=
  rfl

/-- The existing section projection is surjective. -/
theorem coe_surjective (D : Filter ι) (R : ι → Type v) :
    Function.Surjective (fun r : ∀ i, R i => (r : D.Product R)) :=
  Quotient.mk_surjective

/-- Agreement on all representatives characterizes the canonical map. -/
theorem map_unique (D : Filter ι) (φ : ∀ i, R i → S i)
    (f : D.Product R → D.Product S)
    (hf : ∀ r : ∀ i, R i,
      f (r : D.Product R) = ((fun i => φ i (r i)) : D.Product S)) :
    f = map D φ := by
  funext x
  obtain ⟨r, rfl⟩ := coe_surjective D R x
  exact hf r

/-- The representative law uniquely specifies a map on the canonical quotient. -/
theorem existsUnique_map (D : Filter ι) (φ : ∀ i, R i → S i) :
    ∃! f : D.Product R → D.Product S, ∀ r : ∀ i, R i,
      f (r : D.Product R) = ((fun i => φ i (r i)) : D.Product S) :=
  ⟨map D φ, map_coe D φ, fun f hf => map_unique D φ f hf⟩

/-- Coordinate identities induce the identity on the quotient. -/
@[simp]
theorem map_id (D : Filter ι) (R : ι → Type v) :
    map D (fun i (r : R i) => r) = id := by
  funext x
  obtain ⟨r, rfl⟩ := coe_surjective D R x
  rfl

/-- Coordinatewise composition commutes with quotient mapping. -/
@[simp]
theorem map_map (D : Filter ι) (ψ : ∀ i, S i → T i)
    (φ : ∀ i, R i → S i) (x : D.Product R) :
    map D ψ (map D φ x) = map D (fun i r => ψ i (φ i r)) x := by
  obtain ⟨r, rfl⟩ := coe_surjective D R x
  rfl

/-- The function-level composition law. -/
theorem map_comp (D : Filter ι) (ψ : ∀ i, S i → T i) (φ : ∀ i, R i → S i) :
    map D ψ ∘ map D φ = map D (fun i r => ψ i (φ i r)) :=
  funext (map_map D ψ φ)

/-- The map on dependent filter products is injective exactly when there are no
whole source sections or the coordinate maps are eventually injective. -/
theorem map_injective_iff (D : Filter ι) (φ : ∀ i, R i → S i) :
    Function.Injective (map D φ) ↔
      IsEmpty (∀ i, R i) ∨ ∀ᶠ i in D, Function.Injective (φ i) := by
  have hsection : Function.Injective (map D φ) ↔
      ∀ f g : ∀ i, R i,
        (∀ᶠ i in D, φ i (f i) = φ i (g i)) → ∀ᶠ i in D, f i = g i := by
    constructor
    · intro h f g hfg
      apply (coe_eq f g).mp
      apply h
      rw [map_coe, map_coe]
      exact (coe_eq _ _).mpr hfg
    · intro h x y hxy
      obtain ⟨f, rfl⟩ := coe_surjective D R x
      obtain ⟨g, rfl⟩ := coe_surjective D R y
      apply (coe_eq f g).mpr
      apply h f g
      apply (coe_eq (fun i => φ i (f i)) (fun i => φ i (g i))).mp
      exact (map_coe D φ f).symm.trans (hxy.trans (map_coe D φ g))
  exact hsection.trans (Filter.forall_eventually_eq_of_map_eq_iff D φ)

/-- The exact onto criterion retains the empty-target and total-source alternatives. -/
theorem map_surjective_iff (D : Filter ι) (φ : ∀ i, R i → S i) :
    Function.Surjective (map D φ) ↔
      IsEmpty (∀ i, S i) ∨
        (Nonempty (∀ i, R i) ∧ ∀ᶠ i in D, Function.Surjective (φ i)) := by
  have hsection : Function.Surjective (map D φ) ↔
      ∀ s : ∀ i, S i, ∃ r : ∀ i, R i, ∀ᶠ i in D, φ i (r i) = s i := by
    constructor
    · intro h s
      obtain ⟨x, hx⟩ := h (s : D.Product S)
      obtain ⟨r, rfl⟩ := coe_surjective D R x
      refine ⟨r, (coe_eq (fun i => φ i (r i)) s).mp ?_⟩
      exact (map_coe D φ r).symm.trans hx
    · intro h y
      obtain ⟨s, rfl⟩ := coe_surjective D S y
      obtain ⟨r, hr⟩ := h s
      refine ⟨(r : D.Product R), ?_⟩
      rw [map_coe]
      exact (coe_eq _ _).mpr hr
  exact hsection.trans (Filter.forall_exists_eventually_eq_iff D φ)

/-- Coordinate reflection eventually implies reflection of the represented sections.
Preservation of the selected section is not needed in this direction. -/
theorem forall_map_eq_coe_imp_of_eventually (D : Filter ι)
    (φ : ∀ i, R i → S i) (a : ∀ i, R i) (b : ∀ i, S i)
    (h : ∀ᶠ i in D, ∀ r : R i, φ i r = b i → r = a i) :
    ∀ x : D.Product R, map D φ x = (b : D.Product S) → x = (a : D.Product R) := by
  intro x
  obtain ⟨r, rfl⟩ := coe_surjective D R x
  intro hr
  have he : ∀ᶠ i in D, φ i (r i) = b i := by
    apply (coe_eq (fun i => φ i (r i)) b).mp
    exact (map_coe D φ r).symm.trans hr
  exact (coe_eq r a).mpr ((h.and he).mono fun i hi => hi.1 _ hi.2)

/-- Under eventual preservation, selected-section reflection is coordinatewise eventually. -/
theorem forall_map_eq_coe_imp_iff (D : Filter ι)
    (φ : ∀ i, R i → S i) (a : ∀ i, R i) (b : ∀ i, S i)
    (h₀ : ∀ᶠ i in D, φ i (a i) = b i) :
    (∀ x : D.Product R,
      map D φ x = (b : D.Product S) → x = (a : D.Product R)) ↔
      ∀ᶠ i in D, ∀ r : R i, φ i r = b i → r = a i := by
  constructor
  · intro h
    apply (Filter.forall_eventually_map_eq_imp_iff D φ a b h₀).1
    intro r hr
    apply (coe_eq r a).mp
    apply h (r : D.Product R)
    rw [map_coe]
    exact (coe_eq _ _).mpr hr
  · exact forall_map_eq_coe_imp_of_eventually D φ a b

/-- The induced map preserves the SAME chosen zero-section points. -/
@[simp]
theorem map_zeroPoint (D : Filter ι) [∀ i, Zero (R i)] [∀ i, Zero (S i)]
    (g : ∀ i, ZeroHom (R i) (S i)) :
    map D (fun i => (g i : R i → S i)) (zeroPoint D R) = zeroPoint D S := by
  change map D (fun i => (g i : R i → S i))
    ((fun i => (0 : R i)) : D.Product R) = ((fun i => (0 : S i)) : D.Product S)
  rw [map_coe]
  exact (coe_eq _ _).mpr (Eventually.of_forall fun i => map_zero (g i))

/-- Zero-reflection on the product is exactly eventual coordinate zero-reflection.
The zero points come from the SAME selected fibre Zero records as the ZeroHoms. -/
theorem forall_map_eq_zeroPoint_imp_iff (D : Filter ι)
    [∀ i, Zero (R i)] [∀ i, Zero (S i)] (g : ∀ i, ZeroHom (R i) (S i)) :
    (∀ x : D.Product R,
      map D (fun i => (g i : R i → S i)) x = zeroPoint D S → x = zeroPoint D R) ↔
      ∀ᶠ i in D, ∀ r : R i, g i r = 0 → r = 0 :=
  forall_map_eq_coe_imp_iff D (fun i => (g i : R i → S i))
    (fun i => (0 : R i)) (fun i => (0 : S i))
    (Eventually.of_forall fun i => map_zero (g i))

/-- Under stronger data the selected point is exactly the existing product zero.
There is no separately chosen Zero instance in this statement. -/
@[simp]
theorem zeroPoint_eq_zero (D : Filter ι) (R : ι → Type v)
    [∀ i, MonoidWithZero (R i)] : zeroPoint D R = 0 :=
  coe_zero

/-- The class-free map agrees with the existing semiring map on its underlying function. -/
theorem map_eq_mapRingHom (D : Filter ι) [∀ i, Semiring (R i)] [∀ i, Semiring (S i)]
    (φ : ∀ i, R i →+* S i) :
    map D (fun i => (φ i : R i → S i)) = (mapRingHom D φ : D.Product R → D.Product S) := by
  symm
  apply map_unique D (fun i => (φ i : R i → S i))
  intro r
  rw [mapRingHom_coe]

/-- For constant fibres, the canonical map is varying evaluation on the existing germs. -/
theorem map_eq_germ_map₂ {A : Type v} {B : Type w} (D : Filter ι)
    (φ : ι → A → B) (x : Germ D A) :
    map D φ x = Germ.map₂ (fun (f : A → B) (a : A) => f a)
      (φ : Germ D (A → B)) x := by
  refine Germ.inductionOn x ?_
  intro r
  rfl

/-- A fixed coordinate function specializes to the existing unary germ map. -/
theorem map_const_eq_germ_map {A : Type v} {B : Type w} (D : Filter ι)
    (f : A → B) (x : Germ D A) :
    map D (fun _ => f) x = Germ.map f x := by
  refine Germ.inductionOn x ?_
  intro r
  rfl

/-- Constant-family selected zero agrees with the existing germ zero, with the same Zero. -/
@[simp]
theorem zeroPoint_eq_germ_zero {A : Type v} [Zero A] (D : Filter ι) :
    zeroPoint D (fun _ : ι => A) = (0 : Germ D A) :=
  Germ.coe_zero

end Filter.Product
