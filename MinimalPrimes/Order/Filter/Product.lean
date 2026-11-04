/-
Copyright (c) 2019 Abhimanyu Pallavi Sudhir. All rights reserved.
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Order.Filter.FilterProduct
public import Mathlib.RingTheory.Congruence.Hom
public import MinimalPrimes.GroupTheory.Congruence.MonoidWithZero
public import MinimalPrimes.Order.Filter.Product.Nontrivial

/-!
# Algebra on dependent reduced products

The carrier is Mathlib's `Filter.Product`: dependent total sections modulo eventual
equality. Without algebraic assumptions, `Filter.productSetoid_eq_iff` compares
the section relations of two filters by their restrictions to nontrivial fibres,
with a separate alternative for an empty total-section type. `Filter.productCon`
refines its exact setoid and descends multiplication,
unital multiplication, monoid and monoid-with-zero structures without additive
assumptions. The class of the pointwise one section needs only `One` on each fibre.
`Filter.Product.coeMulHom` is the canonical section homomorphism for `MulOneClass`
fibres. Use the existing `Con.mk'` and `Con.lift` APIs for the multiplicative quotient.

With addition, `Filter.productRingCon` extends this same congruence. The existing
`RingCon` quotient structures and universal property apply without a second quotient.
Use `RingCon.mk'`, `RingCon.mk'_surjective`, `RingCon.eq`, `RingCon.lift`,
`RingCon.lift_coe` and `RingCon.lift_unique` directly. In particular, the canonical
section map already has all the usual `RingHom.map_*` laws.

The construction allows arbitrary filters and independently universed fibres.
Principal filters give restriction to their generating set; ultrafilters give
pointwise inversion and division semirings. Properness alone does not imply
nontriviality when fibres may be trivial. No semiring ideal-quotient identification
is involved.

## References

The carrier, quotient operations and universal property reuse Mathlib's
`Order.Filter.Germ.Basic` and `RingTheory.Congruence` interfaces. The ultrafilter
argument generalizes the pointwise inversion argument in Mathlib's
`Order.Filter.FilterProduct`, originally by Abhimanyu Pallavi Sudhir and Yury
Kudryashov. The constant-family construction remains the existing `Filter.Germ`.
The multiplicative quotient construction follows Amelia Livingston's `Con`
formalization and Johan Commelin's surjective transports. Pointwise section data
reuse the Pi formalization by Simon Hudon, Patrick Massot and Eric Wieser.
-/

@[expose] public section

open Filter

universe u v w z

namespace Filter

variable {ι : Type u}

/-- The dependent-product relation is eventual equality of sections,
without algebraic assumptions. -/
@[simp]
theorem productSetoid_apply (F : Filter ι) (K : ι → Type v) (f g : ∀ i, K i) :
    productSetoid F K f g ↔ ∀ᶠ i in F, f i = g i := Iff.rfl

/-- The section setoids of two filters agree exactly when there is no total
section or the filters agree on the nontrivial fibres. No algebraic structure or
inhabitation hypothesis is required. -/
theorem productSetoid_eq_iff {R : ι → Type v} (F G : Filter ι) :
    productSetoid F R = productSetoid G R ↔
      IsEmpty (∀ i, R i) ∨
        F ⊓ principal {i | Nontrivial (R i)} = G ⊓ principal {i | Nontrivial (R i)} := by
  have hrel : productSetoid F R = productSetoid G R ↔
      ∀ f g : (∀ i, R i), (∀ᶠ i in F, f i = g i) ↔ (∀ᶠ i in G, f i = g i) := by
    constructor
    · intro h f g
      have hfg : productSetoid F R f g ↔ productSetoid G R f g := by rw [h]
      simpa only [productSetoid_apply] using hfg
    · intro h
      exact Setoid.ext fun f g => by simpa only [productSetoid_apply] using h f g
  exact hrel.trans (by
    simpa only [nontrivial_iff] using (forall_eventually_eq_iff (R := R) F G))

/-- Eventual equality of dependent sections is a multiplicative congruence. -/
abbrev productCon (F : Filter ι) (K : ι → Type v) [∀ i, Mul (K i)] :
    Con (∀ i, K i) where
  toSetoid := productSetoid F K
  mul' := fun hfg hkl => (hfg.and hkl).mono fun _ h => congrArg₂ (· * ·) h.1 h.2

/-- The multiplicative congruence uses the existing dependent-product setoid. -/
@[simp]
theorem productCon_toSetoid (F : Filter ι) (K : ι → Type v) [∀ i, Mul (K i)] :
    (productCon F K).toSetoid = productSetoid F K := rfl

/-- The multiplicative congruence relates exactly the eventually equal sections. -/
theorem productCon_apply (F : Filter ι) (K : ι → Type v) [∀ i, Mul (K i)]
    (f g : ∀ i, K i) :
    productCon F K f g ↔ ∀ᶠ i in F, f i = g i := Iff.rfl

/-- Eventual equality of dependent sections is an additive and multiplicative congruence. -/
def productRingCon (F : Filter ι) (K : ι → Type v) [∀ i, Add (K i)] [∀ i, Mul (K i)] :
    RingCon (∀ i, K i) where
  toCon := productCon F K
  add' := fun hfg hkl => (hfg.and hkl).mono fun _ h => congrArg₂ (· + ·) h.1 h.2

/-- The congruence uses exactly the existing dependent-product setoid. -/
@[simp]
theorem productRingCon_toSetoid (F : Filter ι) (K : ι → Type v)
    [∀ i, Add (K i)] [∀ i, Mul (K i)] :
    (productRingCon F K).toSetoid = productSetoid F K := rfl

/-- The relation of the congruence is eventual equality, with no algebraic side conditions. -/
@[simp]
theorem productRingCon_apply (F : Filter ι) (K : ι → Type v)
    [∀ i, Add (K i)] [∀ i, Mul (K i)] (f g : ∀ i, K i) :
    productRingCon F K f g ↔ ∀ᶠ i in F, f i = g i := Iff.rfl

namespace Product

variable {F : Filter ι} {K : ι → Type v}

/-- Two sections have the same class precisely when they are eventually equal. -/
theorem coe_eq (f g : ∀ i, K i) :
    (f : F.Product K) = (g : F.Product K) ↔ ∀ᶠ i in F, f i = g i := by
  simp only [Quotient.eq', productSetoid_apply]

/-- Pointwise multiplication descends on the dependent-product carrier. -/
instance instMul [∀ i, Mul (K i)] : Mul (F.Product K) :=
  Con.hasMul (productCon F K)

/-- The pointwise section with value one represents one in the dependent product. -/
instance instOne [∀ i, One (K i)] : One (F.Product K) where
  one := ((1 : ∀ i, K i) : F.Product K)

/-- Pointwise multiplication with a two-sided unit descends on the dependent-product carrier. -/
instance instMulOneClass [∀ i, MulOneClass (K i)] : MulOneClass (F.Product K) :=
  Con.mulOneClass (productCon F K)

/-- Pointwise monoid operations descend on the dependent-product carrier. -/
instance instMonoid [∀ i, Monoid (K i)] : Monoid (F.Product K) :=
  Con.monoid (productCon F K)

/-- Pointwise monoid-with-zero operations descend on the dependent-product carrier. -/
instance instMonoidWithZero [∀ i, MonoidWithZero (K i)] : MonoidWithZero (F.Product K) :=
  Con.monoidWithZero (productCon F K)

/-- The canonical projection from sections to the reduced product preserves multiplication
and one. -/
def coeMulHom (F : Filter ι) [∀ i, MulOneClass (K i)] : (∀ i, K i) →* F.Product K :=
  (productCon F K).mk'

/-- The section homomorphism is the existing coefficient projection. -/
@[simp]
theorem coeMulHom_apply [∀ i, MulOneClass (K i)] (f : ∀ i, K i) :
    coeMulHom F f = (f : F.Product K) := rfl

/-- The constant section with value one represents one. -/
@[simp]
theorem coe_one [∀ i, One (K i)] :
    ((1 : ∀ i, K i) : F.Product K) = (1 : F.Product K) := rfl

/-- Multiplication of representatives is pointwise multiplication. -/
@[simp]
theorem coe_mul [∀ i, Mul (K i)] (f g : ∀ i, K i) :
    ((f * g : ∀ i, K i) : F.Product K) =
      ((· * ·) : F.Product K → F.Product K → F.Product K)
        (f : F.Product K) (g : F.Product K) := rfl

/-- Natural powers of representatives are pointwise powers. -/
@[simp]
theorem coe_pow [∀ i, Monoid (K i)] (f : ∀ i, K i) (n : ℕ) :
    ((f ^ n : ∀ i, K i) : F.Product K) =
      ((· ^ ·) : F.Product K → ℕ → F.Product K) (f : F.Product K) n := rfl

/-- The constant section with value zero represents zero. -/
@[simp]
theorem coe_zero [∀ i, MonoidWithZero (K i)] :
    ((0 : ∀ i, K i) : F.Product K) = (0 : F.Product K) := rfl

/-- An eventual-equality-invariant homomorphism preserving multiplication and one factors
uniquely through the dependent filter product. -/
theorem existsUnique_monoidHom [∀ i, MulOneClass (K i)] {P : Type w} [MulOneClass P]
    (h : (∀ i, K i) →* P)
    (hh : ∀ {f g : ∀ i, K i}, (∀ᶠ i in F, f i = g i) → h f = h g) :
    ∃! g : F.Product K →* P, g.comp (coeMulHom F) = h := by
  have hker : productCon F K ≤ Con.ker h := by
    intro f g hfg
    exact (Con.ker_apply (f := h)).2 (hh ((productCon_apply F K f g).1 hfg))
  refine ⟨Con.lift (productCon F K) h hker, ?_, ?_⟩
  · exact Con.lift_comp_mk' hker
  · intro g hg
    apply Con.hom_ext (c := productCon F K)
    exact hg.trans (Con.lift_comp_mk' (c := productCon F K) (f := h) hker).symm

/-- Pointwise semiring operations descend on the existing dependent-product carrier. -/
instance instSemiring [∀ i, Semiring (K i)] : Semiring (F.Product K) :=
  inferInstanceAs (Semiring (productRingCon F K).Quotient)

/-- Commutative fibres give the corresponding commutative reduced product. -/
instance instCommSemiring [∀ i, CommSemiring (K i)] : CommSemiring (F.Product K) :=
  inferInstanceAs (CommSemiring (productRingCon F K).Quotient)

/-- With semiring fibres, the section monoid homomorphism is the multiplicative part
of the section ring homomorphism. -/
theorem coeMulHom_eq_mk'_toMonoidHom [∀ i, Semiring (K i)] :
    coeMulHom F = (productRingCon F K).mk'.toMonoidHom := rfl

/-- A section represents zero precisely when its zero set belongs to the filter. -/
@[simp]
theorem coe_eq_zero [∀ i, Semiring (K i)] (f : ∀ i, K i) :
    (f : F.Product K) = (0 : F.Product K) ↔ {i | f i = 0} ∈ F := by
  change (f : F.Product K) = ((0 : ∀ i, K i) : F.Product K) ↔ _
  exact Quotient.eq''

/-- The reduced product is trivial exactly when the filter concentrates on trivial fibres. -/
theorem subsingleton_iff [∀ i, Semiring (K i)] :
    Subsingleton (F.Product K) ↔ {i | (0 : K i) = 1} ∈ F := by
  rw [subsingleton_iff_of_nonempty (F := F) (K := K) ⟨0⟩]
  constructor
  · intro h
    exact h.mono fun i hi => @Subsingleton.elim (K i) hi 0 1
  · intro h
    exact Filter.Eventually.mono h fun _ hi => subsingleton_of_zero_eq_one hi

/-- The improper filter gives a trivial semiring, including for an empty index type. -/
instance instSubsingletonBot [∀ i, Semiring (K i)] :
    Subsingleton ((⊥ : Filter ι).Product K) :=
  (subsingleton_iff (F := ⊥) (K := K)).2 (by simp)

/-- The top-filter section map is bijective, including for an empty index type.
The semiring comparison is obtained directly with `RingEquiv.ofBijective`. -/
theorem mk'_top_bijective [∀ i, Semiring (K i)] :
    Function.Bijective (productRingCon (⊤ : Filter ι) K).mk' := by
  refine ⟨?_, (productRingCon (⊤ : Filter ι) K).mk'_surjective⟩
  intro f g h
  have h' : {i | f i = g i} ∈ (⊤ : Filter ι) :=
    (productRingCon (⊤ : Filter ι) K).eq.1 h
  exact funext (Filter.mem_top_iff_forall.1 h')

/-- Properness and nontriviality of every fibre imply nontriviality of the quotient. -/
instance instNontrivial [∀ i, Semiring (K i)] [∀ i, Nontrivial (K i)] [NeBot F] :
    Nontrivial (F.Product K) := by
  apply not_subsingleton_iff_nontrivial.mp
  intro h
  obtain ⟨i, hi⟩ := Filter.Eventually.exists
    ((subsingleton_iff (F := F) (K := K)).mp h)
  exact zero_ne_one hi

/-- Pointwise inversion respects eventual equality for every filter. -/
instance instInv [∀ i, Inv (K i)] : Inv (F.Product K) where
  inv := Quotient.map' (fun f i => (f i)⁻¹)
    (fun _ _ h => h.mono fun _ hi => congrArg Inv.inv hi)

/-- Inversion on representatives is pointwise inversion. -/
@[simp]
theorem coe_inv [∀ i, Inv (K i)] (f : ∀ i, K i) :
    ((fun i => (f i)⁻¹) : F.Product K) =
      (Inv.inv : F.Product K → F.Product K) (f : F.Product K) := rfl

section Map

variable {L : ι → Type w} {M : ι → Type z}
variable [∀ i, Semiring (K i)] [∀ i, Semiring (L i)] [∀ i, Semiring (M i)]

/-- Fibrewise homomorphisms induce a homomorphism of dependent reduced products. -/
def mapRingHom (F : Filter ι) (φ : ∀ i, K i →+* L i) : F.Product K →+* F.Product L :=
  (productRingCon F K).lift
    ((productRingCon F L).mk'.comp
      (RingHom.pi fun i => (φ i).comp (Pi.evalRingHom K i)))
    (fun _ _ h => Quotient.sound (h.mono fun i hi => congrArg (φ i) hi))

/-- The induced homomorphism applies the given homomorphism in each fibre. -/
@[simp]
theorem mapRingHom_coe (φ : ∀ i, K i →+* L i) (f : ∀ i, K i) :
    mapRingHom F φ (f : F.Product K) = ((fun i => φ i (f i)) : F.Product L) := rfl

/-- Identity fibre maps induce the identity on the quotient. -/
@[simp]
theorem mapRingHom_id :
    mapRingHom F (fun i => RingHom.id (K i)) = RingHom.id (F.Product K) := by
  apply RingCon.Quotient.hom_ext (c := productRingCon F K)
  ext f
  rfl

/-- Induced maps preserve composition of fibrewise homomorphisms. -/
theorem mapRingHom_comp (ψ : ∀ i, L i →+* M i) (φ : ∀ i, K i →+* L i) :
    (mapRingHom F ψ).comp (mapRingHom F φ) =
      mapRingHom F (fun i => (ψ i).comp (φ i)) := by
  apply RingCon.Quotient.hom_ext (c := productRingCon F K)
  ext f
  rfl

end Map

section Principal

variable [∀ i, Semiring (K i)]

/-- Restriction identifies the principal reduced product with sections on the generating set.
The restriction homomorphism is unital; extension by zero is used only for surjectivity. -/
noncomputable def principalRingEquiv (s : Set ι) :
    (principal s).Product K ≃+* (∀ i : s, K i.1) :=
  let restriction : (∀ i, K i) →+* (∀ i : s, K i.1) :=
    RingHom.pi fun i : s => Pi.evalRingHom K i.1
  let descended := (productRingCon (principal s) K).lift restriction
    (fun _ _ h => funext fun i : s => h i.2)
  RingEquiv.ofBijective descended (RingCon.lift_bijective_iff.2 ⟨by
    refine RingCon.ext fun f g => ?_
    constructor
    · intro h
      exact funext fun i : s => h i.2
    · intro h i hi
      exact congrFun h ⟨i, hi⟩, by
    intro g
    classical
    refine ⟨fun i => if hi : i ∈ s then g ⟨i, hi⟩ else 0, ?_⟩
    funext i
    exact dite_eq_left i.2⟩)

/-- The principal-filter equivalence is restriction on every representative. -/
@[simp]
theorem principalRingEquiv_coe (s : Set ι) (f : ∀ i, K i) :
    principalRingEquiv (K := K) s (f : (principal s).Product K) = fun i : s => f i.1 := rfl

end Principal

section Ultrafilter

variable (U : Ultrafilter ι)

/-- An ultrafilter reduced product of division semirings is a division semiring. -/
instance instDivisionSemiring [∀ i, DivisionSemiring (K i)] :
    DivisionSemiring ((U : Filter ι).Product K) where
  toSemiring := instSemiring
  toNontrivial := instNontrivial
  inv := Inv.inv
  inv_zero := by
    change ((fun i => (0 : K i)⁻¹) : (U : Filter ι).Product K) =
      ((0 : ∀ i, K i) : (U : Filter ι).Product K)
    exact Quotient.sound (Eventually.of_forall fun _ => inv_zero)
  mul_inv_cancel x := by
    refine Quotient.inductionOn' x ?_
    intro f hf
    change ((fun i => f i * (f i)⁻¹) : (U : Filter ι).Product K) =
      ((1 : ∀ i, K i) : (U : Filter ι).Product K)
    apply Quotient.sound
    rcases U.em (fun i => f i = 0) with h | h
    · exact (hf ((coe_eq_zero f).2 h)).elim
    · exact h.mono fun _ hi => mul_inv_cancel₀ hi
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl

/-- An ultrafilter reduced product of semifields is a semifield. -/
instance instSemifield [∀ i, Semifield (K i)] : Semifield ((U : Filter ι).Product K) where
  __ := instCommSemiring
  __ := instDivisionSemiring U

end Ultrafilter

end Product

/-- On constant families the section monoid homomorphism is the existing germ homomorphism. -/
theorem productCon_mk'_eq_coeMulHom (F : Filter ι) (R : Type v) [Monoid R] :
    (productCon F (fun _ : ι => R)).mk' = Germ.coeMulHom F := rfl

/-- On constant families the section homomorphism is the existing germ homomorphism. -/
theorem productRingCon_mk'_eq_coeRingHom (F : Filter ι) (R : Type v) [Semiring R] :
    (productRingCon F (fun _ : ι => R)).mk' = Germ.coeRingHom F := rfl

end Filter
