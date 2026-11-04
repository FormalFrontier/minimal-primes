/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Exact.Basic
public import MinimalPrimes.Order.Filter.Product.Module

/-!
# Exactness of dependent reduced-product maps

For arbitrary fibre functions, `Filter.Product.map_exact_iff` identifies exactness
of the two existing coordinate maps with eventual exactness of the whole fibre
pair. Only the target fibres need zero records. The target product zero is the
existing point `Filter.Product.zeroPoint`, supplied explicitly as the zero field
of the argument to `Function.Exact`; no product zero instance is installed.

A total source section is essential, even if the empty source fibre would be
ignored by the filter. The hypothesis is `Nonempty` of the total section type,
not a choice of public section data or an extra assumption on the middle family.
A source section maps to a middle section. No preservation of zero, addition or
scalar action is required of either function.

`Filter.Product.map_exact_iff_of_addZeroClass` uses the existing named additive
product zero instead, for arbitrary functions and only target `AddZeroClass`
records. `Filter.Product.zeroPoint_eq_zero_add` aligns the target point with this
zero. In particular, given fibre linear maps can be used through their existing
function coercions: source zeros supply a total section, and the target zero is
inherited from the given additive reduced-product record. All given scalar,
additive and module records stay fixed, even when their carrier types coincide.
No bundled linear map on products is needed.

For constant families, the existing `Filter.Product.map_const_eq_germ_map` and
`Filter.Product.zeroPoint_eq_germ_zero` identify both maps and the selected target
zero with Mathlib's germ maps and germ zero. Bottom filters and empty indices are
included whenever the source section type is nonempty.

## References

This interface uses Antoine Chambert-Loir's `Function.Exact` in Mathlib, the
existing dependent coordinate maps and section coercions, and the additive
reduced-product record and its representative-zero equation. The constant-family
comparisons use Mathlib's filter-germ interfaces.
-/

@[expose] public section

universe u v w z

namespace Filter.Product

variable {ι : Type u} (F : Filter ι)

private theorem coe_mem_range_map_iff
    {X : ι → Type v} {Y : ι → Type w}
    (f : ∀ i, X i → Y i) (a : ∀ i, X i) (y : ∀ i, Y i) :
    (y : F.Product Y) ∈ Set.range (map F f) ↔
      ∀ᶠ i in F, y i ∈ Set.range (f i) := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨s, rfl⟩ := coe_surjective F X x
    exact ((coe_eq (F := F) _ _).1 ((map_coe F f s).symm.trans hx)).mono
      fun i hi => ⟨s i, hi⟩
  · intro h
    have : ∀ i, Nonempty (X i) := fun i => ⟨a i⟩
    obtain ⟨x, hx⟩ :=
      (Filter.skolem (α := X) (P := fun i x => f i x = y i) (F := F)).1 h
    exact ⟨(x : F.Product X), (map_coe F f x).trans
      ((coe_eq (F := F) _ _).2 hx)⟩

private theorem map_coe_eq_zeroPoint_iff
    {Y : ι → Type w} {Z : ι → Type z} [∀ i, Zero (Z i)]
    (g : ∀ i, Y i → Z i) (y : ∀ i, Y i) :
    map F g (y : F.Product Y) = zeroPoint F Z ↔ ∀ᶠ i in F, g i (y i) = 0 := by
  constructor
  · intro h
    exact (coe_eq_zeroPoint_iff F _).1 ((map_coe F g y).symm.trans h)
  · intro h
    exact (map_coe F g y).trans ((coe_eq_zeroPoint_iff F _).2 h)

/-- The existing coordinate maps form an exact pair exactly when the whole fibre
pair is exact on a filter-large set. The target zero is the represented section
of the given fibre zeros. A total source section is required; neither function
has to preserve zero. -/
theorem map_exact_iff {X : ι → Type v} {Y : ι → Type w} {Z : ι → Type z}
    [∀ i, Zero (Z i)] [Nonempty (∀ i, X i)]
    (f : ∀ i, X i → Y i) (g : ∀ i, Y i → Z i) :
    @Function.Exact (F.Product X) (F.Product Y) (F.Product Z)
      (map F f) (map F g) ⟨zeroPoint F Z⟩ ↔
      ∀ᶠ i in F, Function.Exact (f i) (g i) := by
  classical
  obtain ⟨a⟩ := ‹Nonempty (∀ i, X i)›
  constructor
  · intro h
    have hprod : ∀ y : F.Product Y,
        map F g y = zeroPoint F Z ↔ y ∈ Set.range (map F f) := h
    have hcomp : ∀ᶠ i in F, ∀ x : X i, g i (f i x) = 0 := by
      apply (Filter.eventually_forall_iff_forall_section
        (D := F) (P := fun i x => g i (f i x) = 0) a).2
      intro x
      exact (map_coe_eq_zeroPoint_iff F g (fun i => f i (x i))).1
        ((hprod _).2 ⟨(x : F.Product X), map_coe F f x⟩)
    have hker : ∀ᶠ i in F,
        ∀ y : Y i, g i y = 0 → y ∈ Set.range (f i) := by
      apply (Filter.eventually_forall_iff_forall_section
        (D := F) (P := fun i y => g i y = 0 → y ∈ Set.range (f i))
        (fun i => f i (a i))).2
      intro y
      -- The image of the source fallback is in the kernel on the whole-source locus.
      let y' : ∀ i, Y i := fun i => if g i (y i) = 0 then y i else f i (a i)
      have hgy' : map F g (y' : F.Product Y) = zeroPoint F Z := by
        apply (map_coe_eq_zeroPoint_iff F g y').2
        exact hcomp.mono fun i hi => by
          by_cases he : g i (y i) = 0
          · simpa only [y', ite_eq_left he] using he
          · simpa only [y', ite_eq_right he] using hi (a i)
      have hr : ∀ᶠ i in F, y' i ∈ Set.range (f i) :=
        (coe_mem_range_map_iff F f a y').1 ((hprod _).1 hgy')
      exact hr.mono fun i hi he => by
        simpa only [y', ite_eq_left he] using hi
    exact (hcomp.and hker).mono fun i hi => by
      intro y
      constructor
      · exact hi.2 y
      · rintro ⟨x, rfl⟩
        exact hi.1 x
  · intro h y
    obtain ⟨y, rfl⟩ := coe_surjective F Y y
    exact (map_coe_eq_zeroPoint_iff F g y).trans
      ((Filter.eventually_congr (h.mono fun i hi => hi (y i))).trans
        (coe_mem_range_map_iff F f a y).symm)

/-- The exactness criterion with the existing named additive product zero.
Only the target fibres need additive zero classes; the functions are arbitrary.
`zeroPoint_eq_zero_add` identifies this zero with the target point of
`map_exact_iff`. In semimodule applications the given source zeros supply the
total source section, without an extra inhabitation hypothesis. -/
theorem map_exact_iff_of_addZeroClass
    {X : ι → Type v} {Y : ι → Type w} {Z : ι → Type z}
    [aZ : ∀ i, AddZeroClass (Z i)] [Nonempty (∀ i, X i)]
    (f : ∀ i, X i → Y i) (g : ∀ i, Y i → Z i) :
    @Function.Exact (F.Product X) (F.Product Y) (F.Product Z)
      (map F f) (map F g) (@zero ι F Z aZ) ↔
      ∀ᶠ i in F, Function.Exact (f i) (g i) := by
  have hz : (⟨zeroPoint F Z⟩ : Zero (F.Product Z)) = @zero ι F Z aZ :=
    congrArg (fun z : F.Product Z => (⟨z⟩ : Zero (F.Product Z)))
      (@zeroPoint_eq_zero_add ι F Z aZ)
  exact hz ▸ map_exact_iff F f g

end Filter.Product
