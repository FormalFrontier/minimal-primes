/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Sets.Closeds
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.NhdsWithin

/-!
# Irreducible closed subsets of topological products

Products of irreducible sets are irreducible. Conversely, the closure of an irreducible
subset of an arbitrary dependent product is the rectangle of the closures of its
coordinate images. For a binary product the latter result holds for preirreducible
subsets as well, including the empty set.

The canonical products on `TopologicalSpace.IrreducibleCloseds` have set-product and
`Set.pi Set.univ` carriers. Projection followed by closure gives order isomorphisms
from the irreducible closed subsets of a product to the product of the factor orders.
All spaces keep their given topologies; the products carry the usual product topologies.
The dependent-product classification and order isomorphism allow arbitrary index types.

## References

* Mathlib's `Mathlib.Topology.Irreducible`, by Johannes Hölzl, Mario Carneiro and
  Yury Kudryashov, for irreducible sets, images, closures and finite intersections of opens.
* Mathlib's `Mathlib.Topology.Sets.Closeds`, by Floris van Doorn and Yaël Dillies,
  for irreducible closed subsets, their inclusion order and their continuous-image maps.
* Mathlib's product topology, set-product, coordinate-image and closure-of-product APIs.
-/

@[expose] public section

universe u v w

open Set

section Sets

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- The product of two preirreducible sets is preirreducible. -/
theorem IsPreirreducible.prod {A : Set X} {B : Set Y}
    (hA : IsPreirreducible A) (hB : IsPreirreducible B) :
    IsPreirreducible (A ×ˢ B) := by
  rintro U V hU hV ⟨p, hp, hpU⟩ ⟨q, hq, hqV⟩
  obtain ⟨U₁, U₂, hU₁, hU₂, hp₁, hp₂, hUV⟩ :=
    isOpen_prod_iff.mp hU p.1 p.2 hpU
  obtain ⟨V₁, V₂, hV₁, hV₂, hq₁, hq₂, hVV⟩ :=
    isOpen_prod_iff.mp hV q.1 q.2 hqV
  obtain ⟨x, hx, hxU, hxV⟩ := hA U₁ V₁ hU₁ hV₁ ⟨p.1, hp.1, hp₁⟩
    ⟨q.1, hq.1, hq₁⟩
  obtain ⟨y, hy, hyU, hyV⟩ := hB U₂ V₂ hU₂ hV₂ ⟨p.2, hp.2, hp₂⟩
    ⟨q.2, hq.2, hq₂⟩
  exact ⟨(x, y), ⟨hx, hy⟩, hUV ⟨hxU, hyU⟩, hVV ⟨hxV, hyV⟩⟩

/-- The product of two irreducible sets is irreducible. -/
theorem IsIrreducible.prod {A : Set X} {B : Set Y}
    (hA : IsIrreducible A) (hB : IsIrreducible B) :
    IsIrreducible (A ×ˢ B) := by
  exact ⟨hA.nonempty.prod hB.nonempty, hA.isPreirreducible.prod hB.isPreirreducible⟩

/-- The closure of a preirreducible subset of a binary product is the product of the
closures of its two projection images. The subset may be empty. -/
theorem IsPreirreducible.closure_eq_prod {S : Set (X × Y)}
    (hS : IsPreirreducible S) :
    closure S = closure (Prod.fst '' S) ×ˢ closure (Prod.snd '' S) := by
  apply Subset.antisymm
  · exact closure_minimal
      (fun p hp => ⟨subset_closure ⟨p, hp, rfl⟩, subset_closure ⟨p, hp, rfl⟩⟩)
      (isClosed_closure.prod isClosed_closure)
  · intro p hp
    apply mem_closure_iff.mpr
    intro U hU hpU
    obtain ⟨U₁, U₂, hU₁, hU₂, hp₁, hp₂, hUV⟩ :=
      isOpen_prod_iff.mp hU p.1 p.2 hpU
    obtain ⟨_, hxU, q, hq, rfl⟩ := mem_closure_iff.mp hp.1 U₁ hU₁ hp₁
    obtain ⟨_, hyU, r, hr, rfl⟩ := mem_closure_iff.mp hp.2 U₂ hU₂ hp₂
    obtain ⟨z, hz, hz₁, hz₂⟩ := hS (Prod.fst ⁻¹' U₁) (Prod.snd ⁻¹' U₂)
      (hU₁.preimage continuous_fst) (hU₂.preimage continuous_snd)
      ⟨q, hq, hxU⟩ ⟨r, hr, hyU⟩
    exact ⟨z, hUV ⟨hz₁, hz₂⟩, hz⟩

variable {ι : Type w} {Z : ι → Type u} [∀ i, TopologicalSpace (Z i)]

/-- An arbitrary dependent product of preirreducible sets is preirreducible. -/
theorem IsPreirreducible.pi {A : ∀ i, Set (Z i)}
    (hA : ∀ i, IsPreirreducible (A i)) :
    IsPreirreducible (Set.pi Set.univ A) := by
  classical
  rintro U V hU hV ⟨f, hf, hfU⟩ ⟨g, hg, hgV⟩
  obtain ⟨I, B, hB, hBU⟩ := isOpen_pi_iff.mp hU f hfU
  obtain ⟨J, C, hC, hCV⟩ := isOpen_pi_iff.mp hV g hgV
  let B' : ∀ i, Set (Z i) := fun i => if i ∈ I then B i else univ
  let C' : ∀ i, Set (Z i) := fun i => if i ∈ J then C i else univ
  have hB' : ∀ i, IsOpen (B' i) ∧ f i ∈ B' i := by
    intro i
    dsimp [B']
    split_ifs with hi
    · exact hB i hi
    · exact ⟨isOpen_univ, mem_univ _⟩
  have hC' : ∀ i, IsOpen (C' i) ∧ g i ∈ C' i := by
    intro i
    dsimp [C']
    split_ifs with hi
    · exact hC i hi
    · exact ⟨isOpen_univ, mem_univ _⟩
  have hcoord : ∀ i, (A i ∩ (B' i ∩ C' i)).Nonempty := fun i =>
    hA i (B' i) (C' i) (hB' i).1 (hC' i).1
      ⟨f i, hf i (mem_univ i), (hB' i).2⟩
      ⟨g i, hg i (mem_univ i), (hC' i).2⟩
  obtain ⟨z, hz⟩ := univ_pi_nonempty_iff.mpr hcoord
  refine ⟨z, ?_, hBU ?_, hCV ?_⟩
  · intro i _
    exact (hz i (mem_univ i)).1
  · intro i hi
    have hi' : i ∈ I := hi
    have hzi := (hz i (mem_univ i)).2.1
    simpa [B', hi'] using hzi
  · intro i hi
    have hi' : i ∈ J := hi
    have hzi := (hz i (mem_univ i)).2.2
    simpa [C', hi'] using hzi

/-- An arbitrary dependent product of irreducible sets is irreducible, including an
empty-index product. Nonemptiness comes from the factor sets. -/
theorem IsIrreducible.pi {A : ∀ i, Set (Z i)}
    (hA : ∀ i, IsIrreducible (A i)) :
    IsIrreducible (Set.pi Set.univ A) := by
  exact ⟨univ_pi_nonempty_iff.mpr (fun i => (hA i).nonempty),
    IsPreirreducible.pi (fun i => (hA i).isPreirreducible)⟩

/-- The closure of an irreducible subset of an arbitrary dependent product is the
rectangle of the closures of its coordinate images.

Irreducibility, rather than just preirreducibility, includes the nonemptiness needed
when the index type is empty. -/
theorem IsIrreducible.closure_eq_pi {S : Set (∀ i, Z i)} (hS : IsIrreducible S) :
    closure S = Set.pi Set.univ (fun i => closure (Function.eval i '' S)) := by
  classical
  apply Subset.antisymm
  · exact closure_minimal (fun f hf i _ => subset_closure ⟨f, hf, rfl⟩)
      (isClosed_set_pi fun i _ => isClosed_closure)
  · intro p hp
    apply mem_closure_iff.mpr
    intro U hU hpU
    obtain ⟨I, B, hB, hBU⟩ := isOpen_pi_iff.mp hU p hpU
    let C : ι → Set (∀ i, Z i) := fun i => Function.eval i ⁻¹' B i
    have hCopen : ∀ V ∈ I.image C, IsOpen V := by
      intro V hV
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hV
      exact (hB i hi).1.preimage (continuous_apply i)
    have hCmeet : ∀ V ∈ I.image C, (S ∩ V).Nonempty := by
      intro V hV
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hV
      obtain ⟨_, hxB, q, hq, rfl⟩ := mem_closure_iff.mp (hp i (mem_univ i))
        (B i) (hB i hi).1 (hB i hi).2
      exact ⟨q, hq, hxB⟩
    obtain ⟨q, hq, hqC⟩ := isIrreducible_iff_sInter.mp hS (I.image C) hCopen hCmeet
    refine ⟨q, hBU ?_, hq⟩
    intro i hi
    exact mem_sInter.mp hqC (C i) (Finset.mem_image.mpr ⟨i, hi, rfl⟩)

end Sets

namespace TopologicalSpace.IrreducibleCloseds

section Prod

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- The product of irreducible closed subsets has the set product as its carrier. -/
instance instSProd : SProd (IrreducibleCloseds X) (IrreducibleCloseds Y)
    (IrreducibleCloseds (X × Y)) where
  sprod A B :=
    { carrier := (A : Set X) ×ˢ (B : Set Y)
      isIrreducible' := A.isIrreducible.prod B.isIrreducible
      isClosed' := A.isClosed.prod B.isClosed }

/-- Coercion of a product of irreducible closed subsets is the set product. -/
@[simp]
theorem coe_prod (A : IrreducibleCloseds X) (B : IrreducibleCloseds Y) :
    ((A ×ˢ B : IrreducibleCloseds (X × Y)) : Set (X × Y)) =
      (A : Set X) ×ˢ (B : Set Y) := rfl

/-- Membership in a product of irreducible closed subsets is coordinatewise. -/
@[simp]
theorem mem_prod {A : IrreducibleCloseds X} {B : IrreducibleCloseds Y} {p : X × Y} :
    p ∈ (A ×ˢ B : IrreducibleCloseds (X × Y)) ↔ p.1 ∈ A ∧ p.2 ∈ B := Iff.rfl

/-- Products of irreducible closed subsets are monotone in both factors. -/
theorem prod_mono {A A' : IrreducibleCloseds X} {B B' : IrreducibleCloseds Y}
    (hA : A ≤ A') (hB : B ≤ B') :
    (A ×ˢ B : IrreducibleCloseds (X × Y)) ≤ A' ×ˢ B' := by
  exact Set.prod_mono hA hB

/-- Inclusion between products of irreducible closed subsets is coordinatewise. -/
@[simp]
theorem prod_le_prod_iff {A A' : IrreducibleCloseds X} {B B' : IrreducibleCloseds Y} :
    (A ×ˢ B : IrreducibleCloseds (X × Y)) ≤ A' ×ˢ B' ↔ A ≤ A' ∧ B ≤ B' := by
  exact Set.prod_subset_prod_iff'
    (Set.prod_nonempty_iff.mpr ⟨A.isIrreducible.nonempty, B.isIrreducible.nonempty⟩)

/-- The first projection followed by closure recovers the first factor. -/
@[simp]
theorem map_fst_prod (A : IrreducibleCloseds X) (B : IrreducibleCloseds Y) :
    map Prod.fst continuous_fst (A ×ˢ B) = A := by
  apply IrreducibleCloseds.ext
  rw [coe_map, coe_prod, Set.fst_image_prod _ B.isIrreducible.nonempty,
    A.isClosed.closure_eq]

/-- The second projection followed by closure recovers the second factor. -/
@[simp]
theorem map_snd_prod (A : IrreducibleCloseds X) (B : IrreducibleCloseds Y) :
    map Prod.snd continuous_snd (A ×ˢ B) = B := by
  apply IrreducibleCloseds.ext
  rw [coe_map, coe_prod, Set.snd_image_prod A.isIrreducible.nonempty _,
    B.isClosed.closure_eq]

/-- An irreducible closed subset of a binary product is reconstructed from its two
projection closures. -/
@[simp]
theorem prod_map_fst_map_snd (C : IrreducibleCloseds (X × Y)) :
    map Prod.fst continuous_fst C ×ˢ map Prod.snd continuous_snd C = C := by
  apply IrreducibleCloseds.ext
  rw [coe_prod, coe_map, coe_map,
    ← C.isIrreducible.isPreirreducible.closure_eq_prod, C.isClosed.closure_eq]

/-- Inclusion in a product of irreducible closed subsets is equivalent to inclusion
of each projection closure in its factor. -/
theorem le_prod_iff {C : IrreducibleCloseds (X × Y)}
    {A : IrreducibleCloseds X} {B : IrreducibleCloseds Y} :
    C ≤ A ×ˢ B ↔ map Prod.fst continuous_fst C ≤ A ∧
      map Prod.snd continuous_snd C ≤ B := by
  constructor
  · intro h
    exact ⟨by simpa only [map_fst_prod] using map_mono continuous_fst h,
      by simpa only [map_snd_prod] using map_mono continuous_snd h⟩
  · rintro ⟨hfst, hsnd⟩
    simpa only [prod_map_fst_map_snd] using prod_mono hfst hsnd

/-- Projection followed by closure identifies the irreducible closed subsets of the
binary product with the pointwise product of the two factor inclusion orders. -/
def prodOrderIso (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y] :
    IrreducibleCloseds (X × Y) ≃o IrreducibleCloseds X × IrreducibleCloseds Y where
  toFun C := (map Prod.fst continuous_fst C, map Prod.snd continuous_snd C)
  invFun AB := AB.1 ×ˢ AB.2
  left_inv := prod_map_fst_map_snd
  right_inv AB := Prod.ext (map_fst_prod AB.1 AB.2) (map_snd_prod AB.1 AB.2)
  map_rel_iff' := by
    intro A B
    constructor
    · intro h
      calc
        A = map Prod.fst continuous_fst A ×ˢ map Prod.snd continuous_snd A :=
          (prod_map_fst_map_snd A).symm
        _ ≤ map Prod.fst continuous_fst B ×ˢ map Prod.snd continuous_snd B :=
          prod_mono h.1 h.2
        _ = B := prod_map_fst_map_snd B
    · intro h
      exact ⟨map_mono continuous_fst h, map_mono continuous_snd h⟩

/-- The forward product order isomorphism is the pair of projection-closure maps. -/
@[simp]
theorem prodOrderIso_apply (C : IrreducibleCloseds (X × Y)) :
    prodOrderIso X Y C = (map Prod.fst continuous_fst C, map Prod.snd continuous_snd C) := rfl

/-- The inverse product order isomorphism forms the canonical product. -/
@[simp]
theorem prodOrderIso_symm_apply (AB : IrreducibleCloseds X × IrreducibleCloseds Y) :
    (prodOrderIso X Y).symm AB = AB.1 ×ˢ AB.2 := rfl

/-- The first forward carrier is the closure of the first projection image. -/
theorem coe_prodOrderIso_apply_fst (C : IrreducibleCloseds (X × Y)) :
    ((prodOrderIso X Y C).1 : Set X) = closure (Prod.fst '' (C : Set (X × Y))) := rfl

/-- The second forward carrier is the closure of the second projection image. -/
theorem coe_prodOrderIso_apply_snd (C : IrreducibleCloseds (X × Y)) :
    ((prodOrderIso X Y C).2 : Set Y) = closure (Prod.snd '' (C : Set (X × Y))) := rfl

/-- The inverse product order isomorphism has the set-product carrier. -/
theorem coe_prodOrderIso_symm_apply (AB : IrreducibleCloseds X × IrreducibleCloseds Y) :
    ((prodOrderIso X Y).symm AB : Set (X × Y)) =
      (AB.1 : Set X) ×ˢ (AB.2 : Set Y) := rfl

end Prod

section Pi

variable {ι : Type w} {Y : ι → Type u} [∀ i, TopologicalSpace (Y i)]

/-- The irreducible closed dependent product, with the coordinate rectangle as carrier. -/
def pi (A : ∀ i, IrreducibleCloseds (Y i)) : IrreducibleCloseds (∀ i, Y i) where
  carrier := Set.pi Set.univ (fun i => (A i : Set (Y i)))
  isIrreducible' := IsIrreducible.pi (fun i => (A i).isIrreducible)
  isClosed' := isClosed_set_pi (fun i _ => (A i).isClosed)

/-- Coercion of the irreducible closed dependent product is the set rectangle. -/
@[simp]
theorem coe_pi (A : ∀ i, IrreducibleCloseds (Y i)) :
    (pi A : Set (∀ i, Y i)) = Set.pi Set.univ (fun i => (A i : Set (Y i))) := rfl

/-- Membership in an irreducible closed dependent product is coordinatewise. -/
@[simp]
theorem mem_pi {A : ∀ i, IrreducibleCloseds (Y i)} {f : ∀ i, Y i} :
    f ∈ pi A ↔ ∀ i, f i ∈ A i := by
  exact Set.mem_univ_pi

/-- The irreducible closed dependent product is monotone in all its factors. -/
theorem pi_mono {A B : ∀ i, IrreducibleCloseds (Y i)} (h : ∀ i, A i ≤ B i) :
    pi A ≤ pi B := by
  exact Set.pi_mono (fun i _ => h i)

/-- Inclusion between irreducible closed dependent products is coordinatewise. -/
@[simp]
theorem pi_le_pi_iff {A B : ∀ i, IrreducibleCloseds (Y i)} :
    pi A ≤ pi B ↔ ∀ i, A i ≤ B i := by
  constructor
  · intro h i
    have himage : Function.eval i '' (pi A : Set (∀ i, Y i)) ⊆
        Function.eval i '' (pi B : Set (∀ i, Y i)) := Set.image_mono h
    exact SetLike.coe_subset_coe.mp (by
      simpa only [coe_pi, Set.eval_image_univ_pi (pi A).isIrreducible.nonempty,
        Set.eval_image_univ_pi (pi B).isIrreducible.nonempty] using himage)
  · exact pi_mono

/-- Evaluation followed by closure recovers the corresponding factor. -/
@[simp]
theorem map_eval_pi (A : ∀ i, IrreducibleCloseds (Y i)) (i : ι) :
    map (Function.eval i) (continuous_apply i) (pi A) = A i := by
  apply IrreducibleCloseds.ext
  rw [coe_map, coe_pi, Set.eval_image_univ_pi (pi A).isIrreducible.nonempty,
    (A i).isClosed.closure_eq]

/-- An irreducible closed subset of an arbitrary dependent product is reconstructed
from its evaluation closures. -/
@[simp]
theorem pi_map_eval (C : IrreducibleCloseds (∀ i, Y i)) :
    pi (fun i => map (Function.eval i) (continuous_apply i) C) = C := by
  apply IrreducibleCloseds.ext
  rw [coe_pi]
  simp only [coe_map]
  exact C.isIrreducible.closure_eq_pi.symm.trans C.isClosed.closure_eq

/-- Inclusion in an irreducible closed dependent product is equivalent to inclusion
of every evaluation closure in its factor. -/
theorem le_pi_iff {C : IrreducibleCloseds (∀ i, Y i)} {A : ∀ i, IrreducibleCloseds (Y i)} :
    C ≤ pi A ↔ ∀ i, map (Function.eval i) (continuous_apply i) C ≤ A i := by
  constructor
  · intro h i
    simpa only [map_eval_pi] using map_mono (continuous_apply i) h
  · intro h
    simpa only [pi_map_eval] using pi_mono h

/-- Evaluation followed by closure identifies the irreducible closed subsets of an
arbitrary dependent product with the pointwise product of the factor inclusion orders. -/
def piOrderIso (Y : ι → Type u) [∀ i, TopologicalSpace (Y i)] :
    IrreducibleCloseds (∀ i, Y i) ≃o (∀ i, IrreducibleCloseds (Y i)) where
  toFun C i := map (Function.eval i) (continuous_apply i) C
  invFun A := pi A
  left_inv := pi_map_eval
  right_inv A := funext (map_eval_pi A)
  map_rel_iff' := by
    intro A B
    constructor
    · intro h
      calc
        A = pi (fun i => map (Function.eval i) (continuous_apply i) A) := (pi_map_eval A).symm
        _ ≤ pi (fun i => map (Function.eval i) (continuous_apply i) B) := pi_mono h
        _ = B := pi_map_eval B
    · intro h i
      exact map_mono (continuous_apply i) h

/-- The forward dependent-product order isomorphism is evaluation followed by closure. -/
@[simp]
theorem piOrderIso_apply (C : IrreducibleCloseds (∀ i, Y i)) (i : ι) :
    piOrderIso Y C i = map (Function.eval i) (continuous_apply i) C := rfl

/-- The inverse dependent-product order isomorphism forms the canonical rectangle. -/
@[simp]
theorem piOrderIso_symm_apply (A : ∀ i, IrreducibleCloseds (Y i)) :
    (piOrderIso Y).symm A = pi A := rfl

/-- Each forward carrier is the closure of the corresponding evaluation image. -/
theorem coe_piOrderIso_apply (C : IrreducibleCloseds (∀ i, Y i)) (i : ι) :
    (piOrderIso Y C i : Set (Y i)) =
      closure (Function.eval i '' (C : Set (∀ i, Y i))) := rfl

/-- The inverse dependent-product order isomorphism has the set-rectangle carrier. -/
theorem coe_piOrderIso_symm_apply (A : ∀ i, IrreducibleCloseds (Y i)) :
    ((piOrderIso Y).symm A : Set (∀ i, Y i)) =
      Set.pi Set.univ (fun i => (A i : Set (Y i))) := rfl

end Pi

end TopologicalSpace.IrreducibleCloseds
