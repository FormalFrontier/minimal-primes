/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Data.Setoid.Basic
public import Mathlib.Logic.Equiv.Basic
public import MinimalPrimes.Order.Filter.Product

/-!
# Reindexing dependent filter products

A map tending from `F` to `G` pulls dependent sections over `G` back to sections
with fibres `R (u i)` over `F`. `Filter.Product.compTendsto` descends this operation
on Mathlib's existing quotient of total sections. Its representative equation,
identity and composition laws require no algebra, section-existence or properness
assumptions. On constant families it agrees with `Filter.Germ.compTendsto`.
Exact filter-image equality makes pullback injective, without injectivity of the
index map. An equivalence of indices makes pullback surjective with only the
forward convergence assumption; it need not be injective.

An equivalence of indices induces `Filter.Product.compTendstoEquiv` when both
it and its inverse tend to the respective filters. Its forward operation is the
same pullback. The inverse descends `Equiv.piCongrLeft`, including its dependent
transport along `e.apply_symm_apply`. One-way convergence guarantees surjectivity,
but does not in general suffice to descend this inverse to the quotient.

## References

The carrier, section coercion and constant-family operation reuse Mathlib's
`Order.Filter.Germ.Basic`, by Yury Kudryashov and Abhimanyu Pallavi Sudhir.
The descent uses Mathlib's quotient API. Injectivity reuses the complete kernel
criterion in `Data.Setoid.Basic`, by Amelia Livingston and Bryan Gin-ge Chen,
and `eventually_map` in `Order.Filter.Map`, by Johannes Hölzl and Jeremy Avigad.
Representative preimages and the inverse reuse the dependent Pi reindexing in
`Logic.Equiv.Basic`, by Leonardo de Moura and Mario Carneiro. This formalization
was developed with AI assistance.
-/

@[expose] public section

universe u v w z

namespace Filter.Product

variable {ι : Type u} {κ : Type v} {η : Type w}
variable {F : Filter ι} {G : Filter κ} {H : Filter η}
variable {R : κ → Type z}

/-- Pull a dependent filter product back along a map tending to its filter. -/
def compTendsto (x : G.Product R) (u : ι → κ) (hu : Tendsto u F G) :
    F.Product (fun i => R (u i)) :=
  Quotient.map' (fun f i => f (u i)) (fun _ _ h => hu.eventually h) x

/-- Pullback of a representative is precomposition of the section. -/
@[simp]
theorem coe_compTendsto (f : ∀ j, R j) (u : ι → κ) (hu : Tendsto u F G) :
    compTendsto (f : G.Product R) u hu =
      ((fun i => f (u i)) : F.Product (fun i => R (u i))) := rfl

/-- Pullback along the identity is the identity. -/
@[simp]
theorem compTendsto_id (x : G.Product R) :
    x.compTendsto id tendsto_id = x := by
  refine Quotient.inductionOn' x ?_
  intro f
  rfl

/-- Successive pullbacks compose in the contravariant order, with the exact
composite dependent family. -/
theorem compTendsto_comp {S : η → Type z} (x : H.Product S)
    (v : κ → η) (hv : Tendsto v G H) (u : ι → κ) (hu : Tendsto u F G) :
    (x.compTendsto v hv).compTendsto u hu =
      x.compTendsto (v ∘ u) (hv.comp hu) := by
  refine Quotient.inductionOn' x ?_
  intro f
  rfl

/-- The representative equation uniquely determines pullback, even when there
are no total sections. -/
theorem compTendsto_unique (u : ι → κ) (hu : Tendsto u F G)
    (T : G.Product R → F.Product (fun i => R (u i)))
    (hT : ∀ f : ∀ j, R j,
      T (f : G.Product R) = ((fun i => f (u i)) : F.Product (fun i => R (u i)))) :
    T = fun x => x.compTendsto u hu := by
  funext x
  exact Quotient.inductionOn' x hT

/-- Exact filter-image equality makes pullback injective, without any
injectivity assumption on the index map or any section-existence assumption. -/
theorem compTendsto_injective_of_map_eq (u : ι → κ) (hmap : Filter.map u F = G) :
    Function.Injective (fun x : G.Product R => x.compTendsto u hmap.le) := by
  let q : (∀ j, R j) → F.Product (fun i => R (u i)) := fun s =>
    (((fun i : ι => s (u i)) : ∀ i, R (u i)) : F.Product (fun i => R (u i)))
  have hle : productSetoid G R ≤ Setoid.ker q := by
    intro s t hst
    exact (coe_eq _ _).2 ((show Tendsto u F G from hmap.le).eventually hst)
  have hq : Quotient.lift q hle = fun x : G.Product R => x.compTendsto u hmap.le :=
    compTendsto_unique u hmap.le _ (fun _ => rfl)
  rw [← hq]
  apply (Setoid.lift_injective_iff_ker_eq_of_le hle).2
  refine Setoid.ext fun s t => ?_
  change q s = q t ↔ ∀ᶠ j in G, s j = t j
  exact (coe_eq (fun i : ι => s (u i)) (fun i : ι => t (u i))).trans (by
    rw [← hmap, Filter.eventually_map])

/-- An index equivalence makes pullback surjective using only forward convergence.
The representative preimage uses dependent Pi reindexing; it need not descend to
a quotient inverse without reverse convergence. -/
theorem compTendsto_surjective_of_equiv (e : ι ≃ κ) (he : Tendsto e F G) :
    Function.Surjective (fun x : G.Product R => x.compTendsto e he) := by
  intro x
  obtain ⟨s, rfl⟩ : ∃ s : ∀ i, R (e i), (s : F.Product (fun i => R (e i))) = x :=
    Quotient.mk_surjective x
  refine ⟨((Equiv.piCongrLeft R e s) : G.Product R), ?_⟩
  exact (coe_compTendsto (Equiv.piCongrLeft R e s) e he).trans
    (congrArg (fun t : ∀ i, R (e i) => (t : F.Product (fun i => R (e i))))
      ((Equiv.piCongrLeft R e).symm_apply_apply s))

/-- For constant families, pullback is Mathlib's existing germ composition.
The two carriers are definitionally equal; this lemma identifies the operations. -/
theorem compTendsto_eq_germ_compTendsto {A : Type z}
    (x : G.Product (fun _ => A)) (u : ι → κ) (hu : Tendsto u F G) :
    x.compTendsto u hu = Germ.compTendsto x u hu := by
  refine Quotient.inductionOn' x ?_
  intro f
  rfl

/-- Reindex dependent products by an index equivalence tending in both directions.
The inverse is the descended `Equiv.piCongrLeft`, not untransported precomposition. -/
def compTendstoEquiv (R : κ → Type z) (e : ι ≃ κ)
    (he : Tendsto e F G) (he' : Tendsto e.symm G F) :
    G.Product R ≃ F.Product (fun i => R (e i)) where
  toFun x := x.compTendsto e he
  invFun := Quotient.map' (Equiv.piCongrLeft R e) (by
    intro s t h
    apply (he'.eventually h).mono
    intro j hj
    rw [Equiv.piCongrLeft_apply_eq_cast, Equiv.piCongrLeft_apply_eq_cast]
    exact congrArg (cast (congrArg R (e.apply_symm_apply j))) hj)
  left_inv x := by
    refine Quotient.inductionOn' x ?_
    intro f
    exact congrArg (fun s : ∀ j, R j => (s : G.Product R))
      ((Equiv.piCongrLeft R e).apply_symm_apply f)
  right_inv x := by
    refine Quotient.inductionOn' x ?_
    intro s
    exact congrArg (fun t : ∀ i, R (e i) => (t : F.Product (fun i => R (e i))))
      ((Equiv.piCongrLeft R e).symm_apply_apply s)

/-- The equivalence uses the same forward pullback operation. -/
@[simp]
theorem compTendstoEquiv_apply (e : ι ≃ κ)
    (he : Tendsto e F G) (he' : Tendsto e.symm G F) (x : G.Product R) :
    compTendstoEquiv R e he he' x = x.compTendsto e he := rfl

/-- The inverse on representatives is canonical dependent Pi reindexing:
at `j` it transports `s (e.symm j)` along `e.apply_symm_apply j`. -/
@[simp]
theorem compTendstoEquiv_symm_coe (e : ι ≃ κ)
    (he : Tendsto e F G) (he' : Tendsto e.symm G F) (s : ∀ i, R (e i)) :
    (compTendstoEquiv R e he he').symm (s : F.Product (fun i => R (e i))) =
      ((Equiv.piCongrLeft R e s) : G.Product R) := rfl

/-- Inverse reindexing undoes the original pullback. -/
@[simp]
theorem compTendstoEquiv_symm_compTendsto (e : ι ≃ κ)
    (he : Tendsto e F G) (he' : Tendsto e.symm G F) (x : G.Product R) :
    (compTendstoEquiv R e he he').symm (x.compTendsto e he) = x :=
  (compTendstoEquiv R e he he').symm_apply_apply x

/-- Pullback undoes inverse reindexing. -/
@[simp]
theorem compTendsto_compTendstoEquiv_symm (e : ι ≃ κ)
    (he : Tendsto e F G) (he' : Tendsto e.symm G F)
    (x : F.Product (fun i => R (e i))) :
    ((compTendstoEquiv R e he he').symm x).compTendsto e he = x :=
  (compTendstoEquiv R e he he').apply_symm_apply x

end Filter.Product
