/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Group.Ext
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Ring.Ext
public import MinimalPrimes.Order.Filter.Product.Map

/-!
# Semimodules over dependent reduced products

The additive congruence uses eventual equality of total sections. Its quotient
additive monoid and the binary quotient map of the fibre actions give a semimodule
over the existing reduced product of scalar semirings.

The structures `Filter.Product.addCommMonoid`, `Filter.Product.smul` and
`Filter.Product.module` are named data, not global instances. This keeps the given
fibre actions fixed even when the scalar and vector carrier families coincide.
The representative equations and `smul_coe_eq_map` characterize the action on
opaque quotient points. `smul_coe_eq_smul_coe_iff` detects equality of two represented
scalar actions by eventual equality on every fibre vector; vector zeros supply
only a total fallback section. Constant structure records recover the two-germ action
in Mathlib, rather than its fixed-external-scalar action.

## References

This construction uses Mathlib's additive congruence quotient machinery, binary
quotient maps, and module/Pi interfaces. The constant-family comparison is with
Mathlib's `Filter.Germ.instModule'`. The varying map and its uniqueness interface
are those of `MinimalPrimes.Order.Filter.Product.Map`.
-/

@[expose] public section

universe u v w

namespace Filter

variable {ι : Type u}

/-- Eventual equality of dependent sections as an additive congruence. -/
def productAddCon (F : Filter ι) (M : ι → Type w) [∀ i, Add (M i)] :
    AddCon (∀ i, M i) where
  toSetoid := productSetoid F M
  add' h₁ h₂ := by
    exact (h₁.and h₂).mono fun i h => congrArg₂ (· + ·) h.1 h.2

@[simp]
theorem productAddCon_toSetoid (F : Filter ι) (M : ι → Type w) [∀ i, Add (M i)] :
    (productAddCon F M).toSetoid = productSetoid F M := rfl

/-- The additive congruence agrees with the additive parent of the ring congruence. -/
theorem productAddCon_eq_toAddCon (F : Filter ι) (M : ι → Type w)
    [∀ i, Add (M i)] [∀ i, Mul (M i)] :
    productAddCon F M = (productRingCon F M).toAddCon := by
  apply AddCon.toSetoid_injective
  exact (productRingCon_toSetoid F M).symm

namespace Product

variable (F : Filter ι) (M : ι → Type w)

/-- Eliminate a reduced-product point using its existing total-section representatives. -/
@[elab_as_elim]
theorem inductionOn {P : F.Product M → Prop} (x : F.Product M)
    (h : ∀ m : ∀ i, M i, P (m : F.Product M)) : P x := by
  obtain ⟨m, hm⟩ := coe_surjective F M x
  exact hm ▸ h m

/-- Addition on the reduced product, from its additive congruence. -/
@[instance_reducible]
def add [∀ i, Add (M i)] : Add (F.Product M) :=
  (productAddCon F M).hasAdd

/-- Zero on the additive reduced product. -/
@[instance_reducible]
def zero [∀ i, AddZeroClass (M i)] : Zero (F.Product M) :=
  (productAddCon F M).zero

/-- The additive commutative monoid of dependent sections modulo eventual equality. -/
@[instance_reducible]
def addCommMonoid [∀ i, AddCommMonoid (M i)] : AddCommMonoid (F.Product M) :=
  (productAddCon F M).addCommMonoid

section Add

attribute [local instance] add

/-- The existing section coercion as an additive homomorphism. -/
def coeAddHom [∀ i, Add (M i)] : (∀ i, M i) →ₙ+ F.Product M :=
  (productAddCon F M).mkAddHom

@[simp]
theorem coeAddHom_apply [∀ i, Add (M i)] (m : ∀ i, M i) :
    coeAddHom F M m = (m : F.Product M) := rfl

@[simp]
theorem coe_add [∀ i, Add (M i)] (m n : ∀ i, M i) :
    ((m + n : ∀ i, M i) : F.Product M) = ((· + ·) : F.Product M → F.Product M → F.Product M)
      (m : F.Product M) (n : F.Product M) :=
  (coeAddHom F M).map_add m n

end Add

section Zero

attribute [local instance] zero

@[simp]
theorem coe_zero_add [∀ i, AddZeroClass (M i)] :
    ((0 : ∀ i, M i) : F.Product M) = (0 : F.Product M) :=
  (productAddCon F M).coe_zero

/-- The represented section of fibre zeros is the zero of the named additive
reduced-product record. Only additive zero classes are needed. -/
@[simp]
theorem zeroPoint_eq_zero_add [∀ i, AddZeroClass (M i)] :
    zeroPoint F M = (0 : F.Product M) := by
  exact
    ((coe_eq_zeroPoint_iff F (0 : ∀ i, M i)).2
      (Filter.Eventually.of_forall fun _ => rfl)).symm.trans (coe_zero_add F M)

end Zero

section AddCommMonoid

attribute [local instance] addCommMonoid

/-- The existing section coercion as an additive monoid homomorphism. -/
def coeAddMonoidHom [∀ i, AddCommMonoid (M i)] : (∀ i, M i) →+ F.Product M :=
  (productAddCon F M).mk'

@[simp]
theorem coeAddMonoidHom_apply [∀ i, AddCommMonoid (M i)] (m : ∀ i, M i) :
    coeAddMonoidHom F M m = (m : F.Product M) := rfl

@[simp]
theorem coe_nsmul [∀ i, AddCommMonoid (M i)] (n : ℕ) (m : ∀ i, M i) :
    ((n • m : ∀ i, M i) : F.Product M) =
      ((· • ·) : ℕ → F.Product M → F.Product M) n (m : F.Product M) :=
  (coeAddMonoidHom F M).map_nsmul n m

end AddCommMonoid

/-- The quotient additive record agrees with the parent of the existing scalar semiring.
In particular this identifies its natural-number scaling as well as addition and zero. -/
theorem addCommMonoid_eq_semiring [∀ i, Semiring (M i)] :
    addCommMonoid F M = (instSemiring (F := F) (K := M)).toAddCommMonoid := by
  apply AddCommMonoid.ext
  funext x y
  induction x using inductionOn F M with | h m =>
    induction y using inductionOn F M with | h n =>
      exact (coe_add F M m n).symm.trans
        ((show (∀ i, M i) →+* F.Product M from (productRingCon F M).mk').map_add m n)

/-- Addition of scalar representatives for the existing scalar semiring. -/
theorem coe_add_semiring [∀ i, Semiring (M i)] (m n : ∀ i, M i) :
    ((m + n : ∀ i, M i) : F.Product M) = ((· + ·) : F.Product M → F.Product M → F.Product M)
      (m : F.Product M) (n : F.Product M) :=
  (show (∀ i, M i) →+* F.Product M from (productRingCon F M).mk').map_add m n

variable (R : ι → Type v)

/-- The binary quotient map of the given fibre actions. -/
@[instance_reducible]
def smul [∀ i, SMul (R i) (M i)] : SMul (F.Product R) (F.Product M) where
  smul := Quotient.map₂ (fun (r : ∀ i, R i) (m : ∀ i, M i) => fun i => r i • m i)
    (fun _ _ hr _ _ hm => (hr.and hm).mono fun _ h => congrArg₂ (· • ·) h.1 h.2)

section SMul

attribute [local instance] smul

@[simp]
theorem coe_smul [∀ i, SMul (R i) (M i)] (r : ∀ i, R i) (m : ∀ i, M i) :
    ((· • ·) : F.Product R → F.Product M → F.Product M)
      (r : F.Product R) (m : F.Product M) = ((fun i => r i • m i) : F.Product M) := rfl

/-- A represented scalar acts on every quotient point by the existing coordinate map. -/
theorem smul_coe_eq_map [∀ i, SMul (R i) (M i)] (r : ∀ i, R i) :
    (fun x : F.Product M =>
      ((· • ·) : F.Product R → F.Product M → F.Product M) (r : F.Product R) x) =
      map F (fun i m => r i • m) :=
  map_unique F _ _ (fun m => coe_smul F M R r m)

/-- Two represented scalars act equally on every reduced-product vector exactly when
their fibre actions agree on every vector eventually. Fibre zeros supply a total
section; no preservation of zero by the actions is required. -/
theorem smul_coe_eq_smul_coe_iff [z : ∀ i, Zero (M i)]
    [σ : ∀ i, SMul (R i) (M i)] (r t : ∀ i, R i) :
    ((fun x : F.Product M =>
        @SMul.smul (F.Product R) (F.Product M) (@smul ι F M R σ)
          (r : F.Product R) x) =
      (fun x : F.Product M =>
        @SMul.smul (F.Product R) (F.Product M) (@smul ι F M R σ)
          (t : F.Product R) x)) ↔
      ∀ᶠ i in F, ∀ m : M i,
        @SMul.smul (R i) (M i) (σ i) (r i) m =
          @SMul.smul (R i) (M i) (σ i) (t i) m := by
  constructor
  · intro h
    apply (Filter.eventually_forall_iff_forall_section
      (D := F)
      (P := fun i m =>
        @SMul.smul (R i) (M i) (σ i) (r i) m =
          @SMul.smul (R i) (M i) (σ i) (t i) m)
      (fun i => (0 : M i))).2
    intro m
    apply (coe_eq (F := F) _ _).1
    exact (coe_smul F M R r m).symm.trans
      ((congrFun h (m : F.Product M)).trans (coe_smul F M R t m))
  · intro h
    funext x
    obtain ⟨m, rfl⟩ := coe_surjective F M x
    exact (coe_smul F M R r m).trans
      (((coe_eq (F := F) _ _).mpr (h.mono fun i hi => hi (m i))).trans
        (coe_smul F M R t m).symm)

end SMul

section Module

variable [s : ∀ i, Semiring (R i)] [a : ∀ i, AddCommMonoid (M i)]
    [p : ∀ i, Module (R i) (M i)]

attribute [local instance] addCommMonoid smul

/-- The semimodule over the existing scalar reduced product, with the given fibre actions. -/
@[instance_reducible]
def module : Module (F.Product R) (F.Product M) := by
  let qR : (∀ i, R i) →+* F.Product R := (productRingCon F R).mk'
  let qM : (∀ i, M i) →+ F.Product M := coeAddMonoidHom F M
  have hR : Function.Surjective qR := (productRingCon F R).mk'_surjective
  have hM : Function.Surjective qM := (productAddCon F M).mk'_surjective
  have hsmul (r : ∀ i, R i) (m : ∀ i, M i) :
      qR r • qM m = qM (fun i => r i • m i) := coe_smul F M R r m
  exact
    { smul := (smul F M R).smul
      one_smul := fun x => by
        obtain ⟨m, rfl⟩ := hM x
        rw [← qR.map_one, hsmul]
        exact congrArg qM (by ext i; exact one_smul _ _)
      mul_smul := fun r t x => by
        obtain ⟨r, rfl⟩ := hR r
        obtain ⟨t, rfl⟩ := hR t
        obtain ⟨m, rfl⟩ := hM x
        rw [← qR.map_mul, hsmul, hsmul, hsmul]
        exact congrArg qM (by ext i; exact mul_smul _ _ _)
      smul_add := fun r x y => by
        obtain ⟨r, rfl⟩ := hR r
        obtain ⟨m, rfl⟩ := hM x
        obtain ⟨n, rfl⟩ := hM y
        rw [← qM.map_add, hsmul, hsmul, hsmul, ← qM.map_add]
        exact congrArg qM (by ext i; exact smul_add _ _ _)
      smul_zero := fun r => by
        obtain ⟨r, rfl⟩ := hR r
        rw [← qM.map_zero, hsmul]
        exact congrArg qM (by ext i; exact smul_zero _)
      add_smul := fun r t x => by
        obtain ⟨r, rfl⟩ := hR r
        obtain ⟨t, rfl⟩ := hR t
        obtain ⟨m, rfl⟩ := hM x
        rw [← qR.map_add, hsmul, hsmul, hsmul, ← qM.map_add]
        exact congrArg qM (by ext i; exact add_smul _ _ _)
      zero_smul := fun x => by
        obtain ⟨m, rfl⟩ := hM x
        rw [← qR.map_zero, hsmul, ← qM.map_zero]
        exact congrArg qM (by ext i; exact zero_smul _ _) }

/-- The inherited action of the semimodule is the named binary quotient action. -/
theorem module_toSMul : (module F M R).toSMul = smul F M R := rfl

end Module

/-- The scalar semiring on a constant family agrees with the germ semiring as a record. -/
theorem semiring_const_eq_germ (A : Type v) [Semiring A] :
    instSemiring (F := F) (K := fun _ : ι => A) =
      Germ.instSemiring (l := F) (R := A) := by
  apply Semiring.ext
  · funext x y
    induction x using inductionOn F (fun _ : ι => A) with | h r =>
      induction y using inductionOn F (fun _ : ι => A) with | h t =>
        exact (coe_add_semiring F (fun _ : ι => A) r t).symm.trans (Germ.coe_add r t)
  · funext x y
    induction x using inductionOn F (fun _ : ι => A) with | h r =>
      induction y using inductionOn F (fun _ : ι => A) with | h t =>
        exact (coe_mul (F := F) r t).symm.trans (Germ.coe_mul r t)

/-- The additive quotient record on a constant family agrees with the germ record. -/
theorem addCommMonoid_const_eq_germ (B : Type w) [AddCommMonoid B] :
    addCommMonoid F (fun _ : ι => B) = Germ.instAddCommMonoid (l := F) (M := B) := by
  apply AddCommMonoid.ext
  funext x y
  induction x using inductionOn F (fun _ : ι => B) with | h m =>
    induction y using inductionOn F (fun _ : ι => B) with | h n =>
      exact (coe_add F (fun _ : ι => B) m n).symm.trans (Germ.coe_add m n)

/-- Constant fibre actions recover the binary action on two germs. -/
theorem smul_const_eq_germ (A : Type v) (B : Type w) [SMul A B] :
    smul F (fun _ : ι => B) (fun _ : ι => A) = Germ.instSMul' (l := F) := by
  have h : (smul F (fun _ : ι => B) (fun _ : ι => A)).smul =
      (Germ.instSMul' (l := F) : SMul (Germ F A) (Germ F B)).smul := by
    funext r x
    induction r using inductionOn F (fun _ : ι => A) with | h r =>
      induction x using inductionOn F (fun _ : ι => B) with | h m =>
        exact (coe_smul F (fun _ : ι => B) (fun _ : ι => A) r m).trans
          (Germ.coe_smul' r m)
  exact congrArg (fun f : Germ F A → Germ F B → Germ F B =>
    (⟨f⟩ : SMul (Germ F A) (Germ F B))) h

private theorem module_cast_eq {S : Type v} {N : Type w}
    {s t : Semiring S} {a b : AddCommMonoid N} (hs : s = t) (ha : a = b)
    (P : @Module S N s a) (Q : @Module S N t b) (h : P.toSMul = Q.toSMul) :
    cast (congrArg₂ (fun (s : Semiring S) (a : AddCommMonoid N) => @Module S N s a)
      hs ha) P = Q := by
  cases hs
  cases ha
  apply Module.ext'
  intro r x
  exact congrArg (fun σ : SMul S N => @SMul.smul S N σ r x) h

/-- After identifying both base records, constant fibre semimodules recover Mathlib's
semimodule over two germs, with the same given scalar, additive and module records. -/
theorem module_const_eq_germ (A : Type v) (B : Type w)
    [s : Semiring A] [a : AddCommMonoid B] [p : Module A B] :
    cast (congrArg₂
      (fun (s : Semiring (Germ F A)) (a : AddCommMonoid (Germ F B)) =>
        @Module (Germ F A) (Germ F B) s a)
      (semiring_const_eq_germ F A) (addCommMonoid_const_eq_germ F B))
      (module (s := fun _ => s) (a := fun _ => a) (p := fun _ => p)
        F (fun _ : ι => B) (fun _ : ι => A)) =
      Germ.instModule' (l := F) (R := A) (M := B) := by
  exact module_cast_eq (semiring_const_eq_germ F A) (addCommMonoid_const_eq_germ F B)
    _ _ ((module_toSMul F (fun _ : ι => B) (fun _ : ι => A)).trans
      (smul_const_eq_germ F A B))

/-- For the standard fibre self-actions, the quotient action is quotient multiplication. -/
theorem smul_self_eq_mul [∀ i, Semiring (R i)] :
    @smul ι F R R (fun i => (Semiring.toModule : Module (R i) (R i)).toSMul) =
      (⟨(· * ·)⟩ : SMul (F.Product R) (F.Product R)) := by
  have h : (@smul ι F R R
      (fun i => (Semiring.toModule : Module (R i) (R i)).toSMul)).smul =
        ((· * ·) : F.Product R → F.Product R → F.Product R) := by
    funext r x
    induction r using inductionOn F R with | h r =>
      induction x using inductionOn F R with | h m =>
        exact (coe_smul F R R r m).trans (coe_mul (F := F) r m)
  exact congrArg (fun f : F.Product R → F.Product R → F.Product R =>
    (⟨f⟩ : SMul (F.Product R) (F.Product R))) h

/-- With standard given fibre self-modules, the quotient module is the standard
self-module after identification of the vector additive base. -/
theorem module_self_eq [s : ∀ i, Semiring (R i)] :
    cast (congrArg
      (fun a : AddCommMonoid (F.Product R) =>
        @Module (F.Product R) (F.Product R) (instSemiring (F := F) (K := R)) a)
      (addCommMonoid_eq_semiring F R))
      (module (s := s) (a := fun i => (s i).toAddCommMonoid)
        (p := fun i => (Semiring.toModule : Module (R i) (R i))) F R R) =
      (Semiring.toModule : Module (F.Product R) (F.Product R)) := by
  exact module_cast_eq rfl (addCommMonoid_eq_semiring F R) _ _
    ((module_toSMul F R R).trans (smul_self_eq_mul F R))

end Product
end Filter
