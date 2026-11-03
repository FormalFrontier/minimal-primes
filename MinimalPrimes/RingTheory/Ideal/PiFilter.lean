/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Order.Filter.Cofinite
public import MinimalPrimes.Order.Filter.Product
public import Mathlib.RingTheory.Ideal.Basic
public import Mathlib.RingTheory.Ideal.Maps

/-!
# Ideals of products and filters

`Filter.piIdeal` and `Ideal.piFilter` construct ordinary left ideals and filters
for arbitrary dependent semiring families. For division semirings they are inverse,
giving `Ideal.piOrderIsoFilter`. In particular this classifies all ideals of a
product of semifields, not just prime or proper ideals.

The native filter order reverses inclusion of member collections; hence the target
is the order dual. The improper filter corresponds to the whole ideal. No finite,
nonempty or nontrivial-product hypothesis is needed, and the two universes are
independent. The semiring constructors do not themselves classify all ideals:
division is used in `Ideal.zeroSet_mem_piFilter`.

For arbitrary semiring factors, the zero-set construction exchanges filter infima
and suprema with ideal suprema and infima. The infimum-to-supremum law uses the
reversed-order adjunction with `Ideal.piFilter`; the other law follows from zero-set
membership. The proofs reuse Mathlib's Galois-connection and filter/submodule lattice APIs.

The zero-set tests, disjoint-piece sum and pointwise inverse argument generalize
the original prime/ultrafilter construction by Formal Frontier Agents in
`MinimalPrimes.RingTheory.Ideal.PrimePiUltrafilter`. The constructions use Mathlib's
existing ideal, filter, germ and finite-product interfaces.
-/

@[expose] public section

open Set Filter

universe u v

variable {ι : Type u}

namespace Filter

variable (A : ι → Type v) [∀ i, Semiring (A i)]

/-- Functions whose zero set belongs to a filter form a left ideal. -/
def piIdeal (F : Filter ι) : Ideal (Π i, A i) where
  carrier := {f | {i | f i = 0} ∈ F}
  zero_mem' := Filter.Eventually.of_forall fun _ => rfl
  add_mem' := by
    intro f g hf hg
    exact Filter.mem_of_superset (Filter.inter_mem hf hg) fun i hi => by
      rcases hi with ⟨hfi, hgi⟩
      change f i = 0 at hfi
      change g i = 0 at hgi
      change f i + g i = 0
      rw [hfi, hgi, zero_add]
  smul_mem' := by
    intro a f hf
    exact Filter.mem_of_superset hf fun i hi => by
      change f i = 0 at hi
      change a i * f i = 0
      rw [hi, mul_zero]

/-- The characteristic zero-set membership law. -/
@[simp]
theorem mem_piIdeal (F : Filter ι) (f : Π i, A i) :
    f ∈ F.piIdeal A ↔ {i | f i = 0} ∈ F := Iff.rfl

/-- Membership in the sum of a coordinate product ideal and a filter ideal is
coordinatewise ideal membership on a set belonging to the filter. -/
theorem mem_pi_sup_piIdeal {R : ι → Type v} [∀ i, Semiring (R i)]
    (I : ∀ i, Ideal (R i)) (D : Filter ι) (f : ∀ i, R i) :
    f ∈ Ideal.pi I ⊔ D.piIdeal R ↔ {i | f i ∈ I i} ∈ D := by
  classical
  rw [Submodule.mem_sup]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact Filter.mem_of_superset ((mem_piIdeal R D b).mp hb) fun i hi => by
      change b i = 0 at hi
      change a i + b i ∈ I i
      simpa only [hi, add_zero] using (Ideal.mem_pi I a).mp ha i
  · intro hf
    refine ⟨(fun i => if f i ∈ I i then f i else 0), ?_,
      (fun i => if f i ∈ I i then 0 else f i), ?_, ?_⟩
    · rw [Ideal.mem_pi]
      intro i
      split_ifs with hi
      · exact hi
      · exact (I i).zero_mem
    · rw [mem_piIdeal]
      exact Filter.mem_of_superset hf fun i hi => by
        change f i ∈ I i at hi
        change (if f i ∈ I i then 0 else f i) = 0
        simp [hi]
    · ext i
      by_cases hi : f i ∈ I i <;> simp [hi]

/-- The zero-set construction reverses the native filter order. -/
theorem piIdeal_antitone : Antitone (piIdeal A) := by
  intro F G h f hf
  exact h hf

/-- A principal filter gives the ideal of functions vanishing on its generating set. -/
theorem mem_piIdeal_principal (s : Set ι) (f : Π i, A i) :
    f ∈ (principal s).piIdeal A ↔ ∀ i ∈ s, f i = 0 := Iff.rfl

/-- The improper filter gives the whole ideal. -/
@[simp]
theorem piIdeal_bot : (⊥ : Filter ι).piIdeal A = ⊤ := by
  ext f
  simp

/-- The top filter gives the zero ideal, including for an empty index type. -/
@[simp]
theorem piIdeal_top : (⊤ : Filter ι).piIdeal A = ⊥ := by
  ext f
  rw [mem_piIdeal, Filter.mem_top_iff_forall, Ideal.mem_bot]
  exact funext_iff.symm

/-- A pure filter gives the kernel of coordinate evaluation. -/
@[simp]
theorem piIdeal_pure (i : ι) :
    (pure i : Filter ι).piIdeal A = RingHom.ker (Pi.evalRingHom A i) := by
  ext f
  simp [RingHom.mem_ker]

/-- The section homomorphism to the dependent reduced product has the existing filter ideal
as its kernel, for arbitrary semiring fibres and without a properness assumption. -/
theorem piIdeal_eq_ker_productMk (F : Filter ι) :
    F.piIdeal A = RingHom.ker (productRingCon F A).mk' := by
  ext f
  rw [mem_piIdeal, RingHom.mem_ker]
  exact (Product.coe_eq_zero f).symm

/-- For a constant family, the filter ideal is the kernel of the existing germ map. -/
theorem piIdeal_eq_ker_coeRingHom (R : Type v) [Semiring R] (F : Filter ι) :
    F.piIdeal (fun _ : ι => R) = RingHom.ker (Filter.Germ.coeRingHom (R := R) F) := by
  rw [piIdeal_eq_ker_productMk]
  ext f
  rfl

/-- The cofinite filter gives exactly the functions with finite support. -/
theorem mem_piIdeal_cofinite (f : Π i, A i) :
    f ∈ (cofinite : Filter ι).piIdeal A ↔ {i | f i ≠ 0}.Finite := by
  rw [mem_piIdeal, Filter.mem_cofinite]
  rfl

/-- Compatibility with Mathlib's coordinate-ideal classification of finite products. -/
theorem mem_piOrderIso_piIdeal_principal [Finite ι] (s : Set ι) (i : ι) (x : A i) :
    x ∈ (Ideal.piOrderIso ((principal s).piIdeal A)) i ↔ (i ∈ s → x = 0) := by
  classical
  change x ∈ Ideal.map (Pi.evalRingHom A i) ((principal s).piIdeal A) ↔ _
  rw [Ideal.mem_map_iff_of_surjective (Pi.evalRingHom A i) (Function.surjective_eval _)]
  constructor
  · rintro ⟨f, hf, rfl⟩ hi
    exact (mem_piIdeal_principal A s f).1 hf i hi
  · intro h
    refine ⟨Pi.single i x, ?_, ?_⟩
    · intro j hj
      by_cases hji : j = i
      · subst j
        simpa using h hj
      · simp [hji]
    · simp

end Filter

end

public section

open Filter

universe u v w

variable {ι : Type u}

namespace Ideal

variable (A : ι → Type v) [∀ i, Semiring (A i)]

private noncomputable def zeroTest (s : Set ι) : Π i, A i := by
  classical
  exact fun i => if i ∈ s then 0 else 1

private theorem zeroTest_zeroSet [∀ i, Nontrivial (A i)] (s : Set ι) :
    {i | zeroTest A s i = 0} = s := by
  classical
  ext i
  by_cases hi : i ∈ s <;> simp [zeroTest, hi]

private theorem zeroTest_mem_mono (I : Ideal (Π i, A i))
    {s t : Set ι} (hs : zeroTest A s ∈ I) (hst : s ⊆ t) :
    zeroTest A t ∈ I := by
  classical
  have he : zeroTest A t = zeroTest A t * zeroTest A s := by
    ext i
    by_cases hs : i ∈ s
    · simp [zeroTest, hs, hst hs]
    · simp [zeroTest, hs]
  rw [he]
  exact I.mul_mem_left _ hs

private theorem zeroTest_mem_inter (I : Ideal (Π i, A i))
    {s t : Set ι} (hs : zeroTest A s ∈ I) (ht : zeroTest A t ∈ I) :
    zeroTest A (s ∩ t) ∈ I := by
  classical
  have he : zeroTest A (s ∩ t) = zeroTest A s + zeroTest A sᶜ * zeroTest A t := by
    ext i
    by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;> simp [zeroTest, hs, ht]
  rw [he]
  exact I.add_mem hs (I.mul_mem_left _ ht)

/-- A set belongs to the ideal's filter when its zero-on-set, one-off-set test
belongs to the ideal. -/
noncomputable def piFilter (I : Ideal (Π i, A i)) : Filter ι where
  sets := {s | zeroTest A s ∈ I}
  univ_sets := by
    have he : zeroTest A Set.univ = 0 := by
      classical
      ext i
      simp [zeroTest]
    change zeroTest A Set.univ ∈ I
    rw [he]
    exact I.zero_mem
  sets_of_superset := fun hs hst => zeroTest_mem_mono A I hs hst
  inter_sets := fun hs ht => zeroTest_mem_inter A I hs ht

/-- A public characteristic-function witness law, without exposing the private test function. -/
theorem mem_piFilter (I : Ideal (Π i, A i)) (s : Set ι) :
    s ∈ I.piFilter A ↔ ∃ f : Π i, A i,
      f ∈ I ∧ (∀ i ∈ s, f i = 0) ∧ (∀ i ∉ s, f i = 1) := by
  classical
  constructor
  · intro hs
    refine ⟨zeroTest A s, hs, ?_, ?_⟩ <;> intro i hi <;> simp [zeroTest, hi]
  · rintro ⟨f, hf, hzero, hone⟩
    have he : f = zeroTest A s := by
      ext i
      by_cases hi : i ∈ s <;> simp [zeroTest, hi, hzero, hone]
    change zeroTest A s ∈ I
    exact he ▸ hf

/-- Every function whose zero set belongs to the ideal's filter belongs to the ideal.
This direction needs no division or nontriviality assumption on the factors. -/
theorem piIdeal_piFilter_le (I : Ideal (Π i, A i)) :
    (I.piFilter A).piIdeal A ≤ I := by
  classical
  intro f hf
  change zeroTest A {i | f i = 0} ∈ I at hf
  have he : f = f * zeroTest A {i | f i = 0} := by
    ext i
    by_cases hi : f i = 0 <;> simp [zeroTest, hi]
  exact he.symm ▸ I.mul_mem_left f hf

/-- The zero-set ideal and characteristic-test filter satisfy the reversed-order
adjunction already for arbitrary semiring factors. -/
theorem piIdeal_le_iff_piFilter_le (F : Filter ι) (I : Ideal (Π i, A i)) :
    F.piIdeal A ≤ I ↔ I.piFilter A ≤ F := by
  classical
  constructor
  · intro h s hs
    change zeroTest A s ∈ I
    apply h
    exact Filter.mem_of_superset hs fun i hi => by simp [zeroTest, hi]
  · intro h
    exact (Filter.piIdeal_antitone A h).trans (piIdeal_piFilter_le A I)

/-- Ideal inclusion reverses the native filter order. -/
theorem piFilter_antitone : Antitone (piFilter A) := by
  intro I J h s hs
  exact h hs

/-- Recovering a filter needs only nontrivial semiring factors, not division. -/
@[simp]
theorem piFilter_piIdeal [∀ i, Nontrivial (A i)] (F : Filter ι) :
    (F.piIdeal A).piFilter A = F := by
  apply Filter.ext
  intro s
  change zeroTest A s ∈ F.piIdeal A ↔ s ∈ F
  rw [Filter.mem_piIdeal, zeroTest_zeroSet]

/-- The whole ideal gives the improper filter already at semiring generality. -/
@[simp]
theorem piFilter_top : (⊤ : Ideal (Π i, A i)).piFilter A = ⊥ := by
  apply Filter.ext
  intro s
  change zeroTest A s ∈ (⊤ : Ideal (Π i, A i)) ↔ s ∈ (⊥ : Filter ι)
  simp

/-- An ideal gives the improper filter exactly when it is the whole ideal. -/
@[simp]
theorem piFilter_eq_bot_iff (I : Ideal (Π i, A i)) :
    I.piFilter A = ⊥ ↔ I = ⊤ := by
  classical
  constructor
  · intro h
    apply (Ideal.eq_top_iff_one I).2
    have he : (∅ : Set ι) ∈ I.piFilter A := by rw [h]; simp
    change zeroTest A ∅ ∈ I at he
    have htest : zeroTest A ∅ = 1 := by
      ext i
      simp [zeroTest]
    exact htest ▸ he
  · rintro rfl
    exact piFilter_top A

/-- Proper ideals give non-improper filters, without restricting the construction. -/
theorem piFilter_ne_bot_iff (I : Ideal (Π i, A i)) :
    I.piFilter A ≠ ⊥ ↔ I ≠ ⊤ := not_congr (piFilter_eq_bot_iff A I)

/-- The zero ideal gives the top filter for nontrivial semiring factors. -/
@[simp]
theorem piFilter_bot [∀ i, Nontrivial (A i)] :
    (⊥ : Ideal (Π i, A i)).piFilter A = ⊤ := by
  rw [← Filter.piIdeal_top A, piFilter_piIdeal]

/-- Primality upgrades the ordinary ideal filter to the complement law of an ultrafilter. -/
theorem compl_notMem_piFilter (I : Ideal (Π i, A i)) [I.IsPrime] (s : Set ι) :
    sᶜ ∉ I.piFilter A ↔ s ∈ I.piFilter A := by
  classical
  change zeroTest A sᶜ ∉ I ↔ zeroTest A s ∈ I
  have hm : zeroTest A s * zeroTest A sᶜ = 0 := by
    ext i
    by_cases hi : i ∈ s <;> simp [zeroTest, hi]
  have ha : zeroTest A s + zeroTest A sᶜ = 1 := by
    ext i
    by_cases hi : i ∈ s <;> simp [zeroTest, hi]
  constructor
  · intro h
    exact (inferInstance : I.IsPrime).mem_or_mem_of_mul_eq_zero hm |>.resolve_right h
  · intro hs hc
    exact (inferInstance : I.IsPrime).one_notMem (ha ▸ I.add_mem hs hc)

end Ideal

namespace Filter

variable (A : ι → Type v) [∀ i, Semiring (A i)]

/-- The zero-set ideal of an indexed infimum of filters is the supremum of their ideals. -/
theorem piIdeal_iInf {κ : Sort w} (Fs : κ → Filter ι) :
    (iInf Fs).piIdeal A = ⨆ j, (Fs j).piIdeal A := by
  have gc : GaloisConnection
      (fun F : (Filter ι)ᵒᵈ => (OrderDual.ofDual F).piIdeal A)
      (fun I : Ideal (Π i, A i) => OrderDual.toDual (I.piFilter A)) :=
    fun F I => Ideal.piIdeal_le_iff_piFilter_le A (OrderDual.ofDual F) I
  exact gc.l_iSup (f := fun j => OrderDual.toDual (Fs j))

/-- The zero-set ideal of an indexed supremum of filters is the infimum of their ideals. -/
theorem piIdeal_iSup {κ : Sort w} (Fs : κ → Filter ι) :
    (iSup Fs).piIdeal A = ⨅ j, (Fs j).piIdeal A := by
  ext f
  simp only [mem_piIdeal, Filter.mem_iSup, Submodule.mem_iInf]

/-- The zero-set ideal of the infimum of two filters is the join of their ideals. -/
theorem piIdeal_inf (F G : Filter ι) :
    (F ⊓ G).piIdeal A = F.piIdeal A ⊔ G.piIdeal A := by
  have gc : GaloisConnection
      (fun F : (Filter ι)ᵒᵈ => (OrderDual.ofDual F).piIdeal A)
      (fun I : Ideal (Π i, A i) => OrderDual.toDual (I.piFilter A)) :=
    fun F I => Ideal.piIdeal_le_iff_piFilter_le A (OrderDual.ofDual F) I
  exact gc.l_sup (a₁ := OrderDual.toDual F) (a₂ := OrderDual.toDual G)

variable [∀ i, Nontrivial (A i)]

/-- Zero-set ideals distinguish filters as soon as all factors are nontrivial. -/
theorem piIdeal_injective : Function.Injective (piIdeal A) := by
  intro F G h
  simpa only [Ideal.piFilter_piIdeal] using congrArg (Ideal.piFilter A) h

/-- The weak constructor reflects the reversed order for nontrivial semiring factors. -/
theorem piIdeal_le_piIdeal_iff (F G : Filter ι) :
    F.piIdeal A ≤ G.piIdeal A ↔ G ≤ F := by
  constructor
  · intro h
    simpa only [Ideal.piFilter_piIdeal] using Ideal.piFilter_antitone A h
  · intro h
    exact piIdeal_antitone A h

/-- The zero-set ideal is the whole ideal exactly for the improper filter. -/
@[simp]
theorem piIdeal_eq_top_iff (F : Filter ι) : F.piIdeal A = ⊤ ↔ F = ⊥ := by
  constructor
  · intro h
    simpa only [Ideal.piFilter_piIdeal, Ideal.piFilter_top] using
      congrArg (Ideal.piFilter A) h
  · rintro rfl
    exact piIdeal_bot A

end Filter

namespace Ideal

variable (K : ι → Type v) [∀ i, DivisionSemiring (K i)]

/-- Division recovers ideal membership from zero-set membership in the associated filter. -/
@[simp]
theorem zeroSet_mem_piFilter (I : Ideal (Π i, K i)) (f : Π i, K i) :
    {i | f i = 0} ∈ I.piFilter K ↔ f ∈ I := by
  classical
  change zeroTest K {i | f i = 0} ∈ I ↔ f ∈ I
  have he : zeroTest K {i | f i = 0} = (fun i => (f i)⁻¹) * f := by
    ext i
    by_cases hi : f i = 0 <;> simp [zeroTest, hi]
  constructor
  · intro h
    exact piIdeal_piFilter_le K I h
  · intro h
    rw [he]
    exact I.mul_mem_left _ h

/-- Members contain the zero set of a function in the ideal. -/
theorem mem_piFilter_iff_exists_zeroSet (I : Ideal (Π i, K i)) (s : Set ι) :
    s ∈ I.piFilter K ↔ ∃ f : Π i, K i, f ∈ I ∧ {i | f i = 0} ⊆ s := by
  constructor
  · intro hs
    exact ⟨zeroTest K s, hs, (zeroTest_zeroSet K s).subset⟩
  · rintro ⟨f, hf, hfs⟩
    exact Filter.mem_of_superset ((zeroSet_mem_piFilter K I f).2 hf) hfs

/-- Recovering every ideal is the division-semiring round trip. -/
@[simp]
theorem piIdeal_piFilter (I : Ideal (Π i, K i)) :
    (I.piFilter K).piIdeal K = I := by
  ext f
  exact zeroSet_mem_piFilter K I f

/-- The ideal-to-filter map is injective. -/
theorem piFilter_injective : Function.Injective (piFilter K) := by
  intro I J h
  simpa only [piIdeal_piFilter] using congrArg (Filter.piIdeal K) h

/-- Zero-set membership uniquely specifies the filter associated to an ideal. -/
theorem piFilter_eq_iff (I : Ideal (Π i, K i)) (F : Filter ι) :
    I.piFilter K = F ↔ ∀ f : Π i, K i, ({i | f i = 0} ∈ F ↔ f ∈ I) := by
  constructor
  · rintro rfl f
    exact zeroSet_mem_piFilter K I f
  · intro h
    apply Filter.piIdeal_injective K
    ext f
    exact (zeroSet_mem_piFilter K I f).trans (h f).symm

/-- Ideal inclusion corresponds to reversed native filter order. -/
theorem le_iff_piFilter_le (I J : Ideal (Π i, K i)) :
    I ≤ J ↔ J.piFilter K ≤ I.piFilter K := by
  constructor
  · intro h
    exact piFilter_antitone K h
  · intro h f hf
    exact (zeroSet_mem_piFilter K J f).1 (h ((zeroSet_mem_piFilter K I f).2 hf))

/-- All left ideals of an arbitrary product of division semirings correspond to standard filters.
In particular this applies to products of semifields, without additive cancellation. -/
@[expose]
noncomputable def piOrderIsoFilter : Ideal (Π i, K i) ≃o (Filter ι)ᵒᵈ where
  toFun I := OrderDual.toDual (I.piFilter K)
  invFun F := (OrderDual.ofDual F).piIdeal K
  left_inv := piIdeal_piFilter K
  right_inv := piFilter_piIdeal K
  map_rel_iff' := by
    intro I J
    exact (le_iff_piFilter_le K I J).symm

/-- The order isomorphism's forward map is the characteristic ideal filter. -/
@[simp]
theorem piOrderIsoFilter_apply (I : Ideal (Π i, K i)) :
    piOrderIsoFilter K I = OrderDual.toDual (I.piFilter K) := rfl

/-- Its inverse is exactly the zero-set ideal. -/
@[simp]
theorem piOrderIsoFilter_symm_apply (F : (Filter ι)ᵒᵈ) :
    (piOrderIsoFilter K).symm F = (OrderDual.ofDual F).piIdeal K := rfl

/-- A principal vanishing ideal is generated by any function with precisely that zero set. -/
theorem piIdeal_principal_zeroSet (f : Π i, K i) :
    (principal {i | f i = 0}).piIdeal K = Ideal.span {f} := by
  apply le_antisymm
  · intro g hg
    have he : g = (fun i => g i * (f i)⁻¹) * f := by
      ext i
      by_cases hi : f i = 0
      · have hgi : g i = 0 := (Filter.mem_piIdeal_principal K _ g).1 hg i hi
        simp [hi, hgi]
      · simp [hi]
    rw [he]
    exact (Ideal.span {f}).mul_mem_left _ (Ideal.subset_span (by simp))
  · apply Ideal.span_le.mpr
    rintro g rfl
    exact fun _ hi => hi

/-- The filter associated to a singly generated ideal is principal on its generator's zero set. -/
@[simp]
theorem piFilter_span_singleton (f : Π i, K i) :
    (Ideal.span {f}).piFilter K = principal {i | f i = 0} := by
  rw [← piIdeal_principal_zeroSet K f, piFilter_piIdeal]

/-- On an infinite index type the finite-support ideal is not singly generated. -/
theorem piIdeal_cofinite_ne_span_singleton [Infinite ι] (f : Π i, K i) :
    (cofinite : Filter ι).piIdeal K ≠ Ideal.span {f} := by
  intro h
  have hF : (cofinite : Filter ι) = principal {i | f i = 0} := by
    calc
      cofinite = ((cofinite : Filter ι).piIdeal K).piFilter K :=
        (piFilter_piIdeal K cofinite).symm
      _ = (Ideal.span {f}).piFilter K := congrArg (piFilter K) h
      _ = principal {i | f i = 0} := piFilter_span_singleton K f
  have hz : {i | f i = 0} = ∅ := by
    ext i
    constructor
    · intro hi
      have hs : ({i}ᶜ : Set ι) ∈ (cofinite : Filter ι) := by simp
      rw [hF] at hs
      simpa using (Filter.mem_principal.mp hs hi)
    · simp
  have he : (∅ : Set ι) ∈ (cofinite : Filter ι) := by
    rw [hF, hz]
    simp
  exact Filter.empty_notMem (cofinite : Filter ι) he

end Ideal
