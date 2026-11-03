/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MinimalPrimes.RingTheory.Ideal.PiFilter
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Order.Atoms
public import Mathlib.Order.Filter.Ultrafilter.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.Spectrum.Prime.Defs

/-!
# Ultrafilter coordinates of prime ideals of products

`Ultrafilter.piIdeal` assigns to an ultrafilter the ideal of functions whose zero set
belongs to it. The construction works for semiring factors, and the ideals of distinct
ultrafilters have join equal to the whole ideal. This uses Mathlib's ultrafilter
disjointness API. The ideal is prime for nontrivial factors without zero divisors.
These zero-set ideals are maximal already for division
semiring fibres, by extremality in the ideal/filter order isomorphism. For an arbitrary
dependent family of semifields, `PrimeSpectrum.piEquivUltrafilter` classifies all prime
ideals by ultrafilters.

For arbitrary commutative semiring factors, `PrimeSpectrum.piUltrafilterMap` gives
the ultrafilter coordinate of each prime through the characteristic-test filter
`Ideal.piFilter`. Containment of `Ultrafilter.piIdeal` characterizes a coordinate
fiber. Its image consists exactly of the ultrafilters containing the set of
nontrivial factors, and it is surjective exactly when every factor is nontrivial.
The semifield constructor `PrimeSpectrum.piUltrafilter` uses this same map;
only the inverse classification needs division and nontriviality.

The inverse classification uses functions which are zero on a set and one off it.
Intersection closure uses a disjoint-piece sum, so neither subtraction nor additive
cancellation is needed. The index and factor universes are independent, and the index
need not be nonempty or finite.

The pure-ultrafilter and germ-kernel identities connect this construction to Mathlib's
existing evaluation and ultraproduct interfaces. Finite products have exactly the
labelled coordinate kernels; infinite products also have non-coordinate primes.

## References

This development uses Mathlib's ideal, prime spectrum, ultrafilter and germ APIs. Its
finite-product comparison is the coordinate-ideal viewpoint also used in
`MinimalPrimes.RingTheory.Ideal.MinimalPrimePi`.
-/

@[expose] public section

open Set Filter

universe u v w x

variable {ι : Type u}

namespace Ultrafilter

variable (A : ι → Type v) [∀ i, Semiring (A i)]

/-- Functions whose zero set belongs to an ultrafilter form a left ideal. -/
def piIdeal (U : Ultrafilter ι) : Ideal (Π i, A i) :=
  Filter.piIdeal A (U : Filter ι)

/-- The old ultrafilter construction is the general filter construction. -/
theorem piIdeal_eq_filter_piIdeal (U : Ultrafilter ι) :
    U.piIdeal A = (U : Filter ι).piIdeal A := rfl

/-- Membership in the ultrafilter ideal is exactly membership of the zero set. -/
@[simp]
theorem mem_piIdeal (U : Ultrafilter ι) (f : Π i, A i) :
    f ∈ U.piIdeal A ↔ {i | f i = 0} ∈ U := Iff.rfl

/-- The zero-set ideals of distinct ultrafilters have sum equal to the whole ideal. -/
theorem piIdeal_sup_eq_top_of_ne {U V : Ultrafilter ι} (hUV : U ≠ V) :
    U.piIdeal A ⊔ V.piIdeal A = ⊤ := by
  have hdisj : Disjoint (U : Filter ι) (V : Filter ι) :=
    disjoint_iff_not_le.mpr fun hle => hUV (coe_le_coe.mp hle)
  change (U : Filter ι).piIdeal A ⊔ (V : Filter ι).piIdeal A = ⊤
  rw [← Filter.piIdeal_inf A, hdisj.eq_bot, Filter.piIdeal_bot]

/-- A dependent index map and fibrewise homomorphisms pull back the zero-set ideal
along the stock product homomorphism. Division semiring sources and nontrivial
semiring targets suffice: the fibre maps automatically reflect zero. -/
theorem piIdeal_map_comap_piRingHom {κ : Type w}
    (K : ι → Type v) [∀ i, DivisionSemiring (K i)]
    {L : κ → Type x} [∀ j, Semiring (L j)] [∀ j, Nontrivial (L j)]
    (g : κ → ι) (U : Ultrafilter κ) (φ : ∀ j, K (g j) →+* L j) :
    (U.map g).piIdeal K = (U.piIdeal L).comap
      (RingHom.pi fun j => (φ j).comp (Pi.evalRingHom K (g j))) := by
  ext r
  change {i | r i = 0} ∈ U.map g ↔ {j | φ j (r (g j)) = 0} ∈ U
  rw [Ultrafilter.mem_map]
  change {j | r (g j) = 0} ∈ U ↔ {j | φ j (r (g j)) = 0} ∈ U
  simp only [map_eq_zero]

/-- The zero-set ideal is proper exactly when the nontrivial factors form a member
of the ultrafilter. This criterion allows arbitrary semiring factors. -/
theorem piIdeal_ne_top_iff (U : Ultrafilter ι) :
    U.piIdeal A ≠ ⊤ ↔ {i | Nontrivial (A i)} ∈ U := by
  have hbot : Ideal.pi (fun i => (⊥ : Ideal (A i))) = ⊥ := by
    ext f
    simp only [Ideal.mem_pi, Ideal.mem_bot]
    exact funext_iff.symm
  have htop : {i | (⊥ : Ideal (A i)) = ⊤} = {i | Nontrivial (A i)}ᶜ := by
    ext i
    change (⊥ : Ideal (A i)) = ⊤ ↔ ¬ Nontrivial (A i)
    rw [Ideal.eq_top_iff_one, Ideal.mem_bot]
    constructor
    · intro h hnt
      let := hnt
      exact one_ne_zero h
    · intro h
      let : Subsingleton (A i) := not_nontrivial_iff_subsingleton.mp h
      exact Subsingleton.elim _ _
  simpa [hbot, piIdeal_eq_filter_piIdeal, htop] using
    (Filter.pi_sup_piIdeal_ne_top_iff (fun i => (⊥ : Ideal (A i))) (U : Filter ι))

instance piIdeal_isPrime [∀ i, Nontrivial (A i)] [∀ i, NoZeroDivisors (A i)]
    (U : Ultrafilter ι) : (U.piIdeal A).IsPrime where
  ne_top' := by
    intro h
    have h1 : (1 : Π i, A i) ∈ U.piIdeal A := h.symm ▸ Submodule.mem_top
    simp at h1
  mem_or_mem' := by
    intro f g h
    have hz : {i | (f * g) i = 0} = {i | f i = 0} ∪ {i | g i = 0} := by
      ext i
      simp only [Pi.mul_apply, mem_ofPred_eq, mem_union, mul_eq_zero]
    rw [mem_piIdeal, hz, Ultrafilter.union_mem_iff] at h
    exact h.imp (mem_piIdeal A U f).2 (mem_piIdeal A U g).2

/-- A pure ultrafilter gives the kernel of coordinate evaluation. -/
@[simp]
theorem piIdeal_pure (i : ι) :
    (pure i : Ultrafilter ι).piIdeal A = RingHom.ker (Pi.evalRingHom A i) := by
  ext f
  simp [RingHom.mem_ker]

/-- The dependent section homomorphism has the existing ultrafilter zero-set ideal as kernel.
For semifield fibres this is the prime ideal of the product-spectrum correspondence. -/
theorem piIdeal_eq_ker_productMk (U : Ultrafilter ι) :
    U.piIdeal A = RingHom.ker (Filter.productRingCon (U : Filter ι) A).mk' :=
  Filter.piIdeal_eq_ker_productMk A (U : Filter ι)

/-- For a constant family, the ultrafilter ideal is the kernel of the existing germ map. -/
theorem piIdeal_eq_ker_coeRingHom (R : Type v) [Semiring R] (U : Ultrafilter ι) :
    U.piIdeal (fun _ : ι => R) = RingHom.ker (Filter.Germ.coeRingHom (R := R) (U : Filter ι)) :=
  Filter.piIdeal_eq_ker_coeRingHom R (U : Filter ι)

/-- A finitely supported function belongs to the ideal of the cofinite ultrafilter. -/
theorem mem_piIdeal_hyperfilter_of_finite_support [Infinite ι] (f : Π i, A i)
    (hf : {i | f i ≠ 0}.Finite) : f ∈ (Filter.hyperfilter ι).piIdeal A := by
  rw [mem_piIdeal]
  simpa only [Set.compl_ofPred, not_not] using hf.compl_mem_hyperfilter

/-- Extremality in the ideal/filter order isomorphism makes every ultrafilter
zero-set ideal maximal, already for division semiring fibres. -/
instance piIdeal_isMaximal (K : ι → Type v) [∀ i, DivisionSemiring (K i)]
    (U : Ultrafilter ι) : (U.piIdeal K).IsMaximal := by
  apply Ideal.isMaximal_def.mpr
  exact ((Ideal.piOrderIsoFilter K).symm.isCoatom_iff
    (OrderDual.toDual (U : Filter ι))).2 U.isAtom

end Ultrafilter

end

public section

universe u v

variable {ι : Type u}

namespace PrimeSpectrum

section CommSemiring

variable (R : ι → Type v) [∀ i, CommSemiring (R i)]

/-- The ultrafilter coordinate of a prime of an arbitrary dependent semiring product.
Its underlying filter is the original characteristic-test filter of the prime ideal. -/
@[expose]
noncomputable def piUltrafilterMap (p : PrimeSpectrum (Π i, R i)) : Ultrafilter ι :=
  Ultrafilter.ofComplNotMemIff (p.asIdeal.piFilter R)
    (Ideal.compl_notMem_piFilter R p.asIdeal)

/-- The coordinate retains the existing ideal-to-filter construction. -/
@[simp]
theorem coe_piUltrafilterMap (p : PrimeSpectrum (Π i, R i)) :
    (piUltrafilterMap R p : Filter ι) = p.asIdeal.piFilter R := rfl

open Classical in
/-- Membership is detected by nonmembership of the one-on-set, zero-off-set function.
No zero-set equality or nontriviality assumption on the factors is needed. -/
theorem mem_piUltrafilterMap (p : PrimeSpectrum (Π i, R i)) (s : Set ι) :
    s ∈ piUltrafilterMap R p ↔
      (fun i ↦ if i ∈ s then (1 : R i) else 0) ∉ p.asIdeal := by
  have hmem : sᶜ ∈ piUltrafilterMap R p ↔
      (fun i ↦ if i ∈ s then (1 : R i) else 0) ∈ p.asIdeal := by
    change sᶜ ∈ p.asIdeal.piFilter R ↔ _
    rw [Ideal.mem_piFilter]
    constructor
    · rintro ⟨f, hf, hzero, hone⟩
      have he : f = (fun i ↦ if i ∈ s then (1 : R i) else 0) := by
        funext i
        by_cases hi : i ∈ s
        · simpa [hi] using hone i (by simpa using hi)
        · simpa [hi] using hzero i hi
      exact he ▸ hf
    · intro hf
      refine ⟨_, hf, ?_, ?_⟩
      · intro i hi
        simp only [Set.mem_compl_iff] at hi
        simp [hi]
      · intro i hi
        have his : i ∈ s := by simpa only [Set.mem_compl_iff, not_not] using hi
        simp [his]
  exact Ultrafilter.compl_notMem_iff.symm.trans (not_congr hmem)

/-- The zero-set ideal is contained in a prime precisely when its coordinate is the
specified ultrafilter, including when some or all factors are zero semirings. -/
theorem piIdeal_le_asIdeal_iff_piUltrafilterMap_eq (U : Ultrafilter ι)
    (p : PrimeSpectrum (Π i, R i)) :
    U.piIdeal R ≤ p.asIdeal ↔ piUltrafilterMap R p = U := by
  change (U : Filter ι).piIdeal R ≤ p.asIdeal ↔ _
  rw [Ideal.piIdeal_le_iff_piFilter_le]
  change (piUltrafilterMap R p : Filter ι) ≤ (U : Filter ι) ↔ _
  exact Ultrafilter.coe_le_coe

/-- An ultrafilter occurs as a prime's coordinate exactly when it contains the set
of nontrivial factors. No nontriviality assumption on the whole family is needed. -/
theorem mem_range_piUltrafilterMap (U : Ultrafilter ι) :
    U ∈ Set.range (piUltrafilterMap R) ↔ {i | Nontrivial (R i)} ∈ U := by
  constructor
  · rintro ⟨p, hp⟩
    apply (Ultrafilter.piIdeal_ne_top_iff R U).1
    have hle := (piIdeal_le_asIdeal_iff_piUltrafilterMap_eq R U p).2 hp
    intro htop
    apply p.isPrime.ne_top
    apply top_unique
    rw [← htop]
    exact hle
  · intro hU
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (U.piIdeal R)
      ((Ultrafilter.piIdeal_ne_top_iff R U).2 hU)
    exact ⟨⟨M, hM.isPrime⟩,
      (piIdeal_le_asIdeal_iff_piUltrafilterMap_eq R U ⟨M, hM.isPrime⟩).1 hle⟩

/-- The exact image of the ultrafilter coordinate map for arbitrary commutative
semiring factors. -/
theorem range_piUltrafilterMap :
    Set.range (piUltrafilterMap R) = {U | {i | Nontrivial (R i)} ∈ U} := by
  ext U
  exact mem_range_piUltrafilterMap R U

/-- The ultrafilter coordinate map is surjective exactly when every factor is
nontrivial, including the vacuous case of an empty index type. -/
theorem piUltrafilterMap_surjective_iff :
    Function.Surjective (piUltrafilterMap R) ↔ ∀ i, Nontrivial (R i) := by
  constructor
  · intro h i
    exact Ultrafilter.mem_pure.1 ((mem_range_piUltrafilterMap R (pure i)).1 (h _))
  · intro h U
    apply (mem_range_piUltrafilterMap R U).2
    have hD : {i | Nontrivial (R i)} = Set.univ := Set.eq_univ_of_forall h
    rw [hD]
    exact Filter.univ_mem

end CommSemiring

variable (K : ι → Type v) [∀ i, Semifield (K i)]

/-- The ultrafilter associated to a prime ideal of a dependent product of semifields. -/
@[expose]
noncomputable def piUltrafilter (p : PrimeSpectrum (Π i, K i)) : Ultrafilter ι :=
  piUltrafilterMap K p

/-- The general coordinate specializes to the original semifield entry point. -/
@[simp]
theorem piUltrafilterMap_eq_piUltrafilter :
    piUltrafilterMap K = piUltrafilter K := rfl

/-- The old prime classification uses the filter of the general all-ideal construction. -/
@[simp]
theorem coe_piUltrafilter (p : PrimeSpectrum (Π i, K i)) :
    (p.piUltrafilter K : Filter ι) = p.asIdeal.piFilter K := rfl

/-- A zero set belongs to the associated ultrafilter exactly when its function is in the prime. -/
@[simp]
theorem zeroSet_mem_piUltrafilter (p : PrimeSpectrum (Π i, K i)) (f : Π i, K i) :
    {i | f i = 0} ∈ p.piUltrafilter K ↔ f ∈ p.asIdeal :=
  Ideal.zeroSet_mem_piFilter K p.asIdeal f

/-- The all-set membership law: members contain the zero set of a function in the prime. -/
theorem mem_piUltrafilter (p : PrimeSpectrum (Π i, K i)) (s : Set ι) :
    s ∈ p.piUltrafilter K ↔ ∃ f : Π i, K i, f ∈ p.asIdeal ∧ {i | f i = 0} ⊆ s :=
  Ideal.mem_piFilter_iff_exists_zeroSet K p.asIdeal s

/-- Recovering a prime's ideal from its associated ultrafilter. -/
@[simp]
theorem piIdeal_piUltrafilter (p : PrimeSpectrum (Π i, K i)) :
    (p.piUltrafilter K).piIdeal K = p.asIdeal := by
  ext f
  exact zeroSet_mem_piUltrafilter K p f

/-- Recovering an ultrafilter from its prime ideal. -/
@[simp]
theorem piUltrafilter_piIdeal (U : Ultrafilter ι) :
    piUltrafilter K ⟨U.piIdeal K, inferInstance⟩ = U := by
  apply Ultrafilter.ext
  intro s
  change s ∈ ((U : Filter ι).piIdeal K).piFilter K ↔ s ∈ (U : Filter ι)
  rw [Ideal.piFilter_piIdeal]

/-- Prime ideals of an arbitrary dependent product of semifields are classified by ultrafilters. -/
@[expose]
noncomputable def piEquivUltrafilter : PrimeSpectrum (Π i, K i) ≃ Ultrafilter ι where
  toFun := piUltrafilter K
  invFun U := ⟨U.piIdeal K, inferInstance⟩
  left_inv p := PrimeSpectrum.ext (piIdeal_piUltrafilter K p)
  right_inv := piUltrafilter_piIdeal K

/-- The classification sends a prime to its zero-set ultrafilter. -/
@[simp]
theorem piEquivUltrafilter_apply (p : PrimeSpectrum (Π i, K i)) :
    piEquivUltrafilter K p = p.piUltrafilter K := rfl

/-- The inverse classification has the prescribed zero-set ideal. -/
@[simp]
theorem piEquivUltrafilter_symm_asIdeal (U : Ultrafilter ι) :
    ((piEquivUltrafilter K).symm U).asIdeal = U.piIdeal K := rfl

/-- The zero-set construction distinguishes ultrafilters. -/
theorem piIdeal_injective : Function.Injective (fun U : Ultrafilter ι => U.piIdeal K) := by
  intro U V h
  have hp : (piEquivUltrafilter K).symm U = (piEquivUltrafilter K).symm V :=
    PrimeSpectrum.ext h
  exact (piEquivUltrafilter K).symm.injective hp

/-- In a finite product, every prime is a uniquely labelled coordinate kernel. -/
theorem existsUnique_ker_evalRingHom [Finite ι] (p : PrimeSpectrum (Π i, K i)) :
    ∃! i, p.asIdeal = RingHom.ker (Pi.evalRingHom K i) := by
  obtain ⟨i, hi⟩ := Ultrafilter.eq_pure_of_finite (p.piUltrafilter K)
  have hpi : p.asIdeal = RingHom.ker (Pi.evalRingHom K i) := by
    rw [← piIdeal_piUltrafilter K p, hi, Ultrafilter.piIdeal_pure]
  refine ⟨i, hpi, ?_⟩
  intro j hj
  apply Ultrafilter.pure_injective
  apply piIdeal_injective K
  simpa only [Ultrafilter.piIdeal_pure] using hj.symm.trans hpi

/-- On an infinite index type, the cofinite ultrafilter ideal is not a coordinate kernel. -/
theorem piIdeal_hyperfilter_ne_ker_evalRingHom [Infinite ι] (i : ι) :
    (Filter.hyperfilter ι).piIdeal K ≠ RingHom.ker (Pi.evalRingHom K i) := by
  intro h
  have hu : Filter.hyperfilter ι = (pure i : Ultrafilter ι) :=
    piIdeal_injective K (h.trans (Ultrafilter.piIdeal_pure K i).symm)
  have hs : ({i} : Set ι) ∈ Filter.hyperfilter ι := by simp [hu]
  exact Filter.notMem_hyperfilter_of_finite (Set.finite_singleton i) hs

end PrimeSpectrum
