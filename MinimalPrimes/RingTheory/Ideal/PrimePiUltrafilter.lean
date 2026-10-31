/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Order.Filter.FilterProduct
public import Mathlib.Order.Filter.Ultrafilter.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Spectrum.Prime.Defs

/-!
# Prime ideals of products of semifields

`Ultrafilter.piIdeal` assigns to an ultrafilter the ideal of functions whose zero set
belongs to it. The construction works for semiring factors; it is prime for nontrivial
factors without zero divisors. For an arbitrary dependent family of semifields,
`PrimeSpectrum.piEquivUltrafilter` classifies all prime ideals by ultrafilters.

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

universe u v

variable {ι : Type u}

namespace Ultrafilter

variable (A : ι → Type v) [∀ i, Semiring (A i)]

/-- Functions whose zero set belongs to an ultrafilter form a left ideal. -/
def piIdeal (U : Ultrafilter ι) : Ideal (Π i, A i) where
  carrier := {f | {i | f i = 0} ∈ U}
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

/-- Membership in the ultrafilter ideal is exactly membership of the zero set. -/
@[simp]
theorem mem_piIdeal (U : Ultrafilter ι) (f : Π i, A i) :
    f ∈ U.piIdeal A ↔ {i | f i = 0} ∈ U := Iff.rfl

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

/-- For a constant family, the ultrafilter ideal is the kernel of the existing germ map. -/
theorem piIdeal_eq_ker_coeRingHom (R : Type v) [Semiring R] (U : Ultrafilter ι) :
    U.piIdeal (fun _ : ι => R) = RingHom.ker (Filter.Germ.coeRingHom (R := R) (U : Filter ι)) := by
  ext f
  rw [mem_piIdeal, RingHom.mem_ker]
  change {i | f i = 0} ∈ U ↔
    (f : Filter.Germ (U : Filter ι) R) = ((0 : ι → R) : Filter.Germ (U : Filter ι) R)
  exact Filter.Germ.coe_eq.symm

/-- A finitely supported function belongs to the ideal of the cofinite ultrafilter. -/
theorem mem_piIdeal_hyperfilter_of_finite_support [Infinite ι] (f : Π i, A i)
    (hf : {i | f i ≠ 0}.Finite) : f ∈ (Filter.hyperfilter ι).piIdeal A := by
  rw [mem_piIdeal]
  simpa only [Set.compl_ofPred, not_not] using hf.compl_mem_hyperfilter

end Ultrafilter

end

public section

universe u v

variable {ι : Type u}

namespace PrimeSpectrum

variable (K : ι → Type v) [∀ i, Semifield (K i)]

private noncomputable def zeroTest (s : Set ι) : Π i, K i := by
  classical
  exact fun i => if i ∈ s then 0 else 1

private theorem zeroTest_zeroSet (s : Set ι) :
    {i | zeroTest K s i = 0} = s := by
  classical
  ext i
  by_cases hi : i ∈ s <;> simp [zeroTest, hi]

private theorem zeroTest_mem_mono (p : PrimeSpectrum (Π i, K i))
    {s t : Set ι} (hs : zeroTest K s ∈ p.asIdeal) (hst : s ⊆ t) :
    zeroTest K t ∈ p.asIdeal := by
  classical
  have he : zeroTest K t = zeroTest K t * zeroTest K s := by
    ext i
    by_cases hs : i ∈ s
    · simp [zeroTest, hs, hst hs]
    · simp [zeroTest, hs]
  rw [he]
  exact p.asIdeal.mul_mem_left _ hs

private theorem zeroTest_mem_inter (p : PrimeSpectrum (Π i, K i))
    {s t : Set ι} (hs : zeroTest K s ∈ p.asIdeal) (ht : zeroTest K t ∈ p.asIdeal) :
    zeroTest K (s ∩ t) ∈ p.asIdeal := by
  classical
  have he : zeroTest K (s ∩ t) = zeroTest K s + zeroTest K sᶜ * zeroTest K t := by
    ext i
    by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;> simp [zeroTest, hs, ht]
  rw [he]
  exact p.asIdeal.add_mem hs (p.asIdeal.mul_mem_left _ ht)

private theorem zeroTest_compl_notMem_iff (p : PrimeSpectrum (Π i, K i)) (s : Set ι) :
    zeroTest K sᶜ ∉ p.asIdeal ↔ zeroTest K s ∈ p.asIdeal := by
  classical
  have hm : zeroTest K s * zeroTest K sᶜ = 0 := by
    ext i
    by_cases hi : i ∈ s <;> simp [zeroTest, hi]
  have ha : zeroTest K s + zeroTest K sᶜ = 1 := by
    ext i
    by_cases hi : i ∈ s <;> simp [zeroTest, hi]
  constructor
  · intro h
    exact (p.isPrime.mem_or_mem_of_mul_eq_zero hm).resolve_right h
  · intro hs hc
    exact p.isPrime.one_notMem (ha ▸ p.asIdeal.add_mem hs hc)

/-- The ultrafilter associated to a prime ideal of a dependent product of semifields. -/
noncomputable def piUltrafilter (p : PrimeSpectrum (Π i, K i)) : Ultrafilter ι :=
  Ultrafilter.ofComplNotMemIff
    { sets := {s | zeroTest K s ∈ p.asIdeal}
      univ_sets := by
        have he : zeroTest K Set.univ = 0 := by
          classical
          ext i
          simp [zeroTest]
        change zeroTest K Set.univ ∈ p.asIdeal
        rw [he]
        exact p.asIdeal.zero_mem
      sets_of_superset := fun hs hst => zeroTest_mem_mono K p hs hst
      inter_sets := fun hs ht => zeroTest_mem_inter K p hs ht }
    (zeroTest_compl_notMem_iff K p)

/-- A zero set belongs to the associated ultrafilter exactly when its function is in the prime. -/
@[simp]
theorem zeroSet_mem_piUltrafilter (p : PrimeSpectrum (Π i, K i)) (f : Π i, K i) :
    {i | f i = 0} ∈ p.piUltrafilter K ↔ f ∈ p.asIdeal := by
  classical
  change zeroTest K {i | f i = 0} ∈ p.asIdeal ↔ f ∈ p.asIdeal
  have he : zeroTest K {i | f i = 0} = (fun i => (f i)⁻¹) * f := by
    ext i
    by_cases hi : f i = 0
    · simp [zeroTest, hi]
    · simp [zeroTest, hi]
  have hf : f = f * zeroTest K {i | f i = 0} := by
    ext i
    by_cases hi : f i = 0 <;> simp [zeroTest, hi]
  constructor
  · intro h
    exact hf.symm ▸ p.asIdeal.mul_mem_left f h
  · intro h
    rw [he]
    exact p.asIdeal.mul_mem_left _ h

/-- The all-set membership law: members contain the zero set of a function in the prime. -/
theorem mem_piUltrafilter (p : PrimeSpectrum (Π i, K i)) (s : Set ι) :
    s ∈ p.piUltrafilter K ↔ ∃ f : Π i, K i, f ∈ p.asIdeal ∧ {i | f i = 0} ⊆ s := by
  constructor
  · intro hs
    exact ⟨zeroTest K s, hs, (zeroTest_zeroSet K s).subset⟩
  · rintro ⟨f, hf, hfs⟩
    exact Filter.mem_of_superset ((zeroSet_mem_piUltrafilter K p f).2 hf) hfs

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
  change zeroTest K s ∈ U.piIdeal K ↔ s ∈ U
  rw [Ultrafilter.mem_piIdeal, zeroTest_zeroSet]

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
