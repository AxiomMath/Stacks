module

import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import StacksFrontier.RingTheory.LocalCohomology.MinimalPrimeFiltration.ChangeOfSupport
public import StacksFrontier.RingTheory.Spectrum.Prime.NonminimalPrimes
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Closed-support representatives of local cohomology classes

Over a Noetherian ring `A`, local cohomology with support in a specialization-stable subset `T`
of `Spec(A)` is the filtered colimit of local cohomology with support in the closed subsets
`V(I) ⊆ T`. Since the forgetful functor to types preserves this colimit, the colimit can be
computed elementwise: every class in `H^i_T(K)` already comes from a class with closed support,
a class with closed support dying in `H^i_T(K)` already dies at a larger closed support, and
consequently a class annihilated by a finitely generated ideal has a closed-support
representative annihilated by the same ideal.

## Main results

* `Stacks.LocalCohomology.exists_closedSupport_representative` — every class has a
  closed-support representative.
* `Stacks.LocalCohomology.exists_closedSupport_map_eq_zero` — a closed-support class vanishing
  in `H^i_T(K)` vanishes at some larger closed support.
* `Stacks.LocalCohomology.exists_closedSupport_representative_annihilated` — a representative
  can be chosen with the same annihilating ideal.
* `Stacks.LocalCohomology.finite_minimalSupportPrimes_in_closedSupport` — a closed subset of `T`
  contains only finitely many primes that are minimal in `T`.

## References

* [Stacks Project, Tag 0EF8](https://stacks.math.columbia.edu/tag/0EF8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.LocalCohomology

/-- The forgetful functor from modules over `A` to types preserves filtered colimits indexed by
a small category living in the universe of `A`. -/
instance forget_preserves_smallFilteredColimit {A : Type u} [CommRing A] {J : Type u}
    [SmallCategory J] [IsFiltered J] (F : J ⥤ ModuleCat.{max u v} A) :
    PreservesColimit F (forget (ModuleCat.{max u v} A)) := by
  have hbig : PreservesFilteredColimitsOfSize.{max u v, max u v}
      (forget (ModuleCat.{max u v} A)) := by
    change PreservesFilteredColimitsOfSize
      (forget₂ (ModuleCat.{max u v} A) AddCommGrpCat.{max u v} ⋙ forget _)
    infer_instance
  have hsmall : PreservesFilteredColimitsOfSize.{u, u} (forget (ModuleCat.{max u v} A)) :=
    preservesFilteredColimitsOfSize_of_univLE.{max u v, max u v, u, u} _
  infer_instance

/-- Every class in local cohomology with support in `T` is the image of a class in local
cohomology with support in a closed subset `V(I) ⊆ T`. -/
theorem exists_closedSupport_representative (A : Type u) [CommRing A] [IsNoetherianRing A]
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (K : DerivedCategory (ModuleCat.{max u v} A)) (i : ℤ)
    (x : localCohomologyWithSupportIn A T K i) :
    ∃ (J : ClosedSupportIdeal A T)
      (y : localCohomologyWithSupportIn A (ClosedSupportIdeal.support A J) K i),
      (changeOfSupport A (OrderDual.ofDual J).2 K i).hom y = x :=
  Concrete.isColimit_exists_rep _ (isColimit_closedSupportCocone.{u, v} A T hT i K) x

/-- A class with closed support `V(I) ⊆ T` which vanishes in local cohomology with support in
`T` already vanishes in local cohomology with support in some larger closed subset of `T`. -/
theorem exists_closedSupport_map_eq_zero (A : Type u) [CommRing A] [IsNoetherianRing A]
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (K : DerivedCategory (ModuleCat.{max u v} A)) (i : ℤ) (J : ClosedSupportIdeal A T)
    (y : localCohomologyWithSupportIn A (ClosedSupportIdeal.support A J) K i)
    (hy : (changeOfSupport A (OrderDual.ofDual J).2 K i).hom y = 0) :
    ∃ (L : ClosedSupportIdeal A T) (h : J ≤ L),
      (changeOfSupport A (PrimeSpectrum.zeroLocus_anti_mono_ideal h) K i).hom y = 0 := by
  have hzero : (changeOfSupport.{u, v} A (OrderDual.ofDual J).2 K i).hom
      (0 : localCohomologyWithSupportIn A (ClosedSupportIdeal.support A J) K i) = 0 := map_zero _
  obtain ⟨L, f, g, h⟩ :=
    (Concrete.isColimit_rep_eq_iff_exists _ (isColimit_closedSupportCocone.{u, v} A T hT i K)
      y 0).mp (hy.trans hzero.symm)
  refine ⟨L, leOfHom f, ?_⟩
  have h' : (changeOfSupport.{u, v} A
        (PrimeSpectrum.zeroLocus_anti_mono_ideal (leOfHom f)) K i).hom y =
      (changeOfSupport.{u, v} A
        (PrimeSpectrum.zeroLocus_anti_mono_ideal (leOfHom g)) K i).hom 0 := h
  exact h'.trans (map_zero _)

/-- If an ideal `D` annihilates a class in local cohomology with support in `T`, then the class
has a closed-support representative which is again annihilated by `D`. -/
theorem exists_closedSupport_representative_annihilated (A : Type u) [CommRing A]
    [IsNoetherianRing A] (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (K : DerivedCategory (ModuleCat.{max u v} A)) (i : ℤ)
    (x : localCohomologyWithSupportIn A T K i) (D : Ideal A) (hD : ∀ a ∈ D, a • x = 0) :
    ∃ (J : ClosedSupportIdeal A T)
      (y : localCohomologyWithSupportIn A (ClosedSupportIdeal.support A J) K i),
      (changeOfSupport A (OrderDual.ofDual J).2 K i).hom y = x ∧ ∀ a ∈ D, a • y = 0 := by
  classical
  obtain ⟨s, hs⟩ := Ideal.fg_of_isNoetherianRing D
  have hfinite : ∀ t : Finset A, (∀ a ∈ t, a • x = 0) →
      ∃ (J : ClosedSupportIdeal A T)
        (y : localCohomologyWithSupportIn A (ClosedSupportIdeal.support A J) K i),
        (changeOfSupport A (OrderDual.ofDual J).2 K i).hom y = x ∧ ∀ a ∈ t, a • y = 0 := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro _
      obtain ⟨J, y, hy⟩ := exists_closedSupport_representative.{u, v} A T hT K i x
      exact ⟨J, y, hy, fun a ha => (Finset.notMem_empty a ha).elim⟩
    | @insert a t ha ih =>
      intro hx
      obtain ⟨J, y, hy, hyt⟩ := ih fun b hb => hx b (Finset.mem_insert_of_mem hb)
      have hay : (changeOfSupport.{u, v} A (OrderDual.ofDual J).2 K i).hom (a • y) = 0 := by
        rw [map_smul, hy]
        exact hx a (Finset.mem_insert_self _ _)
      obtain ⟨L, hJL, haL⟩ := exists_closedSupport_map_eq_zero.{u, v} A T hT K i J (a • y) hay
      refine ⟨L, (changeOfSupport.{u, v} A
        (PrimeSpectrum.zeroLocus_anti_mono_ideal hJL) K i).hom y, ?_, ?_⟩
      · refine Eq.trans ?_ hy
        exact congrArg (fun φ => (ModuleCat.Hom.hom φ) y) (changeOfSupport_trans.{u, v} A
          (PrimeSpectrum.zeroLocus_anti_mono_ideal hJL) (OrderDual.ofDual L).2 K i)
      · intro b hb
        refine (map_smul _ b y).symm.trans ?_
        rcases Finset.mem_insert.mp hb with rfl | hb
        · exact haL
        · rw [hyt b hb]
          exact map_zero _
  obtain ⟨J, y, hy, hys⟩ := hfinite s fun a ha => hD a (hs ▸ Submodule.subset_span ha)
  refine ⟨J, y, hy, ?_⟩
  have hle : D ≤ LinearMap.ker (LinearMap.toSpanSingleton A _ y) := by
    rw [← hs]
    exact Submodule.span_le.mpr hys
  exact fun a ha => hle ha

/-- A Noetherian ring has only finitely many primes that are minimal in `T` and contain a given
ideal whose zero locus lies in `T`. -/
@[ega "0 1.1.1" "more general"]
theorem finite_minimalSupportPrimes_in_closedSupport {A : Type u} [CommRing A]
    [IsNoetherianRing A] (T : Set (PrimeSpectrum A)) (I : Ideal A)
    (hI : PrimeSpectrum.zeroLocus (I : Set A) ⊆ T) :
    {p : PrimeSpectrum A | p ∈ T \ PrimeSpectrum.nonminimalPrimes T ∧
      p ∈ PrimeSpectrum.zeroLocus (I : Set A)}.Finite := by
  classical
  let toSpectrum : {q : Ideal A // q ∈ I.minimalPrimes} → PrimeSpectrum A := fun q =>
    ⟨q.1, Ideal.IsMinimalPrime.isPrime q.2⟩
  have hfin : Finite {q : Ideal A // q ∈ I.minimalPrimes} :=
    (Ideal.finite_minimalPrimes_of_isNoetherianRing A I).to_subtype
  refine (Set.finite_range toSpectrum).subset ?_
  rintro p ⟨⟨hpT, hpnot⟩, hpI⟩
  obtain ⟨q, hqmin, hqp⟩ :=
    Ideal.exists_minimalPrimes_le ((PrimeSpectrum.mem_zeroLocus p (I : Set A)).mp hpI)
  have hqT : toSpectrum ⟨q, hqmin⟩ ∈ T :=
    hI ((PrimeSpectrum.mem_zeroLocus _ (I : Set A)).mpr (Ideal.IsMinimalPrime.le hqmin))
  have hqle : toSpectrum ⟨q, hqmin⟩ ≤ p := hqp
  exact ⟨⟨q, hqmin⟩, hqle.eq_of_not_lt fun h => hpnot ⟨hpT, _, hqT, h⟩⟩

end Stacks.LocalCohomology

end
