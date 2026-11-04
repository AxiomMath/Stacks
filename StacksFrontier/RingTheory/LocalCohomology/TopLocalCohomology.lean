module

public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import StacksFrontier.Algebra.Homology.DerivedCategory.ProjectiveCorepresents
public import StacksFrontier.Algebra.Module.InjectiveHull.Basic
public import StacksFrontier.RingTheory.AdicCompletion.PermanenceOfProperties
public import StacksFrontier.RingTheory.Dualizing.CoextendRestrictComparison.HomologyExt
public import StacksFrontier.RingTheory.Dualizing.LocalCohomology.LocalDualityExt
public import StacksFrontier.RingTheory.Dualizing.MinimalPrimeNonvanishing
public import StacksFrontier.RingTheory.Dualizing.UbiquityCompleteLocal
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.Normalized
public import StacksFrontier.RingTheory.LocalCohomology.CohomologicalDimension.ChangeOfRings
public import StacksFrontier.RingTheory.LocalCohomology.DimensionBoundUnconditional
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Top local cohomology of a Noetherian local ring

Let `(A, 𝔪)` be a Noetherian local ring of dimension `d`. Then `H^d_𝔪(A)` is nonzero and the
cohomological dimension `cd(A, 𝔪)` of Stacks 0DX8 equals `d`.

## Main results

* `Stacks.LocalCohomology.cohomologicalDimension_eq_iff_not_isZero_localCohomologyModule` — above
  a vanishing bound `d`, the cohomological dimension is `d` exactly when `H^d_{V(I)}(A) ≠ 0`.
* `Stacks.LocalCohomology.extSingleRegularLinearEquivHomology` — `Ext^i_A(A, K) = H^i(K)`.
* `Stacks.LocalCohomology.not_isZero_topLocalCohomologyModule_of_isNormalizedDualizingComplex`
  and
  `Stacks.LocalCohomology.cohomologicalDimension_maximalIdeal_eq_of_isNormalizedDualizingComplex`
  — both assertions of Stacks 0DXE for a ring carrying a normalized dualizing complex.
* `Stacks.LocalCohomology.not_isZero_topLocalCohomologyModule_maximalIdeal` and
  `Stacks.LocalCohomology.cohomologicalDimension_maximalIdeal_eq` — both assertions of
  Stacks 0DXE, for a Noetherian local ring whose completion carries a normalized dualizing
  complex.
* `Stacks.LocalCohomology.not_isZero_topLocalCohomologyModule_maximalIdeal'` and
  `Stacks.LocalCohomology.cohomologicalDimension_maximalIdeal_eq'` — both assertions of
  Stacks 0DXE as the source states them, for an arbitrary Noetherian local ring.
* `Stacks.LocalCohomology.exists_isNormalizedDualizingComplex_adicCompletion` — the completion
  of a Noetherian local ring carries a normalized dualizing complex.

## References

* [Stacks Project, Tag 0DXE](https://stacks.math.columbia.edu/tag/0DXE)
* [Stacks Project, Tag 0DXC](https://stacks.math.columbia.edu/tag/0DXC)
* [Stacks Project, Tag 0DXA](https://stacks.math.columbia.edu/tag/0DXA)
* [Stacks Project, Tag 0AAK](https://stacks.math.columbia.edu/tag/0AAK)
* [Stacks Project, Tag 0A7V](https://stacks.math.columbia.edu/tag/0A7V)
* [Stacks Project, Tag 0BFR](https://stacks.math.columbia.edu/tag/0BFR)
* [Stacks Project, Tag 07NV](https://stacks.math.columbia.edu/tag/07NV)
* [Stacks Project, Tag 00MC](https://stacks.math.columbia.edu/tag/00MC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.LocalCohomology

/-- Two equal ideals have the same cohomological dimension, whatever proofs of finite generation
they are presented with. -/
theorem cohomologicalDimension_congr {A : Type u} [CommRing A] {I J : Ideal A}
    (hI : I.FG) (hJ : J.FG) (h : I = J) :
    cohomologicalDimension A I hI = cohomologicalDimension A J hJ := by
  subst h
  rfl

/-- A cohomological dimension equal to `d ≥ 0` forces the local cohomology of `A` in degree `d`
to be nonzero. -/
theorem not_isZero_localCohomologyModule_of_cohomologicalDimension_eq
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) (d : ℤ) (hd : 0 ≤ d)
    (hcd : cohomologicalDimension A I hI = d) :
    ¬ IsZero (localCohomologyModule A I hI (ModuleCat.of A A) d) := by
  intro hz
  have hbound : IsLocalCohomologyBound A I hI (d - 1) := by
    refine ⟨by omega, fun i hi => ?_⟩
    rcases eq_or_lt_of_le (show d ≤ i by omega) with rfl | hlt
    · exact hz
    · have hcdlt : cohomologicalDimension A I hI < i := by rw [hcd]; omega
      exact (isLocalCohomologyBound_cohomologicalDimension A I hI).2 i hcdlt
  have hle := cohomologicalDimension_le A I hI (d - 1) hbound
  omega

/-- Conversely, below a vanishing bound `d`, nonvanishing in degree `d` forces the cohomological
dimension to be exactly `d`. -/
theorem cohomologicalDimension_eq_of_not_isZero_localCohomologyModule
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) (d : ℤ)
    (hle : cohomologicalDimension A I hI ≤ d)
    (hne : ¬ IsZero (localCohomologyModule A I hI (ModuleCat.of A A) d)) :
    cohomologicalDimension A I hI = d :=
  le_antisymm hle
    (not_lt.mp fun h => hne ((isLocalCohomologyBound_cohomologicalDimension A I hI).2 d h))

/-- Below a vanishing bound `d ≥ 0`, the cohomological dimension is `d` exactly when the local
cohomology of `A` in degree `d` is nonzero. -/
theorem cohomologicalDimension_eq_iff_not_isZero_localCohomologyModule
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) (d : ℤ) (hd : 0 ≤ d)
    (hle : cohomologicalDimension A I hI ≤ d) :
    cohomologicalDimension A I hI = d ↔
      ¬ IsZero (localCohomologyModule A I hI (ModuleCat.of A A) d) :=
  ⟨not_isZero_localCohomologyModule_of_cohomologicalDimension_eq A I hI d hd,
    cohomologicalDimension_eq_of_not_isZero_localCohomologyModule A I hI d hle⟩

/-- **Extensions of the regular module compute cohomology.** For an object `K` of the unbounded
derived category of `A`-modules, `Ext^i_A(A, K)` is the degree-`i` cohomology module of `K`. -/
def extSingleRegularLinearEquivHomology (A : Type u) [CommRing A]
    (K : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) :
    DerivedCategory.Ext
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) K i ≃ₗ[A]
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K :=
  letI : Projective (ModuleCat.of A A) :=
    ModuleCat.projective_of_free (Module.Free.chooseBasis A A)
  (Dualizing.extFromSingleEquiv A i (ModuleCat.of A A) K).symm.trans
    (((DerivedCategory.homologyFromSingleLinearEquiv (ModuleCat.of A A) K i A).trans
      ModuleCat.homLinearEquiv).trans (LinearMap.ringLmapEquivSelf A A _))

/-- A nonzero finite module over a Noetherian local ring has nonzero completion. -/
@[ega "0 7.6.4" "S = {1}"]
theorem nontrivial_adicCompletion_maximalIdeal (A : Type u) [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] (M : Type*) [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Nontrivial M] :
    Nontrivial (AdicCompletion (IsLocalRing.maximalIdeal A) M) :=
  (AdicCompletion.of_injective (IsLocalRing.maximalIdeal A) M).nontrivial

/-- The cohomology modules of the regular module placed in degree zero are finite: they are `A`
in degree zero and vanish elsewhere. -/
theorem finite_homology_singleFunctor_regular (A : Type u) [CommRing A] (j : ℤ) :
    Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A))) := by
  set K := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A) with hK
  by_cases hj : j = 0
  · subst hj
    have e := (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} A) 0).app
      (ModuleCat.of A A)
    let : Module.Finite A ((𝟭 (ModuleCat.{u} A)).obj (ModuleCat.of A A)) := by
      change Module.Finite A A
      infer_instance
    exact Module.Finite.equiv e.toLinearEquiv.symm
  · have hzero : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).obj K) := by
      let : K.IsGE 0 := by rw [hK]; infer_instance
      let : K.IsLE 0 := by rw [hK]; infer_instance
      exact if hj' : j < 0 then DerivedCategory.isZero_of_isGE K 0 j hj'
        else DerivedCategory.isZero_of_isLE K 0 j (by omega)
    let : Subsingleton ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).obj K) :=
      ModuleCat.isZero_iff_subsingleton.mp hzero
    exact Module.Finite.of_surjective
      (0 : A →ₗ[A] ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).obj K))
      fun x => ⟨0, Subsingleton.elim _ _⟩

/-- Let `(A, 𝔪)` be a Noetherian local ring of dimension `d` carrying a normalized dualizing
complex. Then `H^d_𝔪(A)` is nonzero. -/
@[sga "2 V 3.1" "(iii), special case"]
theorem not_isZero_topLocalCohomologyModule_of_isNormalizedDualizingComplex
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hm : (IsLocalRing.maximalIdeal A).FG)
    (d : ℕ) (hdim : ringKrullDim A = (d : WithBot ℕ∞))
    (ω : DerivedCategory (ModuleCat.{u} A))
    (hω : Dualizing.IsNormalizedDualizingComplex.{u, u} ω) :
    ¬ IsZero (localCohomologyModule A (IsLocalRing.maximalIdeal A) hm
      (ModuleCat.of A A) (d : ℤ)) := by
  classical
  obtain ⟨p, hp, hdimp⟩ := Dualizing.exists_minimalPrime_ringKrullDim_quotient_eq (A := A) d hdim
  let : p.asIdeal.IsPrime := hp.isPrime
  obtain ⟨s, hs⟩ := id hm
  obtain ⟨f, hf⟩ := Stacks.ArithmeticRank.exists_range_eq_coe s
  have hspan : Ideal.span (Set.range f) = IsLocalRing.maximalIdeal A := by rw [hf, hs]
  obtain ⟨E, iE, hmono, hhull⟩ := Module.exists_isInjectiveHull A
    ((ModuleCat.uliftFunctor.{u} A).obj (ModuleCat.of A (IsLocalRing.ResidueField A)))
  set K := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A) with hKdef
  have hHom : Nontrivial
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(d : ℤ))).obj ω) := by
    have hloc := (Dualizing.nontrivial_localized_homology_iff_eq_neg_dimension
      ω hω p hp d hdimp (-(d : ℤ))).2 rfl
    by_contra hcon
    rw [not_nontrivial_iff_subsingleton] at hcon
    exact not_nontrivial _ hloc
  let e := extSingleRegularLinearEquivHomology A ω (-(d : ℤ))
  have hExt : Nontrivial (DerivedCategory.Ext K ω (-(d : ℤ))) :=
    e.toEquiv.nontrivial_congr.mpr hHom
  let : Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A)
      (-(d : ℤ))).obj ω) := hω.1.finiteCohomology (-(d : ℤ))
  let : Module.Finite A (DerivedCategory.Ext K ω (-(d : ℤ))) := Module.Finite.equiv e.symm
  have hcompl : Nontrivial
      (AdicCompletion (IsLocalRing.maximalIdeal A) (DerivedCategory.Ext K ω (-(d : ℤ)))) :=
    nontrivial_adicCompletion_maximalIdeal A _
  obtain ⟨duality⟩ :=
    Dualizing.LocalDuality.nonempty_adicCompletion_ext_linearEquiv_linearMap_localCohomology
      A f hspan ω hω K (finite_homology_singleFunctor_regular A) iE hhull (d : ℤ)
  have hMatlis : Nontrivial
      (localCohomologyModule A (IsLocalRing.maximalIdeal A) hm (ModuleCat.of A A) (d : ℤ) →ₗ[A]
        E) := duality.toEquiv.nontrivial_congr.mp hcompl
  intro hz
  let : Subsingleton
      (localCohomologyModule A (IsLocalRing.maximalIdeal A) hm
        (ModuleCat.of A A) (d : ℤ)) := ModuleCat.isZero_iff_subsingleton.mp hz
  refine (not_nontrivial_iff_subsingleton.mpr ?_) hMatlis
  refine ⟨fun g h => LinearMap.ext fun x => ?_⟩
  rw [Subsingleton.elim x 0, map_zero, map_zero]

/-- Let `(A, 𝔪)` be a Noetherian local ring of dimension `d` carrying a normalized dualizing
complex. Then `cd(A, 𝔪) = d`. -/
theorem cohomologicalDimension_maximalIdeal_eq_of_isNormalizedDualizingComplex
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hm : (IsLocalRing.maximalIdeal A).FG)
    (d : ℕ) (hdim : ringKrullDim A = (d : WithBot ℕ∞))
    (ω : DerivedCategory (ModuleCat.{u} A))
    (hω : Dualizing.IsNormalizedDualizingComplex.{u, u} ω) :
    cohomologicalDimension A (IsLocalRing.maximalIdeal A) hm = (d : ℤ) :=
  cohomologicalDimension_eq_of_not_isZero_localCohomologyModule A _ hm (d : ℤ)
    (cohomologicalDimension_le_ringKrullDim A (IsLocalRing.maximalIdeal A) hm d hdim.le)
    (not_isZero_topLocalCohomologyModule_of_isNormalizedDualizingComplex A hm d hdim ω hω)

/-- Let `(A, 𝔪)` be a Noetherian local ring of dimension `d` whose completion carries a normalized
dualizing complex. Then `cd(A, 𝔪) = d`. -/
@[stacks 0DXE "cohomological dimension of the maximal ideal; existence of a normalized dualizing \
complex on the completion, the local case of Stacks 0BFR, is an explicit hypothesis"]
theorem cohomologicalDimension_maximalIdeal_eq
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hm : (IsLocalRing.maximalIdeal A).FG)
    (d : ℕ) (hdim : ringKrullDim A = (d : WithBot ℕ∞))
    (hBFR : ∃ ω : DerivedCategory
        (ModuleCat.{u} (AdicCompletion (IsLocalRing.maximalIdeal A) A)),
      Dualizing.IsNormalizedDualizingComplex.{u, u} ω) :
    cohomologicalDimension A (IsLocalRing.maximalIdeal A) hm = (d : ℤ) := by
  obtain ⟨ω, hω⟩ := hBFR
  have hdimB : ringKrullDim (AdicCompletion (IsLocalRing.maximalIdeal A) A) =
      (d : WithBot ℕ∞) := by
    rwa [← ringKrullDim_adicCompletion_maximalIdeal (A := A)]
  have hmB : (IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal A) A)).FG :=
    Ideal.fg_of_isNoetherianRing _
  have hcdB : cohomologicalDimension (AdicCompletion (IsLocalRing.maximalIdeal A) A)
      (IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal A) A)) hmB =
      (d : ℤ) :=
    cohomologicalDimension_maximalIdeal_eq_of_isNormalizedDualizingComplex
      (AdicCompletion (IsLocalRing.maximalIdeal A) A) hmB d hdimB ω hω
  have hff : (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)).FaithfullyFlat :=
    RingHom.faithfullyFlat_algebraMap_iff.mpr Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hmap : (IsLocalRing.maximalIdeal A).map
      (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) =
      IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal A) A) :=
    AdicCompletion.maximalIdeal_eq_map.symm
  have hdescent := cohomologicalDimension_map_eq_of_faithfullyFlat
    (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) hff
    (IsLocalRing.maximalIdeal A) hm
  rwa [← hdescent, cohomologicalDimension_congr
    (hm.map (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A))) hmB hmap]

/-- Let `(A, 𝔪)` be a Noetherian local ring of dimension `d` whose completion carries a normalized
dualizing complex. Then `H^d_𝔪(A)` is nonzero. -/
@[stacks 0DXE "nonvanishing of top local cohomology; existence of a normalized dualizing complex \
on the completion, the local case of Stacks 0BFR, is an explicit hypothesis",
  sga "2 V 3.1" "(iii), special case"]
theorem not_isZero_topLocalCohomologyModule_maximalIdeal
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hm : (IsLocalRing.maximalIdeal A).FG)
    (d : ℕ) (hdim : ringKrullDim A = (d : WithBot ℕ∞))
    (hBFR : ∃ ω : DerivedCategory
        (ModuleCat.{u} (AdicCompletion (IsLocalRing.maximalIdeal A) A)),
      Dualizing.IsNormalizedDualizingComplex.{u, u} ω) :
    ¬ IsZero (localCohomologyModule A (IsLocalRing.maximalIdeal A) hm
      (ModuleCat.of A A) (d : ℤ)) :=
  not_isZero_localCohomologyModule_of_cohomologicalDimension_eq A _ hm (d : ℤ)
    (Int.natCast_nonneg d) (cohomologicalDimension_maximalIdeal_eq A hm d hdim hBFR)

/-! ### Normalized dualizing complexes on completions -/

/-- A normalized dualizing complex at residue-lift index `0` is one at index `u`. -/
theorem isNormalizedDualizingComplex_of_ulift_zero {A : Type u} [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] {ω : DerivedCategory (ModuleCat.{u} A)}
    (h : Dualizing.IsNormalizedDualizingComplex.{u, 0} ω) :
    Dualizing.IsNormalizedDualizingComplex.{u, u} ω :=
  ⟨h.1, h.2.map fun e => e.trans
    ((DerivedCategory.singleFunctor (ModuleCat.{u} (IsLocalRing.ResidueField A)) 0).mapIso
      (LinearEquiv.toModuleIso
        (ULift.moduleEquiv.trans ULift.moduleEquiv.symm)))⟩

/-- The completion of a Noetherian local ring carries a normalized dualizing complex. -/
theorem exists_isNormalizedDualizingComplex_adicCompletion (B : Type u) [CommRing B]
    [IsNoetherianRing B] [IsLocalRing B] :
    ∃ ω : DerivedCategory (ModuleCat.{u} (AdicCompletion (IsLocalRing.maximalIdeal B) B)),
      Dualizing.IsNormalizedDualizingComplex.{u, u} ω := by
  obtain ⟨ω, hω⟩ :=
    Dualizing.exists_isNormalizedDualizingComplex_of_isPrecomplete_maximalIdeal
      (AdicCompletion (IsLocalRing.maximalIdeal B) B)
  exact ⟨ω, isNormalizedDualizingComplex_of_ulift_zero hω⟩

/-- Let `(A, 𝔪)` be a Noetherian local ring of dimension `d`. Then `cd(A, 𝔪) = d`. -/
@[stacks 0DXE]
theorem cohomologicalDimension_maximalIdeal_eq'
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hm : (IsLocalRing.maximalIdeal A).FG)
    (d : ℕ) (hdim : ringKrullDim A = (d : WithBot ℕ∞)) :
    cohomologicalDimension A (IsLocalRing.maximalIdeal A) hm = (d : ℤ) :=
  cohomologicalDimension_maximalIdeal_eq A hm d hdim
    (exists_isNormalizedDualizingComplex_adicCompletion A)

/-- Let `(A, 𝔪)` be a Noetherian local ring of dimension `d`. Then `H^d_𝔪(A)` is nonzero. -/
@[stacks 0DXE, sga "2 V 3.1" "(iii), special case"]
theorem not_isZero_topLocalCohomologyModule_maximalIdeal'
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hm : (IsLocalRing.maximalIdeal A).FG)
    (d : ℕ) (hdim : ringKrullDim A = (d : WithBot ℕ∞)) :
    ¬ IsZero (localCohomologyModule A (IsLocalRing.maximalIdeal A) hm
      (ModuleCat.of A A) (d : ℤ)) :=
  not_isZero_topLocalCohomologyModule_maximalIdeal A hm d hdim
    (exists_isNormalizedDualizingComplex_adicCompletion A)

end Stacks.LocalCohomology

end
