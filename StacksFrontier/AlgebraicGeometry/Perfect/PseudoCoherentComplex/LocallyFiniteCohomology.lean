module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.StalkRank
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentComplex.Coherence
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentComplex.Locality
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentComplex.RestrictHomology

/-!
# The cohomology of a perfect complex

On a locally Noetherian scheme the cohomology modules of a perfect object of the derived
category of modules are coherent, and on any scheme only finitely many of them are nonzero near
a given point.

## Main results

* `Stacks.AlgebraicGeometry.PerfectCohomology.isCoherent_homology`: coherence of every
  cohomology module.
* `Stacks.AlgebraicGeometry.PerfectCohomology.locally_finite_homology`: local finiteness of the
  set of degrees in which the cohomology has nonempty support.
* `Stacks.AlgebraicGeometry.PerfectCohomology.exists_finset_finiteLocallyFreeRank_eq_zero`: when
  the cohomology modules are finite locally free, near every point all but finitely many of them
  have rank zero.

## References

* [Stacks Project, Tag 0FEP](https://stacks.math.columbia.edu/tag/0FEP)
* [Stacks Project, Tag 08CM](https://stacks.math.columbia.edu/tag/08CM)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open SheafOfModules

universe u d

namespace Stacks.AlgebraicGeometry.PerfectCohomology

/-! ### Coherence of the cohomology over a member of the covering -/

/-- The restriction to `U` of a cohomology module of `K` is coherent as soon as the restriction
to `U` of a representative of `K` receives a quasi-isomorphism from a strictly perfect complex. -/
theorem isCoherent_restrict_of_strictModel (X : Scheme.{u}) [IsLocallyNoetherian X]
    [HasDerivedCategory.{d} (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace)] (U : X.Opens)
    {K : DerivedCategory (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace)}
    {E : CochainComplex (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace) ℤ}
    (eEK : DerivedCategory.Q.obj E ≅ K)
    {P : CochainComplex
      (StrictlyPerfect.OXMod.{u, u} (X.toRingedSpace.restrict U.isOpenEmbedding)) ℤ}
    (hP : StrictlyPerfect.IsStrictlyPerfect P)
    (q : P ⟶ RingedSpace.restrictComplex E U) (hq : QuasiIso q) (n : ℤ) :
    (Scheme.Modules.restrict
      ((DerivedCategory.homologyFunctor
        (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace) n).obj K) U.ι).IsCoherent :=
  CoherenceCriteria.isCoherent_of_isCoherent' <|
    isCoherentStacks_of_iso ((restrictModulesIsoRestrict X U).app _) <|
      isCoherentStacks_of_iso (derivedHomologyRestrictIso X U eEK q hq n)
        (isCoherent_homology_of_isStrictlyPerfect U.toScheme P hP n)

/-! ### Coherence and local finiteness of the cohomology -/

/-- Every cohomology module of a perfect object on a locally Noetherian scheme is coherent. -/
@[stacks 0FEP "locally_finite_cohomology"]
theorem isCoherent_homology (X : Scheme.{u}) [IsLocallyNoetherian X]
    [HasDerivedCategory.{d} (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace)]
    (K : DerivedCategory (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace))
    (hK : RingedSpace.IsPerfect (X := X.toRingedSpace) K) (n : ℤ) :
    _root_.SheafOfModules.IsCoherent
      ((DerivedCategory.homologyFunctor
        (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace) n).obj K) := by
  obtain ⟨E, ⟨I, U, hU, hmodels⟩, ⟨eEK⟩⟩ := hK
  refine isCoherent_of_cover_restrict _ U (IsOpenCover.mk hU) fun i => ?_
  obtain ⟨P, hP, ⟨q, hq⟩⟩ := hmodels i
  exact isCoherent_restrict_of_strictModel X (U i) eEK hP q hq n

/-- Near every point only finitely many cohomology modules of a perfect object have nonempty
support. -/
@[stacks 0FEP "locally_finite_cohomology"]
theorem locally_finite_homology (X : Scheme.{u})
    [HasDerivedCategory.{d} (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace)]
    (K : DerivedCategory (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace))
    (hK : RingedSpace.IsPerfect (X := X.toRingedSpace) K) (x : X) :
    ∃ U : X.Opens, x ∈ U ∧
      {n : ℤ | ∃ y : X, y ∈ U ∧ y ∈ SheafOfModules.supp
        ((DerivedCategory.homologyFunctor
          (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace) n).obj K)}.Finite := by
  classical
  obtain ⟨E, ⟨I, U, hU, hmodels⟩, ⟨eEK⟩⟩ := hK
  obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp (hU ▸ Opens.mem_top x)
  obtain ⟨P, hP, ⟨q, hq⟩⟩ := hmodels i
  refine ⟨U i, hxi, hP.bounded.subset ?_⟩
  rintro n ⟨y, hyU, hy⟩
  by_contra hmem
  have hzeroX : IsZero (P.X n) := not_not.mp (by simpa only [Set.mem_ofPred_eq] using hmem)
  have hzeroH : IsZero (P.homology n) := by
    simpa [HomologicalComplex.homology] using
      ShortComplex.isZero_homology_of_isZero_X₂ (P.sc n) hzeroX
  have hzero : IsZero ((RingedSpace.restrictModules X.toRingedSpace (U i)).obj
      ((DerivedCategory.homologyFunctor
        (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace) n).obj K)) :=
    hzeroH.of_iso (derivedHomologyRestrictIso X (U i) eEK q hq n).symm
  exact notMem_supp_of_isZero_restrictModules X (U i) _ hzero y hyU hy

/-- When the cohomology modules of a perfect object are finite locally free, near every point all
but finitely many of them have rank zero. -/
theorem exists_finset_finiteLocallyFreeRank_eq_zero (X : Scheme.{u})
    [HasDerivedCategory.{d} (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace)]
    (K : DerivedCategory (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace))
    (hK : RingedSpace.IsPerfect (X := X.toRingedSpace) K)
    (hF : ∀ n : ℤ, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := X.ringCatSheaf)
      ((DerivedCategory.homologyFunctor (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace) n).obj K))
    (x : X) :
    ∃ V : X.Opens, x ∈ V ∧ ∃ s : Finset ℤ, ∀ n ∉ s, ∀ v ∈ V,
      @Scheme.Modules.finiteLocallyFreeRank X
        ((DerivedCategory.homologyFunctor (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace) n).obj K)
        (hF n) v = 0 := by
  obtain ⟨U, hxU, hfin⟩ := locally_finite_homology X K hK x
  refine ⟨U, hxU, hfin.toFinset, fun n hn v hv ↦ ?_⟩
  exact @Scheme.Modules.finiteLocallyFreeRank_eq_zero_of_notMem_supp X _ (hF n) v fun hsupp ↦
    hn (hfin.mem_toFinset.mpr ⟨v, hv, hsupp⟩)

end Stacks.AlgebraicGeometry.PerfectCohomology

end
