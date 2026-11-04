module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartOpenRestrictionOver
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartModuleSliceComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionReadingsFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeChartScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.SliceFreeModuleCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartEquivalenceClosure
public import StacksFrontier.CategoryTheory.Sites.Modules.FiniteLocallyFreeOfRankLocalOnCover
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Sheaf

/-!
# Zariski-local trivializations of a finite locally free module on an algebraic space

Let `M` be a quasi-coherent `𝒪_X`-module on the small étale site of an algebraic space `X` which
is finite locally free on the site (Stacks 03DL (2)).  Finite local freeness on the site only
provides *étale* neighbourhoods over which `M` is free.  Over an étale scheme chart `A` of `X`,
Stacks 05VG for the clause 03DL (2) at `τ = étale` turns finite local freeness of `M` on the
slice at `A` into Zariski finite local freeness of the chart module of Descent, Proposition
03DX (2).  So every point of the scheme of `A` has a *Zariski* open neighbourhood `O` such that
`M` is finite free on the slice at the étale chart `openChart A O` that `O` cuts out.

## Main results

* `AlgebraicGeometry.Space.isFiniteLocallyFree_chartSchemeModule_of_isFiniteLocallyFreeOnSite`:
  finite local freeness of `M` on the slice at a chart gives Zariski finite local freeness of the
  chart module.
* `AlgebraicGeometry.Space.isFiniteFree_over_openChart_of_iso_free`: a trivialization of the
  chart module over a Zariski open `O` makes `M` finite free on the slice at `openChart A O`.
* `AlgebraicGeometry.Space.exists_mem_isFiniteFree_over_openChart`: **every point of the scheme
  of an étale chart has a Zariski open neighbourhood over which a finite locally free
  quasi-coherent module is finite free.**

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 05VG](https://stacks.math.columbia.edu/tag/05VG)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : AlgebraicSpaces B S hS) (M : SheafOfModules.{u} (structureRingSheaf B S hS X))
  (hM : M.IsQuasicoherentOnSite) (A : SmallEtale B S hS X.1)

/-- **Finite local freeness on the slice at a chart gives Zariski finite local freeness of the
chart module.** -/
theorem isFiniteLocallyFree_chartSchemeModule_of_isFiniteLocallyFreeOnSite
    (h : SheafOfModules.IsFiniteLocallyFreeOnSite (M.over A)) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (chartSchemeModule B S hS X M hM A) := by
  have := isQuasicoherent_chartSchemeModule B S hS X M hM A
  refine (_root_.AlgebraicGeometry.SmallEtale.isFiniteLocallyFreeOnSite_associatedModule_iff
    (associatedBigEtaleSite B) (chartScheme A)
    ((SmallEtale.toOver B S hS X.1).obj A).left.property _).1 ?_
  refine SheafOfModules.IsFiniteLocallyFreeOnSite.of_iso
    (associatedModuleChartSchemeModuleIso B S hS X M hM A).symm ?_
  refine (isFiniteLocallyFreeOnSite_representedSmallEtaleModule_iff B S hS _ _).1 ?_
  refine SheafOfModules.IsFiniteLocallyFreeOnSite.of_iso
    (representedSmallEtaleChartSchemeEtaleModuleIso B S hS X M hM A).symm ?_
  exact (isFiniteLocallyFreeOnSite_chartSmallEtaleRestriction_iff B S hS X M A).2 h

include hM in
/-- **A trivialization of the chart module over a Zariski open makes the module finite free on
the slice at the open chart.** -/
theorem isFiniteFree_over_openChart_of_iso_free (O : (chartScheme A).Opens) (I : Type u)
    [Finite I] (e : Scheme.Modules.restrict (X := O) (Y := chartScheme A)
      (restrictToChart B S hS X.2 M A) O.ι ≅ SheafOfModules.free I) :
    SheafOfModules.IsFiniteFree _ (M.over (openChart B S hS X.1 A O)) := by
  let iso : restrictToChart B S hS X.2 M ((chartOpens B S hS A).obj O) ≅
      SheafOfModules.free I :=
    (nonempty_over_restrictToChart_chartOpens B S hS X M hM A O).some.symm ≪≫
      (Scheme.Modules.overFunctorEquiv O).app (restrictToChart B S hS X.2 M A) ≪≫ e
  rw [chartOpens_obj_eq_openChart] at iso
  set T := openChart B S hS X.1 A O
  have hff : SheafOfModules.IsFiniteFree (chartScheme T).ringCatSheaf
      (chartSchemeModule B S hS X M hM T) :=
    Stacks.SheafOfModules.isFiniteFree_of_iso
      (restrictToChartIsoChartSchemeModule B S hS X M hM T) (isFiniteFree_of_iso_free iso)
  have := isQuasicoherent_chartSchemeModule B S hS X M hM T
  have h3 := (_root_.AlgebraicGeometry.SmallEtale.isFiniteFree_associatedModule_iff
    (associatedBigEtaleSite B) (chartScheme T)
    ((SmallEtale.toOver B S hS X.1).obj T).left.property
    (chartSchemeModule B S hS X M hM T)).2 hff
  have h4 := Stacks.SheafOfModules.isFiniteFree_of_iso
    (associatedModuleChartSchemeModuleIso B S hS X M hM T) h3
  have h5 := (isFiniteFree_representedSmallEtaleModule_iff B S hS
    ((SmallEtale.toOver B S hS X.1).obj T) (chartSchemeEtaleModule B S hS X M hM T)).2 h4
  have h6 := Stacks.SheafOfModules.isFiniteFree_of_iso
    (representedSmallEtaleChartSchemeEtaleModuleIso B S hS X M hM T) h5
  have h7 : SheafOfModules.IsFiniteFree _ (chartSmallEtaleRestriction B S hS X M T) := h6
  exact (@Stacks.SheafOfModules.isFiniteFree_reindex_iff _ _ _ _
    ((SmallEtale.topology B S hS X.1).over T)
    (SmallEtale.topology B S hS (chartSpace B S hS X T).1)
    (SmallEtale.chartLocalizationEquivalence B S hS X.1 T)
    (isContinuous_chartLocalization_chartSpace B S hS X T) inferInstance
    ((structureRingSheaf B S hS X).over T) (M.over T)).1 h7

include hM in
/-- **A finite locally free quasi-coherent module is finite free over a Zariski neighbourhood of
every point of every chart.**  For an étale scheme chart `A` of `X` and a point `z` of its
scheme there is a Zariski open `O ∋ z` such that `M` is finite free on the slice at the étale
chart `openChart A O`. -/
theorem exists_mem_isFiniteFree_over_openChart (h : SheafOfModules.IsFiniteLocallyFreeOnSite M)
    (z : chartScheme A) :
    ∃ O : (chartScheme A).Opens, z ∈ O ∧
      SheafOfModules.IsFiniteFree _ (M.over (openChart B S hS X.1 A O)) := by
  have hflf := isFiniteLocallyFree_chartSchemeModule_of_isFiniteLocallyFreeOnSite B S hS X M hM A
    (h.over A)
  have hflf' : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (restrictToChart B S hS X.2 M A) :=
    @AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.of_iso _ _ _
      (restrictToChartIsoChartSchemeModule B S hS X M hM A).symm hflf
  obtain ⟨O, hzO, I, hI, ⟨e⟩⟩ :=
    (Scheme.Modules.isFiniteLocallyFree_iff (restrictToChart B S hS X.2 M A)).mpr hflf' z
  exact ⟨O, hzO, isFiniteFree_over_openChart_of_iso_free B S hS X M hM A O I e⟩

end AlgebraicGeometry.Space

end
