module

public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeFpqcDescentQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleRankOneFreeLocusRank
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeChartScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeSiteComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleFreeLocusPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.InvertibleQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleFiniteLocallyFree

/-!
# Invertibility of a quasi-coherent module descends along an fpqc covering

Let `X` be an algebraic space, `{f i : X i ⟶ X}` an fpqc covering and `N` a quasi-coherent
`𝒪_X`-module whose inverse images `f_i^*N` are all invertible.  Then `N` is invertible.  This is
the step of the proof of Stacks 0D27 which, after the descent datum on the test scheme has been
made effective, recognizes the descended module as an element of `Pic(T)`.

## Main results

* `AlgebraicGeometry.Space.isFreeModule_modulePullback_chartToSpace_of_isFiniteFree_over`: a
  module finite free on the slice of the small étale site at an étale scheme chart is free after
  pullback to the algebraic space of that chart.
* `AlgebraicGeometry.Space.isInvertibleModule_of_isFpqcCovering_of_isQuasicoherentOnSite`:
  **invertibility of a quasi-coherent module descends along an fpqc covering.**

## Implementation notes

By Stacks 060X (`isFiniteLocallyFreeOnSite_of_pullback_isFpqcCovering_of_isQuasicoherentOnSite`)
the module `N` is finite locally free, so every point `x` of `X` has an étale neighbourhood over
which `N` is free on some index type.  The point `x` also lies under a point of some member
`X k` of the covering (an fpqc covering is jointly surjective on points), where `N` is
invertible; comparing the two on the fibre product forces the free module to have rank one
(`AlgebraicGeometry.Space.nonempty_iso_unit_of_iso_free_of_isInvertibleModule`).  So every point
lies in the étale rank-one free locus, and a module free of rank one in an étale neighbourhood of
every point is invertible (Stacks 0B8Q).

## References

* [Stacks Project, Tag 0D27](https://stacks.math.columbia.edu/tag/0D27)
* [Stacks Project, Tag 060X](https://stacks.math.columbia.edu/tag/060X)
* [Stacks Project, Tag 0B8Q](https://stacks.math.columbia.edu/tag/0B8Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u v

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Finite freeness on the slice at a chart is freeness on the chart space.**  If an
`𝒪_X`-module is finite free on the slice of the small étale site of `X` at an étale scheme chart
`W`, then its inverse image along the structure morphism of `W` is free. -/
theorem isFreeModule_modulePullback_chartToSpace_of_isFiniteFree_over
    (X : AlgebraicSpaces B S hS) (N : Modules.{u, u} B S hS X.1 X.2) (W : SmallEtale B S hS X.1)
    (h : SheafOfModules.IsFiniteFree ((structureRingSheaf B S hS X).over W) (N.over W)) :
    IsFreeModule B S hS (chartSpace B S hS X W)
      ((modulePullback B S hS (chartToSpace B S hS X W)).obj N) := by
  have h₁ := (@Stacks.SheafOfModules.isFiniteFree_reindex_iff _ _ _ _
    ((SmallEtale.topology B S hS X.1).over W)
    (SmallEtale.topology B S hS (chartSpace B S hS X W).1)
    (SmallEtale.chartLocalizationEquivalence B S hS X.1 W)
    (isContinuous_chartLocalization_chartSpace B S hS X W) _
    ((structureRingSheaf B S hS X).over W) (N.over W)).2 h
  have h₂ := Stacks.SheafOfModules.isFiniteFree_of_iso
    (chartSmallEtaleRestrictionFunctorObjIso X N W ≪≫
      ((modulePullbackIsoEtaleModulePullback B S hS (chartToSpace B S hS X W)
        (isEtale_chartToSpace B S hS X W)).app N).symm) h₁
  exact IsFreeModule.of_isFiniteFree B S hS _ _ h₂

/-- **Invertibility of a quasi-coherent module descends along an fpqc covering.**  A
quasi-coherent `𝒪_X`-module whose inverse images along the members of an fpqc covering of `X` are
all invertible is invertible. -/
theorem isInvertibleModule_of_isFpqcCovering_of_isQuasicoherentOnSite {I : Type v}
    {X : AlgebraicSpaces B S hS} {Xi : I → AlgebraicSpaces B S hS} (f : ∀ i, Xi i ⟶ X)
    (hf : IsFpqcCovering B S hS fun i ↦ (f i).hom) (N : Modules.{u, u} B S hS X.1 X.2)
    (hN : N.IsQuasicoherentOnSite)
    (hNi : ∀ i, IsInvertibleModule (Xi i) ((modulePullback B S hS (f i)).obj N)) :
    IsInvertibleModule X N := by
  have hlf : SheafOfModules.IsFiniteLocallyFreeOnSite N :=
    isFiniteLocallyFreeOnSite_of_pullback_isFpqcCovering_of_isQuasicoherentOnSite B S hS f hf N hN
      fun i ↦ ((isInvertibleModule_iff_isFiniteLocallyFreeOfRank_one _).1
        (hNi i)).isFiniteLocallyFreeOnSite
  refine (isInvertibleModule_iff_isFiniteLocallyFreeOfRank_one N).2
    (isFiniteLocallyFreeOfRank_one_of_forall_mem_etaleRankOneFreeLocus B S hS N fun x => ?_)
  obtain ⟨k, y, hy⟩ := (isJointlySurjective_iff B S hS _ _).1
    (isJointlySurjective_of_isFpqcCovering B S hS _ hf) x
  obtain ⟨U, p, hp⟩ := exists_chart_point B S hS X.1 X.2 x
  obtain ⟨J, V, g, hcov, hfree⟩ := hlf U
  obtain ⟨W, g', hg', q, hq⟩ := SmallEtale.exists_mem_arrows_pointsMap_eq B S hS X.1 hcov p
  obtain ⟨i, h, -⟩ := Sieve.ofArrows.exists hg'
  have hW : yoneda.map ((SmallEtale.toOver B S hS X.1).map g') ≫ U.obj.hom =
      yoneda.map h.hom.left ≫ (V i).obj.hom :=
    (CostructuredArrow.w g'.hom).trans (CostructuredArrow.w h.hom).symm
  set v := pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj W))
    (yoneda.map h.hom.left) q
  have hv : pointsMap B S hS (yoneda.obj (V i).obj.left) (V i).obj.hom v = x := by
    rw [← pointsMap_apply_comm B S hS hW q, hq]
    exact hp
  obtain ⟨Iv, ⟨e⟩⟩ := exists_iso_free_of_isFreeModule B S hS _ _
    (isFreeModule_modulePullback_chartToSpace_of_isFiniteFree_over X N (V i) (hfree i))
  obtain ⟨e₁⟩ := nonempty_iso_unit_of_iso_free_of_isInvertibleModule
    (chartToSpace B S hS X (V i)) (f k) N Iv e (hNi k) v y (hv.trans hy.symm)
  exact ⟨chartSpace B S hS X (V i), chartToSpace B S hS X (V i),
    isEtale_chartToSpace B S hS X (V i), ⟨v, hv⟩, ⟨e₁⟩⟩

end AlgebraicGeometry.Space

end
