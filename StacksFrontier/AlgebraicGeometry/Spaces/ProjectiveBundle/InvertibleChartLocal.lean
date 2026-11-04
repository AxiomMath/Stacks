module

public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackOpenInCoherentStack
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleRankOneFreeLocusRank
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartEquivalenceClosure
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartModuleGlueing

/-!
# Invertibility of a module on an algebraic space is étale local

An `𝒪_X`-module on an algebraic space `X` whose restriction to every étale scheme chart of `X` is
invertible is invertible.  Each point of `X` lies in the image of a chart, the restriction is
trivial on an étale neighbourhood of a lift of the point there, and that neighbourhood is an étale
neighbourhood of the point in `X` on which the module itself is trivial; a module trivial on an
étale neighbourhood of every point is finite locally free of rank one, that is, invertible.

## Main results

* `AlgebraicGeometry.Space.isInvertibleModule_of_forall_chartModuleRestriction`.

## References

* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 03LY](https://stacks.math.columbia.edu/tag/03LY)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Invertibility is étale local.**  An `𝒪_X`-module whose restriction to every étale scheme
chart of `X` is invertible is invertible. -/
theorem isInvertibleModule_of_forall_chartModuleRestriction (X : AlgebraicSpaces B S hS)
    (L : Modules.{u, u} B S hS X.1 X.2)
    (h : ∀ U : SmallEtale B S hS X.1,
      IsInvertibleModule (chartSpace B S hS X U) ((chartModuleRestriction B S hS X U).obj L)) :
    IsInvertibleModule X L := by
  refine (isInvertibleModule_iff_isFiniteLocallyFreeOfRank_one L).2
    (isFiniteLocallyFreeOfRank_one_of_forall_mem_etaleRankOneFreeLocus B S hS L fun x => ?_)
  obtain ⟨U, p, hp⟩ := exists_chart_point B S hS X.1 X.2 x
  obtain ⟨V, a, hae, ⟨v, hv⟩, ⟨e⟩⟩ :=
    mem_etaleRankOneFreeLocus_of_isInvertibleModule (chartSpace B S hS X U) _ (h U) p
  refine ⟨V, a ≫ chartToSpace B S hS X U,
    isEtale_comp B S hS hae (isEtale_chartToSpace B S hS X U), ⟨v, ?_⟩,
    ⟨((modulePullbackCompIso B S hS a (chartToSpace B S hS X U)).app L).symm ≪≫ e⟩⟩
  rw [← hp, ← hv]
  exact pointsMap_comp_apply B S hS a.hom (chartToSpace B S hS X U).hom v

end AlgebraicGeometry.Space

end
