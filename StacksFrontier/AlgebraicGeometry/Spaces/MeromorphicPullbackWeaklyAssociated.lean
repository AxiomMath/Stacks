module

public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.PullbackCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.CodimensionZeroPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierPullbackCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicPullback

/-!
# Pullbacks of meromorphic functions along a morphism avoiding the codimension-zero points

Let `f : X ⟶ Y` be a morphism of algebraic spaces carrying every weakly associated point of
`X` to a point of codimension `0` of `Y`.  Then pullbacks of meromorphic functions are defined
for `f`: this is part (1) of Stacks 0EN9, the companion of the flat case
`AlgebraicGeometry.Space.pullbacksMeromorphicSections_of_flat`.

The condition of Stacks 0EN8 is a condition on the commuting squares of étale scheme charts, so
the proof is the translation of the hypothesis to one such square and an appeal to the
scheme-level criterion `AlgebraicGeometry.pullbacksMeromorphicSections_of_mapsTo_genericPoints`
of Stacks 02OU.  The translation is the two chart descriptions the source cites: a weakly
associated point of a chart of `X` lies over a weakly associated point of `X`, and a point of
codimension `0` of `Y` is a generic point of an irreducible component on every chart of `Y`
carrying a point above it.

## Main results

* `AlgebraicGeometry.Space.chartSchemeToPoints_map_chartDiagram` identifies the point of `Y`
  under the image of a chart point along a chart diagram with the image under `f` of the point
  of `X` under that chart point.
* `AlgebraicGeometry.Space.pullbacksMeromorphicSections_of_mapsTo_codimensionZero` is
  Stacks 0EN9, part (1).

## References

* [Stacks Project, Tag 0EN9](https://stacks.math.columbia.edu/tag/0EN9)
* [Stacks Project, Tag 02OU](https://stacks.math.columbia.edu/tag/02OU)
* [Stacks Project, Tag 0CTX](https://stacks.math.columbia.edu/tag/0CTX)
* [Stacks Project, Tag 0BAQ](https://stacks.math.columbia.edu/tag/0BAQ)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The point of `Y` determined by the image of a chart point along the morphism of schemes of
a chart diagram is the image under `f` of the point of `X` determined by that chart point. -/
theorem chartSchemeToPoints_map_chartDiagram {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}
    (d : ChartDiagram B S hS X Y f) (u : chartScheme d.U) :
    chartSchemeToPoints B S hS Y d.V ((BigFppfOver.toScheme B S hS).map d.g u) =
      pointsMap B S hS X f (chartSchemeToPoints B S hS X d.U u) := by
  rw [chartSchemeToPoints_eq_pointsMap, pointsMap_chartSchemeToPoints,
    ← pointsMap_yoneda_map_class_canonicalSiteFieldPoint B S hS d.g u, d.comm]
  exact (congrFun (pointsMap_comp B S hS
    (yoneda.obj ((SmallEtale.toOver B S hS X).obj d.U)) (yoneda.map d.g) d.V.obj.hom) _).symm

/-- **Stacks 0EN9, part (1).** Pullbacks of meromorphic functions are defined along a morphism
`f : X ⟶ Y` of algebraic spaces carrying every weakly associated point of `X` to a point of
codimension `0` of `Y`.

Over a commuting square of étale scheme charts the claim is the scheme-level criterion of
Stacks 02OU: a weakly associated point of the chart of `X` lies over a weakly associated point
of `X`, which is carried to a point of codimension `0` of `Y`, and such a point is a generic
point of an irreducible component on the chart of `Y` above it. -/
@[stacks 0EN9 "part (1): weakly associated points of X mapped to codimension-zero points of Y"]
theorem pullbacksMeromorphicSections_of_mapsTo_codimensionZero
    {X Y : AlgebraicSpaces B S hS} (f : X.1 ⟶ Y.1)
    (hf : ∀ x ∈ weaklyAssociatedPointsOfSpace B S hS X,
      localRingDimension B S hS (pointsMap B S hS X.1 f x) = 0) :
    PullbacksMeromorphicSections B S hS f := by
  intro d s hs
  have hmaps : Set.MapsTo ((BigFppfOver.toScheme B S hS).map d.g)
      (Stacks.Divisors.schemeWeaklyAssociatedPoints (chartScheme d.U))
      (genericPoints (chartScheme d.V)) := by
    intro u hu
    have hEt : IsEtale B S hS d.V.obj.hom :=
      (isEtale_iff_presheaf_of_yoneda B S hS d.V.obj.hom).mpr d.V.property
    have hcp : ChartPoint B S hS d.V.obj.left d.V.obj.hom
        ((BigFppfOver.toScheme B S hS).map d.g u)
        (pointsMap B S hS X.1 f (chartSchemeToPoints B S hS X.1 d.U u)) := by
      rw [← chartSchemeToPoints_map_chartDiagram B S hS d u]
      exact ⟨canonicalSiteFieldPoint B S hS d.V.obj.left _,
        canonicalSiteFieldPoint_point B S hS d.V.obj.left _, rfl⟩
    exact (localRingDimension_eq_zero_iff_all_etale_genericPoints B S hS Y.2 _).mp
      (hf _ (mem_weaklyAssociatedPointsOfSpace_chartSchemeToPoints B S hS X d.U u hu))
      d.V.obj.left d.V.obj.hom _ hEt hcp
  have hvalue : pullbackSection ((BigFppfOver.toScheme B S hS).map d.g).toLRSHom ⊤ ⊤ (by simp) s =
      Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map d.g).op s := by
    simp only [Functor.comp_obj, ObjectProperty.ι_obj, CostructuredArrow.proj_obj,
      Over.forget_obj, pullbackSection, Functor.comp_map, Over.forget_map, ObjectProperty.ι_map,
      Scheme.Hom.toLRSHom, Opens.map_top, homOfLE_refl, op_id, CategoryTheory.Functor.map_id,
      CommRingCat.hom_id, TopCat.Presheaf.pushforward_obj_obj, Scheme.Γ_obj, Scheme.Γ_map,
      Scheme.Hom.appTop, Scheme.Hom.app, Quiver.Hom.unop_op]
    exact RingHom.id_apply _
  simpa only [hvalue] using
    _root_.AlgebraicGeometry.pullbacksMeromorphicSections_of_mapsTo_genericPoints
      ((BigFppfOver.toScheme B S hS).map d.g) hmaps ⊤ ⊤ (by simp) s hs

end AlgebraicGeometry.Space

end
