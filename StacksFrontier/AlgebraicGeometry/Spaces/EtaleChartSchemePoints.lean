module

public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.LargeFieldPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleSite

/-!
# Points of an étale chart scheme as points of the algebraic space

A point `x` of the scheme underlying an étale chart `U` of a presheaf `F` on the big fppf
site of `S` determines a point of `F` in the sense of Stacks 03BU: the residue field of the
chart scheme at `x` has its spectrum in the site, the canonical morphism
`Spec κ(x) ⟶ chartScheme U` composed with the chart is a section of `F` over that spectrum,
and the resulting field-valued point has a class in `AlgebraicGeometry.Space.points`.

This file packages that assignment and records how it interacts with the two maps on points
already available: `AlgebraicGeometry.Space.pointsToScheme`, which identifies the points of a
*represented* presheaf with the points of the representing scheme, and
`AlgebraicGeometry.Space.pointsMap`, the map on points induced by a morphism of presheaves.

## Main definitions

* `AlgebraicGeometry.Space.chartSchemeFieldValuedPoint` is the field-valued point of `F`
  carried by a point of the scheme underlying an étale chart.
* `AlgebraicGeometry.Space.chartSchemeToPoints` is the induced map
  `chartScheme U → |F|`.

## Main results

* `AlgebraicGeometry.Space.chartSchemeToPoints_eq_pointsMap`: the map is the chart read on
  points, applied to the canonical field-valued point of the represented presheaf at `x`.
* `AlgebraicGeometry.Space.pointsToScheme_class_canonicalSiteFieldPoint` and
  `AlgebraicGeometry.Space.chartSchemeToPoints_eq_pointsMap_pointsEquivScheme_symm`: the
  canonical field-valued point at `x` lies over `x`, so the map is the chart read on points
  precomposed with the inverse of the bijection of Stacks 03BX(1).
* `AlgebraicGeometry.Space.chartSchemeToPoints_map`: the map is compatible with morphisms of
  étale charts, in the sense that moving a point of a smaller chart scheme into a larger one
  does not change the point of `F` it determines.
* `AlgebraicGeometry.Space.pointsMap_chartSchemeToPoints`: a morphism of presheaves carries
  the point determined by a chart point to the point determined by the same chart point of
  the composed chart.
* `AlgebraicGeometry.Space.surjective_chartSchemeToPoints`: the map is surjective as soon as
  the chart is surjective on points, which is the form a covering argument uses.

## Implementation notes

The field-valued point is `AlgebraicGeometry.Space.canonicalSiteFieldPoint` of the object of
the big fppf site underlying the chart, pushed along the chart by
`AlgebraicGeometry.Space.FieldValuedPoint.map`; nothing here uses that the chart is étale, or
that `F` is an algebraic space, so the étale hypothesis is carried only to make the statements
apply to the small étale site of `F`.

The compatibility with a morphism of charts is proved through
`AlgebraicGeometry.Space.canonicalSiteFieldPoint_class_eq`, the smallest-representative
property of `Spec κ(x) ⟶ X`: the image of the canonical point of the smaller chart is a
field-valued point of the larger one lying over the image point, hence has the same class as
the canonical point there. The triangle of the morphism of charts over `F` turns that equality
of classes in the represented presheaf into the asserted equality in `|F|`.

## References

* [Stacks Project, Tag 03BU](https://stacks.math.columbia.edu/tag/03BU)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- The point of the scheme underlying `A` carried by a field-valued point of the presheaf
represented by `A` is the one read off through `AlgebraicGeometry.Space.schemeFieldPoint`. -/
theorem point_schemeFieldPoint (A : BigFppfOver B S hS)
    (p : FieldValuedPoint B S hS (yoneda.obj A)) :
    (schemeFieldPoint B S hS p).point = schemePoint B S hS A p :=
  rfl

/-- The canonical field-valued point of a represented presheaf at `x` lies over `x`. -/
theorem pointsToScheme_class_canonicalSiteFieldPoint (A : BigFppfOver B S hS)
    (x : (BigFppfOver.toScheme B S hS).obj A) :
    pointsToScheme B S hS A
        ((canonicalSiteFieldPoint B S hS A x).class B S hS (yoneda.obj A)) = x :=
  canonicalSiteFieldPoint_point B S hS A x

/-- The field-valued point of `F` carried by a point `x` of the scheme underlying an étale
chart `U`: the residue field at `x`, with the section of `F` obtained by composing
`Spec κ(x) ⟶ chartScheme U` with the chart. -/
noncomputable def chartSchemeFieldValuedPoint (U : SmallEtale B S hS F)
    (x : chartScheme U) : FieldValuedPoint B S hS F :=
  FieldValuedPoint.map B S hS (yoneda.obj ((SmallEtale.toOver B S hS F).obj U)) U.obj.hom
    (canonicalSiteFieldPoint B S hS ((SmallEtale.toOver B S hS F).obj U) x)

/-- The field of `AlgebraicGeometry.Space.chartSchemeFieldValuedPoint` is the residue field of
the chart scheme at the point. -/
theorem chartSchemeFieldValuedPoint_carrier (U : SmallEtale B S hS F) (x : chartScheme U) :
    (chartSchemeFieldValuedPoint B S hS F U x).carrier = (chartScheme U).residueField x :=
  rfl

/-- The point of `F` determined by a point of the scheme underlying an étale chart. -/
noncomputable def chartSchemeToPoints (U : SmallEtale B S hS F) (x : chartScheme U) :
    points B S hS F :=
  (chartSchemeFieldValuedPoint B S hS F U x).class B S hS F

/-- `AlgebraicGeometry.Space.chartSchemeToPoints` is the chart read on points, applied to the
class of the canonical field-valued point at `x`. -/
theorem chartSchemeToPoints_eq_pointsMap (U : SmallEtale B S hS F) (x : chartScheme U) :
    chartSchemeToPoints B S hS F U x =
      pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS F).obj U)) U.obj.hom
        ((canonicalSiteFieldPoint B S hS ((SmallEtale.toOver B S hS F).obj U) x).class B S hS
          (yoneda.obj ((SmallEtale.toOver B S hS F).obj U))) :=
  rfl

/-- `AlgebraicGeometry.Space.chartSchemeToPoints` is the chart read on points, precomposed
with the inverse of the bijection of Stacks 03BX(1) between the points of the represented
presheaf of the chart and the points of the chart scheme. -/
theorem chartSchemeToPoints_eq_pointsMap_pointsEquivScheme_symm (U : SmallEtale B S hS F)
    (x : chartScheme U) :
    chartSchemeToPoints B S hS F U x =
      pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS F).obj U)) U.obj.hom
        ((pointsEquivScheme B S hS ((SmallEtale.toOver B S hS F).obj U)).symm x) := by
  rw [chartSchemeToPoints_eq_pointsMap]
  refine congrArg _ ((Equiv.eq_symm_apply _).2 ?_)
  exact pointsToScheme_class_canonicalSiteFieldPoint B S hS _ x

/-- The class of the canonical field-valued point at `x` is carried by a morphism of the big
fppf site to the class of the canonical field-valued point at the image of `x`. -/
theorem pointsMap_yoneda_map_class_canonicalSiteFieldPoint {A A' : BigFppfOver B S hS}
    (σ : A' ⟶ A) (x : (BigFppfOver.toScheme B S hS).obj A') :
    pointsMap B S hS (yoneda.obj A') (yoneda.map σ)
        ((canonicalSiteFieldPoint B S hS A' x).class B S hS (yoneda.obj A')) =
      (canonicalSiteFieldPoint B S hS A
        ((BigFppfOver.toScheme B S hS).map σ x)).class B S hS (yoneda.obj A) := by
  rw [pointsMap_class]
  refine (canonicalSiteFieldPoint_class_eq B S hS A _ _ ?_).symm
  rw [point_schemeFieldPoint, schemePoint_map_yoneda, ← point_schemeFieldPoint]
  exact congrArg ((BigFppfOver.toScheme B S hS).map σ)
    (canonicalSiteFieldPoint_point B S hS A' x)

/-- Pushing a point of the scheme of a smaller étale chart into the scheme of a larger one
along a morphism of charts does not change the point of `F` it determines. -/
theorem chartSchemeToPoints_map {U V : SmallEtale B S hS F} (g : V ⟶ U)
    (x : chartScheme V) :
    chartSchemeToPoints B S hS F U
        ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS F).map g) x) =
      chartSchemeToPoints B S hS F V x := by
  have htri : yoneda.map ((SmallEtale.toOver B S hS F).map g) ≫ U.obj.hom = V.obj.hom :=
    ((SmallEtale.inclusion B S hS F).map g).w
  have h3 := congrFun (pointsMap_comp B S hS
      (yoneda.obj ((SmallEtale.toOver B S hS F).obj V))
      (yoneda.map ((SmallEtale.toOver B S hS F).map g)) U.obj.hom)
    ((canonicalSiteFieldPoint B S hS ((SmallEtale.toOver B S hS F).obj V) x).class B S hS
      (yoneda.obj ((SmallEtale.toOver B S hS F).obj V)))
  rw [htri] at h3
  rw [chartSchemeToPoints_eq_pointsMap, chartSchemeToPoints_eq_pointsMap,
    ← pointsMap_yoneda_map_class_canonicalSiteFieldPoint B S hS
      ((SmallEtale.toOver B S hS F).map g) x]
  exact h3.symm

/-- A morphism of presheaves carries the point determined by a chart point to the point
determined by the same chart point of the composed chart. -/
theorem pointsMap_chartSchemeToPoints {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (α : F ⟶ G)
    (U : SmallEtale B S hS F) (x : chartScheme U) :
    pointsMap B S hS F α (chartSchemeToPoints B S hS F U x) =
      pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS F).obj U)) (U.obj.hom ≫ α)
        ((canonicalSiteFieldPoint B S hS ((SmallEtale.toOver B S hS F).obj U) x).class B S hS
          (yoneda.obj ((SmallEtale.toOver B S hS F).obj U))) := by
  rw [pointsMap_comp, chartSchemeToPoints_eq_pointsMap]
  rfl

/-- The points of `F` are exhausted by the points of the scheme of an étale chart whose
induced map on points is surjective. -/
theorem surjective_chartSchemeToPoints (U : SmallEtale B S hS F)
    (hU : Function.Surjective
      (pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS F).obj U)) U.obj.hom)) :
    Function.Surjective (chartSchemeToPoints B S hS F U) := by
  intro y
  obtain ⟨z, hz⟩ := hU y
  refine ⟨pointsToScheme B S hS ((SmallEtale.toOver B S hS F).obj U) z, ?_⟩
  rw [chartSchemeToPoints_eq_pointsMap_pointsEquivScheme_symm]
  refine Eq.trans (congrArg _ ?_) hz
  exact (Equiv.symm_apply_eq _).2 rfl

end AlgebraicGeometry.Space

end
