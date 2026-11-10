module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageChartProjection
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartCorrespondence

/-!
# A section of a direct image is determined by its chart projections

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`. The sections of the direct
image `f_*F` of a sheaf of sets on the small étale site of `X` over an étale scheme chart `V` of
`Y` are a limit over the étale scheme charts of `X` above `X ×_Y V`, and
`AlgebraicGeometry.Space.directImageChartProjection` is the projection to one of them. These
projections are jointly injective, and so two morphisms of sheaves of rings into a direct image
are equal as soon as they agree chart by chart.

## Main results

* `AlgebraicGeometry.Space.chartProjection_app_eq_ranChartCone_π`: the chart projection of the
  right Kan extension form is the projection of the limit cone of chart sections, at an arbitrary
  sheaf of sets.
* `AlgebraicGeometry.Space.chartProjection_sheaf_ext` and
  `AlgebraicGeometry.Space.directImageChartProjection_ext`: two sections of a direct image over
  an étale chart agreeing under all chart projections are equal, for the Kan extension form and
  for `AlgebraicGeometry.Space.smallEtaleDirectImage` respectively.
* `AlgebraicGeometry.Space.directImageChartProjection_ringSheafHom_ext`: two morphisms of
  sheaves of rings into a direct image whose chart projections agree on every section are
  equal.
* `AlgebraicGeometry.Space.app_chartPullback_eq_directImageChartProjection`: the value of a
  morphism of sheaves of rings on `X` at a chartwise pullback of a regular function, as a chart
  projection.

## References

* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1), the comparison of the
  two étale sites.
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2), part (1), the direct
  image.
* [Stacks Project, Tag 03G3](https://stacks.math.columbia.edu/tag/03G3), maps of sections on
  charts.
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8), the structure map.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

/-! ### Joint injectivity of the chart projections -/

/-- **The chart projection of the right Kan extension form of the direct image is the projection
of the limit cone of chart sections**, at an arbitrary sheaf of sets. -/
theorem chartProjection_app_eq_ranChartCone_π (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op)
    (F : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (a : (smallEtaleDirectImageRan B S hS f ⋙
      Sheaf.sectionsFunctor (SmallEtale.topology B S hS Y.1) (op V)).obj F) :
    (chartProjection B S hS f V j).app F a =
      (ranChartCone B S hS X F.obj (chartBaseChange B S hS f V)).π.app j a := by
  have h : (((comparisonFunctor B S hS X).sheafAdjunctionCocontinuous (Type u)
        (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X)).counit.app F).hom =
      (comparisonFunctor B S hS X).op.ranCounit.app F.obj := by
    rw [Functor.sheafAdjunctionCocontinuous_counit_app_hom, Functor.ranAdjunction_counit]
  change (((comparisonFunctor B S hS X).sheafAdjunctionCocontinuous (Type u)
        (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X)).counit.app F).hom.app
      j.right
      (((comparisonFunctor B S hS X).op.ran.obj F.obj).map j.hom a) = _
  rw [h]
  rfl

/-- **Two sections of the right Kan extension form of the direct image over an étale chart agree
as soon as all their chart projections agree**, at an arbitrary sheaf of sets. -/
theorem chartProjection_sheaf_ext (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    (F : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    {a b : (smallEtaleDirectImageRan B S hS f ⋙
      Sheaf.sectionsFunctor (SmallEtale.topology B S hS Y.1) (op V)).obj F}
    (h : ∀ j, (chartProjection B S hS f V j).app F a =
      (chartProjection B S hS f V j).app F b) :
    a = b :=
  ranChartCone_π_ext B S hS X F.obj (chartBaseChange B S hS f V) fun j ↦
    (chartProjection_app_eq_ranChartCone_π B S hS f V j F a).symm.trans
      ((h j).trans (chartProjection_app_eq_ranChartCone_π B S hS f V j F b))

/-- The chart projection of `AlgebraicGeometry.Space.smallEtaleDirectImage` is the comparison of
the two forms of the direct image followed by the chart projection of the Kan extension form. -/
theorem directImageChartProjection_app_apply (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op)
    (F : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (a : (smallEtaleDirectImage B S hS f ⋙
      Sheaf.sectionsFunctor (SmallEtale.topology B S hS Y.1) (op V)).obj F) :
    (directImageChartProjection B S hS f V j).app F a =
      (chartProjection B S hS f V j).app F
        (((smallEtaleDirectImageRanIso B S hS f).hom.app F).hom.app (op V) a) := rfl

/-- **Two sections of the direct image over an étale chart agree as soon as all their chart
projections agree.** -/
theorem directImageChartProjection_ext (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    (F : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    {a b : (smallEtaleDirectImage B S hS f ⋙
      Sheaf.sectionsFunctor (SmallEtale.topology B S hS Y.1) (op V)).obj F}
    (h : ∀ j, (directImageChartProjection B S hS f V j).app F a =
      (directImageChartProjection B S hS f V j).app F b) :
    a = b := by
  have hcancel : ∀ z : (smallEtaleDirectImage B S hS f ⋙
      Sheaf.sectionsFunctor (SmallEtale.topology B S hS Y.1) (op V)).obj F,
      ((smallEtaleDirectImageRanIso B S hS f).inv.app F).hom.app (op V)
        (((smallEtaleDirectImageRanIso B S hS f).hom.app F).hom.app (op V) z) = z := fun z ↦
    Sheaf.hom_congr_app_apply (((smallEtaleDirectImageRanIso B S hS f).app F).hom_inv_id)
      (op V) z
  exact Function.LeftInverse.injective hcancel
    (chartProjection_sheaf_ext B S hS f V F h)

/-- **Two morphisms of sheaves of rings into a direct image whose chart projections agree on
every section are equal.** -/
theorem directImageChartProjection_ringSheafHom_ext (f : X ⟶ Y)
    {O : Sheaf (SmallEtale.topology B S hS X.1) RingCat.{u}}
    {A : Sheaf (SmallEtale.topology B S hS Y.1) RingCat.{u}}
    (a b : A ⟶ pullbackRingSheaf.{u, u, u, u + 1, u, u + 1}
      (SmallEtale.topology B S hS Y.1) (smallEtaleDirectImage B S hS f) O)
    (h : ∀ (V : SmallEtale B S hS Y.1)
        (j : StructuredArrow (op (chartBaseChange B S hS f V))
          (comparisonFunctor B S hS X).op)
        (x : ToType (A.obj.obj (op V))),
      (directImageChartProjection B S hS f V j).app
          ((sheafCompose (SmallEtale.topology B S hS X.1)
            (CategoryTheory.forget RingCat.{u})).obj O) (a.hom.app (op V) x) =
        (directImageChartProjection B S hS f V j).app
          ((sheafCompose (SmallEtale.topology B S hS X.1)
            (CategoryTheory.forget RingCat.{u})).obj O) (b.hom.app (op V) x)) :
    a = b :=
  Sheaf.hom_ext (NatTrans.ext (funext fun V ↦ RingCat.hom_ext (RingHom.ext fun x ↦
    directImageChartProjection_ext B S hS f V.unop
      ((sheafCompose (SmallEtale.topology B S hS X.1)
        (CategoryTheory.forget RingCat.{u})).obj O)
      fun j ↦ h V.unop j x)))

/-! ### The chart projection at a chartwise pullback -/

/-- **The value of a morphism of sheaves of rings on `X` at a chartwise pullback, as a chart
projection.** For `φ : 𝒪_X ⟶ O` and a regular function `b` on the chart `V` of `Y`, the value of
`φ` at the pullback of `b` to the chart `j` of `X` above `X ×_Y V` is the chart projection of the
direct image of `φ` at `f^♯(b)`. -/
theorem app_chartPullback_eq_directImageChartProjection (f : X ⟶ Y)
    (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op)
    {O : Sheaf (SmallEtale.topology B S hS X.1) RingCat.{u}}
    (φ : structureRingSheaf B S hS X ⟶ O)
    (b : (structureSetSheaf B S hS Y).obj.obj (op V)) :
    φ.hom.app j.right (chartPullback B S hS f V j b) =
      (directImageChartProjection B S hS f V j).app
          ((sheafCompose (SmallEtale.topology B S hS X.1)
            (CategoryTheory.forget RingCat.{u})).obj O)
          ((pullbackRingSheafMap (SmallEtale.topology B S hS Y.1)
            (smallEtaleDirectImage B S hS f) φ).hom.app (op V)
            ((structureSharpSet B S hS f).hom.app (op V) b)) :=
  (congrArg (φ.hom.app j.right)
      (directImageChartProjection_structureSharpSet B S hS f V j b)).symm.trans
    (directImageChartProjection_ringSheafMap B S hS f V j φ
      ((structureSharpSet B S hS f).hom.app (op V) b)).symm

end AlgebraicGeometry.Space

end
