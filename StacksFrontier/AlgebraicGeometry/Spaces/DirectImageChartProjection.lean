module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStructureMapChart
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleImageData

/-!
# The chart projections of the direct image of a sheaf of rings

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`.  The sections of the direct
image `f_*F` of a sheaf of sets on the small étale site of `X` over an étale scheme chart `V` of
`Y` are a limit over the étale scheme charts of `X` above `X ×_Y V`
(`AlgebraicGeometry.Space.chartIsLimit`), and `AlgebraicGeometry.Space.chartProjection` is the
projection to one of them.  That projection is stated for the right Kan extension form
`AlgebraicGeometry.Space.smallEtaleDirectImageRan` of the direct image; this file transports it
to `AlgebraicGeometry.Space.smallEtaleDirectImage`, which is the form the comorphism
`f^♯ : 𝒪_Y ⟶ f_*𝒪_X` of [Stacks Project, Tag 03G8] and the direct image of sheaves of rings are
built from.

The projection is a natural transformation of functors of the sheaf, so it **commutes with the
direct image of any morphism of sheaves of rings**; and the projection of `f^♯(b)` is the
pullback of the regular function `b` along the vertical morphism of the corresponding diagram of
étale scheme charts. Hence an equation between two morphisms of sheaves of rings on the small
étale site of `X` which is known after `f^♯` is known chartwise, on the functions pulled back
along `f`.

## Main definitions

* `AlgebraicGeometry.Space.directImageChartProjection`: the projection of the sections of `f_*F`
  over an étale chart `V` of `Y` to the sections of `F` over an étale chart of `X` above
  `X ×_Y V`.

## Main results

* `AlgebraicGeometry.Space.directImageChartProjection_map` and
  `AlgebraicGeometry.Space.directImageChartProjection_ringSheafMap`: **the chart projection
  commutes with the direct image of a morphism of sheaves of sets, and of sheaves of rings.**
* `AlgebraicGeometry.Space.directImageChartProjection_structureSharpSet`: **the chart projection
  of `f^♯(b)` is the chartwise pullback of `b`.**
* `AlgebraicGeometry.Space.directImageChartProjection_structureSharpSet_chartDiagram`: the same
  at a commutative diagram of étale scheme charts, where the chartwise pullback is
  `AlgebraicGeometry.Space.chartDiagramPullback`.

## Implementation notes

The statements are made at the underlying sheaves of sets throughout, with
`AlgebraicGeometry.Space.structureSharpSet` rather than
`AlgebraicGeometry.Space.structureSharp`: the sections of a sheaf of rings and of its underlying
sheaf of sets are the same type, but writing the ring-level form forces a coercion into every
statement.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8), the structure map.
* [Stacks Project, Tag 03G3](https://stacks.math.columbia.edu/tag/03G3), diagrams of charts.
* [Stacks Project, Tag 0CKE](https://stacks.math.columbia.edu/tag/0CKE).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

/-- **The projection of the sections of the direct image over an étale chart `V` of `Y` to the
sections over an étale chart of `X` above `X ×_Y V`**, for the direct image
`AlgebraicGeometry.Space.smallEtaleDirectImage` rather than its right Kan extension form: the
comparison of the two forms, followed by `AlgebraicGeometry.Space.chartProjection`.

Being a natural transformation of functors of the sheaf, it commutes with the direct image of
every morphism of sheaves. -/
noncomputable def directImageChartProjection (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op) :
    smallEtaleDirectImage B S hS f ⋙
        Sheaf.sectionsFunctor (SmallEtale.topology B S hS Y.1) (op V) ⟶
      Sheaf.sectionsFunctor (SmallEtale.topology B S hS X.1) j.right :=
  Functor.whiskerRight (smallEtaleDirectImageRanIso B S hS f).hom
      (Sheaf.sectionsFunctor (SmallEtale.topology B S hS Y.1) (op V)) ≫
    chartProjection B S hS f V j

/-- **The chart projection commutes with the direct image of a morphism of sheaves of sets.** -/
theorem directImageChartProjection_map (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op)
    {F F' : Sheaf (SmallEtale.topology B S hS X.1) (Type u)} (ψ : F ⟶ F')
    (z : (smallEtaleDirectImage B S hS f ⋙
      Sheaf.sectionsFunctor (SmallEtale.topology B S hS Y.1) (op V)).obj F) :
    (directImageChartProjection B S hS f V j).app F'
        ((smallEtaleDirectImage B S hS f ⋙
          Sheaf.sectionsFunctor (SmallEtale.topology B S hS Y.1) (op V)).map ψ z) =
      ψ.hom.app j.right ((directImageChartProjection B S hS f V j).app F z) :=
  Functor.natTrans_app_map_apply (directImageChartProjection B S hS f V j) ψ z

/-- **The chart projection commutes with the direct image of a morphism of sheaves of rings.** -/
theorem directImageChartProjection_ringSheafMap (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op)
    {O O' : Sheaf (SmallEtale.topology B S hS X.1) RingCat.{u}} (φ : O ⟶ O')
    (z : (smallEtaleDirectImage B S hS f ⋙
      Sheaf.sectionsFunctor (SmallEtale.topology B S hS Y.1) (op V)).obj
      ((sheafCompose (SmallEtale.topology B S hS X.1)
        (CategoryTheory.forget RingCat.{u})).obj O)) :
    (directImageChartProjection B S hS f V j).app
        ((sheafCompose (SmallEtale.topology B S hS X.1)
          (CategoryTheory.forget RingCat.{u})).obj O')
        ((pullbackRingSheafMap (SmallEtale.topology B S hS Y.1)
          (smallEtaleDirectImage B S hS f) φ).hom.app (op V) z) =
      φ.hom.app j.right
        ((directImageChartProjection B S hS f V j).app
          ((sheafCompose (SmallEtale.topology B S hS X.1)
            (CategoryTheory.forget RingCat.{u})).obj O) z) := by
  have hset : (smallEtaleDirectImage B S hS f ⋙
        Sheaf.sectionsFunctor (SmallEtale.topology B S hS Y.1) (op V)).map
        ((sheafCompose (SmallEtale.topology B S hS X.1)
          (CategoryTheory.forget RingCat.{u})).map φ) z =
      (pullbackRingSheafMap (SmallEtale.topology B S hS Y.1)
        (smallEtaleDirectImage B S hS f) φ).hom.app (op V) z :=
    ConcreteCategory.congr_hom
      (congrArg (fun m : (smallEtaleDirectImage B S hS f).obj
            ((sheafCompose (SmallEtale.topology B S hS X.1)
              (CategoryTheory.forget RingCat.{u})).obj O) ⟶
          (smallEtaleDirectImage B S hS f).obj
            ((sheafCompose (SmallEtale.topology B S hS X.1)
              (CategoryTheory.forget RingCat.{u})).obj O') => m.hom.app (op V))
        (ringSheafMap_pullbackRingSheafMap (SmallEtale.topology B S hS Y.1)
          (smallEtaleDirectImage B S hS f) φ)) z
  rw [← hset]
  exact directImageChartProjection_map B S hS f V j
    ((sheafCompose (SmallEtale.topology B S hS X.1)
      (CategoryTheory.forget RingCat.{u})).map φ) z

/-- **The chart projection of `f^♯(b)` is the chartwise pullback of `b`.** -/
theorem directImageChartProjection_structureSharpSet (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op)
    (b : (structureSetSheaf B S hS Y).obj.obj (op V)) :
    (directImageChartProjection B S hS f V j).app (structureSetSheaf B S hS X)
        ((structureSharpSet B S hS f).hom.app (op V) b) =
      chartPullback B S hS f V j b := by
  have hsharp : (structureSharpSet B S hS f).hom.app (op V) b =
      ((smallEtaleDirectImageRanIso B S hS f).inv.app
          (structureSetSheaf B S hS X)).hom.app (op V) (structureMapApp B S hS f V b) :=
    rfl
  have hcancel : ((smallEtaleDirectImageRanIso B S hS f).hom.app
        (structureSetSheaf B S hS X)).hom.app (op V)
        (((smallEtaleDirectImageRanIso B S hS f).inv.app
          (structureSetSheaf B S hS X)).hom.app (op V) (structureMapApp B S hS f V b)) =
      structureMapApp B S hS f V b :=
    Sheaf.hom_congr_app_apply
      (((smallEtaleDirectImageRanIso B S hS f).app
        (structureSetSheaf B S hS X)).inv_hom_id) (op V) _
  change (chartProjection B S hS f V j).app (structureSetSheaf B S hS X)
      (((smallEtaleDirectImageRanIso B S hS f).hom.app
        (structureSetSheaf B S hS X)).hom.app (op V)
        ((structureSharpSet B S hS f).hom.app (op V) b)) = _
  rw [hsharp, hcancel]
  exact chartProjection_structureMapApp B S hS f V j b

/-- **The chart projection of `f^♯(b)` at a commutative diagram of étale scheme charts is
`AlgebraicGeometry.Space.chartDiagramPullback`**, pullback of regular functions along the
vertical morphism of schemes of the diagram. -/
theorem directImageChartProjection_structureSharpSet_chartDiagram (f : X ⟶ Y)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (b : (structureSetSheaf B S hS Y).obj.obj (op d.V)) :
    (directImageChartProjection B S hS f d.V
          (StructuredArrow.mk (Y := op d.U)
            (baseChangeArrowOfChartDiagram B S hS f d).op)).app
        (structureSetSheaf B S hS X)
        ((structureSharpSet B S hS f).hom.app (op d.V) b) =
      (chartDiagramPullback B S hS f d).hom b := by
  have hg : chartBaseChangeMap B S hS f d.V
      (StructuredArrow.mk (Y := op d.U)
        (baseChangeArrowOfChartDiagram B S hS f d).op) = d.g :=
    chartDiagramOfBaseChangeArrow_baseChangeArrow_g B S hS f d
  have hpull : chartPullback B S hS f d.V
        (StructuredArrow.mk (Y := op d.U)
          (baseChangeArrowOfChartDiagram B S hS f d).op) b =
      (CategoryTheory.forget CommRingCat.{u}).map
        (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
          (chartBaseChangeMap B S hS f d.V
            (StructuredArrow.mk (Y := op d.U)
              (baseChangeArrowOfChartDiagram B S hS f d).op))).op) b :=
    rfl
  refine (directImageChartProjection_structureSharpSet B S hS f d.V _ b).trans ?_
  rw [hpull, hg]
  rfl

/-- **The value of a morphism of sheaves of rings on `X` at a chartwise pullback, as a chart
projection.**  For `φ : 𝒪_X ⟶ O` and a regular function `b` on the chart `d.V` of `Y`, the value
of `φ` at the pullback of `b` to the chart `d.U` of `X` is the chart projection of the direct
image of `φ` at `f^♯(b)`. -/
theorem app_chartDiagramPullback_eq_directImageChartProjection (f : X ⟶ Y)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    {O : Sheaf (SmallEtale.topology B S hS X.1) RingCat.{u}}
    (φ : structureRingSheaf B S hS X ⟶ O)
    (b : (structureSetSheaf B S hS Y).obj.obj (op d.V)) :
    φ.hom.app (op d.U) ((chartDiagramPullback B S hS f d).hom b) =
      (directImageChartProjection B S hS f d.V
            (StructuredArrow.mk (Y := op d.U)
              (baseChangeArrowOfChartDiagram B S hS f d).op)).app
          ((sheafCompose (SmallEtale.topology B S hS X.1)
            (CategoryTheory.forget RingCat.{u})).obj O)
          ((pullbackRingSheafMap (SmallEtale.topology B S hS Y.1)
            (smallEtaleDirectImage B S hS f) φ).hom.app (op d.V)
            ((structureSharpSet B S hS f).hom.app (op d.V) b)) :=
  (congrArg (φ.hom.app (op d.U))
      (directImageChartProjection_structureSharpSet_chartDiagram B S hS f d b)).symm.trans
    (directImageChartProjection_ringSheafMap B S hS f d.V
      (StructuredArrow.mk (Y := op d.U)
        (baseChangeArrowOfChartDiagram B S hS f d).op) φ
      ((structureSharpSet B S hS f).hom.app (op d.V) b)).symm

end AlgebraicGeometry.Space

end
