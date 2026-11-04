module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AffineSectionExtension
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuotientStackChartedPoints

/-!
# Extending a morphism on the presentation of a quotient stack over the charted points

Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces with quotient stack `[U/R]`, let `ℱ`
be a quasi-coherent module and `ℋ` an arbitrary module on the fppf site of `[U/R]`, and let
`φ : x^*ℱ|_{U_étale} ⟶ x^*ℋ|_{U_étale}` be a morphism of modules on the small étale site of `U`.
This file constructs, for every charted point `c` (a point of `U` over an affine object, factored
through an affine étale chart `W`), the linear map

```
ℱ(x(c)) ⟶ ℋ(x(c)),   b^*f ↦ b^*φ(f)  for  b : x(c) ⟶ x(u_U W),
```

which exists because `ℱ` is quasi-coherent: the sections of `ℱ` over `x(c)` are the base change
of its sections over `x(u_U W)` (`AlgebraicGeometry.FibredSite.extendAlong`).

The point of the construction is that these maps are compatible with *every* arrow of `[U/R]`
between charted points, not only with those coming from `U`, as soon as `φ` satisfies the
compatibility of Stacks 076S: there is `χ : (x ∘ s)^*ℱ|_{R_étale} ⟶ (x ∘ s)^*ℋ|_{R_étale}` making
the two squares through the comparison maps of equation 076R commute.  An arrow of `[U/R]`
between charted points is a point of `R`; fppf locally it factors through an affine étale chart
`V` of `R` carrying commutative squares of charts over `s` and over `t`, and there the two
squares say that extending along the source and extending along the target both give the
extension along `V` defined by `χ`.  This is
`AlgebraicGeometry.Stack.chartedExtension_naturality`, the main result of the file, and it is the
form of the source's "this assignment is compatible with the restriction mappings ... if the
cocycle condition of the lemma is satisfied", whose proof the source omits.

## Main definitions

* `AlgebraicGeometry.Stack.chartedExtension`: the linear map `ℱ(x(c)) ⟶ ℋ(x(c))` over a charted
  point.
* `AlgebraicGeometry.Stack.extAlong` and `AlgebraicGeometry.Stack.arrowExtAlong`: the extensions
  along a morphism to the image of a chart of `U`, respectively of `R`.

## Main results

* `AlgebraicGeometry.Stack.chartedExtension_chartMap` and
  `AlgebraicGeometry.Stack.map_chartedExtension`: the extension is `φ` on restrictions of sections
  over the chart, and is compatible with restriction of the charted point.
* `AlgebraicGeometry.Stack.quotientStackSource_square_app` and
  `AlgebraicGeometry.Stack.quotientStackTarget_square_app`: the two squares of Stacks 076S read on
  sections over a commutative square of charts.
* `AlgebraicGeometry.Stack.chartedExtension_naturality`: the extension over a charted point is
  compatible with every arrow of `[U/R]` from it to the image of an affine chart of `U`.

## References

* [Stacks Project, Tag 076R](https://stacks.math.columbia.edu/tag/076R)
* [Stacks Project, Tag 076S](https://stacks.math.columbia.edu/tag/076S)
* [Stacks Project, Tag 06WT](https://stacks.math.columbia.edu/tag/06WT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS} {G : GroupoidInAlgebraicSpaces C S hS B}

section PointwiseAlgebra

variable (G)

/-- The point of `R` underlying an arrow of the pointwise groupoid fibration. -/
noncomputable abbrev pointwiseArrow {X Y : PointwiseFibration G} (f : X ⟶ Y) :
    G.arrows.obj.obj (op X.base) :=
  (G.toGroupoidInFunctors.evaluationArrowEquiv (op X.base) _ _ f.fiber).1

/-- The arrow underlying a commutative square of charts is an identity. -/
theorem pointwiseArrow_chartDiagramPoint {X : AlgebraicSpaces C S hS} (a : X.1 ⟶ G.objects.obj)
    (V : Space.SmallEtale C S hS X.1) (W : Space.SmallEtale C S hS G.objects.obj)
    (g : (Space.SmallEtale.toOver C S hS X.1).obj V ⟶
      (Space.SmallEtale.toOver C S hS G.objects.obj).obj W)
    (hg : V.obj.hom ≫ a = yoneda.map g ≫ W.obj.hom) :
    pointwiseArrow G (chartDiagramPoint G a V W g hg) =
      G.toGroupoidInFunctors.identity _ (a.app _ (yonedaEquiv V.obj.hom)) :=
  evaluationArrow_eqToHom_identity G.toGroupoidInFunctors _
    (chartDiagram_point_eq G a V W g hg)

/-- Composing on the right with an arrow whose point of `R` is an identity does not change the
point of `R`. -/
theorem pointwiseArrow_comp_of_right {X Y Z : PointwiseFibration G} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hg : pointwiseArrow G g = G.toGroupoidInFunctors.identity _ Y.fiber) :
    pointwiseArrow G (f ≫ g) = pointwiseArrow G f :=
  pointwiseComp_arrow_of_right_identity G.toGroupoidInFunctors f g hg

/-- Composing on the left with an arrow whose point of `R` is an identity restricts the point of
`R` along the base. -/
theorem pointwiseArrow_comp_of_left {X Y Z : PointwiseFibration G} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : pointwiseArrow G f = G.toGroupoidInFunctors.identity _ X.fiber) :
    pointwiseArrow G (f ≫ g) = G.arrows.obj.map f.base.op (pointwiseArrow G g) :=
  pointwiseComp_arrow_of_left_identity G.toGroupoidInFunctors f g hf

end PointwiseAlgebra

section Extension

attribute [local instance] FibredSite.objModule

variable {F H : QuotientStackModules G}
  (φ : quotientStackObjectRestriction G F ⟶ quotientStackObjectRestriction G H)
  (χ : quotientStackArrowRestriction G F ⟶ quotientStackArrowRestriction G H)
  (hF : F.IsQuasicoherentOnSite)

/-- The value of `φ : x^*ℱ|_{U_étale} ⟶ x^*ℋ|_{U_étale}` on sections over an étale chart `W` of
`U`, as a map of sections of `ℱ` and `ℋ` over `x(u_U W)`. -/
noncomputable def chartSectionValue (W : Space.SmallEtale C S hS G.objects.obj) :
    F.val.obj (op ((pointwiseToQuotientStack G).obj (chartPoint G W))) →+
      H.val.obj (op ((pointwiseToQuotientStack G).obj (chartPoint G W))) :=
  (φ.val.app (op W)).hom.toAddMonoidHom

/-- The value of `φ` over a chart is linear over the ring of global functions of the chart. -/
theorem chartSectionValue_smul (W : Space.SmallEtale C S hS G.objects.obj)
    (c : FibredSite.objRing C S hS (quotientStack G).p
      ((pointwiseToQuotientStack G).obj (chartPoint G W)))
    (x : F.val.obj (op ((pointwiseToQuotientStack G).obj (chartPoint G W)))) :
    chartSectionValue φ W (c • x) = c • chartSectionValue φ W x := by
  have h := (φ.val.app (op W)).hom.map_smul c x
  have he := quotientStackProj_chartStructureHom_apply G W c
  have e1 : chartSectionValue φ W (c • x) = (φ.val.app (op W)).hom (c • x) := by
    refine congrArg (chartSectionValue φ W) ?_
    exact (congrArg (fun r : FibredSite.objRing C S hS (quotientStack G).p
      ((pointwiseToQuotientStack G).obj (chartPoint G W)) => r • x) he).symm
  refine e1.trans (h.trans ?_)
  exact congrArg (fun r : FibredSite.objRing C S hS (quotientStack G).p
      ((pointwiseToQuotientStack G).obj (chartPoint G W)) => r • chartSectionValue φ W x) he

/-- The morphism `x(c) ⟶ x(u_U W)` from (the image of) a charted point to its chart. -/
noncomputable abbrev ChartedPoint.chartMap (c : ChartedPoint G) :
    (chartedPointFunctor G).obj c ⟶ (pointwiseToQuotientStack G).obj (chartPoint G c.W) :=
  (pointwiseToQuotientStack G).map c.special

/-- The linear map `f ↦ b^*φ(f)` out of the sections of `ℱ` over the image of a chart, along a
morphism `b` to it. -/
noncomputable def seedAlong {z : (quotientStack G).obj} {W : Space.SmallEtale C S hS G.objects.obj}
    (b : z ⟶ (pointwiseToQuotientStack G).obj (chartPoint G W)) :
    letI := FibredSite.objAlgebra C S hS (quotientStack G).p b
    letI : Module (FibredSite.objRing C S hS (quotientStack G).p
        ((pointwiseToQuotientStack G).obj (chartPoint G W))) (H.val.obj (op z)) :=
      Module.compHom _ (algebraMap (FibredSite.objRing C S hS (quotientStack G).p
        ((pointwiseToQuotientStack G).obj (chartPoint G W)))
        (FibredSite.objRing C S hS (quotientStack G).p z))
    F.val.obj (op ((pointwiseToQuotientStack G).obj (chartPoint G W))) →ₗ[
      FibredSite.objRing C S hS (quotientStack G).p
        ((pointwiseToQuotientStack G).obj (chartPoint G W))] H.val.obj (op z) :=
  letI := FibredSite.objAlgebra C S hS (quotientStack G).p b
  letI : Module (FibredSite.objRing C S hS (quotientStack G).p
      ((pointwiseToQuotientStack G).obj (chartPoint G W))) (H.val.obj (op z)) :=
    Module.compHom _ (algebraMap (FibredSite.objRing C S hS (quotientStack G).p
      ((pointwiseToQuotientStack G).obj (chartPoint G W)))
      (FibredSite.objRing C S hS (quotientStack G).p z))
  { toFun := fun x => H.val.map b.op (chartSectionValue φ W x)
    map_add' := fun a b' => (congrArg (H.val.map b.op) (map_add _ a b')).trans
      (map_add (H.val.map b.op).hom _ _)
    map_smul' := fun r x => (congrArg (H.val.map b.op)
      (chartSectionValue_smul φ W r x)).trans (H.val.map_smul b.op r _) }

/-- **The extension of `φ` over a charted point**: the linear map `ℱ(x(c)) ⟶ ℋ(x(c))` sending
`b^*f` to `b^*φ(f)`, for `b` the morphism to the chart. -/
noncomputable def chartedExtension (c : ChartedPoint G) :
    F.val.obj (op ((chartedPointFunctor G).obj c)) →ₗ[
      FibredSite.objRing C S hS (quotientStack G).p ((chartedPointFunctor G).obj c)]
      H.val.obj (op ((chartedPointFunctor G).obj c)) :=
  FibredSite.extendAlong F hF c.chartMap c.hW c.hT H (seedAlong φ c.chartMap)

/-- The extension over a charted point is `φ` on restrictions of sections over the chart. -/
theorem chartedExtension_chartMap (c : ChartedPoint G)
    (x : F.val.obj (op ((pointwiseToQuotientStack G).obj (chartPoint G c.W)))) :
    chartedExtension φ hF c (F.val.map c.chartMap.op x) =
      H.val.map c.chartMap.op (chartSectionValue φ c.W x) :=
  FibredSite.extendAlong_map F hF c.chartMap c.hW c.hT H (seedAlong φ c.chartMap) x

/-- The extension over a charted point is compatible with restriction of the charted point. -/
theorem map_chartedExtension (c : ChartedPoint G) {T' : BigFppfOver C S hS}
    (k : T' ⟶ c.T) (hT' : IsAffineOver C S hS T')
    (σ : F.val.obj (op ((chartedPointFunctor G).obj c))) :
    H.val.map ((pointwiseToQuotientStack G).map (pointwiseSpecial G k c.pt)).op
        (chartedExtension φ hF c σ) =
      chartedExtension φ hF (c.restrict k hT')
        (F.val.map ((pointwiseToQuotientStack G).map (pointwiseSpecial G k c.pt)).op σ) := by
  have hn : (pointwiseToQuotientStack G).map (pointwiseSpecial G k c.pt) ≫ c.chartMap =
      (c.restrict k hT').chartMap :=
    ((pointwiseToQuotientStack G).map_comp _ _).symm.trans
      (congrArg (pointwiseToQuotientStack G).map (ChartedPoint.special_restrict c k hT'))
  refine FibredSite.map_extendAlong' F hF c.chartMap c.hW c.hT H _ _ hn hT' _ _
    (fun x => ?_) σ
  show H.val.map (c.restrict k hT').chartMap.op (chartSectionValue φ c.W x) =
    H.val.map ((pointwiseToQuotientStack G).map (pointwiseSpecial G k c.pt)).op
      (H.val.map c.chartMap.op (chartSectionValue φ c.W x))
  rw [← hn]
  exact H.val.map_comp_apply _ _ _

/-- The value of `χ : (x ∘ s)^*ℱ|_{R_étale} ⟶ (x ∘ s)^*ℋ|_{R_étale}` on sections over an étale
chart `V` of `R`. -/
noncomputable def arrowChartSectionValue (V : Space.SmallEtale C S hS G.arrows.obj) :
    F.val.obj (op ((pointwiseToQuotientStack G).obj (arrowChartPoint G V))) →+
      H.val.obj (op ((pointwiseToQuotientStack G).obj (arrowChartPoint G V))) :=
  (χ.val.app (op V)).hom.toAddMonoidHom

/-- The value of `χ` over a chart is linear over the ring of global functions of the chart. -/
theorem arrowChartSectionValue_smul (V : Space.SmallEtale C S hS G.arrows.obj)
    (c : FibredSite.objRing C S hS (quotientStack G).p
      ((pointwiseToQuotientStack G).obj (arrowChartPoint G V)))
    (x : F.val.obj (op ((pointwiseToQuotientStack G).obj (arrowChartPoint G V)))) :
    arrowChartSectionValue χ V (c • x) = c • arrowChartSectionValue χ V x := by
  have h := (χ.val.app (op V)).hom.map_smul c x
  have he := quotientStackSourceProj_chartStructureHom_apply G V c
  have e1 : arrowChartSectionValue χ V (c • x) = (χ.val.app (op V)).hom (c • x) := by
    refine congrArg (arrowChartSectionValue χ V) ?_
    exact (congrArg (fun r : FibredSite.objRing C S hS (quotientStack G).p
      ((pointwiseToQuotientStack G).obj (arrowChartPoint G V)) => r • x) he).symm
  refine e1.trans (h.trans ?_)
  exact congrArg (fun r : FibredSite.objRing C S hS (quotientStack G).p
      ((pointwiseToQuotientStack G).obj (arrowChartPoint G V)) => r • arrowChartSectionValue χ V x)
          he

/-- **The square through the source, on sections.**  If it commutes, `χ` carries the restriction
of a section of `ℱ` along a square of charts over `s` to the restriction of its image by `φ`. -/
theorem quotientStackSource_square_app
    (hsq : quotientStackSourceComparison G F ≫ χ =
      (Space.modulePullback C S hS G.source).map φ ≫ quotientStackSourceComparison G H)
    (d : Space.ChartDiagram C S hS G.arrows.obj G.objects.obj G.source.hom)
    (x : F.val.obj (op ((pointwiseToQuotientStack G).obj (chartPoint G d.V)))) :
    arrowChartSectionValue χ d.U (F.val.map ((pointwiseToQuotientStack G).map
        (chartDiagramPoint G G.source.hom d.U d.V d.g d.comm)).op x) =
      H.val.map ((pointwiseToQuotientStack G).map
        (chartDiagramPoint G G.source.hom d.U d.V d.g d.comm)).op (chartSectionValue φ d.V x) := by
  rw [← quotientStackSource_comparisonMorphism]
  exact Space.comparisonAlgebraicSpacesModules_square_app (ϕ := φ) (χ := χ) (hsq := hsq)
    C S hS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ d x

/-- **The square through the target, on sections**, over a square of charts over `t`. -/
theorem quotientStackTarget_square_app
    (hsq : quotientStackTargetComparison G F ≫ χ =
      (Space.modulePullback C S hS G.target).map φ ≫ quotientStackTargetComparison G H)
    (d : Space.ChartDiagram C S hS G.arrows.obj G.objects.obj G.target.hom)
    (g : arrowChartPoint G d.U ⟶
        ⟨(Space.SmallEtale.toOver C S hS G.arrows.obj).obj d.U,
          G.target.hom.app _ (yonedaEquiv d.U.obj.hom)⟩)
    (hg : Space.comparisonMorphism C S hS (fibredCategory C S hS G.arrows.obj).val.p
        (fibredCategory C S hS G.objects.obj).val.p
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        (quotientStackTargetLeg G) (quotientStackSourceLeg G ⋙ quotientStackProj G)
            (quotientStackProj G) (quotientStackTwoArrowIso G) G.target
                (quotientStackTargetChartIso G) d =
      (pointwiseToQuotientStack G).map
        (g ≫ chartDiagramPoint G G.target.hom d.U d.V d.g d.comm))
    (x : F.val.obj (op ((pointwiseToQuotientStack G).obj (chartPoint G d.V)))) :
    arrowChartSectionValue χ d.U (F.val.map ((pointwiseToQuotientStack G).map
        (g ≫ chartDiagramPoint G G.target.hom d.U d.V d.g d.comm)).op x) =
      H.val.map ((pointwiseToQuotientStack G).map
        (g ≫ chartDiagramPoint G G.target.hom d.U d.V d.g d.comm)).op (chartSectionValue φ d.V x)
            := by
  rw [← hg]
  exact Space.comparisonAlgebraicSpacesModules_square_app (ϕ := φ) (χ := χ) (hsq := hsq)
    C S hS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ d x

/-- The linear map `f ↦ j^*χ(f)` out of the sections of `ℱ` over the image of a chart of `R`. -/
noncomputable def arrowSeedAlong {z : (quotientStack G).obj}
    {V : Space.SmallEtale C S hS G.arrows.obj}
    (j : z ⟶ (pointwiseToQuotientStack G).obj (arrowChartPoint G V)) :
    letI := FibredSite.objAlgebra C S hS (quotientStack G).p j
    letI : Module (FibredSite.objRing C S hS (quotientStack G).p
        ((pointwiseToQuotientStack G).obj (arrowChartPoint G V))) (H.val.obj (op z)) :=
      Module.compHom _ (algebraMap (FibredSite.objRing C S hS (quotientStack G).p
        ((pointwiseToQuotientStack G).obj (arrowChartPoint G V)))
        (FibredSite.objRing C S hS (quotientStack G).p z))
    F.val.obj (op ((pointwiseToQuotientStack G).obj (arrowChartPoint G V))) →ₗ[
      FibredSite.objRing C S hS (quotientStack G).p
        ((pointwiseToQuotientStack G).obj (arrowChartPoint G V))] H.val.obj (op z) :=
  letI := FibredSite.objAlgebra C S hS (quotientStack G).p j
  letI : Module (FibredSite.objRing C S hS (quotientStack G).p
      ((pointwiseToQuotientStack G).obj (arrowChartPoint G V))) (H.val.obj (op z)) :=
    Module.compHom _ (algebraMap (FibredSite.objRing C S hS (quotientStack G).p
      ((pointwiseToQuotientStack G).obj (arrowChartPoint G V)))
      (FibredSite.objRing C S hS (quotientStack G).p z))
  { toFun := fun x => H.val.map j.op (arrowChartSectionValue χ V x)
    map_add' := fun a b' => (congrArg (H.val.map j.op) (map_add _ a b')).trans
      (map_add (H.val.map j.op).hom _ _)
    map_smul' := fun r x => (congrArg (H.val.map j.op)
      (arrowChartSectionValue_smul χ V r x)).trans (H.val.map_smul j.op r _) }

/-- The extension of `φ` along a morphism from an affine object to the image of an affine chart
of `U`. -/
noncomputable def extAlong {z : (quotientStack G).obj} {W : Space.SmallEtale C S hS G.objects.obj}
    (b : z ⟶ (pointwiseToQuotientStack G).obj (chartPoint G W))
    (hW : IsAffineOver C S hS ((Space.SmallEtale.toOver C S hS G.objects.obj).obj W))
    (hz : IsAffineOver C S hS ((quotientStack G).p.obj z)) :
    F.val.obj (op z) →ₗ[FibredSite.objRing C S hS (quotientStack G).p z] H.val.obj (op z) :=
  FibredSite.extendAlong F hF b hW hz H (seedAlong φ b)

/-- The extension depends only on the morphism. -/
theorem extAlong_congr {z : (quotientStack G).obj} {W : Space.SmallEtale C S hS G.objects.obj}
    {b b' : z ⟶ (pointwiseToQuotientStack G).obj (chartPoint G W)} (h : b = b')
    (hW : IsAffineOver C S hS ((Space.SmallEtale.toOver C S hS G.objects.obj).obj W))
    (hz : IsAffineOver C S hS ((quotientStack G).p.obj z)) :
    extAlong φ hF b hW hz = extAlong φ hF b' hW hz :=
  congrArg (fun b => extAlong φ hF b hW hz) h

/-- The extension of `χ` along a morphism from an affine object to the image of an affine chart
of `R`. -/
noncomputable def arrowExtAlong {z : (quotientStack G).obj}
    {V : Space.SmallEtale C S hS G.arrows.obj}
    (j : z ⟶ (pointwiseToQuotientStack G).obj (arrowChartPoint G V))
    (hV : IsAffineOver C S hS ((Space.SmallEtale.toOver C S hS G.arrows.obj).obj V))
    (hz : IsAffineOver C S hS ((quotientStack G).p.obj z)) :
    F.val.obj (op z) →ₗ[FibredSite.objRing C S hS (quotientStack G).p z] H.val.obj (op z) :=
  FibredSite.extendAlong F hF j hV hz H (arrowSeedAlong χ j)

/-- Extending `φ` along `j ≫ p` is extending `χ` along `j`, if `p` intertwines `χ` and `φ`. -/
private theorem extAlong_comp_eq_arrowExtAlong {z : (quotientStack G).obj}
    {V : Space.SmallEtale C S hS G.arrows.obj} {W : Space.SmallEtale C S hS G.objects.obj}
    (j : z ⟶ (pointwiseToQuotientStack G).obj (arrowChartPoint G V))
    (p : (pointwiseToQuotientStack G).obj (arrowChartPoint G V) ⟶
      (pointwiseToQuotientStack G).obj (chartPoint G W))
    (hp : ∀ x, arrowChartSectionValue χ V (F.val.map p.op x) =
      H.val.map p.op (chartSectionValue φ W x))
    (hV : IsAffineOver C S hS ((Space.SmallEtale.toOver C S hS G.arrows.obj).obj V))
    (hW : IsAffineOver C S hS ((Space.SmallEtale.toOver C S hS G.objects.obj).obj W))
    (hz : IsAffineOver C S hS ((quotientStack G).p.obj z)) :
    extAlong φ hF (j ≫ p) hW hz = arrowExtAlong χ hF j hV hz :=
  FibredSite.extendAlong_comp F hF j hV hz H p hW _ _ fun x =>
    (H.val.map_comp_apply p.op j.op _).trans (congrArg (H.val.map j.op) (hp x).symm)

/-- Extending `φ` along a morphism through a square of charts over the source is extending `χ`. -/
theorem extAlong_src {z : (quotientStack G).obj}
    (hsq : quotientStackSourceComparison G F ≫ χ =
      (Space.modulePullback C S hS G.source).map φ ≫ quotientStackSourceComparison G H)
    (d : Space.ChartDiagram C S hS G.arrows.obj G.objects.obj G.source.hom)
    (j : z ⟶ (pointwiseToQuotientStack G).obj (arrowChartPoint G d.U))
    (hV : IsAffineOver C S hS ((Space.SmallEtale.toOver C S hS G.arrows.obj).obj d.U))
    (hW : IsAffineOver C S hS ((Space.SmallEtale.toOver C S hS G.objects.obj).obj d.V))
    (hz : IsAffineOver C S hS ((quotientStack G).p.obj z)) :
    extAlong φ hF (j ≫ (pointwiseToQuotientStack G).map
        (chartDiagramPoint G G.source.hom d.U d.V d.g d.comm)) hW hz =
      arrowExtAlong χ hF j hV hz := by
  exact extAlong_comp_eq_arrowExtAlong φ χ hF j _
    (quotientStackSource_square_app φ χ hsq d) hV hW hz

/-- Extending `φ` along a morphism through a square of charts over the target is extending `χ`. -/
theorem extAlong_tgt {z : (quotientStack G).obj}
    (hsq : quotientStackTargetComparison G F ≫ χ =
      (Space.modulePullback C S hS G.target).map φ ≫ quotientStackTargetComparison G H)
    (d : Space.ChartDiagram C S hS G.arrows.obj G.objects.obj G.target.hom)
    (g : arrowChartPoint G d.U ⟶
        ⟨(Space.SmallEtale.toOver C S hS G.arrows.obj).obj d.U,
          G.target.hom.app _ (yonedaEquiv d.U.obj.hom)⟩)
    (hg : Space.comparisonMorphism C S hS (fibredCategory C S hS G.arrows.obj).val.p
        (fibredCategory C S hS G.objects.obj).val.p
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        (quotientStackTargetLeg G) (quotientStackSourceLeg G ⋙ quotientStackProj G)
            (quotientStackProj G) (quotientStackTwoArrowIso G) G.target
                (quotientStackTargetChartIso G) d =
      (pointwiseToQuotientStack G).map
        (g ≫ chartDiagramPoint G G.target.hom d.U d.V d.g d.comm))
    (j : z ⟶ (pointwiseToQuotientStack G).obj (arrowChartPoint G d.U))
    (hV : IsAffineOver C S hS ((Space.SmallEtale.toOver C S hS G.arrows.obj).obj d.U))
    (hW : IsAffineOver C S hS ((Space.SmallEtale.toOver C S hS G.objects.obj).obj d.V))
    (hz : IsAffineOver C S hS ((quotientStack G).p.obj z)) :
    extAlong φ hF (j ≫ (pointwiseToQuotientStack G).map
        (g ≫ chartDiagramPoint G G.target.hom d.U d.V d.g d.comm)) hW hz =
      arrowExtAlong χ hF j hV hz := by
  exact extAlong_comp_eq_arrowExtAlong φ χ hF j _
    (quotientStackTarget_square_app φ χ hsq d g hg) hV hW hz

/-- **The extension over a charted point is compatible with every arrow to a chart.**  For an
arrow `q` of the pointwise groupoid fibration from a charted point to the point of an affine
chart `W'` of `U` (a point of `R`, possibly not an identity), the extension sends `q^*f` to
`q^*φ(f)`.  Fppf locally on the base, `q` factors through an affine chart of `R` carrying
squares of charts over the source and the target, and both are then the extension of `χ`. -/
theorem chartedExtension_naturality
    (hsqs : quotientStackSourceComparison G F ≫ χ =
      (Space.modulePullback C S hS G.source).map φ ≫ quotientStackSourceComparison G H)
    (hsqt : quotientStackTargetComparison G F ≫ χ =
      (Space.modulePullback C S hS G.target).map φ ≫ quotientStackTargetComparison G H)
    (c : ChartedPoint G) {W' : Space.SmallEtale C S hS G.objects.obj}
    (hW' : IsAffineOver C S hS ((Space.SmallEtale.toOver C S hS G.objects.obj).obj W'))
    (q : c.toPoint ⟶ chartPoint G W')
    (x : F.val.obj (op ((pointwiseToQuotientStack G).obj (chartPoint G W')))) :
    chartedExtension φ hF c (F.val.map ((pointwiseToQuotientStack G).map q).op x) =
      H.val.map ((pointwiseToQuotientStack G).map q).op (chartSectionValue φ W' x) := by
  let ρ := pointwiseArrow G q
  have hρs : G.source.hom.app _ ρ = c.pt :=
    (G.toGroupoidInFunctors.evaluationArrowEquiv _ _ _ q.fiber).2.1
  refine pointwiseSections_ext G H c.toPoint (Space.generate_twoChartPresieve_mem C S hS
    G.source G.target ρ c.W W' c.g q.base (hρs.trans c.hpt)
    (G.toGroupoidInFunctors.evaluationArrowEquiv _ _ _ q.fiber).2.2) (fun T' k hk => ?_)
  obtain ⟨hT', V, hV, kV, ds, dt, hcs, hct, hρk, hg₁, hg₂⟩ := hk
  let dS : Space.ChartDiagram C S hS G.arrows.obj G.objects.obj G.source.hom := ⟨V, c.W, ds, hcs⟩
  let dT : Space.ChartDiagram C S hS G.arrows.obj G.objects.obj G.target.hom := ⟨V, W', dt, hct⟩
  obtain ⟨g₀, hg₀b, hg₀a, hg₀⟩ := quotientStackTarget_comparisonMorphism G dT
  have hK : G.objects.obj.map k.op c.pt =
      G.objects.obj.map kV.op (G.source.hom.app _ (yonedaEquiv V.obj.hom)) := by
    rw [← NatTrans.naturality_apply, ← hρk, NatTrans.naturality_apply, hρs]
  let mK : (c.restrict k hT').toPoint ⟶ arrowChartPoint G V := ⟨kV, eqToHom hK⟩
  have hmK : pointwiseArrow G mK = G.toGroupoidInFunctors.identity _ (c.restrict k hT').pt :=
    evaluationArrow_eqToHom_identity G.toGroupoidInFunctors _ hK
  have h₁ : mK ≫ chartDiagramPoint G G.source.hom dS.U dS.V dS.g dS.comm =
      (c.restrict k hT').special := by
    apply pointwiseHom_ext G.toGroupoidInFunctors
    · exact hg₁.symm
    · refine (pointwiseArrow_comp_of_left G _ _ hmK).trans ?_
      rw [pointwiseArrow_chartDiagramPoint]
      refine (Deformation.evalMap_identity G.toGroupoidInFunctors kV.op _).trans ?_
      exact (congrArg (G.toGroupoidInFunctors.identity _) hK.symm).trans
        (evaluationArrow_eqToHom_identity G.toGroupoidInFunctors _ (c.restrict k hT').hpt).symm
  have h₂ : mK ≫ g₀ ≫ chartDiagramPoint G G.target.hom dT.U dT.V dT.g dT.comm =
      pointwiseSpecial G k c.pt ≫ q := by
    apply pointwiseHom_ext G.toGroupoidInFunctors
    · show kV ≫ g₀.base ≫ dt = k ≫ q.base
      rw [hg₀b, Category.id_comp, hg₂]
    · refine (pointwiseArrow_comp_of_left G _ _ hmK).trans ?_
      refine Eq.trans ?_ (pointwiseArrow_comp_of_left G _ _ rfl).symm
      rw [pointwiseArrow_comp_of_right G _ _ (pointwiseArrow_chartDiagramPoint G _ _ _ _ _)]
      exact (congrArg (G.arrows.obj.map kV.op) hg₀a).trans hρk.symm
  let j := (pointwiseToQuotientStack G).map mK
  have e₁ : chartedExtension φ hF (c.restrict k hT') = arrowExtAlong χ hF j hV hT' := by
    refine Eq.trans ?_ (extAlong_src φ χ hF hsqs dS j hV c.hW hT')
    exact extAlong_congr φ hF ((congrArg (pointwiseToQuotientStack G).map h₁).symm.trans
      ((pointwiseToQuotientStack G).map_comp _ _)) _ _
  have e₂ : extAlong φ hF ((pointwiseToQuotientStack G).map (pointwiseSpecial G k c.pt ≫ q))
      hW' hT' = arrowExtAlong χ hF j hV hT' := by
    refine Eq.trans ?_ (extAlong_tgt φ χ hF hsqt dT g₀ hg₀ j hV hW' hT')
    exact extAlong_congr φ hF ((congrArg (pointwiseToQuotientStack G).map h₂).symm.trans
      ((pointwiseToQuotientStack G).map_comp _ _)) _ _
  refine (map_chartedExtension φ hF c k hT' _).trans ?_
  rw [e₁, ← e₂]
  have h0' : (pointwiseToQuotientStack G).map (pointwiseSpecial G k c.pt ≫ q) =
      (pointwiseToQuotientStack G).map (pointwiseSpecial G k c.pt) ≫
        (pointwiseToQuotientStack G).map q :=
    (pointwiseToQuotientStack G).map_comp _ _
  have hx : F.val.map ((pointwiseToQuotientStack G).map (pointwiseSpecial G k c.pt)).op
      (F.val.map ((pointwiseToQuotientStack G).map q).op x) =
      F.val.map ((pointwiseToQuotientStack G).map (pointwiseSpecial G k c.pt ≫ q)).op x := by
    rw [h0', op_comp]
    exact (F.val.map_comp_apply ((pointwiseToQuotientStack G).map q).op
      ((pointwiseToQuotientStack G).map (pointwiseSpecial G k c.pt)).op x).symm
  refine (congrArg (extAlong φ hF ((pointwiseToQuotientStack G).map
    (pointwiseSpecial G k c.pt ≫ q)) hW' hT') hx).trans ?_
  refine (FibredSite.extendAlong_map F hF
    ((pointwiseToQuotientStack G).map (pointwiseSpecial G k c.pt ≫ q)) hW' hT' H _ x).trans ?_
  show H.val.map ((pointwiseToQuotientStack G).map (pointwiseSpecial G k c.pt ≫ q)).op
    (chartSectionValue φ W' x) = _
  rw [h0', op_comp]
  exact H.val.map_comp_apply _ _ _

end Extension

end AlgebraicGeometry.Stack

end
