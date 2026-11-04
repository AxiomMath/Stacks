module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionStructureMap
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSharpChartPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStructureMapComp
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleDirectImage

/-!
# Projecting the direct image of a module to a commutative square of charts

Let `f : X' ⟶ X` be a morphism of algebraic spaces over a scheme `S` and let `G` be an
`𝒪_{X'}`-module.  The sections of the direct image `f_*G` over an étale chart `V` of `X` are the
limit of the sections of `G` over the étale charts of `X'` above `X' ×_X V`.  A commutative
square `d` of étale scheme charts over `f` — a chart `U` of `X'`, a chart `V` of `X` and a
morphism of schemes `U ⟶ V` over `f` — is such a chart, so it projects the sections of `f_*G`
over `V` to the sections of `G` over `U`.

This file names that projection and records how it interacts with the module structures: it is
additive, it carries the action of a regular function `a` on `V` to the action of the pullback
of `a` to `U`, and it is natural in both charts of the square.

## Main definitions

* `AlgebraicGeometry.Space.chartDiagramArrow`: the étale chart of `X'` above `X' ×_X V` attached
  to a square of charts.
* `AlgebraicGeometry.Space.chartDiagramProjection`: the projection of the sections of `f_*G`
  over `V` to the sections of `G` over `U`, as an additive map.

## Main results

* `AlgebraicGeometry.Space.chartDiagramProjection_smul`: the projection carries the action of a
  regular function on `V` to the action of its pullback to `U`.
* `AlgebraicGeometry.Space.chartDiagramProjection_ext`: two sections of `f_*G` over `V` with
  the same projections to every square with target chart `V` are equal.
* `AlgebraicGeometry.Space.chartDiagramProjection_naturality`: naturality in a morphism of
  squares of charts.

## References

* [Stacks Project, Tag 03G3](https://stacks.math.columbia.edu/tag/03G3)
* [Stacks Project, Tag 03G4](https://stacks.math.columbia.edu/tag/03G4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite
open Stacks.Sheaves.ToposPullback

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X X' : AlgebraicSpaces B S hS} (f : X' ⟶ X)

/-- The étale chart of `X'` above the cartesian base change `X' ×_X V` attached to a commutative
square of étale scheme charts over `f`. -/
noncomputable abbrev chartDiagramArrow (d : ChartDiagram B S hS X'.1 X.1 f.hom) :
    StructuredArrow (op (chartBaseChange B S hS f d.V)) (comparisonFunctor B S hS X').op :=
  StructuredArrow.mk (Y := op d.U) (baseChangeArrowOfChartDiagram B S hS f d).op

/-- The chartwise morphism of the arrow attached to a square is the vertical morphism of the
square. -/
theorem chartBaseChangeMap_chartDiagramArrow (d : ChartDiagram B S hS X'.1 X.1 f.hom) :
    chartBaseChangeMap B S hS f d.V (chartDiagramArrow B S hS f d) = d.g :=
  chartDiagramOfBaseChangeArrow_baseChangeArrow_g B S hS f d

/-- The projection of the sections over `V` of the direct image of a sheaf of sets to the
sections over the chart of `X'` of a square `d`, as a natural transformation of functors on
sheaves of sets. -/
noncomputable def chartDiagramProjectionNat (d : ChartDiagram B S hS X'.1 X.1 f.hom) :
    smallEtaleDirectImage B S hS f ⋙ sectionsFunctor (SmallEtale.topology B S hS X.1) (op d.V) ⟶
      sectionsFunctor (SmallEtale.topology B S hS X'.1) (op d.U) :=
  Functor.whiskerRight (smallEtaleDirectImageRanIso B S hS f).hom
      (sectionsFunctor (SmallEtale.topology B S hS X.1) (op d.V)) ≫
    chartProjection B S hS f d.V (chartDiagramArrow B S hS f d)

/-- The projection of the structure map is pullback of regular functions along the vertical
morphism of the square. -/
theorem chartDiagramProjectionNat_structureSharpSet (d : ChartDiagram B S hS X'.1 X.1 f.hom)
    (a : (structureSetSheaf B S hS X).obj.obj (op d.V)) :
    (chartDiagramProjectionNat B S hS f d).app (structureSetSheaf B S hS X')
        ((structureSharpSet B S hS f).hom.app (op d.V) a) =
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map d.g).op).hom a := by
  have h := congrArg (fun m => m.hom.app (op d.V) a) (structureSharpSet_comp_ranIso B S hS f)
  change (chartProjection B S hS f d.V (chartDiagramArrow B S hS f d)).app
      (structureSetSheaf B S hS X')
      (((smallEtaleDirectImageRanIso B S hS f).hom.app (structureSetSheaf B S hS X')).hom.app
        (op d.V) ((structureSharpSet B S hS f).hom.app (op d.V) a)) = _
  refine (congrArg _ h).trans ?_
  refine (chartProjection_structureMapApp B S hS f d.V (chartDiagramArrow B S hS f d) a).trans ?_
  rw [chartPullback, chartBaseChangeMap_chartDiagramArrow]
  rfl



section Module

variable (G : Modules.{u, u} B S hS X'.1 X'.2)

/-- On the sections over one object, the transported addition is the addition of sections. -/
theorem _root_.CategoryTheory.Sheaf.moduleAddObj_sectionsFunctor.{w, v₁, u₁} {C : Type u₁}
    [Category.{v₁} C] {J : GrothendieckTopology C} [J.HasSheafCompose (forget RingCat.{w})]
    [J.HasSheafCompose (forget AddCommGrpCat.{w})] (R : Sheaf J RingCat.{w})
    (G : SheafOfModules.{w} R) (X : Cᵒᵖ) (a b : G.val.obj X) :
    moduleAddObj R G (sectionsFunctor J X) a b = a + b :=
  sectionsFunctor_map_moduleAddHom R G X a b

/-- On the sections over one object, the transported scalar action is the action of sections. -/
theorem _root_.CategoryTheory.Sheaf.moduleSMulObj_sectionsFunctor.{w, v₁, u₁} {C : Type u₁}
    [Category.{v₁} C] {J : GrothendieckTopology C} [J.HasSheafCompose (forget RingCat.{w})]
    [J.HasSheafCompose (forget AddCommGrpCat.{w})] (R : Sheaf J RingCat.{w})
    (G : SheafOfModules.{w} R) (X : Cᵒᵖ) (a : R.obj.obj X) (b : G.val.obj X) :
    moduleSMulObj R G (sectionsFunctor J X) a b = a • b :=
  sectionsFunctor_map_moduleSMulHom R G X a b

/-- **The projection of the direct image of a module to a square of charts.**  A section of
`f_*G` over the chart `V` of a square `d` of étale scheme charts over `f` is sent to its
component over the chart `U` of `X'` of the square. -/
noncomputable def chartDiagramProjection (d : ChartDiagram B S hS X'.1 X.1 f.hom) :
    ((modulePushforward B S hS f).obj G).val.obj (op d.V) →+ G.val.obj (op d.U) :=
  AddMonoidHom.mk' (fun m => (chartDiagramProjectionNat B S hS f d).app
      (moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS X') G) m) fun x y =>
    (moduleAddObj_naturality (structureRingSheaf B S hS X') G
      (chartDiagramProjectionNat B S hS f d) x y).trans
      (CategoryTheory.Sheaf.moduleAddObj_sectionsFunctor (structureRingSheaf B S hS X') G
        (op d.U) _ _)

/-- The projection of a section of the direct image is the value at `G` of the natural
projection of section functors `AlgebraicGeometry.Space.chartDiagramProjectionNat`. -/
theorem chartDiagramProjection_apply (d : ChartDiagram B S hS X'.1 X.1 f.hom)
    (m : ((modulePushforward B S hS f).obj G).val.obj (op d.V)) :
    chartDiagramProjection B S hS f G d m = (chartDiagramProjectionNat B S hS f d).app
      (moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS X') G) m := rfl

/-- **The projection is linear over the pullback of regular functions.**  The action of a
regular function `a` on the chart `V` of `X` is carried to the action of the pullback of `a`
along the vertical morphism of the square. -/
theorem chartDiagramProjection_smul (d : ChartDiagram B S hS X'.1 X.1 f.hom)
    (a : (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).obj.obj
      (op d.V))
    (m : ((modulePushforward B S hS f).obj G).val.obj (op d.V)) :
    chartDiagramProjection B S hS f G d (a • m) =
      (show (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS X'.1 X'.2).O).obj.obj (op d.U) from
          (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map d.g).op).hom a) •
        chartDiagramProjection B S hS f G d m := by
  refine (moduleSMulObj_naturality (structureRingSheaf B S hS X') G
    (chartDiagramProjectionNat B S hS f d) _ m).trans ?_
  refine (CategoryTheory.Sheaf.moduleSMulObj_sectionsFunctor (structureRingSheaf B S hS X') G
    (op d.U) _ _).trans ?_
  exact congrArg (fun r : (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X'.1 X'.2).O).obj.obj (op d.U) =>
        r • chartDiagramProjection B S hS f G d m)
    (chartDiagramProjectionNat_structureSharpSet B S hS f d a)

/-- The projection of the image of a section under the direct image of a morphism of sheaves
of sets is the morphism applied to the projection. -/
theorem chartDiagramProjectionNat_map (d : ChartDiagram B S hS X'.1 X.1 f.hom)
    {E E' : Sheaf (SmallEtale.topology B S hS X'.1) (Type u)} (ε : E ⟶ E')
    (x : (smallEtaleDirectImage B S hS f ⋙
      sectionsFunctor (SmallEtale.topology B S hS X.1) (op d.V)).obj E) :
    (chartDiagramProjectionNat B S hS f d).app E'
        ((smallEtaleDirectImage B S hS f ⋙
          sectionsFunctor (SmallEtale.topology B S hS X.1) (op d.V)).map ε x) =
      ε.hom.app (op d.U) ((chartDiagramProjectionNat B S hS f d).app E x) :=
  Functor.natTrans_app_map_apply (chartDiagramProjectionNat B S hS f d) ε x

end Module


section Naturality

/-- The projections of the limit computing the sections of a direct image are compatible with
morphisms of charts of `X'` above `X' ×_X V`: the cone condition, for an arbitrary sheaf of
sets. -/
theorem chartProjection_naturality_sheaf (V : SmallEtale B S hS X.1)
    {j₁ j₂ : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X').op}
    (φ : j₁ ⟶ j₂) (E : Sheaf (SmallEtale.topology B S hS X'.1) (Type u))
    (t : ((comparisonFunctor B S hS X').op.ran.obj E.obj).obj
      (op (chartBaseChange B S hS f V))) :
    (chartProjection B S hS f V j₂).app E t =
      E.obj.map φ.right ((chartProjection B S hS f V j₁).app E t) := by
  rw [chartProjection_app_apply_sheaf, chartProjection_app_apply_sheaf]
  exact (congrArg (fun z => z t) (((Functor.RightExtension.mk _
    ((comparisonFunctor B S hS X').op.ranCounit.app E.obj)).coneAt
    (op (chartBaseChange B S hS f V))).w φ)).symm


/-- The comparison of the direct image with the right Kan extension form is injective on the
sections over a chart. -/
private theorem smallEtaleDirectImageRanIso_hom_app_injective
    (E : Sheaf (SmallEtale.topology B S hS X'.1) (Type u)) (V : SmallEtale B S hS X.1) :
    Function.Injective (((smallEtaleDirectImageRanIso B S hS f).hom.app E).hom.app (op V)) := by
  intro x y hxy
  have := congrArg (((smallEtaleDirectImageRanIso B S hS f).inv.app E).hom.app (op V)) hxy
  have hc : ∀ z, ((smallEtaleDirectImageRanIso B S hS f).inv.app E).hom.app (op V)
      (((smallEtaleDirectImageRanIso B S hS f).hom.app E).hom.app (op V) z) = z := fun z =>
    congrArg (fun k => k.hom.app (op V) z)
      ((smallEtaleDirectImageRanIso B S hS f).hom_inv_id_app E)
  rwa [hc, hc] at this

/-- **The projection to a square through which the base-changed chart factors is injective.**
For a representable `f`, the sections of a direct image over a chart `V` of `X` are attained at
the base-changed chart `X' ×_X V`, which is initial among the charts above `X' ×_X V`; so the
projection to any square receiving the base-changed chart over `V` loses nothing. -/
theorem chartDiagramProjectionNat_injective (hf : yoneda.relativelyRepresentable f.hom)
    (d : ChartDiagram B S hS X'.1 X.1 f.hom)
    (k : (smallBaseChange B S hS f hf).obj d.V ⟶ d.U)
    (hk : (SmallEtale.toOver B S hS X'.1).map k ≫ d.g = hf.snd d.V.1.hom)
    (E : Sheaf (SmallEtale.topology B S hS X'.1) (Type u)) :
    Function.Injective ((chartDiagramProjectionNat B S hS f d).app E) := by
  have hw : (chartDiagramArrow B S hS f d).hom ≫ (comparisonFunctor B S hS X').op.map k.op =
      (chartBaseChangeArrow B S hS f hf d.V).hom := by
    apply Quiver.Hom.unop_inj
    apply chartBaseChangeMap_injective B S hS f
    change chartBaseChangeMap B S hS f d.V (StructuredArrow.mk
        (Y := op ((smallBaseChange B S hS f hf).obj d.V))
        ((comparisonFunctor B S hS X').map k ≫ baseChangeArrowOfChartDiagram B S hS f d).op) =
      chartBaseChangeMap B S hS f d.V (chartBaseChangeArrow B S hS f hf d.V)
    rw [chartBaseChangeMap_comp B S hS f d.V (j₁ := chartDiagramArrow B S hS f d)
        (j₂ := StructuredArrow.mk (Y := op ((smallBaseChange B S hS f hf).obj d.V))
          ((comparisonFunctor B S hS X').map k ≫ baseChangeArrowOfChartDiagram B S hS f d).op)
        (StructuredArrow.homMk k.op rfl),
      chartBaseChangeMap_chartDiagramArrow, chartBaseChangeMap_chartBaseChangeArrow]
    exact hk
  have hiso : IsIso (((Functor.RightExtension.mk _
      ((comparisonFunctor B S hS X').op.ranCounit.app E.obj)).coneAt
      (op (chartBaseChange B S hS f d.V))).π.app (chartBaseChangeArrow B S hS f hf d.V)) :=
    (chartIsLimitSheaf B S hS f d.V E).isIso_π_app_of_isInitial _
      (chartBaseChangeArrowIsInitial B S hS f hf d.V)
  have hinjRan : Function.Injective
      ((chartProjection B S hS f d.V (chartDiagramArrow B S hS f d)).app E) := by
    intro a b hab
    apply ((isIso_iff_bijective _).mp hiso).1
    have ha := chartProjection_naturality_sheaf B S hS f d.V
      (StructuredArrow.homMk (f := chartDiagramArrow B S hS f d)
        (f' := chartBaseChangeArrow B S hS f hf d.V) k.op hw) E a
    have hb' := chartProjection_naturality_sheaf B S hS f d.V
      (StructuredArrow.homMk (f := chartDiagramArrow B S hS f d)
        (f' := chartBaseChangeArrow B S hS f hf d.V) k.op hw) E b
    have e1 := chartProjection_app_apply_sheaf B S hS f d.V E
      (chartBaseChangeArrow B S hS f hf d.V) a
    have e2 := chartProjection_app_apply_sheaf B S hS f d.V E
      (chartBaseChangeArrow B S hS f hf d.V) b
    exact e1.symm.trans ((ha.trans ((congrArg (E.obj.map k.op) hab).trans hb'.symm)).trans e2)
  exact hinjRan.comp (smallEtaleDirectImageRanIso_hom_app_injective B S hS f E d.V)

/-- `AlgebraicGeometry.Space.chartProjection_map` for an arbitrary sheaf of sets. -/
theorem chartProjection_map_sheaf {V₁ V₂ : SmallEtale B S hS X.1} (m : V₁ ⟶ V₂)
    (j : StructuredArrow (op (chartBaseChange B S hS f V₁)) (comparisonFunctor B S hS X').op)
    (E : Sheaf (SmallEtale.topology B S hS X'.1) (Type u))
    (a : ((comparisonFunctor B S hS X').op.ran.obj E.obj).obj
      (op (chartBaseChange B S hS f V₂))) :
    (chartProjection B S hS f V₁ j).app E
        (((comparisonFunctor B S hS X').op.ran.obj E.obj).map
          ((spacesBaseChange B S hS f).functor.map
            ((comparisonFunctor B S hS X).map m)).op a) =
      (chartProjection B S hS f V₂ (StructuredArrow.mk
        (((spacesBaseChange B S hS f).functor.map
          ((comparisonFunctor B S hS X).map m)).op ≫ j.hom))).app E a := by
  rw [chartProjection_app_apply_sheaf, chartProjection_app_apply_sheaf]
  simp only [Functor.RightExtension.coneAt_π_app, types_comp_apply, Functor.RightExtension.mk_left,
    Functor.RightExtension.mk_hom, StructuredArrow.mk_right, StructuredArrow.mk_hom_eq_self,
    ← Functor.map_comp_apply]
  rfl

/-- The restriction maps of the right Kan extension form of the direct image are those of the
right Kan extension along the comparison functor, at the base-changed charts. -/
theorem smallEtaleDirectImageRan_map_apply {V₁ V₂ : SmallEtale B S hS X.1} (m : V₁ ⟶ V₂)
    (E : Sheaf (SmallEtale.topology B S hS X'.1) (Type u))
    (a : (smallEtaleDirectImageRan B S hS f ⋙
      sectionsFunctor (SmallEtale.topology B S hS X.1) (op V₂)).obj E) :
    ((smallEtaleDirectImageRan B S hS f).obj E).obj.map m.op a =
      ((comparisonFunctor B S hS X').op.ran.obj E.obj).map
          ((spacesBaseChange B S hS f).functor.map
            ((comparisonFunctor B S hS X).map m)).op a := rfl

/-- **Naturality of the projection.**  A morphism of squares — a morphism `i : U' ⟶ U` of charts
of `X'` and a morphism `m : V' ⟶ V` of charts of `X` under which the two vertical morphisms
agree — carries the projection to the larger square, followed by restriction along `i`, to
restriction along `m` followed by the projection to the smaller square. -/
theorem chartDiagramProjectionNat_naturality (d d' : ChartDiagram B S hS X'.1 X.1 f.hom)
    (i : d'.U ⟶ d.U) (m : d'.V ⟶ d.V)
    (h : (SmallEtale.toOver B S hS X'.1).map i ≫ d.g =
      d'.g ≫ (SmallEtale.toOver B S hS X.1).map m)
    (E : Sheaf (SmallEtale.topology B S hS X'.1) (Type u))
    (x : (smallEtaleDirectImage B S hS f ⋙
      sectionsFunctor (SmallEtale.topology B S hS X.1) (op d.V)).obj E) :
    (chartDiagramProjectionNat B S hS f d').app E
        (((smallEtaleDirectImage B S hS f).obj E).obj.map m.op x) =
      E.obj.map i.op ((chartDiagramProjectionNat B S hS f d).app E x) := by
  have hw : (chartDiagramArrow B S hS f d).hom ≫ (comparisonFunctor B S hS X').op.map i.op =
      (StructuredArrow.mk (Y := op d'.U)
        (((spacesBaseChange B S hS f).functor.map ((comparisonFunctor B S hS X).map m)).op ≫
          (chartDiagramArrow B S hS f d').hom)).hom := by
    apply Quiver.Hom.unop_inj
    apply chartBaseChangeMap_injective B S hS f
    change chartBaseChangeMap B S hS f d.V (StructuredArrow.mk (Y := op d'.U)
        ((comparisonFunctor B S hS X').map i ≫ baseChangeArrowOfChartDiagram B S hS f d).op) =
      chartBaseChangeMap B S hS f d.V (StructuredArrow.mk (Y := op d'.U)
        (((spacesBaseChange B S hS f).functor.map ((comparisonFunctor B S hS X).map m)).op ≫
          (chartDiagramArrow B S hS f d').hom))
    rw [chartBaseChangeMap_comp B S hS f d.V (j₁ := chartDiagramArrow B S hS f d)
        (j₂ := StructuredArrow.mk (Y := op d'.U)
          ((comparisonFunctor B S hS X').map i ≫ baseChangeArrowOfChartDiagram B S hS f d).op)
        (StructuredArrow.homMk i.op rfl), chartBaseChangeMap_chartDiagramArrow,
      chartBaseChangeMap_map B S hS f m (chartDiagramArrow B S hS f d'),
      chartBaseChangeMap_chartDiagramArrow]
    exact h
  have h0 := NatTrans.naturality_apply ((smallEtaleDirectImageRanIso B S hS f).hom.app E).hom
    m.op x
  have h1 := chartProjection_map_sheaf B S hS f m (chartDiagramArrow B S hS f d') E
    (((smallEtaleDirectImageRanIso B S hS f).hom.app E).hom.app (op d.V) x)
  have h2 := chartProjection_naturality_sheaf B S hS f d.V
    (StructuredArrow.homMk (f := chartDiagramArrow B S hS f d) (f' := StructuredArrow.mk
      (Y := op d'.U)
      (((spacesBaseChange B S hS f).functor.map ((comparisonFunctor B S hS X).map m)).op ≫
        (chartDiagramArrow B S hS f d').hom)) i.op hw) E
    (((smallEtaleDirectImageRanIso B S hS f).hom.app E).hom.app (op d.V) x)
  have h01 := congrArg ((chartProjection B S hS f d'.V (chartDiagramArrow B S hS f d')).app E) h0
  have hr := congrArg ((chartProjection B S hS f d'.V (chartDiagramArrow B S hS f d')).app E)
    (smallEtaleDirectImageRan_map_apply B S hS f m E
      (((smallEtaleDirectImageRanIso B S hS f).hom.app E).hom.app (op d.V) x))
  exact h01.trans (hr.trans (h1.trans h2))

/-- `AlgebraicGeometry.Space.chartDiagramProjectionNat_naturality` for the direct image of a
module. -/
theorem chartDiagramProjection_naturality (G : Modules.{u, u} B S hS X'.1 X'.2)
    (d d' : ChartDiagram B S hS X'.1 X.1 f.hom) (i : d'.U ⟶ d.U) (m : d'.V ⟶ d.V)
    (h : (SmallEtale.toOver B S hS X'.1).map i ≫ d.g =
      d'.g ≫ (SmallEtale.toOver B S hS X.1).map m)
    (x : ((modulePushforward B S hS f).obj G).val.obj (op d.V)) :
    chartDiagramProjection B S hS f G d' (((modulePushforward B S hS f).obj G).val.map m.op x) =
      G.val.map i.op (chartDiagramProjection B S hS f G d x) :=
  chartDiagramProjectionNat_naturality B S hS f d d' i m h _ x

/-- **Sections of a direct image are determined by their projections to squares.** -/
theorem chartDiagramProjectionNat_ext (V : SmallEtale B S hS X.1)
    (E : Sheaf (SmallEtale.topology B S hS X'.1) (Type u))
    {a b : (smallEtaleDirectImage B S hS f ⋙
      sectionsFunctor (SmallEtale.topology B S hS X.1) (op V)).obj E}
    (h : ∀ d : ChartDiagram B S hS X'.1 X.1 f.hom, ∀ hV : d.V = V,
      (chartDiagramProjectionNat B S hS f d).app E (hV ▸ a) =
        (chartDiagramProjectionNat B S hS f d).app E (hV ▸ b)) : a = b := by
  have hran : ((smallEtaleDirectImageRanIso B S hS f).hom.app E).hom.app (op V) a =
      ((smallEtaleDirectImageRanIso B S hS f).hom.app E).hom.app (op V) b := by
    refine chartProjection_ext_sheaf B S hS f V E (fun j => ?_)
    let dj := chartDiagramOfBaseChangeArrow B S hS f j.right.unop V j.hom.unop
    have hw : (chartDiagramArrow B S hS f dj).hom ≫ (comparisonFunctor B S hS X').op.map (𝟙 _) =
        j.hom := by
      rw [CategoryTheory.Functor.map_id, Category.comp_id]
      exact congrArg Quiver.Hom.op
        (baseChangeArrowOfChartDiagram_chartDiagram B S hS f j.right.unop V j.hom.unop)
    have ha := chartProjection_naturality_sheaf B S hS f V
      (StructuredArrow.homMk (f := chartDiagramArrow B S hS f dj) (f' := j) (𝟙 _) hw) E
      (((smallEtaleDirectImageRanIso B S hS f).hom.app E).hom.app (op V) a)
    have hb := chartProjection_naturality_sheaf B S hS f V
      (StructuredArrow.homMk (f := chartDiagramArrow B S hS f dj) (f' := j) (𝟙 _) hw) E
      (((smallEtaleDirectImageRanIso B S hS f).hom.app E).hom.app (op V) b)
    exact ha.trans ((congrArg (E.obj.map (𝟙 (op dj.U))) (h dj rfl)).trans hb.symm)
  exact smallEtaleDirectImageRanIso_hom_app_injective B S hS f E V hran

/-- **Sections of the direct image of a module are determined by their projections to
squares.** -/
theorem chartDiagramProjection_ext (G : Modules.{u, u} B S hS X'.1 X'.2)
    (V : SmallEtale B S hS X.1) {a b : ((modulePushforward B S hS f).obj G).val.obj (op V)}
    (h : ∀ (U : SmallEtale B S hS X'.1)
      (g : (SmallEtale.toOver B S hS X'.1).obj U ⟶ (SmallEtale.toOver B S hS X.1).obj V)
      (hc : U.1.hom ≫ f.hom = yoneda.map g ≫ V.1.hom),
      chartDiagramProjection B S hS f G ⟨U, V, g, hc⟩ a =
        chartDiagramProjection B S hS f G ⟨U, V, g, hc⟩ b) : a = b :=
  chartDiagramProjectionNat_ext B S hS f V _ fun d hV => by
    subst hV
    exact h d.U d.g d.comm

end Naturality

end AlgebraicGeometry.Space

end
