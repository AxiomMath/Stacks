module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineBaseChangeChart
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineBaseChangeChartSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineOverBaseChangeAlgebraIso
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageChartProjectionComp
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageChartProjectionRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageChartProjectionRepresentableComp
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingIdealPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPushforwardAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleChartCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardBaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ThickeningSharpChartLiftRefine
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineTripleOverlap
public import StacksFrontier.CategoryTheory.Limits.IsPullbackOfEq

/-!
# The chart map of an affine base change is a base change of rings

Let `g : Y ⟶ X` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf site
`B`, `Z` an algebraic space affine over `X` and `Z' = Y ×_X Z` its base change.  For a chart
diagram `U ⟶ V` over `g` (an étale chart `U` of `Y`, an étale chart `V` of `X` and a morphism of
schemes over `g`), the comparison `AlgebraicGeometry.Space.pushforwardSquareMap`
`f_* 𝒪_Z ⟶ g_* (f'_* 𝒪_{Z'})` read at `V` and then at the chart `U` above `Y ×_X V` gives the
*chart map* `(f_* 𝒪_Z)(V) ⟶ (f'_* 𝒪_{Z'})(U)`.  This file proves that, when `U` and `V` are
affine, its `𝒪_Y(U)`-linear extension

`𝒪_Y(U) ⊗_{𝒪_X(V)} (f_* 𝒪_Z)(V) ⟶ (f'_* 𝒪_{Z'})(U)`

is bijective.

## Main definitions

* `AlgebraicGeometry.Space.affineOverBaseChangeChartRingHom` and
  `AlgebraicGeometry.Space.affineOverBaseChangeChartLinear`: the chart map of the affine base
  change as a ring homomorphism and as an `𝒪_X(V)`-linear map.

## Main results

* `AlgebraicGeometry.Space.bijective_liftBaseChange_affineOverBaseChange_chart`: the
  `𝒪_Y(U)`-linear extension of the chart map is bijective over an affine chart diagram, for any
  linear map whose values are the chart map; and
  `AlgebraicGeometry.Space.bijective_liftBaseChange_affineOverBaseChangeChartLinear` for the
  chart map itself.
* `AlgebraicGeometry.Space.isPushout_affineOverBaseChangeChartRingHom`: the same as a pushout
  square of rings.
* `AlgebraicGeometry.Space.affineOverBaseChangeChartRingHom_apply`: the chart ring homomorphism
  is the comparison `AlgebraicGeometry.Space.pushforwardSquareMap` read at the chart.

## Implementation notes

The chart computation uses only the `pushforwardCommRingFunctor` spelling of the direct images:
it is definitionally equal to `pushforwardAlgebra`, but the kernel does not check, in reasonable
time, a morphism applied to a section whose source is written in the two spellings at once.

## References

* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

/-! ### The affine base change at an affine chart diagram -/

section AffineBaseChange

/-- The chart map of the affine base change, read through the sections isomorphisms, is pullback
of regular functions along the scheme map of the chart square. -/
private theorem pushforwardAlgebraSectionsIso_squareChartMap_aux (g : Y ⟶ X)
    (Z : AffineOver B S hS X) (d : ChartDiagram B S hS Y.1 X.1 g.hom)
    (s : (pushforwardAlgebra B S hS Z.obj).right.obj.obj (op d.V)) :
    (pushforwardAlgebraSectionsIso B S hS (affineOverBaseChange B S hS g Z).obj
        (relativelyRepresentable_hom_of_isAffineHom B S hS (affineOverBaseChange B S hS g
            Z).obj.hom (affineOverBaseChange B S hS g Z).property) d.U).hom.hom
        (squareChartMap B S hS g Z.obj (affineOverBaseChange B S hS g Z).obj
        (affineOverBaseChangeProjection B S hS g Z) (affineOverBaseChange_isPullback B S hS g Z).w
        d s) =
      ((BigFppfOver.toScheme B S hS).map (squareChartSchemeMap B S hS g Z.obj (affineOverBaseChange
          B S hS g Z).obj (affineOverBaseChangeProjection B S hS g Z)
          (affineOverBaseChange_isPullback B S hS g Z).w
              (relativelyRepresentable_hom_of_isAffineHom B S hS Z.obj.hom Z.property)
              (relativelyRepresentable_hom_of_isAffineHom B S hS (affineOverBaseChange B S hS g
              Z).obj.hom (affineOverBaseChange B S hS g Z).property)
          d)).appTop.hom ((pushforwardAlgebraSectionsIso B S hS Z.obj
          (relativelyRepresentable_hom_of_isAffineHom B S hS Z.obj.hom Z.property) d.V).hom.hom s)
              :=
  (directImageChartProjection_chartBaseChangeArrow_apply B S hS (affineOverBaseChange B S hS g
      Z).obj (relativelyRepresentable_hom_of_isAffineHom B S hS (affineOverBaseChange B S hS g
          Z).obj.hom (affineOverBaseChange B S hS g Z).property) d.U
      _).symm.trans
    ((directImageChartProjection_squareChartMap B S hS g Z.obj (affineOverBaseChange B S hS g
        Z).obj (affineOverBaseChangeProjection B S hS g Z) (affineOverBaseChange_isPullback B S hS
        g Z).w (relativelyRepresentable_hom_of_isAffineHom B S hS Z.obj.hom Z.property)
            (relativelyRepresentable_hom_of_isAffineHom B S hS (affineOverBaseChange B S hS g
            Z).obj.hom (affineOverBaseChange B S hS g Z).property) d s).trans
      (congrArg _ (directImageChartProjection_chartBaseChangeArrow_apply B S hS Z.obj
          (relativelyRepresentable_hom_of_isAffineHom B S hS Z.obj.hom Z.property) d.V s)))

/-- The square of global functions of the chart square of the affine base change is a pushout. -/
private theorem isPushout_appTop_squareChartSchemeMap_aux (g : Y ⟶ X) (Z : AffineOver B S hS X)
    (d : ChartDiagram B S hS Y.1 X.1 g.hom)
    (haU : IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj d.U))
    (haV : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj d.V)) :
    IsPushout
      ((BigFppfOver.toScheme B S hS).map
        ((relativelyRepresentable_hom_of_isAffineHom B S hS Z.obj.hom Z.property).snd
          d.V.1.hom)).appTop
      ((BigFppfOver.toScheme B S hS).map d.g).appTop
      ((BigFppfOver.toScheme B S hS).map (squareChartSchemeMap B S hS g Z.obj
        (affineOverBaseChange B S hS g Z).obj (affineOverBaseChangeProjection B S hS g Z)
        (affineOverBaseChange_isPullback B S hS g Z).w
        (relativelyRepresentable_hom_of_isAffineHom B S hS Z.obj.hom Z.property)
        (relativelyRepresentable_hom_of_isAffineHom B S hS
          (affineOverBaseChange B S hS g Z).obj.hom (affineOverBaseChange B S hS g Z).property)
        d)).appTop
      ((BigFppfOver.toScheme B S hS).map
        ((relativelyRepresentable_hom_of_isAffineHom B S hS
          (affineOverBaseChange B S hS g Z).obj.hom (affineOverBaseChange B S hS g Z).property).snd
          d.U.1.hom)).appTop := by
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj ((relativelyRepresentable_hom_of_isAffineHom
      B S hS Z.obj.hom Z.property).pullback d.V.1.hom)) :=
    isAffine_smallBaseChange_obj B S hS Z.obj.hom (relativelyRepresentable_hom_of_isAffineHom B S
        hS Z.obj.hom Z.property) Z.property d.V haV
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj d.U.1.left) := haU
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj d.V.1.left) := haV
  have hpo := isPushout_appTop_of_isPullback
    ((isPullback_squareChartSchemeMap B S hS g Z.obj (affineOverBaseChange B S hS g Z).obj
        (affineOverBaseChangeProjection B S hS g Z) (affineOverBaseChange_isPullback B S hS g Z).w
        (relativelyRepresentable_hom_of_isAffineHom B S hS Z.obj.hom Z.property)
        (relativelyRepresentable_hom_of_isAffineHom B S hS (affineOverBaseChange B S hS g Z).obj.hom
      (affineOverBaseChange B S hS g Z).property) d
      (affineOverBaseChange_isPullback B S hS g Z)).map (BigFppfOver.toScheme B S hS))
  exact hpo

/-- The chart map of the base change of an algebraic space affine over `X`, extended to a base
change, is bijective at every affine chart diagram.  Let `g : Y ⟶ X`, let `Z` be an algebraic
space affine over `X` with base change `Z' = Y ×_X Z`, and let `d` be a chart diagram `U ⟶ V`
over `g` between affine charts.  For any `𝒪_X(V)`-linear map
`τ : (f_* 𝒪_Z)(V) ⟶ (f'_* 𝒪_{Z'})(U)` which is the chart map
`AlgebraicGeometry.Space.squareChartMap` of the base-change square (the comparison
`AlgebraicGeometry.Space.pushforwardSquareMap` at `V`, read at the chart `U` above `Y ×_X V`),
the `𝒪_Y(U)`-linear extension

`𝒪_Y(U) ⊗_{𝒪_X(V)} (f_* 𝒪_Z)(V) ⟶ (f'_* 𝒪_{Z'})(U)`

is bijective. -/
theorem bijective_liftBaseChange_affineOverBaseChange_chart (g : Y ⟶ X)
    (Z : AffineOver B S hS X) (d : ChartDiagram B S hS Y.1 X.1 g.hom)
    (haU : IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj d.U))
    (haV : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj d.V))
    (τ : letI := chartDiagramSectionModule B S hS g d (pushforwardAlgebra B S hS
        (affineOverBaseChange B S hS g Z).obj).underlyingModule
      (pushforwardAlgebra B S hS Z.obj).underlyingModule.val.obj (op d.V) →ₗ[chartRing B S hS X.1
          X.2 d.V]
        (pushforwardAlgebra B S hS (affineOverBaseChange B S hS g Z).obj).underlyingModule.val.obj
            (op d.U))
    (hτ : ∀ s, τ s = squareChartMap B S hS g Z.obj (affineOverBaseChange B S hS g Z).obj
        (affineOverBaseChangeProjection B S hS g Z) (affineOverBaseChange_isPullback B S hS g Z).w
        d s) :
    letI := chartDiagramAlgebra B S hS g d
    letI := chartDiagramSectionModule B S hS g d (pushforwardAlgebra B S hS (affineOverBaseChange B
        S hS g Z).obj).underlyingModule
    haveI := chartDiagramSection_isScalarTower B S hS g d (pushforwardAlgebra B S hS
        (affineOverBaseChange B S hS g Z).obj).underlyingModule
    Function.Bijective (τ.liftBaseChange (chartRing B S hS Y.1 Y.2 d.U)) := by
  have hpo := isPushout_appTop_squareChartSchemeMap_aux B S hS g Z d haU haV
  have key := fun s ↦ (congrArg _ (hτ s)).trans
    (pushforwardAlgebraSectionsIso_squareChartMap_aux B S hS g Z d s)
  have hV := fSharp_app_comp_pushforwardAlgebraSectionsIso B S hS Z.obj
      (relativelyRepresentable_hom_of_isAffineHom B S hS Z.obj.hom Z.property) d.V
  have hU := fSharp_app_comp_pushforwardAlgebraSectionsIso B S hS (affineOverBaseChange B S hS g
      Z).obj (relativelyRepresentable_hom_of_isAffineHom B S hS (affineOverBaseChange B S hS g
          Z).obj.hom (affineOverBaseChange B S hS g Z).property) d.U
  refine LinearMap.bijective_liftBaseChange_of_isPushout_of_ringEquiv
    (R := chartRing B S hS X.1 X.2 d.V) (S := chartRing B S hS Y.1 Y.2 d.U)
    (M := (pushforwardAlgebra B S hS Z.obj).right.obj.obj (op d.V)) (N := (pushforwardAlgebra B S
        hS (affineOverBaseChange B S hS g Z).obj).right.obj.obj (op d.U))
    (instRS := chartDiagramAlgebra B S hS g d)
    (instM := (inferInstance : Module (chartRing B S hS X.1 X.2 d.V)
      ((pushforwardAlgebra B S hS Z.obj).underlyingModule.val.obj (op d.V))))
    (instN := (inferInstance : Module (chartRing B S hS Y.1 Y.2 d.U)
      ((pushforwardAlgebra B S hS (affineOverBaseChange B S hS g Z).obj).underlyingModule.val.obj
          (op d.U))))
    (instRN := chartDiagramSectionModule B S hS g d (pushforwardAlgebra B S hS
        (affineOverBaseChange B S hS g Z).obj).underlyingModule)
    (instT := chartDiagramSection_isScalarTower B S hS g d (pushforwardAlgebra B S hS
        (affineOverBaseChange B S hS g Z).obj).underlyingModule)
    hpo (RingEquiv.refl _) (RingEquiv.refl _) (pushforwardAlgebraSectionsIso B S hS Z.obj
        (relativelyRepresentable_hom_of_isAffineHom B S hS Z.obj.hom Z.property)
            d.V).commRingCatIsoToRingEquiv
    (pushforwardAlgebraSectionsIso B S hS (affineOverBaseChange B S hS g Z).obj
        (relativelyRepresentable_hom_of_isAffineHom B S hS (affineOverBaseChange B S hS g
            Z).obj.hom (affineOverBaseChange B S hS g Z).property)
        d.U).commRingCatIsoToRingEquiv ((pushforwardAlgebra B S hS Z.obj).algebraMap (op d.V))
        ((pushforwardAlgebra B S hS (affineOverBaseChange B S hS g Z).obj).algebraMap (op d.U))
    (((pushforwardAlgebraSectionsIso B S hS (affineOverBaseChange B S hS g Z).obj
        (relativelyRepresentable_hom_of_isAffineHom B S hS (affineOverBaseChange B S hS g
            Z).obj.hom (affineOverBaseChange B S hS g Z).property)
        d.U).commRingCatIsoToRingEquiv.symm.toRingHom.comp
      ((BigFppfOver.toScheme B S hS).map (squareChartSchemeMap B S hS g Z.obj (affineOverBaseChange
          B S hS g Z).obj (affineOverBaseChangeProjection B S hS g Z)
          (affineOverBaseChange_isPullback B S hS g Z).w
              (relativelyRepresentable_hom_of_isAffineHom B S hS Z.obj.hom Z.property)
              (relativelyRepresentable_hom_of_isAffineHom B S hS (affineOverBaseChange B S hS g
              Z).obj.hom (affineOverBaseChange B S hS g Z).property)
          d)).appTop.hom).comp ((pushforwardAlgebraSectionsIso B S hS Z.obj
          (relativelyRepresentable_hom_of_isAffineHom B S hS Z.obj.hom Z.property)
              d.V).commRingCatIsoToRingEquiv.toRingHom))
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun r ↦ ?_) (fun r ↦ rfl) (fun m ↦ ?_)
    (fun x ↦ ?_) τ (fun m ↦ ?_)
  · exact (ConcreteCategory.congr_hom hV r).symm
  · exact (RingEquiv.apply_symm_apply _ _).symm
  · exact (ConcreteCategory.congr_hom hU x).symm
  · refine (pushforwardAlgebraSectionsIso B S hS (affineOverBaseChange B S hS g Z).obj
      (relativelyRepresentable_hom_of_isAffineHom B S hS (affineOverBaseChange B S hS g Z).obj.hom
          (affineOverBaseChange B S hS g Z).property)
      d.U).commRingCatIsoToRingEquiv.injective ?_
    exact (key m).trans (RingEquiv.apply_symm_apply _ _).symm

/-- After the identifications `AlgebraicGeometry.Space.pushforwardAlgebraSectionsIso`, the chart
map of the affine base change is pullback of regular functions along `Z' ×_Y U ⟶ Z ×_X V`. -/
theorem pushforwardAlgebraSectionsIso_squareChartMap_affineOverBaseChange (g : Y ⟶ X)
    (Z : AffineOver B S hS X) (d : ChartDiagram B S hS Y.1 X.1 g.hom)
    (s : (pushforwardAlgebra B S hS Z.obj).right.obj.obj (op d.V)) :
    (pushforwardAlgebraSectionsIso B S hS (affineOverBaseChange B S hS g Z).obj
        (relativelyRepresentable_hom_of_isAffineHom B S hS (affineOverBaseChange B S hS g
            Z).obj.hom (affineOverBaseChange B S hS g Z).property) d.U).hom.hom
        (squareChartMap B S hS g Z.obj (affineOverBaseChange B S hS g Z).obj
        (affineOverBaseChangeProjection B S hS g Z) (affineOverBaseChange_isPullback B S hS g Z).w
        d s) =
      ((BigFppfOver.toScheme B S hS).map (squareChartSchemeMap B S hS g Z.obj (affineOverBaseChange
          B S hS g Z).obj (affineOverBaseChangeProjection B S hS g Z)
          (affineOverBaseChange_isPullback B S hS g Z).w
              (relativelyRepresentable_hom_of_isAffineHom B S hS Z.obj.hom Z.property)
              (relativelyRepresentable_hom_of_isAffineHom B S hS (affineOverBaseChange B S hS g
              Z).obj.hom (affineOverBaseChange B S hS g Z).property)
          d)).appTop.hom ((pushforwardAlgebraSectionsIso B S hS Z.obj
          (relativelyRepresentable_hom_of_isAffineHom B S hS Z.obj.hom Z.property) d.V).hom.hom s)
              :=
  pushforwardAlgebraSectionsIso_squareChartMap_aux B S hS g Z d s

/-- The chart map of the affine base change as a ring homomorphism: after the identifications
`AlgebraicGeometry.Space.pushforwardAlgebraSectionsIso`, pullback of regular functions along
`Z' ×_Y U ⟶ Z ×_X V`. -/
def affineOverBaseChangeChartRingHom (g : Y ⟶ X) (Z : AffineOver B S hS X)
    (d : ChartDiagram B S hS Y.1 X.1 g.hom) :
    (pushforwardAlgebra B S hS Z.obj).right.obj.obj (op d.V) →+* (pushforwardAlgebra B S hS
        (affineOverBaseChange B S hS g Z).obj).right.obj.obj (op d.U) :=
  ((pushforwardAlgebraSectionsIso B S hS (affineOverBaseChange B S hS g Z).obj
      (relativelyRepresentable_hom_of_isAffineHom B S hS (affineOverBaseChange B S hS g Z).obj.hom
          (affineOverBaseChange B S hS g Z).property)
      d.U).commRingCatIsoToRingEquiv.symm.toRingHom.comp ((BigFppfOver.toScheme B S hS).map
      (squareChartSchemeMap B S hS g Z.obj (affineOverBaseChange B S hS g Z).obj
      (affineOverBaseChangeProjection B S hS g Z) (affineOverBaseChange_isPullback B S hS g Z).w
      (relativelyRepresentable_hom_of_isAffineHom B S hS Z.obj.hom Z.property)
          (relativelyRepresentable_hom_of_isAffineHom B S hS (affineOverBaseChange B S hS g
          Z).obj.hom (affineOverBaseChange B S hS g Z).property) d)).appTop.hom).comp
    (pushforwardAlgebraSectionsIso B S hS Z.obj (relativelyRepresentable_hom_of_isAffineHom B S hS
        Z.obj.hom Z.property)
        d.V).commRingCatIsoToRingEquiv.toRingHom

/-- The chart map of the affine base change is the ring homomorphism
`AlgebraicGeometry.Space.affineOverBaseChangeChartRingHom`. -/
theorem squareChartMap_affineOverBaseChange (g : Y ⟶ X) (Z : AffineOver B S hS X)
    (d : ChartDiagram B S hS Y.1 X.1 g.hom) (s : (pushforwardAlgebra B S hS Z.obj).right.obj.obj
        (op d.V)) :
    squareChartMap B S hS g Z.obj (affineOverBaseChange B S hS g Z).obj
        (affineOverBaseChangeProjection B S hS g Z) (affineOverBaseChange_isPullback B S hS g Z).w
        d s = affineOverBaseChangeChartRingHom B S hS g Z d s := by
  refine (pushforwardAlgebraSectionsIso B S hS (affineOverBaseChange B S hS g Z).obj
      (relativelyRepresentable_hom_of_isAffineHom B S hS (affineOverBaseChange B S hS g Z).obj.hom
          (affineOverBaseChange B S hS g Z).property)
      d.U).commRingCatIsoToRingEquiv.injective ?_
  exact (pushforwardAlgebraSectionsIso_squareChartMap_affineOverBaseChange B S hS g Z d s).trans
    (RingEquiv.apply_symm_apply _ _).symm

/-- The chart map of the affine base change carries the structure map of `f_* 𝒪_Z` to the
structure map of `f'_* 𝒪_{Z'}` after pullback along the chart diagram. -/
theorem affineOverBaseChangeChartRingHom_algebraMap (g : Y ⟶ X) (Z : AffineOver B S hS X)
    (d : ChartDiagram B S hS Y.1 X.1 g.hom) (r : chartRing B S hS X.1 X.2 d.V) :
    affineOverBaseChangeChartRingHom B S hS g Z d ((pushforwardAlgebra B S hS Z.obj).algebraMap (op
        d.V) r) =
      (pushforwardAlgebra B S hS (affineOverBaseChange B S hS g Z).obj).algebraMap (op d.U)
          (chartDiagramRestrict B S hS g d r) := by
  refine (pushforwardAlgebraSectionsIso B S hS (affineOverBaseChange B S hS g Z).obj
      (relativelyRepresentable_hom_of_isAffineHom B S hS (affineOverBaseChange B S hS g Z).obj.hom
          (affineOverBaseChange B S hS g Z).property)
      d.U).commRingCatIsoToRingEquiv.injective ?_
  refine (RingEquiv.apply_symm_apply _ _).trans ?_
  have hV := ConcreteCategory.congr_hom
    (fSharp_app_comp_pushforwardAlgebraSectionsIso B S hS Z.obj
        (relativelyRepresentable_hom_of_isAffineHom B S hS Z.obj.hom Z.property) d.V) r
  have hU := ConcreteCategory.congr_hom
    (fSharp_app_comp_pushforwardAlgebraSectionsIso B S hS (affineOverBaseChange B S hS g Z).obj
        (relativelyRepresentable_hom_of_isAffineHom B S hS (affineOverBaseChange B S hS g
            Z).obj.hom (affineOverBaseChange B S hS g Z).property) d.U)
    (chartDiagramRestrict B S hS g d r)
  have hsq := congrArg (fun k ↦ ((BigFppfOver.toScheme B S hS).map k).appTop.hom r)
    (squareChartSchemeMap_snd B S hS g Z.obj (affineOverBaseChange B S hS g Z).obj
        (affineOverBaseChangeProjection B S hS g Z) (affineOverBaseChange_isPullback B S hS g Z).w
        (relativelyRepresentable_hom_of_isAffineHom B S hS Z.obj.hom Z.property)
            (relativelyRepresentable_hom_of_isAffineHom B S hS (affineOverBaseChange B S hS g
            Z).obj.hom (affineOverBaseChange B S hS g Z).property) d)
  simp only [Functor.map_comp, Scheme.Hom.comp_appTop, CommRingCat.hom_comp,
    RingHom.coe_comp] at hsq
  exact (congrArg _ hV).trans (hsq.trans hU.symm)

/-- The chart map of the affine base change as an `𝒪_X(V)`-linear map, the sections of
`f'_* 𝒪_{Z'}` over `U` being an `𝒪_X(V)`-module by restriction of scalars along the chart
diagram. -/
def affineOverBaseChangeChartLinear (g : Y ⟶ X) (Z : AffineOver B S hS X)
    (d : ChartDiagram B S hS Y.1 X.1 g.hom) :
    letI := chartDiagramSectionModule B S hS g d (pushforwardAlgebra B S hS (affineOverBaseChange B
        S hS g Z).obj).underlyingModule
    (pushforwardAlgebra B S hS Z.obj).underlyingModule.val.obj (op d.V) →ₗ[chartRing B S hS X.1 X.2
        d.V]
      (pushforwardAlgebra B S hS (affineOverBaseChange B S hS g Z).obj).underlyingModule.val.obj
          (op d.U) := by
  letI := chartDiagramSectionModule B S hS g d (pushforwardAlgebra B S hS (affineOverBaseChange B S
      hS g Z).obj).underlyingModule
  exact
  { toFun := squareChartMap B S hS g Z.obj (affineOverBaseChange B S hS g Z).obj
      (affineOverBaseChangeProjection B S hS g Z) (affineOverBaseChange_isPullback B S hS g Z).w d
    map_add' := fun x y ↦ by
      have e : ∀ z : (pushforwardAlgebra B S hS Z.obj).right.obj.obj (op d.V),
          squareChartMap B S hS g Z.obj (affineOverBaseChange B S hS g Z).obj
              (affineOverBaseChangeProjection B S hS g Z) (affineOverBaseChange_isPullback B S hS g
              Z).w d z =
            affineOverBaseChangeChartRingHom B S hS g Z d z :=
        squareChartMap_affineOverBaseChange B S hS g Z d
      exact (e (x + y)).trans ((map_add _ x y).trans (congrArg₂ (· + ·) (e x).symm (e y).symm))
    map_smul' := fun r x ↦ by
      have e : ∀ z : (pushforwardAlgebra B S hS Z.obj).right.obj.obj (op d.V),
          squareChartMap B S hS g Z.obj (affineOverBaseChange B S hS g Z).obj
              (affineOverBaseChangeProjection B S hS g Z) (affineOverBaseChange_isPullback B S hS g
              Z).w d z =
            affineOverBaseChangeChartRingHom B S hS g Z d z :=
        squareChartMap_affineOverBaseChange B S hS g Z d
      have hx : (r • x : (pushforwardAlgebra B S hS Z.obj).underlyingModule.val.obj (op d.V)) =
          ((pushforwardAlgebra B S hS Z.obj).algebraMap (op d.V) r * (show (pushforwardAlgebra B S
              hS Z.obj).right.obj.obj (op d.V) from x) :
            (pushforwardAlgebra B S hS Z.obj).right.obj.obj (op d.V)) := rfl
      have hy : ∀ y : (pushforwardAlgebra B S hS (affineOverBaseChange B S hS g
          Z).obj).underlyingModule.val.obj (op d.U), (r • y) =
          ((pushforwardAlgebra B S hS (affineOverBaseChange B S hS g Z).obj).algebraMap (op d.U)
              (chartDiagramRestrict B S hS g d r) *
            (show (pushforwardAlgebra B S hS (affineOverBaseChange B S hS g Z).obj).right.obj.obj
                (op d.U) from y) : (pushforwardAlgebra B S hS (affineOverBaseChange B S hS g
                Z).obj).right.obj.obj (op d.U)) := fun _ ↦ rfl
      refine (congrArg _ hx).trans ((e _).trans ?_)
      refine Eq.trans ?_ (hy _).symm
      refine (map_mul _ _ _).trans ?_
      exact congrArg₂ (· * ·) (affineOverBaseChangeChartRingHom_algebraMap B S hS g Z d r)
        (e x).symm }

/-- The linear chart map `affineOverBaseChangeChartLinear` is the chart map `squareChartMap`. -/
theorem affineOverBaseChangeChartLinear_apply (g : Y ⟶ X) (Z : AffineOver B S hS X)
    (d : ChartDiagram B S hS Y.1 X.1 g.hom) (s : (pushforwardAlgebra B S hS
        Z.obj).underlyingModule.val.obj (op d.V)) :
    affineOverBaseChangeChartLinear B S hS g Z d s =
      squareChartMap B S hS g Z.obj (affineOverBaseChange B S hS g Z).obj
          (affineOverBaseChangeProjection B S hS g Z) (affineOverBaseChange_isPullback B S hS g
          Z).w d s :=
  rfl

/-- The `𝒪_Y(U)`-linear extension of the chart map
`AlgebraicGeometry.Space.affineOverBaseChangeChartLinear` is bijective at every affine chart
diagram. -/
theorem bijective_liftBaseChange_affineOverBaseChangeChartLinear (g : Y ⟶ X)
    (Z : AffineOver B S hS X) (d : ChartDiagram B S hS Y.1 X.1 g.hom)
    (haU : IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj d.U))
    (haV : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj d.V)) :
    letI := chartDiagramAlgebra B S hS g d
    letI := chartDiagramSectionModule B S hS g d (pushforwardAlgebra B S hS (affineOverBaseChange B
        S hS g Z).obj).underlyingModule
    haveI := chartDiagramSection_isScalarTower B S hS g d (pushforwardAlgebra B S hS
        (affineOverBaseChange B S hS g Z).obj).underlyingModule
    Function.Bijective ((affineOverBaseChangeChartLinear B S hS g Z d).liftBaseChange
      (chartRing B S hS Y.1 Y.2 d.U)) :=
  bijective_liftBaseChange_affineOverBaseChange_chart B S hS g Z d haU haV _ fun _ ↦ rfl

/-- `AlgebraicGeometry.Space.affineOverBaseChangeChartRingHom` is the base-change comparison
`AlgebraicGeometry.Space.pushforwardSquareMap` at `V`, read at the chart `U` above `Y ×_X V`. -/
theorem affineOverBaseChangeChartRingHom_apply (g : Y ⟶ X) (Z : AffineOver B S hS X)
    (d : ChartDiagram B S hS Y.1 X.1 g.hom) (s : (pushforwardAlgebra B S hS Z.obj).right.obj.obj
        (op d.V)) :
    affineOverBaseChangeChartRingHom B S hS g Z d s =
      (moduleChartProjection B S hS g d.V (indexOfChartDiagram B S hS g d)).app
        ((smallEtaleRingedTopos B S hS Y).forgetRing.obj (pushforwardAlgebra B S hS
            (affineOverBaseChange B S hS g Z).obj).right)
        ((pushforwardSquareMap B S hS g Z.obj (affineOverBaseChange B S hS g Z).obj
            (affineOverBaseChangeProjection B S hS g Z) (affineOverBaseChange_isPullback B S hS g
            Z).w).hom.app (op d.V) s) :=
  (squareChartMap_affineOverBaseChange B S hS g Z d s).symm.trans
    (congrArg ((moduleChartProjection B S hS g d.V (indexOfChartDiagram B S hS g d)).app
        ((smallEtaleRingedTopos B S hS Y).forgetRing.obj
          (pushforwardAlgebra B S hS (affineOverBaseChange B S hS g Z).obj).right))
      (sheafCompose_forget_map_hom_app_apply _ (op d.V) s))

/-- The ring square of the affine base change at an affine chart diagram is a pushout: the
structure maps of `f_* 𝒪_Z` over `V` and of `f'_* 𝒪_{Z'}` over `U`, the pullback of regular
functions `𝒪_X(V) ⟶ 𝒪_Y(U)` along the chart diagram and the chart map
`AlgebraicGeometry.Space.affineOverBaseChangeChartRingHom`. -/
theorem isPushout_affineOverBaseChangeChartRingHom (g : Y ⟶ X) (Z : AffineOver B S hS X)
    (d : ChartDiagram B S hS Y.1 X.1 g.hom)
    (haU : IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj d.U))
    (haV : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj d.V)) :
    IsPushout (CommRingCat.ofHom ((pushforwardAlgebra B S hS Z.obj).algebraMap (op d.V)))
      (CommRingCat.ofHom (chartDiagramRestrict B S hS g d))
      (CommRingCat.ofHom (affineOverBaseChangeChartRingHom B S hS g Z d))
      (CommRingCat.ofHom ((pushforwardAlgebra B S hS (affineOverBaseChange B S hS g
          Z).obj).algebraMap (op d.U))) := by
  have hpo := isPushout_appTop_squareChartSchemeMap_aux B S hS g Z d haU haV
  have hV := fSharp_app_comp_pushforwardAlgebraSectionsIso B S hS Z.obj
      (relativelyRepresentable_hom_of_isAffineHom B S hS Z.obj.hom Z.property) d.V
  have hU := fSharp_app_comp_pushforwardAlgebraSectionsIso B S hS (affineOverBaseChange B S hS g
      Z).obj (relativelyRepresentable_hom_of_isAffineHom B S hS (affineOverBaseChange B S hS g
      Z).obj.hom
      (affineOverBaseChange B S hS g Z).property) d.U
  refine hpo.of_iso' (RingEquiv.refl (chartRing B S hS X.1 X.2 d.V)).toCommRingCatIso
    (pushforwardAlgebraSectionsIso B S hS Z.obj (relativelyRepresentable_hom_of_isAffineHom B S hS
        Z.obj.hom Z.property) d.V).commRingCatIsoToRingEquiv.toCommRingCatIso
    (RingEquiv.refl (chartRing B S hS Y.1 Y.2 d.U)).toCommRingCatIso
    (pushforwardAlgebraSectionsIso B S hS (affineOverBaseChange B S hS g Z).obj
        (relativelyRepresentable_hom_of_isAffineHom B S hS (affineOverBaseChange B S hS g Z).obj.hom
      (affineOverBaseChange B S hS g Z).property) d.U).commRingCatIsoToRingEquiv.toCommRingCatIso
          ?_ ?_ ?_ ?_
  · ext r
    exact (ConcreteCategory.congr_hom hV r).symm
  · ext r
    rfl
  · ext s
    exact (pushforwardAlgebraSectionsIso_squareChartMap_affineOverBaseChange B S hS g Z d
        s).symm.trans
      (congrArg _ (squareChartMap_affineOverBaseChange B S hS g Z d s))
  · ext x
    exact (ConcreteCategory.congr_hom hU x).symm

end AffineBaseChange

end AlgebraicGeometry.Space

end
