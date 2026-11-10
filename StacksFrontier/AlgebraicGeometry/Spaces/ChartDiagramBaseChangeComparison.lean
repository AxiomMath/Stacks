module

public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import Mathlib.RingTheory.TensorProduct.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSpacePresentedSections
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingIdealPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.FreeModuleSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSpellingBridge

/-!
# The base-change comparison of an inverse image of modules over a chart diagram

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site `B`, let
`M` be an `𝒪_Y`-module on the small étale site and let `d` be a commutative diagram of étale
scheme charts over `f` — a chart `d.U` of `X` above a chart `d.V` of `Y`.  Pullback of regular
functions along the vertical morphism makes `𝒪_X(d.U)` an `𝒪_Y(d.V)`-algebra, and this file
builds the comparison map

`𝒪_X(d.U) ⊗_{𝒪_Y(d.V)} M(d.V) ⟶ (f^*M)(d.U)`

out of the chart component `AlgebraicGeometry.Space.modulePullbackChartSection` of the unit of
the Stacks 03D7 adjunction, and identifies it at a free module.

## Main definitions

* `AlgebraicGeometry.Space.modulePullbackChartFMap` is the chart component of the unit, read as
  an `AlgebraicGeometry.Space.ModuleFMap`: the chartwise transpose of the identity of `f^*M`.
* `AlgebraicGeometry.Space.modulePullbackChartSectionLinear` is that chart component as an
  `𝒪_Y(d.V)`-linear map into the sections of `f^*M` over `d.U`, restricted along the vertical
  pullback of regular functions.
* `AlgebraicGeometry.Space.modulePullbackChartBaseChange`: **the comparison map**, the
  `𝒪_X(d.U)`-linear extension of the chart component along `LinearMap.liftBaseChange`.

## Main results

* `AlgebraicGeometry.Space.modulePullbackChartSection_add` and
  `AlgebraicGeometry.Space.modulePullbackChartSection_smul`: the chart component is additive and
  semilinear over the vertical pullback of regular functions.
* `AlgebraicGeometry.Space.modulePullbackChartBaseChange_map`: **the comparison is natural in
  the module.**
* `AlgebraicGeometry.Space.isoValAppLinearEquiv`: the component of an isomorphism of modules at
  a chart, as a linear equivalence of sections.
* `AlgebraicGeometry.Space.modulePullbackChartBaseChange_free_tmul` and
  `AlgebraicGeometry.Space.bijective_modulePullbackChartBaseChange_free`: **over a diagram of
  affine charts the comparison at a free module is bijective**, being
  `TensorProduct.finsuppScalarRight` read through
  `AlgebraicGeometry.Space.freeSectionsIsoOfIsAffine` on both sides and the identification
  `SheafOfModules.mapFreeIso` of the inverse image of a free module with a free module.

## Implementation notes

The two algebraic properties of the chart component are those of
`AlgebraicGeometry.Space.ModuleFMap`, and they are available for
`AlgebraicGeometry.Space.modulePullbackChartSection` only through
`AlgebraicGeometry.Space.modulePullbackUnitSection_eq_modulePullbackChartSection`: the
`ModuleFMap` is built from the transported spelling of the unit, and the value
`AlgebraicGeometry.Space.modulePullbackUnitIso_inv_val_app_one` at the unit function — which is
what makes the comparison *bijective* at the unit module rather than merely defined — from the
untransported one.  That identification is why the comparison below has both.

The `𝒪_Y(d.V)`-module structure on the sections of `f^*M` over `d.U` is restriction of scalars
along the vertical pullback, `Module.compHom`; it is introduced as a `def` rather than an
instance because it depends on the chart diagram, exactly like
`AlgebraicGeometry.Space.chartDiagramAlgebra`.

Bijectivity at a free module is checked on the generators `a ⊗ 𝟙_i x` and is the unit case
spread over the index type: by naturality at the coproduct injection `SheafOfModules.ιFree i`
the value at `a ⊗ 𝟙_i x` is the image of the value at `a ⊗ x` of the unit module, and there the
chart component of the unit is semilinear with `1 ↦ 1`, so the comparison is multiplication by
`1`.  Affineness of both charts enters only through
`AlgebraicGeometry.Space.freeSectionsIsoOfIsAffine`, which is where a free module's sections are
the finitely supported families: over a non-affine chart they are strictly more, and the
statement is false.

Nothing here raises a compiler limit or disables a linter.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (M : Modules.{u, u} B S hS Y.1 Y.2)

/-! ### The chart component of the unit as a linear map of sections -/

/-- The chart component of the unit of the Stacks 03D7 adjunction, read as a linear map of
sections along `f`: the chartwise transpose of the identity of `f^*M`. -/
noncomputable def modulePullbackChartFMap :
    ModuleFMap B S hS f ((modulePullback B S hS f).obj M) M :=
  modulePullbackHomFMap B S hS f M ((modulePullback B S hS f).obj M) (𝟙 _)

/-- The values of that linear map of sections are the chart sections. -/
theorem modulePullbackChartFMap_app (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (s : M.val.obj (op d.V)) :
    (modulePullbackChartFMap B S hS f M).app d s =
      modulePullbackChartSection B S hS f M d s :=
  (modulePullbackHomFMap_app B S hS f M ((modulePullback B S hS f).obj M) (𝟙 _) d s).trans
    (modulePullbackUnitSection_eq_modulePullbackChartSection B S hS f M d s)

/-- **The chart component of the unit is additive.** -/
theorem modulePullbackChartSection_add (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (s t : M.val.obj (op d.V)) :
    modulePullbackChartSection B S hS f M d (s + t) =
      modulePullbackChartSection B S hS f M d s +
        modulePullbackChartSection B S hS f M d t := by
  rw [← modulePullbackChartFMap_app, ← modulePullbackChartFMap_app,
    ← modulePullbackChartFMap_app]
  exact (modulePullbackChartFMap B S hS f M).map_add d s t

/-- **The chart component of the unit is semilinear over the vertical pullback of regular
functions.** -/
theorem modulePullbackChartSection_smul (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (r : chartRing B S hS Y.1 Y.2 d.V) (s : M.val.obj (op d.V)) :
    modulePullbackChartSection B S hS f M d (r • s) =
      chartDiagramRestrict B S hS f d r • modulePullbackChartSection B S hS f M d s := by
  rw [← modulePullbackChartFMap_app, ← modulePullbackChartFMap_app]
  exact (modulePullbackChartFMap B S hS f M).map_smul d r s

/-! ### The base-change comparison -/

/-- The `𝒪_Y(d.V)`-module structure on the sections of `f^*M` over `d.U`, by restriction of
scalars along the vertical pullback of regular functions.  Not an instance: it depends on the
chart diagram. -/
@[instance_reducible]
noncomputable def modulePullbackChartSectionModule
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) :
    Module (chartRing B S hS Y.1 Y.2 d.V)
      (((modulePullback B S hS f).obj M).val.obj (op d.U)) :=
  Module.compHom _ (chartDiagramRestrict B S hS f d)

/-- The restricted action is the action of the pulled-back scalar. -/
theorem modulePullbackChartSectionModule_smul (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (r : chartRing B S hS Y.1 Y.2 d.V)
    (x : ((modulePullback B S hS f).obj M).val.obj (op d.U)) :
    letI := modulePullbackChartSectionModule B S hS f M d
    r • x = chartDiagramRestrict B S hS f d r • x := rfl

/-- The two scalar actions on the sections of `f^*M` over `d.U` are compatible. -/
theorem modulePullbackChart_isScalarTower (d : ChartDiagram B S hS X.1 Y.1 f.hom) :
    letI := chartDiagramAlgebra B S hS f d
    letI := modulePullbackChartSectionModule B S hS f M d
    IsScalarTower (chartRing B S hS Y.1 Y.2 d.V) (chartRing B S hS X.1 X.2 d.U)
      (((modulePullback B S hS f).obj M).val.obj (op d.U)) :=
  let _ := chartDiagramAlgebra B S hS f d
  let _ := modulePullbackChartSectionModule B S hS f M d
  IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)

/-- The chart component of the unit as an `𝒪_Y(d.V)`-linear map into the sections of `f^*M`
over `d.U`, restricted along the vertical pullback of regular functions. -/
noncomputable def modulePullbackChartSectionLinear (d : ChartDiagram B S hS X.1 Y.1 f.hom) :
    letI := modulePullbackChartSectionModule B S hS f M d
    M.val.obj (op d.V) →ₗ[chartRing B S hS Y.1 Y.2 d.V]
      ((modulePullback B S hS f).obj M).val.obj (op d.U) :=
  letI := modulePullbackChartSectionModule B S hS f M d
  { toFun := modulePullbackChartSection B S hS f M d
    map_add' := modulePullbackChartSection_add B S hS f M d
    map_smul' := modulePullbackChartSection_smul B S hS f M d }

/-- **The base-change comparison of an inverse image of modules over a diagram of étale scheme
charts**: the `𝒪_X(d.U)`-linear map from the base change of the sections of `M` over `d.V` to
the sections of `f^*M` over `d.U` extending the chart component of the unit of the Stacks 03D7
adjunction. -/
noncomputable def modulePullbackChartBaseChange (d : ChartDiagram B S hS X.1 Y.1 f.hom) :
    letI := chartDiagramAlgebra B S hS f d
    TensorProduct (chartRing B S hS Y.1 Y.2 d.V) (chartRing B S hS X.1 X.2 d.U)
        (M.val.obj (op d.V)) →ₗ[chartRing B S hS X.1 X.2 d.U]
      ((modulePullback B S hS f).obj M).val.obj (op d.U) :=
  letI := chartDiagramAlgebra B S hS f d
  letI := modulePullbackChartSectionModule B S hS f M d
  haveI := modulePullbackChart_isScalarTower B S hS f M d
  (modulePullbackChartSectionLinear B S hS f M d).liftBaseChange
    (chartRing B S hS X.1 X.2 d.U)

/-- The comparison carries `a ⊗ s` to `a` times the chart component of the unit at `s`. -/
theorem modulePullbackChartBaseChange_tmul (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (a : chartRing B S hS X.1 X.2 d.U) (s : M.val.obj (op d.V)) :
    letI := chartDiagramAlgebra B S hS f d
    modulePullbackChartBaseChange B S hS f M d
        (TensorProduct.tmul (chartRing B S hS Y.1 Y.2 d.V) a s) =
      a • modulePullbackChartSection B S hS f M d s := rfl

/-! ### Naturality of the comparison in the module -/

variable {M} {M' : Modules.{u, u} B S hS Y.1 Y.2}

/-- **The base-change comparison is natural in the module.** This is the naturality
`AlgebraicGeometry.Space.modulePullbackChartSection_map` of the chart component of the unit,
extended along the base change. -/
theorem modulePullbackChartBaseChange_map (a : M ⟶ M')
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) :
    letI := chartDiagramAlgebra B S hS f d
    ∀ z : TensorProduct (chartRing B S hS Y.1 Y.2 d.V) (chartRing B S hS X.1 X.2 d.U)
        (M.val.obj (op d.V)),
      ((modulePullback B S hS f).map a).val.app (op d.U)
          (modulePullbackChartBaseChange B S hS f M d z) =
        modulePullbackChartBaseChange B S hS f M' d
          (LinearMap.lTensor (chartRing B S hS X.1 X.2 d.U) (a.val.app (op d.V)).hom z) := by
  let := chartDiagramAlgebra B S hS f d
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul b s =>
    rw [LinearMap.lTensor_tmul, modulePullbackChartBaseChange_tmul,
      modulePullbackChartBaseChange_tmul,
      (((modulePullback B S hS f).map a).val.app (op d.U)).hom.map_smul]
    exact congrArg (fun y ↦ b • y) (modulePullbackChartSection_map B S hS f M a d s)
  | add z w hz hw => simp only [map_add, hz, hw]

/-! ### The comparison at a free module -/

variable (M)

/-- The component of an isomorphism of modules at a chart, as a linear equivalence of the
sections over that chart.  Bijectivity is
`SheafOfModules.bijective_iso_hom_val_app`, which holds over every object of any
site. -/
noncomputable def isoValAppLinearEquiv {Z : AlgebraicSpaces B S hS}
    {N N' : Modules.{u, u} B S hS Z.1 Z.2} (e : N ≅ N') (W : SmallEtale B S hS Z.1) :
    N.val.obj (op W) ≃ₗ[chartRing B S hS Z.1 Z.2 W] N'.val.obj (op W) :=
  LinearEquiv.ofBijective (e.hom.val.app (op W)).hom
    (SheafOfModules.bijective_iso_hom_val_app e (op W))

/-- The chart component of the unit at the unit module is the vertical pullback of the section
times the value of the identification `𝒪_X ≅ f^*𝒪_Y` of Stacks 03LU on the unit function. -/
theorem modulePullbackChartSection_unit (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (x : chartRing B S hS Y.1 Y.2 d.V) :
    modulePullbackChartSection B S hS f
        (unit ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS Y.1 Y.2).O))) d x =
      chartDiagramRestrict B S hS f d x •
        (modulePullbackUnitIso B S hS f).inv.val.app (op d.U)
          (1 : chartRing B S hS X.1 X.2 d.U) := by
  refine Eq.trans ?_ (congrArg (fun y ↦ chartDiagramRestrict B S hS f d x • y)
    (modulePullbackUnitIso_inv_val_app_one B S hS f d).symm)
  exact Eq.trans
    (congrArg (modulePullbackChartSection B S hS f
      (unit ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS Y.1 Y.2).O))) d) (mul_one x).symm)
    (modulePullbackChartSection_smul B S hS f
      (unit ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))) d x
      (1 : chartRing B S hS Y.1 Y.2 d.V))

/-- The identification of the inverse image of a free module with a free module, for the inverse
image of modules of Stacks 03LU: `SheafOfModules.mapFreeIso` for the identification
`𝒪_X ≅ f^*𝒪_Y` of the structure sheaves. -/
noncomputable def modulePullbackFreeIso (I : Type u) :
    (free (R := (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O)) I) ≅
      (modulePullback B S hS f).obj (SheafOfModules.free I) :=
  haveI := preservesColimitsOfSize_modulePullback B S hS f
  SheafOfModules.mapFreeIso (modulePullback B S hS f) I (modulePullbackUnitIso B S hS f).symm

/-- The identification carries the `i`-th tautological section of the free module to the
inverse image of the `i`-th coproduct injection applied to the unit function. -/
theorem modulePullbackFreeIso_hom_val_app_ιFree (I : Type u) (i : I)
    (W : ((smallEtaleRingedSite B S hS X.1 X.2).C)ᵒᵖ)
    (x : ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O)).obj.obj W) :
    (modulePullbackFreeIso B S hS f I).hom.val.app W
        ((ιFree (R := (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS X.1 X.2).O)) i).val.app W x) =
      ((modulePullback B S hS f).map (SheafOfModules.ιFree i)).val.app W
        ((modulePullbackUnitIso B S hS f).inv.val.app W x) :=
  haveI := preservesColimitsOfSize_modulePullback B S hS f
  congrArg (fun m : unit ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X.1 X.2).O)) ⟶
      (modulePullback B S hS f).obj (SheafOfModules.free I) ↦ m.val.app W x)
    (SheafOfModules.ιFree_mapFreeIso_hom (modulePullback B S hS f) I
      (modulePullbackUnitIso B S hS f).symm i)

/-- **The base-change comparison at a free module, on a tautological section.** The comparison
carries `a ⊗ 𝟙_i x` to the `i`-th tautological section of the free module on `X` at the product
of `a` with the vertical pullback of `x`, read through the identification of the inverse image of
the free module with the free module. -/
theorem modulePullbackChartBaseChange_ιFree (I : Type u)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) (i : I)
    (a : chartRing B S hS X.1 X.2 d.U) (x : chartRing B S hS Y.1 Y.2 d.V) :
    letI := chartDiagramAlgebra B S hS f d
    modulePullbackChartBaseChange B S hS f
        (free (R := (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS Y.1 Y.2).O)) I) d
        (TensorProduct.tmul (chartRing B S hS Y.1 Y.2 d.V) a
          ((ιFree (R := (Stacks.SheafOfModules.Tensor.ringSheaf
              (smallEtaleRingedSite B S hS Y.1 Y.2).O)) i).val.app (op d.V) x)) =
      (modulePullbackFreeIso B S hS f I).hom.val.app (op d.U)
        ((ιFree (R := (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS X.1 X.2).O)) i).val.app (op d.U)
          (a * chartDiagramRestrict B S hS f d x)) := by
  let := chartDiagramAlgebra B S hS f d
  rw [modulePullbackChartBaseChange_tmul,
    ← modulePullbackChartSection_map B S hS f
      (unit ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)))
      (ιFree (R := (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS Y.1 Y.2).O)) i) d x,
    modulePullbackChartSection_unit,
    (((modulePullback B S hS f).map
      (ιFree (R := (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS Y.1 Y.2).O)) i)).val.app
        (op d.U)).hom.map_smul]
  refine Eq.trans (congrArg (fun y ↦ a • chartDiagramRestrict B S hS f d x • y)
    (modulePullbackFreeIso_hom_val_app_ιFree B S hS f I i (op d.U)
      (1 : chartRing B S hS X.1 X.2 d.U)).symm) ?_
  refine (smul_smul a (chartDiagramRestrict B S hS f d x) _).trans ?_
  refine Eq.trans (((modulePullbackFreeIso B S hS f I).hom.val.app
    (op d.U)).hom.map_smul _ _).symm ?_
  refine congrArg
    (fun y ↦ (modulePullbackFreeIso B S hS f I).hom.val.app (op d.U) y) ?_
  exact Eq.trans
    (((ιFree (R := (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O)) i).val.app
      (op d.U)).hom.map_smul _ _).symm
    (congrArg
      (fun c ↦ (ιFree (R := (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS X.1 X.2).O)) i).val.app
        (op d.U) c)
      (mul_one (a * chartDiagramRestrict B S hS f d x)))

/-- Over an affine chart the sections of a free module are the finitely supported families, by a
linear equivalence carrying `single i x` to the `i`-th tautological section at `x`. -/
private theorem exists_linearEquiv_free_sections (Z : AlgebraicSpaces B S hS) (I : Type u)
    (W : SmallEtale B S hS Z.1)
    (hW : IsAffine ((SmallEtale.toOver B S hS Z.1 ⋙ BigFppfOver.toScheme B S hS).obj W)) :
    ∃ e : (I →₀ chartRing B S hS Z.1 Z.2 W) ≃ₗ[chartRing B S hS Z.1 Z.2 W]
        ((free (R := (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS Z.1 Z.2).O)) I).val.obj (op W)),
      ∀ (i : I) (x : chartRing B S hS Z.1 Z.2 W),
        e (Finsupp.single i x) =
          (ιFree (R := (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS Z.1 Z.2).O)) i).val.app (op W) x :=
  ⟨LinearEquiv.ofBijective
      (Stacks.Sites.freeSectionsMap (R := (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS Z.1 Z.2).O)) I (op W)).hom
      (bijective_freeSectionsMap_of_isAffine B S hS Z.1 Z.2 I W hW),
    fun i x ↦ Stacks.Sites.freeSectionsMap_single (R := (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS Z.1 Z.2).O)) I (op W) i x⟩

/-- **Over a diagram of affine étale scheme charts the base-change comparison at a free module
is bijective.**

The sections of a free module over an affine chart are the finitely supported families of
regular functions on the chart, by
`AlgebraicGeometry.Space.bijective_freeSectionsMap_of_isAffine` on each side; through those two
identifications and the identification of the inverse image of the free module with the free
module, the comparison is `TensorProduct.finsuppScalarRight`, which is bijective.  That it is
*that* map is checked on `a ⊗ 𝟙_i x`, which is
`AlgebraicGeometry.Space.modulePullbackChartBaseChange_ιFree`. -/
theorem bijective_modulePullbackChartBaseChange_free (I : Type u)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (hU : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj d.U))
    (hV : IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj d.V)) :
    letI := chartDiagramAlgebra B S hS f d
    Function.Bijective (modulePullbackChartBaseChange B S hS f
      (free (R := (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS Y.1 Y.2).O)) I) d) := by
  classical
  let := chartDiagramAlgebra B S hS f d
  obtain ⟨eV, heV⟩ := exists_linearEquiv_free_sections B S hS Y I d.V hV
  obtain ⟨eU, heU⟩ := exists_linearEquiv_free_sections B S hS X I d.U hU
  have hΨ : ∀ (b : chartRing B S hS X.1 X.2 d.U) (i : I) (x : chartRing B S hS Y.1 Y.2 d.V),
      TensorProduct.finsuppScalarRight (chartRing B S hS Y.1 Y.2 d.V)
          (chartRing B S hS X.1 X.2 d.U) (chartRing B S hS X.1 X.2 d.U) I
          (TensorProduct.tmul (chartRing B S hS Y.1 Y.2 d.V) b (Finsupp.single i x)) =
        Finsupp.single i (x • b) := fun b i x ↦ by
    rw [TensorProduct.finsuppScalarRight_apply_tmul,
      Finsupp.sum_single_index (by rw [zero_smul, Finsupp.single_zero])]
  have hτ : ∀ (b : chartRing B S hS X.1 X.2 d.U) (w : I →₀ chartRing B S hS Y.1 Y.2 d.V),
      LinearEquiv.lTensor (chartRing B S hS X.1 X.2 d.U) eV
          (TensorProduct.tmul (chartRing B S hS Y.1 Y.2 d.V) b w) =
        TensorProduct.tmul (chartRing B S hS Y.1 Y.2 d.V) b (eV w) := fun _ _ ↦ rfl
  have key : ∀ (b : chartRing B S hS X.1 X.2 d.U) (w : I →₀ chartRing B S hS Y.1 Y.2 d.V),
      modulePullbackChartBaseChange B S hS f
          (free (R := (Stacks.SheafOfModules.Tensor.ringSheaf
              (smallEtaleRingedSite B S hS Y.1 Y.2).O)) I) d
          (TensorProduct.tmul (chartRing B S hS Y.1 Y.2 d.V) b (eV w)) =
        (modulePullbackFreeIso B S hS f I).hom.val.app (op d.U)
          (eU (TensorProduct.finsuppScalarRight (chartRing B S hS Y.1 Y.2 d.V)
            (chartRing B S hS X.1 X.2 d.U) (chartRing B S hS X.1 X.2 d.U) I
            (TensorProduct.tmul (chartRing B S hS Y.1 Y.2 d.V) b w))) := by
    intro b w
    induction w using Finsupp.induction_linear with
    | zero => simp only [map_zero, TensorProduct.tmul_zero]
    | add w₁ w₂ h₁ h₂ => simp only [TensorProduct.tmul_add, map_add, h₁, h₂]
    | single i x =>
      rw [heV, modulePullbackChartBaseChange_ιFree, hΨ, heU, Algebra.smul_def,
        chartDiagramAlgebra_algebraMap, mul_comm b (chartDiagramRestrict B S hS f d x)]
  have key' : ∀ z : TensorProduct (chartRing B S hS Y.1 Y.2 d.V)
      (chartRing B S hS X.1 X.2 d.U) (I →₀ chartRing B S hS Y.1 Y.2 d.V),
      modulePullbackChartBaseChange B S hS f
          (free (R := (Stacks.SheafOfModules.Tensor.ringSheaf
              (smallEtaleRingedSite B S hS Y.1 Y.2).O)) I) d
          (LinearEquiv.lTensor (chartRing B S hS X.1 X.2 d.U) eV z) =
        (modulePullbackFreeIso B S hS f I).hom.val.app (op d.U)
          (eU (TensorProduct.finsuppScalarRight (chartRing B S hS Y.1 Y.2 d.V)
            (chartRing B S hS X.1 X.2 d.U) (chartRing B S hS X.1 X.2 d.U) I z)) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul b w =>
      rw [hτ]
      exact key b w
    | add z w hz hw => simp only [map_add, hz, hw]
  have hcomp : ⇑(modulePullbackChartBaseChange B S hS f
        (free (R := (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS Y.1 Y.2).O)) I) d) =
      fun y ↦ (modulePullbackFreeIso B S hS f I).hom.val.app (op d.U)
        (eU (TensorProduct.finsuppScalarRight (chartRing B S hS Y.1 Y.2 d.V)
          (chartRing B S hS X.1 X.2 d.U) (chartRing B S hS X.1 X.2 d.U) I
          ((LinearEquiv.lTensor (chartRing B S hS X.1 X.2 d.U) eV).symm y))) := by
    funext y
    have h := key' ((LinearEquiv.lTensor (chartRing B S hS X.1 X.2 d.U) eV).symm y)
    rwa [LinearEquiv.apply_symm_apply] at h
  rw [hcomp]
  exact ((SheafOfModules.bijective_iso_hom_val_app (modulePullbackFreeIso B S hS f I)
      (op d.U)).comp (eU.bijective.comp
        (TensorProduct.finsuppScalarRight (chartRing B S hS Y.1 Y.2 d.V)
          (chartRing B S hS X.1 X.2 d.U) (chartRing B S hS X.1 X.2 d.U) I).bijective)).comp
    (LinearEquiv.lTensor (chartRing B S hS X.1 X.2 d.U) eV).symm.bijective

end AlgebraicGeometry.Space

end
