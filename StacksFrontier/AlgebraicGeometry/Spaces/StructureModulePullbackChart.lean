module

public import StacksFrontier.AlgebraicGeometry.Spaces.AssociatedModulePullbackUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartCorrespondenceComp
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealSheafMapStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModulePullbackBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsChartPushforward

/-!
# The canonical map `f^*𝒪_Y ⟶ 𝒪_X` is the one of base change of étale scheme charts

Let `f : X ⟶ Y` be a *representable* morphism of algebraic spaces over a scheme `S` contained in
a big fppf site `B`.  Two maps `f^*𝒪_Y ⟶ 𝒪_X` of `𝒪_X`-modules are available.

* `AlgebraicGeometry.Space.structureModulePullbackMap` is the one for the inverse image of
  modules of [Stacks Project, Tag 03LU]: the transpose of pullback of regular functions along
  the vertical morphism of a diagram of étale scheme charts.
* `SheafOfModules.pullbackObjUnitToUnit` of
  `AlgebraicGeometry.Space.smallBaseChangeSharp` is the one for pullback of modules along the
  morphism of small étale ringed *sites* given by base change of étale scheme charts.

For a representable morphism the two inverse images are identified by
`AlgebraicGeometry.Space.modulePullbackChartIso`, and this file shows that identification carries
the first map to the second.

## Main results

* `AlgebraicGeometry.Space.chartRanIso_hom_app_moduleFMapSection`: **the homomorphism into the
  direct image of modules attached to a linear map of sections along `f`, read over an étale
  scheme chart `V` of `Y` through the chart comparison, is the component of that linear map at
  the base-changed chart `V ×_Y X`.**
* `AlgebraicGeometry.Space.modulePushforwardChartIso_structureModuleFMap_app` and
  `AlgebraicGeometry.Space.modulePushforwardChartIso_structureModuleFMap`: the transpose of
  `AlgebraicGeometry.Space.structureModulePullbackMap`, read through the identification of the
  two direct images, is `SheafOfModules.unitToPushforwardObjUnit` of
  `AlgebraicGeometry.Space.smallBaseChangeSharp` — on sections, and as morphisms.
* `AlgebraicGeometry.Space.homEquiv_structureModulePullbackMap`: the two transposes agree.
* `AlgebraicGeometry.Space.structureModulePullbackMap_eq_modulePullbackChartIso_comp`: **the
  identification of the two inverse images of modules carries the canonical map
  `f^*𝒪_Y ⟶ 𝒪_X` of [Stacks Project, Tag 03LU] to the one of base change of étale scheme
  charts.**

## Implementation notes

The chart comparison of `AlgebraicGeometry.Space.chartRanIso` is written out as
`AlgebraicGeometry.Space.smallEtaleDirectImageRanIso` followed by
`AlgebraicGeometry.Space.chartRanIso`, the spelling
`AlgebraicGeometry.Space.modulePushforwardChartIso_hom_app_apply` uses, rather than as
`AlgebraicGeometry.Space.chartComparison`: the two are equal by
`AlgebraicGeometry.Space.chartComparison_hom_app`, and keeping one spelling throughout avoids a
conversion.

The two adjunctions that `AlgebraicGeometry.Space.modulePullbackChartIso` is the
`CategoryTheory.Adjunction.leftAdjointUniq` of are passed to
`CategoryTheory.Adjunction.eq_leftAdjointUniq_hom_app_comp` as explicit terms, written out as
they are in that definition; left to unification they are metavariables whose categories are not
determined.  For the same reason every lemma below is applied with all of its arguments.

**Why no step below is a `rw` or a bare `exact` on the composite.**  The sections of
`𝒪_X` carry two definitionally equal but not reducibly equal spellings — `Modules B S hS X.obj _`
and `SheafOfModules (AlgebraicGeometry.Space.smallEtaleRingSheaf B S hS X.obj _)` — and the
statement here mixes them, `AlgebraicGeometry.Space.structureModulePullbackMap` being written in
the first and `SheafOfModules.pullbackObjUnitToUnit` of
`AlgebraicGeometry.Space.smallBaseChangeSharp` in the second.  A `rw` of
`SheafOfModules.comp_val` on such a goal reports the target as not type-correct at the
`implicit` transparency level, and asking `exact` to see the composite's action on sections as
the action of its second factor exhausts the heartbeats.  Both are avoided the same way: the
composite is split by `SheafOfModules.comp_val_app_apply` applied to both factors explicitly,
and the first factor's action on sections is supplied by
`AlgebraicGeometry.Space.modulePushforwardHomEquiv_symm_val_app_apply`, which is `rfl` because
it mentions one spelling only.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03G4](https://stacks.math.columbia.edu/tag/03G4)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

attribute [local instance] isContinuous_smallBaseChange

/-! ### The chart correspondence read through the chart comparison -/

/-- **The homomorphism into the direct image of modules attached to a linear map of sections
along `f`, read through the chart comparison, is the component of that linear map at the
base-changed chart.**  For a representable `f : X ⟶ Y` and an étale scheme chart `V` of `Y`, the
section of the direct image of `F` over `V` attached to a section `s` of `G` by a linear map `ξ`
of sections along `f`, read as a section over `V ×_Y X`, is the value at `s` of the component of
`ξ` at the chart diagram of the base-changed chart. -/
theorem chartRanIso_hom_app_moduleFMapSection (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    (G : Modules.{u, u} B S hS Y.1 Y.2) (ξ : ModuleFMap B S hS f F G)
    (V : SmallEtale B S hS Y.1) (s : G.val.obj (op V)) :
    ((smallEtaleDirectImageRanIso B S hS f ≪≫ chartRanIso B S hS f hf).hom.app
          (moduleSetSheaf B S hS X F)).hom.app (op V)
        (moduleFMapSection B S hS f F G ξ V s) =
      ξ.app (chartDiagramOfIndex B S hS f V (smallBaseChangeIndex B S hS f hf V)) s := by
  have h1 : ((smallEtaleDirectImageRanIso B S hS f).hom.app
          (moduleSetSheaf B S hS X F)).hom.app (op V)
        (moduleFMapSection B S hS f F G ξ V s) =
      fmapRanApp B S hS f (moduleSetSheaf B S hS X F) (moduleSetSheaf B S hS Y G)
        (ModuleFMap.toFMap B S hS ξ) V s :=
    congrArg (fun m ↦ m.hom.app (op V) s)
      (fmapDirectImageEquiv_comp_ranIso B S hS f (moduleSetSheaf B S hS X F)
        (moduleSetSheaf B S hS Y G) (ModuleFMap.toFMap B S hS ξ))
  refine Eq.trans (congrArg
    (fun σ ↦ chartRanApp B S hS f hf (moduleSetSheaf B S hS X F).obj V σ) h1) ?_
  exact fmapRanApp_π B S hS f (moduleSetSheaf B S hS X F) (moduleSetSheaf B S hS Y G)
    (ModuleFMap.toFMap B S hS ξ) V (smallBaseChangeIndex B S hS f hf V) s

/-! ### The structure comparison at the unit module -/

/-- The morphism of `𝒪_Y`-modules into the direct image attached to a linear map of sections
along `f` by the chartwise universal property of [Stacks Project, Tag 03LU] acts on sections by
`AlgebraicGeometry.Space.moduleFMapSection`. -/
theorem modulePushforwardHomEquiv_symm_val_app_apply (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) (G : Modules.{u, u} B S hS Y.1 Y.2)
    (ξ : ModuleFMap B S hS f F G) (V : (SmallEtale B S hS Y.1)ᵒᵖ) (s : G.val.obj V) :
    (((modulePushforwardHomEquiv B S hS f F G).symm ξ).val.app V).hom s =
      moduleFMapSection B S hS f F G ξ V.unop s :=
  rfl

/-- **The transpose of the canonical map `f^*𝒪_Y ⟶ 𝒪_X`, read through the identification of the
two direct images of modules, is the structure map of base change of étale scheme charts.**  On
sections over an étale scheme chart `V` of `Y` both are pullback of regular functions along the
cartesian projection `V ×_Y X ⟶ V`. -/
theorem modulePushforwardChartIso_structureModuleFMap_app (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (V : SmallEtale B S hS Y.1)
    (z : (structureRingSheaf B S hS Y).obj.obj (op V)) :
    (((modulePushforwardChartIso B S hS f hf).hom.app
            (SheafOfModules.unit (structureRingSheaf B S hS X))).val.app (op V)).hom
        (moduleFMapSection B S hS f (SheafOfModules.unit (structureRingSheaf B S hS X))
          (SheafOfModules.unit (structureRingSheaf B S hS Y))
          (structureModuleFMap B S hS f) V z) =
      ((SheafOfModules.unitToPushforwardObjUnit
        (smallBaseChangeSharp B S hS f hf)).val.app (op V)).hom z := by
  refine Eq.trans (modulePushforwardChartIso_hom_app_apply B S hS f hf
    (SheafOfModules.unit (structureRingSheaf B S hS X)) V
    (moduleFMapSection B S hS f (SheafOfModules.unit (structureRingSheaf B S hS X))
      (SheafOfModules.unit (structureRingSheaf B S hS Y))
      (structureModuleFMap B S hS f) V z)) ?_
  refine Eq.trans (chartRanIso_hom_app_moduleFMapSection B S hS f hf
    (SheafOfModules.unit (structureRingSheaf B S hS X))
    (SheafOfModules.unit (structureRingSheaf B S hS Y))
    (structureModuleFMap B S hS f) V z) ?_
  exact congrArg (fun m ↦ ((forget₂ CommRingCat.{u} RingCat.{u}).map
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map m).op)) z)
    (chartBaseChangeMap_smallBaseChangeIndex B S hS f hf V)

/-- **The transpose of the canonical map `f^*𝒪_Y ⟶ 𝒪_X`, read through the identification of the
two direct images of modules, is the structure map of base change of étale scheme charts.**  The
morphism-level form of
`AlgebraicGeometry.Space.modulePushforwardChartIso_structureModuleFMap_app`. -/
theorem modulePushforwardChartIso_structureModuleFMap (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) :
    (modulePushforwardHomEquiv B S hS f (SheafOfModules.unit (structureRingSheaf B S hS X))
            (SheafOfModules.unit (structureRingSheaf B S hS Y))).symm
          (structureModuleFMap B S hS f) ≫
        (modulePushforwardChartIso B S hS f hf).hom.app
          (SheafOfModules.unit (structureRingSheaf B S hS X)) =
      SheafOfModules.unitToPushforwardObjUnit (smallBaseChangeSharp B S hS f hf) := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext (fun W ↦ ModuleCat.hom_ext
    (LinearMap.ext (fun z ↦ ?_))))
  refine Eq.trans (SheafOfModules.comp_val_app_apply
    ((modulePushforwardHomEquiv B S hS f (SheafOfModules.unit (structureRingSheaf B S hS X))
        (SheafOfModules.unit (structureRingSheaf B S hS Y))).symm
      (structureModuleFMap B S hS f))
    ((modulePushforwardChartIso B S hS f hf).hom.app
      (SheafOfModules.unit (structureRingSheaf B S hS X))) W z) ?_
  refine Eq.trans (congrArg (fun y ↦ ((modulePushforwardChartIso B S hS f hf).hom.app
      (SheafOfModules.unit (structureRingSheaf B S hS X))).val.app W y)
    (modulePushforwardHomEquiv_symm_val_app_apply B S hS f
      (SheafOfModules.unit (structureRingSheaf B S hS X))
      (SheafOfModules.unit (structureRingSheaf B S hS Y))
      (structureModuleFMap B S hS f) W z)) ?_
  exact modulePushforwardChartIso_structureModuleFMap_app B S hS f hf W.unop z

/-- The transpose of `AlgebraicGeometry.Space.structureModulePullbackMap` along the adjunction of
[Stacks Project, Tag 03D7], read through the identification of the direct image of modules with
the direct image along base change of étale scheme charts, is
`SheafOfModules.unitToPushforwardObjUnit` of
`AlgebraicGeometry.Space.smallBaseChangeSharp` — which is in turn the transpose of
`SheafOfModules.pullbackObjUnitToUnit` of that structure map. -/
theorem homEquiv_structureModulePullbackMap (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) :
    ((modulePullbackAdjunction B S hS f).ofNatIsoRight
          (modulePushforwardChartIso B S hS f hf)).homEquiv
        (SheafOfModules.unit (structureRingSheaf B S hS Y))
        (SheafOfModules.unit (structureRingSheaf B S hS X))
        (structureModulePullbackMap B S hS f) =
      (smallBaseChangeModulePullbackAdjunction B S hS f hf).homEquiv
        (SheafOfModules.unit (structureRingSheaf B S hS Y))
        (SheafOfModules.unit (structureRingSheaf B S hS X))
        (SheafOfModules.pullbackObjUnitToUnit (smallBaseChangeSharp B S hS f hf)) := by
  refine Eq.trans (Adjunction.homEquiv_ofNatIsoRight_apply (modulePullbackAdjunction B S hS f)
    (modulePushforwardChartIso B S hS f hf) (structureModulePullbackMap B S hS f)) ?_
  refine Eq.trans (congrArg (fun m ↦ m ≫ (modulePushforwardChartIso B S hS f hf).hom.app
      (SheafOfModules.unit (structureRingSheaf B S hS X)))
    (structureModulePullbackMap_transpose B S hS f)) ?_
  exact Eq.trans (modulePushforwardChartIso_structureModuleFMap B S hS f hf)
    (SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
      (smallBaseChangeSharp B S hS f hf)).symm

/-! ### The first factor -/

/-- `AlgebraicGeometry.Space.modulePullbackChartIso` is the comparison of the two left adjoints,
written out. -/
theorem modulePullbackChartIso_eq (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) :
    modulePullbackChartIso B S hS f hf =
      Adjunction.leftAdjointUniq
        ((modulePullbackAdjunction B S hS f).ofNatIsoRight
          (modulePushforwardChartIso B S hS f hf))
        (smallBaseChangeModulePullbackAdjunction B S hS f hf) :=
  rfl

/-- **The identification of the two inverse images of modules carries the canonical map
`f^*𝒪_Y ⟶ 𝒪_X` to the one of base change of étale scheme charts.**  For a representable
morphism `f : X ⟶ Y` of algebraic spaces,
`AlgebraicGeometry.Space.modulePullbackChartIso` carries
`AlgebraicGeometry.Space.structureModulePullbackMap` — the canonical map out of the inverse
image of modules of [Stacks Project, Tag 03LU] — to `SheafOfModules.pullbackObjUnitToUnit` of
`AlgebraicGeometry.Space.smallBaseChangeSharp`, the canonical map out of the pullback along the
morphism of small étale ringed sites of base change of charts. -/
theorem structureModulePullbackMap_eq_modulePullbackChartIso_comp (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) :
    structureModulePullbackMap B S hS f =
      (modulePullbackChartIso B S hS f hf).hom.app
          (SheafOfModules.unit (structureRingSheaf B S hS Y)) ≫
        SheafOfModules.pullbackObjUnitToUnit (smallBaseChangeSharp B S hS f hf) := by
  rw [modulePullbackChartIso_eq B S hS f hf]
  exact Adjunction.eq_leftAdjointUniq_hom_app_comp
    ((modulePullbackAdjunction B S hS f).ofNatIsoRight (modulePushforwardChartIso B S hS f hf))
    (smallBaseChangeModulePullbackAdjunction B S hS f hf)
    (SheafOfModules.unit (structureRingSheaf B S hS Y))
    (structureModulePullbackMap B S hS f)
    (SheafOfModules.pullbackObjUnitToUnit (smallBaseChangeSharp B S hS f hf))
    (homEquiv_structureModulePullbackMap B S hS f hf)

end AlgebraicGeometry.Space

end
