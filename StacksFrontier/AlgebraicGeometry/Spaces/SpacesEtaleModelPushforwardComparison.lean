module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictionPullbackModuleSquare
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposModuleRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageChartProjectionComp
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageChartProjectionExt
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SmallEtaleDerivedPullbackPerfect
public import StacksFrontier.CategoryTheory.Adjunction.MateAlongEquivalences
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleModelEtaleModulesComparison

/-!
# Direct images on the spaces-étale models and on the small étale sites

Let `f : X ⟶ Y` be a morphism of algebraic spaces. This file proves the comparison of the
direct image of modules along the morphism of models of the ringed spaces-étale sites
(`AlgebraicGeometry.Space.spacesEtaleModelHom f`) with the direct image
`AlgebraicGeometry.Space.modulePushforward f` of `𝒪`-modules on the small étale sites, under the
equivalences `AlgebraicGeometry.Space.spacesEtaleModelModulesEquiv` of Stacks 03G1.

The equivalence of Stacks 03G1 is read directly as restriction along the comparison
`AlgebraicGeometry.Space.spacesEtaleModelChart` of the small étale site with the model of the
spaces-étale site, followed by the identification of the structure sheaves; the direct image on
the models is read as an inverse image of modules along restriction of sheaves of sets; and the
direct images of sheaves of sets agree by the base change square of the comparison. The two
direct images of modules are then isomorphic by
`Stacks.Sheaves.ToposPullback.restrictionPullbackModuleSquareIso`, whose one hypothesis is the
agreement of the structure maps; that is checked on the chart projections of the direct image.
Passing to left adjoints gives the comparison of the inverse images.

## Main definitions

* `AlgebraicGeometry.Space.spacesEtaleModelChart`: the comparison of Stacks 03G1 from the small
  étale site of `Z` to the model of its spaces-étale site.
* `AlgebraicGeometry.Space.spacesEtaleModelChartRingIso`: the restricted structure sheaf of the
  model is the structure sheaf.
* `AlgebraicGeometry.Space.spacesEtaleModelChartModules` and
  `AlgebraicGeometry.Space.spacesEtaleModelChartModulesIso`: restriction to the small étale site
  is the functor of `AlgebraicGeometry.Space.spacesEtaleModelModulesEquiv`.
* `AlgebraicGeometry.Space.spacesEtaleModelPushforwardIsoRestriction`: the direct image of
  modules along the morphism of models is restriction followed by restrictions of scalars.
* `AlgebraicGeometry.Space.spacesEtaleModelPushforwardRestrictionIso`: the direct image of
  modules along the morphism of models, read on the small étale site of `Y`, as an inverse image
  of modules along restriction of sheaves of sets.
* `AlgebraicGeometry.Space.spacesEtaleModelChartDirectImageIso`: the square of direct images of
  sheaves of sets.
* `AlgebraicGeometry.Space.spacesEtaleModelModulesPushforwardIso`: **the direct images agree**,
  `(model f)_* ⋙ e_Y ≅ e_X ⋙ f_*`.
* `AlgebraicGeometry.Space.spacesEtaleModelModulesPullbackIso`: **the inverse images agree**,
  `(model f)^* ⋙ e_X ≅ e_Y ⋙ f^*`, as the mate of the comparison of direct images.

## Main results

* `AlgebraicGeometry.Space.spacesEtaleModelChartSharp_compat`: the structure maps of the
  morphism of models and of the morphism of small étale ringed topoi (Stacks 03G8) agree; on an
  étale chart of `X` above `X ×_Y V` both pull a regular function back along the chart morphism
  (`AlgebraicGeometry.Space.spacesEtaleModelChartRingIso_hom_map_fSharp`).
* `AlgebraicGeometry.Space.isPerfect_smallEtaleDerivedModulePullback_of_hasLeftDerivedFunctor`:
  Stacks 08H6 on the small étale sites, transported from the models.

## References

* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.DenseSubsiteModules
open Stacks.Sheaves.ToposPullback

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section RestrictScalarsComp

variable {C : Type*} [Category C] {J : GrothendieckTopology C}
  {R₁ R₂ R₃ R₄ T : Sheaf J RingCat.{u}}

/-- Two composites of restrictions of scalars along maps of sheaves of rings with the same
composite are isomorphic, by the identity on sections. -/
def _root_.SheafOfModules.restrictScalarsCompCongrIso (α : R₂ ⟶ T) (β : R₁ ⟶ R₂)
    (γ : R₃ ⟶ T) (δ : R₁ ⟶ R₃) (h : β ≫ α = δ ≫ γ) :
    SheafOfModules.restrictScalars.{u} α ⋙ SheafOfModules.restrictScalars.{u} β ≅
      SheafOfModules.restrictScalars.{u} γ ⋙ SheafOfModules.restrictScalars.{u} δ :=
  NatIso.ofComponents (fun M => (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun U =>
      { hom := ModuleCat.ofHom
          (X := ↑(((SheafOfModules.restrictScalars.{u} β).obj
            ((SheafOfModules.restrictScalars.{u} α).obj M)).val.obj U))
          (Y := ↑(((SheafOfModules.restrictScalars.{u} δ).obj
            ((SheafOfModules.restrictScalars.{u} γ).obj M)).val.obj U))
          { toFun := fun x => x
            map_add' := fun _ _ => rfl
            map_smul' := fun r x => by
              change (show T.obj.obj U from ((β ≫ α).hom.app U).hom r) •
                  (show M.val.obj U from x) =
                (show T.obj.obj U from ((δ ≫ γ).hom.app U).hom r) • (show M.val.obj U from x)
              rw [h] }
        inv := ModuleCat.ofHom
          (X := ↑(((SheafOfModules.restrictScalars.{u} δ).obj
            ((SheafOfModules.restrictScalars.{u} γ).obj M)).val.obj U))
          (Y := ↑(((SheafOfModules.restrictScalars.{u} β).obj
            ((SheafOfModules.restrictScalars.{u} α).obj M)).val.obj U))
          { toFun := fun x => x
            map_add' := fun _ _ => rfl
            map_smul' := fun r x => by
              change (show T.obj.obj U from ((δ ≫ γ).hom.app U).hom r) •
                  (show M.val.obj U from x) =
                (show T.obj.obj U from ((β ≫ α).hom.app U).hom r) • (show M.val.obj U from x)
              rw [h] }
        hom_inv_id := rfl
        inv_hom_id := rfl }) (fun _ _ _ => rfl))) (fun _ => rfl)

end RestrictScalarsComp

section PushforwardRestrictScalars

variable {C : Type*} [Category C] {D : Type*} [Category D] {J : GrothendieckTopology C}
  {K : GrothendieckTopology D} {F : C ⥤ D} [F.IsContinuous J K]
  {R R' R'' : Sheaf J RingCat.{u}} {T : Sheaf K RingCat.{u}}

/-- A pushforward of sheaves of modules followed by two restrictions of scalars is the
pushforward along the composite structure map, by the identity on sections. -/
def _root_.SheafOfModules.pushforwardRestrictScalarsCompIso
    (φ : R ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj T) (α : R' ⟶ R) (β : R'' ⟶ R')
    (ψ : R'' ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj T) (h : β ≫ α ≫ φ = ψ) :
    SheafOfModules.pushforward.{u} φ ⋙ SheafOfModules.restrictScalars.{u} α ⋙
        SheafOfModules.restrictScalars.{u} β ≅ SheafOfModules.pushforward.{u} ψ :=
  NatIso.ofComponents (fun M => (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun U =>
      { hom := ModuleCat.ofHom
          (X := ↑(((SheafOfModules.restrictScalars.{u} β).obj
            ((SheafOfModules.restrictScalars.{u} α).obj
              ((SheafOfModules.pushforward.{u} φ).obj M))).val.obj U))
          (Y := ↑(((SheafOfModules.pushforward.{u} ψ).obj M).val.obj U))
          { toFun := fun x => x
            map_add' := fun _ _ => rfl
            map_smul' := fun r x => by
              change (show T.obj.obj (op (F.obj U.unop)) from ((β ≫ α ≫ φ).hom.app U).hom r) •
                  (show M.val.obj (op (F.obj U.unop)) from x) =
                (show T.obj.obj (op (F.obj U.unop)) from (ψ.hom.app U).hom r) •
                  (show M.val.obj (op (F.obj U.unop)) from x)
              rw [h] }
        inv := ModuleCat.ofHom
          (X := ↑(((SheafOfModules.pushforward.{u} ψ).obj M).val.obj U))
          (Y := ↑(((SheafOfModules.restrictScalars.{u} β).obj
            ((SheafOfModules.restrictScalars.{u} α).obj
              ((SheafOfModules.pushforward.{u} φ).obj M))).val.obj U))
          { toFun := fun x => x
            map_add' := fun _ _ => rfl
            map_smul' := fun r x => by
              change (show T.obj.obj (op (F.obj U.unop)) from (ψ.hom.app U).hom r) •
                  (show M.val.obj (op (F.obj U.unop)) from x) =
                (show T.obj.obj (op (F.obj U.unop)) from ((β ≫ α ≫ φ).hom.app U).hom r) •
                  (show M.val.obj (op (F.obj U.unop)) from x)
              rw [h] }
        hom_inv_id := rfl
        inv_hom_id := rfl }) (fun _ _ _ => rfl))) (fun _ => rfl)

end PushforwardRestrictScalars

/-- The comparison of Stacks 03G1 from the small étale site of `Z` to the model of its
spaces-étale site. -/
abbrev spacesEtaleModelChart (Z : AlgebraicSpaces B S hS) :
    SmallEtale B S hS Z.1 ⥤ SmallModel.{u} (SpacesEtale B S hS Z) :=
  comparisonFunctor B S hS Z ⋙ (equivSmallModel.{u} (SpacesEtale B S hS Z)).functor

/-- The comparison from the small étale site of `Z` to the model of its spaces-étale site is a
dense subsite. -/
instance isDenseSubsite_spacesEtaleModelChart (Z : AlgebraicSpaces B S hS) :
    (spacesEtaleModelChart B S hS Z).IsDenseSubsite (SmallEtale.topology B S hS Z.1)
      (smallModelTopology B S hS Z) :=
  Functor.isDenseSubsite_comp _ (SpacesEtale.topology B S hS Z) _ _ _

/-- The structure sheaf of the model of the spaces-étale site of `Z`, restricted to the small
étale site, is the structure sheaf of `Z`, as sheaves of commutative rings. -/
def spacesEtaleModelChartStructureIso (Z : AlgebraicSpaces B S hS) :
    ((spacesEtaleModelChart B S hS Z).sheafPushforwardContinuous CommRingCat.{u}
        (SmallEtale.topology B S hS Z.1) (smallModelTopology B S hS Z)).obj
          (spacesEtaleModelStructureSheaf B S hS Z) ≅
      structureSheaf B S hS Z.1 Z.2 :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (Functor.isoWhiskerLeft (comparisonFunctor B S hS Z).op
        (Functor.isoWhiskerRight (NatIso.op (equivSmallModel.{u} (SpacesEtale B S hS Z)).unitIso)
          (shrinkCommRingPresheaf.{u, u + 1} (SpacesEtale.structurePresheaf B S hS Z))) ≪≫
      comparisonStructureIso B S hS Z)

/-- `AlgebraicGeometry.Space.spacesEtaleModelChartStructureIso` for the underlying sheaves of
rings. -/
def spacesEtaleModelChartRingIso (Z : AlgebraicSpaces B S hS) :
    ((spacesEtaleModelChart B S hS Z).sheafPushforwardContinuous RingCat.{u}
        (SmallEtale.topology B S hS Z.1) (smallModelTopology B S hS Z)).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleModelStructureSheaf B S hS Z)) ≅
      structureRingSheaf B S hS Z :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (Functor.isoWhiskerRight ((sheafToPresheaf _ _).mapIso
      (spacesEtaleModelChartStructureIso B S hS Z)) (forget₂ CommRingCat.{u} RingCat.{u}))

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- Restriction along base change on the models. -/
abbrev smallModelBaseChangeRestriction :
    Sheaf (smallModelTopology B S hS X) (Type u) ⥤ Sheaf (smallModelTopology B S hS Y) (Type u) :=
  (smallModelBaseChange B S hS f).sheafPushforwardContinuous (Type u)
    (smallModelTopology B S hS Y) (smallModelTopology B S hS X)

/-- The comparison into the model of the spaces-étale site of `Y` followed by base change on the
models is continuous. -/
instance isContinuous_spacesEtaleModelChart_comp_smallModelBaseChange :
    (spacesEtaleModelChart B S hS Y ⋙ smallModelBaseChange B S hS f).IsContinuous
      (SmallEtale.topology B S hS Y.1) (smallModelTopology B S hS X) :=
  Functor.isContinuous_comp _ _ _ (smallModelTopology B S hS Y) _

/-- The comparison into the spaces-étale site of `Y`, followed by base change on the spaces-étale
sites and the equivalence with the model of `X`, is continuous. -/
instance isContinuous_comparisonFunctor_comp_spacesBaseChange_comp :
    (comparisonFunctor B S hS Y ⋙ (spacesBaseChange B S hS f).functor ⋙
        (equivSmallModel.{u} (SpacesEtale B S hS X)).functor).IsContinuous
      (SmallEtale.topology B S hS Y.1) (smallModelTopology B S hS X) :=
  haveI : ((spacesBaseChange B S hS f).functor ⋙
      (equivSmallModel.{u} (SpacesEtale B S hS X)).functor).IsContinuous
      (SpacesEtale.topology B S hS Y) (smallModelTopology B S hS X) :=
    Functor.isContinuous_comp _ _ _ (SpacesEtale.topology B S hS X) _
  Functor.isContinuous_comp _ _ _ (SpacesEtale.topology B S hS Y) _

/-- The base change on the models, read on the small étale site of `Y`, is base change on the
spaces-étale sites read on the small étale site, up to the unit of the model of `Y`. -/
def spacesEtaleModelChartBaseChangeIso :
    spacesEtaleModelChart B S hS Y ⋙ smallModelBaseChange B S hS f ≅
      comparisonFunctor B S hS Y ⋙ (spacesBaseChange B S hS f).functor ⋙
        (equivSmallModel.{u} (SpacesEtale B S hS X)).functor :=
  Functor.isoWhiskerLeft (comparisonFunctor B S hS Y)
    (Functor.isoWhiskerRight (equivSmallModel.{u} (SpacesEtale B S hS Y)).unitIso.symm
      ((spacesBaseChange B S hS f).functor ⋙ (equivSmallModel.{u} (SpacesEtale B S hS X)).functor))

/-- The square of sheaves of sets: base change on the models followed by restriction to the small
étale site of `Y` is restriction to the small étale site of `X` followed by the direct image. -/
def spacesEtaleModelChartDirectImageIso :
    smallModelBaseChangeRestriction B S hS f ⋙
        (spacesEtaleModelChart B S hS Y).sheafPushforwardContinuous (Type u)
          (SmallEtale.topology B S hS Y.1) (smallModelTopology B S hS Y) ≅
      (spacesEtaleModelChart B S hS X).sheafPushforwardContinuous (Type u)
          (SmallEtale.topology B S hS X.1) (smallModelTopology B S hS X) ⋙
        smallEtaleDirectImage B S hS f :=
  Functor.sheafPushforwardContinuousIso (spacesEtaleModelChartBaseChangeIso B S hS f) _ _ _ ≪≫
    Functor.isoWhiskerLeft
      ((equivSmallModel.{u} (SpacesEtale B S hS X)).functor.sheafPushforwardContinuous
        (Type u) (SpacesEtale.topology B S hS X) (smallModelTopology B S hS X))
      (smallToposMorphismTypeU_comparison B S hS f).symm

/-- The structure map of the morphism of models, as a map into the inverse image of the
structure sheaf along restriction. -/
def spacesEtaleModelSharpPullback :
    Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleModelStructureSheaf B S hS Y) ⟶
      pullbackRingSheaf (smallModelTopology B S hS Y) (smallModelBaseChangeRestriction B S hS f)
        (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleModelStructureSheaf B S hS X)) :=
  (spacesEtaleModelHom B S hS f).fSharpRing ≫ (restrictionRingIso _ _ _ _).inv

/-- The structure map of `f` on the small étale sites, read through the identifications of the
structure sheaves with the restricted structure sheaves of the models. -/
def spacesEtaleModelChartSharp :
    ((spacesEtaleModelChart B S hS Y).sheafPushforwardContinuous RingCat.{u}
        (SmallEtale.topology B S hS Y.1) (smallModelTopology B S hS Y)).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleModelStructureSheaf B S hS Y)) ⟶
      pullbackRingSheaf (SmallEtale.topology B S hS Y.1) (smallEtaleDirectImage B S hS f)
        (((spacesEtaleModelChart B S hS X).sheafPushforwardContinuous RingCat.{u}
          (SmallEtale.topology B S hS X.1) (smallModelTopology B S hS X)).obj
          (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleModelStructureSheaf B S hS X))) :=
  (spacesEtaleModelChartRingIso B S hS Y).hom ≫ structureSharp B S hS f ≫
    pullbackRingSheafMap _ _ (spacesEtaleModelChartRingIso B S hS X).inv

/-- The chart projections of `AlgebraicGeometry.Space.spacesEtaleModelChartDirectImageIso`: a
section over the base change of an étale chart `V` of `Y`, projected to an étale chart of `X`
above `X ×_Y V`, is its restriction along the corresponding morphism of the model of `X`. -/
theorem directImageChartProjection_spacesEtaleModelChartDirectImageIso
    (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op)
    (F : Sheaf (smallModelTopology B S hS X) (Type u))
    (y : F.obj.obj (op ((smallModelBaseChange B S hS f).obj
      ((spacesEtaleModelChart B S hS Y).obj V)))) :
    (directImageChartProjection B S hS f V j).app
        (((spacesEtaleModelChart B S hS X).sheafPushforwardContinuous (Type u)
          (SmallEtale.topology B S hS X.1) (smallModelTopology B S hS X)).obj F)
        (((spacesEtaleModelChartDirectImageIso B S hS f).hom.app F).hom.app (op V) y) =
      F.obj.map ((equivSmallModel.{u} (SpacesEtale B S hS X)).functor.map
        (j.hom.unop ≫ (spacesBaseChange B S hS f).functor.map
          ((equivSmallModel.{u} (SpacesEtale B S hS Y)).unitIso.hom.app
            ((comparisonFunctor B S hS Y).obj V)))).op y := by
  let H := ((equivSmallModel.{u} (SpacesEtale B S hS X)).functor.sheafPushforwardContinuous
    (Type u) (SpacesEtale.topology B S hS X) (smallModelTopology B S hS X)).obj F
  let z := ((Functor.sheafPushforwardContinuousIso (spacesEtaleModelChartBaseChangeIso B S hS f)
    (Type u) (SmallEtale.topology B S hS Y.1) (smallModelTopology B S hS X)).hom.app F).hom.app
      (op V) y
  have hinv : ((smallToposMorphismTypeU_comparison B S hS f).hom.app H).hom.app (op V)
      (((smallToposMorphismTypeU_comparison B S hS f).inv.app H).hom.app (op V) z) = z :=
    congrArg (fun φ => φ.hom.app (op V) z)
      ((smallToposMorphismTypeU_comparison B S hS f).inv_hom_id_app H)
  refine (directImageChartProjection_comparison B S hS f V j H _).trans ?_
  refine (congrArg (H.obj.map j.hom) hinv).trans ?_
  rw [Functor.map_comp, op_comp, FunctorToTypes.map_comp_apply]
  rfl

/-- The chart projections of `AlgebraicGeometry.Space.spacesEtaleModelChartSharp` are the
chartwise pullbacks of regular functions. -/
theorem directImageChartProjection_spacesEtaleModelChartSharp (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op)
    (x : ((spacesEtaleModelChart B S hS Y).sheafPushforwardContinuous RingCat.{u}
        (SmallEtale.topology B S hS Y.1) (smallModelTopology B S hS Y)).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleModelStructureSheaf B S hS Y))
          |>.obj.obj (op V)) :
    (directImageChartProjection B S hS f V j).app
        ((sheafCompose (SmallEtale.topology B S hS X.1) (forget RingCat.{u})).obj
          (((spacesEtaleModelChart B S hS X).sheafPushforwardContinuous RingCat.{u}
            (SmallEtale.topology B S hS X.1) (smallModelTopology B S hS X)).obj
            (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleModelStructureSheaf B S hS X))))
        ((spacesEtaleModelChartSharp B S hS f).hom.app (op V) x) =
      (spacesEtaleModelChartRingIso B S hS X).inv.hom.app j.right
        (chartPullback B S hS f V j
          ((spacesEtaleModelChartRingIso B S hS Y).hom.hom.app (op V) x)) :=
  (directImageChartProjection_ringSheafMap B S hS f V j
    (spacesEtaleModelChartRingIso B S hS X).inv _).trans
    (congrArg ((spacesEtaleModelChartRingIso B S hS X).inv.hom.app j.right)
      (directImageChartProjection_structureSharpSet B S hS f V j _))

/-- Pullback of regular functions along the chart morphism of Stacks 03G8, read through the
global functions of the represented algebraic spaces. -/
theorem chartPullback_globalFunctionsYonedaEquiv {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op)
    (τ : globalFunctions' B S hS ((SpacesEtale.toSpaces B S hS Y).obj
      ((comparisonFunctor B S hS Y).obj V)).1) :
    chartPullback B S hS f V j
        (globalFunctionsYonedaEquiv B S hS ((SmallEtale.toOver B S hS Y.1).obj V) τ) =
      globalFunctionsYonedaEquiv B S hS ((SmallEtale.toOver B S hS X.1).obj j.right.unop)
        (globalFunctionsMap B S hS ((SpacesEtale.toSpaces B S hS X).map j.hom.unop ≫
          (spacesBaseChange B S hS f).projection.app ((comparisonFunctor B S hS Y).obj V)) τ) :=
  (globalFunctionsMap_val_of_yoneda_map_comp B S hS
    ((SpacesEtale.toSpaces B S hS X).map j.hom.unop ≫
      (spacesBaseChange B S hS f).projection.app ((comparisonFunctor B S hS Y).obj V)) τ
    (idChart B S hS ((SmallEtale.toOver B S hS X.1).obj j.right.unop))
    (idChart B S hS ((SmallEtale.toOver B S hS Y.1).obj V))
    (chartBaseChangeMap B S hS f V j) (by
      refine (Category.comp_id _).trans ((yoneda_map_chartBaseChangeMap B S hS f V j).trans ?_)
      exact (Category.id_comp _).symm)).symm

/-- **The structure maps agree chartwise**: pulling a regular function back along the morphism of
models and restricting to an étale chart of `X` above `X ×_Y V` is the chartwise pullback of
Stacks 03G8. -/
theorem spacesEtaleModelChartRingIso_hom_map_fSharp (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op)
    (x : (spacesEtaleModelStructureSheaf B S hS Y).obj.obj
      (op ((spacesEtaleModelChart B S hS Y).obj V))) :
    (spacesEtaleModelChartRingIso B S hS X).hom.hom.app j.right
        ((spacesEtaleModelStructureSheaf B S hS X).obj.map
          ((equivSmallModel.{u} (SpacesEtale B S hS X)).functor.map
            (j.hom.unop ≫ (spacesBaseChange B S hS f).functor.map
              ((equivSmallModel.{u} (SpacesEtale B S hS Y)).unitIso.hom.app
                ((comparisonFunctor B S hS Y).obj V)))).op
          ((spacesEtaleModelHom B S hS f).fSharp.hom.app
            (op ((spacesEtaleModelChart B S hS Y).obj V)) x)) =
      chartPullback B S hS f V j
        ((spacesEtaleModelChartRingIso B S hS Y).hom.hom.app (op V) x) := by
  have hunit : ∀ {A A' : SpacesEtale B S hS X} (k : A ⟶ A'),
      (equivSmallModel.{u} (SpacesEtale B S hS X)).unitIso.hom.app A ≫
        (equivSmallModel.{u} (SpacesEtale B S hS X)).inverse.map
          ((equivSmallModel.{u} (SpacesEtale B S hS X)).functor.map k) ≫
        (equivSmallModel.{u} (SpacesEtale B S hS X)).unitIso.inv.app A' = k := fun k => by
    simp
  have hn := (spacesBaseChange B S hS f).projection.naturality
    ((equivSmallModel.{u} (SpacesEtale B S hS Y)).unitIso.hom.app
      ((comparisonFunctor B S hS Y).obj V))
  have h1 := hunit (A := (comparisonFunctor B S hS X).obj j.right.unop)
    (A' := (spacesBaseChange B S hS f).functor.obj
      ((equivSmallModel.{u} (SpacesEtale B S hS Y)).inverse.obj
        ((spacesEtaleModelChart B S hS Y).obj V)))
    (j.hom.unop ≫ (spacesBaseChange B S hS f).functor.map
      ((equivSmallModel.{u} (SpacesEtale B S hS Y)).unitIso.hom.app
        ((comparisonFunctor B S hS Y).obj V)))
  have E : (SpacesEtale.toSpaces B S hS X).map
        ((equivSmallModel.{u} (SpacesEtale B S hS X)).unitIso.hom.app
          ((comparisonFunctor B S hS X).obj j.right.unop)) ≫
      (SpacesEtale.toSpaces B S hS X).map ((equivSmallModel.{u} (SpacesEtale B S hS X)).inverse.map
        ((equivSmallModel.{u} (SpacesEtale B S hS X)).functor.map
          (j.hom.unop ≫ (spacesBaseChange B S hS f).functor.map
            ((equivSmallModel.{u} (SpacesEtale B S hS Y)).unitIso.hom.app
              ((comparisonFunctor B S hS Y).obj V))))) ≫
        spacesEtaleModelSharpMap B S hS f ((spacesEtaleModelChart B S hS Y).obj V) =
      ((SpacesEtale.toSpaces B S hS X).map j.hom.unop ≫
        (spacesBaseChange B S hS f).projection.app ((comparisonFunctor B S hS Y).obj V)) ≫
        (SpacesEtale.toSpaces B S hS Y).map
          ((equivSmallModel.{u} (SpacesEtale B S hS Y)).unitIso.hom.app
            ((comparisonFunctor B S hS Y).obj V)) := by
    rw [spacesEtaleModelSharpMap, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc,
      Category.assoc, h1, Functor.map_comp, Category.assoc, Category.assoc]
    exact congrArg ((SpacesEtale.toSpaces B S hS X).map j.hom.unop ≫ ·) hn
  refine (congrArg (globalFunctionsYonedaEquiv B S hS
      ((SmallEtale.toOver B S hS X.1).obj j.right.unop))
    (shrinkCommRingPresheaf_map_apply.{u, u + 1} (SpacesEtale.structurePresheaf B S hS X)
      ((equivSmallModel.{u} (SpacesEtale B S hS X)).unitIso.hom.app
        ((comparisonFunctor B S hS X).obj j.right.unop)).op _)).trans ?_
  refine (congrArg (fun t => globalFunctionsYonedaEquiv B S hS
      ((SmallEtale.toOver B S hS X.1).obj j.right.unop)
      (((SpacesEtale.structurePresheaf B S hS X).map
        ((equivSmallModel.{u} (SpacesEtale B S hS X)).unitIso.hom.app
          ((comparisonFunctor B S hS X).obj j.right.unop)).op).hom t))
    (spacesEtaleModelStructureSheaf_map_apply B S hS X _ _)).trans ?_
  refine (congrArg (fun t => globalFunctionsYonedaEquiv B S hS
      ((SmallEtale.toOver B S hS X.1).obj j.right.unop)
      (((SpacesEtale.structurePresheaf B S hS X).map
        ((equivSmallModel.{u} (SpacesEtale B S hS X)).unitIso.hom.app
          ((comparisonFunctor B S hS X).obj j.right.unop)).op).hom
        (((SpacesEtale.structurePresheaf B S hS X).map _).hom t)))
    (spacesEtaleModelHom_fSharp_apply B S hS f _ x)).trans ?_
  refine Eq.trans ?_ (congrArg (chartPullback B S hS f V j)
    (congrArg (globalFunctionsYonedaEquiv B S hS ((SmallEtale.toOver B S hS Y.1).obj V))
      (shrinkCommRingPresheaf_map_apply.{u, u + 1} (SpacesEtale.structurePresheaf B S hS Y)
        ((equivSmallModel.{u} (SpacesEtale B S hS Y)).unitIso.hom.app
          ((comparisonFunctor B S hS Y).obj V)).op x)).symm)
  refine Eq.trans ?_ (chartPullback_globalFunctionsYonedaEquiv B S hS f V j _).symm
  refine congrArg (globalFunctionsYonedaEquiv B S hS
    ((SmallEtale.toOver B S hS X.1).obj j.right.unop)) ?_
  refine Eq.trans ?_ ((RingHom.congr_fun (congrArg (fun φ => globalFunctionsMap B S hS φ) E)
    (Shrink.ringEquiv ((SpacesEtale.structurePresheaf B S hS Y).obj
      (op ((equivSmallModel.{u} (SpacesEtale B S hS Y)).inverse.obj
        ((spacesEtaleModelChart B S hS Y).obj V)))) x)).trans ?_)
  all_goals simp only [globalFunctionsMap_comp]; rfl

/-- **The structure maps of the morphism of models and of the morphism of small étale ringed topoi
agree**, read on the small étale site of `Y` through the square
`AlgebraicGeometry.Space.spacesEtaleModelChartDirectImageIso` of direct images of sheaves of
sets. -/
theorem spacesEtaleModelChartSharp_compat :
    ((spacesEtaleModelChart B S hS Y).sheafPushforwardContinuous (Type u)
        (SmallEtale.topology B S hS Y.1) (smallModelTopology B S hS Y)).map
        ((sheafCompose (smallModelTopology B S hS Y) (forget RingCat.{u})).map
          (spacesEtaleModelSharpPullback B S hS f)) ≫
      (spacesEtaleModelChartDirectImageIso B S hS f).hom.app
        (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf
          (spacesEtaleModelStructureSheaf B S hS X))) =
      (sheafCompose (SmallEtale.topology B S hS Y.1) (forget RingCat.{u})).map
        (spacesEtaleModelChartSharp B S hS f) := by
  refine Sheaf.hom_ext_sections (fun V x => ?_)
  refine directImageChartProjection_ext B S hS f V.unop _ (fun j => ?_)
  refine (directImageChartProjection_spacesEtaleModelChartDirectImageIso B S hS f V.unop j _
    _).trans ?_
  refine Eq.trans ?_ (directImageChartProjection_spacesEtaleModelChartSharp B S hS f V.unop j
    x).symm
  refine Eq.trans ?_ (congrArg ((spacesEtaleModelChartRingIso B S hS X).inv.hom.app j.right)
    (spacesEtaleModelChartRingIso_hom_map_fSharp B S hS f V.unop j x))
  exact (ConcreteCategory.congr_hom (congrArg (fun φ => φ.hom.app j.right)
    (spacesEtaleModelChartRingIso B S hS X).hom_inv_id) _).symm

/-- Restriction to the small étale site followed by the identification of the structure sheaves:
the functor of `AlgebraicGeometry.Space.spacesEtaleModelModulesEquiv`, without the detour through
the small étale model. -/
abbrev spacesEtaleModelChartModules (Z : AlgebraicSpaces B S hS) :
    (spacesEtaleModelRingedTopos B S hS Z).Modules ⥤ Modules.{u, u} B S hS Z.1 Z.2 :=
  restrictionModules (SmallEtale.topology B S hS Z.1) (smallModelTopology B S hS Z)
      (spacesEtaleModelChart B S hS Z)
      (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleModelStructureSheaf B S hS Z)) ⋙
    SheafOfModules.restrictScalars.{u} (spacesEtaleModelChartRingIso B S hS Z).inv

/-- The inverse of `AlgebraicGeometry.Space.spacesEtaleModelRingRestrictionIso` is the image of
the inverse of `AlgebraicGeometry.Space.spacesEtaleModelChartRingIso` under restriction to the
small étale model. -/
theorem spacesEtaleModelRingRestrictionIso_inv_eq (Z : AlgebraicSpaces B S hS) :
    (spacesEtaleModelRingRestrictionIso B S hS Z).inv =
      ((smallEtaleModelEquiv B S hS Z).inverse.sheafPushforwardContinuous RingCat.{u}
        (smallEtaleModelTopology B S hS Z.1) (SmallEtale.topology B S hS Z.1)).map
        (spacesEtaleModelChartRingIso B S hS Z).inv :=
  Sheaf.hom_ext (NatTrans.ext (funext fun _ => RingCat.hom_ext (RingHom.ext fun _ => rfl)))

/-- Restriction of scalars along the identification of the structure sheaves commutes with
restriction to the small étale model. -/
def spacesEtaleModelChartRestrictScalarsIso (Z : AlgebraicSpaces B S hS) :
    SheafOfModules.pushforward.{u} (F := (smallEtaleModelEquiv B S hS Z).inverse)
        (𝟙 (((smallEtaleModelEquiv B S hS Z).inverse.sheafPushforwardContinuous RingCat.{u}
          (smallEtaleModelTopology B S hS Z.1) (SmallEtale.topology B S hS Z.1)).obj
          (((spacesEtaleModelChart B S hS Z).sheafPushforwardContinuous RingCat.{u}
            (SmallEtale.topology B S hS Z.1) (smallModelTopology B S hS Z)).obj
            (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleModelStructureSheaf B S hS Z))))) ⋙
        SheafOfModules.restrictScalars.{u} (spacesEtaleModelRingRestrictionIso B S hS Z).inv ≅
      SheafOfModules.restrictScalars.{u} (spacesEtaleModelChartRingIso B S hS Z).inv ⋙
        (smallEtaleModelModulesEquiv B S hS Z).functor :=
  SheafOfModules.pushforwardCompRestrictScalarsIso _ _ _ _
    (Sheaf.hom_ext (NatTrans.ext (funext fun _ => RingCat.hom_ext (RingHom.ext fun _ => rfl))))

/-- `AlgebraicGeometry.Space.spacesEtaleModelChartModules` followed by restriction to the small
étale model is the restriction to the small étale model of the functor of
`AlgebraicGeometry.Space.spacesEtaleModelModulesEquiv`. -/
def spacesEtaleModelChartModulesRestrictionIso (Z : AlgebraicSpaces B S hS) :
    spacesEtaleModelChartModules B S hS Z ⋙ (smallEtaleModelModulesEquiv B S hS Z).functor ≅
      moduleRestriction (smallEtaleModelTopology B S hS Z.1) (smallModelTopology B S hS Z)
          (spacesEtaleModelComparison B S hS Z)
          (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleModelStructureSheaf B S hS Z)) ⋙
        SheafOfModules.restrictScalars.{u} (spacesEtaleModelRingRestrictionIso B S hS Z).inv :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (spacesEtaleModelChartRestrictScalarsIso B S hS Z).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (SheafOfModules.pushforwardComp _ _ ≪≫
      SheafOfModules.pushforwardCongr (Category.comp_id _)) _

/-- `AlgebraicGeometry.Space.spacesEtaleModelChartModules` is the functor of
`AlgebraicGeometry.Space.spacesEtaleModelModulesEquiv`. -/
def spacesEtaleModelChartModulesIso (Z : AlgebraicSpaces B S hS) :
    spacesEtaleModelChartModules B S hS Z ≅ (spacesEtaleModelModulesEquiv B S hS Z).functor :=
  (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft _ (smallEtaleModelModulesEquiv B S hS Z).unitIso ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (spacesEtaleModelChartModulesRestrictionIso B S hS Z) _ ≪≫
    Functor.associator _ _ _ ≪≫ eqToIso (spacesEtaleModelModulesEquiv_functor_eq B S hS Z).symm

/-- The direct image of modules along the morphism of models as restriction followed by two
restrictions of scalars. -/
def spacesEtaleModelPushforwardIsoRestriction :
    (spacesEtaleModelHom B S hS f).pushforwardTopos ≅
      restrictionModules (smallModelTopology B S hS Y) (smallModelTopology B S hS X)
          (smallModelBaseChange B S hS f)
          (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleModelStructureSheaf B S hS X)) ⋙
        SheafOfModules.restrictScalars.{u} (restrictionRingIso (smallModelTopology B S hS Y)
          (smallModelTopology B S hS X) (smallModelBaseChange B S hS f)
          (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleModelStructureSheaf B S hS X))).hom ⋙
        SheafOfModules.restrictScalars.{u} (spacesEtaleModelSharpPullback B S hS f) :=
  (SheafOfModules.pushforwardRestrictScalarsCompIso (F := smallModelBaseChange B S hS f)
    (J := smallModelTopology B S hS Y) (K := smallModelTopology B S hS X) (𝟙 _)
    (restrictionRingIso (smallModelTopology B S hS Y)
      (smallModelTopology B S hS X) (smallModelBaseChange B S hS f)
      (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleModelStructureSheaf B S hS X))).hom
    (spacesEtaleModelSharpPullback B S hS f) (spacesEtaleModelHom B S hS f).fSharpRing
    (Sheaf.hom_ext (NatTrans.ext (funext fun _ =>
      RingCat.hom_ext (RingHom.ext fun _ => rfl))))).symm

/-- The direct image of modules along the morphism of models, followed by restriction to the
small étale site, as an inverse image of modules along restriction of sheaves of sets. -/
def spacesEtaleModelPushforwardRestrictionIso :
    (spacesEtaleModelHom B S hS f).pushforwardTopos ⋙
        restrictionModules (SmallEtale.topology B S hS Y.1) (smallModelTopology B S hS Y)
          (spacesEtaleModelChart B S hS Y)
          (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleModelStructureSheaf B S hS Y)) ≅
      pullbackModuleFunctor (smallModelTopology B S hS Y) (smallModelBaseChangeRestriction B S hS f)
          (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleModelStructureSheaf B S hS X)) ⋙
        SheafOfModules.restrictScalars.{u} (spacesEtaleModelSharpPullback B S hS f) ⋙
        restrictionModules (SmallEtale.topology B S hS Y.1) (smallModelTopology B S hS Y)
          (spacesEtaleModelChart B S hS Y)
          (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleModelStructureSheaf B S hS Y)) :=
  Functor.isoWhiskerRight (spacesEtaleModelPushforwardIsoRestriction B S hS f) _ ≪≫
    Functor.isoWhiskerRight (Functor.associator
      (restrictionModules (smallModelTopology B S hS Y) (smallModelTopology B S hS X)
        (smallModelBaseChange B S hS f)
        (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleModelStructureSheaf B S hS X)))
      (SheafOfModules.restrictScalars.{u} (restrictionRingIso (smallModelTopology B S hS Y)
        (smallModelTopology B S hS X) (smallModelBaseChange B S hS f)
        (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleModelStructureSheaf B S hS X))).hom)
      (SheafOfModules.restrictScalars.{u} (spacesEtaleModelSharpPullback B S hS f))).symm _ ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerRight
      (restrictionModuleIso (smallModelTopology B S hS Y) (smallModelTopology B S hS X)
        (smallModelBaseChange B S hS f)
        (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleModelStructureSheaf B S hS X))).symm
      (SheafOfModules.restrictScalars.{u} (spacesEtaleModelSharpPullback B S hS f))) _ ≪≫
    Functor.associator _ _ _

/-- **The direct images of modules on the spaces-étale models and on the small étale sites
agree**, under restriction to the small étale sites. -/
def spacesEtaleModelChartModulesPushforwardIso :
    (spacesEtaleModelHom B S hS f).pushforwardTopos ⋙ spacesEtaleModelChartModules B S hS Y ≅
      spacesEtaleModelChartModules B S hS X ⋙ modulePushforward B S hS f :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (spacesEtaleModelPushforwardRestrictionIso B S hS f ≪≫
      restrictionPullbackModuleSquareIso (spacesEtaleModelChartDirectImageIso B S hS f)
        (spacesEtaleModelSharpPullback B S hS f) (spacesEtaleModelChartSharp B S hS f)
        (spacesEtaleModelChartSharp_compat B S hS f)) _ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (SheafOfModules.restrictScalarsCompCongrIso _ _ _ _
        (Iso.inv_hom_id_assoc _ _)) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (Stacks.Sheaves.ToposPullback.pullbackModuleFunctorRestrictScalarsIso
          (SmallEtale.topology B S hS Y.1) (smallEtaleDirectImage B S hS f)
          (spacesEtaleModelChartRingIso B S hS X).inv).symm _ ≪≫
      Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm

/-- `AlgebraicGeometry.Space.spacesEtaleModelChartModulesPushforwardIso` for the functors of
`AlgebraicGeometry.Space.spacesEtaleModelModulesEquiv`. -/
def spacesEtaleModelModulesPushforwardIso :
    (spacesEtaleModelHom B S hS f).pushforwardTopos ⋙
        (spacesEtaleModelModulesEquiv B S hS Y).functor ≅
      (spacesEtaleModelModulesEquiv B S hS X).functor ⋙ modulePushforward B S hS f :=
  Functor.isoWhiskerLeft _ (spacesEtaleModelChartModulesIso B S hS Y).symm ≪≫
    spacesEtaleModelChartModulesPushforwardIso B S hS f ≪≫
    Functor.isoWhiskerRight (spacesEtaleModelChartModulesIso B S hS X) _

/-- The pullback of modules along the morphism of small étale ringed topoi is left adjoint to
`AlgebraicGeometry.Space.modulePushforward`. -/
def smallEtaleModulePullbackModulesAdjunction :
    smallEtaleModulePullbackModules B S hS f ⊣ modulePushforward B S hS f :=
  (RingedToposHom.pullbackAdjPushforwardModules (smallEtaleRingedToposHom B S hS f)).ofNatIsoRight
    (pushforwardModulesIsoModulePushforward B S hS f)

/-- The comparison of the inverse images of modules, as the mate of the comparison of direct
images. -/
def spacesEtaleModelModulesPullbackHom :
    (spacesEtaleModelModulesEquiv B S hS Y).functor ⋙ smallEtaleModulePullbackModules B S hS f ⟶
      (spacesEtaleModelHom B S hS f).pullbackTopos ⋙
        (spacesEtaleModelModulesEquiv B S hS X).functor :=
  Adjunction.mateOfRightIso (spacesEtaleModelHom B S hS f).pullbackPushforwardAdjunctionTopos
    (smallEtaleModulePullbackModulesAdjunction B S hS f)
    (spacesEtaleModelModulesPushforwardIso B S hS f)

/-- The comparison `AlgebraicGeometry.Space.spacesEtaleModelModulesPullbackHom` of the inverse
images of modules is an isomorphism. -/
instance isIso_spacesEtaleModelModulesPullbackHom :
    IsIso (spacesEtaleModelModulesPullbackHom B S hS f) :=
  Adjunction.isIso_mateOfRightIso _ _ _
    (spacesEtaleModelModulesEquiv B S hS Y).fullyFaithfulFunctor
    (spacesEtaleModelModulesEquiv B S hS X).fullyFaithfulFunctor

/-- **The inverse image of modules along the morphism of models of the spaces-étale sites is the
inverse image of modules along the morphism of small étale ringed topoi**, under the equivalences
of Stacks 03G1. -/
def spacesEtaleModelModulesPullbackIso :
    (spacesEtaleModelHom B S hS f).pullbackTopos ⋙
        (spacesEtaleModelModulesEquiv B S hS X).functor ≅
      (spacesEtaleModelModulesEquiv B S hS Y).functor ⋙ smallEtaleModulePullbackModules B S hS f :=
  (asIso (spacesEtaleModelModulesPullbackHom B S hS f)).symm

section Perfect

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance 10000] HasDerivedCategory.standard

/-- **Stacks 08H6 on the small étale sites**: for a morphism `f : X ⟶ Y` of algebraic spaces,
the derived pullback `Lf^*` sends perfect objects of `D(𝒪_Y)` to perfect objects of `D(𝒪_X)`. -/
theorem isPerfect_smallEtaleDerivedModulePullback_of_hasLeftDerivedFunctor
    [(smallEtaleModulePullbackOnHomotopy B S hS f).HasLeftDerivedFunctor
      (smallEtaleModuleQuasiIso B S hS Y)]
    (K : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
    (hK : (smallEtaleRingedSite B S hS Y.1 Y.2).IsPerfect K) :
    (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect
      ((smallEtaleDerivedModulePullback B S hS f).obj K) :=
  isPerfect_smallEtaleDerivedModulePullback_of_modelIso B S hS f
    (spacesEtaleModelModulesPullbackIso B S hS f) K hK

end Perfect

end AlgebraicGeometry.Space
