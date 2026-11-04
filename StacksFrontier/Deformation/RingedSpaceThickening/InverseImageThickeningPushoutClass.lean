module

public import StacksFrontier.Deformation.RingedSpaceThickening.InverseImageThickeningClasses
public import
  StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.ClosedSubsetPullbackLeftExact
import StacksCore.Tactic.StacksAttribute

/-!
# The class of the pushout extension of Stacks 0GQ2

Let `f : (X, 𝒪_X) ⟶ (S, 𝒪_S)` and `g : (Y, 𝒪_Y) ⟶ (X, 𝒪_X)` be morphisms of ringed spaces, `ℱ`
an `𝒪_X`-module, `𝒢` an `𝒪_Y`-module, `c : ℱ ⟶ g_*𝒢` a `g`-map and
`0 ⟶ ℱ ⟶ 𝒪_{X'} ⟶ 𝒪_X ⟶ 0` an extension of `f⁻¹𝒪_S`-algebras with square-zero ideal, with class
`ξ ∈ Ext¹_{𝒪_X}(𝖭𝖫_{X/S}, ℱ)` (**Stacks 0GPZ**). **Stacks 0GQ2** observes that the class of the
pushout `𝒪'₁` of `g⁻¹𝒪_{X'}` along `c : g⁻¹ℱ ⟶ 𝒢`, an extension of `g⁻¹𝒪_X` by `𝒢` over the
ringed space `(Y, g⁻¹𝒪_X)`, corresponds to the image of `ξ`, through the identification of
`Ext¹_{g⁻¹𝒪_X}(𝖭𝖫_{g⁻¹𝒪_X/g⁻¹f⁻¹𝒪_S}, 𝒢)` with `Ext¹_{g⁻¹𝒪_X}(g⁻¹𝖭𝖫_{X/S}, 𝒢)` given by the
canonical map `g⁻¹𝖭𝖫_{X/S} ⟶ 𝖭𝖫_{g⁻¹𝒪_X/g⁻¹f⁻¹𝒪_S}` (**Stacks 08TM**).

Here `g⁻¹ = π^*` is the pullback of modules along the projection
`π : (Y, g⁻¹𝒪_X) ⟶ (X, 𝒪_X)` (`inverseImageProj g`), an exact functor; the image of `ξ` is
`π^*ξ` followed by the `g⁻¹𝒪_X`-linear map `c^♭ : g⁻¹ℱ ⟶ 𝒢` adjoint to `c`
(`inverseImagePushoutExtMap`); and the canonical map is
`AlgebraicGeometry.RingedSpaceThickening.pullbackNaiveCotangentMap` for `π`.

## Main results

* `extClass_inverseImagePushout`: the class of `𝒪'₁`, read on `g⁻¹𝖭𝖫_{X/S}`, is the image of the
  class of `𝒪_{X'}`.

The comparison is an isomorphism (`isIso_pullbackNaiveCotangentMap`), so the class of `𝒪'₁` is
equally an element of `Ext¹_{g⁻¹𝒪_X}(𝖭𝖫_{g⁻¹𝒪_X/g⁻¹f⁻¹𝒪_S}, 𝒢)`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.SheafOfModules (ringedSpaceStructureMap)
open Stacks.Sites.SqZeroPushout
open Stacks.Sites.Conormal (kernelIdeal)

universe u

namespace AlgebraicGeometry.RingedSpaceThickening

variable {X S Y : RingedSpace.{u, u}} (f : X ⟶ S) (g : Y ⟶ X)

/-- The projection `π : (Y, g⁻¹𝒪_X) ⟶ (X, 𝒪_X)`: the map `g` on spaces, with the unit
`𝒪_X ⟶ g_*g⁻¹𝒪_X` on structure sheaves. -/
abbrev inverseImageProj : inverseImageRingedSpace g ⟶ X :=
  RingedSpace.inverseImageProjection X g.hom.base

/-- The pullback of modules along `π : (Y, g⁻¹𝒪_X) ⟶ (X, 𝒪_X)` preserves finite limits. -/
instance : PreservesFiniteLimits (modulePullback (inverseImageProj g)) :=
  preservesFiniteLimits_inverseImageModulePullback X g.hom.base

/-- The pullback of modules along `π : (Y, g⁻¹𝒪_X) ⟶ (X, 𝒪_X)` preserves finite colimits. -/
instance : PreservesFiniteColimits (modulePullback (inverseImageProj g)) :=
  letI := (modulePullbackPushforwardAdjunction (inverseImageProj g)).leftAdjoint_preservesColimits
  inferInstance

attribute [local instance 10000] HasDerivedCategory.standard

variable {f g} {F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (J := Opens.grothendieckTopology X.carrier) X.sheaf)}
  {G : SheafOfModules.{u} (structureSheafRing Y)}

/-- The `g`-map `c : ℱ ⟶ g_*𝒢`, read as an `𝒪_X`-linear map `ℱ ⟶ π_*𝒢` into the pushforward along
`π` of `𝒢` viewed as a `g⁻¹𝒪_X`-module: the same map on sections. -/
def inverseImageIdealPush (c : F ⟶ (modulePushforward g).obj G) :
    F ⟶ (modulePushforward (inverseImageProj g)).obj (restrictedModule g G) :=
  ⟨PresheafOfModules.homMk ((PresheafOfModules.toPresheaf _).map c.val :
      F.val.presheaf ⟶ ((modulePushforward g).obj G).val.presheaf) (fun U r m ↦
    ((c.val.app U).hom.map_smul r m).trans (congrArg (fun (s : (structureSheafRing Y).obj.obj
      (op ((Opens.map g.hom.base).obj U.unop))) ↦ s • (show G.val.obj (op ((Opens.map
      g.hom.base).obj U.unop)) from (c.val.app U).hom m)) (c_app_eq g U.unop r)))⟩

/-- `c^♭ : g⁻¹ℱ = π^*ℱ ⟶ 𝒢`, the `g⁻¹𝒪_X`-linear map adjoint to `c`. -/
def inverseImageIdealMap (c : F ⟶ (modulePushforward g).obj G) :
    (modulePullback (inverseImageProj g)).obj F ⟶ restrictedModule g G :=
  ((modulePullbackPushforwardAdjunction (inverseImageProj g)).homEquiv _ _).symm
    (inverseImageIdealPush c)

/-- **The image of `ξ`**: `Ext¹_{𝒪_X}(𝖭𝖫_{X/S}, ℱ) ⟶ Ext¹_{g⁻¹𝒪_X}(g⁻¹𝖭𝖫_{X/S}, 𝒢)`, the inverse
image along `π` (an exact functor) followed by `c^♭ : g⁻¹ℱ ⟶ 𝒢`. -/
def inverseImagePushoutExtMap (c : F ⟶ (modulePushforward g).obj G)
    (z : extOneNaiveCotangent f F) :=
  (modulePullback (inverseImageProj g)).mapExtOne z ≫
    ((DerivedCategory.singleFunctor _ 0).map (inverseImageIdealMap c))⟦(1 : ℤ)⟧'

section PushoutClass

variable (P : SquareZeroAlgebraExtension f F) (c : F ⟶ (modulePushforward g).obj G)

/-- `𝒪_{X'} ⟶ g_*g⁻¹𝒪_{X'} ⟶ g_*𝒪'₁`: the unit followed by the comparison of the pushout. -/
abbrev pushoutFstPush : P.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u}
    (inverseImageProj g).hom.base).obj (inverseImagePushout G P c).sheaf :=
  (adjP g.hom.base).unit.app P.sheaf ≫
    (TopCat.Sheaf.pushforward CommRingCat.{u} g.hom.base).map (inverseImagePushoutMap P c)

/-- The presentation of `𝒪_X` by the sections of `𝒪_{X'}` maps to that of `g⁻¹𝒪_X` by the
sections of `𝒪'₁` along `𝒪_{X'} ⟶ g_*𝒪'₁`: compatibility with the generators. -/
theorem pushoutGenerators_comm :
    Functor.whiskerRight (pushoutFstPush P c).hom (forget CommRingCat.{u}) ≫
        Functor.whiskerLeft (Opens.map (inverseImageProj g).hom.base).op
          (inverseImagePushout G P c).generatorsMap =
      P.generatorsMap ≫ Functor.whiskerRight (structureComorphism (inverseImageProj g)).hom
        (forget CommRingCat.{u}) := by
  refine NatTrans.ext (funext fun U ↦ ?_)
  ext x
  exact (congrArg (fun t ↦ (t.hom.app (op ((Opens.map g.hom.base).obj U.unop))).hom
    (unitSec g P.sheaf U.unop x)) (inverseImagePushoutMap_comp_reduction P c)).trans
      (unitSec_naturality g P.reduction U.unop x).symm

/-- The chain map `𝖭𝖫(α) ⟶ π_*𝖭𝖫(α₁)` from the presentation of `𝒪_X` by the sections of `𝒪_{X'}`
to that of `g⁻¹𝒪_X` by the sections of `𝒪'₁`. -/
def pushoutPresentationMap :=
  letI := P.toAlgebraSquareZeroExtension.presentation_isLocallySurjective
  letI := (inverseImagePushout G P c).toAlgebraSquareZeroExtension.presentation_isLocallySurjective
  Stacks.SheafOfModules.presentationNaiveCotangentPushMap (inverseImageProj g).hom.base
    (E₁ := P.generators) (α₁ := P.generatorsMap)
    (E₂ := (inverseImagePushout G P c).generators)
    (α₂ := (inverseImagePushout G P c).generatorsMap)
    (structureRingMap_comp_structureComorphism (inverseImageProj g) f) (pushoutGenerators_comm P c)

/-- The comparison `𝖭𝖫(α) ⟶ 𝖭𝖫_{X/S}` of Stacks 08TL for the presentation of `𝒪_X` by the
sections of `𝒪_{X'}`. -/
abbrev sourcePresentationComparison :=
  letI := P.toAlgebraSquareZeroExtension.presentation_isLocallySurjective
  Stacks.SheafOfModules.naiveCotangentComplexComparison.{u, u, u, u}
    (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) X.sheaf
    (structureRingMap f) P.generators P.generatorsMap

/-- The comparison `𝖭𝖫(α₁) ⟶ 𝖭𝖫_{g⁻¹𝒪_X/g⁻¹f⁻¹𝒪_S}` of Stacks 08TL for the presentation of
`g⁻¹𝒪_X` by the sections of `𝒪'₁`. -/
abbrev pushoutPresentationComparison :=
  letI := (inverseImagePushout G P c).toAlgebraSquareZeroExtension.presentation_isLocallySurjective
  Stacks.SheafOfModules.naiveCotangentComplexComparison.{u, u, u, u}
    (Opens.grothendieckTopology (inverseImageRingedSpace g).carrier)
    (inverseImageBaseRing (inverseImageSpaceHom f g)) (inverseImageRingedSpace g).sheaf
    (structureRingMap (inverseImageSpaceHom f g)) (inverseImagePushout G P c).generators
    (inverseImagePushout G P c).generatorsMap

/-- The comparison map of the presentation by the sections of `𝒪_{X'}`, followed by the
pushforward map on naive cotangent complexes, equals `pushoutPresentationMap` followed by `π_*`
of the comparison map of the presentation by the sections of `𝒪'₁`. -/
theorem pushoutPresentationComparison_comp :
    sourcePresentationComparison P ≫ naiveCotangentPushMap (inverseImageProj g) f =
      pushoutPresentationMap P c ≫ ((modulePushforward (inverseImageProj g)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (pushoutPresentationComparison P c) :=
  let := P.toAlgebraSquareZeroExtension.presentation_isLocallySurjective
  let := (inverseImagePushout G P c).toAlgebraSquareZeroExtension.presentation_isLocallySurjective
  let := Stacks.SheafOfModules.presentation_id_isLocallySurjective
    (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) X.sheaf (structureRingMap f)
  let := Stacks.SheafOfModules.presentation_id_isLocallySurjective
    (Opens.grothendieckTopology (inverseImageRingedSpace g).carrier)
    (inverseImageBaseRing (inverseImageSpaceHom f g)) (inverseImageRingedSpace g).sheaf
    (structureRingMap (inverseImageSpaceHom f g))
  (Stacks.SheafOfModules.presentationNaiveCotangentPushMap_naturality
      (inverseImageProj g).hom.base
      (α₁' := 𝟙 _) (α₂' := 𝟙 _)
      P.generatorsMap (inverseImagePushout G P c).generatorsMap (pushoutGenerators_comm P c)
      (Category.comp_id _) (Category.comp_id _)
      (structureRingMap_comp_structureComorphism (inverseImageProj g) f)
      (pushoutGenerators_comm P c) (underlyingPresheafMap_comp (inverseImageProj g))).symm

/-- `f⁻¹𝒪_S ⟶ g_*g⁻¹f⁻¹𝒪_S ⟶ g_*g⁻¹𝒪_{X'}` is `f⁻¹𝒪_S ⟶ 𝒪_{X'} ⟶ g_*g⁻¹𝒪_{X'}`. -/
theorem baseRingPushMap_comp_inverseImageBase :
    baseRingPushMap (inverseImageProj g) f ≫
        (TopCat.Sheaf.pushforward CommRingCat.{u} g.hom.base).map (inverseImageBase (g := g) P) =
      P.base ≫ (adjP g.hom.base).unit.app P.sheaf := by
  refine ((adjP f.hom.base).homEquiv _ _).injective ?_
  have h1 : (adjP f.hom.base).homEquiv _ _ (baseRingPushMap (inverseImageProj g) f ≫
        (TopCat.Sheaf.pushforward CommRingCat.{u} g.hom.base).map (inverseImageBase (g := g) P)) =
      (adjP (inverseImageProj g ≫ f).hom.base).unit.app S.sheaf ≫
        (TopCat.Sheaf.pushforward CommRingCat.{u} (inverseImageProj g ≫ f).hom.base).map
          (inverseImageBase (g := g) P) :=
    ((adjP f.hom.base).homEquiv_naturality_right _ _).trans
      (congrArg (· ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).map
        ((TopCat.Sheaf.pushforward CommRingCat.{u} g.hom.base).map (inverseImageBase (g := g) P)))
        (homEquiv_baseRingPushMap (inverseImageProj g) f))
  have h2 : (adjP (inverseImageProj g ≫ f).hom.base).unit.app S.sheaf ≫
        (TopCat.Sheaf.pushforward CommRingCat.{u} (inverseImageProj g ≫ f).hom.base).map
          (inverseImageBase (g := g) P) =
      (adjP (inverseImageProj g ≫ f).hom.base).homEquiv _ _ (inverseImageBase (g := g) P) :=
    ((adjP (inverseImageProj g ≫ f).hom.base).homEquiv_unit _ _ _).symm
  exact h1.trans (h2.trans ((homEquiv_inverseImageBase (g := g) P).trans
    ((adjP f.hom.base).homEquiv_naturality_right _ _).symm))

/-- On the coefficients of the free algebra, `freeAlgebraPushMap` followed by the lift of `𝒪'₁`
is the lift of `𝒪_{X'}` followed by `𝒪_{X'} ⟶ g_*𝒪'₁`. -/
theorem pushoutFreeAlgebraPushMap_comp_lift_coeff :
    Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X.carrier)
        (inverseImageBaseRing f) P.generators ≫
      Stacks.SheafOfModules.freeAlgebraPushMap (inverseImageProj g).hom.base
          (inverseImageBaseRing f) P.generators
          (inverseImageBaseRing (inverseImageSpaceHom f g)) (inverseImagePushout G P c).generators
          (baseRingPushMap (inverseImageProj g) f)
          (Functor.whiskerRight (pushoutFstPush P c).hom (forget CommRingCat.{u})) ≫
        (TopCat.Sheaf.pushforward CommRingCat.{u} (inverseImageProj g).hom.base).map
          (inverseImagePushout G P c).lift =
    Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X.carrier)
        (inverseImageBaseRing f) P.generators ≫
      P.lift ≫ pushoutFstPush P c := by
  have e1 := Stacks.SheafOfModules.freeAlgebraSheafCoefficientMap_comp_freeAlgebraPushMap
    (inverseImageProj g).hom.base (inverseImageBaseRing f) P.generators
    (inverseImageBaseRing (inverseImageSpaceHom f g)) (inverseImagePushout G P c).generators
    (baseRingPushMap (inverseImageProj g) f)
    (Functor.whiskerRight (pushoutFstPush P c).hom (forget CommRingCat.{u}))
  have e2 := Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap_comp_desc
    (Opens.grothendieckTopology (inverseImageRingedSpace g).carrier)
    (inverseImageBaseRing (inverseImageSpaceHom f g))
    (inverseImagePushout G P c).sheaf (inverseImagePushout G P c).generators
    (inverseImagePushout G P c).base (𝟙 _)
  have e3 := Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap_comp_desc
    (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) P.sheaf P.generators
    P.base (𝟙 _)
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ (TopCat.Sheaf.pushforward CommRingCat.{u}
    (inverseImageProj g).hom.base).map (inverseImagePushout G P c).lift) e1).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (baseRingPushMap (inverseImageProj g) f ≫ ·)
    ((Functor.map_comp _ _ _).symm.trans (congrArg _ e2))).trans ?_
  refine Eq.trans ?_ ((Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ pushoutFstPush P c) e3)).symm
  have e4 : (TopCat.Sheaf.pushforward CommRingCat.{u} g.hom.base).map
      (inverseImagePushout G P c).base =
      (TopCat.Sheaf.pushforward CommRingCat.{u} g.hom.base).map (inverseImageBase (g := g) P) ≫
        (TopCat.Sheaf.pushforward CommRingCat.{u} g.hom.base).map (inverseImagePushoutMap P c) :=
    Functor.map_comp _ (inverseImageBase (g := g) P) (inverseImagePushoutMap P c)
  refine (congrArg (baseRingPushMap (inverseImageProj g) f ≫ ·) e4).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} g.hom.base).map
    (inverseImagePushoutMap P c)) (baseRingPushMap_comp_inverseImageBase P)).trans ?_
  exact Category.assoc _ _ _

/-- On the variables of the free algebra, `freeAlgebraPushMap` followed by the lift of `𝒪'₁` is
the lift of `𝒪_{X'}` followed by `𝒪_{X'} ⟶ g_*𝒪'₁`. -/
theorem pushoutFreeAlgebraPushMap_comp_lift_variable :
    Stacks.Sites.FreeAlgebra.freeAlgebraSheafVariable (Opens.grothendieckTopology X.carrier)
        (inverseImageBaseRing f) P.generators ≫
      Functor.whiskerRight
        ((sheafToPresheaf (Opens.grothendieckTopology X.carrier) CommRingCat.{u}).map
          (Stacks.SheafOfModules.freeAlgebraPushMap (inverseImageProj g).hom.base
              (inverseImageBaseRing f) P.generators
              (inverseImageBaseRing (inverseImageSpaceHom f g))
              (inverseImagePushout G P c).generators
              (baseRingPushMap (inverseImageProj g) f)
              (Functor.whiskerRight (pushoutFstPush P c).hom (forget CommRingCat.{u})) ≫
            (TopCat.Sheaf.pushforward CommRingCat.{u} (inverseImageProj g).hom.base).map
              (inverseImagePushout G P c).lift))
        (forget CommRingCat.{u}) =
    Stacks.Sites.FreeAlgebra.freeAlgebraSheafVariable (Opens.grothendieckTopology X.carrier)
        (inverseImageBaseRing f) P.generators ≫
      Functor.whiskerRight
        ((sheafToPresheaf (Opens.grothendieckTopology X.carrier) CommRingCat.{u}).map
          (P.lift ≫ pushoutFstPush P c))
        (forget CommRingCat.{u}) := by
  have hv1 := Stacks.SheafOfModules.freeAlgebraSheafVariable_comp_freeAlgebraPushMap
    (inverseImageProj g).hom.base (inverseImageBaseRing f) P.generators
    (inverseImageBaseRing (inverseImageSpaceHom f g)) (inverseImagePushout G P c).generators
    (baseRingPushMap (inverseImageProj g) f)
    (Functor.whiskerRight (pushoutFstPush P c).hom (forget CommRingCat.{u}))
  have hv2 := Stacks.Sites.FreeAlgebra.freeAlgebraSheafVariable_comp_desc
    (Opens.grothendieckTopology (inverseImageRingedSpace g).carrier)
    (inverseImageBaseRing (inverseImageSpaceHom f g))
    (inverseImagePushout G P c).sheaf (inverseImagePushout G P c).generators
    (inverseImagePushout G P c).base (𝟙 _)
  have hv3 := Stacks.Sites.FreeAlgebra.freeAlgebraSheafVariable_comp_desc
    (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) P.sheaf P.generators
    P.base (𝟙 _)
  refine NatTrans.ext (funext fun U ↦ ?_)
  ext x
  have a1 := congrArg (fun t ↦ t x) (NatTrans.congr_app hv1 U)
  have a2 := congrArg (fun t ↦ t (((pushoutFstPush P c).hom.app U).hom x))
    (NatTrans.congr_app hv2 ((Opens.map (inverseImageProj g).hom.base).op.obj U))
  have a3 := congrArg (fun t ↦ t x) (NatTrans.congr_app hv3 U)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, types_comp_apply, NatTrans.id_app,
    types_id_apply] at a1 a2 a3
  exact (congrArg ((inverseImagePushout G P c).lift.hom.app _).hom a1).trans (a2.trans
    (congrArg ((pushoutFstPush P c).hom.app U).hom a3).symm)

/-- The polynomial presentation of `𝒪_X` by the sections of `𝒪_{X'}` maps to that of `g⁻¹𝒪_X`
by the sections of `𝒪'₁` compatibly with the lifts. -/
theorem pushoutFreeAlgebraPushMap_comp_lift :
    Stacks.SheafOfModules.freeAlgebraPushMap (inverseImageProj g).hom.base
        (inverseImageBaseRing f) P.generators
        (inverseImageBaseRing (inverseImageSpaceHom f g)) (inverseImagePushout G P c).generators
        (baseRingPushMap (inverseImageProj g) f)
        (Functor.whiskerRight (pushoutFstPush P c).hom (forget CommRingCat.{u})) ≫
      (TopCat.Sheaf.pushforward CommRingCat.{u} (inverseImageProj g).hom.base).map
        (inverseImagePushout G P c).lift =
      P.lift ≫ pushoutFstPush P c :=
  Stacks.Sites.FreeAlgebra.freeAlgebraSheaf_hom_ext _ _ _ _
    (pushoutFreeAlgebraPushMap_comp_lift_coeff P c)
    (pushoutFreeAlgebraPushMap_comp_lift_variable P c)

/-- The conormal homomorphism `𝒦/𝒦² ⟶ ℱ` of `𝒪_{X'}`, typed on the conormal sequence. -/
abbrev sourcePresentationConormal :
    (Stacks.SheafOfModules.presentationConormalSequence.{u, u, u, u}
      (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) X.sheaf
      (structureRingMap f) P.generators P.generatorsMap).X₁ ⟶ F :=
  Stacks.Sites.Conormal.conormalDesc.{u, u, u, u} _ F
    P.toAlgebraSquareZeroExtension.idealRestriction

/-- The conormal homomorphism `𝒥/𝒥² ⟶ 𝒢` of `𝒪'₁`, typed on the conormal sequence. -/
abbrev pushoutPresentationConormal :
    letI :=
      (inverseImagePushout G P c).toAlgebraSquareZeroExtension.presentation_isLocallySurjective
    (Stacks.SheafOfModules.presentationConormalSequence.{u, u, u, u}
      (Opens.grothendieckTopology (inverseImageRingedSpace g).carrier)
      (inverseImageBaseRing (inverseImageSpaceHom f g)) (inverseImageRingedSpace g).sheaf
      (structureRingMap (inverseImageSpaceHom f g)) (inverseImagePushout G P c).generators
      (inverseImagePushout G P c).generatorsMap).X₁ ⟶ restrictedModule g G :=
  Stacks.Sites.Conormal.conormalDesc.{u, u, u, u} _ (restrictedModule g G)
    (inverseImagePushout G P c).toAlgebraSquareZeroExtension.idealRestriction

/-- The map `𝒦/𝒦² ⟶ π_*(𝒥/𝒥²)` of conormal sheaves along `𝒪_{X'} ⟶ g_*𝒪'₁`. -/
abbrev pushoutConormalMap :=
  letI := P.toAlgebraSquareZeroExtension.presentation_isLocallySurjective
  letI := (inverseImagePushout G P c).toAlgebraSquareZeroExtension.presentation_isLocallySurjective
  Stacks.SheafOfModules.presentationConormalPushMap (inverseImageProj g).hom.base
    (E₁ := P.generators) (α₁ := P.generatorsMap)
    (E₂ := (inverseImagePushout G P c).generators)
    (α₂ := (inverseImagePushout G P c).generatorsMap)
    (structureRingMap_comp_structureComorphism (inverseImageProj g) f) (pushoutGenerators_comm P c)

/-- The degree `-1` component of `pushoutPresentationMap`. -/
theorem pushoutPresentationMap_f_negOne :
    letI := P.toAlgebraSquareZeroExtension.presentation_isLocallySurjective
    letI :=
      (inverseImagePushout G P c).toAlgebraSquareZeroExtension.presentation_isLocallySurjective
    (pushoutPresentationMap P c).f (-1) =
      eqToHom (Stacks.SheafOfModules.presentationNaiveCotangentComplex_X_negOne.{u, u, u, u}
          (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) X.sheaf
          (structureRingMap f) P.generators P.generatorsMap) ≫
        pushoutConormalMap P c ≫
        (modulePushforward (inverseImageProj g)).map
          (eqToHom (Stacks.SheafOfModules.presentationNaiveCotangentComplex_X_negOne.{u, u, u, u}
            (Opens.grothendieckTopology (inverseImageRingedSpace g).carrier)
            (inverseImageBaseRing (inverseImageSpaceHom f g)) (inverseImageRingedSpace g).sheaf
            (structureRingMap (inverseImageSpaceHom f g)) (inverseImagePushout G P c).generators
            (inverseImagePushout G P c).generatorsMap).symm) :=
  let := P.toAlgebraSquareZeroExtension.presentation_isLocallySurjective
  let := (inverseImagePushout G P c).toAlgebraSquareZeroExtension.presentation_isLocallySurjective
  Stacks.SheafOfModules.presentationNaiveCotangentPushMap_f_negOne (inverseImageProj g).hom.base
    (E₁ := P.generators) (α₁ := P.generatorsMap)
    (E₂ := (inverseImagePushout G P c).generators)
    (α₂ := (inverseImagePushout G P c).generatorsMap)
    (structureRingMap_comp_structureComorphism (inverseImageProj g) f) (pushoutGenerators_comm P c)

/-- The map of conormal sheaves followed by the conormal homomorphism of `𝒪'₁` is the conormal
homomorphism of `𝒪_{X'}` followed by `c`. -/
theorem pushoutConormalMap_comp :
    pushoutConormalMap P c ≫
        (modulePushforward (inverseImageProj g)).map (pushoutPresentationConormal P c) =
      sourcePresentationConormal P ≫ inverseImageIdealPush c := by
  refine Stacks.Sites.Conormal.conormal_hom_ext.{u, u, u, u} _ _ (fun U x ↦ ?_)
  show ((modulePushforward (inverseImageProj g)).map (pushoutPresentationConormal P c)).val.app U
    ((pushoutConormalMap P c).val.app U _) = (inverseImageIdealPush c).val.app U
      ((sourcePresentationConormal P).val.app U _)
  let ψ := Stacks.SheafOfModules.freeAlgebraPushMap (inverseImageProj g).hom.base
    (inverseImageBaseRing f) P.generators
    (inverseImageBaseRing (inverseImageSpaceHom f g)) (inverseImagePushout G P c).generators
    (baseRingPushMap (inverseImageProj g) f)
    (Functor.whiskerRight (pushoutFstPush P c).hom (forget CommRingCat.{u}))
  have hψc := Stacks.SheafOfModules.freeAlgebraPushMap_comp_presentation
    (inverseImageProj g).hom.base
    (structureRingMap_comp_structureComorphism (inverseImageProj g) f) (pushoutGenerators_comm P c)
  have h1 := Stacks.Sites.Conormal.conormalSheafMapPush_toAssociatedModule
    (inverseImageProj g).hom.base X.sheaf (inverseImageRingedSpace g).sheaf
    (structureComorphism (inverseImageProj g))
    P.presentation (inverseImagePushout G P c).presentation ψ hψc U
    ((kernelIdeal P.presentation.hom U).toCotangent x)
  refine (congrArg (((modulePushforward (inverseImageProj g)).map
    (pushoutPresentationConormal P c)).val.app U).hom h1).trans ?_
  have hψ := Stacks.Sites.Conormal.kernelIdeal_le_comap_sectionsMapPush
    (inverseImageProj g).hom.base X.sheaf (inverseImageRingedSpace g).sheaf
    (structureComorphism (inverseImageProj g))
    P.presentation (inverseImagePushout G P c).presentation ψ hψc U x.2
  have h2 := Stacks.Sites.Conormal.conormalDesc_toAssociatedModule
    (inverseImagePushout G P c).presentation (restrictedModule g G)
    (inverseImagePushout G P c).toAlgebraSquareZeroExtension.idealRestriction
    ((Opens.map (inverseImageProj g).hom.base).op.obj U) ⟨_, hψ⟩
  have h3 := Stacks.Sites.Conormal.conormalDesc_toAssociatedModule P.presentation F
    P.toAlgebraSquareZeroExtension.idealRestriction U x
  refine h2.trans (Eq.trans ?_ (congrArg ((inverseImageIdealPush c).val.app U).hom h3).symm)
  have h4 := congrArg (fun t ↦ (t.hom.app U).hom x.1) (pushoutFreeAlgebraPushMap_comp_lift P c)
  let a : kernelIdeal P.reduction.hom U :=
    ⟨_, P.toAlgebraSquareZeroExtension.lift_mem_kernelIdeal U x⟩
  have ha := unitSec_mem_kernelIdeal (g := g) P U.unop a
  refine (congrArg ((inverseImagePushout G P c).ideal.app _) (Subtype.ext (h4.trans
    (inverseImagePushoutMap_app_kernel P c ((Opens.map g.hom.base).obj U.unop) ⟨_, ha⟩)))).trans ?_
  exact ((inverseImagePushout G P c).ideal_incl _ _).trans
    (idealMap_app_unitSec (P := P) (G := G) (c := c) U.unop a ha)

/-- The degreewise description of the adjoint transpose of a chain map along `π^* ⊣ π_*`. -/
theorem mapHomologicalComplex_homEquiv_symm_f
    {K : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ}
    {L : CochainComplex (SheafOfModules.{u} (structureSheafRing (inverseImageRingedSpace g))) ℤ}
    (ψ : K ⟶ ((modulePushforward (inverseImageProj g)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj L) (n : ℤ) :
    ((((modulePullbackPushforwardAdjunction (inverseImageProj g)).mapHomologicalComplex
        (ComplexShape.up ℤ)).homEquiv _ _).symm ψ).f n =
      ((modulePullbackPushforwardAdjunction (inverseImageProj g)).homEquiv _ _).symm (ψ.f n) := by
  simp [Adjunction.homEquiv_counit, Adjunction.mapHomologicalComplex]

/-- The adjoint transpose `π^*𝖭𝖫(α) ⟶ 𝖭𝖫(α₁)` of `pushoutPresentationMap`. -/
abbrev pushoutPresentationMapAdj :=
  (((modulePullbackPushforwardAdjunction (inverseImageProj g)).mapHomologicalComplex
    (ComplexShape.up ℤ)).homEquiv _ _).symm (pushoutPresentationMap P c)

/-- `π^*` of the comparison map of the presentation by the sections of `𝒪_{X'}`, followed by
`pullbackNaiveCotangentMap`, equals `pushoutPresentationMapAdj` followed by the comparison map
of the presentation by the sections of `𝒪'₁`. -/
theorem pushoutPresentationMapAdj_comp :
    ((modulePullback (inverseImageProj g)).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (sourcePresentationComparison P) ≫ pullbackNaiveCotangentMap (inverseImageProj g) f =
      pushoutPresentationMapAdj P c ≫ pushoutPresentationComparison P c :=
  (((modulePullbackPushforwardAdjunction (inverseImageProj g)).mapHomologicalComplex
      (ComplexShape.up ℤ)).homEquiv_naturality_left_symm _ _).symm.trans
    ((congrArg (((modulePullbackPushforwardAdjunction (inverseImageProj g)).mapHomologicalComplex
      (ComplexShape.up ℤ)).homEquiv _ _).symm (pushoutPresentationComparison_comp P c)).trans
      (((modulePullbackPushforwardAdjunction (inverseImageProj g)).mapHomologicalComplex
        (ComplexShape.up ℤ)).homEquiv_naturality_right_symm _ _))

/-- **The degree `-1` condition**: `π^*` of the conormal homomorphism of `𝒪_{X'}` followed by
`c^♭` is the degree `-1` part of `π^*𝖭𝖫(α) ⟶ 𝖭𝖫(α₁)` followed by the conormal homomorphism of
`𝒪'₁`. -/
theorem pushoutConormal_adj_comp :
    (modulePullback (inverseImageProj g)).map
        (eqToHom (Stacks.SheafOfModules.presentationNaiveCotangentComplex_X_negOne.{u, u, u, u}
          (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) X.sheaf
          (structureRingMap f) P.generators P.generatorsMap) ≫ sourcePresentationConormal P) ≫
        inverseImageIdealMap c =
      (pushoutPresentationMapAdj P c).f (-1) ≫
        eqToHom (Stacks.SheafOfModules.presentationNaiveCotangentComplex_X_negOne.{u, u, u, u}
            (Opens.grothendieckTopology (inverseImageRingedSpace g).carrier)
            (inverseImageBaseRing (inverseImageSpaceHom f g)) (inverseImageRingedSpace g).sheaf
            (structureRingMap (inverseImageSpaceHom f g)) (inverseImagePushout G P c).generators
            (inverseImagePushout G P c).generatorsMap) ≫ pushoutPresentationConormal P c := by
  refine ((modulePullbackPushforwardAdjunction (inverseImageProj g)).homEquiv _ _).injective ?_
  refine ((modulePullbackPushforwardAdjunction (inverseImageProj g)).homEquiv_naturality_left
    _ _).trans ?_
  refine (congrArg (_ ≫ ·) (((modulePullbackPushforwardAdjunction
    (inverseImageProj g)).homEquiv _ _).apply_symm_apply (inverseImageIdealPush c))).trans ?_
  refine Eq.trans ?_ ((modulePullbackPushforwardAdjunction
    (inverseImageProj g)).homEquiv_naturality_right _ _).symm
  refine Eq.trans ?_ (congrArg (· ≫ _) ((congrArg _ (mapHomologicalComplex_homEquiv_symm_f
    (pushoutPresentationMap P c) (-1))).trans (((modulePullbackPushforwardAdjunction
      (inverseImageProj g)).homEquiv _ _).apply_symm_apply _))).symm
  refine (Category.assoc _ _ _).trans ?_
  refine Eq.trans ?_ (congrArg (· ≫ _) (pushoutPresentationMap_f_negOne P c)).symm
  exact (Functor.eqToHom_comp_comp_map_eqToHom_comp_map _ _ _ _ _ _ _
    (pushoutConormalMap_comp P c)).symm

/-- **The class of `𝒪'₁` is the image of `ξ`.** The class of the pushout `𝒪'₁` of `g⁻¹𝒪_{X'}`
along `c`, read on `g⁻¹𝖭𝖫_{X/S}` through the canonical map
`g⁻¹𝖭𝖫_{X/S} ⟶ 𝖭𝖫_{g⁻¹𝒪_X/g⁻¹f⁻¹𝒪_S}`, is `g⁻¹ξ` followed by `c^♭ : g⁻¹ℱ ⟶ 𝒢`. -/
theorem extClass_inverseImagePushout (P : SquareZeroAlgebraExtension f F)
    (c : F ⟶ (modulePushforward g).obj G) :
    DerivedCategory.Q.map (pullbackNaiveCotangentMap (inverseImageProj g) f) ≫
        (inverseImagePushout G P c).extClass =
      inverseImagePushoutExtMap c P.extClass :=
  Functor.Q_map_comp_conormalExtClass_eq_mapExtOne_comp (modulePullback (inverseImageProj g)) _ _
    (sourcePresentationComparison P) (pushoutPresentationComparison P c)
    ((DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
      (Stacks.SheafOfModules.quasiIso_naiveCotangentComplexComparison _ _ _ _ _))
    ((DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
      (Stacks.SheafOfModules.quasiIso_naiveCotangentComplexComparison _ _ _ _ _))
    (pushoutPresentationMapAdj P c) (pullbackNaiveCotangentMap (inverseImageProj g) f)
    (pushoutPresentationMapAdj_comp P c) (inverseImageIdealMap c)
    (sourcePresentationConormal P) (pushoutPresentationConormal P c)
    (Stacks.SheafOfModules.presentationNaiveCotangentComplex_X_negOne.{u, u, u, u}
      (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) X.sheaf
      (structureRingMap f) P.generators P.generatorsMap)
    (Stacks.SheafOfModules.presentationNaiveCotangentComplex_X_negOne.{u, u, u, u}
      (Opens.grothendieckTopology (inverseImageRingedSpace g).carrier)
      (inverseImageBaseRing (inverseImageSpaceHom f g)) (inverseImageRingedSpace g).sheaf
      (structureRingMap (inverseImageSpaceHom f g)) (inverseImagePushout G P c).generators
      (inverseImagePushout G P c).generatorsMap)
    (pushoutConormal_adj_comp P c)

end PushoutClass

end AlgebraicGeometry.RingedSpaceThickening
