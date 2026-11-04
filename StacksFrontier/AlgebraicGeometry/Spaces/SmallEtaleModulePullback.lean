module

public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfModulesRestrictScalarsCongr
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHom
public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.RingedToposHomModules
public import StacksFrontier.Deformation.ToposThickening.PushforwardComparison.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Pullback of modules along a morphism of algebraic spaces

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`. This file constructs the inverse image `f^* : Mod(𝒪_Y) ⥤ Mod(𝒪_X)` of modules on the
small étale sites and the adjunction `f^* ⊣ f_*` with the direct image
`AlgebraicGeometry.Space.modulePushforward`, at the module universe of the structure rings.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleRingedToposModulesHom`: the morphism of small étale ringed
  topoi of `f`, as a `Stacks.Sheaves.RingedToposModules.RingedToposHom`.
* `AlgebraicGeometry.Space.modulePullback`: the inverse image `f^*` of `𝒪_Y`-modules, that is
  `𝒪_X ⊗_{f⁻¹𝒪_Y} f⁻¹(-)`.
* `AlgebraicGeometry.Space.pushforwardModulesIsoModulePushforward`: the natural isomorphism
  between the direct image of modules of the morphism of small étale ringed topoi and
  `AlgebraicGeometry.Space.modulePushforward`, whose components are the identity on sections.
* `AlgebraicGeometry.Space.modulePushforwardIso`: the comparison of the two direct images of
  modules, restricting scalars before or after taking the direct image.
* `AlgebraicGeometry.Space.modulePullbackAdjunction`: the adjunction `f^* ⊣ f_*`.

## Main results

* `AlgebraicGeometry.Space.smallEtaleRingedToposHom_pushforward_eq`: the geometric direct image
  of the morphism of small étale ringed topoi is `AlgebraicGeometry.Space.smallEtaleDirectImage`.
* `AlgebraicGeometry.Space.pushforwardModules_eq_modulePushforward`: the direct image of modules
  of the morphism of small étale ringed topoi is `AlgebraicGeometry.Space.modulePushforward`.
* `AlgebraicGeometry.Space.eqToIso_pushforwardModules_eq_modulePushforward`: the transport along
  that equality is `AlgebraicGeometry.Space.pushforwardModulesIsoModulePushforward`.
* `AlgebraicGeometry.Space.modulePullback_eq` and `AlgebraicGeometry.Space.modulePushforward_eq`:
  the two definitions, stated as equations.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public section

open CategoryTheory
open Stacks.Sheaves.RingedToposModules (pushforwardModules pullbackAdjPushforwardModules)

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- The morphism of small étale ringed topoi `AlgebraicGeometry.Space.smallEtaleRingedToposHom`
of a morphism of algebraic spaces, as a `Stacks.Sheaves.RingedToposModules.RingedToposHom`. -/
noncomputable def smallEtaleRingedToposModulesHom (f : X ⟶ Y) :
    Stacks.Sheaves.RingedToposModules.RingedToposHom
      (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y) :=
  (smallEtaleRingedToposHom B S hS f).toRingedToposModulesHom

/-- The geometric direct image of the morphism of small étale ringed topoi of `f` is
`AlgebraicGeometry.Space.smallEtaleDirectImage`. -/
theorem smallEtaleRingedToposHom_pushforward_eq (f : X ⟶ Y) :
    (smallEtaleRingedToposModulesHom B S hS f).toToposHom.pushforward =
      smallEtaleDirectImage B S hS f :=
  rfl

/-- The pullback `f^*G = 𝒪_X ⊗_{f⁻¹𝒪_Y} f⁻¹G` of `𝒪_Y`-modules along a morphism `f : X ⟶ Y`
of algebraic spaces. -/
@[stacks 03LU "pullback"]
noncomputable def modulePullback (f : X ⟶ Y) :
    Modules.{u, u} B S hS Y.1 Y.2 ⥤ Modules.{u, u} B S hS X.1 X.2 :=
  (smallEtaleRingedToposModulesHom B S hS f).pullbackModules

/-- The inverse image of `𝒪`-modules along a morphism of algebraic spaces is the pullback of
modules along the morphism of small étale ringed topoi of `f`. -/
theorem modulePullback_eq (f : X ⟶ Y) :
    modulePullback B S hS f =
      (smallEtaleRingedToposModulesHom B S hS f).pullbackModules :=
  rfl

/-- The direct image of `𝒪`-modules along a morphism of algebraic spaces is the direct image
`AlgebraicGeometry.Space.moduleDirectImage` followed by restriction of scalars along the
structure map `AlgebraicGeometry.Space.structureSharp`. -/
theorem modulePushforward_eq (f : X ⟶ Y) :
    modulePushforward B S hS f =
      moduleDirectImage B S hS f ⋙
        SheafOfModules.restrictScalars (structureSharp B S hS f) :=
  rfl

/-- The direct image of `𝒪_X`-modules attached to the morphism of small étale ringed topoi of
`f` is `AlgebraicGeometry.Space.modulePushforward`. -/
theorem pushforwardModules_eq_modulePushforward (f : X ⟶ Y) :
    (smallEtaleRingedToposHom B S hS f).pushforwardModules = modulePushforward B S hS f :=
  congrArg (fun φ ↦ moduleDirectImage B S hS f ⋙ SheafOfModules.restrictScalars φ)
    (forgetCommRingSheaf_map_fSharp B S hS f)

/-- The direct image of `𝒪_X`-modules attached to the morphism of small étale ringed topoi of
`f` is isomorphic to `AlgebraicGeometry.Space.modulePushforward`, by the natural isomorphism
whose components are the identity on sections. -/
noncomputable def pushforwardModulesIsoModulePushforward (f : X ⟶ Y) :
    (smallEtaleRingedToposHom B S hS f).pushforwardModules ≅ modulePushforward B S hS f :=
  Functor.isoWhiskerLeft (moduleDirectImage B S hS f)
    (SheafOfModules.restrictScalarsCongr (forgetCommRingSheaf_map_fSharp B S hS f))

/-- The component-wise identification of the two direct images of modules is the identity on
sections. -/
theorem pushforwardModulesIsoModulePushforward_hom_app_val_app (f : X ⟶ Y)
    (N : Modules.{u, u} B S hS X.1 X.2) (W : (SmallEtale B S hS Y.1)ᵒᵖ)
    (y : ((smallEtaleRingedToposHom B S hS f).pushforwardModules.obj N).val.obj W) :
    ((pushforwardModulesIsoModulePushforward B S hS f).hom.app N).val.app W y = y := rfl

/-- The comparison of the two direct images of modules is the identity on underlying sheaves of
sets. -/
@[simp]
theorem moduleSheafFunctor_map_pushforwardModulesIsoModulePushforward_hom_app (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).map
        ((pushforwardModulesIsoModulePushforward B S hS f).hom.app F) =
      𝟙 ((smallToposMorphismTypeU B S hS f).pushforward.obj
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj F)) := rfl

/-- The inverse of the comparison of the two direct images of modules is the identity on
underlying sheaves of sets. -/
@[simp]
theorem moduleSheafFunctor_map_pushforwardModulesIsoModulePushforward_inv_app (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).map
        ((pushforwardModulesIsoModulePushforward B S hS f).inv.app F) =
      𝟙 ((smallToposMorphismTypeU B S hS f).pushforward.obj
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj F)) := rfl

/-- The direct image of modules acts on a morphism by the direct image of sheaves of sets
`(AlgebraicGeometry.Space.smallToposMorphismTypeU f).pushforward` of the underlying morphism. -/
theorem moduleSheafFunctor_map_modulePushforward_map_geometric (f : X ⟶ Y)
    {M N : Modules.{u, u} B S hS X.1 X.2} (φ : M ⟶ N) :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).map
        ((modulePushforward B S hS f).map φ) =
      (smallToposMorphismTypeU B S hS f).pushforward.map
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map φ) :=
  Sheaf.hom_ext_sections fun _ _ ↦ rfl

/-- The transport along `AlgebraicGeometry.Space.pushforwardModules_eq_modulePushforward` is the
identity on underlying sheaves of sets. -/
theorem moduleSheafFunctor_map_eqToHom_pushforwardModules_eq_modulePushforward_app (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).map
        ((eqToHom (pushforwardModules_eq_modulePushforward B S hS f)).app F) =
      𝟙 ((smallToposMorphismTypeU B S hS f).pushforward.obj
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj F)) :=
  ((congrArg (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).map
        (eqToHom_app (pushforwardModules_eq_modulePushforward B S hS f) F)).trans
      (eqToHom_map (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y))
        (Functor.congr_obj (pushforwardModules_eq_modulePushforward B S hS f) F))).trans
    (eqToHom_refl _ _)

/-- The transport along `AlgebraicGeometry.Space.pushforwardModules_eq_modulePushforward` is
`AlgebraicGeometry.Space.pushforwardModulesIsoModulePushforward`. -/
theorem eqToIso_pushforwardModules_eq_modulePushforward (f : X ⟶ Y) :
    eqToIso (pushforwardModules_eq_modulePushforward B S hS f) =
      pushforwardModulesIsoModulePushforward B S hS f := by
  refine Iso.ext (NatTrans.ext (funext fun F ↦ ?_))
  refine Stacks.Sheaves.RingedToposModules.hom_ext_moduleSheafFunctor
    (R := structureRingSheaf B S hS Y) ?_
  refine Eq.trans ?_
    (moduleSheafFunctor_map_pushforwardModulesIsoModulePushforward_hom_app B S hS f F).symm
  exact moduleSheafFunctor_map_eqToHom_pushforwardModules_eq_modulePushforward_app B S hS f F

/-- The comparison of the two direct images of modules: the direct image built from the morphism
of small étale ringed topoi, restricting scalars along the inverse-image form `f⁻¹𝒪_Y ⟶ 𝒪_X` of
the structure map and then taking the direct image, is isomorphic to
`AlgebraicGeometry.Space.modulePushforward`, which takes the direct image first and then
restricts along the direct-image form `𝒪_Y ⟶ f_*𝒪_X`. -/
noncomputable def modulePushforwardIso (f : X ⟶ Y) :
    pushforwardModules (X := smallEtaleRingedTopos B S hS X)
        (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposModulesHom B S hS f) ≅
      modulePushforward B S hS f :=
  (smallEtaleRingedToposHom B S hS f).pushforwardModulesIso ≪≫
    pushforwardModulesIsoModulePushforward B S hS f

/-- Pullback of `𝒪`-modules along a morphism of algebraic spaces is left adjoint to the
pushforward `AlgebraicGeometry.Space.modulePushforward`: there is a bijection
`Hom_{𝒪_X}(f^*G, F) = Hom_{𝒪_Y}(G, f_*F)`, natural in both variables. -/
@[stacks 03LU "the adjunction"]
noncomputable def modulePullbackAdjunction (f : X ⟶ Y) :
    modulePullback B S hS f ⊣ modulePushforward B S hS f :=
  (pullbackAdjPushforwardModules (X := smallEtaleRingedTopos B S hS X)
    (Y := smallEtaleRingedTopos B S hS Y)
    (smallEtaleRingedToposModulesHom B S hS f)).ofNatIsoRight (modulePushforwardIso B S hS f)

end AlgebraicGeometry.Space

end
