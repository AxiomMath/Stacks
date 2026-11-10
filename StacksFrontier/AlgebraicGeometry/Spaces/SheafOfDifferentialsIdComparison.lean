module

public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentials
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackId
public import StacksFrontier.CategoryTheory.Adjunction.LeftAdjointCompIsoHomEquiv

/-!
# The comparison map of differentials at an identity square

Stacks 04CX attaches to a commutative square with top edge `f : X' ⟶ X` and left edge
`p' : X' ⟶ Y'` a comparison map `c_f : f^*Ω_{X/Y} ⟶ Ω_{X'/Y'}` of `𝒪_{X'}`-modules, uniquely
characterized by carrying `f^*d_{X/Y}(t)` to `d_{X'/Y'}(f♯ t)`:
`AlgebraicGeometry.Space.IsSheafOfDifferentialsMap` is that characterizing property and
`AlgebraicGeometry.Space.eq_of_isSheafOfDifferentialsMap` its uniqueness.

This file identifies the comparison map at a square whose horizontal edges are identities.  It
is the unit law `(𝟙 X)^* ≅ 𝟭` of Stacks 03LU, `AlgebraicGeometry.Space.modulePullbackIdIso`,
evaluated at `Ω_{X/Y}`; in particular it is an isomorphism.

## Main results

* `AlgebraicGeometry.Space.isSheafOfDifferentialsMap_modulePullbackIdIso`: the unit law of
  Stacks 03LU at `Ω_{X/Y}` has the characterizing property of Stacks 04CX for the square whose
  horizontal edges are the identity of `X`.
* `AlgebraicGeometry.Space.isIso_of_isSheafOfDifferentialsMap_id`: the comparison map of
  Stacks 04CX at an identity square is an isomorphism.

## References

* [Stacks Project, Tag 04CX](https://stacks.math.columbia.edu/tag/04CX)
* [Stacks Project, Tag 04CT](https://stacks.math.columbia.edu/tag/04CT)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The direct-image unit law on underlying sheaves of sets -/

/-- The unit law for the direct image of `𝒪`-modules attached to the morphism of small étale
ringed topoi of `𝟙 X`: that direct image is the identity functor. -/
def pushforwardModulesIsoIdSmallEtale (X : AlgebraicSpaces B S hS) :
    𝟭 (Modules.{u, u} B S hS X.1 X.2) ≅
      (smallEtaleRingedToposHom B S hS (𝟙 X)).pushforwardModules :=
  RingedToposHom.pushforwardModulesIsoId (smallEtaleRingedToposHom B S hS (𝟙 X))
    (smallEtaleDirectImageIdIso B S hS X).symm
    ((forgetRing_map_fSharp B S hS (𝟙 X)).trans (structureSharpSet_id B S hS X))

/-- The unit law `AlgebraicGeometry.Space.modulePushforwardIdIso` for the direct image of
`𝒪`-modules, exhibited as its two factors: the unit law for the direct image attached to the
morphism of ringed topoi, transported along
`AlgebraicGeometry.Space.pushforwardModules_eq_modulePushforward`. -/
theorem modulePushforwardIdIso_eq (X : AlgebraicSpaces B S hS) :
    modulePushforwardIdIso B S hS X =
      eqToIso (pushforwardModules_eq_modulePushforward B S hS (𝟙 X)).symm ≪≫
        (pushforwardModulesIsoIdSmallEtale B S hS X).symm :=
  rfl

/-- **On underlying sheaves of sets,
`AlgebraicGeometry.Space.pushforwardModulesIsoIdSmallEtale` is the identification
`AlgebraicGeometry.Space.smallEtaleDirectImageIdIso` of the direct image of sheaves of sets along
an identity with the identity functor.** -/
theorem moduleSheafFunctor_map_pushforwardModulesIsoIdSmallEtale_hom_app
    (X : AlgebraicSpaces B S hS) (M : Modules.{u, u} B S hS X.1 X.2) :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
        ((pushforwardModulesIsoIdSmallEtale B S hS X).hom.app M) =
      (smallEtaleDirectImageIdIso B S hS X).inv.app
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj M) :=
  rfl

set_option maxHeartbeats 1000000 in
-- The kernel's check of the defeq of the underlying sheaves of sets exceeds the default.
/-- The identification of `AlgebraicGeometry.Space.pushforwardModules_eq_modulePushforward` at an
identity is the identity on underlying sheaves of sets. -/
theorem moduleSheafFunctor_map_eqToHom_pushforwardModules_eq_id_app
    (X : AlgebraicSpaces B S hS) (M : Modules.{u, u} B S hS X.1 X.2)
    (h : (smallEtaleRingedToposHom B S hS (𝟙 X)).pushforwardModules =
      modulePushforward B S hS (𝟙 X)) :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map ((eqToHom h).app M) =
      𝟙 ((smallToposMorphismTypeU B S hS (𝟙 X)).pushforward.obj
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj M)) :=
  ((congrArg (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
        (eqToHom_app h M)).trans
      (eqToHom_map (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X))
        (Functor.congr_obj h M))).trans
    (eqToHom_refl _ _)

section Reducible

attribute [local implicit_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite

/-- The unit law for the direct image of `𝒪`-modules, componentwise, split into the unit law of
the direct image attached to the morphism of ringed topoi and the transport. -/
theorem modulePushforwardIdIso_inv_app_eq (X : AlgebraicSpaces B S hS)
    (M : Modules.{u, u} B S hS X.1 X.2) :
    (modulePushforwardIdIso B S hS X).inv.app M =
      (pushforwardModulesIsoIdSmallEtale B S hS X).hom.app M ≫
        (eqToIso (pushforwardModules_eq_modulePushforward B S hS (𝟙 X)).symm).inv.app M := by
  rw [modulePushforwardIdIso_eq, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app]

/-- **On underlying sheaves of sets the unit law for the direct image of `𝒪`-modules along an
identity is the unit law for the direct image of sheaves of sets.** -/
theorem moduleSheafFunctor_map_modulePushforwardIdIso_inv_app (X : AlgebraicSpaces B S hS)
    (M : Modules.{u, u} B S hS X.1 X.2) :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
        ((modulePushforwardIdIso B S hS X).inv.app M) =
      (smallEtaleDirectImageIdIso B S hS X).inv.app
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj M) := by
  rw [modulePushforwardIdIso_inv_app_eq, CategoryTheory.Functor.map_comp, eqToIso.inv,
    moduleSheafFunctor_map_eqToHom_pushforwardModules_eq_id_app]
  exact (Category.comp_id _).trans
    (moduleSheafFunctor_map_pushforwardModulesIsoIdSmallEtale_hom_app B S hS X M)

end Reducible

/-- The unit law for the direct image of `𝒪`-modules along an identity, read on a section. -/
theorem modulePushforwardIdIso_inv_app_val_app_apply (X : AlgebraicSpaces B S hS)
    (M : Modules.{u, u} B S hS X.1 X.2) (U : (SmallEtale B S hS X.1)ᵒᵖ) (m : M.val.obj U) :
    (((modulePushforwardIdIso B S hS X).inv.app M).val.app U).hom m =
      ((smallEtaleDirectImageIdIso B S hS X).inv.app
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj M)).hom.app U m :=
  congrArg (fun s : (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj M ⟶
      (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj
        ((modulePushforward B S hS (𝟙 X)).obj M) ↦ s.hom.app U m)
    (moduleSheafFunctor_map_modulePushforwardIdIso_inv_app B S hS X M)

/-! ### The transpose of the unit law for the inverse image -/

/-- The unit law `AlgebraicGeometry.Space.modulePullbackIdIso` of Stacks 03LU, exhibited as the
transport of the unit law for the direct image along the adjunction. -/
theorem modulePullbackIdIso_eq (X : AlgebraicSpaces B S hS) :
    modulePullbackIdIso B S hS X =
      Adjunction.leftAdjointIdIso (modulePullbackAdjunction B S hS (𝟙 X))
        (modulePushforwardIdIso B S hS X) :=
  rfl

/-- **The adjoint transpose of the unit law `(𝟙 X)^* ≅ 𝟭` of Stacks 03LU is the inverse of the
unit law `(𝟙 X)_* ≅ 𝟭`.** -/
theorem homEquiv_modulePullbackIdIso_hom_app (X : AlgebraicSpaces B S hS)
    (M : Modules.{u, u} B S hS X.1 X.2) :
    (modulePullbackAdjunction B S hS (𝟙 X)).homEquiv M M
        ((modulePullbackIdIso B S hS X).hom.app M) =
      (modulePushforwardIdIso B S hS X).inv.app M := by
  rw [modulePullbackIdIso_eq]
  exact Adjunction.homEquiv_leftAdjointIdIso_hom_app _ _ M

/-! ### The pushed-forward universal derivation at an identity -/

variable {X Y : AlgebraicSpaces B S hS}

/-- **The composite of Stacks 04CX at an identity square is the universal derivation followed by
the canonical identification of the direct image along an identity with the identity functor.** -/
theorem pushforwardUniversalDerivationHom_id_eq (p : X ⟶ Y) :
    pushforwardUniversalDerivationHom B S hS (𝟙 X) p =
      universalDerivationHom B S hS p ≫
        (smallEtaleDirectImageIdIso B S hS X).inv.app
          ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj
            (sheafOfDifferentials B S hS p)) :=
  (congrArg (fun m ↦ m ≫ (smallEtaleDirectImage B S hS (𝟙 X)).map
      (universalDerivationHom B S hS p)) (structureSharpSet_id B S hS X)).trans
    ((smallEtaleDirectImageIdIso B S hS X).inv.naturality
      (universalDerivationHom B S hS p)).symm

/-- The composite of Stacks 04CX at an identity square, read on a local section of `𝒪_X`: it is
the universal differential of that section, carried along the identification of the direct image
along an identity with the identity functor. -/
theorem pushforwardUniversalDerivationHom_id_app (p : X ⟶ Y)
    (U : (SmallEtale B S hS X.1)ᵒᵖ) (t : (structureRingSheaf B S hS X).obj.obj U) :
    (pushforwardUniversalDerivationHom B S hS (𝟙 X) p).hom.app U t =
      ((smallEtaleDirectImageIdIso B S hS X).inv.app
          ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj
            (sheafOfDifferentials B S hS p))).hom.app U
        ((universalDerivation B S hS p).d t) :=
  congrArg (fun m ↦ m.hom.app U t) (pushforwardUniversalDerivationHom_id_eq B S hS p)

/-! ### The comparison map at an identity square -/

/-- **The unit law of Stacks 03LU at `Ω_{X/Y}` is a comparison map of Stacks 04CX for the square
whose horizontal edges are the identity of `X`.** -/
theorem isSheafOfDifferentialsMap_modulePullbackIdIso (p : X ⟶ Y) :
    IsSheafOfDifferentialsMap B S hS (𝟙 X) p p
      ((modulePullbackIdIso B S hS X).hom.app (sheafOfDifferentials B S hS p)) := by
  intro U t
  rw [homEquiv_modulePullbackIdIso_hom_app, modulePushforwardIdIso_inv_app_val_app_apply]
  exact (pushforwardUniversalDerivationHom_id_app B S hS p U t).symm

/-- **The comparison map of Stacks 04CX at an identity square is an isomorphism.** -/
theorem isIso_of_isSheafOfDifferentialsMap_id (p : X ⟶ Y)
    {c : (modulePullback B S hS (𝟙 X)).obj (sheafOfDifferentials B S hS p) ⟶
      sheafOfDifferentials B S hS p}
    (hc : IsSheafOfDifferentialsMap B S hS (𝟙 X) p p c) : IsIso c := by
  rw [eq_of_isSheafOfDifferentialsMap B S hS (𝟙 X) p p hc
    (isSheafOfDifferentialsMap_modulePullbackIdIso B S hS p)]
  exact ((modulePullbackIdIso B S hS X).app (sheafOfDifferentials B S hS p)).isIso_hom

end AlgebraicGeometry.Space

end
