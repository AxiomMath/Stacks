module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.CategoryTheory.Filtered.Connected
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.PresheafPullback
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.RingedSite

/-!
# The associated-module functor of the big fppf site of a scheme

The inclusion of the small Zariski site of `S` into the big fppf category of schemes over `S` is
a continuous functor of sites, and the structure sheaves of the two sites are compared by the
isomorphism `Γ(U, 𝒪_U) ≅ Γ(S, U)` identifying the global functions of an open subscheme with the
sections of the structure sheaf of `S` over that open. Those two data are a morphism of
*ringed* sites `((Sch/S)_fppf, 𝒪) → (S_Zar, 𝒪_S)`, and its pullback on sheaves of modules is the
associated-module functor `𝒪_S`-modules → `𝒪`-modules on the big fppf site of `S`.

Its right adjoint is the pushforward, which is restriction along the inclusion; being a left
adjoint, the associated-module functor preserves all colimits.

## Main definitions

* `AlgebraicGeometry.BigFppfOver.structureMap`: the comparison of structure sheaves, the ring
  half of the morphism of ringed sites.
* `AlgebraicGeometry.BigFppfOver.associatedModule`: the pullback functor
  `S.Modules ⥤ SheafOfModules (structureSheaf B S hS)`.
* `AlgebraicGeometry.BigFppfOver.restrictModule`: its right adjoint, restriction along the
  inclusion of the small Zariski site.
* `AlgebraicGeometry.BigFppfOver.associatedModuleAdjunction`: the adjunction between them.
* `AlgebraicGeometry.BigFppfOver.associatedModuleUnitIso`: the associated module of `𝒪_S` is the
  structure sheaf of the big fppf site.
* `AlgebraicGeometry.BigFppfOver.associatedModuleFreeIso`: the associated module of a free module
  is free on the same index set.

## Main results

* `AlgebraicGeometry.Scheme.Opens.topIso_inv_appTop`: the identification
  `Γ(S, U) ≅ Γ(U, 𝒪_U)` is natural in `U`.
* `AlgebraicGeometry.BigFppfOver.preservesColimitsOfSize_associatedModule`: the
  associated-module functor preserves all colimits, being a left adjoint.

## References

* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03FH](https://stacks.math.columbia.edu/tag/03FH)
* [Stacks Project, Tag 03DC](https://stacks.math.columbia.edu/tag/03DC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- Restricting a section of the structure sheaf of `S` over `U` to the global functions of the
open subscheme `U` is natural in `U`. -/
public theorem Scheme.Opens.topIso_inv_appTop {X : Scheme.{u}} {U V : X.Opens} (h : V ≤ U) :
    (U.topIso).inv ≫ (X.homOfLE h).appTop
      = X.presheaf.map (homOfLE h).op ≫ (V.topIso).inv := by
  simp only [Scheme.Opens.topIso_inv, Scheme.homOfLE_appTop]
  exact ((X.presheaf.map_comp _ _).symm.trans
    (congrArg X.presheaf.map (Subsingleton.elim _ _))).trans (X.presheaf.map_comp _ _)

namespace BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The comparison of structure sheaves along the inclusion of the small Zariski site of `S`
into the big fppf category over `S`: over an open `U` it is the identification of the sections
of `𝒪_S` over `U` with the global functions of the open subscheme `U`. Together with the
continuity of the inclusion this is the morphism of ringed sites
`((Sch/S)_fppf, 𝒪) → (S_Zar, 𝒪_S)`. -/
public noncomputable def structureMap :
    S.ringCatSheaf ⟶ ((opensToBig B S hS).sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology ↥S) (topology B S hS)).obj (structureSheaf B S hS) where
  hom :=
    { app := fun U ↦ (CategoryTheory.forget₂ CommRingCat RingCat.{u}).map
        (Scheme.Opens.topIso U.unop).inv
      naturality := fun U V h ↦ by
        dsimp
        exact (((CategoryTheory.forget₂ CommRingCat RingCat.{u}).map_comp _ _).symm.trans
          ((congrArg _ (Scheme.Opens.topIso_inv_appTop (X := S) (leOfHom h.unop)).symm).trans
            ((CategoryTheory.forget₂ CommRingCat RingCat.{u}).map_comp _ _))) }

/-- Over an open `U` of `S`, `structureMap` is the inverse of `Scheme.Opens.topIso U`. -/
@[simp]
public theorem structureMap_hom_app (U : (S.Opens)ᵒᵖ) :
    (structureMap B S hS).hom.app U
      = (CategoryTheory.forget₂ CommRingCat RingCat.{u}).map
          (Scheme.Opens.topIso U.unop).inv := rfl

/-- Abelian presheaves on the big fppf category over `S` have a sheafification. -/
public instance hasWeakSheafify_topology :
    HasWeakSheafify (topology B S hS) AddCommGrpCat.{u} :=
  hasWeakSheafify B S hS .fppf

/-- Weak equivalences of abelian presheaves on the big fppf category over `S` are the locally
bijective maps. -/
public instance wEqualsLocallyBijective_topology :
    (topology B S hS).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  wEqualsLocallyBijective B S hS .fppf

/-- The pushforward of presheaves of modules along the structure-sheaf comparison has a left
adjoint. -/
public instance presheafPushforward_isRightAdjoint :
    (PresheafOfModules.pushforward.{u} (structureMap B S hS).hom).IsRightAdjoint :=
  Stacks.ModulePullback.isRightAdjoint_pushforward _

/-- The pushforward of sheaves of modules along the morphism of ringed sites has a left
adjoint. -/
public instance sheafPushforward_isRightAdjoint :
    (SheafOfModules.pushforward.{u} (structureMap B S hS)).IsRightAdjoint :=
  (SheafOfModules.PullbackConstruction.adjunction.{u} (structureMap B S hS)).isRightAdjoint

/-- The associated-module functor of the big fppf site of `S`: the pullback of sheaves of
modules along the morphism of ringed sites `((Sch/S)_fppf, 𝒪) → (S_Zar, 𝒪_S)`. -/
public noncomputable def associatedModule :
    S.Modules ⥤ SheafOfModules.{u} (structureSheaf B S hS) :=
  SheafOfModules.pullback.{u} (structureMap B S hS)

/-- Restriction of a sheaf of modules on the big fppf site of `S` along the inclusion of the
small Zariski site of `S`, the right adjoint of the associated-module functor. -/
public noncomputable def restrictModule :
    SheafOfModules.{u} (structureSheaf B S hS) ⥤ S.Modules :=
  SheafOfModules.pushforward.{u} (structureMap B S hS)

/-- The associated-module functor is left adjoint to restriction along the inclusion of the
small Zariski site. -/
public noncomputable def associatedModuleAdjunction :
    associatedModule B S hS ⊣ restrictModule B S hS :=
  SheafOfModules.pullbackPushforwardAdjunction.{u} (structureMap B S hS)

/-- The associated-module functor is a left adjoint. -/
public instance isLeftAdjoint_associatedModule : (associatedModule B S hS).IsLeftAdjoint :=
  (associatedModuleAdjunction B S hS).isLeftAdjoint

/-- The associated-module functor preserves all colimits. -/
public noncomputable instance preservesColimitsOfSize_associatedModule.{w, w'} :
    PreservesColimitsOfSize.{w, w'} (associatedModule B S hS) :=
  (associatedModuleAdjunction B S hS).leftAdjoint_preservesColimits


/-- The small Zariski site of `S` is a final subcategory of the big fppf category over `S`. -/
public instance final_opensToBig : (opensToBig B S hS).Final :=
  ⟨fun _ ↦ IsCofiltered.isConnected _⟩

/-- The comparison map from the pullback of the unit object along the morphism of ringed sites to
the unit object is an isomorphism. -/
public instance isIso_pullbackObjUnitToUnit :
    IsIso (SheafOfModules.pullbackObjUnitToUnit.{u} (structureMap B S hS)) :=
  SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal _

/-- The associated module of the structure sheaf of `S` is the structure sheaf of the big fppf
site. -/
public noncomputable def associatedModuleUnitIso :
    (associatedModule B S hS).obj (SheafOfModules.unit S.ringCatSheaf)
      ≅ SheafOfModules.unit (structureSheaf B S hS) :=
  @asIso _ _ _ _ (SheafOfModules.pullbackObjUnitToUnit.{u} (structureMap B S hS))
    (isIso_pullbackObjUnitToUnit B S hS)

/-- The associated module of a free module is free on the same index set. -/
public noncomputable def associatedModuleFreeIso (I : Type u) :
    (associatedModule B S hS).obj (SheafOfModules.free I)
      ≅ SheafOfModules.free I :=
  SheafOfModules.pullbackObjFreeIso.{u} (structureMap B S hS) I

end BigFppfOver

end AlgebraicGeometry

end
