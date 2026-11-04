module

public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.AlgebraicGeometry.Pullbacks
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.IsoTransport
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.Module
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModuleFunctors

/-!
# Flatness over the base transfers along an isomorphism of modules

Flatness of an `𝒪_X`-module over the target of a morphism of ringed spaces is a property of
the stalks of the module, so it is invariant under an isomorphism of modules. For morphisms of
schemes it is also unchanged by composing the morphism with an isomorphism.

## Main definitions

* `AlgebraicGeometry.schemeModulePullbackCompIso`: the comparison isomorphism
  `g^* ∘ f^* ≅ (f ≫ g)^*` for the pullback of sheaves of modules along morphisms of schemes.

## Main results

* `AlgebraicGeometry.isFlatOver_of_moduleIso`: flatness over the target transfers along an
  isomorphism of modules.
* `AlgebraicGeometry.isFlatOver_comp_iso` and `AlgebraicGeometry.isFlatOver_comp_iso_iff`:
  flatness over the target is unchanged by composing the morphism with an isomorphism.
* `AlgebraicGeometry.isFlatOver_overPullback_map_iff`: for `X` over `T` and `b : U ⟶ T`, the
  base change of the structure morphism of `X` and the projection `X ×_T U ⟶ U` have the same
  flat modules, the two differing by the isomorphism `T ×_T U ≅ U`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry

/-- Flatness over the target transfers along an isomorphism of modules on a ringed space. -/
public lemma isFlatOver_of_moduleIso {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    {F G : SheafOfModules.{u} (structureSheafRing X)} (e : F ≅ G)
    (hF : IsFlatOver f F) : IsFlatOver f G :=
  fun x ↦ isFlatOverAt_of_moduleIso f e x (hF x)

/-- The comparison isomorphism between the pullback of sheaves of modules along a composite of
morphisms of schemes and the composite of the two pullbacks. -/
public noncomputable def schemeModulePullbackCompIso {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    RingedSpaceModuleAdjunction.modulePullback g.toLRSHom.toShHom ⋙
        RingedSpaceModuleAdjunction.modulePullback f.toLRSHom.toShHom ≅
      RingedSpaceModuleAdjunction.modulePullback (f ≫ g).toLRSHom.toShHom := by
  change (_root_.pullback g.toLRSHom.toShHom ⋙ _root_.pullback f.toLRSHom.toShHom) ≅
    _root_.pullback (f.toLRSHom.toShHom ≫ g.toLRSHom.toShHom)
  exact (_root_.pullbackComp f.toLRSHom.toShHom g.toLRSHom.toShHom).symm

/-! ### Flatness over a target composed with an isomorphism -/

/-- Flatness of a module over the target of a morphism of schemes is preserved by composing
that morphism with an isomorphism. -/
public theorem isFlatOver_comp_iso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (e : Y ≅ Z)
    (M : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    (hM : IsFlatOver f.toLRSHom.toShHom M) :
    IsFlatOver (f ≫ e.hom).toLRSHom.toShHom M := fun x ↦
  IsFlatOverAt.comp f.toLRSHom.toShHom e.hom.toLRSHom.toShHom M x (hM x)
    (Flat.stalkMap e.hom _)

/-- Flatness of a module over the target of a morphism of schemes is invariant under composing
that morphism with an isomorphism. -/
public theorem isFlatOver_comp_iso_iff {X Y Z : Scheme.{u}} (f : X ⟶ Y) (e : Y ≅ Z)
    (M : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) :
    IsFlatOver f.toLRSHom.toShHom M ↔ IsFlatOver (f ≫ e.hom).toLRSHom.toShHom M := by
  refine ⟨isFlatOver_comp_iso f e M, fun h ↦ ?_⟩
  simpa using isFlatOver_comp_iso (f ≫ e.hom) e.symm M h

/-- For a scheme `X` over `T` and a morphism `b : U ⟶ T`, a module on `X ×_T U` is flat over
`T ×_T U` along the base change of the structure morphism of `X` if and only if it is flat over
`U` along the second projection. -/
public theorem isFlatOver_overPullback_map_iff {T U : Scheme.{u}} (X : Over T) (b : U ⟶ T)
    (N : SheafOfModules.{u} (structureSheafRing (pullback X.hom b).toRingedSpace)) :
    IsFlatOver ((Over.pullback b).map
          (Over.homMk X.hom : X ⟶ Over.mk (𝟙 T))).left.toLRSHom.toShHom N ↔
      IsFlatOver (pullback.snd X.hom b).toLRSHom.toShHom N := by
  have hm : ((Over.pullback b).map (Over.homMk X.hom : X ⟶ Over.mk (𝟙 T))).left ≫
      (asIso (pullback.snd (𝟙 T) b)).hom = pullback.snd X.hom b := by
    dsimp only [Over.pullback, asIso_hom, Comma.mapLeft_obj_hom, Functor.id_obj,
      Over.map_obj_left, Over.map_obj_hom, Over.homMk_left]
    exact pullback.lift_snd _ _ _
  rw [isFlatOver_comp_iso_iff _ (asIso (pullback.snd (𝟙 T) b)) N, hm]

end AlgebraicGeometry
