module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.Defs

/-!
# Pseudofunctoriality of the module pullback, and transport along an isomorphism

`RingedSpaceModuleAdjunction.modulePullback` and `modulePushforward` are defined for one
morphism of ringed spaces at a time, as an abstract left adjoint and the sheaf-level
pushforward. This file records that the assignments are (pseudo)functorial in the morphism, and
draws the consequence that both are *equivalences* when the morphism is an isomorphism. It then
transports the ideal sheaf of `Stacks.ClosedImmersion.idealSheaf` along such an isomorphism.

The pushforward is functorial **on the nose**: `Mathlib`'s `SheafOfModules.pushforwardComp` and
`pushforwardId` are both `Iso.refl`, the composite `opensMap h ⋙ opensMap g` *is*
`opensMap (g ≫ h)`, and `structureSheafHom (g ≫ h)` *is* the composite of the two structure-sheaf
maps, all three by `rfl`. So
`modulePushforward a ⋙ modulePushforward b = modulePushforward (a ≫ b)` and
`modulePushforward (𝟙 X) = 𝟭` hold by `rfl`, and so does the factorization

`u (a ≫ b)♯ = u b♯ ≫ b_* (u a♯)`, where `u` abbreviates
`SheafOfModules.unitToPushforwardObjUnit`.

The pullback is functorial only up to isomorphism, through `SheafOfModules.pullbackComp` and
`SheafOfModules.pullbackId`.

## Main definitions

* `Stacks.RingedSpace.modulePushforwardComp`, `modulePushforwardId`, `modulePushforwardCongr` and
  `Stacks.RingedSpace.modulePullbackComp`, `modulePullbackId`, `modulePullbackCongr`:
  pseudofunctoriality of `f ↦ f_*` and of `f ↦ f^*` in the morphism of ringed spaces.
* `Stacks.RingedSpace.modulePushforwardEquivalence` and
  `Stacks.RingedSpace.modulePullbackEquivalence`: for an isomorphism `b` of ringed spaces, `b_*`
  and `b^*` are equivalences of the categories of module sheaves, with `(b⁻¹)_*` and `(b⁻¹)^*` as
  inverses.
* `Stacks.RingedSpace.pullbackPushforwardObjIso`: `b^* (b_* N) ≅ N` for an isomorphism `b`, the
  counit of `b^* ⊣ b_*`.
* `Stacks.ClosedImmersion.idealSheafPushforwardIso`: `ℐ_{a ≫ b} ≅ b_* ℐ_a` for an isomorphism `b`.
* `Stacks.ClosedImmersion.pullbackIdealSheafIso`: `(a ≫ b)^* ℐ_{a ≫ b} ≅ a^* ℐ_a` for an
  isomorphism `b`, i.e. the pullback of the ideal sheaf of a closed immersion does not change when
  the target is replaced by an isomorphic one.

## Main results

* `Stacks.RingedSpace.isEquivalence_modulePushforward` and `isEquivalence_modulePullback`.
* `Stacks.RingedSpace.isIso_unitToPushforwardObjUnit`: `𝒪_X ⟶ b_* 𝒪_W` is an isomorphism for an
  isomorphism `b : W ⟶ X` of ringed spaces.
* `AlgebraicGeometry.Scheme.Hom.isIso_toShHom`: an isomorphism of schemes is an isomorphism of the
  underlying ringed spaces.

## Implementation notes

The two equivalences are built with `CategoryTheory.Equivalence.mk`, which asks only for the two
isomorphisms `𝟭 ≅ F ⋙ G` and `G ⋙ F ≅ 𝟭` and repairs the triangle identity itself
(`Equivalence.adjointifyη`). The unit and counit of `b^* ⊣ b_*` are then isomorphisms by
`Adjunction.unit_isIso_of_L_fully_faithful` and `Adjunction.counit_isIso_of_R_fully_faithful`.

`modulePushforwardComp` and `modulePushforwardId` are `Iso.refl`, not equalities, so that the
pushforward and pullback sides read the same way; the underlying equalities do hold by `rfl` and
are used directly where that is shorter.

## References

* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096)
* [Stacks Project, Tag 01C2](https://stacks.math.columbia.edu/tag/01C2)
* [Stacks Project, Tag 01R2](https://stacks.math.columbia.edu/tag/01R2)
* [Stacks Project, Tag 0B3P](https://stacks.math.columbia.edu/tag/0B3P)
-/


@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingedSpaceModuleAdjunction
open TopologicalSpace

universe u

namespace Stacks.RingedSpace

variable {Z W X : RingedSpace.{u, u}} (a : Z ⟶ W) (b : W ⟶ X)

/-- **The pushforward of module sheaves is functorial in the morphism of ringed spaces**, on the
nose: `(a ≫ b)_* = b_* ∘ a_*`. -/
noncomputable def modulePushforwardComp :
    modulePushforward a ⋙ modulePushforward b ≅ modulePushforward (a ≫ b) :=
  Iso.refl _

variable (W) in
/-- The pushforward along an identity is the identity functor, on the nose. -/
noncomputable def modulePushforwardId : modulePushforward (𝟙 W) ≅ 𝟭 _ :=
  Iso.refl _

/-- Pushforwards along equal morphisms of ringed spaces are isomorphic. -/
noncomputable def modulePushforwardCongr {a a' : Z ⟶ W} (h : a = a') :
    modulePushforward a ≅ modulePushforward a' :=
  eqToIso (by rw [h])

/-- **The pushforward along an isomorphism of ringed spaces is an equivalence** of the categories
of module sheaves, with the pushforward along the inverse as its inverse. -/
noncomputable def modulePushforwardEquivalence [IsIso b] :
    SheafOfModules.{u} (structureSheafRing W) ≌ SheafOfModules.{u} (structureSheafRing X) :=
  CategoryTheory.Equivalence.mk (modulePushforward b) (modulePushforward (inv b))
    (modulePushforwardComp b (inv b) ≪≫ modulePushforwardCongr (IsIso.hom_inv_id b) ≪≫
      modulePushforwardId W).symm
    (modulePushforwardComp (inv b) b ≪≫ modulePushforwardCongr (IsIso.inv_hom_id b) ≪≫
      modulePushforwardId X)

/-- The pushforward of module sheaves along an isomorphism of ringed spaces is an equivalence. -/
instance isEquivalence_modulePushforward [IsIso b] : (modulePushforward b).IsEquivalence :=
  Functor.isEquivalence_of_iso
    (show (modulePushforwardEquivalence b).functor ≅ modulePushforward b from Iso.refl _)

/-- **Pseudofunctoriality of the module pullback**: `a^* ∘ b^* ≅ (a ≫ b)^*`. -/
noncomputable def modulePullbackComp :
    modulePullback b ⋙ modulePullback a ≅ modulePullback (a ≫ b) := by
  letI : (SheafOfModules.pushforward (structureSheafHom a)).IsRightAdjoint :=
    modulePushforward_isRightAdjoint a
  letI : (SheafOfModules.pushforward (structureSheafHom b)).IsRightAdjoint :=
    modulePushforward_isRightAdjoint b
  letI : (opensMap b ⋙ opensMap a).IsContinuous
      (Opens.grothendieckTopology X.carrier) (Opens.grothendieckTopology Z.carrier) :=
    opensMap_isContinuous (a ≫ b)
  exact SheafOfModules.pullbackComp (structureSheafHom b) (structureSheafHom a)

variable (W) in
/-- The pullback along an identity is the identity functor. -/
noncomputable def modulePullbackId : modulePullback (𝟙 W) ≅ 𝟭 _ := by
  letI : (SheafOfModules.pushforward (structureSheafHom (𝟙 W))).IsRightAdjoint :=
    modulePushforward_isRightAdjoint (𝟙 W)
  exact SheafOfModules.pullbackId (structureSheafRing W)

/-- Pullbacks along equal morphisms of ringed spaces are isomorphic. -/
noncomputable def modulePullbackCongr {a a' : Z ⟶ W} (h : a = a') :
    modulePullback a ≅ modulePullback a' :=
  eqToIso (by rw [h])

/-- **The pullback along an isomorphism of ringed spaces is an equivalence** of the categories of
module sheaves, with the pullback along the inverse as its inverse. -/
noncomputable def modulePullbackEquivalence [IsIso b] :
    SheafOfModules.{u} (structureSheafRing X) ≌ SheafOfModules.{u} (structureSheafRing W) :=
  CategoryTheory.Equivalence.mk (modulePullback b) (modulePullback (inv b))
    (modulePullbackComp (inv b) b ≪≫ modulePullbackCongr (IsIso.inv_hom_id b) ≪≫
      modulePullbackId X).symm
    (modulePullbackComp b (inv b) ≪≫ modulePullbackCongr (IsIso.hom_inv_id b) ≪≫
      modulePullbackId W)

/-- The pullback of module sheaves along an isomorphism of ringed spaces is an equivalence. -/
instance isEquivalence_modulePullback [IsIso b] : (modulePullback b).IsEquivalence :=
  Functor.isEquivalence_of_iso
    (show (modulePullbackEquivalence b).functor ≅ modulePullback b from Iso.refl _)

/-- **`b^* (b_* N) ≅ N` for an isomorphism `b` of ringed spaces**, given by the counit of
`b^* ⊣ b_*`. -/
noncomputable def pullbackPushforwardObjIso [IsIso b]
    (N : SheafOfModules.{u} (structureSheafRing W)) :
    (modulePullback b).obj ((modulePushforward b).obj N) ≅ N :=
  asIso ((modulePullbackPushforwardAdjunction b).counit.app N)

/-- **`𝒪_X ⟶ b_* 𝒪_W` is an isomorphism for an isomorphism `b : W ⟶ X` of ringed spaces.** -/
instance isIso_unitToPushforwardObjUnit [IsIso b] :
    IsIso (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom b)) := by
  let _ : (SheafOfModules.pushforward (structureSheafHom b)).IsRightAdjoint :=
    modulePushforward_isRightAdjoint b
  let _ : (Opens.map b.hom.base).Final := CategoryTheory.final_of_representablyFlat _
  let _ : (SheafOfModules.pullback (structureSheafHom b)).IsEquivalence :=
    isEquivalence_modulePullback b
  rw [← SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
    (structureSheafHom b), Adjunction.homEquiv_unit]
  infer_instance

end Stacks.RingedSpace

namespace AlgebraicGeometry.Scheme.Hom

/-- An isomorphism of schemes is an isomorphism of the underlying ringed spaces. -/
instance isIso_toShHom {P Q : Scheme.{u}} (f : P ⟶ Q) [IsIso f] : IsIso f.toLRSHom.toShHom :=
  ⟨(inv f).toLRSHom.toShHom, by
    rw [show f.toLRSHom.toShHom ≫ (inv f).toLRSHom.toShHom =
      (f ≫ inv f).toLRSHom.toShHom from rfl, IsIso.hom_inv_id]; rfl, by
    rw [show (inv f).toLRSHom.toShHom ≫ f.toLRSHom.toShHom =
      (inv f ≫ f).toLRSHom.toShHom from rfl, IsIso.inv_hom_id]; rfl⟩

end AlgebraicGeometry.Scheme.Hom

namespace Stacks.ClosedImmersion

open Stacks.RingedSpace

variable {Z W X : RingedSpace.{u, u}} (a : Z ⟶ W) (b : W ⟶ X)

/-- **The ideal sheaf of `a ≫ b` is the pushforward of the ideal sheaf of `a`**, when `b` is an
isomorphism of ringed spaces. -/
noncomputable def idealSheafPushforwardIso [IsIso b] :
    idealSheaf (a ≫ b) ≅ (modulePushforward b).obj (idealSheaf a) :=
  letI : (modulePushforward b).IsEquivalence := isEquivalence_modulePushforward b
  kernelIsIsoComp (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom b))
      ((modulePushforward b).map
        (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom a))) ≪≫
    (PreservesKernel.iso (modulePushforward b)
      (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom a))).symm

/-- **The pullback of the ideal sheaf of a closed immersion is unchanged by replacing the target
with an isomorphic one**: for `b` an isomorphism of ringed spaces,
`(a ≫ b)^* ℐ_{a ≫ b} ≅ a^* ℐ_a`. -/
noncomputable def pullbackIdealSheafIsoComp [IsIso b] :
    (modulePullback (a ≫ b)).obj (idealSheaf (a ≫ b)) ≅
      (modulePullback a).obj (idealSheaf a) :=
  (modulePullback (a ≫ b)).mapIso (idealSheafPushforwardIso a b) ≪≫
    (modulePullbackComp a b).symm.app ((modulePushforward b).obj (idealSheaf a)) ≪≫
    (modulePullback a).mapIso (pullbackPushforwardObjIso b (idealSheaf a))

/-- `pullbackIdealSheafIsoComp` for a morphism `c` presented as a composite: if `a ≫ b = c` with
`b` an isomorphism of ringed spaces, then `c^* ℐ_c ≅ a^* ℐ_a`. -/
noncomputable def pullbackIdealSheafIso [IsIso b] (c : Z ⟶ X) (hc : a ≫ b = c) :
    (modulePullback c).obj (idealSheaf c) ≅ (modulePullback a).obj (idealSheaf a) := by
  subst hc
  exact pullbackIdealSheafIsoComp a b

end Stacks.ClosedImmersion

end
