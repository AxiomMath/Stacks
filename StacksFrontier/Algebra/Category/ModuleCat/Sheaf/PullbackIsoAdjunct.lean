module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import StacksFrontier.CategoryTheory.Adjunction.LeftAdjointUniqTranspose

/-!
# Transposing across the two adjunctions `SheafOfModules.pullbackIso` compares

`SheafOfModules.pullbackIso` identifies the pullback of *sheaves* of modules along a morphism
`φ` of sheaves of rings with the sheafification of the pullback of *presheaves* of modules along
`φ.hom`. Both are left adjoint to the same pushforward, and the isomorphism is
`CategoryTheory.Adjunction.leftAdjointUniq` of the two adjunctions.

This file computes what the isomorphism does to a *transpose*. A morphism out of the pullback of
sheaves of modules can be transposed across the sheaf-level adjunction, or pushed through the
isomorphism and transposed across the presheaf-level adjunction followed by the sheafification
adjunction; the two answers agree.

## Main results

* `SheafOfModules.homEquiv_sheafificationAdjunction_unit_comp_pullbackIso_inv_app`: **the
  transpose across the presheaf-level adjunction of the sheafification unit followed by
  `SheafOfModules.pullbackIso` is the transpose across the sheaf-level adjunction.**
-/

@[expose] public section

open CategoryTheory Opposite

universe v v₁ v₂ u₁ u₂

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  {S : Sheaf J RingCat.{v}} {R : Sheaf K RingCat.{v}} [F.IsContinuous J K]
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{v} J K).obj R)
  [(PresheafOfModules.pushforward.{v} φ.hom).IsRightAdjoint]
  [(SheafOfModules.pushforward.{v} φ).IsRightAdjoint]
  [HasWeakSheafify K AddCommGrpCat.{v}] [K.WEqualsLocallyBijective AddCommGrpCat.{v}]

omit [(pushforward φ).IsRightAdjoint] in
/-- **The transpose across `SheafOfModules.PullbackConstruction.adjunction`, read on underlying
presheaves of modules.** It is the transpose across the sheafification adjunction followed by the
transpose across the presheaf-level pullback--pushforward adjunction. -/
public theorem forget_map_homEquiv_pullbackConstruction_adjunction (X : SheafOfModules.{v} S)
    (G : SheafOfModules.{v} R)
    (g : (PresheafOfModules.sheafification (𝟙 R.obj)).obj
      ((PresheafOfModules.pullback.{v} φ.hom).obj X.val) ⟶ G) :
    (SheafOfModules.forget S).map
        ((SheafOfModules.PullbackConstruction.adjunction.{v} φ).homEquiv X G g) =
      (PresheafOfModules.pullbackPushforwardAdjunction.{v} φ.hom).homEquiv X.val _
        ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv _ _ g) :=
  rfl

/-- **The passage between the adjunction of sheaves of modules along `φ` and the adjunction of
presheaves of modules along `φ.hom` followed by sheafification.** Let `ν` be a morphism out of the
pullback of sheaves of modules of `X`. Composing `SheafOfModules.pullbackIso` with `ν`, prefixing
the unit of the sheafification adjunction and transposing across the presheaf-level
pullback--pushforward adjunction gives the transpose of `ν` across the sheaf-level
pullback--pushforward adjunction, read on underlying presheaves of modules. -/
public theorem homEquiv_sheafificationAdjunction_unit_comp_pullbackIso_inv_app
    (X : SheafOfModules.{v} S) (G : SheafOfModules.{v} R)
    (ν : (SheafOfModules.pullback.{v} φ).obj X ⟶ G) :
    (PresheafOfModules.pullbackPushforwardAdjunction.{v} φ.hom).homEquiv X.val _
        ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app
            ((PresheafOfModules.pullback.{v} φ.hom).obj X.val) ≫
          (SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)).map
            ((SheafOfModules.pullbackIso.{v} φ).inv.app X ≫ ν)) =
      (SheafOfModules.forget S).map
        ((SheafOfModules.pullbackPushforwardAdjunction.{v} φ).homEquiv X G ν) := by
  rw [← Adjunction.homEquiv_unit,
    ← forget_map_homEquiv_pullbackConstruction_adjunction φ X G]
  exact congrArg (SheafOfModules.forget S).map
    (Adjunction.homEquiv_leftAdjointUniq_inv_app_comp _ _ X ν)

end SheafOfModules

end
