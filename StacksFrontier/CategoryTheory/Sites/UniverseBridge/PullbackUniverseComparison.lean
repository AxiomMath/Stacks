module

public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Sites.Limits

/-!
# Changing the value universe of sheaf pullback

For a continuous functor between small sites, sheaf pullback commutes with lifting
the values of a small-valued sheaf. This uses preservation of left Kan extensions
and sheafification by `ULift`; no left exactness of the presheaf Kan extension is needed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace Stacks.Sites.UniverseBridge

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)

/-- Lifting the values of sheaves preserves finite limits. -/
theorem preservesFiniteLimits_sheafCompose_ulift :
    PreservesFiniteLimits (sheafCompose J uliftFunctor.{v, u}) := by
  refine ⟨fun A _ _ => ?_⟩
  let V := sheafToPresheaf J (Type (max u v))
  have : PreservesLimitsOfShape A (sheafCompose J uliftFunctor.{v, u} ⋙ V) :=
    inferInstanceAs (PreservesLimitsOfShape A
      (sheafToPresheaf J (Type u) ⋙
        (Functor.whiskeringRight _ _ _).obj uliftFunctor.{v, u}))
  exact preservesLimitsOfShape_of_reflects_of_preserves _ V

variable (F : C ⥤ D) [F.IsContinuous J K]

/-- The explicit Kan-extension construction of sheaf pullback commutes with value lifting. -/
def constructedSheafPullbackUliftIso :
    sheafCompose J uliftFunctor.{v, u} ⋙
        Functor.sheafPullbackConstruction.sheafPullback F (Type (max u v)) J K ≅
      Functor.sheafPullbackConstruction.sheafPullback F (Type u) J K ⋙
        sheafCompose K uliftFunctor.{v, u} := by
  let eLan := uliftFunctor.{v, u}.lanCompIsoOfPreserves F.op
  let eSheaf := sheafComposeNatIso K uliftFunctor.{v, u}
    (sheafificationAdjunction K (Type u))
    (sheafificationAdjunction K (Type (max u v)))
  exact Functor.isoWhiskerLeft (sheafToPresheaf J (Type u))
    (Functor.isoWhiskerRight eLan.symm (presheafToSheaf K (Type (max u v))) ≪≫
      Functor.isoWhiskerLeft (F.op.lan : (Cᵒᵖ ⥤ Type u) ⥤ Dᵒᵖ ⥤ Type u) eSheaf)

/-- The chosen sheaf pullback commutes with lifting the values of a small-valued sheaf. -/
def sheafPullbackUliftIso :
    sheafCompose J uliftFunctor.{v, u} ⋙ F.sheafPullback (Type (max u v)) J K ≅
      F.sheafPullback (Type u) J K ⋙ sheafCompose K uliftFunctor.{v, u} :=
  Functor.isoWhiskerLeft (sheafCompose J uliftFunctor.{v, u})
      (Functor.sheafPullbackConstruction.sheafPullbackIso F (Type (max u v)) J K) ≪≫
    constructedSheafPullbackUliftIso J K F ≪≫
    Functor.isoWhiskerRight
      (Functor.sheafPullbackConstruction.sheafPullbackIso F (Type u) J K).symm
      (sheafCompose K uliftFunctor.{v, u})

end Stacks.Sites.UniverseBridge

end
