module

public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
public import StacksFrontier.CategoryTheory.Sites.UniverseBridge.LimitsOfColimitPresentations
import StacksCore.Tactic.EgaSgaAttribute

/-! # Filtered colimits and finite limits of sheaves -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Sites.UniverseBridge

/-- Colimits in a reflective subcategory can be computed by reflecting colimits in the
ambient category. This is stated as an isomorphism of functors. -/
def reflectiveColimitIso
    {A B I : Type*} [Category* A] [Category* B] [Category* I]
    [HasColimitsOfShape I A] [HasColimitsOfShape I B]
    (L : A ⥤ B) (R : B ⥤ A) (adj : L ⊣ R) [R.Full] [R.Faithful] :
    (Functor.whiskeringRight I B A).obj R ⋙ colim ⋙ L ≅
      (colim : (I ⥤ B) ⥤ B) := by
  letI : L.IsLeftAdjoint := adj.isLeftAdjoint
  let eRL : R ⋙ L ≅ 𝟭 B := asIso adj.counit
  let e : (Functor.whiskeringRight I B A).obj R ⋙
      (Functor.whiskeringRight I A B).obj L ≅ 𝟭 (I ⥤ B) :=
    NatIso.ofComponents (fun E ↦ Functor.isoWhiskerLeft E eRL ≪≫ Functor.rightUnitor E)
      (fun _ ↦ by ext; simp [eRL])
  exact Functor.isoWhiskerLeft ((Functor.whiskeringRight I B A).obj R)
      (preservesColimitNatIso L) ≪≫
    Functor.isoWhiskerRight e colim ≪≫ Functor.leftUnitor colim

/-- An exact reflection preserves commutation of colimits with finite limits. -/
theorem preservesFiniteLimits_colim_of_reflective
    {A B I : Type*} [Category* A] [Category* B] [Category* I]
    [HasFiniteLimits A] [HasFiniteLimits B]
    [HasColimitsOfShape I A] [HasColimitsOfShape I B]
    (L : A ⥤ B) (R : B ⥤ A) (adj : L ⊣ R) [R.Full] [R.Faithful]
    [PreservesFiniteLimits L] [PreservesFiniteLimits R]
    [PreservesFiniteLimits (colim : (I ⥤ A) ⥤ A)] :
    PreservesFiniteLimits (colim : (I ⥤ B) ⥤ B) := by
  have : PreservesFiniteLimits ((Functor.whiskeringRight I B A).obj R) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  have : PreservesFiniteLimits ((colim : (I ⥤ A) ⥤ A) ⋙ L) :=
    comp_preservesFiniteLimits _ _
  have : PreservesFiniteLimits ((Functor.whiskeringRight I B A).obj R ⋙ colim ⋙ L) :=
    comp_preservesFiniteLimits _ _
  exact preservesFiniteLimits_of_natIso (reflectiveColimitIso L R adj)

universe v u

/-- Filtered colimits of sheaves of sets commute with finite limits on a small site. -/
@[sga "4 I 2.8" "more general", sga "4 II 4.3" "clause 4 for small sites"]
theorem preservesFiniteLimits_sheaf_colim
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (I : Type (max u v)) [SmallCategory I] [IsFiltered I] :
    PreservesFiniteLimits (colim : (I ⥤ Sheaf J (Type (max u v))) ⥤ _) := by
  have : PreservesFiniteLimits (colim : (I ⥤ Cᵒᵖ ⥤ Type (max u v)) ⥤ _) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  exact preservesFiniteLimits_colim_of_reflective
    (presheafToSheaf J (Type (max u v))) (sheafToPresheaf J (Type (max u v)))
    (sheafificationAdjunction J (Type (max u v)))

end Stacks.Sites.UniverseBridge

end
