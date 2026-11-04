module

public import Mathlib.CategoryTheory.Sites.CoverLifting

/-!
# Sheafification commutes with pushforward compatibly with composition of site functors

`CategoryTheory.Functor.pushforwardContinuousSheafificationCompatibility` compares restricting a
presheaf along a continuous and cocontinuous site functor and then sheafifying with sheafifying
and then restricting. This module records the one coherence that comparison needs in order to be
usable in a *family* of site functors: for `F ⋙ G ≅ FG` the comparison for `FG` is the two
comparisons for `F` and `G` followed by
`CategoryTheory.Functor.sheafPushforwardContinuousComp'`.

## Main results

* `CategoryTheory.Functor.pushforwardContinuousSheafificationCompatibility_comp'`: the hexagon.

## Implementation notes

The comparison is a `CategoryTheory.Adjunction.leftAdjointUniq`, but it is not proved here by
uniqueness of left adjoints: Mathlib characterises it instead by what it does to the
sheafification unit,
`CategoryTheory.Functor.toSheafify_pullbackSheafificationCompatibility`, and both sides here are
morphisms out of a sheafification, so `CategoryTheory.sheafify_hom_ext` reduces the hexagon to
that characterisation applied three times. What is left after those three rewrites is the
naturality of the sheafification unit at the components of the comparison `eFG`, which is where
the `eFG.hom`/`eFG.inv` pair of the statement cancels.
-/

@[expose] public section

open CategoryTheory Opposite

namespace CategoryTheory.Functor

universe v u

variable {C₁ : Type*} [Category C₁] {C₂ : Type*} [Category C₂] {C₃ : Type*} [Category C₃]
  {F : C₁ ⥤ C₂} {G : C₂ ⥤ C₃} {FG : C₁ ⥤ C₃} (eFG : F ⋙ G ≅ FG)
  (A : Type u) [Category.{v} A]
  (J₁ : GrothendieckTopology C₁) (J₂ : GrothendieckTopology C₂) (J₃ : GrothendieckTopology C₃)
  [F.IsContinuous J₁ J₂] [F.IsCocontinuous J₁ J₂]
  [G.IsContinuous J₂ J₃] [G.IsCocontinuous J₂ J₃]
  [FG.IsContinuous J₁ J₃] [FG.IsCocontinuous J₁ J₃]
  [∀ P : C₁ᵒᵖ ⥤ A, F.op.HasPointwiseRightKanExtension P]
  [∀ P : C₂ᵒᵖ ⥤ A, G.op.HasPointwiseRightKanExtension P]
  [∀ P : C₁ᵒᵖ ⥤ A, FG.op.HasPointwiseRightKanExtension P]
  [HasWeakSheafify J₁ A] [HasWeakSheafify J₂ A] [HasWeakSheafify J₃ A]

/-- **The pushforward-sheafification comparison is compatible with composition of site
functors.** For continuous and cocontinuous `F`, `G` and `FG` with `eFG : F ⋙ G ≅ FG`, the
comparison for `FG` is the comparison for `F`, then the comparison for `G` restricted along `F`,
then `CategoryTheory.Functor.sheafPushforwardContinuousComp'`, the whole preceded by the
reindexing of the presheaf along `eFG`. -/
theorem pushforwardContinuousSheafificationCompatibility_comp' (P : C₃ᵒᵖ ⥤ A) :
    (FG.pushforwardContinuousSheafificationCompatibility A J₁ J₃).hom.app P =
      (presheafToSheaf J₁ A).map (Functor.whiskerRight (NatTrans.op eFG.hom) P) ≫
        (F.pushforwardContinuousSheafificationCompatibility A J₁ J₂).hom.app (G.op ⋙ P) ≫
          (F.sheafPushforwardContinuous A J₁ J₂).map
              ((G.pushforwardContinuousSheafificationCompatibility A J₂ J₃).hom.app P) ≫
            (sheafPushforwardContinuousComp' eFG A J₁ J₂ J₃).hom.app
              ((presheafToSheaf J₃ A).obj P) := by
  let : (F ⋙ G).IsContinuous J₁ J₃ := Functor.isContinuous_comp F G J₁ J₂ J₃
  refine Sheaf.hom_ext (sheafify_hom_ext J₁ _ _
    ((FG.sheafPushforwardContinuous A J₁ J₃).obj ((presheafToSheaf J₃ A).obj P)).property ?_)
  refine Eq.trans (FG.toSheafify_pullbackSheafificationCompatibility A J₁ J₃ P) ?_
  simp only [ObjectProperty.FullSubcategory.comp_hom,
    pushforwardContinuousSheafificationCompatibility_hom_app_hom]
  rw [← toSheafify_naturality_assoc]
  refine Eq.trans ?_ (whisker_eq _
    (toSheafify_sheafifyLift_assoc J₁
      (Functor.whiskerLeft F.op (toSheafify J₂ (G.op ⋙ P))) _ _)).symm
  have hcomp : ((sheafPushforwardContinuousComp' eFG A J₁ J₂ J₃).hom.app
        ((presheafToSheaf J₃ A).obj P)).hom =
      Functor.whiskerRight (NatTrans.op eFG.inv) (sheafify J₃ P) :=
    (Category.id_comp (((Functor.sheafPushforwardContinuousNatTrans eFG.inv A J₁ J₃).app
      ((presheafToSheaf J₃ A).obj P)).hom)).trans
      (Functor.sheafPushforwardContinuousNatTrans_app_hom eFG.inv A J₁ J₃
        ((presheafToSheaf J₃ A).obj P))
  have hmap : ((F.sheafPushforwardContinuous A J₁ J₂).map
        ((G.pushforwardContinuousSheafificationCompatibility A J₂ J₃).hom.app P)).hom =
      Functor.whiskerLeft F.op
        (sheafifyLift J₂ (Functor.whiskerLeft G.op (toSheafify J₃ P))
          ((presheafToSheaf J₃ A ⋙ G.sheafPushforwardContinuous A J₂ J₃).obj P).property) :=
    congrArg (Functor.whiskerLeft F.op)
      (G.pushforwardContinuousSheafificationCompatibility_hom_app_hom A J₂ J₃ P)
  rw [hcomp, hmap]
  have h1 : Functor.whiskerLeft F.op (toSheafify J₂ (G.op ⋙ P)) ≫
        Functor.whiskerLeft F.op
          (sheafifyLift J₂ (Functor.whiskerLeft G.op (toSheafify J₃ P))
            ((presheafToSheaf J₃ A ⋙ G.sheafPushforwardContinuous A J₂ J₃).obj P).property) =
      Functor.whiskerLeft F.op (Functor.whiskerLeft G.op (toSheafify J₃ P)) :=
    (Functor.whiskerLeft_comp F.op _ _).symm.trans
      (congrArg (Functor.whiskerLeft F.op)
        (toSheafify_sheafifyLift J₂ (Functor.whiskerLeft G.op (toSheafify J₃ P))
          ((presheafToSheaf J₃ A ⋙ G.sheafPushforwardContinuous A J₂ J₃).obj P).property))
  have h3 : Functor.whiskerRight (NatTrans.op eFG.hom) (sheafify J₃ P) ≫
        Functor.whiskerRight (NatTrans.op eFG.inv) (sheafify J₃ P) = 𝟙 _ := by
    rw [← Functor.whiskerRight_comp, ← NatTrans.op_comp, eFG.inv_hom_id, NatTrans.op_id,
      Functor.whiskerRight_id']
  show Functor.whiskerLeft FG.op (toSheafify J₃ P) =
    Functor.whiskerRight (NatTrans.op eFG.hom) P ≫
      Functor.whiskerLeft F.op (toSheafify J₂ (G.op ⋙ P)) ≫
        Functor.whiskerLeft F.op
          (sheafifyLift J₂ (Functor.whiskerLeft G.op (toSheafify J₃ P))
            ((presheafToSheaf J₃ A ⋙ G.sheafPushforwardContinuous A J₂ J₃).obj P).property) ≫
          Functor.whiskerRight (NatTrans.op eFG.inv) (sheafify J₃ P)
  have h4 : Functor.whiskerRight (NatTrans.op eFG.hom) P ≫
        Functor.whiskerLeft F.op (Functor.whiskerLeft G.op (toSheafify J₃ P)) =
      Functor.whiskerLeft FG.op (toSheafify J₃ P) ≫
        Functor.whiskerRight (NatTrans.op eFG.hom) (sheafify J₃ P) :=
    (Functor.whiskerLeft_comp_whiskerRight (NatTrans.op eFG.hom) (toSheafify J₃ P)).symm
  rw [← Category.assoc (Functor.whiskerLeft F.op (toSheafify J₂ (G.op ⋙ P))), h1,
    ← Category.assoc (Functor.whiskerRight (NatTrans.op eFG.hom) P), h4, Category.assoc, h3,
    Category.comp_id]


end CategoryTheory.Functor

end
