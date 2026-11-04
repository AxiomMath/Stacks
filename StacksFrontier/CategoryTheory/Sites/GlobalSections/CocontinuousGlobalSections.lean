module

public import Mathlib.CategoryTheory.Sites.CoverLifting
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.RestrictionOfGlobalSections

/-!
# Global sections along the direct image for a cocontinuous functor of sites

Let `G : C ⥤ D` be a cocontinuous functor of sites, [Stacks, Tag 00XI], and let `A` be a category
of coefficients with limits of shape `Cᵒᵖ` and of shape `Dᵒᵖ`.  The direct image
`CategoryTheory.Functor.sheafPushforwardCocontinuous` loses no global section:

`Γ(D, G_*ℱ) ≅ Γ(C, ℱ)`.

Both sides are limits of the underlying presheaf, `CategoryTheory.Sheaf.ΓNatIsoLim`; the presheaf
underlying `G_*ℱ` is the right Kan extension of that of `ℱ` along `G.op`, [Stacks, Tag 00XK]; and
the limit of a right Kan extension is the limit of the functor extended,
`CategoryTheory.Functor.ranCompLimIso`.

## Main definitions

* `Stacks.Sites.cocontinuousGlobalSectionsIso` — the isomorphism above.

## Main results

* `Stacks.Sites.cocontinuousGlobalSectionsIso_hom_app_comp_ΓRes` — its evaluation against the
  restriction maps `CategoryTheory.Sheaf.ΓRes` out of global sections: restricting a global
  section of `ℱ` to an object `X` of `C` is restricting the corresponding global section of
  `G_*ℱ` to `G.obj X` and then applying the counit of the Kan extension.  Since
  `CategoryTheory.Sheaf.isLimitConeΓ` exhibits global sections as a limit whose legs are the
  restriction maps, this determines the isomorphism completely, and it is the form in which a
  coherence square of such comparisons is checked.

## Implementation notes

The two sides of the evaluation are composable only up to definitional unfolding of
`CategoryTheory.Functor.sheafPushforwardCocontinuous`, so the statement is not type-correct at
the `implicit` transparency level that `rw` and `simp` use for their motives.  The proof is
therefore a term-mode chain of `Eq.trans` and `congrArg`, which elaborates at default
transparency; the tactic steps are confined to subgoals living over a single site.

## References

* [Stacks Project, Tag 00XI](https://stacks.math.columbia.edu/tag/00XI)
* [Stacks Project, Tag 00XK](https://stacks.math.columbia.edu/tag/00XK)
-/

@[expose] public section

universe v₁ v₂ v u₁ u₂ u

open CategoryTheory Limits Opposite

namespace Stacks.Sites

noncomputable section

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (G : C ⥤ D)
  (A : Type u) [Category.{v} A] (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [G.IsCocontinuous J K] [∀ (P : Cᵒᵖ ⥤ A), G.op.HasPointwiseRightKanExtension P]
  [HasWeakSheafify J A] [HasWeakSheafify K A] [HasLimitsOfShape Cᵒᵖ A] [HasLimitsOfShape Dᵒᵖ A]

/-- **`Γ(D, G_*ℱ) ≅ Γ(C, ℱ)`** for a cocontinuous functor of sites `G : C ⥤ D`: taking global
sections after the direct image loses nothing.

Both sides are limits of the underlying presheaf, `CategoryTheory.Sheaf.ΓNatIsoLim`, and the
presheaf underlying `G_*ℱ` is the right Kan extension of that of `ℱ` along `G.op`,
[Stacks, Tag 00XK], whose limit is the limit of the functor extended by
`CategoryTheory.Functor.ranCompLimIso`. -/
def cocontinuousGlobalSectionsIso :
    G.sheafPushforwardCocontinuous A J K ⋙ Sheaf.Γ K A ≅ Sheaf.Γ J A :=
  Functor.isoWhiskerLeft (G.sheafPushforwardCocontinuous A J K) (Sheaf.ΓNatIsoLim K A) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (G.sheafPushforwardCocontinuousCompSheafToPresheafIso A J K) lim ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (sheafToPresheaf J A) (Functor.ranCompLimIso (H := A) G.op) ≪≫
    (Sheaf.ΓNatIsoLim J A).symm

variable {G A J K}

/-- **The comparison `Γ(D, G_*ℱ) ≅ Γ(C, ℱ)` read against the restriction maps.**  Composed with
the restriction of global sections of `ℱ` to an object `X` of `C`, the isomorphism
`cocontinuousGlobalSectionsIso` is the restriction of global sections of `G_*ℱ` to `G.obj X`
followed by the counit of the right Kan extension at `X`.

This pins the comparison down: `CategoryTheory.Sheaf.isLimitConeΓ` exhibits `Γ(C, ℱ)` as a limit
whose legs are the restriction maps, so a morphism into it is determined by its composites with
them. -/
theorem cocontinuousGlobalSectionsIso_hom_app_comp_ΓRes (F : Sheaf J A) (X : C) :
    (cocontinuousGlobalSectionsIso G A J K).hom.app F ≫ Sheaf.ΓRes F (op X) =
      Sheaf.ΓRes ((G.sheafPushforwardCocontinuous A J K).obj F) (op (G.obj X)) ≫
        (G.op.ranCounit.app F.obj).app (op X) := by
  have key : (Sheaf.ΓNatIsoLim J A).inv.app F ≫ Sheaf.ΓRes F (op X) =
      limit.π F.obj (op X) := by
    rw [← Sheaf.ΓNatIsoLim_hom_app_comp_π F (op X), ← Category.assoc, Iso.inv_hom_id_app,
      Category.id_comp]
  have hπ : (Functor.whiskerRight
        (𝟙 (G.sheafPushforwardCocontinuous A J K ⋙ sheafToPresheaf K A)) lim).app F ≫
      limit.π (G.op.ran.obj F.obj) (op (G.obj X)) =
        limit.π ((G.sheafPushforwardCocontinuous A J K).obj F).obj (op (G.obj X)) :=
    (limMap_π (𝟙 ((G.sheafPushforwardCocontinuous A J K).obj F).obj) (op (G.obj X))).trans
      (Category.comp_id _)
  simp only [Functor.comp_obj, cocontinuousGlobalSectionsIso, Iso.trans_hom,
    Functor.isoWhiskerLeft_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    Functor.sheafPushforwardCocontinuousCompSheafToPresheafIso_hom, NatTrans.comp_app,
    ObjectProperty.ι_obj, lim_obj, Functor.whiskerLeft_app, Functor.associator_inv_app,
    Functor.associator_hom_app, Functor.ranCompLimIso_hom_app, Category.id_comp, Category.assoc,
    key, Functor.limitIsoOfIsRightKanExtension_hom_π, Functor.op_obj, Functor.id_obj,
    Functor.whiskeringLeft_obj_obj]
  exact (congrArg (fun z ↦ (Sheaf.ΓNatIsoLim K A).hom.app
        ((G.sheafPushforwardCocontinuous A J K).obj F) ≫ z)
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun z ↦ z ≫ (G.op.ranCounit.app F.obj).app (op X)) hπ))).trans
    ((Category.assoc _ _ _).symm.trans
      (congrArg (fun z ↦ z ≫ (G.op.ranCounit.app F.obj).app (op X))
        (Sheaf.ΓNatIsoLim_hom_app_comp_π ((G.sheafPushforwardCocontinuous A J K).obj F)
          (op (G.obj X)))))

end

end Stacks.Sites

end
