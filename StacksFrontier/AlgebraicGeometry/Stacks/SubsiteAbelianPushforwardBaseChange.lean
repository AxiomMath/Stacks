module

public import StacksFrontier.AlgebraicGeometry.Stacks.SubsiteSheafPushforwardBaseChange
public import StacksFrontier.CategoryTheory.Functor.KanExtension.RanBaseChangeUnderlyingSets
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsiteDerivedPushforwardBaseChange

/-!
# The base change of right Kan extensions of Stacks 07AT at abelian sheaves

Let `f : 𝒳 ⟶ 𝒴` be a smooth (respectively flat) 1-morphism of algebraic stacks, `f'` its
restriction to the lisse-étale (respectively flat-fppf) sites, and `g`, `g'` the inclusions of
**Stacks 0788**. The canonical map `g^{-1}f_* ⟶ f'_*(g')^{-1}` of Sites, Section 06UM is the base
change of right Kan extensions of the commuting square of `f`, `f'` and the two inclusions. The
right Kan extensions involved exist for abelian presheaves, and the base change is invertible at
every abelian presheaf on `𝒳` which is a sheaf.

## Main results

* `AlgebraicGeometry.Stack.LisseEtale.hasPointwiseRightKanExtension_subsiteFunctor_ab`,
  `AlgebraicGeometry.Stack.LisseEtale.hasPointwiseRightKanExtension_homFunctor_ab` and their
  flat-fppf versions: the right Kan extensions exist for abelian presheaves.
* `AlgebraicGeometry.Stack.LisseEtale.isIso_ranBaseChange_app_of_isSheaf` and
  `AlgebraicGeometry.Stack.FlatFppf.isIso_ranBaseChange_app_of_isSheaf`: the base change is
  invertible at every abelian sheaf.

## References

* [Stacks Project, Tag 06UM](https://stacks.math.columbia.edu/tag/06UM)
* [Stacks Project, Tag 07AT](https://stacks.math.columbia.edu/tag/07AT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)

attribute [local instance] hasPointwiseRightKanExtension_homFunctor

namespace LisseEtale

attribute [local instance] hasPointwiseRightKanExtension_inclusion_comp_homFunctor
  hasPointwiseRightKanExtension_primedSiteFunctor

variable (hf : AlgebraicStacks.IsSmooth B S hS f)

/-- Restriction of abelian presheaves along the site functor of **Stacks 07AT** (1) admits a
pointwise right Kan extension. -/
theorem hasPointwiseRightKanExtension_subsiteFunctor_ab :
    ∀ G : (LisseEtale.{u, w} B S hS 𝒳)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor (smoothObject.{u, w} B S hS 𝒳)
        (smoothObject_map.{u, w} B S hS f hf)).op.HasPointwiseRightKanExtension G :=
  fun _ Y => by
  have := hasLimitsOfShape_of_essentiallySmall.{u + 1}
    (StructuredArrow Y (SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor
      (smoothObject.{u, w} B S hS 𝒳) (smoothObject_map.{u, w} B S hS f hf)).op)
    AddCommGrpCat.{u + 1}
  infer_instance

/-- Restriction of abelian presheaves along the underlying functor of a 1-morphism of algebraic
stacks admits a pointwise right Kan extension. -/
theorem hasPointwiseRightKanExtension_homFunctor_ab :
    ∀ G : (𝒳.val.val.obj)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      f.hom.hom.toFunctor.op.HasPointwiseRightKanExtension G := fun _ Y => by
  have := hasLimitsOfShape_of_essentiallySmall.{u + 1}
    (StructuredArrow Y f.hom.hom.toFunctor.op) AddCommGrpCat.{u + 1}
  infer_instance

attribute [local instance] hasPointwiseRightKanExtension_subsiteFunctor_ab
  hasPointwiseRightKanExtension_homFunctor_ab

/-- The base change of right Kan extensions of the square of `f`, its restriction `f'` and the
two inclusions is invertible at every abelian presheaf on `𝒳` which is a sheaf. -/
theorem isIso_ranBaseChange_app_of_isSheaf (G : (𝒳.val.val.obj)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (hG : Presheaf.IsSheaf (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .etale) G) :
    IsIso ((SubsitePushforward.subsiteRanSquare f.hom.hom.toFunctor (smoothObject.{u, w} B S hS 𝒳)
      (smoothObject_map.{u, w} B S hS f hf)).ranBaseChange.app G) := by
  have hG' : Presieve.IsSheaf (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .etale)
      (G ⋙ forget AddCommGrpCat.{u + 1}) :=
    (isSheaf_iff_isSheaf_of_type _ _).mp
      ((Presheaf.isSheaf_iff_isSheaf_forget _ G (forget AddCommGrpCat.{u + 1})).mp hG)
  refine (NatTrans.isIso_iff_isIso_app _).2 fun z => (ConcreteCategory.isIso_iff_bijective _).2 ?_
  exact (Stacks.SheafOfModules.bijective_ranBaseChange_app_app_forget_iff _ G z).2
    (bijective_subsiteRanBaseChange B S hS f hf (G ⋙ forget AddCommGrpCat.{u + 1}) hG' z.unop)

end LisseEtale

namespace FlatFppf

attribute [local instance] hasPointwiseRightKanExtension_inclusion_comp_homFunctor
  hasPointwiseRightKanExtension_primedSiteFunctor

variable (hf : AlgebraicStacks.IsFlat B S hS f)

/-- Restriction of abelian presheaves along the site functor of **Stacks 07AT** (2) admits a
pointwise right Kan extension. -/
theorem hasPointwiseRightKanExtension_subsiteFunctor_ab :
    ∀ G : (FlatFppf B S hS 𝒳)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor (objectProperty B S hS 𝒳)
        (flatObject_map B S hS f hf)).op.HasPointwiseRightKanExtension G :=
  fun _ Y => by
  have := hasLimitsOfShape_of_essentiallySmall.{u + 1}
    (StructuredArrow Y (SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor
      (objectProperty B S hS 𝒳) (flatObject_map B S hS f hf)).op)
    AddCommGrpCat.{u + 1}
  infer_instance

/-- Restriction of abelian presheaves along the underlying functor of a 1-morphism of algebraic
stacks admits a pointwise right Kan extension. -/
alias hasPointwiseRightKanExtension_homFunctor_ab :=
  LisseEtale.hasPointwiseRightKanExtension_homFunctor_ab

attribute [local instance] hasPointwiseRightKanExtension_subsiteFunctor_ab
  hasPointwiseRightKanExtension_homFunctor_ab

/-- The base change of right Kan extensions of the square of `f`, its restriction `f'` and the
two inclusions is invertible at every abelian presheaf on `𝒳` which is a sheaf. -/
theorem isIso_ranBaseChange_app_of_isSheaf (G : (𝒳.val.val.obj)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (hG : Presheaf.IsSheaf (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf) G) :
    IsIso ((SubsitePushforward.subsiteRanSquare f.hom.hom.toFunctor (objectProperty B S hS 𝒳)
      (flatObject_map B S hS f hf)).ranBaseChange.app G) := by
  have hG' : Presieve.IsSheaf (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf)
      (G ⋙ forget AddCommGrpCat.{u + 1}) :=
    (isSheaf_iff_isSheaf_of_type _ _).mp
      ((Presheaf.isSheaf_iff_isSheaf_forget _ G (forget AddCommGrpCat.{u + 1})).mp hG)
  refine (NatTrans.isIso_iff_isIso_app _).2 fun z => (ConcreteCategory.isIso_iff_bijective _).2 ?_
  exact (Stacks.SheafOfModules.bijective_ranBaseChange_app_app_forget_iff _ G z).2
    (bijective_subsiteRanBaseChange B S hS f hf (G ⋙ forget AddCommGrpCat.{u + 1}) hG' z.unop)

end FlatFppf

end AlgebraicGeometry.Stack
