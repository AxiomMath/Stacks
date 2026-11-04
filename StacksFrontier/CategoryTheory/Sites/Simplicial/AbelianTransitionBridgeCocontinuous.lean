module

public import StacksFrontier.CategoryTheory.Sites.AbelianInverseImageForget
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AbelianTransitionBridge
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentSumFormulaLegCocontinuous

/-!
# The inverse image of Stacks 09WG is the transition of Stacks 07TF

The transition along a simplex map has two descriptions: the transformation
`CategoryTheory.SimplicialSiteSituation.abelianTransitionOfFiber` into the restriction functor
`g_n^{-1}`, whose underlying map of sheaves of sets is the transition of Stacks 09WF, and the
transformation `CategoryTheory.SimplicialSiteSituation.fiberTransitionAb` out of the chosen
inverse image `transitionInverseImageAb` that is the summand of the sum formula of Stacks 09WG.
They are the same map, read through the comparison
`CategoryTheory.SimplicialSiteSituation.transitionInverseImageAbIso` of the two inverse images.
This file proves this in case (B) of Stacks 09WE, and in general by combining it with case (A),
`CategoryTheory.SimplicialSite.fiberTransitionAb_eq`.

## Main results

* `whiskerRight_toSheafify_comp_cocontinuousAbelianInverseImageIso_inv_app`, in the namespace
  `Stacks.Sites.AbelianPullback`: on underlying presheaves of sets, the sheafification unit of an
  abelian presheaf followed by the inverse of the comparison of the two descriptions of the
  pullback of abelian sheaves along a cocontinuous functor is the sheafification unit of the
  underlying presheaf of sets.
* `CategoryTheory.CocontinuousSimplicialSite.toSheafify_comp_fiberTransition_inr_app`: in case
  (B), the sheafification unit followed by the transition of Stacks 09WF is the family of
  restrictions along the cross-fibre arrows.
* `CategoryTheory.CocontinuousSimplicialSite.fiberTransitionAb_eq`: in case (B), the summand
  transformation of the sum formula is the transition of Stacks 07TF transported along the
  comparison of inverse images.
* `CategoryTheory.SimplicialSiteSituation.fiberTransitionAb_eq`: the same statement for an
  arbitrary simplicial-site situation.

The primed versions state the same results with `restrictAb` in place of `abelianComponent`.

## Implementation notes

Instances for the component topologies of a concrete constructor application `⟨Sum.inr C⟩` are
passed to the generic lemmas by name, in an application written with `@`: synthesis fails for
them during the elaboration of such an application, even with the instance in the local context.

## References

* [Stacks Project, Tag 07TF](https://stacks.math.columbia.edu/tag/07TF)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 09WF](https://stacks.math.columbia.edu/tag/09WF)
* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
* [Stacks Project, Tag 00XL](https://stacks.math.columbia.edu/tag/00XL)
* [Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open CategoryTheory.Sites CategoryTheory.Sites.AbelianSheaf Opposite
open CategoryTheory.SimplicialSiteSituation

universe u

namespace Stacks.Sites.AbelianPullback

variable {C : Type u} [Category.{u} C] {D : Type u} [Category.{u} D]

/-- **The comparison of the two descriptions of the pullback of abelian sheaves along a
cocontinuous functor is the identity on sheafification units.**  On underlying presheaves of sets
the sheafification unit of the restricted abelian presheaf, followed by the inverse of the
comparison, is the sheafification unit of the restricted presheaf of sets. -/
theorem whiskerRight_toSheafify_comp_cocontinuousAbelianInverseImageIso_inv_app
    (F : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [HasSheafify J (Type u)] [HasWeakSheafify J Ab.{u}] (X : Sheaf K Ab.{u}) :
    Functor.whiskerRight (toSheafify J (F.op ⋙ X.obj)) (forget Ab.{u}) ≫
        ((sheafCompose J (forget Ab.{u})).map
          ((cocontinuousAbelianInverseImageIso F J K).inv.app X)).hom =
      toSheafify J ((F.op ⋙ X.obj) ⋙ forget Ab.{u}) := by
  have key : toSheafify J ((F.op ⋙ X.obj) ⋙ forget Ab.{u}) ≫
      ((sheafCompose J (forget Ab.{u})).map
        ((cocontinuousAbelianInverseImageIso F J K).hom.app X)).hom =
      Functor.whiskerRight (toSheafify J (F.op ⋙ X.obj)) (forget Ab.{u}) := by
    rw [cocontinuousAbelianInverseImageIso_hom_app_forget F J K X]
    exact toSheafify_comp_sheafificationInternalIso_hom_app J (F.op ⋙ X.obj)
  have h3 : ((sheafCompose J (forget Ab.{u})).map
        ((cocontinuousAbelianInverseImageIso F J K).hom.app X)).hom ≫
      ((sheafCompose J (forget Ab.{u})).map
        ((cocontinuousAbelianInverseImageIso F J K).inv.app X)).hom = 𝟙 _ := by
    rw [← InducedCategory.comp_hom, ← Functor.map_comp, Iso.hom_inv_id_app]
    exact congrArg InducedCategory.Hom.hom ((sheafCompose J (forget Ab.{u})).map_id _)
  rw [← key]
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h3).trans (Category.comp_id _))

end Stacks.Sites.AbelianPullback

namespace CategoryTheory

/-- Two morphisms of abelian presheaves with the same underlying morphism of presheaves of sets
are equal. -/
private theorem whiskerRight_forget_injective {E : Type u} [Category.{u} E]
    {P Q : Eᵒᵖ ⥤ Ab.{u}} {f g : P ⟶ Q}
    (h : Functor.whiskerRight f (forget Ab.{u}) = Functor.whiskerRight g (forget Ab.{u})) :
    f = g :=
  NatTrans.ext (funext fun V => (forget Ab.{u}).map_injective (congrArg (fun k => k.app V) h))

namespace CocontinuousSimplicialSite

/-- In case (B), the transition of Stacks 09WF is the transpose of the family of restrictions
along the cross-fibre arrows along the right Kan extension. -/
private theorem restrictTransition_inr_hom (C : CocontinuousSimplicialSite.{u})
    {m n : SimplexCategory} (φ : m ⟶ n)
    (F : Sheaf (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalTopology (Type u)) :
    ((restrictTransition (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) φ).app F).hom =
      (((C.underlying.map φ.op).toFunctor).op.ranAdjunction (Type u)).homEquiv _ _
        (Functor.whiskerRight
          (NatTrans.op (Grothendieck.ιNatTrans (F := C.underlying) φ.op)) F.obj) := rfl

/-- In case (B), the sheafification unit followed by the transition of Stacks 09WF is the family
of restrictions along the cross-fibre arrows. -/
theorem toSheafify_comp_fiberTransition_inr_app (C : CocontinuousSimplicialSite.{u})
    {m n : SimplexCategory} (φ : m ⟶ n)
    (F : Sheaf (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalTopology (Type u)) :
    toSheafify ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentTopology n)
        (((C.underlying.map φ.op).toFunctor).op ⋙
          (((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).restrict m).obj F).obj) ≫
        ((fiberTransition (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) φ).app F).hom =
      Functor.whiskerRight
        (NatTrans.op (Grothendieck.ιNatTrans (F := C.underlying) φ.op)) F.obj := by
  have hco : ((C.underlying.map φ.op).toFunctor).IsCocontinuous
      ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentTopology n)
      ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentTopology m) :=
    C.isCocontinuous φ.op
  have hws : HasWeakSheafify
      ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentTopology n) (Type u) :=
    inferInstance
  have hran : ∀ G : ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).component n)ᵒᵖ ⥤ Type u,
      ((C.underlying.map φ.op).toFunctor).op.HasPointwiseRightKanExtension G :=
    inferInstance
  refine Eq.trans
    (@Functor.toSheafify_comp_sheafAdjunctionPullbackCocontinuous_homEquiv_symm_hom
      _ _ _ _ ((C.underlying.map φ.op).toFunctor) (Type u) _
      ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentTopology n)
      ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentTopology m) hco hws hran _ _
      ((restrictTransition (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) φ).app F)) ?_
  refine Eq.trans (congrArg
    (fun k => ((((C.underlying.map φ.op).toFunctor).op.ranAdjunction (Type u)).homEquiv
      (((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).restrict m).obj F).obj
      (((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).restrict n).obj F).obj).symm k)
    (restrictTransition_inr_hom C φ F)) ?_
  exact Equiv.symm_apply_apply _ _

open Stacks.Sites.AbelianPullback in
/-- **The two descriptions of the transition along a simplex map agree, in case (B).** The
summand transformation of the sum formula of Stacks 09WG is the transition of Stacks 07TF,
transported along the comparison of the chosen inverse image of abelian sheaves with the inverse
image of Stacks 04JC. -/
theorem fiberTransitionAb_eq (C : CocontinuousSimplicialSite.{u}) {m n : SimplexCategory}
    (φ : m ⟶ n) :
    fiberTransitionAb (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) φ =
      Functor.whiskerLeft ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).abelianComponent m)
          (transitionInverseImageAbIso C φ).hom ≫
        abelianTransitionOfFiber (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) φ := by
  refine NatTrans.ext (funext fun A => ?_)
  refine Sheaf.hom_ext_toSheafify _ _ ?_
  refine whiskerRight_forget_injective ?_
  have hsplit : ((Functor.whiskerLeft
        ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).abelianComponent m)
          (transitionInverseImageAbIso C φ).hom ≫
        abelianTransitionOfFiber (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) φ).app A).hom =
      ((transitionInverseImageAbIso C φ).hom.app
          (((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).abelianComponent m).obj A)).hom ≫
        ((abelianTransitionOfFiber (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) φ).app A).hom := rfl
  have hK := whiskerRight_toSheafify_comp_cocontinuousAbelianInverseImageIso_inv_app
      ((C.underlying.map φ.op).toFunctor) (topologyOfCoverings (C.coverage (op n)))
      (topologyOfCoverings (C.coverage (op m)))
      (((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).abelianComponent m).obj A)
  have hatof : Functor.whiskerRight
        ((abelianTransitionOfFiber (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) φ).app A).hom
        (forget Ab.{u}) =
      ((fiberTransition (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) φ).app
        ((sheafCompose (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalTopology
          (forget Ab.{u})).obj A)).hom :=
    congrArg InducedCategory.Hom.hom
      (abelianTransitionOfFiber_forget (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) φ A)
  refine Eq.trans (congrArg (fun k => Functor.whiskerRight k (forget Ab.{u}))
    (toSheafify_comp_fiberTransitionAb_inr_app C φ A)) ?_
  refine Eq.trans ?_ (congrArg (fun k => Functor.whiskerRight (toSheafify _ _ ≫ k)
    (forget Ab.{u})) hsplit).symm
  refine Eq.trans ?_ (congrArg (fun k => Functor.whiskerRight k (forget Ab.{u}))
    (Category.assoc _ _ _))
  refine Eq.trans ?_ (Functor.whiskerRight_comp _ _ _).symm
  refine Eq.trans ?_ (congrArg (fun k => k ≫ Functor.whiskerRight
    ((abelianTransitionOfFiber (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) φ).app A).hom
    (forget Ab.{u})) (Eq.trans (Functor.whiskerRight_comp _ _ _) hK).symm)
  refine Eq.trans ?_ (congrArg (fun k => toSheafify
    (topologyOfCoverings (C.coverage (op n))) _ ≫ k) hatof.symm)
  exact (toSheafify_comp_fiberTransition_inr_app C φ
    ((sheafCompose (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalTopology
      (forget Ab.{u})).obj A)).symm

open Stacks.Sites.AbelianPullback in
/-- **The two descriptions of the transition along a simplex map agree, in case (B).** The
summand transformation of the sum formula of Stacks 09WG is the transition of Stacks 07TF,
transported along the comparison of the chosen inverse image of abelian sheaves with the inverse
image of Stacks 04JC, stated with `restrictAb`. -/
theorem fiberTransitionAb_eq' (C : CocontinuousSimplicialSite.{u}) {m n : SimplexCategory}
    (φ : m ⟶ n) :
    fiberTransitionAb' (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) φ =
      Functor.whiskerLeft ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).restrictAb m)
          (transitionInverseImageAbIso C φ).hom ≫
        abelianTransitionOfFiber' (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) φ := by
  refine NatTrans.ext (funext fun A => ?_)
  refine Sheaf.hom_ext_toSheafify _ _ ?_
  refine whiskerRight_forget_injective ?_
  have hsplit : ((Functor.whiskerLeft
        ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).restrictAb m)
          (transitionInverseImageAbIso C φ).hom ≫
        abelianTransitionOfFiber' (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) φ).app A).hom =
      ((transitionInverseImageAbIso C φ).hom.app
          (((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).restrictAb m).obj A)).hom ≫
        ((abelianTransitionOfFiber' (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) φ).app A).hom := rfl
  have hK := whiskerRight_toSheafify_comp_cocontinuousAbelianInverseImageIso_inv_app
      ((C.underlying.map φ.op).toFunctor) (topologyOfCoverings (C.coverage (op n)))
      (topologyOfCoverings (C.coverage (op m)))
      (((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).restrictAb m).obj A)
  have hatof : Functor.whiskerRight
        ((abelianTransitionOfFiber' (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) φ).app A).hom
        (forget Ab.{u}) =
      ((fiberTransition (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) φ).app
        ((sheafCompose (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalTopology
          (forget Ab.{u})).obj A)).hom :=
    congrArg InducedCategory.Hom.hom
      (abelianTransitionOfFiber_forget' (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) φ A)
  refine Eq.trans (congrArg (fun k => Functor.whiskerRight k (forget Ab.{u}))
    (toSheafify_comp_fiberTransitionAb_inr_app' C φ A)) ?_
  refine Eq.trans ?_ (congrArg (fun k => Functor.whiskerRight (toSheafify _ _ ≫ k)
    (forget Ab.{u})) hsplit).symm
  refine Eq.trans ?_ (congrArg (fun k => Functor.whiskerRight k (forget Ab.{u}))
    (Category.assoc _ _ _))
  refine Eq.trans ?_ (Functor.whiskerRight_comp _ _ _).symm
  refine Eq.trans ?_ (congrArg (fun k => k ≫ Functor.whiskerRight
    ((abelianTransitionOfFiber' (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) φ).app A).hom
    (forget Ab.{u})) (Eq.trans (Functor.whiskerRight_comp _ _ _) hK).symm)
  refine Eq.trans ?_ (congrArg (fun k => toSheafify
    (topologyOfCoverings (C.coverage (op n))) _ ≫ k) hatof.symm)
  exact (toSheafify_comp_fiberTransition_inr_app C φ
    ((sheafCompose (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalTopology
      (forget Ab.{u})).obj A)).symm

end CocontinuousSimplicialSite

namespace SimplicialSiteSituation

/-- **The two descriptions of the transition along a simplex map agree.** The summand
transformation of the sum formula of Stacks 09WG is the transition of Stacks 07TF, transported
along the comparison of the chosen inverse image of abelian sheaves with the inverse image of
Stacks 04JC, in both cases of Stacks 09WE. -/
theorem fiberTransitionAb_eq (S : SimplicialSiteSituation.{u}) {m n : SimplexCategory}
    (φ : m ⟶ n) :
    fiberTransitionAb S φ =
      Functor.whiskerLeft (S.abelianComponent m) (S.transitionInverseImageAbIso φ).hom ≫
        abelianTransitionOfFiber S φ := by
  obtain ⟨c⟩ := S
  cases c with
  | inl C => exact SimplicialSite.fiberTransitionAb_eq C φ
  | inr C => exact CocontinuousSimplicialSite.fiberTransitionAb_eq C φ

/-- **The two descriptions of the transition along a simplex map agree.** The summand
transformation of the sum formula of Stacks 09WG is the transition of Stacks 07TF, transported
along the comparison of the chosen inverse image of abelian sheaves with the inverse image of
Stacks 04JC, in both cases of Stacks 09WE, stated with `restrictAb`. -/
theorem fiberTransitionAb_eq' (S : SimplicialSiteSituation.{u}) {m n : SimplexCategory}
    (φ : m ⟶ n) :
    fiberTransitionAb' S φ =
      Functor.whiskerLeft (S.restrictAb m) (S.transitionInverseImageAbIso φ).hom ≫
        abelianTransitionOfFiber' S φ := by
  obtain ⟨c⟩ := S
  cases c with
  | inl C => exact SimplicialSite.fiberTransitionAb_eq' C φ
  | inr C => exact CocontinuousSimplicialSite.fiberTransitionAb_eq' C φ

end SimplicialSiteSituation

end CategoryTheory

end
