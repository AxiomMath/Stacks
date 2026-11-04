module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.AbelianRestrictTransition

/-!
# The inverse image of Stacks 09WG is the transition of Stacks 07TF (case (A))

The theory of cartesian objects of Stacks 07TF describes the transition along a simplex map by
`CategoryTheory.SimplicialSiteSituation.abelianTransitionOfFiber`, a transformation into the
restriction functor `g_n^{-1}` whose underlying map of sheaves of sets is the transition of
Stacks 09WF; the sum formula of Stacks 09WG describes the same transition by
`CategoryTheory.SimplicialSiteSituation.fiberTransitionAb`, a transformation out of the chosen
inverse image `transitionInverseImageAb` that is the summand of the formula.  The two are the same
map, read through the comparison
`CategoryTheory.SimplicialSiteSituation.transitionInverseImageAbIso` of the two inverse images.
This file proves that in case (A) of Stacks 09WE.

## Main results

* `Stacks.Sites.AbelianPullback.toSheafify_comp_sheafificationInternalIso_hom_app`: the
  comparison of sheafification of abelian presheaves with sheafification of the underlying
  presheaves of sets is, after the sheafification unit of the underlying presheaf, the underlying
  map of the sheafification unit.
* `CategoryTheory.SimplicialSite.fiberTransitionAb_eq`: in case (A), the summand transformation of
  the sum formula is the transition of Stacks 07TF transported along the comparison of inverse
  images.
* `CategoryTheory.SimplicialSite.fiberTransitionAb_eq'`: the same statement with `restrictAb` in
  place of `abelianComponent`.

## Implementation notes

The comparison `Stacks.Sites.AbelianPullback.sheafificationInternalIso` is stated and built with
the cartesian and braided structures of sheaves and presheaves of sets as file-local instances, so
those instances are declared again here; they are the same terms, which is what makes the two
spellings of its type agree.

The main proofs use `Eq.trans` against named lemmas rather than rewrites: the transition data
through `CategoryTheory.SimplicialSiteSituation.transitionAdjunctionAb` and through
`CategoryTheory.Functor.sheafPullbackConstruction.sheafAdjunctionContinuous` are definitionally
but not syntactically equal, and a rewrite does not see that equality.

## References

* [Stacks Project, Tag 07TF](https://stacks.math.columbia.edu/tag/07TF)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 09WF](https://stacks.math.columbia.edu/tag/09WF)
* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
* [Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open CategoryTheory.Sites CategoryTheory.Sites.AbelianSheaf
open CategoryTheory.SimplicialSiteSituation Opposite

universe u

namespace Stacks.Sites.AbelianPullback

attribute [local instance] CategoryTheory.sheafTypeCartesian CategoryTheory.sheafTypeBraided

noncomputable local instance cartesianPresheafTypes' {C : Type u} [Category.{u} C] :
    CartesianMonoidalCategory (C ⥤ Type u) := Functor.cartesianMonoidalCategory

noncomputable local instance braidedPresheafTypes' {C : Type u} [Category.{u} C] :
    BraidedCategory (C ⥤ Type u) := .ofCartesianMonoidalCategory

noncomputable local instance braidedSheafToPresheafTypes' {C : Type u} [Category.{u} C]
    (J : GrothendieckTopology C) : (sheafToPresheaf J (Type u)).Braided :=
  .ofChosenFiniteProducts _

variable {C : Type u} [Category.{u} C]

/-- The sheafification of an abelian presheaf is the sheafification of its underlying presheaf of
sets: on underlying sheaves of sets the comparison, composed with the sheafification unit of the
underlying presheaf, is the underlying map of the sheafification unit. -/
theorem toSheafify_comp_sheafificationInternalIso_hom_app (J : GrothendieckTopology C)
    [HasSheafify J (Type u)] [HasWeakSheafify J Ab.{u}] (P : Cᵒᵖ ⥤ Ab.{u}) :
    toSheafify J (P ⋙ forget Ab.{u}) ≫
        ((sheafCompose J (forget Ab.{u})).map
          ((sheafificationInternalIso J).hom.app P)).hom =
      Functor.whiskerRight (toSheafify J P) (forget Ab.{u}) := by
  let _ : (presheafToSheaf J (Type u)).Braided := .ofChosenFiniteProducts _
  let E : (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ≌ CommGrp (Cᵒᵖ ⥤ Type u) := presheafEquivalence _
  let E' : Sheaf J AddCommGrpCat.{u} ≌ CommGrp (Sheaf J (Type u)) := AbelianSheaf.equivalence J
  let a := (E.toAdjunction.comp (sheafificationAdjunction J (Type u)).mapCommGrp).comp
    E'.symm.toAdjunction
  let e : sheafToPresheaf J AddCommGrpCat.{u} ≅
      internalSheaf J ⋙ (sheafToPresheaf J (Type u)).mapCommGrp ⋙ abelianPresheaves :=
    (Functor.rightUnitor _).symm ≪≫
      Functor.isoWhiskerLeft _ E.unitIso ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (sheafToPresheafInternalIso J) _ ≪≫
      Functor.associator _ _ _
  have h0 : (sheafificationInternalIso J).hom.app P =
      ((a.ofNatIsoRight e.symm).leftAdjointUniq
        (sheafificationAdjunction J Ab.{u})).hom.app P :=
    Category.id_comp _
  have hu : Functor.whiskerRight ((a.ofNatIsoRight e.symm).unit.app P) (forget Ab.{u}) =
      toSheafify J (P ⋙ forget Ab.{u}) := by
    simp only [a]
    rfl
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app (a.ofNatIsoRight e.symm)
    (sheafificationAdjunction J Ab.{u}) P
  refine Eq.trans (congrArg (fun k => toSheafify J (P ⋙ forget Ab.{u}) ≫
      ((sheafCompose J (forget Ab.{u})).map k).hom) h0) ?_
  refine Eq.trans ?_ (congrArg (fun k => Functor.whiskerRight k (forget Ab.{u})) h)
  refine Eq.trans ?_ (congrArg (fun k => Functor.whiskerRight k (forget Ab.{u}))
    ((a.ofNatIsoRight e.symm).homEquiv_unit P _
      (((a.ofNatIsoRight e.symm).leftAdjointUniq
        (sheafificationAdjunction J Ab.{u})).hom.app P))).symm
  refine Eq.trans ?_ (Functor.whiskerRight_comp _ _ _).symm
  exact (congrArg (fun k => k ≫ Functor.whiskerRight
    (((a.ofNatIsoRight e.symm).leftAdjointUniq
      (sheafificationAdjunction J Ab.{u})).hom.app P).hom (forget Ab.{u})) hu).symm

end Stacks.Sites.AbelianPullback

namespace CategoryTheory.SimplicialSite

open Stacks.Sites.AbelianPullback in
/-- **The two descriptions of the transition along a simplex map agree, in case (A).** The
summand transformation of the sum formula of Stacks 09WG is the transition of Stacks 07TF,
transported along the comparison of the chosen inverse image of abelian sheaves with the inverse
image of Stacks 04JC. -/
theorem fiberTransitionAb_eq (C : SimplicialSite.{u}) {m n : SimplexCategory} (φ : m ⟶ n) :
    fiberTransitionAb (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) φ =
      Functor.whiskerLeft ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).abelianComponent m)
          (transitionInverseImageAbIso C φ).hom ≫
        abelianTransitionOfFiber (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) φ := by
  have hcont : ((C.underlying.map φ).toFunctor).IsContinuous
      (C.coverage m).toGrothendieck (C.coverage n).toGrothendieck :=
    (C.isMorphismOfSites φ).isContinuous
  have hA1 : ∀ X : Sheaf ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentTopology m) Ab.{u},
      (transitionInverseImageAbIso C φ).hom.app X =
        ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            ((C.underlying.map φ).toFunctor) Ab.{u}
            (C.coverage m).toGrothendieck (C.coverage n).toGrothendieck).leftAdjointUniq
          ((abelianSheafAdjunction (C.isMorphismOfSites φ)).ofNatIsoRight
            (abelianSheafPushforwardIso ((C.underlying.map φ).toFunctor)
              (C.coverage m).toGrothendieck (C.coverage n).toGrothendieck))).hom.app X := by
    intro X
    refine Eq.trans (congrArg (fun k => k ≫
      (sheafPullbackAbIsoAbelianInverseImage (C.isMorphismOfSites φ)).hom.app X)
      (Adjunction.leftAdjointUniq_inv_app _ _ X)) ?_
    exact Adjunction.leftAdjointUniq_trans_app _ _ _ X
  have key : ∀ X : Sheaf ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentTopology m) Ab.{u},
      ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).transitionAdjunctionAb φ).homEquiv X _
          ((transitionInverseImageAbIso C φ).hom.app X) =
        ((abelianSheafAdjunction (C.isMorphismOfSites φ)).ofNatIsoRight
          (abelianSheafPushforwardIso ((C.underlying.map φ).toFunctor)
            (C.coverage m).toGrothendieck (C.coverage n).toGrothendieck)).unit.app X := by
    intro X
    refine Eq.trans (congrArg
      (((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).transitionAdjunctionAb φ).homEquiv X _)
      (hA1 X)) ?_
    exact Adjunction.homEquiv_leftAdjointUniq_hom_app _ _ X
  have hA2 : ∀ X : Sheaf ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentTopology m) Ab.{u},
      (sheafCompose ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentTopology m)
          (forget Ab.{u})).map
        (((abelianSheafAdjunction (C.isMorphismOfSites φ)).ofNatIsoRight
          (abelianSheafPushforwardIso ((C.underlying.map φ).toFunctor)
            (C.coverage m).toGrothendieck (C.coverage n).toGrothendieck)).unit.app X) =
      ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).transitionMorphism φ).adj.unit.app
        ((sheafCompose ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentTopology m)
          (forget Ab.{u})).obj X) := by
    intro X
    simp only [abelianSheafAdjunction]
    rfl
  have hbridge : ∀ {Y Z : Sheaf ((⟨Sum.inl C⟩ :
        SimplicialSiteSituation.{u}).componentTopology n) Ab.{u}} (g : Y ⟶ Z),
      ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).transitionMorphism φ).pushforward.map
          ((sheafCompose ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentTopology n)
            (forget Ab.{u})).map g) =
        (sheafCompose ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentTopology m)
            (forget Ab.{u})).map
          (((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).transitionDirectImageAb φ).map g) := by
    intro Y Z g
    rfl
  refine NatTrans.ext (funext fun A => ?_)
  refine (((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).transitionAdjunctionAb φ).homEquiv
    _ _).injective ?_
  rw [fiberTransitionAb_adj]
  have hrhs : ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).transitionAdjunctionAb φ).homEquiv
        _ _
        ((Functor.whiskerLeft ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).abelianComponent m)
            (transitionInverseImageAbIso C φ).hom ≫
          abelianTransitionOfFiber (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) φ).app A) =
      ((abelianSheafAdjunction (C.isMorphismOfSites φ)).ofNatIsoRight
          (abelianSheafPushforwardIso ((C.underlying.map φ).toFunctor)
            (C.coverage m).toGrothendieck (C.coverage n).toGrothendieck)).unit.app
          (((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).abelianComponent m).obj A) ≫
        ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).transitionDirectImageAb φ).map
          ((abelianTransitionOfFiber (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) φ).app A) := by
    refine Eq.trans (Adjunction.homEquiv_unit _ _ _ _) ?_
    refine Eq.trans (congrArg (fun k =>
      ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).transitionAdjunctionAb φ).unit.app
        (((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).abelianComponent m).obj A) ≫ k)
      (((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).transitionDirectImageAb φ).map_comp _ _)) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    exact congrArg (fun k => k ≫
      ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).transitionDirectImageAb φ).map
        ((abelianTransitionOfFiber (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) φ).app A))
      ((Adjunction.homEquiv_unit _ _ _ _).symm.trans
        (key (((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).abelianComponent m).obj A)))
  rw [hrhs]
  refine (sheafCompose ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentTopology m)
    (forget Ab.{u})).map_injective ?_
  refine Eq.trans (restrictTransitionAb_inl_forget C φ A) ?_
  refine Eq.trans (fiberTransition_adj (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) φ
    ((sheafCompose (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).totalTopology
      (forget Ab.{u})).obj A)).symm ?_
  refine Eq.trans (Adjunction.homEquiv_unit _ _ _ _) ?_
  refine Eq.trans ?_ ((sheafCompose
    ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentTopology m) (forget Ab.{u})).map_comp
      _ _).symm
  refine Eq.trans (congrArg (fun k => k ≫
      ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).transitionMorphism φ).pushforward.map
        ((fiberTransition (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) φ).app
          ((sheafCompose (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).totalTopology
            (forget Ab.{u})).obj A)))
    (hA2 (((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).abelianComponent m).obj A)).symm) ?_
  have hlast : ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).transitionMorphism
          φ).pushforward.map
        ((fiberTransition (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) φ).app
          ((sheafCompose (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).totalTopology
            (forget Ab.{u})).obj A)) =
      (sheafCompose ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentTopology m)
          (forget Ab.{u})).map
        (((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).transitionDirectImageAb φ).map
          ((abelianTransitionOfFiber (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) φ).app A)) :=
    Eq.trans (congrArg ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).transitionMorphism
        φ).pushforward.map
      (abelianTransitionOfFiber_forget (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) φ A).symm)
      (hbridge _)
  exact congrArg _ hlast

open Stacks.Sites.AbelianPullback in
/-- **The two descriptions of the transition along a simplex map agree, in case (A).** The
summand transformation of the sum formula of Stacks 09WG is the transition of Stacks 07TF,
transported along the comparison of the chosen inverse image of abelian sheaves with the inverse
image of Stacks 04JC, stated with `restrictAb`. -/
theorem fiberTransitionAb_eq' (C : SimplicialSite.{u}) {m n : SimplexCategory} (φ : m ⟶ n) :
    fiberTransitionAb' (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) φ =
      Functor.whiskerLeft ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).restrictAb m)
          (transitionInverseImageAbIso C φ).hom ≫
        abelianTransitionOfFiber' (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) φ := by
  have hcont : ((C.underlying.map φ).toFunctor).IsContinuous
      (C.coverage m).toGrothendieck (C.coverage n).toGrothendieck :=
    (C.isMorphismOfSites φ).isContinuous
  have hA1 : ∀ X : Sheaf ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentTopology m) Ab.{u},
      (transitionInverseImageAbIso C φ).hom.app X =
        ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            ((C.underlying.map φ).toFunctor) Ab.{u}
            (C.coverage m).toGrothendieck (C.coverage n).toGrothendieck).leftAdjointUniq
          ((abelianSheafAdjunction (C.isMorphismOfSites φ)).ofNatIsoRight
            (abelianSheafPushforwardIso ((C.underlying.map φ).toFunctor)
              (C.coverage m).toGrothendieck (C.coverage n).toGrothendieck))).hom.app X := by
    intro X
    refine Eq.trans (congrArg (fun k => k ≫
      (sheafPullbackAbIsoAbelianInverseImage (C.isMorphismOfSites φ)).hom.app X)
      (Adjunction.leftAdjointUniq_inv_app _ _ X)) ?_
    exact Adjunction.leftAdjointUniq_trans_app _ _ _ X
  have key : ∀ X : Sheaf ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentTopology m) Ab.{u},
      ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).transitionAdjunctionAb φ).homEquiv X _
          ((transitionInverseImageAbIso C φ).hom.app X) =
        ((abelianSheafAdjunction (C.isMorphismOfSites φ)).ofNatIsoRight
          (abelianSheafPushforwardIso ((C.underlying.map φ).toFunctor)
            (C.coverage m).toGrothendieck (C.coverage n).toGrothendieck)).unit.app X := by
    intro X
    refine Eq.trans (congrArg
      (((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).transitionAdjunctionAb φ).homEquiv X _)
      (hA1 X)) ?_
    exact Adjunction.homEquiv_leftAdjointUniq_hom_app _ _ X
  have hA2 : ∀ X : Sheaf ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentTopology m) Ab.{u},
      (sheafCompose ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentTopology m)
          (forget Ab.{u})).map
        (((abelianSheafAdjunction (C.isMorphismOfSites φ)).ofNatIsoRight
          (abelianSheafPushforwardIso ((C.underlying.map φ).toFunctor)
            (C.coverage m).toGrothendieck (C.coverage n).toGrothendieck)).unit.app X) =
      ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).transitionMorphism φ).adj.unit.app
        ((sheafCompose ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentTopology m)
          (forget Ab.{u})).obj X) := by
    intro X
    simp only [abelianSheafAdjunction]
    rfl
  have hbridge : ∀ {Y Z : Sheaf ((⟨Sum.inl C⟩ :
        SimplicialSiteSituation.{u}).componentTopology n) Ab.{u}} (g : Y ⟶ Z),
      ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).transitionMorphism φ).pushforward.map
          ((sheafCompose ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentTopology n)
            (forget Ab.{u})).map g) =
        (sheafCompose ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentTopology m)
            (forget Ab.{u})).map
          (((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).transitionDirectImageAb φ).map g) := by
    intro Y Z g
    rfl
  refine NatTrans.ext (funext fun A => ?_)
  refine (((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).transitionAdjunctionAb φ).homEquiv
    _ _).injective ?_
  rw [fiberTransitionAb_adj']
  have hrhs : ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).transitionAdjunctionAb φ).homEquiv
        _ _
        ((Functor.whiskerLeft ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).restrictAb m)
            (transitionInverseImageAbIso C φ).hom ≫
          abelianTransitionOfFiber' (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) φ).app A) =
      ((abelianSheafAdjunction (C.isMorphismOfSites φ)).ofNatIsoRight
          (abelianSheafPushforwardIso ((C.underlying.map φ).toFunctor)
            (C.coverage m).toGrothendieck (C.coverage n).toGrothendieck)).unit.app
          (((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).restrictAb m).obj A) ≫
        ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).transitionDirectImageAb φ).map
          ((abelianTransitionOfFiber' (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) φ).app A) := by
    refine Eq.trans (Adjunction.homEquiv_unit _ _ _ _) ?_
    refine Eq.trans (congrArg (fun k =>
      ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).transitionAdjunctionAb φ).unit.app
        (((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).restrictAb m).obj A) ≫ k)
      (((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).transitionDirectImageAb φ).map_comp _ _)) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    exact congrArg (fun k => k ≫
      ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).transitionDirectImageAb φ).map
        ((abelianTransitionOfFiber' (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) φ).app A))
      ((Adjunction.homEquiv_unit _ _ _ _).symm.trans
        (key (((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).restrictAb m).obj A)))
  rw [hrhs]
  refine (sheafCompose ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentTopology m)
    (forget Ab.{u})).map_injective ?_
  refine Eq.trans (restrictTransitionAb_inl_forget' C φ A) ?_
  refine Eq.trans (fiberTransition_adj (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) φ
    ((sheafCompose (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).totalTopology
      (forget Ab.{u})).obj A)).symm ?_
  refine Eq.trans (Adjunction.homEquiv_unit _ _ _ _) ?_
  refine Eq.trans ?_ ((sheafCompose
    ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentTopology m) (forget Ab.{u})).map_comp
      _ _).symm
  refine Eq.trans (congrArg (fun k => k ≫
      ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).transitionMorphism φ).pushforward.map
        ((fiberTransition (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) φ).app
          ((sheafCompose (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).totalTopology
            (forget Ab.{u})).obj A)))
    (hA2 (((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).restrictAb m).obj A)).symm) ?_
  have hlast : ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).transitionMorphism
          φ).pushforward.map
        ((fiberTransition (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) φ).app
          ((sheafCompose (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).totalTopology
            (forget Ab.{u})).obj A)) =
      (sheafCompose ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentTopology m)
          (forget Ab.{u})).map
        (((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).transitionDirectImageAb φ).map
          ((abelianTransitionOfFiber' (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) φ).app A)) :=
    Eq.trans (congrArg ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).transitionMorphism
        φ).pushforward.map
      (abelianTransitionOfFiber_forget' (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) φ A).symm)
      (hbridge _)
  exact congrArg _ hlast

end CategoryTheory.SimplicialSite

end
