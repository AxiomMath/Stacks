module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.RepresentableBridgeBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleBaseChangeUnitors
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChangeIdComp
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SmallEtaleSheafAdjPseudofunctor
public import StacksFrontier.CategoryTheory.Bicategory.LeftAdjointStrongTrans
public import StacksFrontier.CategoryTheory.Sites.Descent.RestrictedBaseDescentData
public import StacksFrontier.CategoryTheory.Sites.Descent.StrongTransDescentData

/-!
# The spaces-étale and small étale pseudofunctors agree on representable algebraic spaces

On the big fppf site of `S` there are two pseudofunctors of inverse images of étale sheaves:
the spaces-étale one, `V ↦ Sh((h_V)_{spaces-étale})`, restricted along the Yoneda embedding
into algebraic spaces, and the small étale one, `V ↦ Sh(V'_étale)`, restricted along the
forgetful functor to the schemes of the site. Restriction along the chart functors
(`AlgebraicGeometry.Space.representedRestriction`) is an equivalence between their fibres,
and it intertwines the direct images (`AlgebraicGeometry.Space.representedPushforwardIso`).
This file checks that this comparison of direct images is compatible with composition and
identities, and assembles it, through `CategoryTheory.Pseudofunctor.strongTransOfLeftAdjoints`,
into a strong transformation between the two pseudofunctors of inverse images.

## Main definitions

* `AlgebraicGeometry.Space.representedSpacesPseudofunctor` and
  `AlgebraicGeometry.Space.representedSchemesPseudofunctor`: the two pseudofunctors.
* `AlgebraicGeometry.Space.representedComparison`: the strong transformation between them, with
  components `AlgebraicGeometry.Space.representedRestriction`.

## Main results

* `AlgebraicGeometry.Space.rightAdjointComp_representedSpacesPseudofunctor`,
  `AlgebraicGeometry.Space.rightAdjointComp_representedSchemesPseudofunctor` and their
  `rightAdjointId_` analogues: the composition and identity constraints of the two
  pseudofunctors, read on the direct images, are the composition and identity isomorphisms of
  direct images.
* `AlgebraicGeometry.Space.representedChartBaseChangeIso_comp_app` and
  `AlgebraicGeometry.Space.representedChartBaseChangeIso_id_app`: the base-change comparison of
  chart functors is compatible with composition and identities, at the level of sites.
* `AlgebraicGeometry.Space.representedPushforwardSquare_comp` and
  `AlgebraicGeometry.Space.representedPushforwardSquare_id`: the same for the comparison of
  direct images.
* `AlgebraicGeometry.Space.properSurjectivePrestackOverSchemes_of_fullyFaithful`: full
  faithfulness of descent of small étale sheaves along proper surjections of schemes gives
  `AlgebraicGeometry.Space.ProperSurjectivePrestackOverSchemes`, the input of
  `AlgebraicGeometry.Space.isPrestackFor_of_isProper_isSurjective`.

## References

* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 0DFX](https://stacks.math.columbia.edu/tag/0DFX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TwoSquare

universe u v₁ u₁ v₂ u₂

namespace CategoryTheory.Over

/-- The inverse of the identity comparison of slice pullback along an identity is a section of
the first projection of the fibre product. -/
@[reassoc (attr := simp)]
theorem pullbackId_inv_app_left_fst {C : Type*} [Category C] [HasPullbacks C] {X : C}
    (V : Over X) : (pullbackId.inv.app V).left ≫ pullback.fst V.hom (𝟙 X) = 𝟙 V.left := by
  rw [← pullbackId_hom_app_left, ← Over.comp_left, Iso.inv_hom_id_app]
  rfl

end CategoryTheory.Over

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The pseudofunctor of spaces-étale inverse images, restricted to the algebraic spaces
represented by objects of the big fppf site. -/
abbrev representedSpacesPseudofunctor :
    Pseudofunctor (LocallyDiscrete (BigFppfOver B S hS)ᵒᵖ) Cat :=
  (spacesEtalePseudofunctor B S hS).restrict (schemeSpaceFunctor B S hS)

/-- The pseudofunctor of small étale inverse images, restricted to the schemes underlying
objects of the big fppf site. -/
abbrev representedSchemesPseudofunctor :
    Pseudofunctor (LocallyDiscrete (BigFppfOver B S hS)ᵒᵖ) Cat :=
  (smallEtaleSheafInverseImagePseudofunctor (associatedBigEtaleSite B)).restrict
    (Over.forget (B.obj hS))

variable {B S hS}

/-- Small étale base change along the morphism of schemes underlying a morphism of the site is
continuous. -/
instance representedSchemeBaseChange_isContinuous {V W : BigFppfOver B S hS} (f : W ⟶ V) :
    (smallEtaleBaseChange (associatedBigEtaleSite B) f.left).IsContinuous
      (representedSchemeTopology B S hS V) (representedSchemeTopology B S hS W) :=
  smallEtaleBaseChange_isContinuous (associatedBigEtaleSite B) f.left

/-- The spaces-étale direct image along a morphism of the site. -/
abbrev representedSpacesPushforward {V W : BigFppfOver B S hS} (f : W ⟶ V) :
    (representedSpacesPseudofunctor B S hS).obj (.mk (op W)) ⥤
      (representedSpacesPseudofunctor B S hS).obj (.mk (op V)) :=
  spacesEtaleSheafPushforward B S hS ((schemeSpaceFunctor B S hS).map f)

/-- The spaces-étale inverse image is left adjoint to the direct image. -/
abbrev representedSpacesAdjunction {V W : BigFppfOver B S hS} (f : W ⟶ V) :
    ((representedSpacesPseudofunctor B S hS).map f.op.toLoc).toFunctor ⊣
      representedSpacesPushforward f :=
  spacesEtaleAdjunction B S hS ((schemeSpaceFunctor B S hS).map f)

/-- The small étale direct image along the morphism of schemes underlying a morphism of the
site. -/
abbrev representedSchemesPushforward {V W : BigFppfOver B S hS} (f : W ⟶ V) :
    (representedSchemesPseudofunctor B S hS).obj (.mk (op W)) ⥤
      (representedSchemesPseudofunctor B S hS).obj (.mk (op V)) :=
  (smallEtaleBaseChange (associatedBigEtaleSite B) f.left).sheafPushforwardContinuous
    (Type (u + 1)) (representedSchemeTopology B S hS V) (representedSchemeTopology B S hS W)

/-- The small étale inverse image is left adjoint to the direct image. -/
abbrev representedSchemesAdjunction {V W : BigFppfOver B S hS} (f : W ⟶ V) :
    ((representedSchemesPseudofunctor B S hS).map f.op.toLoc).toFunctor ⊣
      representedSchemesPushforward f :=
  (smallEtaleBaseChange (associatedBigEtaleSite B) f.left).sheafAdjunctionContinuous
    (Type (u + 1)) (representedSchemeTopology B S hS V) (representedSchemeTopology B S hS W)

/-- The comparison of direct images, as a `2`-square. -/
abbrev representedPushforwardSquare {V W : BigFppfOver B S hS} (f : W ⟶ V) :
    TwoSquare (representedSpacesPushforward f) (representedRestriction W (Type (u + 1)))
      (representedRestriction V (Type (u + 1))) (representedSchemesPushforward f) :=
  (representedPushforwardIso f (Type (u + 1))).hom

/-- The composition constraint of the restricted spaces-étale pseudofunctor, read on the
direct images, is the composition isomorphism of spaces-étale direct images. -/
theorem rightAdjointComp_representedSpacesPseudofunctor {X Y Z : BigFppfOver B S hS}
    (p : Y ⟶ X) (q : Z ⟶ Y) :
    Pseudofunctor.rightAdjointComp (fun p ↦ representedSpacesPushforward p)
        (fun p ↦ representedSpacesAdjunction p) p q =
      (spacesEtaleSheafPushforwardComp B S hS ((schemeSpaceFunctor B S hS).map q)
        ((schemeSpaceFunctor B S hS).map p)).hom :=
  (Equiv.eq_symm_apply _).1 rfl

/-- The composition constraint of the restricted small étale pseudofunctor, read on the
direct images, is the composition isomorphism of small étale direct images. -/
theorem rightAdjointComp_representedSchemesPseudofunctor {X Y Z : BigFppfOver B S hS}
    (p : Y ⟶ X) (q : Z ⟶ Y) :
    Pseudofunctor.rightAdjointComp (fun p ↦ representedSchemesPushforward p)
        (fun p ↦ representedSchemesAdjunction p) p q =
      (smallEtaleMorphism_comp_pushforwardIso (associatedBigEtaleSite B) _ _ _
        q.left p.left).inv :=
  (Equiv.eq_symm_apply _).1 (Category.id_comp _).symm

/-- The identity constraint of the restricted spaces-étale pseudofunctor, read on the direct
images, is the identity comparison of spaces-étale direct images. -/
theorem rightAdjointId_representedSpacesPseudofunctor (X : BigFppfOver B S hS) :
    Pseudofunctor.rightAdjointId (fun p ↦ representedSpacesPushforward p)
        (fun p ↦ representedSpacesAdjunction p) X =
      (spacesEtaleSheafPushforwardId B S hS ((schemeSpaceFunctor B S hS).obj X)).hom :=
  (Equiv.eq_symm_apply _).1 rfl

/-- The identity constraint of the restricted small étale pseudofunctor, read on the direct
images, is the identity comparison of small étale direct images. -/
theorem rightAdjointId_representedSchemesPseudofunctor (X : BigFppfOver B S hS) :
    Pseudofunctor.rightAdjointId (fun p ↦ representedSchemesPushforward p)
        (fun p ↦ representedSchemesAdjunction p) X =
      letI : (smallEtaleBaseChange (associatedBigEtaleSite B) (𝟙 X.left)).IsContinuous
        (representedSchemeTopology B S hS X) (representedSchemeTopology B S hS X) :=
        smallEtaleBaseChange_isContinuous _ _
      (Functor.sheafPushforwardContinuousId'
        (smallEtaleBaseChange_idIso (associatedBigEtaleSite B) X.left) (Type (u + 1))
        (representedSchemeTopology B S hS X)).hom :=
  (Equiv.eq_symm_apply _).1 rfl

/-- **The base-change comparison of chart functors is compatible with composition**, at the
level of sites: along `q ≫ p`, the comparison followed by the composition isomorphism of small
étale base changes is the composite of the comparisons along `q` and along `p` followed by the
composition isomorphism of spaces-étale base changes. -/
theorem representedChartBaseChangeIso_comp_app {X Y Z : BigFppfOver B S hS} (p : Y ⟶ X)
    (q : Z ⟶ Y) (U : representedSchemeSmallEtale B S hS X) :
    (representedSchemeChartFunctor Z).map
        ((smallEtaleBaseChange_compIso (associatedBigEtaleSite B) _ _ _ q.left p.left).val.hom.app
          U) ≫ (representedChartBaseChangeIso (q ≫ p)).hom.app U =
      (representedChartBaseChangeIso q).hom.app
          ((smallEtaleBaseChange (associatedBigEtaleSite B) p.left).obj U) ≫
        (spacesBaseChange B S hS (yonedaSpaceHom q)).functor.map
          ((representedChartBaseChangeIso p).hom.app U) ≫
        (spacesBaseChange_comp B S hS (yonedaSpaceHom q) (yonedaSpaceHom p)).hom.app
          ((representedSchemeChartFunctor X).obj U) := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  apply (isPullback_spacesBaseChange_representedChart (q ≫ p) U).hom_ext
  · have e1 := representedChartBaseChangeIsoApp_hom_fst (q ≫ p) U
    have e2 := representedChartBaseChangeIsoApp_hom_fst q
      ((smallEtaleBaseChange (associatedBigEtaleSite B) p.left).obj U)
    have e3 := representedChartBaseChangeIsoApp_hom_fst p U
    have e4 : ((spacesBaseChange_comp B S hS (yonedaSpaceHom q) (yonedaSpaceHom p)).hom.app
          ((representedSchemeChartFunctor X).obj U)).hom.left ≫
          (spacesBaseChange B S hS (yonedaSpaceHom (q ≫ p))).projection.app
            ((representedSchemeChartFunctor X).obj U) =
        (spacesBaseChange B S hS (yonedaSpaceHom q)).projection.app
            ((spacesBaseChange B S hS (yonedaSpaceHom p)).functor.obj
              ((representedSchemeChartFunctor X).obj U)) ≫
          (spacesBaseChange B S hS (yonedaSpaceHom p)).projection.app
            ((representedSchemeChartFunctor X).obj U) :=
      spacesBaseChange_comp_projection B S hS (yonedaSpaceHom q) (yonedaSpaceHom p)
        ((representedSchemeChartFunctor X).obj U)
    have e5 : ((spacesBaseChange B S hS (yonedaSpaceHom q)).functor.map
          (representedChartBaseChangeIsoApp p U).hom).hom.left ≫
          (spacesBaseChange B S hS (yonedaSpaceHom q)).projection.app
            ((spacesBaseChange B S hS (yonedaSpaceHom p)).functor.obj
              ((representedSchemeChartFunctor X).obj U)) =
        (spacesBaseChange B S hS (yonedaSpaceHom q)).projection.app
            ((representedSchemeChartFunctor Y).obj
              ((smallEtaleBaseChange (associatedBigEtaleSite B) p.left).obj U)) ≫
          (representedChartBaseChangeIsoApp p U).hom.hom.left :=
      (spacesBaseChange B S hS (yonedaSpaceHom q)).projection.naturality _
    have e6 : (representedChartHomMap
        ((smallEtaleBaseChange_compIso (associatedBigEtaleSite B) _ _ _ q.left p.left).val.hom.app
          U) ≫ representedChartPullbackFst (q ≫ p) U :
          representedChartPullbackObj q
            ((smallEtaleBaseChange (associatedBigEtaleSite B) p.left).obj U) ⟶
          representedChartObj U) =
        representedChartPullbackFst q
          ((smallEtaleBaseChange (associatedBigEtaleSite B) p.left).obj U) ≫
          representedChartPullbackFst p U :=
      Over.OverMorphism.ext (smallEtaleBaseChange_factoredCompIso_hom_app_fst
        (associatedBigEtaleSite B) _ _ _ q.left p.left (q ≫ p).left rfl U)
    have e7 := congrArg yonedaSpaceHom e6
    simp only at e7
    have s1 : yonedaSpaceHom (representedChartHomMap
            ((smallEtaleBaseChange_compIso (associatedBigEtaleSite B) _ _ _ q.left
              p.left).val.hom.app U)) ≫
          ((representedChartBaseChangeIsoApp (q ≫ p) U).hom.hom.left ≫
            (spacesBaseChange B S hS (yonedaSpaceHom (q ≫ p))).projection.app
              ((representedSchemeChartFunctor X).obj U)) =
        yonedaSpaceHom (representedChartPullbackFst q
            ((smallEtaleBaseChange (associatedBigEtaleSite B) p.left).obj U)) ≫
          yonedaSpaceHom (representedChartPullbackFst p U) := by rw [e1]; exact e7
    have s2 : yonedaSpaceHom (representedChartPullbackFst q
            ((smallEtaleBaseChange (associatedBigEtaleSite B) p.left).obj U)) ≫
          yonedaSpaceHom (representedChartPullbackFst p U) =
        (representedChartBaseChangeIsoApp q
            ((smallEtaleBaseChange (associatedBigEtaleSite B) p.left).obj U)).hom.hom.left ≫
          (spacesBaseChange B S hS (yonedaSpaceHom q)).projection.app
            ((representedSchemeChartFunctor Y).obj
              ((smallEtaleBaseChange (associatedBigEtaleSite B) p.left).obj U)) ≫
          (representedChartBaseChangeIsoApp p U).hom.hom.left ≫
          (spacesBaseChange B S hS (yonedaSpaceHom p)).projection.app
            ((representedSchemeChartFunctor X).obj U) := by
      rw [e3]
      exact (congrArg (· ≫ yonedaSpaceHom (representedChartPullbackFst p U)) e2).symm
    have s3 : (representedChartBaseChangeIsoApp q
            ((smallEtaleBaseChange (associatedBigEtaleSite B) p.left).obj U)).hom.hom.left ≫
          (spacesBaseChange B S hS (yonedaSpaceHom q)).projection.app
            ((representedSchemeChartFunctor Y).obj
              ((smallEtaleBaseChange (associatedBigEtaleSite B) p.left).obj U)) ≫
          (representedChartBaseChangeIsoApp p U).hom.hom.left ≫
          (spacesBaseChange B S hS (yonedaSpaceHom p)).projection.app
            ((representedSchemeChartFunctor X).obj U) =
        (representedChartBaseChangeIsoApp q
            ((smallEtaleBaseChange (associatedBigEtaleSite B) p.left).obj U)).hom.hom.left ≫
          ((spacesBaseChange B S hS (yonedaSpaceHom q)).functor.map
            (representedChartBaseChangeIsoApp p U).hom).hom.left ≫
          ((spacesBaseChange_comp B S hS (yonedaSpaceHom q) (yonedaSpaceHom p)).hom.app
            ((representedSchemeChartFunctor X).obj U)).hom.left ≫
          (spacesBaseChange B S hS (yonedaSpaceHom (q ≫ p))).projection.app
            ((representedSchemeChartFunctor X).obj U) := by rw [e4, reassoc_of% e5]
    exact s1.trans (s2.trans s3)
  · exact (Over.w _).trans (Over.w _).symm

/-- **The base-change comparison of chart functors at an identity**, at the level of sites: it
is the identity comparison of spaces-étale base change, after the identity comparison of small
étale base change. -/
theorem representedChartBaseChangeIso_id_app (X : BigFppfOver B S hS)
    (U : representedSchemeSmallEtale B S hS X) :
    (representedSchemeChartFunctor X).map
        ((smallEtaleBaseChange_idIso (associatedBigEtaleSite B) X.left).inv.app U) ≫
        (representedChartBaseChangeIso (𝟙 X)).hom.app U =
      (spacesBaseChange_id B S hS (yonedaSpace B S hS X)).inv.app
        ((representedSchemeChartFunctor X).obj U) := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  apply (isPullback_spacesBaseChange_representedChart (𝟙 X) U).hom_ext
  · have e1 := representedChartBaseChangeIsoApp_hom_fst (𝟙 X) U
    have e2 : ((smallEtaleBaseChange_idIso (associatedBigEtaleSite B) X.left).inv.app U).hom.left ≫
        pullback.fst U.obj.hom (𝟙 X.left) = 𝟙 _ := by
      have h : (_root_.AlgebraicGeometry.SmallEtale.inclusion _ _ _).map
          ((smallEtaleBaseChange_idIso (associatedBigEtaleSite B) X.left).hom.app U) =
          Over.pullbackId.hom.app U.obj := by
        simp only [smallEtaleBaseChange_idIso, Functor.fullyFaithfulCancelRight]
        simp only [ObjectProperty.ι_obj, smallEtaleBaseChange_obj_obj, Functor.id_obj,
          NatIso.trans_app, Functor.comp_obj, NatIso.ofComponents_hom_app, ObjectProperty.ι_map,
          Over.forget_obj]
        exact (_root_.AlgebraicGeometry.SmallEtale.inclusion _ _ _).map_preimage _
      have h' : (_root_.AlgebraicGeometry.SmallEtale.inclusion _ _ _).map
          ((smallEtaleBaseChange_idIso (associatedBigEtaleSite B) X.left).inv.app U) =
          Over.pullbackId.inv.app U.obj :=
        congrArg Iso.inv (show (_root_.AlgebraicGeometry.SmallEtale.inclusion _ _ _).mapIso
          ((smallEtaleBaseChange_idIso (associatedBigEtaleSite B) X.left).app U) =
            Over.pullbackId.app U.obj from Iso.ext h)
      have h'' : ((smallEtaleBaseChange_idIso (associatedBigEtaleSite B) X.left).inv.app
          U).hom.left = (Over.pullbackId.inv.app U.obj).left := congrArg (fun k => k.left) h'
      rw [h'']
      exact Over.pullbackId_inv_app_left_fst U.obj
    have e3 : (representedChartHomMap
        ((smallEtaleBaseChange_idIso (associatedBigEtaleSite B) X.left).inv.app U) ≫
          representedChartPullbackFst (𝟙 X) U : representedChartObj U ⟶ representedChartObj U) =
        𝟙 _ := Over.OverMorphism.ext e2
    have e4 := congrArg yonedaSpaceHom e3
    simp only [yonedaSpaceHom_id] at e4
    have s1 : yonedaSpaceHom (representedChartHomMap
            ((smallEtaleBaseChange_idIso (associatedBigEtaleSite B) X.left).inv.app U)) ≫
          ((representedChartBaseChangeIsoApp (𝟙 X) U).hom.hom.left ≫
            (spacesBaseChange B S hS (yonedaSpaceHom (𝟙 X))).projection.app
              ((representedSchemeChartFunctor X).obj U)) = 𝟙 _ := by rw [e1]; exact e4
    refine s1.trans ?_
    exact (Over.pullbackId_inv_app_left_fst
      ((SpacesEtale.inclusion B S hS _).obj ((representedSchemeChartFunctor X).obj U))).symm
  · exact (Over.w _).trans (Over.w _).symm

/-- **The comparison of direct images is compatible with composition.** -/
theorem representedPushforwardSquare_comp {X Y Z : BigFppfOver B S hS} (p : Y ⟶ X)
    (q : Z ⟶ Y) :
    (representedPushforwardSquare (q ≫ p)).whiskerBottom
        (smallEtaleMorphism_comp_pushforwardIso (associatedBigEtaleSite B) _ _ _
          q.left p.left).inv =
      (representedPushforwardSquare q ≫ₕ representedPushforwardSquare p).whiskerTop
        (spacesEtaleSheafPushforwardComp B S hS ((schemeSpaceFunctor B S hS).map q)
          ((schemeSpaceFunctor B S hS).map p)).hom := by
  refine TwoSquare.ext _ _ fun M => ?_
  apply ObjectProperty.hom_ext
  refine NatTrans.ext (funext fun U => ?_)
  show M.obj.map ((representedChartBaseChangeIso (q ≫ p)).hom.app U.unop).op ≫
      M.obj.map ((representedSchemeChartFunctor Z).map
        ((smallEtaleBaseChange_compIso (associatedBigEtaleSite B) _ _ _ q.left p.left).val.hom.app
          U.unop)).op =
    M.obj.map ((spacesBaseChange_comp B S hS (yonedaSpaceHom q) (yonedaSpaceHom p)).hom.app
        ((representedSchemeChartFunctor X).obj U.unop)).op ≫
      M.obj.map ((spacesBaseChange B S hS (yonedaSpaceHom q)).functor.map
        ((representedChartBaseChangeIso p).hom.app U.unop)).op ≫
      M.obj.map ((representedChartBaseChangeIso q).hom.app
        ((smallEtaleBaseChange (associatedBigEtaleSite B) p.left).obj U.unop)).op
  change Sheaf (SpacesEtale.topology B S hS (yonedaSpace B S hS Z)) (Type (u + 1)) at M
  rw [← M.obj.map_comp, ← M.obj.map_comp, ← M.obj.map_comp]
  exact congrArg (fun k => M.obj.map k.op) (representedChartBaseChangeIso_comp_app p q U.unop)

/-- **The comparison of direct images is compatible with identities.** -/
theorem representedPushforwardSquare_id (X : BigFppfOver B S hS) :
    (representedPushforwardSquare (𝟙 X)).whiskerBottom
        (letI : (smallEtaleBaseChange (associatedBigEtaleSite B) (𝟙 X.left)).IsContinuous
            (representedSchemeTopology B S hS X) (representedSchemeTopology B S hS X) :=
          smallEtaleBaseChange_isContinuous _ _
        (Functor.sheafPushforwardContinuousId'
          (smallEtaleBaseChange_idIso (associatedBigEtaleSite B) X.left) (Type (u + 1))
          (representedSchemeTopology B S hS X)).hom) =
      (TwoSquare.hId (representedRestriction X (Type (u + 1)))).whiskerTop
        (spacesEtaleSheafPushforwardId B S hS ((schemeSpaceFunctor B S hS).obj X)).hom := by
  refine TwoSquare.ext _ _ fun M => ?_
  apply ObjectProperty.hom_ext
  refine NatTrans.ext (funext fun U => ?_)
  show M.obj.map ((representedChartBaseChangeIso (𝟙 X)).hom.app U.unop).op ≫
      M.obj.map ((representedSchemeChartFunctor X).map
        ((smallEtaleBaseChange_idIso (associatedBigEtaleSite B) X.left).inv.app U.unop)).op =
    M.obj.map ((spacesBaseChange_id B S hS (yonedaSpace B S hS X)).inv.app
        ((representedSchemeChartFunctor X).obj U.unop)).op
  change Sheaf (SpacesEtale.topology B S hS (yonedaSpace B S hS X)) (Type (u + 1)) at M
  rw [← M.obj.map_comp]
  exact congrArg (fun k => M.obj.map k.op) (representedChartBaseChangeIso_id_app X U.unop)

set_option synthInstance.maxHeartbeats 400000 in
/-- **The comparison of the two pseudofunctors of inverse images on representable algebraic
spaces**: a strong transformation from the spaces-étale one to the small étale one, whose
components are the restrictions along the chart functors and whose naturality constraints are
the adjoint mates of the comparison of direct images. -/
noncomputable def representedComparison :
    (representedSpacesPseudofunctor B S hS).StrongTrans (representedSchemesPseudofunctor B S hS) :=
  @Pseudofunctor.strongTransOfLeftAdjoints _ _ _ _ (fun p ↦ representedSpacesPushforward p)
    (fun p ↦ representedSpacesAdjunction p) (fun p ↦ representedSchemesPushforward p)
    (fun p ↦ representedSchemesAdjunction p) (fun V ↦ representedRestriction V (Type (u + 1)))
    (fun p ↦ representedPushforwardSquare p) (fun V ↦ representedRestriction_isEquivalence V
        (Type (u + 1)))
    (fun p ↦ (representedPushforwardIso p (Type (u + 1))).isIso_hom)
    (fun p q ↦ by
      rw [rightAdjointComp_representedSchemesPseudofunctor,
        rightAdjointComp_representedSpacesPseudofunctor]
      exact representedPushforwardSquare_comp p q)
    (fun X ↦ by
      rw [rightAdjointId_representedSchemesPseudofunctor,
        rightAdjointId_representedSpacesPseudofunctor]
      exact representedPushforwardSquare_id X)

/-- The components of the comparison are the restrictions along the chart functors. -/
@[simp]
theorem representedComparison_app (V : BigFppfOver B S hS) :
    (representedComparison (B := B) (S := S) (hS := hS)).app (.mk (op V)) =
      Cat.Hom.ofFunctor (representedRestriction V (Type (u + 1))) :=
  rfl

variable (B S hS) in
set_option synthInstance.maxHeartbeats 400000 in
/-- **Descent along proper surjections of representable algebraic spaces is fully faithful, as
soon as it is for schemes.** If, for every proper surjection of schemes `h` of a big étale site,
the functor sending a small étale sheaf to its canonical descent datum along `h` is fully
faithful, then the pseudofunctor of spaces-étale inverse images is a prestack for every sieve
generated by a proper surjection of representable algebraic spaces.

The comparison `AlgebraicGeometry.Space.representedComparison` identifies the descent data of
the two pseudofunctors along a morphism of the big fppf site, and descent data of a restricted
pseudofunctor are those of the original one along the image of the morphism: faithfully along
the Yoneda embedding into algebraic spaces, and equivalently along the forgetful functor of the
slice, which preserves fibre products. -/
theorem properSurjectivePrestackOverSchemes_of_fullyFaithful
    (hdesc : ∀ (E : BigEtaleSite.{u}) ⦃X Y : E.Scheme⦄ (h : Y ⟶ X),
      _root_.AlgebraicGeometry.Surjective (E.inclusion.map h) →
      _root_.AlgebraicGeometry.IsProper (E.inclusion.map h) →
      Nonempty (smallEtaleSheafInverseImageDescentFunctor E h).FullyFaithful) :
    ProperSurjectivePrestackOverSchemes B S hS := by
  intro V W m hprop hsurj
  rw [Pseudofunctor.IsPrestackFor_generate_iff, Pseudofunctor.isPrestackFor_ofArrows_iff]
  show Nonempty ((spacesEtalePseudofunctor B S hS).toDescentData
    (fun _ : Unit ↦ (schemeSpaceFunctor B S hS).map m)).FullyFaithful
  let g : Unit → (W ⟶ V) := fun _ ↦ m
  -- the scheme case
  have hG : Nonempty (((smallEtaleSheafInverseImagePseudofunctor (associatedBigEtaleSite B))
      ).toDescentData (fun i ↦ (Over.forget (B.obj hS)).map (g i))).FullyFaithful :=
    hdesc (associatedBigEtaleSite B) m.left hsurj hprop
  -- along the forgetful functor of the slice, restriction of descent data is an equivalence
  have hG' : Nonempty ((representedSchemesPseudofunctor B S hS).toDescentData g).FullyFaithful := by
    have := Pseudofunctor.isEquivalence_restrictDescentData
      (smallEtaleSheafInverseImagePseudofunctor (associatedBigEtaleSite B))
      (Over.forget (B.obj hS))
      (fun i j ↦ ChosenPullback.ofHasPullback (g i) (g j))
      (fun i j ↦ (ChosenPullback.ofHasPullback (g i) (g j)).isPullback.map _)
      (fun _ _ _ ↦ ChosenPullback₃.ofHasPullbacks _ _ _)
      (fun i j k ↦ (ChosenPullback₃.ofHasPullbacks
        (ChosenPullback.ofHasPullback (g i) (g j))
        (ChosenPullback.ofHasPullback (g j) (g k))
        (ChosenPullback.ofHasPullback (g i) (g k))).isPullback₂.map _)
    exact ⟨(hG.some.comp (Functor.FullyFaithful.ofFullyFaithful _)).ofIso
      (Pseudofunctor.toDescentDataCompRestrictDescentDataIso _ _ g)⟩
  -- along the comparison of the two pseudofunctors, a fibrewise equivalence
  have hF' : Nonempty ((representedSpacesPseudofunctor B S hS).toDescentData g).FullyFaithful := by
    have : ∀ a, (representedComparison.app a).toFunctor.Faithful := fun a ↦
      (inferInstance : (representedRestriction (B := B) (S := S) (hS := hS) a.as.unop
          (Type (u + 1))).Faithful)
    have := (representedComparison (B := B) (S := S) (hS := hS)).faithful_descentDataFunctor g
    exact ⟨Functor.FullyFaithful.ofCompFaithful
      (((Functor.FullyFaithful.ofFullyFaithful (representedRestriction V
          (Type (u + 1)))).comp hG'.some).ofIso
        ((representedComparison (B := B) (S := S) (hS := hS)).toDescentDataCompDescentDataFunctorIso
          g).symm)⟩
  -- along the Yoneda embedding into algebraic spaces, restriction of descent data is faithful
  have : (Pseudofunctor.restrictDescentData (spacesEtalePseudofunctor B S hS)
      (schemeSpaceFunctor B S hS) (fun _ : Unit ↦ m)).Faithful :=
    ⟨fun {_ _} φ ψ h ↦ by ext i; exact congrArg (fun χ ↦ χ.hom i) h⟩
  exact ⟨Functor.FullyFaithful.ofCompFaithful (G := Pseudofunctor.restrictDescentData
    (spacesEtalePseudofunctor B S hS) (schemeSpaceFunctor B S hS) (fun _ : Unit ↦ m))
    (hF'.some.ofIso (Pseudofunctor.toDescentDataCompRestrictDescentDataIso _ _ _).symm)⟩

end AlgebraicGeometry.Space

end
