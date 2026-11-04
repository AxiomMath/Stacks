module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedSiteBaseChangeComposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedSiteBaseChangeRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedSiteSectionPullbackTransfer
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.CompGerm
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.InverseImageSectionsColimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SystemPullbackComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.LimitCategory.StageLeg

/-!
# The legs of sections on the two presentations of the small étale site

This file compares the leg `g⁻¹G ⟶ f_* h⁻¹G` of `AlgebraicGeometry.smallEtaleStageLeg`, built on
the small étale site of Stacks 021B, with the corresponding leg on Mathlib's small étale site,
whose effect on sections is `Stacks.EtaleCohomology.pullbackSectionsMap`. For abelian sheaves the
two agree through the comparisons of inverse images along the restriction functors,
`AlgebraicGeometry.SmallEtale.restrictionPullbackBaseChangeIso`, and of direct images,
`AlgebraicGeometry.SmallEtale.toEtaleSitePushforwardBaseChangeIso`.

Both legs are characterized by unit equations, so the comparison is an instance of
`CategoryTheory.Adjunction.unitCharacterized_transport`; its inputs are the two unit equations, the
mate identities of the comparisons of inverse images, and the compatibility of the comparisons of
direct images with composition, which is the site-level
`AlgebraicGeometry.SmallEtale.toEtaleSiteBaseChangeIso_hom_app_comp'`.

## Main definitions

* `Stacks.EtaleCohomology.smallEtaleAbStageLeg` — the leg on Mathlib's small étale site.

## Main results

* `Stacks.EtaleCohomology.unit_comp_map_smallEtaleAbStageLeg` — its unit equation.
* `AlgebraicGeometry.SmallEtale.smallEtaleStageLeg_restriction` — the comparison of the two legs.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

variable {X Y Z : Scheme.{u}} (g : X ⟶ Y) (f : Y ⟶ Z) (gf : X ⟶ Z) (hgf : gf = g ≫ f)

/-- **The leg of sections on Mathlib's small étale site.** The unit of `g⁻¹ ⊣ g_*` at `f⁻¹H`
followed by `g_*` of the comparison `g⁻¹f⁻¹H ≅ (gf)⁻¹H`; on sections it is
`Stacks.EtaleCohomology.pullbackSectionsMap`. -/
def smallEtaleAbStageLeg (H : Sheaf (smallEtaleTopology Z) Ab.{u + 1}) :
    (smallEtalePullbackAb f).obj H ⟶
      (smallEtalePushforwardAb g).obj ((smallEtalePullbackAb gf).obj H) :=
  (smallEtaleAdjunctionAb g).unit.app _ ≫
    (smallEtalePushforwardAb g).map ((smallEtalePullbackAbComp' g f gf hgf).hom.app H)

/-- On sections the leg is `Stacks.EtaleCohomology.pullbackSectionsMap`. -/
theorem smallEtaleAbStageLeg_hom_app (H : Sheaf (smallEtaleTopology Z) Ab.{u + 1}) (U : Y.Etale) :
    (smallEtaleAbStageLeg g f gf hgf H).hom.app (op U) = pullbackSectionsMap g f gf hgf H U :=
  rfl

/-- **The unit equation characterizing the leg on Mathlib's small étale site.** -/
theorem unit_comp_map_smallEtaleAbStageLeg (H : Sheaf (smallEtaleTopology Z) Ab.{u + 1}) :
    (smallEtaleAdjunctionAb f).unit.app H ≫
        (smallEtalePushforwardAb f).map (smallEtaleAbStageLeg g f gf hgf H) =
      (smallEtaleAdjunctionAb gf).unit.app H ≫
        (smallEtalePushforwardAbComp' g f gf hgf).inv.app ((smallEtalePullbackAb gf).obj H) := by
  simp only [smallEtaleAbStageLeg, smallEtalePullbackAbComp'_eq_leftAdjointCompIso]
  exact Adjunction.unit_comp_map_leftAdjointCompIso_hom _ _ _ _ H

end Stacks.EtaleCohomology

namespace AlgebraicGeometry.SmallEtale

open Stacks.EtaleCohomology

variable (B : BigEtaleSite.{u})
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (topology B S.obj S.property) (topology B T.obj T.property)).IsRightAdjoint]

/-- Restriction of abelian sheaves along the embedding of the small étale site of Stacks 021B
into Mathlib's. -/
abbrev abRestriction (S : B.Scheme) :
    Sheaf S.obj.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf (topology B S.obj S.property) AddCommGrpCat.{u + 1} :=
  (toEtaleSite B S.obj S.property).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (topology B S.obj S.property) S.obj.smallEtaleTopology

/-- The comparison of inverse images of abelian sheaves along the restriction functors, for the
inverse images of `AlgebraicGeometry.smallEtaleSheafPullback` and
`Stacks.EtaleCohomology.smallEtalePullbackAb`. -/
abbrev abRestrictionPullbackIso {S T : B.Scheme} (f : T ⟶ S) :
    abRestriction B S ⋙ smallEtaleSheafPullback B AddCommGrpCat.{u + 1} f ≅
      smallEtalePullbackAb (B.inclusion.map f) ⋙ abRestriction B T :=
  restrictionPullbackBaseChangeIso B AddCommGrpCat.{u + 1} f
    (smallEtaleAdjunctionAb (B.inclusion.map f))
    (smallEtaleSheafAdjunction B AddCommGrpCat.{u + 1} f)

/-- **The unit equation of the comparison of inverse images along the restriction functors.** -/
theorem unit_comp_map_abRestrictionPullbackIso_hom {S T : B.Scheme} (f : T ⟶ S)
    (H : Sheaf S.obj.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (smallEtaleSheafAdjunction B AddCommGrpCat.{u + 1} f).unit.app ((abRestriction B S).obj H) ≫
        (smallEtaleSheafPushforward B AddCommGrpCat.{u + 1} f).map
          ((abRestrictionPullbackIso B f).hom.app H) =
      (abRestriction B S).map ((smallEtaleAdjunctionAb (B.inclusion.map f)).unit.app H) ≫
        (toEtaleSitePushforwardBaseChangeIso B f AddCommGrpCat.{u + 1}).hom.app
          ((smallEtalePullbackAb (B.inclusion.map f)).obj H) := by
  have h := unit_mateEquiv (smallEtaleAdjunctionAb (B.inclusion.map f))
    (smallEtaleSheafAdjunction B AddCommGrpCat.{u + 1} f)
    (restrictionPullbackBaseChange B AddCommGrpCat.{u + 1} f
      (smallEtaleAdjunctionAb (B.inclusion.map f))
      (smallEtaleSheafAdjunction B AddCommGrpCat.{u + 1} f)) H
  have hm := NatTrans.congr_app (mateEquiv_restrictionPullbackBaseChange B AddCommGrpCat.{u + 1} f
    (smallEtaleAdjunctionAb (B.inclusion.map f))
    (smallEtaleSheafAdjunction B AddCommGrpCat.{u + 1} f))
    ((smallEtalePullbackAb (B.inclusion.map f)).obj H)
  exact h.symm.trans (congrArg (_ ≫ ·) hm)

/-- The inverse of the comparison of direct images along a composite, on sections. -/
theorem smallEtalePushforwardAbComp'_inv_app_hom_app {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) (fg : X ⟶ Z) (hfg : fg = f ≫ g)
    (F : Sheaf (smallEtaleTopology X) Ab.{u + 1}) (U : (Z.Etale)ᵒᵖ) :
    ((smallEtalePushforwardAbComp' f g fg hfg).inv.app F).hom.app U =
      F.obj.map (Opposite.op ((smallEtaleBaseChangeComp' f g fg hfg).inv.app U.unop)) :=
  Category.comp_id _

omit [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (topology B S.obj S.property) (topology B T.obj T.property)).IsRightAdjoint] in
/-- Restriction along the embedding, on sections of a morphism. -/
theorem abRestriction_map_hom_app {S : B.Scheme}
    {K K' : Sheaf S.obj.smallEtaleTopology AddCommGrpCat.{u + 1}} (φ : K ⟶ K')
    (V : SmallEtale B S.obj S.property) :
    ((abRestriction B S).map φ).hom.app (op V) =
      φ.hom.app (op ((toEtaleSite B S.obj S.property).obj V)) :=
  rfl

omit [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (topology B S.obj S.property) (topology B T.obj T.property)).IsRightAdjoint] in
/-- Direct image on the bounded site, on sections of a morphism. -/
theorem smallEtaleSheafPushforward_map_hom_app {S T : B.Scheme} (g : T ⟶ S)
    {K K' : Sheaf (topology B T.obj T.property) AddCommGrpCat.{u + 1}} (φ : K ⟶ K')
    (V : SmallEtale B S.obj S.property) :
    ((smallEtaleSheafPushforward B AddCommGrpCat.{u + 1} g).map φ).hom.app (op V) =
      φ.hom.app (op ((AlgebraicGeometry.smallEtaleBaseChange B g).obj V)) :=
  rfl

/-- **The comparisons of direct images along the restriction functors are compatible with
composition.** -/
theorem abRestriction_pushforwardComp_compat {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : X ⟶ Z) (e : f ≫ g = h) (K : Sheaf X.obj.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (abRestriction B Z).map ((smallEtalePushforwardAbComp' (B.inclusion.map f)
        (B.inclusion.map g) (B.inclusion.map h)
        ((congrArg B.inclusion.map e).symm.trans (B.inclusion.map_comp f g))).inv.app K) ≫
      (toEtaleSitePushforwardBaseChangeIso B g AddCommGrpCat.{u + 1}).hom.app
        (((Stacks.EtaleCohomology.smallEtaleBaseChange
            (B.inclusion.map f)).sheafPushforwardContinuous
          AddCommGrpCat.{u + 1} Y.obj.smallEtaleTopology X.obj.smallEtaleTopology).obj K) ≫
      (smallEtaleSheafPushforward B AddCommGrpCat.{u + 1} g).map
        ((toEtaleSitePushforwardBaseChangeIso B f AddCommGrpCat.{u + 1}).hom.app K) =
    (toEtaleSitePushforwardBaseChangeIso B h AddCommGrpCat.{u + 1}).hom.app K ≫
      (smallEtalePushforwardCompHom B AddCommGrpCat.{u + 1} f g h e).app
        ((abRestriction B X).obj K) := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun U => ?_))
  induction U with | op V => ?_
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    abRestriction_map_hom_app, smallEtalePushforwardAbComp'_inv_app_hom_app,
    toEtaleSitePushforwardBaseChangeIso_hom_app_app,
    smallEtalePushforwardCompHom, AlgebraicGeometry.sheafPushforwardContinuousComp'_inv_app_hom_app]
  have hmor : (toEtaleSiteBaseChangeIso B f).hom.app
        ((AlgebraicGeometry.smallEtaleBaseChange B g).obj V) ≫
      (Stacks.EtaleCohomology.smallEtaleBaseChange (B.inclusion.map f)).map
        ((toEtaleSiteBaseChangeIso B g).hom.app V) ≫
      (smallEtaleBaseChangeComp' (B.inclusion.map f) (B.inclusion.map g) (B.inclusion.map h)
        ((congrArg B.inclusion.map e).symm.trans (B.inclusion.map_comp f g))).inv.app
        ((toEtaleSite B Z.obj Z.property).obj V) =
      (toEtaleSite B X.obj X.property).map
          ((smallEtaleBaseChange_factoredCompIso B X Y Z f g h e).hom.app V) ≫
        (toEtaleSiteBaseChangeIso B h).hom.app V := by
    rw [toEtaleSiteBaseChangeIso_hom_app_comp' B f g h e.symm V]
    simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app]
    exact ((congrArg (· ≫ _) ((toEtaleSite B X.obj X.property).map_id _)).trans
      (Category.id_comp _)).symm
  have hmid : ((toEtaleSitePushforwardBaseChangeIso B g AddCommGrpCat.{u + 1}).hom.app
        (((Stacks.EtaleCohomology.smallEtaleBaseChange
            (B.inclusion.map f)).sheafPushforwardContinuous
          AddCommGrpCat.{u + 1} Y.obj.smallEtaleTopology X.obj.smallEtaleTopology).obj K) ≫
      (smallEtaleSheafPushforward B AddCommGrpCat.{u + 1} g).map
        ((toEtaleSitePushforwardBaseChangeIso B f AddCommGrpCat.{u + 1}).hom.app K)).hom.app
          (op V) =
      K.obj.map ((Stacks.EtaleCohomology.smallEtaleBaseChange (B.inclusion.map f)).map
          ((toEtaleSiteBaseChangeIso B g).hom.app V)).op ≫
        K.obj.map ((toEtaleSiteBaseChangeIso B f).hom.app
          ((AlgebraicGeometry.smallEtaleBaseChange B g).obj V)).op :=
    congrArg₂ (· ≫ ·) (toEtaleSitePushforwardBaseChangeIso_hom_app_app B g _ V)
      (toEtaleSitePushforwardBaseChangeIso_hom_app_app B f K _)
  refine (congrArg (K.obj.map _ ≫ ·) hmid).trans ?_
  have hK := congrArg (fun m => K.obj.map m.op) hmor
  simp only [op_comp, Functor.map_comp, Category.assoc] at hK
  exact hK

/-- **The legs of sections on the two presentations of the small étale site agree.** For
`f ≫ g = h` in a big étale site and an abelian sheaf `H` on Mathlib's small étale site of `Z`, the
leg `g⁻¹ρH ⟶ f_* h⁻¹ρH` of the bounded presentation, read through the comparisons of inverse
images along the restriction functors `ρ`, is the restriction of the leg of Mathlib's
presentation, read through the comparison of direct images. -/
theorem smallEtaleStageLeg_restriction {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
    (e : f ≫ g = h) (H : Sheaf Z.obj.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (abRestrictionPullbackIso B g).hom.app H ≫
        (abRestriction B Y).map (smallEtaleAbStageLeg (B.inclusion.map f) (B.inclusion.map g)
          (B.inclusion.map h) ((congrArg B.inclusion.map e).symm.trans (B.inclusion.map_comp f g))
          H) ≫
        (toEtaleSitePushforwardBaseChangeIso B f AddCommGrpCat.{u + 1}).hom.app
          ((smallEtalePullbackAb (B.inclusion.map h)).obj H) =
      smallEtaleStageLeg B AddCommGrpCat.{u + 1} f g h e ((abRestriction B Z).obj H) ≫
        (smallEtaleSheafPushforward B AddCommGrpCat.{u + 1} f).map
          ((abRestrictionPullbackIso B h).hom.app H) :=
  Adjunction.unitCharacterized_transport (smallEtaleSheafAdjunction B AddCommGrpCat.{u + 1} g)
    (smallEtaleSheafAdjunction B AddCommGrpCat.{u + 1} h)
    (smallEtalePushforwardCompHom B AddCommGrpCat.{u + 1} f g h e)
    (smallEtaleAdjunctionAb (B.inclusion.map g)) (smallEtaleAdjunctionAb (B.inclusion.map h))
    (smallEtalePushforwardAbComp' (B.inclusion.map f) (B.inclusion.map g) (B.inclusion.map h)
      ((congrArg B.inclusion.map e).symm.trans (B.inclusion.map_comp f g))).inv
    (abRestriction B Z) (abRestriction B Y) (abRestriction B X)
    (toEtaleSitePushforwardBaseChangeIso B g AddCommGrpCat.{u + 1}).hom
    (toEtaleSitePushforwardBaseChangeIso B h AddCommGrpCat.{u + 1}).hom
    (toEtaleSitePushforwardBaseChangeIso B f AddCommGrpCat.{u + 1}).hom
    (smallEtaleStageLeg B AddCommGrpCat.{u + 1} f g h e)
    (unit_comp_map_smallEtaleStageLeg B AddCommGrpCat.{u + 1} f g h e)
    (smallEtaleAbStageLeg (B.inclusion.map f) (B.inclusion.map g) (B.inclusion.map h)
      ((congrArg B.inclusion.map e).symm.trans (B.inclusion.map_comp f g)))
    (unit_comp_map_smallEtaleAbStageLeg _ _ _ _)
    (fun H => (abRestrictionPullbackIso B g).hom.app H)
    (unit_comp_map_abRestrictionPullbackIso_hom B g)
    (fun H => (abRestrictionPullbackIso B h).hom.app H)
    (unit_comp_map_abRestrictionPullbackIso_hom B h)
    (abRestriction_pushforwardComp_compat B f g h e) H

end AlgebraicGeometry.SmallEtale
