module

public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.AffineIndEtaleDense
public import StacksFrontier.AlgebraicGeometry.ProEtale.SiteFunctoriality.AffineIndEtaleAdjunction
public import StacksFrontier.AlgebraicGeometry.ProEtale.SiteFunctoriality.SmallBaseChange
public import StacksFrontier.CategoryTheory.Sites.CoverLifting
public import StacksFrontier.CategoryTheory.Sites.Localization.PushforwardAdjunction
public import Mathlib.CategoryTheory.Sites.LeftExact
public import StacksCore.Tactic.StacksAttribute

/-!
# Closed immersions of affine schemes and pro-étale sheaves

Let `i : Z ⟶ X` be a closed immersion of affine objects of a chosen big pro-étale site. Base
change along `i` represents a morphism of the small pro-étale topoi, and the lift of affine
ind-étale objects is a fully faithful cocontinuous left adjoint of base change on the affine
ind-étale sites. Restriction to those sites is an equivalence of topoi, so the two descriptions
agree: the morphism of topoi attached to base change is the one attached to the cocontinuous
lift.

Full faithfulness of the direct image, and invertibility of the counit
`i^{-1} i_* → id`, are read off that identification: on the affine ind-étale sites the direct
image is the right Kan extension along a fully faithful functor, hence fully faithful, and the
restriction equivalences carry this back to the small pro-étale topoi.

## Main results

* `AlgebraicGeometry.ProEtale.affineIndEtalePushforwardIso` identifies the direct image of the
  small pro-étale morphism, read through the restriction equivalences, with the direct image
  attached to the cocontinuous lift.
* `AlgebraicGeometry.ProEtale.affineIndEtaleLiftSheafPushforward_fullyFaithful`: the direct
  image attached to the lift is fully faithful.
* `AlgebraicGeometry.ProEtale.smallProetaleMorphism_pushforward_fullyFaithful_of_isAffine` and
  `AlgebraicGeometry.ProEtale.smallProetaleMorphism_counit_isIso_of_isAffine`: for a closed
  immersion of affine schemes the direct image on small pro-étale sheaves of sets is fully
  faithful and the counit of the adjunction is an isomorphism.
* `AlgebraicGeometry.ProEtale.proetaleInverseImage_sheafify_affineIndEtaleLift`: on the affine
  ind-étale site of `Z`, the inverse image of a sheaf is the sheafification of its values on
  the lift.

## Implementation notes

The identification of the two morphisms of topoi is stated for their direct images, which keeps
naturality in the sheaf; the inverse images are then identified by conjugation. The lift is only
cocontinuous, not continuous, so its direct image on sheaves is the right Kan extension along
`affineIndEtaleLift.op`, and full faithfulness is deduced from full faithfulness of that Kan
extension together with the faithfulness of the forgetful functor to presheaves.

## References

* [Stacks Project, Tag 09BL](https://stacks.math.columbia.edu/tag/09BL)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.ProEtale

variable (B : BigProetaleSite.{u}) {Z X : B.Scheme} (i : Z ⟶ X)
  [IsAffine X.obj] [IsAffine Z.obj] [IsClosedImmersion (B.inclusion.map i)]

/-- **Stacks 09BL.** The direct image of the small pro-étale morphism of a closed immersion of
affine schemes, read through the restriction equivalences to the affine ind-étale sites, is the
direct image attached to the cocontinuous lift. -/
@[stacks 09BL "topos_identification"]
def affineIndEtalePushforwardIso :
    (smallProetaleMorphism B Z X i).pushforward ⋙
      (AffineIndEtaleProetale.inclusion B X).sheafPushforwardContinuous (Type (u + 1))
        (AffineIndEtaleProetale.topology B X) (SmallProetale.topology B X.obj X.property) ≅
    (AffineIndEtaleProetale.inclusion B Z).sheafPushforwardContinuous (Type (u + 1))
        (AffineIndEtaleProetale.topology B Z) (SmallProetale.topology B Z.obj Z.property) ⋙
      (affineIndEtaleLift B i).sheafPushforwardCocontinuous (Type (u + 1))
        (AffineIndEtaleProetale.topology B Z) (AffineIndEtaleProetale.topology B X) := by
  let JZ := AffineIndEtaleProetale.topology B Z
  let JX := AffineIndEtaleProetale.topology B X
  let KZ := SmallProetale.topology B Z.obj Z.property
  let KX := SmallProetale.topology B X.obj X.property
  let aZ := AffineIndEtaleProetale.inclusion B Z
  let aX := AffineIndEtaleProetale.inclusion B X
  let sZ := SmallProetale.inclusion B Z.obj Z.property
  let sX := SmallProetale.inclusion B X.obj X.property
  let b := affineIndEtaleBaseChange B i
  let l := affineIndEtaleLift B i
  let q := smallProetaleBaseChange B Z X i
  let adj : l ⊣ b := Classical.choice (affineIndEtaleLift_adj_baseChange B i)
  letI : l.IsCocontinuous JZ JX := affineIndEtaleLift_isCocontinuous B i
  letI : b.IsContinuous JX JZ := affineIndEtaleBaseChange_isContinuous B i
  letI : q.IsContinuous KX KZ :=
    (smallProetaleBaseChange_isMorphismOfSites B Z X i).toIsContinuous
  letI : aX.IsContinuous JX KX := AffineIndEtaleProetale.inclusion_isContinuous B X
  letI : aZ.IsContinuous JZ KZ := AffineIndEtaleProetale.inclusion_isContinuous B Z
  have hAdj : l.sheafPushforwardCocontinuous (Type (u + 1)) JZ JX ≅
      b.sheafPushforwardContinuous (Type (u + 1)) JX JZ :=
    adj.sheafPushforwardCocontinuousIso (Type (u + 1))
  have hSite : aX ⋙ q ≅ b ⋙ aZ := by
    let e₁ := Classical.choice (affineIndEtaleBaseChange_comp_forget B i)
    have hq : q ⋙ sZ = sX ⋙ Over.pullback i :=
      smallProetaleBaseChange_comp_inclusion B Z X i
    have e₂ : aX ⋙ q ⋙ sZ ≅ aX ⋙ sX ⋙ Over.pullback i := by rw [hq]
    exact Functor.fullyFaithfulCancelRight sZ (e₂.trans e₁.symm)
  let eL := Functor.sheafPushforwardContinuousComp aX q (Type (u + 1)) JX KX KZ
  let eR := Functor.sheafPushforwardContinuousComp b aZ (Type (u + 1)) JX JZ KZ
  letI : (aX ⋙ q).IsContinuous JX KZ := Functor.isContinuous_comp aX q JX KX KZ
  letI : (b ⋙ aZ).IsContinuous JX KZ := Functor.isContinuous_comp b aZ JX JZ KZ
  let eSite := Functor.sheafPushforwardContinuousIso hSite (Type (u + 1)) JX KZ
  let result := eL.trans (eSite.trans (eR.symm.trans (Functor.isoWhiskerLeft
    (aZ.sheafPushforwardContinuous (Type (u + 1)) JZ KZ) hAdj.symm)))
  simpa [smallProetaleMorphism, aX, q, JX, KX, KZ] using result

/-- **Stacks 09BL.** The direct image on the affine ind-étale sites attached to the cocontinuous
lift of a closed immersion of affine schemes is fully faithful. -/
def affineIndEtaleLiftSheafPushforward_fullyFaithful :
    ((affineIndEtaleLift B i).sheafPushforwardCocontinuous (Type (u + 1))
        (AffineIndEtaleProetale.topology B Z)
        (AffineIndEtaleProetale.topology B X)).FullyFaithful := by
  classical
  let l := affineIndEtaleLift B i
  let J₁ := AffineIndEtaleProetale.topology B Z
  let J₂ := AffineIndEtaleProetale.topology B X
  let I₂ := sheafToPresheaf J₂ (Type (u + 1))
  let L := l.op.ranAdjunction (Type (u + 1))
  have hl : l.FullyFaithful := Classical.choice (affineIndEtaleLift_fullyFaithful B i)
  have hL : l.op.FullyFaithful := hl.op
  letI : l.op.Full := hL.full
  letI : l.op.Faithful := hL.faithful
  letI : IsIso L.counit := inferInstance
  have hRan : l.op.ran.FullyFaithful := L.fullyFaithfulROfIsIsoCounit
  letI : I₂.Faithful := (fullyFaithfulSheafToPresheaf J₂ (Type (u + 1))).faithful
  exact Functor.FullyFaithful.ofCompFaithful (G := I₂)
    (((fullyFaithfulSheafToPresheaf J₁ (Type (u + 1))).comp hRan).ofIso
      (l.sheafPushforwardCocontinuousCompSheafToPresheafIso (Type (u + 1)) J₁ J₂).symm)

/-- **Stacks 09BL.** For a closed immersion of affine schemes, the direct image on small
pro-étale sheaves of sets is fully faithful. -/
def smallProetaleMorphism_pushforward_fullyFaithful_of_isAffine :
    (smallProetaleMorphism B Z X i).pushforward.FullyFaithful := by
  classical
  let jZ := (AffineIndEtaleProetale.inclusion B Z).sheafPushforwardContinuous (Type (u + 1))
    (AffineIndEtaleProetale.topology B Z) (SmallProetale.topology B Z.obj Z.property)
  let jX := (AffineIndEtaleProetale.inclusion B X).sheafPushforwardContinuous (Type (u + 1))
    (AffineIndEtaleProetale.topology B X) (SmallProetale.topology B X.obj X.property)
  let lStar := (affineIndEtaleLift B i).sheafPushforwardCocontinuous (Type (u + 1))
    (AffineIndEtaleProetale.topology B Z) (AffineIndEtaleProetale.topology B X)
  let M := smallProetaleMorphism B Z X i
  letI : jZ.IsEquivalence := AffineIndEtaleProetale.isEquivalence_restriction.{u, u + 1} B Z
  letI : jX.IsEquivalence := AffineIndEtaleProetale.isEquivalence_restriction.{u, u + 1} B X
  letI : lStar.FullyFaithful := affineIndEtaleLiftSheafPushforward_fullyFaithful B i
  have hTop : M.pushforward ⋙ jX ≅ jZ ⋙ lStar := affineIndEtalePushforwardIso B i
  exact Functor.FullyFaithful.ofCompFaithful (G := jX)
    (((Functor.FullyFaithful.ofFullyFaithful jZ).comp ‹lStar.FullyFaithful›).ofIso hTop.symm)

/-- **Stacks 09BL.** For a closed immersion of affine schemes, the counit
`i^{-1} i_* → id` of the small pro-étale adjunction is an isomorphism. -/
@[stacks 09BL "pushforward_counit"]
theorem smallProetaleMorphism_counit_isIso_of_isAffine :
    IsIso (smallProetaleMorphism B Z X i).adj.counit := by
  let hPush := smallProetaleMorphism_pushforward_fullyFaithful_of_isAffine B i
  have : (smallProetaleMorphism B Z X i).pushforward.Full := hPush.full
  have : (smallProetaleMorphism B Z X i).pushforward.Faithful := hPush.faithful
  exact Adjunction.counit_isIso_of_R_fully_faithful
    (h := (smallProetaleMorphism B Z X i).adj)

/-- **Stacks 09BL.** For a closed immersion of affine schemes, the inverse image of a small
pro-étale sheaf, restricted to the affine ind-étale site of `Z`, is the sheafification of the
presheaf of its values on the lift, naturally in the sheaf. -/
@[stacks 09BL "inverse_image_formula"]
def proetaleInverseImage_sheafify_affineIndEtaleLift :
    (smallProetaleMorphism B Z X i).inverseImage ⋙
        (AffineIndEtaleProetale.inclusion B Z).sheafPushforwardContinuous (Type (u + 1))
          (AffineIndEtaleProetale.topology B Z) (SmallProetale.topology B Z.obj Z.property) ≅
      sheafToPresheaf (SmallProetale.topology B X.obj X.property) (Type (u + 1)) ⋙
        (Functor.whiskeringLeft (AffineIndEtaleProetale B Z)ᵒᵖ
          (SmallProetale B X.obj X.property)ᵒᵖ (Type (u + 1))).obj
            (affineIndEtaleLift B i ⋙ AffineIndEtaleProetale.inclusion B X).op ⋙
        presheafToSheaf (AffineIndEtaleProetale.topology B Z) (Type (u + 1)) := by
  classical
  let SX := SmallProetale B X.obj X.property
  let AZ := AffineIndEtaleProetale B Z
  let AX := AffineIndEtaleProetale B X
  let KZ := SmallProetale.topology B Z.obj Z.property
  let KX := SmallProetale.topology B X.obj X.property
  let JZ := AffineIndEtaleProetale.topology B Z
  let JX := AffineIndEtaleProetale.topology B X
  let aZ := AffineIndEtaleProetale.inclusion B Z
  let aX := AffineIndEtaleProetale.inclusion B X
  let l := affineIndEtaleLift B i
  let M := smallProetaleMorphism B Z X i
  let jZ := aZ.sheafPushforwardContinuous (Type (u + 1)) JZ KZ
  let jX := aX.sheafPushforwardContinuous (Type (u + 1)) JX KX
  letI : jZ.IsEquivalence := AffineIndEtaleProetale.isEquivalence_restriction.{u, u + 1} B Z
  letI : jX.IsEquivalence := AffineIndEtaleProetale.isEquivalence_restriction.{u, u + 1} B X
  let eZ : Sheaf KZ (Type (u + 1)) ≌ Sheaf JZ (Type (u + 1)) := jZ.asEquivalence
  let eX : Sheaf KX (Type (u + 1)) ≌ Sheaf JX (Type (u + 1)) := jX.asEquivalence
  let k := (Functor.whiskeringLeft AZᵒᵖ SXᵒᵖ (Type (u + 1))).obj (l ⋙ aX).op
  let g := sheafToPresheaf KX (Type (u + 1)) ⋙ k ⋙ presheafToSheaf JZ (Type (u + 1))
  letI : l.IsCocontinuous JZ JX := affineIndEtaleLift_isCocontinuous B i
  let gStar := l.sheafPushforwardCocontinuous (Type (u + 1)) JZ JX
  let gInv := sheafToPresheaf JX (Type (u + 1)) ⋙
    (Functor.whiskeringLeft AZᵒᵖ AXᵒᵖ (Type (u + 1))).obj l.op ⋙
    presheafToSheaf JZ (Type (u + 1))
  let adjLeft : (M.inverseImage ⋙ jZ) ⊣ (eZ.inverse ⋙ M.pushforward) :=
    M.adj.comp eZ.toAdjunction
  let adjX : jX ⊣ eX.inverse := eX.toAdjunction
  let adjLift : gInv ⊣ gStar := Adjunction.restrictFullyFaithful
    ((l.op.ranAdjunction (Type (u + 1))).comp (sheafificationAdjunction JZ (Type (u + 1))))
    (fullyFaithfulSheafToPresheaf JX (Type (u + 1)))
    (Functor.FullyFaithful.id _)
    (Functor.rightUnitor _).symm
    ((Functor.leftUnitor _).trans
      (l.sheafPushforwardCocontinuousCompSheafToPresheafIso (Type (u + 1)) JZ JX).symm)
  let adjRight : (jX ⋙ gInv) ⊣ (gStar ⋙ eX.inverse) := adjX.comp adjLift
  have hRight : (eZ.inverse ⋙ M.pushforward) ≅ (gStar ⋙ eX.inverse) := by
    let hTop := affineIndEtalePushforwardIso B i
    calc
      eZ.inverse ⋙ M.pushforward ≅ eZ.inverse ⋙ M.pushforward ⋙ jX ⋙ eX.inverse :=
        Functor.isoWhiskerLeft eZ.inverse (Functor.isoWhiskerLeft M.pushforward eX.unitIso)
      _ ≅ eZ.inverse ⋙ (M.pushforward ⋙ jX) ⋙ eX.inverse :=
        Functor.isoWhiskerRight (Functor.associator eZ.inverse M.pushforward jX) eX.inverse
      _ ≅ eZ.inverse ⋙ (jZ ⋙ gStar) ⋙ eX.inverse :=
        Functor.isoWhiskerRight (Functor.isoWhiskerLeft eZ.inverse hTop) eX.inverse
      _ ≅ (eZ.inverse ⋙ jZ) ⋙ gStar ⋙ eX.inverse :=
        Functor.isoWhiskerRight (Functor.associator eZ.inverse jZ gStar).symm eX.inverse
      _ ≅ (eZ.inverse ⋙ jZ) ⋙ (gStar ⋙ eX.inverse) :=
        Functor.associator (eZ.inverse ⋙ jZ) gStar eX.inverse
      _ ≅ (𝟭 (Sheaf JZ (Type (u + 1))) ⋙ (gStar ⋙ eX.inverse)) :=
        Functor.isoWhiskerRight eZ.counitIso (gStar ⋙ eX.inverse)
      _ ≅ gStar ⋙ eX.inverse := Functor.leftUnitor _
  have adjRight' : (jX ⋙ gInv) ⊣ (eZ.inverse ⋙ M.pushforward) :=
    adjRight.ofNatIsoRight hRight.symm
  have hFunctor : jX ⋙ gInv ≅ g := by
    dsimp [jX, gInv, g, k, JX, KX, JZ, aX, AX, SX]
    rfl
  exact (Adjunction.leftAdjointUniq adjLeft adjRight').trans hFunctor

end AlgebraicGeometry.ProEtale

end
