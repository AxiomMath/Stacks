module

public import StacksFrontier.AlgebraicGeometry.Crystalline.FCrystal
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.Formula07MKInjectives

/-!
# The pullback `F ↦ F_U` of (07MK) is restriction along change of base

The displayed equation (07MK) of [Stacks, Tag 07MJ] is written with the pullback
`F ↦ F_U : Ab(Cris(X/S)) ⥤ Ab(Cris(U/T))`, which
`Crystalline.GlobalCrystallineSituation.SmallSite.pullbackAbelianSheaf` defines as the inverse
image along the `crisMorphism` of [Stacks, Tag 07IK] — that is, through the *big* crystalline
site, as the composite `i_{X, !}`, `f_{CRIS}^{-1}`, `i_{U}^{-1}` of
`...SmallSite.crisInverseImage`.  The route (07MK) is proved along needs it in the other
presentation: plain restriction along the change-of-base functor `Cris(U/T) ⥤ Cris(X/S)` of
[Stacks, Tag 07KL], which is `...SmallSite.pullbackAbelianRestriction`.

This file identifies the two.  Nothing about localization at a sheaf is used, so this is
independent of [Stacks, Tag 0791]; the three inputs are all in the library:

* change of divided power base is **continuous** for the big crystalline topologies,
  `...changeBase_isContinuous` of [Stacks, Tag 07IC], so the sheafification in
  `CategoryTheory.Functor.sheafPullbackCocontinuous` is unnecessary and `f_{CRIS}^{-1}` is plain
  restriction, [Stacks, Tag 00XR] (1);
* the square of sites commutes **on the nose**: `smallChangeBase` is cut out of `changeBase` by
  `CategoryTheory.ObjectProperty.lift`, so `smallChangeBase ⋙ ι_{X'} = ι_U ⋙ changeBase`
  definitionally, and restriction along a composite is the composite of the restrictions,
  `CategoryTheory.Functor.sheafPushforwardContinuousComp`;
* `i_{X, !}` followed by `i_X^{-1}` is the identity, the inclusion of the small crystalline site
  being continuous, cocontinuous and fully faithful — [Stacks, Tag 00XT], as
  `CategoryTheory.Functor.isIso_unit_of_sheafPushforwardContinuous`.  This is
  `...CrystallineThickening.lowerShriekRestrictionIsoId` read at the coefficients
  `AddCommGrpCat.{u + 1}` instead of `Type (u + 1)`.

The chain is therefore

`i_{U}^{-1} ∘ f_{CRIS}^{-1} ∘ i_{X, !} ≅ i_U^{-1} ∘ ι_U^{p} ∘ i_{X, !}`
`≅ (smallChangeBase)^{p} ∘ i_X^{-1} ∘ i_{X, !} ≅ (smallChangeBase)^{p}`,

the middle step being the commuting square.

## Main definitions

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `crisInverseImageIsoSmallChangeBaseAbelianRestriction` — **the inverse image along `f_cris` of
  [Stacks, Tag 07IK] is restriction along the change-of-base functor of [Stacks, Tag 07KL]**, for
  a morphism of situations whose morphism of schemes is an open immersion, at the coefficients
  `AddCommGrpCat.{u + 1}`.
* `pullbackAbelianSheafIsoPullbackAbelianRestriction` — **the first missing input of (07MK)**: the
  pullback `F ↦ F_U` of [Stacks, Tag 07MJ] is restriction along `Cris(U/T) ⥤ Cris(X/S)`.

## References

* [Stacks Project, Tag 07MJ](https://stacks.math.columbia.edu/tag/07MJ)
* [Stacks Project, Tag 07MK](https://stacks.math.columbia.edu/tag/07MK)
* [Stacks Project, Tag 07KL](https://stacks.math.columbia.edu/tag/07KL)
* [Stacks Project, Tag 07IK](https://stacks.math.columbia.edu/tag/07IK)
* [Stacks Project, Tag 00XR](https://stacks.math.columbia.edu/tag/00XR)
* [Stacks Project, Tag 00XT](https://stacks.math.columbia.edu/tag/00XT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

section ChangeBase

variable (S S' : GlobalCrystallineSituation.{u}) (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
  (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber)
  [IsOpenImmersion g]

/-- **The commuting square of sites, at abelian coefficients**: restriction along change of
divided power base followed by restriction to the small crystalline site of `X/S` is restriction
to the small crystalline site of `X'/S'` followed by restriction along the change-of-base functor
`Cris(X/S) ⥤ Cris(X'/S')` of [Stacks, Tag 07KL].

The square of sites commutes definitionally — `smallChangeBase` is
`CategoryTheory.ObjectProperty.lift` of `ι ⋙ changeBase`, so composing it back with the inclusion
returns that functor on the nose — and restriction along a composite is the composite of the
restrictions. -/
def changeBaseAbelianRestrictionCompSmallRestrictionIso :
    (changeBase S S' f g h).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (topology S) (topology S') ⋙ smallRestriction S ≅
      smallRestriction S' ⋙ smallChangeBaseAbelianRestriction S S' f g h :=
  Functor.sheafPushforwardContinuousComp (CrystallineThickening.ι S) (changeBase S S' f g h)
      AddCommGrpCat.{u + 1} (smallTopology S) (topology S) (topology S') ≪≫
    (Functor.sheafPushforwardContinuousComp (smallChangeBase S S' f g h)
      (CrystallineThickening.ι S') AddCommGrpCat.{u + 1} (smallTopology S) (smallTopology S')
      (topology S')).symm

/-- **The abelian inverse image along `f_cris` is restriction along change of divided power
base**, when the morphism of schemes is an open immersion.

`Crystalline.GlobalCrystallineSituation.SmallSite.crisInverseImage` is built through the big
crystalline site, as `i_X^{-1} ∘ f_{CRIS}^{-1} ∘ i_{X', !}` — this is the inverse image of the
`crisMorphism` of [Stacks, Tag 07IK], whose three factors are the inclusion, change of base and
the retraction.  When the morphism of schemes is an open immersion the change-of-base functor of
[Stacks, Tag 07KL] exists on the small crystalline sites, and the composite collapses to
restriction along it: `f_{CRIS}^{-1}` is plain restriction because change of base is continuous as
well as cocontinuous ([Stacks, Tag 00XR] (1)), the square of sites commutes on the nose, and
`i_{X', !}` followed by `i_{X'}^{-1}` is the identity ([Stacks, Tag 00XT]).

So `pullbackAbelianSheaf` and `pullbackAbelianRestriction` are the same functor; see
`pullbackAbelianSheafIsoPullbackAbelianRestriction`. -/
def crisInverseImageIsoSmallChangeBaseAbelianRestriction :
    crisInverseImage S S' f g h ≅ smallChangeBaseAbelianRestriction S S' f g h :=
  haveI : IsIso (smallRestrictionAdjunction S').unit :=
    Functor.isIso_unit_of_sheafPushforwardContinuous (CrystallineThickening.ι S')
      AddCommGrpCat.{u + 1} (smallTopology S') (topology S') (smallRestrictionAdjunction S')
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight
        ((changeBase S S' f g h).sheafPullbackCocontinuousIsoSheafPushforwardContinuous
          AddCommGrpCat.{u + 1} (topology S) (topology S')) (smallRestriction S) ≪≫
      changeBaseAbelianRestrictionCompSmallRestrictionIso S S' f g h) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (asIso (smallRestrictionAdjunction S').unit).symm
      (smallChangeBaseAbelianRestriction S S' f g h) ≪≫
    Functor.leftUnitor _

end ChangeBase

/-! ### The pullback `F ↦ F_U` of (07MK) -/

section Pullback

open DividedPowerScheme

variable (S S' : GlobalCrystallineSituation.{u}) (fS : S.S ⟶ S'.S) (fX : S.X ⟶ S'.X)
  (hf : S.toClosedFiber ≫ closedFiberMap fS = fX ≫ S'.toClosedFiber)
  (A' : CrystallineThickening S')

include hf

/-- **The first missing input of the displayed equation (07MK) of [Stacks, Tag 07MJ]**: the
pullback `F ↦ F_U` the formula is written with — the inverse image along the `crisMorphism` of
[Stacks, Tag 07IK], `pullbackAbelianSheaf` — **is restriction along the change-of-base functor
`Cris(U/T) ⥤ Cris(X/S)`** of [Stacks, Tag 07KL], `pullbackAbelianRestriction`.

`U = X ×_{X'} U'` is an open subscheme of `X`, so the small-site change-of-base functor exists,
and this is `crisInverseImageIsoSmallChangeBaseAbelianRestriction` for the situation `U/T`.
Together with
`...SmallSite.preservesInjectiveObjects_pullbackAbelianRestriction` this makes the reduction of
(07MK) to an injective `F` unconditional: the pullback the formula uses carries injective abelian
sheaves to injective abelian sheaves. -/
def pullbackAbelianSheafIsoPullbackAbelianRestriction :
    pullbackAbelianSheaf S S' fS fX hf A' ≅ pullbackAbelianRestriction S S' fS fX hf A' :=
  @crisInverseImageIsoSmallChangeBaseAbelianRestriction (pullbackSituation S S' fS fX hf A') S
    (pullback.fst fS A'.obj.toBase) (pullback.fst fX A'.obj.toX)
    (pullbackSituation_comm S S' fS fX hf A')
    (isOpenImmersion_pullbackSituationToX S S' fX A')

end Pullback

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
