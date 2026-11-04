module

public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleToposMorphism
public import StacksFrontier.CategoryTheory.Sites.Continuous.PullbackOfRepresentable
public import StacksFrontier.CategoryTheory.Sites.Modules.InverseImage.AbelianSheaf

/-!
# Inverse image along a morphism of small étale topoi

A morphism `f : X ⟶ Y` of algebraic spaces over `S` induces a morphism of small étale topoi
(Stacks 03G2, part (3)), whose inverse image is the pullback of small étale sheaves. This file
records its exactness, for sheaves of sets and for sheaves of abelian groups, and computes it
on representable sheaves.

## Main definitions

* `AlgebraicGeometry.Space.abelianPullback`: the inverse image of ordinary sheaves of abelian
  groups on the small étale sites.

## Main results

* `AlgebraicGeometry.Space.smallEtaleInverseImage_exact` and
  `AlgebraicGeometry.Space.abelianPullback_exact`: pullback along `f` is exact, on sheaves of
  sets and on sheaves of abelian groups.
* `AlgebraicGeometry.Space.smallEtalePullbackRepresentableNatIso`: the inverse image of a
  representable small étale sheaf is represented by the cartesian base change, naturally in
  the representing étale algebraic space.

## Implementation notes

Exactness is `CategoryTheory.Limits.exactFunctor`, which packages preservation of finite
limits and finite colimits. For sheaves of sets both halves are properties of any morphism of
topoi: left exactness is part of the structure, and right exactness holds because the inverse
image is a left adjoint. For sheaves of abelian groups the inverse image is the canonical one
of Stacks 04JC — geometric inverse image applied to the internal group objects — and its
exactness is that tag's, specialized to the morphism of topoi of Stacks 03G2.

The computation on representable sheaves is transported from the spaces-étale site, where it
is Stacks 04D3 for the cartesian base-change functor. The transport is by uniqueness of left
adjoints: the inverse image of `AlgebraicGeometry.Space.smallToposMorphism` is, through the
comparison equivalences of Stacks 03G1, a left adjoint of the spaces-étale direct image, hence
canonically isomorphic to the spaces-étale inverse image. No `eqToHom` algebra appears, since
the comparison direction used is `AlgebraicGeometry.Space.smallToposMorphism_comparison`.

## References

* [Stacks Project, Tag 04K2](https://stacks.math.columbia.edu/tag/04K2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- The inverse image of ordinary sheaves of abelian groups along the morphism of small étale
topoi induced by a morphism `f : X ⟶ Y` of algebraic spaces. -/
noncomputable abbrev abelianPullback :
    Sheaf (SmallEtale.topology B S hS Y.1) AddCommGrpCat.{u + 1} ⥤
      Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1} :=
  Sites.abelianInverseImage (smallToposMorphism B S hS f)

/-- **Stacks 04K2.** Pullback of sheaves of abelian groups along a morphism of algebraic
spaces is exact on the small étale sites. -/
@[stacks 04K2 "abelian_pullback_exact"]
theorem abelianPullback_exact :
    exactFunctor
      (Sheaf (SmallEtale.topology B S hS Y.1) AddCommGrpCat.{u + 1})
      (Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1})
      (abelianPullback B S hS f) :=
  Sites.abelianInverseImage_exact (smallToposMorphism B S hS f)

/-- **Stacks 04K2.** The inverse image of the small étale sheaf represented by an algebraic
space `V` étale over `Y` is the sheaf represented by the cartesian base change `X ×_Y V`,
naturally in `V`.

An algebraic space étale over `Y` need not be a scheme, so the sheaf it represents on the
small étale site is its sheafified Yoneda presheaf on the spaces-étale site, restricted along
the comparison functor of Stacks 03G1. -/
@[stacks 04K2 "representable_pullback"]
noncomputable def smallEtalePullbackRepresentableNatIso :
    (yoneda ⋙ presheafToSheaf (SpacesEtale.topology B S hS Y) (Type (u + 1)) ⋙
      (comparisonFunctor B S hS Y).sheafPushforwardContinuous (Type (u + 1))
        (SmallEtale.topology B S hS Y.1) (SpacesEtale.topology B S hS Y) ⋙
      (smallToposMorphism B S hS f).inverseImage) ≅
    ((spacesBaseChange B S hS f).functor ⋙ yoneda ⋙
      presheafToSheaf (SpacesEtale.topology B S hS X) (Type (u + 1)) ⋙
      (comparisonFunctor B S hS X).sheafPushforwardContinuous (Type (u + 1))
        (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X)) := by
  let cY := comparisonFunctor B S hS Y
  let cX := comparisonFunctor B S hS X
  let cYstar := cY.sheafPushforwardContinuous (Type (u + 1))
    (SmallEtale.topology B S hS Y.1) (SpacesEtale.topology B S hS Y)
  let cXstar := cX.sheafPushforwardContinuous (Type (u + 1))
    (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X)
  let cYpull := cY.sheafPullback (Type (u + 1))
    (SmallEtale.topology B S hS Y.1) (SpacesEtale.topology B S hS Y)
  let cXpull := cX.sheafPullback (Type (u + 1))
    (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X)
  let uBC := (spacesBaseChange B S hS f).functor
  have : uBC.IsContinuous (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X) :=
    (spacesBaseChange_isMorphismOfSites B S hS f).isContinuous
  let uPull := uBC.sheafPullback (Type (u + 1))
    (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X)
  let uStar := uBC.sheafPushforwardContinuous (Type (u + 1))
    (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X)
  have : cYstar.IsEquivalence := comparisonFunctor_sheafEquivalence B S hS Y (Type (u + 1))
  have : cXstar.IsEquivalence := comparisonFunctor_sheafEquivalence B S hS X (Type (u + 1))
  let adjY := cY.sheafAdjunctionContinuous (Type (u + 1))
    (SmallEtale.topology B S hS Y.1) (SpacesEtale.topology B S hS Y)
  let adjX := cX.sheafAdjunctionContinuous (Type (u + 1))
    (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X)
  let eqY := cYstar.asEquivalence
  let eqYInvIso : eqY.inverse ≅ cYpull :=
    Adjunction.leftAdjointUniq eqY.symm.toAdjunction adjY
  let adjYRev := eqY.toAdjunction.ofNatIsoRight eqYInvIso
  let cYCounit : cYstar ⋙ cYpull ≅ 𝟭 _ := (asIso adjYRev.unit).symm
  let cXUnit : 𝟭 _ ≅ cXpull ⋙ cXstar := asIso adjX.unit
  let adjF := (smallToposMorphism B S hS f).adj
  let fStar := (smallToposMorphism B S hS f).pushforward
  let adjLeft := (adjYRev.comp adjF).comp adjX
  let directComparison := smallToposMorphism_comparison B S hS f
  let rightComparison : cXstar ⋙ (fStar ⋙ cYpull) ≅ uStar :=
    (Functor.associator cXstar fStar cYpull).symm ≪≫
      Functor.isoWhiskerRight directComparison cYpull ≪≫
      Functor.associator uStar cYstar cYpull ≪≫
      Functor.isoWhiskerLeft uStar cYCounit ≪≫
      Functor.rightUnitor uStar
  let adjLeftToSpaces := adjLeft.ofNatIsoRight rightComparison
  let adjU := uBC.sheafAdjunctionContinuous (Type (u + 1))
    (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X)
  let coreInverseComparison := Adjunction.leftAdjointUniq adjLeftToSpaces adjU
  let inverseComparison :
      cYstar ⋙ (smallToposMorphism B S hS f).inverseImage ≅ uPull ⋙ cXstar :=
    (Functor.rightUnitor (cYstar ⋙ (smallToposMorphism B S hS f).inverseImage)).symm ≪≫
      Functor.isoWhiskerLeft
        (cYstar ⋙ (smallToposMorphism B S hS f).inverseImage) cXUnit ≪≫
      Functor.associator cYstar (smallToposMorphism B S hS f).inverseImage
        (cXpull ⋙ cXstar) ≪≫
      Functor.isoWhiskerRight coreInverseComparison cXstar
  let representablePullback :
      yoneda ⋙ presheafToSheaf (SpacesEtale.topology B S hS Y) (Type (u + 1)) ⋙ uPull ≅
        uBC ⋙ yoneda ⋙ presheafToSheaf (SpacesEtale.topology B S hS X) (Type (u + 1)) :=
    Classical.choice (sheafPullback_sheafify_yoneda_natIso uBC
      (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X))
  exact
    Functor.associator
        (yoneda ⋙ presheafToSheaf (SpacesEtale.topology B S hS Y) (Type (u + 1))) cYstar
        (smallToposMorphism B S hS f).inverseImage ≪≫
      Functor.isoWhiskerLeft
        (yoneda ⋙ presheafToSheaf (SpacesEtale.topology B S hS Y) (Type (u + 1)))
        inverseComparison ≪≫
      (Functor.associator
        (yoneda ⋙ presheafToSheaf (SpacesEtale.topology B S hS Y) (Type (u + 1)))
        uPull cXstar).symm ≪≫
      Functor.isoWhiskerRight representablePullback cXstar

/-- **Stacks 04K2.** Pullback of sheaves of sets along a morphism of algebraic spaces is exact
on the small étale sites. -/
@[stacks 04K2 "sheaf_pullback_exact"]
theorem smallEtaleInverseImage_exact :
    exactFunctor _ _ (smallToposMorphism B S hS f).inverseImage := by
  rw [exactFunctor_iff]
  refine ⟨(smallToposMorphism B S hS f).preservesFiniteLimits, ?_⟩
  have h : PreservesColimitsOfSize.{0, 0} (smallToposMorphism B S hS f).inverseImage :=
    (smallToposMorphism B S hS f).adj.leftAdjoint_preservesColimits
  exact h.preservesFiniteColimits

end AlgebraicGeometry.Space

end
