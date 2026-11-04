module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtalePostcompSlice

/-!
# Postcomposition along an étale morphism is cocontinuous

Let `f : X ⟶ Y` be an étale morphism of algebraic spaces over a scheme `S` contained in a big
fppf site `B`.  Stacks 03LP attaches to it the postcomposition functor

`j : X_étale ⥤ Y_étale`, `(φ : U ⟶ X) ↦ (φ ≫ f : U ⟶ Y)`,

which is `AlgebraicGeometry.Space.smallEtalePostcomp`, and asserts that `j` is *cocontinuous* as
well as continuous.  Continuity is
`AlgebraicGeometry.Space.smallEtalePostcomp_isContinuous`; this file supplies cocontinuity.

Stacks' reason for cocontinuity is that "a covering `{U_i → U}` of `j(φ : U ⟶ X)` in `Y_étale`
is the same thing as a covering of `(φ : U ⟶ X)` in `X_étale`".  That comparison of the two
slices is already available as
`AlgebraicGeometry.Space.SmallEtale.postcompOverEquivalence` and its cover-lifting consequence
`AlgebraicGeometry.Space.SmallEtale.smallEtalePostcomp_cover_lift`, so cocontinuity is exactly
that lemma repackaged as the class `CategoryTheory.Functor.IsCocontinuous`.

With both continuity and cocontinuity in hand, Sites 00XO attaches a morphism of topoi to `j`
whose *inverse* image is restriction along `j`, and Sites 00XR identifies its sections:
`(j^{-1}G)(U) = G(jU)`.  Both are recorded here for an arbitrary coefficient category.

## Main results

* `AlgebraicGeometry.Space.smallEtalePostcomp_isCocontinuous`: **Stacks 03LP**, cocontinuity of
  `j`.
* `AlgebraicGeometry.Space.smallEtalePostcompAdjunction`: restriction along `j` is left adjoint
  to the cocontinuous pushforward, i.e. it is the inverse image of the morphism of topoi that
  Sites 00XO attaches to `j`.
* `AlgebraicGeometry.Space.smallEtalePostcomp_sheafPushforwardContinuous_obj_val_obj`: the
  sections of a restricted sheaf, `(j^{-1}G)(U) = G(jU)`, which holds by definition.

## Implementation notes

The remaining assertion of Stacks 03LP — that the morphism of topoi attached to `j` *is*
`f_{small}`, the morphism of small étale topoi of Stacks 03G2, part (3) — is not proved in this
file, but it is proved in this development:
`AlgebraicGeometry.Space.smallToposMorphism_inverseImageIso` of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleRestrictionInverseImage.lean` carries both
`@[stacks 03LQ]` and `@[stacks 03LP "the morphism of topoi attached to j is f_small"]`, and
Stacks 03LR part (1) is
`AlgebraicGeometry.Space.smallEtalePushforwardBaseChangeIso` of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtalePushforwardBaseChange.lean`.

The identification rests on the adjunction between the spaces-étale analogue of `j` and
spaces-étale base change, which does not go through `AlgebraicGeometry.Space.smallBaseChange` of
Stacks 03G2, part (4), a construction that needs a *representable* morphism.  The adjunction is
`AlgebraicGeometry.Space.spacesEtalePostcompBaseChangeAdjunction`, with its sheaf-level form
`AlgebraicGeometry.Space.spacesEtalePostcompSheafAdjunction` for an arbitrary coefficient
category; and no representability is needed, because the adjunction is on the spaces-étale
sites throughout, where base change exists for an arbitrary morphism.  The small-site shortcut
is simply not the route.  See the implementation notes of
`SmallEtaleRestrictionInverseImage.lean`, where the adjunction is built.

The existence hypothesis of the cocontinuous pushforward is left as a typeclass argument rather
than discharged: `CategoryTheory.Functor.sheafPushforwardCocontinuous` is built from the right
Kan extension `j.op.ran`, and the pointwise existence of that extension is the general
hypothesis of Sites 00XO.  For the small étale site it would follow from essential smallness
(`AlgebraicGeometry.Space.SmallEtale` is essentially small) together with enough limits in the
coefficient category, but no such instance is in the library and the general form is what the
consumers of this file state.

## References

* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
* [Stacks Project, Tag 03LQ](https://stacks.math.columbia.edu/tag/03LQ)
* [Stacks Project, Tag 00XO](https://stacks.math.columbia.edu/tag/00XO)
* [Stacks Project, Tag 00XR](https://stacks.math.columbia.edu/tag/00XR)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- **Stacks 03LP.** Postcomposition along an étale morphism of algebraic spaces is
cocontinuous for the small étale topologies: a covering sieve of the composite chart `jU` pulls
back to a covering sieve of `U`.

This is `AlgebraicGeometry.Space.SmallEtale.smallEtalePostcomp_cover_lift`, which in turn comes
from the comparison of the slice of the small étale site of `X` at `U` with the slice of that of
`Y` at `jU` — Stacks' remark that a covering of `jU` in `Y_étale` is the same thing as a
covering of `U` in `X_étale`. -/
@[stacks 03LP "cocontinuity"]
instance smallEtalePostcomp_isCocontinuous (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) :
    (smallEtalePostcomp B S hS f hf).IsCocontinuous
      (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Y.1) where
  cover_lift hSv := SmallEtale.smallEtalePostcomp_cover_lift B S hS f hf _ _ hSv

/-- **Sites 00XO and 00XR for the functor `j` of Stacks 03LP.** Restriction along
postcomposition is left adjoint to the pushforward attached to its cocontinuity, so it is the
inverse image of a morphism of topoi `Sh(X_étale) ⟶ Sh(Y_étale)`.

The coefficient category is arbitrary, as is the pointwise right Kan extension hypothesis under
which the cocontinuous pushforward exists. -/
noncomputable def smallEtalePostcompAdjunction (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    (A : Type*) [Category A]
    [∀ F : (SmallEtale B S hS X.1)ᵒᵖ ⥤ A,
      (smallEtalePostcomp B S hS f hf).op.HasPointwiseRightKanExtension F] :
    (smallEtalePostcomp B S hS f hf).sheafPushforwardContinuous A
        (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Y.1) ⊣
      (smallEtalePostcomp B S hS f hf).sheafPushforwardCocontinuous A
        (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Y.1) :=
  (smallEtalePostcomp B S hS f hf).sheafAdjunctionCocontinuous A
    (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Y.1)

/-- **Stacks 03LP, the displayed formula for the inverse image**, for the morphism of topoi
attached to `j` by Sites 00XO: the sections of the restriction of `G` over an étale chart `U` of
`X` are the sections of `G` over the composite chart `jU`.  As in Stacks it "holds even for
presheaves", and here it is an equality of objects, by definition of restriction. -/
theorem smallEtalePostcomp_sheafPushforwardContinuous_obj_val_obj (f : X ⟶ Y)
    (hf : IsEtale B S hS f.hom) (A : Type*) [Category A]
    (G : Sheaf (SmallEtale.topology B S hS Y.1) A) (U : SmallEtale B S hS X.1) :
    (((smallEtalePostcomp B S hS f hf).sheafPushforwardContinuous A
          (SmallEtale.topology B S hS X.1)
          (SmallEtale.topology B S hS Y.1)).obj G).obj.obj (.op U) =
      G.obj.obj (.op ((smallEtalePostcomp B S hS f hf).obj U)) :=
  rfl

end AlgebraicGeometry.Space

end
