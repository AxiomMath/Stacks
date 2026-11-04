module

public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardSectionsEtaleRestriction

/-!
# The first arrow of Stacks 03M8 is restriction along the counit of the base change

Let `τ : U ⟶ X` be an étale morphism of algebraic spaces over a scheme `S` contained in a big
fppf site `B`.  The fork of `AlgebraicGeometry.Space.isLimitForkDirectImage` has as its first
arrow restriction along the counit `U ⨯ W ⟶ W` of the *product comonad* of `U`, while the
adjunction of sites of Stacks 03LP and 03G2, part (1), produces the projection `W ×_X U ⟶ W`
as the counit of `AlgebraicGeometry.Space.spacesEtalePostcompBaseChangeAdjunction`.  This file
identifies the two, which is what the `a_*(G|_U)` reading of the first arrow of Stacks 03M8 asks
for on the geometric side: it is the first-arrow analogue of
`AlgebraicGeometry.Space.postcompBaseChangeCompSectionsIso_naturality`, which does the same for
the two parallel arrows.

## Main results

* `AlgebraicGeometry.Space.postcompBaseChangeProdIsoApp_inv_comp_counit`: under the product
  comparison `AlgebraicGeometry.Space.postcompBaseChangeProdIsoApp`, the counit of the
  base-change adjunction **is** the second projection `CategoryTheory.Limits.prod.snd` of the
  binary product `U ⨯ W` of the spaces-étale site of `X`.
* `AlgebraicGeometry.Space.map_counit_comp_prodIsoApp_inv`: the same statement on sections of an
  arbitrary presheaf, which is the shape the fork of Stacks 03M8 consumes — restriction along
  the counit followed by the product comparison is restriction along `prod.snd`.

## Implementation notes

Both statements are made at a single object `W` of the spaces-étale site of `X` rather than as
an equality of natural transformations in `W`.  The reason is the one the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/SpacesEtalePostcompProductNaturality.lean` record for its
own rewriting: a natural transformation whose components these are has target
`(spacesBaseChange f).functor ⋙ 𝟭` where the product comparison has
`(spacesBaseChange f).functor`, and those two are definitionally but not syntactically equal, so
`CategoryTheory.NatTrans.comp_app` — which matches at `implicit` transparency — does not fire on
the composite and the simplification stalls with the composite untouched.  At a single object
every type is spelled with concrete objects of the site and no such mismatch arises.

Nothing here raises a compiler limit or disables a linter.

## What is not done

The arrow `AlgebraicGeometry.Space.chartDirectImageUnitArrow` of
`StacksFrontier/AlgebraicGeometry/Spaces/ModulePushforwardPresentationArrows.lean` — the direct
image along `f` of the unit of
`AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction` at `τ`, followed by the composition
comparison of Stacks 03G2, part (3) — is **not** identified with the first arrow of the fork
here.  What that identification still needs is the sheaf-theoretic half: that the unit of the
small étale restriction adjunction, pushed forward along `f`, is restriction along the counit of
the adjunction of sites.  It is not definitional.
`AlgebraicGeometry.Space.smallEtaleDirectImage` begins with
`(smallEtaleComparisonRestriction X).asEquivalence.inverse`, so
`AlgebraicGeometry.Space.chartDirectImageUnitArrow` contains the inverse of the comparison
equivalence of Stacks 03G1 applied to that unit, which is not a restriction map; and the bridge
that would replace it,
`AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction_unit_comparison`, is stated only at
sheaves of the form `(smallEtaleComparisonRestriction X).obj H`, so the join needs the counit of
that equivalence at a general sheaf together with naturality of the unit.

## References

* [Stacks Project, Tag 03M8](https://stacks.math.columbia.edu/tag/03M8)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w w' u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X U : AlgebraicSpaces B S hS} (τ : U ⟶ X) (hτ : IsEtale B S hS τ.hom)

/-- **The counit of the base-change adjunction is the second projection of the product.**  For
an étale `τ : U ⟶ X` and an object `W` of the spaces-étale site of `X`, the product comparison
`AlgebraicGeometry.Space.postcompBaseChangeProdIsoApp`, which reads the base change `W ×_X U`
over `X` as the binary product `U ⨯ W`, carries the counit of
`AlgebraicGeometry.Space.spacesEtalePostcompBaseChangeAdjunction` to
`CategoryTheory.Limits.prod.snd`.

This is the first-arrow half of the dictionary between the two spellings of the sequence of
Stacks 03M8: the fork of `AlgebraicGeometry.Space.isLimitForkDirectImage` has restriction along
`prod.snd` as its first arrow, while the `a_*(G|_U)` reading produces restriction along the
counit.  It is `AlgebraicGeometry.Space.spacesEtalePostcompBaseChangeAdjunction_counit_app_eq`,
which identifies the counit with the projection of the postcomposed base change, followed by
`AlgebraicGeometry.Space.postcompBaseChangeProdIsoApp_hom_snd`, which identifies that projection
with the second projection of the product. -/
theorem postcompBaseChangeProdIsoApp_inv_comp_counit (W : SpacesEtale B S hS X) :
    (postcompBaseChangeProdIsoApp B S hS τ hτ (spacesBaseChange B S hS τ) W).inv ≫
        (spacesEtalePostcompBaseChangeAdjunction B S hS τ hτ).counit.app W =
      prod.snd := by
  rw [spacesEtalePostcompBaseChangeAdjunction_counit_app_eq]
  exact (Iso.inv_comp_eq _).2
    (postcompBaseChangeProdIsoApp_hom_snd B S hS τ hτ (spacesBaseChange B S hS τ) W).symm

/-- **The first arrow of Stacks 03M8 on sections.**  For a presheaf `P` on the spaces-étale site
of `X` with arbitrary coefficients and an object `W` of that site, restriction of sections along
the counit of `AlgebraicGeometry.Space.spacesEtalePostcompBaseChangeAdjunction`, followed by the
product comparison on sections, is restriction along the second projection of the product
`U ⨯ W` — which is the first arrow of the fork of
`AlgebraicGeometry.Space.isLimitForkProdOfEtalePresentation`, and hence of
`AlgebraicGeometry.Space.isLimitForkDirectImage` at `W = V ×_Y X`.

It is `AlgebraicGeometry.Space.postcompBaseChangeProdIsoApp_inv_comp_counit` with the opposite
morphisms applied to `P`. -/
theorem map_counit_comp_prodIsoApp_inv {A : Type w} [Category.{w'} A]
    (P : (SpacesEtale B S hS X)ᵒᵖ ⥤ A) (W : SpacesEtale B S hS X) :
    P.map ((spacesEtalePostcompBaseChangeAdjunction B S hS τ hτ).counit.app W).op ≫
        P.map (postcompBaseChangeProdIsoApp B S hS τ hτ
          (spacesBaseChange B S hS τ) W).inv.op =
      P.map (prod.snd : etaleOverObj B S hS τ hτ ⨯ W ⟶ W).op := by
  rw [← P.map_comp, ← op_comp]
  exact congrArg (fun m ↦ P.map (Quiver.Hom.op m))
    (postcompBaseChangeProdIsoApp_inv_comp_counit B S hS τ hτ W)

end AlgebraicGeometry.Space

end
