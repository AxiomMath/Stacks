module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.Adjunction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.Cocontinuous
public import StacksFrontier.CategoryTheory.Sites.Continuous
public import StacksCore.Tactic.StacksAttribute

/-!
# Direct image along an open immersion of small étale sites

Let `j : U ⟶ X` be an étale morphism, viewed as an object of the small étale site of `X`.
Composition with `j` is a continuous *and* cocontinuous functor of small étale sites, so
restriction `j^{-1}` of étale sheaves sits in the middle of an adjoint triple
`j_! ⊣ j^{-1} ⊣ j_*`: the right adjoint `j_*` is the restriction to sheaves of the right Kan
extension along composition with `j`.

When `j` is an open immersion its structure morphism is a monomorphism, so composition with it
is fully faithful, and then the counit `j^{-1}j_*F ⟶ F` of `j^{-1} ⊣ j_*` is an isomorphism:
a sheaf on `U` is recovered from its direct image by restricting back to `U`. This is the half
of Stacks 0F70 about the direct image, the other half — the unit `F ⟶ j^{-1}j_!F` — being
`AlgebraicGeometry.abelianExtensionByZeroAdjunction_unit_isIso`.

## Main definitions

* `AlgebraicGeometry.abelianDirectImage` — `j_*` on abelian étale sheaves.
* `AlgebraicGeometry.abelianDirectImageAdjunction` — the adjunction `j^{-1} ⊣ j_*`.

## Main results

* `AlgebraicGeometry.abelianDirectImageAdjunction_counit_isIso` — along an open immersion the
  counit `j^{-1}j_*F ⟶ F` is an isomorphism.
* `AlgebraicGeometry.abelianDirectImage_fullyFaithful` — equivalently, direct image along an
  open immersion is fully faithful.

## Implementation notes

`j_*` is Mathlib's `CategoryTheory.Functor.sheafPushforwardCocontinuous` of
`AlgebraicGeometry.smallEtalePostcompose` and the adjunction is Mathlib's
`CategoryTheory.Functor.sheafAdjunctionCocontinuous`, so the map whose invertibility is
asserted is the canonical counit and not an unspecified isomorphism of functors. Invertibility
is the general statement `CategoryTheory.Functor.isIso_sheafAdjunctionCocontinuous_counit` of
Stacks 00XT for a cocontinuous, continuous, fully faithful functor of sites; the three
properties of composition with `j` are instances, full faithfulness through the monomorphism
`U ⟶ X` coming from the open immersion.

## References

* [Stacks Project, Tag 0F70](https://stacks.math.columbia.edu/tag/0F70)
* [Stacks Project, Tag 00XT](https://stacks.math.columbia.edu/tag/00XT)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable (B : AlgebraicGeometry.BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)
  (U : SmallEtale B X hX)

/-- Direct image of abelian étale sheaves along the étale morphism `U ⟶ X`: the right adjoint
of restriction, obtained from the right Kan extension along composition with `U ⟶ X`, which
carries sheaves to sheaves because that composition is cocontinuous. -/
public abbrev abelianDirectImage :
    Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property) AddCommGrpCat.{u + 1} ⥤
      Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1} :=
  (smallEtalePostcompose B X hX U).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
    (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
    (SmallEtale.topology B X hX)

/-- Restriction of abelian étale sheaves along `U ⟶ X` is left adjoint to direct image. This
adjunction is the right half of the adjoint triple `j_! ⊣ j^{-1} ⊣ j_*`, and its counit is the
canonical map `j^{-1}j_*F ⟶ F`. -/
public def abelianDirectImageAdjunction :
    abelianRestriction B X hX U ⊣ abelianDirectImage B X hX U :=
  (smallEtalePostcompose B X hX U).sheafAdjunctionCocontinuous AddCommGrpCat.{u + 1}
    (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
    (SmallEtale.topology B X hX)

variable [IsOpenImmersion (B.inclusion.map U.obj.hom)]

/-- **Stacks 0F70.** Along an open immersion `U ⟶ X` the counit of the adjunction between
restriction and direct image is an isomorphism: an abelian étale sheaf on `U` is recovered from
its direct image by restricting back to `U`. Composition with `U ⟶ X` is continuous,
cocontinuous, and — because the structure morphism of `U` is a monomorphism — fully faithful,
which is exactly the situation of Stacks 00XT. -/
@[stacks 0F70 "direct_image_counit"]
public theorem abelianDirectImageAdjunction_counit_isIso :
    IsIso (abelianDirectImageAdjunction B X hX U).counit := by
  have : Mono U.obj.hom := B.inclusion.mono_of_mono_map inferInstance
  exact Functor.isIso_sheafAdjunctionCocontinuous_counit (smallEtalePostcompose B X hX U)
    AddCommGrpCat.{u + 1} (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
    (SmallEtale.topology B X hX)

/-- Direct image of abelian étale sheaves along an open immersion is fully faithful, the counit
of its adjunction with restriction being an isomorphism. -/
public def abelianDirectImage_fullyFaithful :
    (abelianDirectImage B X hX U).FullyFaithful :=
  have := abelianDirectImageAdjunction_counit_isIso B X hX U
  Adjunction.fullyFaithfulROfIsIsoCounit (abelianDirectImageAdjunction B X hX U)

end AlgebraicGeometry

end
