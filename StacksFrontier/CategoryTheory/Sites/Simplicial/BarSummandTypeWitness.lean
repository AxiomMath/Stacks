module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationComponentInverseImageAb
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationResolutionTerms
public import StacksFrontier.CategoryTheory.Sites.Simplicial.SliceAbelianLowerShriekTransition

/-!
# The two sides of a proposed comparison, and why no equation between them exists

The comparison of the simplex-coefficient resolution of Stacks 09WG/0D78 with the Čech resolution
of Stacks 01GE was at one point specified as an equation between the two morphisms this file
writes down, for a simplex map `φ : m ⟶ n`.  No such equation can be stated: the two morphisms
live in categories of abelian sheaves on *different* simplicial components.  This file records
that as a build-checked fact rather than as a remark, by ascribing the type of each side
explicitly.

`barSummandSideA` is the `φ`-labelled summand of the degree-`m` term of the resolution, read over
the component of degree `n` through the compatibility of Stacks 0D70 in inverse images.  Its
ambient category is `Sheaf ((situation J K).componentTopology n) Ab`.

`barSummandSideB` is the extension by zero along the relocalization `r_φ` of the comparison
`CategoryTheory.SimplicialSemiRepresentable.sliceAbelianRestrictionCompIso`, followed by the
counit of `r_{φ!} ⊣ r_φ^{-1}`.  Its ambient category is
`Sheaf ((situation J K).componentTopology m) Ab`.

Transposing the second into degree `n` does not repair the mismatch.  The target of
`barSummandSideA` is the degree-`m` term of the resolution restricted to the component of degree
`n`, which by `CategoryTheory.SimplicialSiteSituation.abelianComponentBarIsoCoproduct'` is a
copower of the restriction indexed by *all* simplex maps `m ⟶ n`, and `barSummandSideA` is by
`CategoryTheory.SimplicialSiteSituation.sigma_ι_comp_abelianComponentBarIsoCoproduct_inv'` the
`φ`-th inclusion into that copower, up to the Stacks 0D70 comparison.  The target of
`barSummandSideB` is a single such factor.  A coproduct inclusion indexed by a type with more
than one element is not an isomorphism, so the two cannot be the two sides of one equation in any
degree.

What the two ascriptions check is that the ambient category of the first is indexed by `n` and
that of the second by `m`; for a simplex map `φ : m ⟶ n` with `m ≠ n` those are different
categories, and no equation between terms of different types can be written.

What the comparison does reduce to is stated in
`StacksFrontier/CategoryTheory/Sites/Simplicial/SliceComponentTransitionRestriction.lean`, where
both sides are morphisms of abelian sheaves on the component of degree `n`.

No tag attribute is placed: nothing here is a statement of the Stacks project.

## Main definitions

* `CategoryTheory.SimplicialSemiRepresentable.barSummandSideA`
* `CategoryTheory.SimplicialSemiRepresentable.barSummandSideB`

## References

* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
* [Stacks Project, Tag 0D70](https://stacks.math.columbia.edu/tag/0D70)
* [Stacks Project, Tag 0D78](https://stacks.math.columbia.edu/tag/0D78)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.SimplicialSiteSituation

universe u

namespace CategoryTheory.SimplicialSemiRepresentable

open SemiRepresentable

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (K : SimplicialObject (FormalCoproduct.{u} C)) [J.toCoverage.HasPullbacks]

/-- The `φ`-labelled summand of the degree-`m` term of the simplex-coefficient resolution of
`a^{-1}𝒢`, read over the component of degree `n` through the compatibility of Stacks 0D70 in
inverse images.  The ascribed types of the source and the target are the point of the
declaration: this is a morphism of abelian sheaves on the component of simplicial degree `n`. -/
def barSummandSideA {m n : SimplexCategory} (φ : m ⟶ n) (G : Sheaf J Ab.{u}) :
    ((Augmentation.componentInverseImageAb (situation J K) (Cat.of C) J
          (situationAugmentation J K) n).obj G :
        Sheaf ((situation J K).componentTopology n) Ab.{u}) ⟶
      (((situation J K).restrictAb n).obj
          (((barSimplicial' (situation J K)).obj
            ((Augmentation.totalInverseImageAb (situation J K) (Cat.of C) J
              (situationAugmentation J K)).obj G)).obj (op m)) :
        Sheaf ((situation J K).componentTopology n) Ab.{u}) :=
  (componentRestrictionAbInverseImageIso' (situation J K) (Cat.of C) J
      (situationAugmentation J K) G n).inv ≫
    componentSheafSummand' (situation J K)
      ((Augmentation.totalInverseImageAb (situation J K) (Cat.of C) J
        (situationAugmentation J K)).obj G) φ

/-- The extension by zero along the relocalization `r_φ` of the comparison
`sliceAbelianRestrictionCompIso`, followed by the counit of `r_{φ!} ⊣ r_φ^{-1}`.  The ascribed
types of the source and the target are the point of the declaration: this is a morphism of
abelian sheaves on the component of simplicial degree `m`, not `n`. -/
def barSummandSideB {m n : SimplexCategory} (φ : m ⟶ n) (G : Sheaf J Ab.{u}) :
    ((transitionAbelianLowerShriek J K φ).obj
          (((sliceForget K (op n)).sheafPushforwardContinuous AddCommGrpCat.{u}
            ((situation J K).componentTopology n) J).obj G) :
        Sheaf ((situation J K).componentTopology m) AddCommGrpCat.{u}) ⟶
      (((sliceForget K (op m)).sheafPushforwardContinuous AddCommGrpCat.{u}
          ((situation J K).componentTopology m) J).obj G :
        Sheaf ((situation J K).componentTopology m) AddCommGrpCat.{u}) :=
  (transitionAbelianLowerShriek J K φ).map
      ((sliceAbelianRestrictionCompIso J K φ).inv.app G) ≫
    (transitionAbelianLowerShriekAdjunction J K φ).counit.app
      (((sliceForget K (op m)).sheafPushforwardContinuous AddCommGrpCat.{u}
        ((situation J K).componentTopology m) J).obj G)

end CategoryTheory.SimplicialSemiRepresentable

end
