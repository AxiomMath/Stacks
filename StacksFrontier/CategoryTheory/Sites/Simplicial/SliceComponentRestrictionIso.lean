module

public import StacksFrontier.CategoryTheory.Adjunction.RightAdjointUniqOfNatIso
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringSituationComponentKInjective
public import StacksFrontier.CategoryTheory.Sites.Simplicial.SliceAbelianLowerShriekTransition
public import StacksFrontier.CategoryTheory.Sites.Topos.PushPullTransition

/-!
# The restriction of `a^{-1}` to a simplicial degree, read through the localization functor

Let `(C, J)` be a site with fibre products and `K` a simplicial semi-representable object.
`CategoryTheory.SimplicialSemiRepresentable.situationComponentInverseImageSliceIso` identifies
the inverse image `a^{-1}` along the total augmentation followed by restriction to the component
of simplicial degree `p` with restriction along the localization functor `j_p`.  It is built by
uniqueness of *right* adjoints, from the identification
`componentLowerShriekCompAugmentationAbelianIso` of `a_! g_{p!}` with `j_{p!}`.

That identification is itself built by uniqueness of *left* adjoints from the comparison
`componentAugmentationRestrictionIso` of the restrictions along the two factorizations of `j_p`,
and this file proves that the two constructions are inverse to each other: the comparison built
from uniqueness of right adjoints is the comparison of restrictions one started from, up to the
identification of `a^{-1}` with restriction along `j_total`.

This is what makes `situationComponentInverseImageSliceIso` computable.  As it stands it is a
`CategoryTheory.Adjunction.rightAdjointUniq`, so nothing about it can be evaluated; read through
this identity it is a `CategoryTheory.Functor.sheafPushforwardContinuousComp'` of an
`CategoryTheory.eqToIso`, which is restriction of presheaves along an equality of site functors.

## Main results

* `CategoryTheory.SimplicialSemiRepresentable.situationComponentInverseImageSliceIso_eq`: **the
  comparison is the comparison of restrictions**, after `a^{-1}` is read as restriction along
  `j_total`.
* `CategoryTheory.SimplicialSemiRepresentable.situationComponentInverseImageSliceIso_hom_app`:
  the same at an object.

## Implementation notes

The adjunction `situationAbelianLowerShriekAdjunction` whose right adjoint is the inverse image
of the morphism of topoi is `augmentationAbelianLowerShriekAdjunction` — whose right adjoint is
restriction along `j_total` — read through `situationTotalInverseImageAbIso`, so the composite
adjunction that `situationComponentInverseImageSliceIso` is taken against differs from the one
that `componentLowerShriekCompAugmentationAbelianIso_eq` speaks of only by an
`CategoryTheory.Adjunction.ofNatIsoRight`.  The three identities of
`StacksFrontier.CategoryTheory.Adjunction.RightAdjointUniqOfNatIso` move that transport out of the
composite, past the transport of the left adjoint, and out of the comparison, and
`Stacks.CategoryTheory.rightAdjointUniq_ofNatIsoLeft_leftAdjointCompIso_inv` returns the
comparison of restrictions from what remains.

Those three identities are applied there rather than here.  The two spellings of the category of
sheaves on the component of degree `p` carry different category instances, which makes the goal
ill-typed at `instances` transparency, and `rewrite` then fails to find a pattern that is
visibly present in it; the same rewrites in a statement whose categories are variables succeed.

## References

* [Stacks Project, Tag 09WM](https://stacks.math.columbia.edu/tag/09WM)
* [Stacks Project, Tag 0D8B](https://stacks.math.columbia.edu/tag/0D8B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory.SimplicialSemiRepresentable

open SemiRepresentable

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (K : SimplicialObject (FormalCoproduct.{u} C)) [J.toCoverage.HasPullbacks]

/-- **The comparison of `a^{-1}(-)|_p` with `j_p^{-1}` is the comparison of restrictions.**
Reading the inverse image along the total augmentation as restriction along `j_total` by
`situationTotalInverseImageAbIso` and then comparing the restriction along `g_p ⋙ j_total` with
the restriction along `j_p` by `componentAugmentationRestrictionIso` is
`situationComponentInverseImageSliceIso`.

Both are comparisons of two right adjoints of `j_{p!}`, and the one built by uniqueness is the
one built by hand because `componentLowerShriekCompAugmentationAbelianIso` was itself built from
the one built by hand, by uniqueness of left adjoints. -/
theorem situationComponentInverseImageSliceIso_eq (p : SimplexCategory) :
    situationComponentInverseImageSliceIso J K p =
      Functor.isoWhiskerRight (situationTotalInverseImageAbIso J K)
          ((situation J K).restrictAb p) ≪≫
        componentAugmentationRestrictionIso J K p := by
  refine Adjunction.rightAdjointUniq_comp_ofNatIsoRight_symm_ofNatIsoLeft_eq
    (SimplicialSiteSituation.componentLowerShriekAbAdjunction' (situation J K) p)
    (augmentationAbelianLowerShriekAdjunction J K) (situationTotalInverseImageAbIso J K)
    (componentLowerShriekCompAugmentationAbelianIso J K p)
    (sliceAbelianLowerShriekAdjunction J K p) (componentAugmentationRestrictionIso J K p)
    (Iso.ext ?_)
  rw [componentLowerShriekCompAugmentationAbelianIso_eq J K p]
  exact Stacks.CategoryTheory.rightAdjointUniq_ofNatIsoLeft_leftAdjointCompIso_inv
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (SimplicialSiteSituation.componentFunctor (situation J K) p) AddCommGrpCat.{u}
      ((situation J K).componentTopology p) ((situation J K).totalTopology))
    (sliceAbelianLowerShriekAdjunction J K p)
    (augmentationAbelianLowerShriekAdjunction J K)
    (componentAugmentationRestrictionIso J K p)

/-- `situationComponentInverseImageSliceIso_eq` at an object. -/
theorem situationComponentInverseImageSliceIso_hom_app (p : SimplexCategory)
    (G : Sheaf J Ab.{u}) :
    (situationComponentInverseImageSliceIso J K p).hom.app G =
      ((situation J K).restrictAb p).map ((situationTotalInverseImageAbIso J K).hom.app G) ≫
        (componentAugmentationRestrictionIso J K p).hom.app G :=
  congrArg (fun e => e.hom.app G) (situationComponentInverseImageSliceIso_eq J K p)

end CategoryTheory.SimplicialSemiRepresentable

end
