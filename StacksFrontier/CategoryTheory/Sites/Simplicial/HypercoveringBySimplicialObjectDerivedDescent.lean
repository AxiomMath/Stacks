module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringBySimplicialObject
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringObjectDerivedDescent

/-!
# The augmentation of the total site of a hypercovering by a simplicial object of the site

Let `C` be a site with fibre products given by a pretopology `P`, let `X` be an object of `C`,
let `U` be a simplicial object of `C` and let `a : U ⟶ X` be an augmentation. When `a` is a
hypercovering of `X` in `C` in the sense of Stacks 09X8, that is, when it satisfies the three
covering conditions of
`Stacks.CategoryTheory.Hypercovering.IsHypercoveringAugmentation`, it determines the
one-summand simplicial semi-representable object `n ↦ {U_n ⟶ X}` over `X`, its total site
`(C/U)_total`, and the augmentation `a : Sh((C/U)_total) ⟶ Sh(C/X)` given by the degree-zero
localization functor.

This file names that augmentation as a simplicial-site augmentation in the sense of
Stacks 0D8B. It is the construction that the two deductions of Section 85.21 are about:

* **Stacks 09X9**, `RΓ(X, E) = RΓ((C/U)_total, a⁻¹E)` for `E` in `D(C/X)`, which the source
  obtains from **Stacks 09X7**, and
* **Stacks 0DA9**, that `a⁻¹ : D⁺(C/X) ⟶ D⁺_𝒜((C/U)_total)` is an equivalence with quasi-inverse
  `Ra_*`, where `𝒜 ⊂ Ab((C/U)_total)` is the weak Serre subcategory of cartesian abelian sheaves
  of Stacks 0D7J, which the source obtains from **Stacks 0D8M**.

Both are proved in the sibling module
`HypercoveringBySimplicialObjectDerivedDescentUnconditional` of this directory,
as `CategoryTheory.SimplicialSemiRepresentable.derivedGlobalSectionsInverseImageIsoAugmented'`
(with the canonical forward map pinned by
`CategoryTheory.SimplicialSemiRepresentable.derivedGlobalSectionsInverseImageIsoAugmented_hom_app'`)
and as `CategoryTheory.SimplicialSemiRepresentable.derivedTotalInverseImageEquivalenceAugmented'`
(with its two functors pinned by
`CategoryTheory.SimplicialSemiRepresentable.derivedTotalInverseImageEquivalenceAugmented_functor'`
and
`CategoryTheory.SimplicialSemiRepresentable.derivedTotalInverseImageEquivalenceAugmented_inverse'`),
both stated at the augmentation defined here.

## Main definitions

* `CategoryTheory.SimplicialSemiRepresentable.augmentationAugmented`: the augmentation
  `a : Sh((C/U)_total) ⟶ Sh(C/X)` of Stacks 09X8 read as a simplicial-site augmentation in the
  sense of Stacks 0D8B. It is `augmentationOver` at the associated simplicial
  semi-representable object.

## Implementation notes

The hypothesis that `C` has fibre products is the `HasPullbacks C` instance. It is what makes
`Over X` have pullbacks, hence makes the localized topology `P.toGrothendieck.over X` admit
pullbacks of covering families, which the simplicial family of sites of Stacks 0D8B requires; it
also makes the coskeleta appearing in the hypercovering conditions exist, so that
`IsHypercoveringAugmentation` is well formed at all.

The pretopology `P` is named rather than a topology because the hypercovering predicate of
Stacks 09X8 is stated for covering families; the site `C/X` is the Grothendieck topology it
generates, localized at `X`.

## References

* [Stacks Project, Tag 09X9](https://stacks.math.columbia.edu/tag/09X9)
* [Stacks Project, Tag 0DA9](https://stacks.math.columbia.edu/tag/0DA9)
* [Stacks Project, Tag 09X7](https://stacks.math.columbia.edu/tag/09X7)
* [Stacks Project, Tag 0D8M](https://stacks.math.columbia.edu/tag/0D8M)
* [Stacks Project, Tag 0D8B](https://stacks.math.columbia.edu/tag/0D8B)
* [Stacks Project, Tag 0D7J](https://stacks.math.columbia.edu/tag/0D7J)
* [Stacks Project, Tag 09X8](https://stacks.math.columbia.edu/tag/09X8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.SimplicialSiteSituation Opposite

universe u

namespace CategoryTheory.SimplicialSemiRepresentable

open Stacks.CategoryTheory.Hypercovering

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [SmallCategory C] [HasPullbacks C] (P : Pretopology C) {X : C}
  (U : SimplicialObject C) (a : U ⟶ (SimplicialObject.const C).obj X)

/-! ### The augmentation of the total site, as a simplicial-site augmentation -/

/-- The augmentation `a : Sh((C/U)_total) ⟶ Sh(C/X)` of Stacks 09X8, read as a simplicial-site
augmentation in the sense of Stacks 0D8B: the augmentation `augmentationOver` of the simplicial
family of sites `n ↦ (C/X)/U_n` over the slice site `C/X`, taken at the one-summand simplicial
semi-representable object `n ↦ {U_n ⟶ X}` that `a` determines.

This is the single construction both Stacks 09X9 and Stacks 0DA9 are statements about:
`derivedGlobalSectionsInverseImageIsoAugmented'` and `derivedTotalInverseImageEquivalenceAugmented'`
are the statements of `HypercoveringObjectDerivedDescentUnconditional` at this augmentation. -/
abbrev augmentationAugmented :
    Augmentation (totalSituation P U a) (Cat.of (Over X)) (P.toGrothendieck.over X) :=
  augmentationOver P (associatedSimplicialObject.{u} U a)

end CategoryTheory.SimplicialSemiRepresentable

end
