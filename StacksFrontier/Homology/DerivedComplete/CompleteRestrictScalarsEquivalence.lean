module

public import StacksFrontier.Homology.DerivedComplete.CompleteRestrictScalarsEquivalence.DerivedAdjunction
public import StacksFrontier.Homology.DerivedComplete.CompleteRestrictScalarsEquivalence.CechTerms
public import StacksFrontier.Homology.DerivedComplete.CompleteRestrictScalarsEquivalence.LargeUniverse
public import StacksFrontier.Homology.DerivedComplete.CompleteRestrictScalarsEquivalence.SmallQuotients

/-!
# Restriction of scalars for derived complete complexes

This file collects the four parts `CompleteRestrictScalarsEquivalence.DerivedAdjunction`,
`CompleteRestrictScalarsEquivalence.CechTerms`, `CompleteRestrictScalarsEquivalence.LargeUniverse`
and `CompleteRestrictScalarsEquivalence.SmallQuotients`.

Let `A → B` be a flat map of commutative rings which is an isomorphism modulo a finitely
generated ideal `I` of `A`. Restriction of scalars induces an equivalence between the full
subcategories of derived complete complexes over `B` and over `A`, cut out by
`IsDerivedComplete`; the countable products used to define derived completeness exist.

## Main results

* `CompleteRestrictScalarsEquivalence.isEquivalence_lift_of_counit`: a left adjoint which
  reflects isomorphisms and whose counit is invertible on a full subcategory restricts to an
  equivalence of full subcategories.
* `CompleteRestrictScalarsEquivalence.exists_derivedAdjunction`: an adjunction of exact functors
  induces one on derived categories when the target has K-injective resolutions.
* `CompleteRestrictScalarsEquivalence.restrictScalars_equivalence_derivedComplete`: restriction
  of scalars induces an equivalence on the full subcategories of derived complete objects.

## References

* [The Stacks Project, Tag 0925](https://stacks.math.columbia.edu/tag/0925)
* [Bhatt--Scholze, *Projectivity of the Witt vector affine Grassmannian*][BS]
-/
