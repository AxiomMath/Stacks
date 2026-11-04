module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianDerivedSheaves
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringBoundedBelowEquivalence
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringBoundedBelowEquivalenceUnconditional

/-!
# The derived inverse image along an augmentation is cartesian

Let `S` be a simplicial-site situation and `a` an augmentation of `S` towards a site `(D, K)`.
For an object `E` of `D(D, K)` the derived inverse image `a⁻¹E` is a cartesian object of the
derived category of abelian sheaves on the total site, i.e. every derived transition
`f_φ⁻¹ (a⁻¹E)_m ⟶ (a⁻¹E)_n` is invertible. This holds on the whole of `D((C/K)_total)`, not only
on its bounded below part.

## Main results

* `Augmentation.isCartesianDerived_derivedTotalInverseImage`: the derived inverse image `a⁻¹E`
  is a cartesian derived abelian sheaf on the total site.

## References

* [Stacks Project, Tag 0D7H](https://stacks.math.columbia.edu/tag/0D7H)
* [Stacks Project, Tag 0D7L](https://stacks.math.columbia.edu/tag/0D7L)
* [Stacks Project, Tag 07TF](https://stacks.math.columbia.edu/tag/07TF)
* [Stacks Project, Tag 0D70](https://stacks.math.columbia.edu/tag/0D70)
* [Stacks Project, Tag 0D6Z](https://stacks.math.columbia.edu/tag/0D6Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.SimplicialSiteSituation.Augmentation

attribute [local instance] HasDerivedCategory.standard

variable (S : SimplicialSiteSituation.{u}) (D : Cat.{u, u}) (K : GrothendieckTopology D)
  (a : Augmentation S D K)

/-- For an object `E` of the derived category of abelian sheaves on the augmentation site, the
derived inverse image `a⁻¹E` is a cartesian object of the derived category of abelian sheaves on
the total site.

It suffices that every cohomology sheaf of `a⁻¹E` be cartesian
(`isCartesianDerived_iff_forall_isCartesianAbSheaf_homology'`); those cohomology sheaves are the
inverse images of the cohomology sheaves of `E`, since `a⁻¹` is exact, and the inverse image of
an abelian sheaf along the augmentation is cartesian (`isCartesianAbSheaf_totalInverseImageAb`). -/
@[stacks 0D7H "part (2), the derived inverse image of an object of D(D) is cartesian"]
theorem isCartesianDerived_derivedTotalInverseImage
    (E : DerivedCategory (Sheaf K AddCommGrpCat.{u})) :
    S.IsCartesianDerived ((derivedTotalInverseImage S D K a).obj E) :=
  (isCartesianDerived_iff_forall_isCartesianAbSheaf_homology' S _).2 fun q ↦
    ObjectProperty.prop_of_iso (P := IsCartesianAbSheaf S)
      (derivedTotalInverseImageHomologyObjIso S D K a E q).symm
      (isCartesianAbSheaf_totalInverseImageAb S D K a _)

end CategoryTheory.SimplicialSiteSituation.Augmentation

end
