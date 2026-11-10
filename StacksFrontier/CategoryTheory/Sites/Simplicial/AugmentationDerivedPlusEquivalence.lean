module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactAdjunctionBoundedBelowEquivalence
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationCartesian
public import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianWeakSerre
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringCohomologicalDescent

/-!
# The inverse image along an augmentation as an equivalence onto `D⁺_𝒜`

Let `a : Sh((C_n)_total) ⟶ Sh(D)` be the augmentation of topoi of an augmented simplicial site,
and let `𝒜 ⊂ Ab((C_n)_total)` be the weak Serre subcategory of cartesian abelian sheaves. The
inverse image `a⁻¹` of abelian sheaves is exact, and `a⁻¹𝒢` is always cartesian; so its right
derived functor on bounded below derived categories takes values in `D⁺_𝒜((C_n)_total)`, the
bounded below objects whose cohomology sheaves are cartesian.

This file records that `a⁻¹ : D⁺(D) ⟶ D⁺_𝒜((C_n)_total)` is an equivalence with quasi-inverse
`Ra_*` as soon as

* the unit `K ⟶ Ra_*a⁻¹K` is an isomorphism for every `K` in `D⁺(D)` (cohomological descent),
  and
* every cartesian abelian sheaf on the total site is isomorphic to `a⁻¹𝒢` for an abelian sheaf
  `𝒢` on `D` (descent for cartesian sheaves).

These are exactly the two inputs of the descent statements of the form "`a⁻¹` is an equivalence
`D⁺(X) ⟶ D⁺_𝒜(U)` with quasi-inverse `Ra_*`" for hypercoverings, which the source deduces as a
formal consequence of them together with Tag 0D7U.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.Augmentation.derivedPlusInverseImageEquivalence`:
  **the equivalence** `D⁺(D) ≌ D⁺_𝒜((C_n)_total)`.

## Main results

* `CategoryTheory.SimplicialSiteSituation.Augmentation`
  `.derivedCategoryB_rightDerivedFunctorPlus_totalInverseImageAb_obj`: `a⁻¹` carries `D⁺(D)` into
  `D⁺_𝒜((C_n)_total)`, with no hypothesis on the augmentation.
* `derivedPlusInverseImageEquivalence_functor` and `derivedPlusInverseImageEquivalence_inverse`:
  the two functors of the equivalence are `a⁻¹` and `Ra_*`.

## Implementation notes

The derived categories are arbitrary models, and the enough-injectives conditions are instance
arguments, being properties of the two abelian categories rather than hypotheses of the source.

## References

* [Stacks Project, Tag 0D7U](https://stacks.math.columbia.edu/tag/0D7U)
* [Stacks Project, Tag 0D7H](https://stacks.math.columbia.edu/tag/0D7H)
* [Stacks Project, Tag 0D7J](https://stacks.math.columbia.edu/tag/0D7J)
* [Stacks Project, Tag 0DH9](https://stacks.math.columbia.edu/tag/0DH9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.SimplicialSiteSituation.Augmentation

variable (S : SimplicialSiteSituation.{u}) (D : Cat.{u, u}) (K : GrothendieckTopology D)
  (a : Augmentation S D K)
  [HasDerivedCategory (Sheaf K AddCommGrpCat.{u})]
  [HasDerivedCategory (Sheaf S.totalTopology AddCommGrpCat.{u})]
  [EnoughInjectives (Sheaf K AddCommGrpCat.{u})]

/-- `D⁺_𝒜((C_n)_total)`: the bounded below complexes of abelian sheaves on the total site all of
whose cohomology sheaves are cartesian. -/
abbrev cartesianDerivedPlus :
    ObjectProperty (DerivedCategory.Plus (Sheaf S.totalTopology AddCommGrpCat.{u})) :=
  (DerivedCategoryB.derivedCategoryB (IsCartesianAbSheaf S)).inverseImage DerivedCategory.Plus.ι

/-- **`a⁻¹` carries `D⁺(D)` into `D⁺_𝒜((C_n)_total)`**: for `X` in `D⁺(D)`, every cohomology
sheaf of `a⁻¹X` is cartesian. -/
theorem derivedCategoryB_rightDerivedFunctorPlus_totalInverseImageAb_obj
    (X : DerivedCategory.Plus (Sheaf K AddCommGrpCat.{u})) :
    cartesianDerivedPlus S ((totalInverseImageAb S D K a).rightDerivedFunctorPlus.obj X) :=
  Adjunction.derivedCategoryB_rightDerivedFunctorPlus_obj (IsCartesianAbSheaf S)
    (isCartesianAbSheaf_totalInverseImageAb S D K a) X

variable [EnoughInjectives (Sheaf S.totalTopology AddCommGrpCat.{u})]

/-- **`a⁻¹ : D⁺(D) ⟶ D⁺_𝒜((C_n)_total)` is an equivalence with quasi-inverse `Ra_*`**, granted
cohomological descent `K ≅ Ra_*a⁻¹K` on `D⁺(D)` and that every cartesian abelian sheaf on the
total site is `a⁻¹` of an abelian sheaf on `D`. -/
def derivedPlusInverseImageEquivalence
    (hunit : ∀ X, IsIso ((abelianTotalAdjunction S D K a).rightDerivedFunctorPlus.unit.app X))
    (hsurj : ∀ G : Sheaf S.totalTopology AddCommGrpCat.{u}, IsCartesianAbSheaf S G →
      (totalInverseImageAb S D K a).essImage G) :
    DerivedCategory.Plus (Sheaf K AddCommGrpCat.{u}) ≌ (cartesianDerivedPlus S).FullSubcategory :=
  (abelianTotalAdjunction S D K a).rightDerivedFunctorPlusEquivalence (IsCartesianAbSheaf S)
    (isCartesianAbSheaf_totalInverseImageAb S D K a) hunit hsurj

/-- **The forward functor of the equivalence is `a⁻¹`.** -/
theorem derivedPlusInverseImageEquivalence_functor
    (hunit : ∀ X, IsIso ((abelianTotalAdjunction S D K a).rightDerivedFunctorPlus.unit.app X))
    (hsurj : ∀ G : Sheaf S.totalTopology AddCommGrpCat.{u}, IsCartesianAbSheaf S G →
      (totalInverseImageAb S D K a).essImage G) :
    (derivedPlusInverseImageEquivalence S D K a hunit hsurj).functor =
      (cartesianDerivedPlus S).lift (totalInverseImageAb S D K a).rightDerivedFunctorPlus
        (derivedCategoryB_rightDerivedFunctorPlus_totalInverseImageAb_obj S D K a) :=
  rfl

/-- **The quasi-inverse of the equivalence is `Ra_*`.** -/
theorem derivedPlusInverseImageEquivalence_inverse
    (hunit : ∀ X, IsIso ((abelianTotalAdjunction S D K a).rightDerivedFunctorPlus.unit.app X))
    (hsurj : ∀ G : Sheaf S.totalTopology AddCommGrpCat.{u}, IsCartesianAbSheaf S G →
      (totalInverseImageAb S D K a).essImage G) :
    (derivedPlusInverseImageEquivalence S D K a hunit hsurj).inverse =
      (cartesianDerivedPlus S).ι ⋙ (abelianTotalPushforward S D K a).rightDerivedFunctorPlus :=
  rfl

end CategoryTheory.SimplicialSiteSituation.Augmentation
