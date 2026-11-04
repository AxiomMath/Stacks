module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactAdjunctionBoundedBelowSerreEquivalence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsion.TorsionSheavesAndAdjunctions
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationCartesian
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringCohomologicalDescent

/-!
# The inverse image along an augmentation on torsion coefficients

Let `S` be a simplicial-site situation (Stacks 09WE) with an augmentation `a` towards a site
`(D, K)` (Stacks 0D6Z), and let `a⁻¹ ⊣ a_*` be the adjunction on abelian sheaves. Write
`D⁺_tors(D)` for the bounded below complexes of abelian sheaves on `D` with torsion cohomology
sheaves, and `D⁺_{𝒜, tors}` for the bounded below complexes of abelian sheaves on the total
site whose cohomology sheaves are cartesian and torsion; `𝒜` is the weak Serre subcategory of
cartesian abelian sheaves of Stacks 0D7J.

This file records that `a⁻¹ : D⁺_tors(D) ⟶ D⁺_{𝒜, tors}` is an equivalence with quasi-inverse
`Ra_*`, as soon as

* `a⁻¹` is faithful on abelian sheaves, and every cartesian abelian sheaf on the total site is
  `a⁻¹` of an abelian sheaf on `D`;
* the unit `K ⟶ Ra_*a⁻¹K` is an isomorphism for every `K` in `D⁺_tors(D)` (cohomological
  descent for torsion coefficients).

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.Augmentation.cartesianTorsionAbSheaf`: the cartesian
  torsion abelian sheaves on the total site.
* `CategoryTheory.SimplicialSiteSituation.Augmentation.derivedPlusTorsionEquivalence`: the
  equivalence `D⁺_tors(D) ≌ D⁺_{𝒜, tors}`, with `derivedPlusTorsionEquivalence_functor` and
  `derivedPlusTorsionEquivalence_inverse` identifying its functors with `a⁻¹` and `Ra_*`.

## Main results

* `SimplicialSiteSituation.Augmentation.cartesianTorsionAbSheaf_totalInverseImageAb`:
  `a⁻¹` carries torsion abelian sheaves to cartesian torsion ones.
* `SimplicialSiteSituation.Augmentation.torsionSheafProperty_of_totalInverseImageAb`:
  a faithful `a⁻¹` reflects torsion abelian sheaves.
* `SimplicialSiteSituation.Augmentation.exists_torsion_totalInverseImageAb_iso`:
  every cartesian torsion abelian sheaf is `a⁻¹` of a torsion abelian sheaf.

## References

* [Stacks Project, Tag 0DHN](https://stacks.math.columbia.edu/tag/0DHN)
* [Stacks Project, Tag 0D7U](https://stacks.math.columbia.edu/tag/0D7U)
* [Stacks Project, Tag 0DD7](https://stacks.math.columbia.edu/tag/0DD7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.SimplicialSiteSituation.Augmentation

variable (S : SimplicialSiteSituation.{u}) (D : Cat.{u, u}) (K : GrothendieckTopology D)
  (a : Augmentation S D K)

/-- The cartesian torsion abelian sheaves on the total site. -/
abbrev cartesianTorsionAbSheaf : ObjectProperty (Sheaf S.totalTopology AddCommGrpCat.{u}) :=
  IsCartesianAbSheaf S ⊓ Stacks.Torsion.torsionSheafProperty S.totalTopology

/-- **`a⁻¹` carries torsion abelian sheaves to cartesian torsion ones.** -/
theorem cartesianTorsionAbSheaf_totalInverseImageAb (G : Sheaf K AddCommGrpCat.{u})
    (hG : Stacks.Torsion.torsionSheafProperty K G) :
    cartesianTorsionAbSheaf S ((totalInverseImageAb S D K a).obj G) :=
  ⟨isCartesianAbSheaf_totalInverseImageAb S D K a G,
    Stacks.Torsion.torsionSheafProperty_obj_of_adjunction (abelianTotalAdjunction S D K a) hG⟩

/-- **A faithful `a⁻¹` reflects torsion abelian sheaves.** -/
theorem torsionSheafProperty_of_totalInverseImageAb [(totalInverseImageAb S D K a).Faithful]
    (G : Sheaf K AddCommGrpCat.{u})
    (hG : Stacks.Torsion.torsionSheafProperty S.totalTopology
      ((totalInverseImageAb S D K a).obj G)) :
    Stacks.Torsion.torsionSheafProperty K G :=
  Stacks.Torsion.torsionSheafProperty_of_torsionSheafProperty_obj (totalInverseImageAb S D K a) hG

/-- **Every cartesian torsion abelian sheaf is `a⁻¹` of a torsion abelian sheaf**, when `a⁻¹` is
faithful and every cartesian abelian sheaf lies in its essential image. -/
theorem exists_torsion_totalInverseImageAb_iso [(totalInverseImageAb S D K a).Faithful]
    (hsurj : ∀ G : Sheaf S.totalTopology AddCommGrpCat.{u}, IsCartesianAbSheaf S G →
      (totalInverseImageAb S D K a).essImage G)
    (M : Sheaf S.totalTopology AddCommGrpCat.{u}) (hM : cartesianTorsionAbSheaf S M) :
    ∃ N, Stacks.Torsion.torsionSheafProperty K N ∧
      Nonempty ((totalInverseImageAb S D K a).obj N ≅ M) := by
  obtain ⟨N, ⟨e⟩⟩ := hsurj M hM.1
  exact ⟨N, torsionSheafProperty_of_totalInverseImageAb S D K a N
    ((Stacks.Torsion.torsionSheafProperty S.totalTopology).prop_of_iso e.symm hM.2), ⟨e⟩⟩

variable [HasDerivedCategory (Sheaf K AddCommGrpCat.{u})]
  [HasDerivedCategory (Sheaf S.totalTopology AddCommGrpCat.{u})]
  [EnoughInjectives (Sheaf K AddCommGrpCat.{u})]
  [EnoughInjectives (Sheaf S.totalTopology AddCommGrpCat.{u})]
  [(totalInverseImageAb S D K a).Faithful]
  (hsurj : ∀ G : Sheaf S.totalTopology AddCommGrpCat.{u}, IsCartesianAbSheaf S G →
    (totalInverseImageAb S D K a).essImage G)
  (hunit : ∀ X, (DerivedCategoryB.derivedCategoryB
      (Stacks.Torsion.torsionSheafProperty K)).inverseImage DerivedCategory.Plus.ι X →
    IsIso ((abelianTotalAdjunction S D K a).rightDerivedFunctorPlus.unit.app X))

/-- **`a⁻¹ : D⁺_tors(D) ⟶ D⁺_{𝒜, tors}` is an equivalence with quasi-inverse `Ra_*`**, granted
that `a⁻¹` is faithful on abelian sheaves with every cartesian abelian sheaf in its essential
image, and cohomological descent `K ≅ Ra_*a⁻¹K` on `D⁺_tors(D)`. -/
def derivedPlusTorsionEquivalence :
    ((DerivedCategoryB.derivedCategoryB
        (Stacks.Torsion.torsionSheafProperty K)).inverseImage
          DerivedCategory.Plus.ι).FullSubcategory ≌
      ((DerivedCategoryB.derivedCategoryB
        (cartesianTorsionAbSheaf S)).inverseImage DerivedCategory.Plus.ι).FullSubcategory :=
  (abelianTotalAdjunction S D K a).rightDerivedFunctorPlusEquivalenceOfProp _ _
    (cartesianTorsionAbSheaf_totalInverseImageAb S D K a)
    (fun G hG ↦ torsionSheafProperty_of_totalInverseImageAb S D K a G hG.2) hunit
    (exists_torsion_totalInverseImageAb_iso S D K a hsurj)

/-- **The forward functor of the equivalence is `a⁻¹`.** -/
theorem derivedPlusTorsionEquivalence_functor :
    (derivedPlusTorsionEquivalence S D K a hsurj hunit).functor =
      Adjunction.rightDerivedFunctorPlusOfProp (L := totalInverseImageAb S D K a) _ _
        (cartesianTorsionAbSheaf_totalInverseImageAb S D K a) :=
  rfl

/-- **The quasi-inverse of the equivalence is `Ra_*`.** -/
theorem derivedPlusTorsionEquivalence_inverse :
    (derivedPlusTorsionEquivalence S D K a hsurj hunit).inverse =
      (abelianTotalAdjunction S D K a).rightDerivedFunctorPlusRightAdjointOfProp _ _
        (fun G hG ↦ torsionSheafProperty_of_totalInverseImageAb S D K a G hG.2) hunit
        (exists_torsion_totalInverseImageAb_iso S D K a hsurj) :=
  rfl

end CategoryTheory.SimplicialSiteSituation.Augmentation

end
