module

public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowNaturalTransformations
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowSerreImage
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CohomologicalDescent.UnitAndCounitIsomorphisms
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationCartesian
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationDerivedInverseImageTriangulated
public import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianWeakSerre
public import StacksFrontier.Homology.PseudoCoherent.Locality
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringSituationDescentAb
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringObjectDerivedPushforwardUnconditional
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringUnit
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringBoundedBelowEquivalence

/-!
# `a⁻¹` as an equivalence onto the cartesian bounded below derived category, for a hypercovering

Let `C` be a site with equalizers and fibre products, let `K` be a hypercovering of it and let
`a` be the augmentation of Stacks 0D8B from the total site `(C/K)_total` to `C`. Let
`𝒜 ⊂ Ab((C/K)_total)` be the weak Serre subcategory of cartesian abelian sheaves, which is
Stacks 0D7J. Stacks 0D8I asserts that

`a⁻¹ : D⁺(C) ⟶ D⁺_𝒜((C/K)_total)`

is an equivalence of categories, with quasi-inverse `R a_*`.

The proof is the one of Stacks 0D7U, carried out for the adjunction `a⁻¹ ⊣ R a_*` on
*abelian* sheaves: the two derived functors restrict to the bounded below subcategories, the
restricted adjunction has both adjoints fully faithful by Stacks 0D7Q and 0D7R, and an adjunction
whose two adjoints are fully faithful is an equivalence. The general form of this argument, for
an augmentation whose unit and counit are known to be invertible, is
`CategoryTheory.SimplicialSiteSituation.Augmentation.derivedTotalInverseImageEquivalence`
in `StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringBoundedBelowEquivalence`; this file
supplies those inputs for the augmentation attached to a hypercovering.

## Main definitions

* `Stacks.CategoryTheory.Hypercovering.derivedTotalInverseImageEquivalenceOfHypercovering'`:
  the equivalence `D⁺(C) ≌ D⁺_𝒜((C/K)_total)` of Stacks 0D8I.

## Main results

* `Stacks.CategoryTheory.Hypercovering.derivedTotalInverseImageEquivalenceOfHypercovering_functor'`
  and `..._inverse'`: its two functors are the restrictions of `a⁻¹` and of `R a_*`.

## Implementation notes

`D⁺(C)` and `D⁺_𝒜((C/K)_total)` are both `DerivedCategoryB.derivedCategoryBPlus`, of the weak
Serre subcategory of *all* abelian sheaves on `C` and of the cartesian abelian sheaves on the
total site respectively. The source writes the first as `D⁺_{Ab(C)}(C)`.

The two inputs of Stacks 0D8G are that the underived unit `F ⟶ a_*a⁻¹F` is an isomorphism
(Stacks 0D8E in its abelian form) and that `a⁻¹` of a K-injective complex computes `R a_*`; the
input of the counit, that every cartesian abelian sheaf on the total site lies in the essential
image of `a⁻¹`, is the remaining clause of Stacks 0D8E (2). All three are provided by
`CategoryTheory.SimplicialSemiRepresentable` for the augmentation of a hypercovering.

The equivalence is the restricted adjunction, not an isomorphism assembled by hand, so its two
functors are the restrictions of `a⁻¹` and of `R a_*` on the nose.

## References

* [Stacks Project, Tag 0D8I](https://stacks.math.columbia.edu/tag/0D8I)
* [Stacks Project, Tag 0D8G](https://stacks.math.columbia.edu/tag/0D8G)
* [Stacks Project, Tag 0D8E](https://stacks.math.columbia.edu/tag/0D8E)
* [Stacks Project, Tag 0D8B](https://stacks.math.columbia.edu/tag/0D8B)
* [Stacks Project, Tag 0D7J](https://stacks.math.columbia.edu/tag/0D7J)
* [Stacks Project, Tag 0D7Q](https://stacks.math.columbia.edu/tag/0D7Q)
* [Stacks Project, Tag 0D7R](https://stacks.math.columbia.edu/tag/0D7R)
* [Stacks Project, Tag 0D7U](https://stacks.math.columbia.edu/tag/0D7U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u

namespace Stacks.CategoryTheory.Hypercovering

open CategoryTheory CategoryTheory.SimplicialSiteSituation

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [SmallCategory C] [HasEqualizers C] [HasPullbacks C] (J : Pretopology C)
  (H : HypercoveringOfTerminal.{u, u} J)

/-- **Stacks 0D8I.** For a site `C` with
equalizers and fibre products, a hypercovering `K` of it, the augmentation `a` of Stacks 0D8B and
the weak Serre subcategory `𝒜 ⊂ Ab((C/K)_total)` of cartesian abelian sheaves of Stacks 0D7J, the
derived inverse image is an equivalence

`a⁻¹ : D⁺(C) ⟶ D⁺_𝒜((C/K)_total)`

with quasi-inverse `R a_*`. Both functors of the equivalence are the restrictions of `a⁻¹` and
of `R a_*` on the nose, since the equivalence is the restricted adjunction.

The `Ra_*`-acyclicity input of Stacks 0D8G, that `a⁻¹` of a K-injective complex computes
`R a_*`, is `CategoryTheory.SimplicialSemiRepresentable`
`.inverseImageComputesDerivedPushforward_of_hypercoveringOfTerminal`. The other input of
Stacks 0D8G, that the underived unit `F ⟶ a_*a⁻¹F` is an isomorphism, is Stacks 0D8E in its
abelian form, which
`CategoryTheory.SimplicialSemiRepresentable.isIso_situationAbelianTotalAdjunctionUnit` proves for
this augmentation. The essential surjectivity input of
`Augmentation.isIso_derivedCounit_app_of_isCartesian`, that every cartesian abelian sheaf on the
total site lies in the essential image of `a⁻¹`, is discharged here by
`CategoryTheory.SimplicialSemiRepresentable`
`.essImage_situationTotalInverseImageAb_of_isCartesianAbSheaf`,
the Stacks 0D8E (2) clause in the spelling of `a⁻¹` as `Augmentation.totalInverseImageAb`. -/
@[stacks 0D8I, sga "4 Vbis 2.2.7" "special case"]
def derivedTotalInverseImageEquivalenceOfHypercovering' :
    (DerivedCategoryB.derivedCategoryBPlus
        (⊤ : ObjectProperty (Sheaf J.toGrothendieck AddCommGrpCat.{u}))).FullSubcategory ≌
      (DerivedCategoryB.derivedCategoryBPlus
        ((hypercoveringSituation J H).IsCartesianAbSheaf)).FullSubcategory :=
  have hall : ∀ X, IsIso ((Augmentation.derivedTotalAdjunction (hypercoveringSituation J H)
      (Cat.of C) J.toGrothendieck (hypercoveringAugmentation J H)).unit.app X) :=
    SimplicialSemiRepresentable.isIso_derivedAugmentationUnit_app_of_hypercovering_unconditional
      J H
  Augmentation.derivedTotalInverseImageEquivalence _ _ _ _ (fun X _ ↦ hall X)
    (fun X hX ↦ Augmentation.isIso_derivedCounit_app_of_isCartesian _ _ _ _ hall
      (fun G hG ↦
        SimplicialSemiRepresentable.essImage_situationTotalInverseImageAb_of_isCartesianAbSheaf
          J H G hG) X hX)

/-- **Stacks 0D8I, the forward functor of the equivalence is `a⁻¹`:** it is the restriction of
the derived inverse image to the bounded below subcategories. -/
@[stacks 0D8I "the forward functor of the equivalence is a⁻¹"]
theorem derivedTotalInverseImageEquivalenceOfHypercovering_functor' :
    (derivedTotalInverseImageEquivalenceOfHypercovering' J H).functor =
      Augmentation.derivedTotalInverseImagePlus (hypercoveringSituation J H) (Cat.of C)
        J.toGrothendieck (hypercoveringAugmentation J H) :=
  rfl

/-- **Stacks 0D8I, the quasi-inverse of the equivalence is `R a_*`:** it is the restriction of
the derived direct image to the bounded below subcategories. -/
@[stacks 0D8I "the quasi-inverse of the equivalence is Ra_*"]
theorem derivedTotalInverseImageEquivalenceOfHypercovering_inverse' :
    (derivedTotalInverseImageEquivalenceOfHypercovering' J H).inverse =
      Augmentation.derivedTotalPushforwardPlus (hypercoveringSituation J H) (Cat.of C)
        J.toGrothendieck (hypercoveringAugmentation J H) :=
  rfl

end Stacks.CategoryTheory.Hypercovering

end
