module

public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowExactAdjunctionEquivalence
public import StacksFrontier.Topology.Simplicial.CartesianAbWeakSerre
public import StacksFrontier.Topology.Simplicial.ProperHypercoveringFullyFaithful

/-!
# Bounded below cohomological descent along a proper hypercovering

Let `U` be a simplicial object of the category `LC` of Hausdorff, locally quasi-compact spaces,
let `a : U ⟶ X` be an augmentation and let `a : Sh(U_Zar) ⟶ Sh(X)` be the morphism of topoi of
Stacks 09W4. Let `𝒜 ⊂ Ab(U_Zar)` be the weak Serre subcategory of cartesian abelian sheaves
(`Stacks.Topology.Simplicial.ProperHypercovering.isCartesianAb_isWeakSerreClass`). This file
sets up the two derived functors

`a⁻¹ : D⁺(X) ⥤ D⁺(U_Zar)` and `R a_* : D⁺(U_Zar) ⥤ D⁺(X)`

and the adjunction between them, and proves the formal part of Stacks 0DAH: for a proper
hypercovering, as soon as the unit `K ⟶ R a_*(a⁻¹K)` is invertible on `D⁺(X)`, the functor `a⁻¹`
is an equivalence `D⁺(X) ≌ D⁺_𝒜(U_Zar)` with quasi-inverse `R a_*`.

## Main definitions

* `Stacks.Topology.Simplicial.ProperHypercovering.cartesianPlus`: `D⁺_𝒜(U_Zar)`.
* `Stacks.Topology.Simplicial.ProperHypercovering.derivedAdjunction`: `a⁻¹ ⊣ R a_*` on bounded
  below derived categories.
* `Stacks.Topology.Simplicial.ProperHypercovering.derivedEquivalenceOfIsIsoUnit`: the equivalence
  `D⁺(X) ≌ D⁺_𝒜(U_Zar)`, given the invertibility of the derived unit.

## References

* [Stacks Project, Tag 0DAH](https://stacks.math.columbia.edu/tag/0DAH)
* [Stacks Project, Tag 0DAG](https://stacks.math.columbia.edu/tag/0DAG)
* [Stacks Project, Tag 09XS](https://stacks.math.columbia.edu/tag/09XS)
* [Stacks Project, Tag 0D7J](https://stacks.math.columbia.edu/tag/0D7J)
* [Stacks Project, Tag 0D7U](https://stacks.math.columbia.edu/tag/0D7U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.Topology.Simplicial.ProperHypercovering

open Stacks.Topology Stacks.Topology.Simplicial

variable (Y : SimplicialObject LocallyQuasiCompactHausdorff.{u})
  (X : LocallyQuasiCompactHausdorff.{u})
  (a : Y ⟶ (SimplicialObject.const LocallyQuasiCompactHausdorff).obj X)

/-- `a⁻¹` on abelian sheaves is left exact (Stacks 04JC). -/
instance abelianInverseImage_preservesFiniteLimits :
    PreservesFiniteLimits (abelianInverseImage Y X a) :=
  Sites.abelianInverseImage_preservesFiniteLimits (augmentationTopoi Y X a)

/-- `a⁻¹` on abelian sheaves is right exact (Stacks 04JC). -/
instance abelianInverseImage_preservesFiniteColimits :
    PreservesFiniteColimits (abelianInverseImage Y X a) :=
  Sites.abelianInverseImage_preservesFiniteColimits (augmentationTopoi Y X a)

/-- `a⁻¹` on abelian sheaves is additive. -/
instance abelianInverseImage_additive : (abelianInverseImage Y X a).Additive := by
  have : (abelianInverseImage Y X a).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_preserves_terminal_object
  exact Functor.additive_of_preserves_binary_products _

/-- `a_*` on abelian sheaves is additive. -/
instance abelianDirectImage_additive : (abelianDirectImage Y X a).Additive :=
  (abelianAdjunction Y X a).right_adjoint_additive

variable [HasDerivedCategory (Sheaf (Opens.grothendieckTopology
    (locallyQuasiCompactHausdorffToTop.obj X)) AddCommGrpCat.{u})]
  [HasDerivedCategory (Sheaf (SimplicialOpen.grothendieckTopology (U Y)) AddCommGrpCat.{u})]

/-- `D⁺_𝒜(U_Zar)`: the bounded below derived objects of abelian sheaves on `U_Zar` all of whose
cohomology sheaves are cartesian. -/
abbrev cartesianPlus :
    ObjectProperty (DerivedCategory.Plus
      (Sheaf (SimplicialOpen.grothendieckTopology (U Y)) AddCommGrpCat.{u})) :=
  DerivedCategory.Plus.homologyIn (IsCartesianAb (U Y))

/-- The adjunction `a⁻¹ ⊣ R a_*` on bounded below derived categories: `a⁻¹` is exact and acts
degreewise, `R a_*` is the total right derived functor of `a_*`. -/
abbrev derivedAdjunction :
    (abelianInverseImage Y X a).mapDerivedCategoryPlus ⊣
      (abelianDirectImage Y X a).rightDerivedFunctorPlus :=
  Stacks.ComparingTopologies.derivedPlusAdjunction (abelianAdjunction Y X a)

/-- `a⁻¹` carries `D⁺(X)` into `D⁺_𝒜(U_Zar)`. -/
theorem cartesianPlus_mapDerivedCategoryPlus_obj
    (K : DerivedCategory.Plus (Sheaf (Opens.grothendieckTopology
      (locallyQuasiCompactHausdorffToTop.obj X)) AddCommGrpCat.{u})) :
    cartesianPlus Y ((abelianInverseImage Y X a).mapDerivedCategoryPlus.obj K) :=
  CategoryTheory.Adjunction.homologyIn_mapDerivedCategoryPlus_obj _
    (isCartesianAb_abelianInverseImage Y X a) K

/-- **The derived unit `K ⟶ R a_*(a⁻¹K)` is invertible on `D⁺(X)`** for a proper hypercovering,
as soon as `R^q a_*(a⁻¹F) = 0` for every abelian sheaf `F` on `X` and every `q > 0`. -/
theorem isIso_derivedAdjunction_unit_app_of_isZero_rightDerived
    (hyp : MorphismProperty.IsHypercovering properSurjective ⟨Y, X, a⟩)
    (hvan : ∀ (F : Sheaf (Opens.grothendieckTopology (locallyQuasiCompactHausdorffToTop.obj X))
      AddCommGrpCat.{u}) (q : ℕ), 0 < q →
        IsZero (((abelianDirectImage Y X a).rightDerived q).obj
          ((abelianInverseImage Y X a).obj F)))
    (K : DerivedCategory.Plus (Sheaf (Opens.grothendieckTopology
      (locallyQuasiCompactHausdorffToTop.obj X)) AddCommGrpCat.{u})) :
    IsIso ((derivedAdjunction Y X a).unit.app K) :=
  CategoryTheory.Adjunction.isIso_derivedPlusAdjunction_unit_app_of_isZero_rightDerived _
    (abelianInverseImage_fullyFaithful_of_isHypercovering Y X a hyp).2.2.2.1 hvan K

/-- **`a⁻¹ : D⁺(X) ≌ D⁺_𝒜(U_Zar)` with quasi-inverse `R a_*`**, for a proper hypercovering, given
that the unit `K ⟶ R a_*(a⁻¹K)` is invertible for every `K` of `D⁺(X)`. -/
def derivedEquivalenceOfIsIsoUnit
    (hyp : MorphismProperty.IsHypercovering properSurjective ⟨Y, X, a⟩)
    (hunit : ∀ K, IsIso ((derivedAdjunction Y X a).unit.app K)) :
    DerivedCategory.Plus (Sheaf (Opens.grothendieckTopology
        (locallyQuasiCompactHausdorffToTop.obj X)) AddCommGrpCat.{u}) ≌
      (cartesianPlus Y).FullSubcategory :=
  CategoryTheory.Adjunction.derivedPlusEquivalenceOfHomologyIn (abelianAdjunction Y X a)
    (IsCartesianAb (U Y)) (isCartesianAb_abelianInverseImage Y X a) hunit
    (fun G hG ↦ ((abelianInverseImage_fullyFaithful_of_isHypercovering Y X a hyp).2.2.1 G).2 hG)

/-- The forward functor of `derivedEquivalenceOfIsIsoUnit` is `a⁻¹`. -/
theorem derivedEquivalenceOfIsIsoUnit_functor
    (hyp : MorphismProperty.IsHypercovering properSurjective ⟨Y, X, a⟩)
    (hunit : ∀ K, IsIso ((derivedAdjunction Y X a).unit.app K)) :
    (derivedEquivalenceOfIsIsoUnit Y X a hyp hunit).functor =
      (cartesianPlus Y).lift (abelianInverseImage Y X a).mapDerivedCategoryPlus
        (cartesianPlus_mapDerivedCategoryPlus_obj Y X a) :=
  rfl

/-- The quasi-inverse of `derivedEquivalenceOfIsIsoUnit` is `R a_*`. -/
theorem derivedEquivalenceOfIsIsoUnit_inverse
    (hyp : MorphismProperty.IsHypercovering properSurjective ⟨Y, X, a⟩)
    (hunit : ∀ K, IsIso ((derivedAdjunction Y X a).unit.app K)) :
    (derivedEquivalenceOfIsIsoUnit Y X a hyp hunit).inverse =
      (cartesianPlus Y).ι ⋙ (abelianDirectImage Y X a).rightDerivedFunctorPlus :=
  rfl

end Stacks.Topology.Simplicial.ProperHypercovering

end
