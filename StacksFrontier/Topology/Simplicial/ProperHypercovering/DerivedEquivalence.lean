module

public import StacksFrontier.Topology.Simplicial.ProperHypercovering.BoundedBelowDescent
public import StacksFrontier.Topology.Simplicial.ProperHypercovering.DerivedUnit
import StacksCore.Tactic.StacksAttribute

/-!
# Proper hypercoverings: `D⁺(X) ≌ D⁺_𝒜(U_Zar)`

Let `U` be a simplicial object of the category `LC` of Hausdorff, locally quasi-compact spaces, let
`a : U → X` be an augmentation and let `𝒜 ⊂ Ab(U_Zar)` be the weak Serre subcategory of cartesian
abelian sheaves. Stacks 0DAH asserts that if `U` is a proper hypercovering of `X`, then

`a⁻¹ : D⁺(X) ⟶ D⁺_𝒜(U_Zar)`

is an equivalence of categories with quasi-inverse `R a_*`, where `a : Sh(U_Zar) → Sh(X)` is the
morphism of topoi of Stacks 09W4.

## The proof

`𝒜` is a weak Serre subcategory by Stacks 0D7J (1) for `U_Zar`
(`Stacks.Topology.Simplicial.ProperHypercovering.isCartesianAb_isWeakSerreClass`). The derived
unit `K ⟶ R a_*(a⁻¹K)` is invertible for `K` in `D⁺(X)` (Stacks 09XS,
`isIso_derivedAdjunction_unit_app_of_isHypercovering`). The cartesian abelian sheaves are the
abelian sheaves of the form `a⁻¹F` (Stacks 0DAG), so the counit is invertible on `D⁺_𝒜(U_Zar)` by
the argument of Stacks 0D7U (`CategoryTheory.Adjunction.derivedPlusEquivalenceOfHomologyIn`).

## Main results

* `Stacks.Topology.Simplicial.ProperHypercovering.derivedEquivalence`: the equivalence.
* `Stacks.Topology.Simplicial.ProperHypercovering.derivedInverseImage_equivalence`:
  **Stacks 0DAH**.

## References

* [Stacks Project, Tag 0DAH](https://stacks.math.columbia.edu/tag/0DAH)
* [Stacks Project, Tag 09XS](https://stacks.math.columbia.edu/tag/09XS)
* [Stacks Project, Tag 0DAG](https://stacks.math.columbia.edu/tag/0DAG)
* [Stacks Project, Tag 0D7J](https://stacks.math.columbia.edu/tag/0D7J)
* [Stacks Project, Tag 0D7U](https://stacks.math.columbia.edu/tag/0D7U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.Topology.Simplicial.ProperHypercovering

open Stacks.Topology Stacks.Topology.Simplicial

variable {Y : SimplicialObject LocallyQuasiCompactHausdorff.{u}}
  {X : LocallyQuasiCompactHausdorff.{u}}
  {a : Y ⟶ (SimplicialObject.const LocallyQuasiCompactHausdorff).obj X}

variable [HasDerivedCategory (Sheaf (Opens.grothendieckTopology
    (locallyQuasiCompactHausdorffToTop.obj X)) AddCommGrpCat.{u})]
  [HasDerivedCategory (Sheaf (SimplicialOpen.grothendieckTopology (U Y)) AddCommGrpCat.{u})]

/-- The equivalence `a⁻¹ : D⁺(X) ≌ D⁺_𝒜(U_Zar)` of Stacks 0DAH, with quasi-inverse `R a_*`. -/
def derivedEquivalence (hyp : MorphismProperty.IsHypercovering properSurjective ⟨Y, X, a⟩) :
    DerivedCategory.Plus (Sheaf (Opens.grothendieckTopology
        (locallyQuasiCompactHausdorffToTop.obj X)) AddCommGrpCat.{u}) ≌
      (cartesianPlus Y).FullSubcategory :=
  derivedEquivalenceOfIsIsoUnit Y X a hyp
    (isIso_derivedAdjunction_unit_app_of_isHypercovering hyp)

/-- **Stacks Project, Tag 0DAH.** Let `U` be a simplicial object of the category `LC` of Hausdorff,
locally quasi-compact spaces and let `a : U → X` be an augmentation. Let `𝒜 ⊂ Ab(U_Zar)` denote
the weak Serre subcategory of cartesian abelian sheaves. If `U` is a proper hypercovering of `X`,
then the functor `a⁻¹` defines an equivalence

`D⁺(X) ⟶ D⁺_𝒜(U_Zar)`

with quasi-inverse `R a_*`, where `a : Sh(U_Zar) → Sh(X)` is the morphism of topoi of Stacks 09W4.

Here `U = Y`; the proper hypercovering condition of Stacks Section 09XA is
`MorphismProperty.IsHypercovering properSurjective`; `𝒜` is `IsCartesianAb (U Y)`, which is a
weak Serre subcategory (the first conjunct); `D⁺_𝒜(U_Zar)` is `cartesianPlus Y`, the objects of
`D⁺(U_Zar)` all of whose cohomology sheaves are cartesian; `a⁻¹` is the exact functor
`(abelianInverseImage Y X a).mapDerivedCategoryPlus` and `R a_*` the total right derived functor
of `a_*`. The derived categories are arbitrary models. -/
@[stacks 0DAH]
theorem derivedInverseImage_equivalence
    (hyp : MorphismProperty.IsHypercovering properSurjective ⟨Y, X, a⟩) :
    ObjectProperty.IsWeakSerreClass (IsCartesianAb (U Y)) ∧
      ∃ e : DerivedCategory.Plus (Sheaf (Opens.grothendieckTopology
          (locallyQuasiCompactHausdorffToTop.obj X)) AddCommGrpCat.{u}) ≌
            (cartesianPlus Y).FullSubcategory,
        e.functor = (cartesianPlus Y).lift (abelianInverseImage Y X a).mapDerivedCategoryPlus
          (cartesianPlus_mapDerivedCategoryPlus_obj Y X a) ∧
        e.inverse = (cartesianPlus Y).ι ⋙ (abelianDirectImage Y X a).rightDerivedFunctorPlus :=
  ⟨inferInstance, derivedEquivalence hyp, rfl, rfl⟩

end Stacks.Topology.Simplicial.ProperHypercovering

end
