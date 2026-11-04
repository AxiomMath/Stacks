module

public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSpaces.FppfHypercoveringDerivedUnitOfSchemes
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleConstantSheaf
public import StacksFrontier.Algebra.Homology.DerivedCategory.LerayDerivedUnitComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.DerivedPlusAdjunctionEquivalence
import StacksCore.Tactic.StacksAttribute

/-!
# Fppf hypercoverings compute étale cohomology (Stacks 0DH7, 0DH8)

Let `S` be a scheme, `X` an algebraic space over `S`, `U` a simplicial algebraic space over `S`
and `a : U → X` an augmentation which is an fppf hypercovering of `X`. Let
`a : Sh(U_étale) → Sh(X_étale)` be the morphism of topoi of Section 0DE7. Then

* `K ⟶ Ra_*(a⁻¹K)` is an isomorphism for `K ∈ D⁺(X_étale)` (**Stacks 0DH7**);
* `RΓ(X_étale, K) = RΓ(U_étale, a⁻¹K)` for `K ∈ D⁺(X_étale)` (**Stacks 0DH8**).

## The small étale site of `X`

Section 0DE7 works with the small étale site `X_étale` of Properties of Spaces, Definition 03ED,
whose objects are schemes étale over `X`, and identifies its topos with that of the spaces-étale
site `X_spaces,étale` through the inclusion `X_étale ⊂ X_spaces,étale` of Stacks 03G1
(`AlgebraicGeometry.Space.comparisonFunctor`, restriction along which is an equivalence by
`AlgebraicGeometry.Space.comparisonFunctor_sheafEquivalence`). As in the statements registered for
Stacks 0DH6, the functor `a⁻¹ : Ab(X_étale) ⥤ Ab(U_étale)` is the inverse of that equivalence
followed by the inverse image of the morphism of topoi of Section 0DE7, and `a_*` is the direct
image followed by restriction to `X_étale`; the adjunction `a⁻¹ ⊣ a_*` is the composite of the
two. The site of `U_étale` is the total site of the simplicial site whose `n`-th site is the
spaces-étale site of `U_n` (Lemma 09WC), as in Stacks 0DH6.

## Main results

* `CategoryTheory.Functor.IsDenseSubsite.sheafPushforwardContinuousCompGammaIso`: restriction to
  a dense subsite does not change global sections.
* `AlgebraicGeometry.Space.IsFppfHypercovering.isIso_smallEtaleDerivedUnit`: **Stacks 0DH7**.
* `AlgebraicGeometry.Space.IsFppfHypercovering.smallEtaleDerivedGlobalSectionsIso`:
  **Stacks 0DH8**.

## Implementation notes

Both statements are first proved on `X_spaces,étale`
(`AlgebraicGeometry.Space.IsFppfHypercovering.isIso_derivedUnit`), and carried to `X_étale`:
the derived unit by
`CategoryTheory.Adjunction.isIso_derivedPlusAdjunction_unit_app_comp_equivalence`, and the
derived global sections by the pullback on derived global sections
`Stacks.LerayPullbackComparison.lerayPullback` of the composite adjunction, which is invertible
wherever the derived unit is (the factorization `RΓ(U_étale, -) = RΓ(X_étale, -) ∘ Ra_*` of Stacks
08J6, used in the source's proof of 0DH8).

## References

* [Stacks Project, Tag 0DH7](https://stacks.math.columbia.edu/tag/0DH7)
* [Stacks Project, Tag 0DH8](https://stacks.math.columbia.edu/tag/0DH8)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 08J6](https://stacks.math.columbia.edu/tag/08J6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory.Functor.IsDenseSubsite

variable {C D : Type*} [Category* C] [Category* D] (J : GrothendieckTopology C)
  (K : GrothendieckTopology D) (G : C ⥤ D) [G.IsDenseSubsite J K] (A : Type*) [Category* A]
  [(G.sheafPushforwardContinuous A J K).IsEquivalence] [HasWeakSheafify J A]
  [HasWeakSheafify K A] [HasGlobalSectionsFunctor J A] [HasGlobalSectionsFunctor K A]

/-- **Restriction to a dense subsite does not change global sections**: `Γ(C, F|_C) = Γ(D, F)`,
naturally in the sheaf `F` on `D`. Both sides are right adjoint to the constant sheaf functor on
`D`, the restriction of a constant sheaf being constant
(`CategoryTheory.Functor.IsDenseSubsite.constantSheafCompSheafPushforwardContinuousIso`). -/
def sheafPushforwardContinuousCompGammaIso :
    G.sheafPushforwardContinuous A J K ⋙ Sheaf.Γ J A ≅ Sheaf.Γ K A :=
  (((constantSheafΓAdj J A).comp
      (G.sheafPushforwardContinuous A J K).asEquivalence.symm.toAdjunction).ofNatIsoLeft
    (Functor.isoWhiskerRight (constantSheafCompSheafPushforwardContinuousIso J K G A).symm
        (G.sheafPushforwardContinuous A J K).inv ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (G.sheafPushforwardContinuous A J K).asEquivalence.unitIso.symm ≪≫
      Functor.rightUnitor _)).rightAdjointUniq (constantSheafΓAdj K A)

end CategoryTheory.Functor.IsDenseSubsite

namespace AlgebraicGeometry.Space

open Stacks.Topos.AbelianPushforward

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : SimplicialObject.Augmented (AlgebraicSpaces B S hS)}

variable (A) in
/-- The inverse of the equivalence `Ab(X_spaces,étale) ≌ Ab(X_étale)` of Stacks 03G1, restriction
along the comparison functor, is additive. -/
instance smallEtaleAbelianComparisonInverse_additive :
    ((comparisonFunctor B S hS A.right).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (SmallEtale.topology B S hS A.right.1)
      (SpacesEtale.topology B S hS A.right)).asEquivalence.symm.functor.Additive :=
  Functor.additive_of_preserves_binary_products _

variable [HasDerivedCategory (Sheaf (SmallEtale.topology B S hS A.right.1) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory (Sheaf (SpacesEtale.topology B S hS A.right) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory (Sheaf (etaleSimplicialSite A).totalTopology AddCommGrpCat.{u + 1})]

/-- **Stacks 0DH7.** Let `S` be a scheme, `X` an algebraic space over `S`, `U` a simplicial
algebraic space over `S` and `a : U → X` an augmentation which is an fppf hypercovering of `X`.
Then for every `K ∈ D⁺(X_étale)` the map `K ⟶ Ra_*(a⁻¹K)` is an isomorphism. Here
`a : Sh(U_étale) → Sh(X_étale)` is the morphism of topoi of Section 0DE7, with `X_étale` the small
étale site of `X` (Stacks 03ED) and its abelian sheaves identified with those of `X_spaces,étale`
by the equivalence of Stacks 03G1, so that `a⁻¹ ⊣ a_*` is the composite of that equivalence with
the adjunction of Section 0DE7; the map is the unit of the derived adjunction `a⁻¹ ⊣ Ra_*` on
bounded below derived categories. -/
@[stacks 0DH7]
theorem IsFppfHypercovering.isIso_smallEtaleDerivedUnit (hA : IsFppfHypercovering A)
    (K : DerivedCategory.Plus
      (Sheaf (SmallEtale.topology B S hS A.right.1) AddCommGrpCat.{u + 1})) :
    IsIso ((Stacks.ComparingTopologies.derivedPlusAdjunction
      (((comparisonFunctor B S hS A.right).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (SmallEtale.topology B S hS A.right.1)
        (SpacesEtale.topology B S hS A.right)).asEquivalence.symm.toAdjunction.comp
          (etaleAugmentationAbelianAdjunction A))).unit.app K) :=
  CategoryTheory.Adjunction.isIso_derivedPlusAdjunction_unit_app_comp_equivalence _
    (etaleAugmentationAbelianAdjunction A) hA.isIso_derivedUnit K

variable (A) in
/-- `Γ(X_étale, -)` is additive. -/
instance sheafΓ_smallEtale_additive :
    (Sheaf.Γ (SmallEtale.topology B S hS A.right.1) AddCommGrpCat.{u + 1}).Additive :=
  (constantSheafΓAdj _ AddCommGrpCat.{u + 1}).right_adjoint_additive

variable (A) in
/-- `Γ(X_étale, -)` is left exact. -/
instance sheafΓ_smallEtale_preservesFiniteLimits :
    PreservesFiniteLimits (Sheaf.Γ (SmallEtale.topology B S hS A.right.1) AddCommGrpCat.{u + 1}) :=
  have : PreservesLimitsOfSize.{0, 0}
      (Sheaf.Γ (SmallEtale.topology B S hS A.right.1) AddCommGrpCat.{u + 1}) :=
    (constantSheafΓAdj _ AddCommGrpCat.{u + 1}).rightAdjoint_preservesLimits
  PreservesLimitsOfSize.preservesFiniteLimits _

variable (A) in
/-- The direct image `a_* : Ab(U_étale) ⥤ Ab(X_étale)`, the direct image of Section 0DE7 followed
by restriction to `X_étale`, preserves injective objects, being right adjoint to an exact
functor. -/
instance smallEtaleAugmentationAbelianDirectImage_preservesInjectiveObjects :
    (abelianPushforward (etaleSimplicialSite A).totalTopology (etaleAugmentationMorphism A) ⋙
      ((comparisonFunctor B S hS A.right).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (SmallEtale.topology B S hS A.right.1)
        (SpacesEtale.topology B S hS
          A.right)).asEquivalence.symm.inverse).PreservesInjectiveObjects :=
  ⟨fun {I} hI => (((comparisonFunctor B S hS A.right).sheafPushforwardContinuous
    AddCommGrpCat.{u + 1} (SmallEtale.topology B S hS A.right.1)
    (SpacesEtale.topology B S hS A.right)).asEquivalence.symm.toAdjunction.comp
      (etaleAugmentationAbelianAdjunction A)).map_injective I hI⟩

variable (A) in
/-- `Γ(X_étale, a_*F) = Γ(U_étale, F)` for abelian sheaves `F` on `U_étale`, with `a_*` the direct
image to `X_étale`. -/
def smallEtaleAugmentationGammaIso :
    (abelianPushforward (etaleSimplicialSite A).totalTopology (etaleAugmentationMorphism A) ⋙
      ((comparisonFunctor B S hS A.right).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (SmallEtale.topology B S hS A.right.1)
        (SpacesEtale.topology B S hS A.right)).asEquivalence.symm.inverse) ⋙
        Sheaf.Γ (SmallEtale.topology B S hS A.right.1) AddCommGrpCat.{u + 1} ≅
      Sheaf.Γ (etaleSimplicialSite A).totalTopology AddCommGrpCat.{u + 1} :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (CategoryTheory.Functor.IsDenseSubsite.sheafPushforwardContinuousCompGammaIso
        (SmallEtale.topology B S hS A.right.1) (SpacesEtale.topology B S hS A.right)
        (comparisonFunctor B S hS A.right) AddCommGrpCat.{u + 1}) ≪≫
    etaleAugmentationGammaIso A

variable [HasDerivedCategory AddCommGrpCat.{u + 1}]

/-- **Stacks 0DH8.** Let `S` be a scheme, `X` an algebraic space over `S`, `U` a simplicial
algebraic space over `S` and `a : U → X` an augmentation which is an fppf hypercovering of `X`.
Then `RΓ(X_étale, K) = RΓ(U_étale, a⁻¹K)` for `K ∈ D⁺(X_étale)`, naturally in `K`. Here
`a : Sh(U_étale) → Sh(X_étale)` is the morphism of topoi of Section 0DE7, with `X_étale` the small
étale site of `X` (Stacks 03ED) and `a⁻¹` as in `IsFppfHypercovering.isIso_smallEtaleDerivedUnit`.
The isomorphism is the pullback on derived global sections: `RΓ(X_étale, -)` of the map
`K ⟶ Ra_*(a⁻¹K)` of Stacks 0DH7 followed by the factorization
`RΓ(U_étale, -) = RΓ(X_étale, -) ∘ Ra_*` of Stacks 08J6. -/
@[stacks 0DH8]
def IsFppfHypercovering.smallEtaleDerivedGlobalSectionsIso (hA : IsFppfHypercovering A) :
    (Sheaf.Γ (SmallEtale.topology B S hS A.right.1) AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus ≅
      (((comparisonFunctor B S hS A.right).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (SmallEtale.topology B S hS A.right.1)
        (SpacesEtale.topology B S hS A.right)).asEquivalence.symm.functor ⋙
          etaleAugmentationAbelianInverseImage A).mapDerivedCategoryPlus ⋙
        (Sheaf.Γ (etaleSimplicialSite A).totalTopology
          AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus :=
  let adj := ((comparisonFunctor B S hS A.right).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (SmallEtale.topology B S hS A.right.1)
    (SpacesEtale.topology B S hS A.right)).asEquivalence.symm.toAdjunction.comp
      (etaleAugmentationAbelianAdjunction A)
  have : ∀ K, IsIso ((Stacks.LerayPullbackComparison.lerayPullback adj
      (Sheaf.Γ (SmallEtale.topology B S hS A.right.1) AddCommGrpCat.{u + 1})
      (Sheaf.Γ (etaleSimplicialSite A).totalTopology AddCommGrpCat.{u + 1})
      (smallEtaleAugmentationGammaIso A)).app K) := fun K ↦ by
    have : IsIso ((Stacks.LerayPullbackComparison.derivedUnit adj).app K) := by
      rw [Stacks.LerayPullbackComparison.derivedUnit_eq_derivedPlusAdjunction_unit]
      exact hA.isIso_smallEtaleDerivedUnit K
    exact Stacks.LerayPullbackComparison.isIso_lerayPullback_app _ _ _ _ K
  have := NatIso.isIso_of_isIso_app (Stacks.LerayPullbackComparison.lerayPullback adj
    (Sheaf.Γ (SmallEtale.topology B S hS A.right.1) AddCommGrpCat.{u + 1})
    (Sheaf.Γ (etaleSimplicialSite A).totalTopology AddCommGrpCat.{u + 1})
    (smallEtaleAugmentationGammaIso A))
  asIso (Stacks.LerayPullbackComparison.lerayPullback adj
    (Sheaf.Γ (SmallEtale.topology B S hS A.right.1) AddCommGrpCat.{u + 1})
    (Sheaf.Γ (etaleSimplicialSite A).totalTopology AddCommGrpCat.{u + 1})
    (smallEtaleAugmentationGammaIso A))

end AlgebraicGeometry.Space

end
