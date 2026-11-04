module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedAdjunctionSectionsPullback
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringCohomologicalDescent
public import StacksFrontier.CategoryTheory.Sites.Topos.AbelianPushforwardGlobalSections

/-!
# Derived global sections along an augmentation, on bounded below derived categories

Let `a : Sh(C_total) → Sh(D)` be the total augmentation of an augmented simplicial site
(Stacks 0D70). Global sections are unchanged by the direct image, `Γ(D, a_*F) = Γ(C_total, F)`,
and `a_*` preserves injectives, being right adjoint to the exact functor `a⁻¹`; so
`RΓ(C_total, -) = RΓ(D, -) ∘ Ra_*` on `D⁺` (Cohomology on Sites, Remark 08J6). Together with the
unit `K ⟶ Ra_*(a⁻¹K)` of the derived adjunction `a⁻¹ ⊣ Ra_*` this gives the comparison

```
RΓ(D, K) ⟶ RΓ(D, Ra_*(a⁻¹K)) = RΓ(C_total, a⁻¹K),
```

natural in `K ∈ D⁺(D)`, which is invertible wherever the derived unit is. This is the deduction
of `RΓ(X, K) = RΓ(U, a⁻¹K)` from cohomological descent `K = Ra_*a⁻¹K` in the source.

## Main definitions

* `Augmentation.derivedPlusGlobalSectionsComparison`:
  the comparison `RΓ(D, -) ⟶ a⁻¹ ⋙ RΓ(C_total, -)` on `D⁺(D)`.

## Main results

* `Augmentation.isIso_derivedPlusGlobalSectionsComparison_app`:
  it is invertible at `K` when `K ⟶ Ra_*(a⁻¹K)` is.

## References

* [Stacks Project, Tag 08J6](https://stacks.math.columbia.edu/tag/08J6)
* [Stacks Project, Tag 0D70](https://stacks.math.columbia.edu/tag/0D70)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.SimplicialSiteSituation.Augmentation

variable (S : SimplicialSiteSituation.{u}) (D : Cat.{u, u}) (K : GrothendieckTopology D)
  (a : Augmentation S D K)

/-- The direct image of abelian sheaves along the total augmentation preserves injective
objects, being right adjoint to the exact functor `a⁻¹`. -/
instance preservesInjectiveObjects_abelianTotalPushforward :
    (abelianTotalPushforward S D K a).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (abelianTotalAdjunction S D K a)

variable [HasDerivedCategory (Sheaf K AddCommGrpCat.{u})]
  [HasDerivedCategory (Sheaf S.totalTopology AddCommGrpCat.{u})]
  [HasDerivedCategory AddCommGrpCat.{u}]
  [EnoughInjectives (Sheaf K AddCommGrpCat.{u})]
  [EnoughInjectives (Sheaf S.totalTopology AddCommGrpCat.{u})]

/-- **The comparison `RΓ(D, K) ⟶ RΓ(C_total, a⁻¹K)`** on bounded below derived categories:
`RΓ(D, -)` of the unit `K ⟶ Ra_*(a⁻¹K)` of the derived adjunction `a⁻¹ ⊣ Ra_*`, followed by the
factorization `RΓ(C_total, -) = RΓ(D, -) ∘ Ra_*` of Stacks 08J6, built from
`Γ(D, a_*F) = Γ(C_total, F)`. -/
def derivedPlusGlobalSectionsComparison :
    (Sheaf.Γ K AddCommGrpCat.{u}).rightDerivedFunctorPlus ⟶
      (totalInverseImageAb S D K a).rightDerivedFunctorPlus ⋙
        (Sheaf.Γ S.totalTopology AddCommGrpCat.{u}).rightDerivedFunctorPlus :=
  (abelianTotalAdjunction S D K a).rightDerivedFunctorPlusSectionsPullback
    (Sheaf.Γ K AddCommGrpCat.{u}) (Sheaf.Γ S.totalTopology AddCommGrpCat.{u})
    (Stacks.Topos.AbelianPushforward.abelianPushforwardΓIso S.totalTopology
      (totalMorphismOfTopoi S D K a))

/-- **`RΓ(D, K) = RΓ(C_total, a⁻¹K)` wherever cohomological descent holds**: the comparison is
invertible at every `K ∈ D⁺(D)` at which the unit `K ⟶ Ra_*(a⁻¹K)` is invertible. -/
theorem isIso_derivedPlusGlobalSectionsComparison_app
    (X : DerivedCategory.Plus (Sheaf K AddCommGrpCat.{u}))
    [IsIso ((abelianTotalAdjunction S D K a).rightDerivedFunctorPlus.unit.app X)] :
    IsIso ((derivedPlusGlobalSectionsComparison S D K a).app X) :=
  Adjunction.isIso_rightDerivedFunctorPlusSectionsPullback_app _ _ _ _ X

end CategoryTheory.SimplicialSiteSituation.Augmentation

end
