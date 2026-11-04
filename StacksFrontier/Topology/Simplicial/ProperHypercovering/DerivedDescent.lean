module

public import StacksFrontier.Topology.Simplicial.ProperHypercovering.DerivedUnit
public import StacksFrontier.Topology.Simplicial.ProperHypercovering.BoundedBelowDescent
public import StacksFrontier.Topology.Simplicial.AugmentationGlobalSections
public import StacksFrontier.Algebra.Homology.DerivedCategory.LerayDerivedUnitComparison
import StacksCore.Tactic.StacksAttribute

/-!
# Proper hypercoverings compute cohomology

Let `U` be a simplicial object of the category `LC` of Hausdorff, locally quasi-compact spaces and
let `a : U → X` be an augmentation which is a proper hypercovering of `X` (Stacks Section 09XA).
Let `a : Sh(U_Zar) → Sh(X)` be the morphism of topoi of Stacks 09W4. This file proves
**Stacks 09XC**: `RΓ(X, K) = RΓ(U_Zar, a^{-1}K)` for `K ∈ D⁺(X)`
(`Stacks.Topology.Simplicial.ProperHypercovering.derivedGlobalSectionsIsoOfIsHypercovering`).

## The proof

The source deduces Stacks 09XC from Stacks 09XS, `K = Ra_*(a^{-1}K)`, and from
`RΓ(U_Zar, -) = RΓ(X, -) ∘ Ra_*` (Stacks 08J6). The second is the Leray factorization of
Stacks 015M for the underived identity `Γ(X, a_*F) = Γ(U_Zar, F)`
(`Stacks.Topology.Simplicial.augmentationPushforwardAbGlobalSectionsIso`); the comparison map
`RΓ(X, K) → RΓ(U_Zar, a^{-1}K)` is the pullback on derived sections
`Stacks.LerayPullbackComparison.lerayPullback`, `RΓ(X, -)` of the unit `K → Ra_*a^{-1}K` followed
by the inverse of that factorization, which is invertible wherever the unit is. The unit is the
unit of the derived adjunction `a^{-1} ⊣ Ra_*`
(`Stacks.LerayPullbackComparison.derivedUnit_eq_derivedPlusAdjunction_unit`), invertible by
Stacks 09XS (`isIso_derivedAdjunction_unit_app_of_isHypercovering`).

The derived categories are arbitrary models (`HasDerivedCategory`).

## References

* [Stacks Project, Tag 09XC](https://stacks.math.columbia.edu/tag/09XC)
* [Stacks Project, Tag 09XS](https://stacks.math.columbia.edu/tag/09XS)
* [Stacks Project, Tag 08J6](https://stacks.math.columbia.edu/tag/08J6)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.Topology.Simplicial.ProperHypercovering

open Stacks.Topology Stacks.Topology.Simplicial
open Stacks.CategoryTheory.Hypercovering CategoryTheory.SimplicialSemiRepresentable

variable {Y : SimplicialObject LocallyQuasiCompactHausdorff.{u}}
  {T : LocallyQuasiCompactHausdorff.{u}}
  {b : Y ⟶ (SimplicialObject.const LocallyQuasiCompactHausdorff).obj T}

section Derived

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable [HasDerivedCategory
    (Sheaf (Opens.grothendieckTopology (locallyQuasiCompactHausdorffToTop.obj T))
      AddCommGrpCat.{u})]
  [HasDerivedCategory (Sheaf (SimplicialOpen.grothendieckTopology (U Y)) AddCommGrpCat.{u})]

variable (Y T b) in
/-- The direct image `a_*` of abelian sheaves preserves injective objects, being right adjoint to
the exact functor `a^{-1}`. -/
instance preservesInjectiveObjects_abelianDirectImage :
    (abelianDirectImage Y T b).PreservesInjectiveObjects :=
  ⟨fun {I} hI => (abelianAdjunction Y T b).map_injective I hI⟩

variable (Y T b) in
/-- **`Γ(X, a_*F) = Γ(U_Zar, F)`**, naturally in the abelian sheaf `F` on `U_Zar`: the underived
identity behind Stacks 08J6 for `a : Sh(U_Zar) → Sh(X)`. -/
def abelianDirectImageGlobalSectionsIso :
    abelianDirectImage Y T b ⋙
        Sheaf.Γ (Opens.grothendieckTopology (locallyQuasiCompactHausdorffToTop.obj T))
          AddCommGrpCat.{u} ≅
      Sheaf.Γ (SimplicialOpen.grothendieckTopology (U Y)) AddCommGrpCat.{u} :=
  augmentationPushforwardAbGlobalSectionsIso (U Y) (locallyQuasiCompactHausdorffToTop.obj T)
    (topologicalAugmentation Y T b)

/-- The global sections functor on abelian sheaves on the space `X` is additive. -/
instance additive_sheafΓ_opens :
    (Sheaf.Γ (Opens.grothendieckTopology (locallyQuasiCompactHausdorffToTop.obj T))
      AddCommGrpCat.{u}).Additive :=
  haveI : PreservesLimitsOfSize.{0, 0}
      (Sheaf.Γ (Opens.grothendieckTopology (locallyQuasiCompactHausdorffToTop.obj T))
        AddCommGrpCat.{u}) :=
    (constantSheafΓAdj _ AddCommGrpCat.{u}).rightAdjoint_preservesLimits
  Functor.additive_of_preserves_binary_products _

/-- The global sections functor on abelian sheaves on the space `X` preserves finite limits. -/
instance preservesFiniteLimits_sheafΓ_opens :
    PreservesFiniteLimits
      (Sheaf.Γ (Opens.grothendieckTopology (locallyQuasiCompactHausdorffToTop.obj T))
        AddCommGrpCat.{u}) :=
  haveI : PreservesLimitsOfSize.{0, 0}
      (Sheaf.Γ (Opens.grothendieckTopology (locallyQuasiCompactHausdorffToTop.obj T))
        AddCommGrpCat.{u}) :=
    (constantSheafΓAdj _ AddCommGrpCat.{u}).rightAdjoint_preservesLimits
  PreservesLimitsOfSize.preservesFiniteLimits _

variable (Y) in
/-- The global sections functor on abelian sheaves on the site `U_Zar` is additive. -/
instance additive_sheafΓ_simplicialOpen :
    (Sheaf.Γ (SimplicialOpen.grothendieckTopology (U Y)) AddCommGrpCat.{u}).Additive :=
  haveI : PreservesLimitsOfSize.{0, 0}
      (Sheaf.Γ (SimplicialOpen.grothendieckTopology (U Y)) AddCommGrpCat.{u}) :=
    (constantSheafΓAdj _ AddCommGrpCat.{u}).rightAdjoint_preservesLimits
  Functor.additive_of_preserves_binary_products _

variable [HasDerivedCategory AddCommGrpCat.{u}]

variable (b) in
/-- **Stacks Project, Tag 09XC.** Let `U` be a simplicial object of `LC` and let `a : U → X` be an
augmentation. If `U` is a proper hypercovering of `X`, then

`RΓ(X, K) = RΓ(U_Zar, a^{-1}K)`

for `K ∈ D⁺(X)`, where `a : Sh(U_Zar) → Sh(X)` is the morphism of topoi of Lemma 09W4.

Here `U = Y`, `X = T` and `a = b`; the proper hypercovering condition of Stacks Section 09XA is
`MorphismProperty.IsHypercovering properSurjective`, `a^{-1}` is the inverse image of abelian
sheaves along the morphism of topoi of Stacks 09W4, extended to `D⁺` degreewise because it is
exact, and `RΓ(X, -)`, `RΓ(U_Zar, -)` are the right derived functors on `D⁺` of the global
sections functors of the space `X` and of the site `U_Zar`. The derived categories are arbitrary
models. The isomorphism is the canonical one: its forward map is the pullback on derived
sections, `RΓ(X, -)` of the unit `K → Ra_*a^{-1}K` followed by the factorization
`RΓ(U_Zar, -) = RΓ(X, -) ∘ Ra_*` of Stacks 08J6 (`derivedGlobalSectionsIsoOfIsHypercovering_hom`).
It is invertible because the unit is, by `isIso_derivedAdjunction_unit_app_of_isHypercovering`
(Stacks 09XS). -/
@[stacks 09XC]
def derivedGlobalSectionsIsoOfIsHypercovering
    (hyp : MorphismProperty.IsHypercovering properSurjective ⟨Y, T, b⟩) :
    (Sheaf.Γ (Opens.grothendieckTopology (locallyQuasiCompactHausdorffToTop.obj T))
        AddCommGrpCat.{u}).rightDerivedFunctorPlus ≅
      (abelianInverseImage Y T b).mapDerivedCategoryPlus ⋙
        (Sheaf.Γ (SimplicialOpen.grothendieckTopology (U Y))
          AddCommGrpCat.{u}).rightDerivedFunctorPlus :=
  have : ∀ K, IsIso ((Stacks.LerayPullbackComparison.lerayPullback (abelianAdjunction Y T b)
      (Sheaf.Γ (Opens.grothendieckTopology (locallyQuasiCompactHausdorffToTop.obj T))
        AddCommGrpCat.{u})
      (Sheaf.Γ (SimplicialOpen.grothendieckTopology (U Y)) AddCommGrpCat.{u})
      (abelianDirectImageGlobalSectionsIso Y T b)).app K) := fun K =>
    have : IsIso
        ((Stacks.LerayPullbackComparison.derivedUnit (abelianAdjunction Y T b)).app K) := by
      rw [Stacks.LerayPullbackComparison.derivedUnit_eq_derivedPlusAdjunction_unit]
      exact isIso_derivedAdjunction_unit_app_of_isHypercovering hyp K
    Stacks.LerayPullbackComparison.isIso_lerayPullback_app _ _ _ _ K
  have := NatIso.isIso_of_isIso_app (Stacks.LerayPullbackComparison.lerayPullback
    (abelianAdjunction Y T b)
    (Sheaf.Γ (Opens.grothendieckTopology (locallyQuasiCompactHausdorffToTop.obj T))
      AddCommGrpCat.{u})
    (Sheaf.Γ (SimplicialOpen.grothendieckTopology (U Y)) AddCommGrpCat.{u})
    (abelianDirectImageGlobalSectionsIso Y T b))
  asIso (Stacks.LerayPullbackComparison.lerayPullback (abelianAdjunction Y T b)
    (Sheaf.Γ (Opens.grothendieckTopology (locallyQuasiCompactHausdorffToTop.obj T))
      AddCommGrpCat.{u})
    (Sheaf.Γ (SimplicialOpen.grothendieckTopology (U Y)) AddCommGrpCat.{u})
    (abelianDirectImageGlobalSectionsIso Y T b))

/-- The isomorphism of Stacks 09XC is the pullback on derived sections along
`a : Sh(U_Zar) → Sh(X)`. -/
theorem derivedGlobalSectionsIsoOfIsHypercovering_hom
    (hyp : MorphismProperty.IsHypercovering properSurjective ⟨Y, T, b⟩) :
    (derivedGlobalSectionsIsoOfIsHypercovering b hyp).hom =
      Stacks.LerayPullbackComparison.lerayPullback (abelianAdjunction Y T b)
        (Sheaf.Γ (Opens.grothendieckTopology (locallyQuasiCompactHausdorffToTop.obj T))
          AddCommGrpCat.{u})
        (Sheaf.Γ (SimplicialOpen.grothendieckTopology (U Y)) AddCommGrpCat.{u})
        (abelianDirectImageGlobalSectionsIso Y T b) :=
  rfl

end Derived

end Stacks.Topology.Simplicial.ProperHypercovering

end
