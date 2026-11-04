module

public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSpaces.FppfHypercoveringDerivedUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSpaces.FppfSpacesEtaleAcyclicUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfToSmallEtaleSchemeVanishing

/-!
# Fppf hypercoverings compute étale cohomology on the spaces-étale site

Let `a : U → X` be an fppf hypercovering of an algebraic space over `S` (Section 0DH4).
`StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSpaces.FppfHypercoveringDerivedUnit` proves the
statements of Stacks 0DH7 and Stacks 0DH8 on the spaces-étale site of `X` from Stacks 0DGG on
single sheaves for `X` and every `U_n` (`AlgebraicGeometry.Space.FppfSpacesEtaleAcyclic`).
That property holds for every algebraic space,
`AlgebraicGeometry.Space.fppfSpacesEtaleAcyclic_of_algebraicSpace` of
`StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSpaces.FppfSpacesEtaleAcyclicUnconditional`. This
file combines the two.

## Main results

In the namespace `AlgebraicGeometry.Space`:

* `IsFppfHypercovering.isIso_derivedUnit`: `K ⟶ Ra_*(a⁻¹K)` is an isomorphism for every
  `K ∈ D⁺(X_spaces,étale)`.
* `IsFppfHypercovering.derivedGlobalSectionsIso`: `RΓ(X_spaces,étale, K) = RΓ(U_étale, a⁻¹K)`.

The same statements on the small étale site `X_étale` of Stacks 03ED, which are those of Stacks
0DH7 and 0DH8, are in
`StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSpaces.FppfHypercoveringSmallEtaleDerived`.

## References

* [Stacks Project, Tag 0DH7](https://stacks.math.columbia.edu/tag/0DH7)
* [Stacks Project, Tag 0DH8](https://stacks.math.columbia.edu/tag/0DH8)
* [Stacks Project, Tag 0DGG](https://stacks.math.columbia.edu/tag/0DGG)
* [Stacks Project, Tag 0DDS](https://stacks.math.columbia.edu/tag/0DDS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : SimplicialObject.Augmented (AlgebraicSpaces B S hS)}

variable [HasDerivedCategory (Sheaf (SpacesEtale.topology B S hS A.right) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory (Sheaf (etaleSimplicialSite A).totalTopology AddCommGrpCat.{u + 1})]

/-- **Fppf hypercoverings and the derived unit, on the spaces-étale site.** Let `a : U → X` be an
fppf hypercovering of an algebraic space and `a : Sh(U_étale) → Sh(X_spaces,étale)` the morphism
of topoi of Section 0DE7. Then for every `K ∈ D⁺(X_spaces,étale)` the map `K ⟶ Ra_*(a⁻¹K)` is an
isomorphism. -/
theorem IsFppfHypercovering.isIso_derivedUnit (hA : IsFppfHypercovering A)
    (K : DerivedCategory.Plus (Sheaf (SpacesEtale.topology B S hS A.right) AddCommGrpCat.{u + 1})) :
    IsIso ((Stacks.ComparingTopologies.derivedPlusAdjunction
      (etaleAugmentationAbelianAdjunction A)).unit.app K) :=
  hA.isIso_derivedUnit_of_fppfSpacesEtaleAcyclic
    (fppfSpacesEtaleAcyclic_of_algebraicSpace A.right)
    (fun n ↦ fppfSpacesEtaleAcyclic_of_algebraicSpace (A.left.obj (op n))) K

variable [HasDerivedCategory AddCommGrpCat.{u + 1}]

/-- **Fppf hypercoverings and derived global sections, on the spaces-étale site.** Under the
hypotheses of `IsFppfHypercovering.isIso_derivedUnit`, `RΓ(X_spaces,étale, K) = RΓ(U_étale, a⁻¹K)`
naturally in `K ∈ D⁺(X_spaces,étale)`. -/
def IsFppfHypercovering.derivedGlobalSectionsIso (hA : IsFppfHypercovering A) :
    (Sheaf.Γ (SpacesEtale.topology B S hS A.right) AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus ≅
      (etaleAugmentationAbelianInverseImage A).mapDerivedCategoryPlus ⋙
        (Sheaf.Γ (etaleSimplicialSite A).totalTopology
          AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus :=
  hA.derivedGlobalSectionsIsoOfFppfSpacesEtaleAcyclic
    (fppfSpacesEtaleAcyclic_of_algebraicSpace A.right)
    (fun n ↦ fppfSpacesEtaleAcyclic_of_algebraicSpace (A.left.obj (op n)))

end AlgebraicGeometry.Space

end
