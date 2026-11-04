module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Embedded
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.MinimalSupport
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Reduced
public import StacksFrontier.AlgebraicGeometry.GenericPointProduct.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The generic-point product decomposition on a reduced or a locally Noetherian scheme

The hypotheses of the generic-point decomposition are that the weakly associated points of the
scheme are generic points of irreducible components, and that each quasi-compact open has finitely
many irreducible components. Both hold on a reduced scheme with the second hypothesis assumed, and
both hold on a locally Noetherian scheme without embedded points.

## Main results

In the `Stacks.AlgebraicGeometry.GenericPointProduct` namespace:

* `meromorphicFunctions_iso_product_genericPointStalks` is the decomposition for a reduced
  scheme.
* `meromorphicFunctions_iso_product_of_noEmbeddedPoints` is the decomposition for a locally
  Noetherian scheme without embedded points.

## Implementation notes

On a locally Noetherian scheme a quasi-compact open is a Noetherian scheme, hence a Noetherian
space, which bounds its irreducible components; and the associated and weakly associated points
agree (Stacks 05AR), while the absence of embedded points forces every associated point to be
generic, since the generic point of the irreducible component of any point is itself associated
(Stacks 05AH).

## References

* [Stacks Project, Tag 02OW](https://stacks.math.columbia.edu/tag/02OW)
* [Stacks Project, Tag 0EMF](https://stacks.math.columbia.edu/tag/0EMF)
* [Stacks Project, Tag 0EMH](https://stacks.math.columbia.edu/tag/0EMH)
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.GenericPointProduct

open Stacks.AlgebraicGeometry.GenericPointDecomposition

/-- Every quasi-compact open of `X` has finitely many irreducible components. -/
abbrev FiniteComponentsOnCompactOpens (X : Scheme.{u}) : Prop :=
  ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite

/-- **Stacks Project, Tag 02OW.** On a reduced scheme whose quasi-compact opens have finitely many
irreducible components, the `𝒪_X`-module of meromorphic functions is the product, over the generic
points of the irreducible components, of the structure sheaves of the local schemes there, pushed
forward to `X`. -/
@[stacks 02OW "generic-point product"]
theorem meromorphicFunctions_iso_product_genericPointStalks (X : Scheme.{u}) [IsReduced X]
    (hfinite : FiniteComponentsOnCompactOpens X) :
    Nonempty (meromorphicFunctions X ≅
      ∏ᶜ fun η : genericPoints X ↦ genericPointStalkModule X η) :=
  ⟨meromorphicFunctionsIsoProduct
    (weaklyAssociatedPointsOfScheme_eq_genericPoints X).le hfinite⟩

/-- On a locally Noetherian scheme every quasi-compact open has finitely many irreducible
components: it is then a Noetherian scheme, hence a Noetherian space. -/
@[ega "0 2.2.5" "special case"]
theorem finiteComponentsOnCompactOpens_of_isLocallyNoetherian (X : Scheme.{u})
    [IsLocallyNoetherian X] : FiniteComponentsOnCompactOpens X := by
  intro U hU
  have : CompactSpace (U : Type u) := isCompact_iff_compactSpace.mp hU
  have : IsNoetherian U.toScheme := ⟨⟩
  exact finite_irreducibleComponents_of_isNoetherian

/-- On a locally Noetherian scheme without embedded points the weakly associated points are
generic points of irreducible components. The weakly associated points are the associated points
there (Stacks 05AR); the generic point of the irreducible component of any point is associated
(Stacks 05AH), so an associated point which is not itself generic would be embedded. -/
theorem schemeWeaklyAssociatedPoints_subset_genericPoints (X : Scheme.{u})
    [IsLocallyNoetherian X] (hX : AlgebraicGeometry.HasNoEmbeddedPoints X) :
    Stacks.Divisors.schemeWeaklyAssociatedPoints X ⊆ genericPoints X := by
  intro x hx
  have hassoc : x ∈ Stacks.Divisors.schemeAssociatedPoints X := by
    simpa only [Stacks.Divisors.schemeWeaklyAssociatedPoints,
      ← AlgebraicGeometry.associatedPoints_eq_weaklyAssociatedPoints X
        (SheafOfModules.unit X.ringCatSheaf)] using hx
  let C : irreducibleComponents X :=
    ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
  let η : genericPoints X := genericPoints.ofComponent C
  have hηx : η.1 ⤳ x := specializes_iff_mem_closure.mpr <|
    (genericPoints.isGenericPoint_ofComponent C).symm ▸ mem_irreducibleComponent
  have hη_eq : η.1 = x := by
    by_contra hne
    exact hX x ⟨hassoc, ⟨η.1,
      AlgebraicGeometry.mem_schemeAssociatedPoints_of_isGenericPoint_irreducibleComponent
        X C.property (genericPoints.isGenericPoint_ofComponent C), hηx, hne⟩⟩
  exact hη_eq ▸ η.property

/-- **Stacks Project, Tag 0EMH.** On a locally Noetherian scheme without embedded points, the
`𝒪_X`-module of meromorphic functions is the product, over the generic points of the irreducible
components, of the structure sheaves of the local schemes there, pushed forward to `X`. -/
@[stacks 0EMH "meromorphic functions as a product"]
theorem meromorphicFunctions_iso_product_of_noEmbeddedPoints (X : Scheme.{u})
    [IsLocallyNoetherian X] (hX : AlgebraicGeometry.HasNoEmbeddedPoints X) :
    Nonempty (meromorphicFunctions X ≅
      ∏ᶜ fun η : genericPoints X ↦ genericPointStalkModule X η) :=
  ⟨meromorphicFunctionsIsoProduct (schemeWeaklyAssociatedPoints_subset_genericPoints X hX)
    (finiteComponentsOnCompactOpens_of_isLocallyNoetherian X)⟩

end Stacks.AlgebraicGeometry.GenericPointProduct
