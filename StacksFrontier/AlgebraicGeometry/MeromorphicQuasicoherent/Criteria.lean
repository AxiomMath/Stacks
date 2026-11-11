module

public import StacksFrontier.AlgebraicGeometry.MeromorphicQuasicoherent.Product

/-!
# Quasi-coherence of the sheaf of meromorphic functions

On a scheme whose weakly associated points are generic points of irreducible components and whose
quasi-compact opens have finitely many irreducible components, the sheaf of meromorphic functions
is quasi-coherent as an `𝒪_X`-module. This is part (1) of Stacks Tag 0EMF. Its two specialisations,
to a reduced scheme and to a locally Noetherian scheme without embedded points, are part (1) of
Stacks Tag 02OW and the corresponding assertion of Tag 0EMH.

## Main results

* In the namespace `Stacks.AlgebraicGeometry.MeromorphicQuasicoherent`,
  `meromorphicFunctions_isQuasicoherent_of_genericHypotheses` is the statement under the
  hypotheses of Tag 0EMF.
* `Stacks.AlgebraicGeometry.MeromorphicQuasicoherent.meromorphicFunctions_isQuasicoherent` is the
  statement for a reduced scheme.
* In the same namespace, `meromorphicFunctions_isQuasicoherent_of_noEmbeddedPoints` is the
  statement for a locally Noetherian scheme without embedded points.

## Implementation notes

Both are the generic-point decomposition together with quasi-coherence of the generic-point
product. The decomposition needs both hypotheses of Tag 0EMF — that the weakly associated points
are generic points, and local finiteness of the irreducible components — and quasi-coherence of the
product needs only the second, so the two hypothesis derivations are exactly the ones the product
decomposition already uses:
`AlgebraicGeometry.weaklyAssociatedPointsOfScheme_eq_genericPoints` in the reduced case and
`Stacks.AlgebraicGeometry.GenericPointProduct.schemeWeaklyAssociatedPoints_subset_genericPoints`
in the locally Noetherian case.

## References

* [Stacks Project, Tag 0EMF](https://stacks.math.columbia.edu/tag/0EMF)
* [Stacks Project, Tag 02OW](https://stacks.math.columbia.edu/tag/02OW)
* [Stacks Project, Tag 0EMH](https://stacks.math.columbia.edu/tag/0EMH)
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.MeromorphicQuasicoherent

open Stacks.AlgebraicGeometry.GenericPointDecomposition
open Stacks.AlgebraicGeometry.GenericPointProduct

/-- **Part (1) of [Stacks, Tag 0EMF].** On a scheme whose weakly associated points are generic
points of irreducible components and whose quasi-compact opens have finitely many irreducible
components, the sheaf of meromorphic functions is quasi-coherent: it is then the product of the
generic-point contributions, and that product is quasi-coherent. -/
@[stacks 0EMF "part (1)"]
theorem meromorphicFunctions_isQuasicoherent_of_genericHypotheses {X : Scheme.{u}}
    (hass : Stacks.Divisors.schemeWeaklyAssociatedPoints X ⊆ genericPoints X)
    (hfin : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents (U : Set X)).Finite) :
    (meromorphicFunctions X).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (meromorphicFunctionsIsoProduct hass hfin).symm
    (isQuasicoherent_piGenericPointStalkModule X hfin)

/-- **Stacks Project, Tag 02OW, part (1).** On a reduced scheme whose quasi-compact opens have
finitely many irreducible components, the sheaf of meromorphic functions is quasi-coherent. -/
@[stacks 02OW "part (1)"]
theorem meromorphicFunctions_isQuasicoherent (X : Scheme.{u}) [IsReduced X]
    (hfinite : FiniteComponentsOnCompactOpens X) :
    (meromorphicFunctions X).IsQuasicoherent :=
  meromorphicFunctions_isQuasicoherent_of_genericHypotheses
    (weaklyAssociatedPointsOfScheme_eq_genericPoints X).le hfinite

/-- **Stacks Project, Tag 0EMH.** On a locally Noetherian scheme without embedded points, the
sheaf of meromorphic functions is quasi-coherent.
One clause of [Stacks, Tag 0EMH]; the complete statement is
`AlgebraicGeometry.genericPointDecomposition_of_hasNoEmbeddedPoints`. -/
theorem meromorphicFunctions_isQuasicoherent_of_noEmbeddedPoints (X : Scheme.{u})
    [IsLocallyNoetherian X] (hX : AlgebraicGeometry.HasNoEmbeddedPoints X) :
    (meromorphicFunctions X).IsQuasicoherent :=
  meromorphicFunctions_isQuasicoherent_of_genericHypotheses
    (schemeWeaklyAssociatedPoints_subset_genericPoints X hX)
    (finiteComponentsOnCompactOpens_of_isLocallyNoetherian X)

end Stacks.AlgebraicGeometry.MeromorphicQuasicoherent
