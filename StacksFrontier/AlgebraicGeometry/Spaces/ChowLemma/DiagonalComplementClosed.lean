module

public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.DiagonalComplement
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionProper
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceGeneralizations

/-!
# The complement of the diagonals is a closed subspace

For an object `U` of the spaces-étale site of `X` and `n : ℕ`, the inclusion of the complement
of the diagonals `AlgebraicGeometry.Space.SpacesEtale.diagonalComplement` into the `n`-fold
self-product `U ×_X ⋯ ×_X U` is both an open and a closed immersion of algebraic spaces over `S`.

## Main results

* `AlgebraicGeometry.Space.SpacesEtale.isOpenImmersion_diagonalComplementι`: the inclusion of
  the complement of the diagonals is an open immersion of algebraic spaces over `S`.
* `AlgebraicGeometry.Space.SpacesEtale.isClosedImmersion_diagonalComplementι`: it is a closed
  immersion of algebraic spaces over `S`.
* `AlgebraicGeometry.Space.SpacesEtale.isQuasiCompactSpace_diagonalComplement`: if the
  `n`-fold self-product is quasi-compact then so is the complement of the diagonals.

## References

* [Stacks Project, Tag 04CD](https://stacks.math.columbia.edu/tag/04CD)
* [Stacks Project, Tag 0726](https://stacks.math.columbia.edu/tag/0726)
* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

namespace SpacesEtale

/-- The inclusion of the complement of the diagonals into the `n`-fold self-product is an open
immersion. -/
theorem isOpenImmersion_diagonalComplementι (U : SpacesEtale B S hS X) (n : ℕ)
    (hsep : IsSeparated B S hS U.1.hom.hom) :
    IsOpenImmersion B S hS
      ((toSpaces B S hS X).map (diagonalComplementι B S hS X U n hsep)).hom :=
  (diagonalComplementSubspace B S hS X U n hsep).2.2

/-- The inclusion of the complement of the diagonals into the `n`-fold self-product is a closed
immersion. -/
theorem isClosedImmersion_diagonalComplementι (U : SpacesEtale B S hS X) (n : ℕ)
    (hsep : IsSeparated B S hS U.1.hom.hom) :
    IsClosedImmersion B S hS
      ((toSpaces B S hS X).map (diagonalComplementι B S hS X U n hsep)).hom :=
  isClosedImmersion_of_isClosed_range_pointsMap B S hS _
    (isImmersion_of_isOpenImmersion B S hS
      (isOpenImmersion_diagonalComplementι B S hS X U n hsep))
    (range_pointsMap_diagonalComplementι B S hS X U n hsep ▸
      isClosed_diagonalComplementPoints B S hS X U n)

/-- If the `n`-fold self-product is quasi-compact, then so is the complement of the diagonals. -/
theorem isQuasiCompactSpace_diagonalComplement (U : SpacesEtale B S hS X) (n : ℕ)
    (hsep : IsSeparated B S hS U.1.hom.hom)
    (hqc : IsQuasiCompactSpace B S hS (underlying B S hS X (selfProd B S hS X U n)).1) :
    IsQuasiCompactSpace B S hS
      (underlying B S hS X (diagonalComplement B S hS X U n hsep)).1 :=
  isQuasiCompactSpace_of_isClosedImmersion B S hS hqc _
    (isClosedImmersion_diagonalComplementι B S hS X U n hsep)

end SpacesEtale

end AlgebraicGeometry.Space

end
