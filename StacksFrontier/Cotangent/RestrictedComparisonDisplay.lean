module

public import StacksFrontier.Cotangent.BaseChangeQuasiIso
public import StacksFrontier.Cotangent.RestrictedResolutionComparison

/-!
# The comparison of resolutions and the second displayed morphism

For a tower `A → B → C` with `B` a polynomial algebra over `A`,
`StacksFrontier/Cotangent/RestrictedResolutionComparison.lean` names the quasi-isomorphism
`L_{C/A} ⟶ Ω[P_•⁄A] ⊗[P_•] C` which identifies the middle term of the short exact sequence
behind [Stacks, Tag 08SA] — `CommAlgCat.restrictedCotangentShortComplex` of
`StacksFrontier/Cotangent/StandardResolutionOverPolynomialBase.lean` — with the cotangent complex.

Naming the arrow is not enough to compare triangles: the identification must *commute with the
sequence's own maps*. This file proves the commutation with the third map, which is the one the
display of [Stacks, Tag 08QS] names. In every simplicial degree the composite

`L_{C/A} ⟶ Ω[P_•⁄A] ⊗[P_•] C ⟶ Ω[P_•⁄B] ⊗[P_•] C = L_{C/B}`

is the functoriality map of [Stacks, Tag 08PN] at the square `(A → B, 𝟙_C)`, which is
`CommAlgCat.displaySquare₂` of the display, written with `CommAlgCat.restrictedBase` as its
source.

## Main results

* `CommAlgCat.restrictedResolutionComparison_toRelative`: **the comparison followed by the third
  map of the sequence is the second displayed morphism**, in every simplicial degree.

## Implementation notes

Both sides are pinned by a formula on the pure differential `1 ⊗ d q`, and the proof is the two
formulas compared: `CommAlgCat.overDifferentialsFunctor_map_mk` carries `1 ⊗ d q` to
`1 ⊗ d (u q)` for `u` the comparison of resolutions, `CommAlgCat.restrictedCotangentToRelative_D`
then reads it as a differential over `B`, and
`CommAlgCat.squareCotangentTermMap_D` gives the same element on the other side.

Three spellings of the pure differential meet here —
`CommAlgCat.overDifferentialsMk`, `CommAlgCat.cotangentTermDifferential` and
`CommAlgCat.restrictedCotangentDifferential` — and all three are `1 ⊗ₜ D p` by definition, so
they are definitionally equal but not syntactically so. **The proof is therefore a term, a chain
of `congrArg` and `Eq.trans`, and contains no `rw` at all.** A `rw` here is rejected: its motive
mixes the spellings and the target is then not type-correct at `implicit` transparency, which is
what `rw` checks motives at. The chain elaborates at default transparency and builds no motive,
so each spelling is crossed exactly once. This is the same discipline the implementation notes of
`StacksFrontier/Cotangent/BaseChangeComplexCounit.lean` and
`StacksFrontier/Cotangent/BaseChangeCompositionCounit.lean` record.

Everything is at an **arbitrary** simplicial degree: evaluating the standard resolution at a
concrete simplex is what makes the unifier diverge here, so nothing below mentions one.

## References

* [Stacks Project, Tag 08PN](https://stacks.math.columbia.edu/tag/08PN)
* [Stacks Project, Tag 08QS](https://stacks.math.columbia.edu/tag/08QS)
* [Stacks Project, Tag 08SA](https://stacks.math.columbia.edu/tag/08SA)
* [Stacks Project, Tag 08SC](https://stacks.math.columbia.edu/tag/08SC)
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicTopology

universe u

namespace CommAlgCat

variable (A : Type u) [CommRing A] (B : Type u) [CommRing B] [Algebra A B]
  (C : Type u) [CommRing C] [Algebra B C]

/-- **The comparison, followed by the third map of the [Stacks, Tag 08SA] sequence, is the second
displayed morphism of [Stacks, Tag 08QS].** In simplicial degree `n` both sides send the pure
differential `1 ⊗ d q` of `L_{C/A}` to `1 ⊗ d (u q)` in `L_{C/B}`, for `u` the comparison of
resolutions `P_•(C/A) ⟶ P_•(C/B)`.

This is the compatibility which makes the triangle of the sequence the triangle *of the display*:
the identification of the middle term with `L_{C/A}`
(`CommAlgCat.restrictedResolutionComparisonOver`) commutes with the sequence's own map to
`L_{C/B}`, which is `CommAlgCat.squareCotangentTermMap` at `CommAlgCat.restrictedTowerSquare`. -/
theorem restrictedResolutionComparison_toRelative (n : SimplexCategoryᵒᵖ) :
    overDifferentialsFunctor.map ((restrictedResolutionComparisonOver A B C).app n) ≫
        restrictedCotangentToRelative.{u, u} A B C n =
      squareCotangentTermMap.{u, u, u} (restrictedTowerSquare A B C) n :=
  cotangentTerm_hom_ext.{u, u} A (restrictedBase A B C) n _ _ fun q =>
    (congrArg (fun z => restrictedCotangentToRelative.{u, u} A B C n z)
        (overDifferentialsFunctor_map_mk
          ((restrictedResolutionComparisonOver A B C).app n) q)).trans
      ((restrictedCotangentToRelative_D.{u, u} A B C n
          (standardResolutionSquareMap.{u, u, u} (restrictedTowerSquare A B C) n q)).trans
        (squareCotangentTermMap_D.{u, u, u} (restrictedTowerSquare A B C) n q).symm)

end CommAlgCat

end
