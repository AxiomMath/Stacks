module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RelativeNormalizationNagataFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationInQcqsUniversalProperty

/-!
# The normalization of a Nagata algebraic space in a reduced one is finite

Let `f : Y ⟶ X` be a quasi-separated morphism of finite type of algebraic spaces over `S`, with
`X` Nagata and `Y` reduced. Tag 0BB0 says that the normalization `ν : X' ⟶ X` of `X` in `Y` is
finite. This file states it for the normalization of Stacks 0822,
`AlgebraicGeometry.Space.normalizationInQcqsHom`, which is defined for `f` quasi-compact and
quasi-separated; quasi-compactness is part of being of finite type.

## Main results

* `AlgebraicGeometry.Space.isFinite_normalizationInQcqsHom_of_isNagata` is **Tag 0BB0** for
  the normalization of Stacks 0822.

## Implementation notes

The proof is `AlgebraicGeometry.Space.IsRelativeNormalization.isFinite_of_isNagata_of_isReduced`
of `StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RelativeNormalizationNagataFinite`, which
proves Tag 0BB0 for every factorization with the two properties of Tag 0823, applied to
`AlgebraicGeometry.Space.isRelativeNormalization_normalizationInQcqs`, which says that the
normalization of Stacks 0822 has them.

## References

* [Stacks Project, Tag 0BB0](https://stacks.math.columbia.edu/tag/0BB0)
* [Stacks Project, Tag 0822](https://stacks.math.columbia.edu/tag/0822)
* [Stacks Project, Tag 0823](https://stacks.math.columbia.edu/tag/0823)
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Stacks 0BB0.** Let `f : Y ⟶ X` be a morphism of algebraic spaces over `S` such that `X`
is Nagata, `f` is quasi-separated of finite type, and `Y` is reduced. Then the normalization
`ν : X' ⟶ X` of `X` in `Y` (Stacks 0822) is finite.

Being Nagata and being reduced are the étale-local properties of schemes of Tag 03E6; the
quasi-compactness that the normalization of Stacks 0822 requires of `f` is the second half of
`f` being of finite type. -/
@[stacks 0BB0]
theorem isFinite_normalizationInQcqsHom_of_isNagata {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (hXnagata : HasEtaleLocalProperty B S hS X.1 fun Z : Scheme.{u} => IsNagataScheme Z)
    (hYred : HasEtaleLocalProperty B S hS Y.1 fun Z : Scheme.{u} => IsReduced Z)
    (hft : IsFiniteType B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom) :
    IsFinite B S hS (normalizationInQcqsHom B S hS f hft.2 hfqs).hom :=
  (isRelativeNormalization_normalizationInQcqs f hft.2 hfqs).isFinite_of_isNagata_of_isReduced
    X.2 Y.2 (normalizationInQcqs B S hS f hft.2 hfqs).2 hXnagata hYred hft hfqs

end AlgebraicGeometry.Space

end
