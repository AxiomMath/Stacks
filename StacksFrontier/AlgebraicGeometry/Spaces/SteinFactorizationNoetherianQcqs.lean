module

public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.Separated
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationInUniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationCancellation
public import StacksFrontier.AlgebraicGeometry.Spaces.SteinFactorizationQcqs
import StacksCore.Tactic.StacksAttribute

/-!
# Stein factorization of a proper morphism of algebraic spaces, through the qcqs normalization

Let `f : X ⟶ Y` be a proper morphism of algebraic spaces over a scheme `S` with `Y` locally
Noetherian.  Stacks 0A1B factors `f` as `X ⟶ Y' ⟶ Y` with

1. `f'` proper with connected geometric fibres,
2. `π : Y' ⟶ Y` finite,
3. `f'_* 𝒪_X = 𝒪_{Y'}`,
4. `Y' = \underline{Spec}_Y(f_* 𝒪_X)`,
5. `Y'` the normalization of `Y` in `X`.

This file takes for that factorization the normalization of `Y` in `X` constructed, with no
carried hypothesis, by `StacksFrontier.AlgebraicGeometry.Spaces.NormalizationInQcqs`:
`Y' = AlgebraicGeometry.Space.normalizationInQcqs`,
`π = AlgebraicGeometry.Space.normalizationInQcqsHom` and
`f' = AlgebraicGeometry.Space.toNormalizationInQcqs`.
A proper morphism is quasi-compact (it is of finite type) and quasi-separated (it is separated,
Stacks 03KK), which is all that construction asks.  Unlike the factorization through
`AlgebraicGeometry.Space.normalizationIn` used by
`StacksFrontier.AlgebraicGeometry.Spaces.SteinFactorization`, it needs neither the anti-equivalence
of Stacks 081V nor the structures `P`, `D`, `hloc` of Stacks 0823.

## Main results

* `AlgebraicGeometry.Space.isProper_toNormalizationInQcqs`: the properness half of clause (1):
  `f'` is proper, by Stacks 04NX part (2), `π` being affine and hence separated (Stacks 03KM).
* Clause (4) of Stacks 0A1B is
  `Space.isIso_pushforwardAlgebraMap_toNormalizationInQcqsOver_of_universallyClosed`
  of `StacksFrontier.AlgebraicGeometry.Spaces.NormalizationInUniversallyClosed`: `π` is affine (it is
  an object of `AlgebraicGeometry.Space.AffineOver Y`) and the map `π_* 𝒪_{Y'} ⟶ f_* 𝒪_X` induced
  by `f'` is an isomorphism of `𝒪_Y`-algebras, which is what `Y' = \underline{Spec}_Y(f_* 𝒪_X)`
  means; it is proved for every quasi-compact, quasi-separated, universally closed `f`, and a
  proper `f` is all three.  The tag is attached to it below.
* Clause (5) of Stacks 0A1B is
  `AlgebraicGeometry.Space.isRelativeNormalization_normalizationInQcqs` of
  `StacksFrontier.AlgebraicGeometry.Spaces.NormalizationInQcqsUniversalProperty`: the factorization
  has the two properties of Stacks 0823 characterizing the normalization of `Y` in `X` (Stacks
  0822).  It is proved for every quasi-compact quasi-separated `f`.  The tag is attached to it
  below.
* Clause (3) of Stacks 0A1B is `AlgebraicGeometry.Space.isIso_fSharp_toNormalizationInQcqs` of
  `StacksFrontier.AlgebraicGeometry.Spaces.SteinFactorizationQcqs` (Stacks 0A19, clause (3)): the
  structure map `𝒪_{Y'} ⟶ f'_* 𝒪_X` is an isomorphism; it is proved for every universally closed,
  quasi-compact, quasi-separated `f`, which a proper `f` is.  The tag is attached to it below.
* Clause (2) of Stacks 0A1B is
  `AlgebraicGeometry.Space.isFinite_normalizationInQcqsHom_of_isProper` of
  `StacksFrontier.AlgebraicGeometry.Spaces.NormalizationInFiniteOfProper`, where the tag is attached.
* Clause (1) of Stacks 0A1B, properness together with connectedness of the geometric fibres, is
  `AlgebraicGeometry.Space.isProper_and_connectedPullback_toNormalizationInQcqs` of
  `StacksFrontier.AlgebraicGeometry.Spaces.SteinFactorizationNoetherianConnectedFibres`, where the
  tag is attached.

## References

* [Stacks Project, Tag 0A1B](https://stacks.math.columbia.edu/tag/0A1B)
* [Stacks Project, Tag 0A0Q](https://stacks.math.columbia.edu/tag/0A0Q)
* [Stacks Project, Tag 0822](https://stacks.math.columbia.edu/tag/0822)
* [Stacks Project, Tag 0823](https://stacks.math.columbia.edu/tag/0823)
* [Stacks Project, Tag 03KK](https://stacks.math.columbia.edu/tag/03KK)
* [Stacks Project, Tag 03KM](https://stacks.math.columbia.edu/tag/03KM)
* [Stacks Project, Tag 04NX](https://stacks.math.columbia.edu/tag/04NX)
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y : AlgebraicSpaces B S hS}

end AlgebraicGeometry.Space

add_to_stacks 0A1B "part (3): f'_*O_X = O_{Y'} for the factorization X -> Y' -> Y through the \
normalization of Stacks 0822 -- the structure map O_{Y'} -> f'_*O_X is an isomorphism of sheaves \
of rings; proved for every quasi-compact, quasi-separated, universally closed f, which a proper f \
is"
  AlgebraicGeometry.Space.isIso_fSharp_toNormalizationInQcqs

add_to_stacks 0A1B "part (4): Y' = Spec_Y(f_*O_X) for the factorization through the \
normalization of Stacks 0822 -- pi is affine and the map pi_*O_{Y'} -> f_*O_X induced by f' is \
an isomorphism of O_Y-algebras; proved for every quasi-compact, quasi-separated, universally \
closed f, which a proper f is"
  AlgebraicGeometry.Space.isIso_pushforwardAlgebraMap_toNormalizationInQcqsOver_of_universallyClosed

add_to_stacks 0A1B "part (5): the intermediate space Y' of the factorization X -> Y' -> Y is \
the normalization of Y in X, in the characterization of Stacks 0823; proved for every \
quasi-compact quasi-separated f, which a proper f is"
  AlgebraicGeometry.Space.isRelativeNormalization_normalizationInQcqs

end
