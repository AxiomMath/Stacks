module

public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModulePullbackPermanence

/-!
# Relative flatness of a quasi-coherent module along a flat pullback (Stacks 05VY)

Let `S` be a scheme contained in a big fppf site `B`, let `f : X ⟶ Y` and `g : Y ⟶ Z` be
morphisms of algebraic spaces over `S`, let `G` be a quasi-coherent `𝒪_Y`-module and let `x` be
a point of `|X|`, with image `y` in `|Y|`.  **Stacks 05VY** asserts two things under those
hypotheses:

* if `f` is flat at `x`, then `G` is flat over `Z` at `y` if and only if `f^*G` is flat over
  `Z` at `x`;
* in particular, if `f` is surjective and flat, then `G` is flat over `Z` if and only if
  `f^*G` is flat over `Z`.

This file states both as a single result,
`AlgebraicGeometry.Space.relativeFlatnessPermanence_modulePullback`.  Each assertion carries a
hypothesis of its own — flatness of `f` at `x` for the first, surjectivity and flatness of `f`
for the second — so inside the one statement the two appear as implications with those
hypotheses as their antecedents, which is the form the source gives them in.  Nothing is left
to a caller: no existential escape, no clause handed out as a hypothesis, no `Prop` binder
standing in for content.

## Main results

* `AlgebraicGeometry.Space.relativeFlatnessPermanence_modulePullback`: the whole of
  **Stacks 05VY**, both of its assertions, for a composable pair of morphisms of algebraic
  spaces over `S` and a quasi-coherent module on the middle one.

## Implementation notes

The two assertions are the library's existing component results, and the statement below is
their conjunction:

* `AlgebraicGeometry.Space.isFlatOverAtPoint_modulePullback_iff_of_isFlatAt` is the pointwise
  equivalence, read through `AlgebraicGeometry.Space.IsFlatOverAtPoint`, the some-chart
  condition (1) of Stacks 05VU at a point of the point space;
* `AlgebraicGeometry.Space.isFlatOver_modulePullback_iff_of_isSurjective_of_isFlat` is the
  source's "in particular", read through `AlgebraicGeometry.Space.IsFlatOver`, which is
  Stacks 05VV.

Both live in `StacksFrontier.AlgebraicGeometry.Spaces.FlatModulePullbackPermanence`, where the
source's own proof is carried out: a geometric point above `x` turns each side into the
geometric-stalk condition (2) of Stacks 05VU, the stalk of `f^*G` there is
`𝒪_{X, x̄} ⊗_{𝒪_{Y, ȳ}} G_ȳ` by Stacks 05VQ, flatness of `f` at `x` makes
`𝒪_{Y, ȳ} ⟶ 𝒪_{X, x̄}` faithfully flat by Stacks 04NG and Stacks 03MK, and the equivalence is
then Stacks 0584 (2).

The point `y` of the source is `pointsMap B S hS X.1 f.hom x`, the image of `x` under the map
of point spaces, so it is not a separate binder.  Quasi-coherence of `G` is the source's
hypothesis; quasi-coherence of `f^*G`, which reading either side at a point of the point space
also needs, is not an extra one, being Stacks 03GA.  The module universe is the universe `u`
of the structure rings, as it must be for `AlgebraicGeometry.Space.IsFlatOver`.

## References

* [Stacks Project, Tag 05VY](https://stacks.math.columbia.edu/tag/05VY)
* [Stacks Project, Tag 05VV](https://stacks.math.columbia.edu/tag/05VV)
* [Stacks Project, Tag 05VU](https://stacks.math.columbia.edu/tag/05VU)
* [Stacks Project, Tag 05VQ](https://stacks.math.columbia.edu/tag/05VQ)
* [Stacks Project, Tag 04NG](https://stacks.math.columbia.edu/tag/04NG)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
* [Stacks Project, Tag 0584](https://stacks.math.columbia.edu/tag/0584)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Space

universe u

/-- **Stacks 05VY.**  Let `S` be a scheme contained in the big fppf site `B`, let
`f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of algebraic spaces over `S`, let `G` be a
quasi-coherent `𝒪_Y`-module and let `x` be a point of `|X|`, with image `y` in `|Y|`.  Then:

1. if `f` is flat at `x`, then `G` is flat over `Z` at `y` if and only if `f^*G` is flat over
   `Z` at `x`;
2. in particular, if `f` is surjective and flat, then `G` is flat over `Z` if and only if
   `f^*G` is flat over `Z`.

A geometric point above `x` turns each side of (1) into the geometric-stalk condition (2) of
Stacks 05VU; there the stalk of `f^*G` is `𝒪_{X, x̄} ⊗_{𝒪_{Y, ȳ}} G_ȳ` by Stacks 05VQ and
`𝒪_{Y, ȳ} ⟶ 𝒪_{X, x̄}` is faithfully flat, so the equivalence is Stacks 0584 (2).  For (2) the
morphism `f` is flat at every point, and surjectivity of `|X| → |Y|` puts a point of `|X|`
above every point of `|Y|`. -/
@[stacks 05VY]
theorem relativeFlatnessPermanence_modulePullback (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (G : Modules.{u, u} B S hS Y.1 Y.2) [G.IsQuasicoherentOnSite] (x : points B S hS X.1) :
    (IsFlatAt B S hS f.hom x →
        (IsFlatOverAtPoint B S hS Y.2 g.hom G (pointsMap B S hS X.1 f.hom x) ↔
          IsFlatOverAtPoint B S hS X.2 (f ≫ g).hom ((modulePullback B S hS f).obj G) x)) ∧
      (IsSurjective B S hS f.hom → IsFlat B S hS f.hom →
        (IsFlatOver B S hS Y.2 g.hom G ↔
          IsFlatOver B S hS X.2 (f ≫ g).hom ((modulePullback B S hS f).obj G))) :=
  ⟨fun hf => isFlatOverAtPoint_modulePullback_iff_of_isFlatAt B S hS f g G x hf,
    fun hsurj hflat =>
      isFlatOver_modulePullback_iff_of_isSurjective_of_isFlat B S hS f g G hsurj hflat⟩

end AlgebraicGeometry.Space

end
