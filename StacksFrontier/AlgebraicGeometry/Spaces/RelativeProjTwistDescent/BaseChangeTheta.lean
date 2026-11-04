module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.BaseChangeTheta.ProjMap
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.BaseChangeTheta.PullbackDescended
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.BaseChangeTheta.QuadrupleLiesOver
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.BaseChangeTheta.TwistComparison

/-!
# The twists of a relative Proj under base change, degreewise

In Situation 0849 let `g : X' ⟶ X` be a morphism of algebraic spaces, `P = Proj_X(𝒜)` and
`P' = Proj_{X'}(g^*𝒜)` the two relative Projs of Stacks 084B, and `h : P' ⟶ P` the morphism of
Stacks 085C (`AlgebraicGeometry.Space.RelativeProjSituation.relativeProjBaseChangeHom`), so that
`P' = X' ×_X P`.  This file constructs the chart data of the isomorphism

`θ_n : h^*𝒪_P(n) ≅ 𝒪_{P'}(n)`

of the second assertion of Stacks 085C, in every degree `n`, for the twists `𝒪_P(n)` of Stacks 084D
(`AlgebraicGeometry.Space.RelativeProjSituation.twistModule`), descended from presentations
`X = U/R` and `X' = U'/R'` compatible with `g`.

As in the source, `θ` is computed on the charts: over a scheme point `v` of `X'` and `u` of `X`
with `u ∘ k = g ∘ v`, a morphism of base changes `V ×_{X'} P' ⟶ U ×_X P` lying over `k` and `h` is,
on schemes, the identification `Proj_V(v^*g^*𝒜) ≅ Proj_V((g v)^*𝒜) ≅ Proj_V(k^*u^*𝒜)` of the
restricted algebras followed by the base-change morphism of Tag 01O3; the twists of Tag 01NR are
compared along it by Tag 01O3's `θ`.  These comparisons satisfy the cocycle conditions with the
comparisons of twists of the two descent data, so they descend (Stacks 03M3).

## Main definitions

* `AlgebraicGeometry.Space.GradedAlgebraRestriction.ComapHom.projMap`: for a comparison of
  restriction data along `g`, the morphism `Proj_T(f'^*𝒜') ⟶ Proj_T((g f')^*𝒜)` over `T`.
* `AlgebraicGeometry.Space.RelativeProjPoints.LiesOverAlong`: a morphism of base changes of two
  relative Projs lying over a morphism of test objects and over a morphism `h` of the Projs.
* `AlgebraicGeometry.Space.presentationPullbackDescendedIso`: for a morphism `h : X'' ⟶ X` of
  algebraic spaces and compatible chart data on presentations of `X''` and `X`, the inverse image
  `h^*𝒯` of the descended module is the descended module of the pulled-back chart data (03M3).
* `AlgebraicGeometry.Space.RelativeProjPoints.pullbackAlongDescendedIso`: the same along a
  morphism of relative Projs, for presentations `U ×_X P` and `U' ×_{X'} P'` and a morphism of the
  presenting schemes lying over `ℓ : U' ⟶ U` and `h`.
* `AlgebraicGeometry.Space.RelativeProjSituation.baseChangeTwistPieceComparison`: the
  comparison `y^*𝒪_{U ×_X P}(n) ≅ 𝒪_{V ×_{X'} P'}(n)` along a morphism lying over `k` and `h`.
* `AlgebraicGeometry.Space.RelativeProjSituation.baseChangeTwistChartIso`: the identification
  `c'^*(h^*𝒪_P(n)) ≅ 𝒪(n)` on the atlas of a presentation of `P'`, the chart of `θ_n`.
* `AlgebraicGeometry.Space.RelativeProjSituation.baseChangeTwistModuleIso`: **the isomorphism
  `θ_n : h^*𝒪_P(n) ≅ 𝒪_{P'}(n)`** of Stacks 085C, in every degree `n`.

## Main results

* `AlgebraicGeometry.Space.GradedAlgebraRestriction.ComapHom.toScheme_map_projMap`: on schemes,
  `projMap` is the identification of relative Projs along the comparison.
* `AlgebraicGeometry.Space.RelativeProjSituation.toScheme_map_eq_of_liesOverAlong`: a morphism
  lying over `k` and `h` is, on schemes, the identification of the restricted algebras followed by
  the base-change morphism of Tag 01O3.
* `AlgebraicGeometry.Space.RelativeProjSituation.baseChangeTwistSheafIso_comp_liesOver` and
  `…baseChangeTwistSheafIso_liesOver_comp`: the two cocycle conditions of the comparisons.
* `…RelativeProjSituation.schemePairTransition_twistPieceComparison_baseChange`: the comparison
  of twists carries the pulled-back transition of the twists of `P` to the
  transition of the twists of `P'` (at variable points).
* `…RelativeProjSituation.baseChangeTwistModuleIso_spec`: on the atlas of `P'`, `θ_n` is the
  comparison of twists of Tag 01O3 on the presenting schemes.

## Implementation notes

As in `StacksFrontier/AlgebraicGeometry/Spaces/RelativeProjTwistDescent/Datum.lean`, every statement
about the charts is proved at variable points and only then instantiated at the presentations.
The descent step itself is proved once for arbitrary presentations
(`AlgebraicGeometry.Space.presentationPullbackDescendedIso`, then
`AlgebraicGeometry.Space.RelativeProjPoints.pullbackAlongDescendedIso`) and instantiated once at
the twists of `P` and `P'`.  The compatibility hypothesis of that step is the one-field structure
`AlgebraicGeometry.Space.RelativeProjPoints.PullbackTransitionCompatible`, so that the proof
supplied at the twists has literally the type of the hypothesis; the base changes of `P'` are
typed over the site of `X` in
`RelativeProjSituation.schemePairTransition_baseChangeTwistPieceComparison_of_eq` for the same
reason.  The multiplicativity of `θ = ⨁ θ_n` is not carried out here.

## Parts

* `BaseChangeTheta.ProjMap`: the fibre map `projMap` and morphisms lying over `h`.
* `BaseChangeTheta.PullbackDescended`: the inverse image of a descended module.
* `BaseChangeTheta.QuadrupleLiesOver`: morphisms of base changes along the functor of quadruples.
* `BaseChangeTheta.TwistComparison`: the comparison of twists, its cocycle conditions, and `θ_n`.

## References

* [Stacks Project, Tag 085C](https://stacks.math.columbia.edu/tag/085C)
* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
* [Stacks Project, Tag 03M3](https://stacks.math.columbia.edu/tag/03M3)
-/
