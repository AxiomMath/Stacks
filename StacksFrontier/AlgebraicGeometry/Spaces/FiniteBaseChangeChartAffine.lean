module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallBaseChangeChartFiniteness

/-!
# The chart base change of a finite morphism of algebraic spaces is an affine scheme

Let `f : X ⟶ Y` be a finite morphism of algebraic spaces over a scheme `S` of a big fppf site
`B`, and let `V` be an étale scheme chart of `Y` whose scheme is affine.  Base change of charts
along `f` produces the étale chart `U = V ×_Y X` of `X` with its cartesian projection
`ψ : U ⟶ V`, which is a finite morphism of schemes by
`AlgebraicGeometry.Space.isFinite_baseChangeChartHom`.  A finite morphism is affine, so the
scheme of `U` is affine and `Γ(U, 𝒪_U)` is a finite algebra over `Γ(V, 𝒪_V)`.

This is the ring the proof of **Stacks 0EQ4** for algebraic spaces works with. There `Y` is an
integral good algebraic space, `V` an affine étale chart of it, and `p : X ⟶ Y` a proper
dominant morphism which **Stacks 0AD2** — available as
`AlgebraicGeometry.Space.exists_isOpenSubspace_isFinite_pullback_snd_of_localRingDimension_le_one`
— makes finite after shrinking; `Γ(X ×_Y V, ⊤)` is then the ring `C` of
`StacksFrontier.RingTheory.Localization.GenericFibreComponents`, whose generic fibre over the
branches of `V` carries the components of `X ×_Y V` dominating them.

## Main results

* `AlgebraicGeometry.Space.isAffine_chartScheme_baseChangeChart_of_isFinite`: for `f` finite and
  `V` an étale chart of `Y` with affine scheme, the scheme of the base-changed chart `V ×_Y X`
  is affine.
* `AlgebraicGeometry.Space.finite_appTop_baseChangeChartHom`: the ring homomorphism
  `Γ(V, 𝒪_V) → Γ(V ×_Y X, 𝒪)` the cartesian projection induces is finite — that is, the ring of
  the base-changed chart is a finite module over the ring of the chart.

## Implementation notes

Both statements are read off the single input
`AlgebraicGeometry.Space.isFinite_baseChangeChartHom`, which says that the projection
`ψ : V ×_Y X ⟶ V` is `AlgebraicGeometry.IsFinite` as a morphism of schemes, through Mathlib's
affine-local description of that property: `AlgebraicGeometry.IsFinite` has
`AlgebraicGeometry.HasAffineProperty` with local property `IsAffine X ∧ RingHom.Finite f.appTop`,
so over an affine target the two conclusions are its two halves. Affineness alone is also
`AlgebraicGeometry.isAffine_of_isAffineHom`, since `AlgebraicGeometry.IsFinite` extends
`AlgebraicGeometry.IsAffineHom`.

The hypotheses are the ones `AlgebraicGeometry.Space.isFinite_baseChangeChartHom` needs: `f` is
assumed relatively representable, with the witness `hrep` explicit because the base-changed
chart `AlgebraicGeometry.Space.baseChangeChart` is built from it, and a finite morphism is
relatively representable by
`AlgebraicGeometry.Space.relativelyRepresentable_hom_of_isFinite`.

What this does **not** give is a cartesian square of *schemes* over which
`AlgebraicGeometry.algebraIsPushout_appTop_of_isPullback` could decompose
`Γ(V ×_Y X, ⊤)` as a tensor product: the square
`AlgebraicGeometry.Space.isPullback_baseChangeChartHom` has `f` itself as one of its sides, and
`f` is a morphism of algebraic spaces, not of schemes. That is exactly the point at which the
absence of an affine open in `Y` is felt.

That a finite morphism is affine is Stacks 01WN for schemes, and the passage to charts is
Stacks 03ZQ.

## References

* [Stacks Project, Tag 01WN](https://stacks.math.columbia.edu/tag/01WN)
* [Stacks Project, Tag 03ZQ](https://stacks.math.columbia.edu/tag/03ZQ)
* [Stacks Project, Tag 0EQ4](https://stacks.math.columbia.edu/tag/0EQ4)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

/-- **The chart base change of a finite morphism of algebraic spaces is an affine scheme.** For
`f : X ⟶ Y` finite and `V` an étale scheme chart of `Y` whose scheme is affine, the scheme of the
base-changed chart `V ×_Y X` of `X` is affine.

The projection `V ×_Y X ⟶ V` is a finite morphism of schemes by
`AlgebraicGeometry.Space.isFinite_baseChangeChartHom`, hence affine, and a scheme affine over an
affine scheme is affine. -/
theorem isAffine_chartScheme_baseChangeChart_of_isFinite (f : X ⟶ Y)
    (hrep : yoneda.relativelyRepresentable f.hom) (hf : IsFinite B S hS f.hom)
    (V : SmallEtale B S hS Y.1) [IsAffine (chartScheme V)] :
    IsAffine (chartScheme (baseChangeChart B S hS f hrep V)) :=
  have := isFinite_baseChangeChartHom B S hS f hrep hf V
  isAffine_of_isAffineHom
    ((BigFppfOver.toScheme B S hS).map (baseChangeChartHom B S hS f hrep V))

/-- **The ring of the base-changed chart is a finite module over the ring of the chart.** For
`f : X ⟶ Y` finite and `V` an étale scheme chart of `Y` whose scheme is affine, the homomorphism
`Γ(V, 𝒪_V) → Γ(V ×_Y X, 𝒪)` induced by the cartesian projection is a finite ring homomorphism.

This is the defining clause `AlgebraicGeometry.IsFinite.finite_app` of
`AlgebraicGeometry.IsFinite` at the affine open `⊤` of the chart, applied to the finite
projection of `AlgebraicGeometry.Space.isFinite_baseChangeChartHom`; the affineness of the source
which the same property carries is
`AlgebraicGeometry.Space.isAffine_chartScheme_baseChangeChart_of_isFinite`.

It is the hypothesis `Module.Finite O C` of
`Stacks.GenericFibre.module_finite_of_localization` and
`Stacks.GenericFibre.isArtinianRing_of_localization`, which is what makes the generic fibre of
`V ×_Y X ⟶ V` a finite-dimensional algebra over the function field of a branch of `V`, hence
Artinian, hence a product of the function fields of the components of `V ×_Y X` dominating that
branch. -/
theorem finite_appTop_baseChangeChartHom (f : X ⟶ Y)
    (hrep : yoneda.relativelyRepresentable f.hom) (hf : IsFinite B S hS f.hom)
    (V : SmallEtale B S hS Y.1) [IsAffine (chartScheme V)] :
    RingHom.Finite
      ((BigFppfOver.toScheme B S hS).map (baseChangeChartHom B S hS f hrep V)).appTop.hom :=
  have := isFinite_baseChangeChartHom B S hS f hrep hf V
  _root_.AlgebraicGeometry.IsFinite.finite_app
    ((BigFppfOver.toScheme B S hS).map (baseChangeChartHom B S hS f hrep V)) ⊤
    (isAffineOpen_top (chartScheme V))

end AlgebraicGeometry.Space

end
