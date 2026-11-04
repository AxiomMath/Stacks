module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDirectImageAlgebraQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeAlgebra

/-!
# The chart restriction of the direct-image algebra of an algebraic space

Let `X` be an algebraic space and `Y` an algebraic space over `X`.  Stacks 03G8 makes the direct
image `f_* 𝒪_Y` of the structure sheaf a sheaf of commutative `𝒪_X`-algebras on the small étale
site of `X`, which is `AlgebraicGeometry.Space.pushforwardAlgebra`, and
`AlgebraicGeometry.Space.chartSchemeAlgebra` restricts that to the Zariski site of the scheme of
an étale chart `V`.  This file records what the restriction and the restricted morphisms are on
sections, and assembles the composite of the direct-image functor of Stacks 081V with the chart
restriction.

The sections statements are the ones whose absence blocked reading the direct-image algebra on a
chart: `AlgebraicGeometry.Space.pushforwardRingMap` had no computation on sections over a chart
anywhere in this development.  They need no proof beyond the two definitional computations of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartSchemeAlgebra.lean` — the chart restriction
sheafifies nothing, so a section of the restricted algebra over a Zariski open `O` of
`chartScheme V` is a section of `f_* 𝒪_Y` over the étale chart `O` cuts out, and the restricted
morphism's component there is `AlgebraicGeometry.Space.pushforwardRingMap`'s own component at
that chart.

## Main definitions

* `AlgebraicGeometry.Space.chartSchemeDirectImageAlgebra`: the direct-image algebra `f_* 𝒪_Y`,
  restricted to the Zariski site of an étale chart's scheme.
* `AlgebraicGeometry.Space.chartSchemeAffineDirectImageAlgebraFunctor`: **the direct-image
  functor of Stacks 081V followed by the chart restriction**, from the opposite of the algebraic
  spaces affine over `X` to the quasi-coherent algebras on the chart's scheme.

## Main results

* `AlgebraicGeometry.Space.chartSchemeDirectImageAlgebra_sections`: its sections over a Zariski
  open of the chart's scheme are the sections of `f_* 𝒪_Y` over the étale chart that open cuts
  out.
* `AlgebraicGeometry.Space.chartSchemeDirectImageAlgebraMap_app`: **the chart restriction of the
  direct-image map on sections is `AlgebraicGeometry.Space.pushforwardRingMap` at that chart**,
  which is also the action on morphisms of the composite functor below.
* `AlgebraicGeometry.Space.isQuasicoherent_chartSchemeDirectImageAlgebra`: the restriction of the
  direct-image algebra of a morphism affine over `X` is quasi-coherent on the chart's scheme.

## Implementation notes

No `stacks` attribute is carried.  Stacks 081V is the statement that the direct-image functor is
an anti-equivalence, and nothing here is about that functor being full, faithful or essentially
surjective; Stacks 04CF is `f'_*(A|_U) = (f_* A)|_V` for the *slice* of the small étale site at a
chart, which is
`AlgebraicGeometry.Space.commRingDirectImage_comp_overPullbackIso`, and the restriction taken
here lands on the Zariski site instead.  What this file states is the chart restriction of one
algebra and of one map, and the composite functor that restriction defines.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 04CF](https://stacks.math.columbia.edu/tag/04CF)
* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-- **The direct-image algebra `f_* 𝒪_Y` of an algebraic space `Y` over `X`, restricted to the
Zariski site of the scheme of an étale chart `V` of `X`.** -/
abbrev chartSchemeDirectImageAlgebra (Y : Over X) (V : SmallEtale B S hS X.1) :
    Stacks.RelativeSpec.AlgebraSheaf (chartScheme V) :=
  chartSchemeAlgebra B S hS X (pushforwardAlgebra B S hS Y) V

/-- **The sections of the chart restriction of `f_* 𝒪_Y` over a Zariski open of the chart's
scheme are the sections of `f_* 𝒪_Y` over the étale chart that open cuts out.** -/
theorem chartSchemeDirectImageAlgebra_sections (Y : Over X) (V : SmallEtale B S hS X.1)
    (O : (chartScheme V).Opens) :
    (chartSchemeDirectImageAlgebra B S hS X Y V).sections O =
      (pushforwardAlgebra B S hS Y).right.obj.obj (op (openChart B S hS X.1 V O)) :=
  rfl

/-- The structure morphism of the chart restriction of `f_* 𝒪_Y`, on sections over a Zariski open:
restrict a regular function on that open to the étale chart it cuts out, then apply the structure
map `f^♯` of Stacks 03G8 there. -/
theorem chartSchemeDirectImageAlgebra_hom_app (Y : Over X) (V : SmallEtale B S hS X.1)
    (O : (chartScheme V).Opens) :
    (chartSchemeDirectImageAlgebra B S hS X Y V).hom.hom.app (op O) =
      (Scheme.restrictFunctorΓ (X := chartScheme V)).inv.app (op O) ≫
        (pushforwardAlgebra B S hS Y).hom.hom.app (op (openChart B S hS X.1 V O)) :=
  rfl

/-- **The chart restriction of the direct-image map, on sections over a Zariski open, is
`AlgebraicGeometry.Space.pushforwardRingMap` at the étale chart that open cuts out.**

This is the computation of `AlgebraicGeometry.Space.pushforwardRingMap` on sections at a chart,
read on the Zariski site of the chart's scheme: the scheme-level map one gets by restricting the
direct-image map of Stacks 081V to a chart has the space-level map's own components. -/
theorem chartSchemeDirectImageAlgebraMap_app {Y Z : Over X} (f : Y ⟶ Z)
    (V : SmallEtale B S hS X.1) (O : (chartScheme V).Opens) :
    ((chartSchemeAlgebraFunctor B S hS X V).map
        (pushforwardAlgebraMap B S hS f)).right.hom.app (op O) =
      (pushforwardRingMap B S hS f).hom.app (op (openChart B S hS X.1 V O)) :=
  rfl

/-- The chart restriction of the direct-image algebra of a morphism *affine* over `X` is
quasi-coherent on the Zariski site of the chart's scheme.

The direct-image algebra of an affine morphism is quasi-coherent on the small étale site by
`AlgebraicGeometry.Space.isQuasicoherent_pushforwardAlgebra_of_isAffineHom`, and the chart
restriction of a quasi-coherent algebra is quasi-coherent. -/
theorem isQuasicoherent_chartSchemeDirectImageAlgebra (Y : AffineOver B S hS X)
    (V : SmallEtale B S hS X.1) :
    (chartSchemeDirectImageAlgebra B S hS X Y.obj V).IsQuasicoherent :=
  isQuasicoherent_chartSchemeAlgebra B S hS X (pushforwardAlgebra B S hS Y.obj)
    (isQuasicoherent_pushforwardAlgebra_of_isAffineHom B S hS Y.obj Y.property) V

/-- **The direct-image functor of Stacks 081V followed by the chart restriction**: the
contravariant functor from the algebraic spaces affine over `X` to the quasi-coherent sheaves of
commutative algebras on the scheme of an étale chart of `X`, sending `f : Y ⟶ X` to the chart
restriction of `f_* 𝒪_Y`.

This is the functor the scheme-level anti-equivalence of Stacks 01SA applies to: its target is a
category of quasi-coherent algebras on a scheme. -/
def chartSchemeAffineDirectImageAlgebraFunctor (V : SmallEtale B S hS X.1) :
    (AffineOver B S hS X)ᵒᵖ ⥤
      Stacks.AffineAlgebraEquivalence.QuasicoherentAlgebra (chartScheme V) :=
  affinePushforwardQuasicoherentAlgebraFunctor B S hS X ⋙
    chartSchemeQuasicoherentAlgebraFunctor B S hS X V

/-- The composite functor restricts the direct-image algebras. -/
@[simp]
theorem chartSchemeAffineDirectImageAlgebraFunctor_obj (V : SmallEtale B S hS X.1)
    (Y : (AffineOver B S hS X)ᵒᵖ) :
    ((chartSchemeAffineDirectImageAlgebraFunctor B S hS X V).obj Y).obj =
      chartSchemeDirectImageAlgebra B S hS X Y.unop.obj V :=
  rfl

end AlgebraicGeometry.Space

end
