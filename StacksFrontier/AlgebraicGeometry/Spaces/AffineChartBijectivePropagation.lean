module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSectionsComparison

/-!
# Bijectivity on affine-chart sections propagates downwards for cartesian modules

Let `F` be an algebraic space and let `j : P ⟶ Q` be a morphism of `𝒪_F`-modules on its small
étale site, both of them cartesian on affine charts.  If `j` is bijective on the sections over an
affine chart `U` then it is bijective on the sections over every affine chart lying over `U`.

The sections over a chart `W` above `U` are the base change `𝒪_F(W) ⊗_{𝒪_F(U)} P(U)` of the
sections over `U`, and the base change comparison `AlgebraicGeometry.Space.sectionsBaseChange` is
natural in the module; so the map on the sections over `W` is, up to the two comparisons, the
base change of the map on the sections over `U`, and the base change of a bijection of modules is
a bijection.

This is the step that turns a statement proved at the finitely many Noetherian affine charts of a
covering family into a statement at every affine chart, which is what a chart-local construction
has to supply before the joint conservativity of the restrictions to the slices
(`Stacks.SheafOfModules.isIso_of_isIso_overFunctor_map`) can be applied.

## Main results

* `AlgebraicGeometry.Space.bijective_val_app_of_bijective_of_cartesian` — **a morphism of
  `𝒪_F`-modules cartesian on affine charts which is bijective on the sections over an affine
  chart is bijective on the sections over every affine chart above it.**

## Implementation notes

The hypothesis `AlgebraicGeometry.Space.IsCartesianOnAffineCharts` is the base change criterion
of Stacks 03DX(2); for a quasi-coherent module it is automatic, by
`AlgebraicGeometry.Space.isCartesianOnAffineCharts_of_isQuasicoherentOnSite`.  No flatness of the
restriction map is used, unlike for the kernel clause of
`StacksFrontier.AlgebraicGeometry.Spaces.ChartSectionsKernel`: the argument only transports a
bijection across two bijections, by
`AlgebraicGeometry.Space.bijective_lTensor_of_bijective`.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u m

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- **A morphism of `𝒪_F`-modules cartesian on affine charts which is bijective on the sections
over an affine chart is bijective on the sections over every affine chart above it.**

The base change comparisons over the chart morphism are bijective for the source and for the
target, being the criterion of Stacks 03DX(2), and they conjugate the map on the sections over
the smaller chart into the base change of the map on the sections over the larger one
(`AlgebraicGeometry.Space.app_sectionsBaseChange`), which is bijective because the base change of
a bijection is one. -/
theorem bijective_val_app_of_bijective_of_cartesian {P Q : Modules.{u, m} B S hS F hF}
    (j : P ⟶ Q) (hP : IsCartesianOnAffineCharts P) (hQ : IsCartesianOnAffineCharts Q)
    {U W : SmallEtale B S hS F} (hU : IsAffine (chartScheme U)) (hW : IsAffine (chartScheme W))
    (f : W ⟶ U) (h : Function.Bijective (j.val.app (op U))) :
    Function.Bijective (j.val.app (op W)) := by
  let _ := chartAlgebra (hF := hF) f
  refine (Function.Bijective.of_comp_iff _ (hP U W hU hW f)).mp ?_
  convert (hQ U W hU hW f).comp
    (bijective_lTensor_of_bijective (chartRing B S hS F hF W) _ h) using 1
  exact funext (app_sectionsBaseChange j f)

end AlgebraicGeometry.Space

end
