module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartStalkTensorIsomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSiteFlatStalk

/-!
# Flatness of a module over its own algebraic space from one chart stalk

Let `X` be an algebraic space over a scheme `S` of a big fppf site and let `F` be a
quasi-coherent `𝒪_X`-module.  Flatness of `F` over `X` itself — `IsFlatOver` of Stacks 05VV
along the identity — is by the stalk criterion a condition on the geometric stalks `F_{x̄}`,
and Stacks 05VP presents each of those as a base change of the ordinary (Zariski) stalk of the
restriction of `F` to *one* étale scheme chart around `x̄`.  Since flatness is stable under
base change, a single chart with a flat Zariski stalk at the point under `x̄` makes the
geometric stalk flat, and a choice of one such chart at every geometric point makes `F` flat
over `X`.

## Main results

* `AlgebraicGeometry.Space.flat_geometricModuleStalk_of_flat_chartZariskiModuleStalk`: the
  geometric stalk is flat as soon as the Zariski stalk of the chart restriction is flat, on
  some one small étale neighbourhood of the geometric point.
* `AlgebraicGeometry.Space.isFlatOver_id_of_forall_exists_flat_chartZariskiModuleStalk`: a
  quasi-coherent `𝒪_X`-module with a flat chart stalk at every geometric point is flat
  over `X`.

## Implementation notes

The content is the base change of Stacks 05VP, `AlgebraicGeometry.Space.chartZariskiModuleStalk`
tensored up along `AlgebraicGeometry.Space.chartLocalRingToEtaleLocalRing`, together with the
fact that the comparison map is an isomorphism for a quasi-coherent module
(`AlgebraicGeometry.Space.isIso_chartStalkTensorComparison`).  `Module.Flat.baseChange` makes
the tensor product flat over the étale local ring and `Module.Flat.of_linearEquiv` carries that
across the comparison; the algebra structure along which the base change is taken is the one
`CategoryTheory.ModuleCat.extendScalars` installs, so it is introduced by `letI` with the same
term rather than left to instance search.

No faithfully flat *descent* is used and none is available: what is needed here is the
ascent, which is the base change.  The hypothesis is existential in the neighbourhood, as the
source's is — flatness of the Zariski stalk on one chart around the point is what Stacks 05VU
reads as condition (1).

Nothing here carries a `stacks` tag.  Stacks 05VP is tagged at the comparison map and at the
statement that it is an isomorphism, Stacks 05VV at
`AlgebraicGeometry.Space.IsFlatOver`, and the geometric-stalk form of 05VV at the criterion
`AlgebraicGeometry.Space.isFlatOver_iff_forall_isFlatOverAtGeometricPoint`; what is below is
the combination of those, which asserts no further clause of any of them.

## References

* [Stacks Project, Tag 05VV](https://stacks.math.columbia.edu/tag/05VV)
* [Stacks Project, Tag 05VP](https://stacks.math.columbia.edu/tag/05VP)
* [Stacks Project, Tag 05VQ](https://stacks.math.columbia.edu/tag/05VQ)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The geometric stalk is flat as soon as one chart stalk is.**  Let `F` be a quasi-coherent
`𝒪_X`-module and let `V` be a small étale neighbourhood of a geometric point `x̄`.  If the
Zariski stalk `(a^* F)_u` of the restriction of `F` to the chart of `V` is a flat module over
the local ring `𝒪_{U, u}` of that chart, then the geometric stalk `F_{x̄}` is a flat module over
the étale local ring `𝒪_{X, x̄}`.

By Stacks 05VP the geometric stalk is the base change of the Zariski stalk along
`𝒪_{U, u} → 𝒪_{X, x̄}`, and a base change of a flat module is flat. -/
theorem flat_geometricModuleStalk_of_flat_chartZariskiModuleStalk
    {X : AlgebraicSpaces B S hS} {xbar : GeometricPoint B S hS X.1}
    (V : SmallEtaleNeighborhood xbar) (F : Modules.{u, u} B S hS X.1 X.2)
    [F.IsQuasicoherentOnSite]
    (hflat : Module.Flat ↥(chartLocalRing B S hS X.1 V)
      ↥(chartZariskiModuleStalk B S hS X.1 X.2 V F)) :
    Module.Flat ↥(etaleLocalRing B S hS X.1 xbar)
      ↥(geometricModuleStalk B S hS X xbar F) := by
  have := hflat
  have htensor : Module.Flat ↥(etaleLocalRing B S hS X.1 xbar)
      ↥(chartStalkTensorEtaleLocalRing B S hS X.1 X.2 V F) := by
    let : Algebra ↥(chartLocalRing B S hS X.1 V) ↥(etaleLocalRing B S hS X.1 xbar) :=
      (chartLocalRingToEtaleLocalRing B S hS X.1 X.2 V).toAlgebra
    exact Module.Flat.baseChange ↥(chartLocalRing B S hS X.1 V)
      ↥(etaleLocalRing B S hS X.1 xbar) ↥(chartZariskiModuleStalk B S hS X.1 X.2 V F)
  have := isIso_chartStalkTensorComparison B S hS X.2 V F
  exact Module.Flat.of_linearEquiv
    (asIso (chartStalkTensorComparison B S hS X.2 V F)).symm.toLinearEquiv

/-- **A quasi-coherent module with a flat chart stalk at every geometric point is flat over its
own algebraic space.**  If every geometric point of `X` has a small étale neighbourhood on whose
chart the Zariski stalk of the restriction of `F` is flat over the local ring of the chart, then
`F` is flat over `X` in the sense of Stacks 05VV read along the identity. -/
theorem isFlatOver_id_of_forall_exists_flat_chartZariskiModuleStalk
    {X : AlgebraicSpaces B S hS} (F : Modules.{u, u} B S hS X.1 X.2)
    [F.IsQuasicoherentOnSite]
    (h : ∀ xbar : GeometricPoint B S hS X.1, ∃ V : SmallEtaleNeighborhood xbar,
      Module.Flat ↥(chartLocalRing B S hS X.1 V)
        ↥(chartZariskiModuleStalk B S hS X.1 X.2 V F)) :
    IsFlatOver B S hS X.2 (𝟙 X : X ⟶ X).hom F :=
  (isFlatOver_id_iff_forall_flat_geometricModuleStalk B S hS F).2 fun xbar =>
    (h xbar).elim fun V hV =>
      flat_geometricModuleStalk_of_flat_chartZariskiModuleStalk B S hS V F hV

end AlgebraicGeometry.Space

end
