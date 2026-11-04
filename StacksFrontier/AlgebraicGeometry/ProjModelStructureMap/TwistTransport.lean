module

public import StacksFrontier.AlgebraicGeometry.ProjModelStructureMap.CoefficientBaseChangeCartesian
public import StacksFrontier.AlgebraicGeometry.ProjTwistFunctor.Projective

/-!
# Transporting `𝒪(d)` between the two models of projective space

The development carries two projective `n`-spaces over a commutative ring `S`:

* `AlgebraicGeometry.Proj (Stacks.ProjectiveCohomology.polyGrading S n)`, the homogeneous
  spectrum of `S[T₀, …, Tₙ]`, whose twisting sheaf is
  `AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf (polyGrading S n) d`;
* `AlgebraicGeometry.projectiveSpaceOverRing n S`, the base change of the integral model along
  `Spec S ⟶ Spec ℤ`, whose twisting sheaf
  `Stacks.AlgebraicGeometry.ProjTwistFunctor.projectiveTwistingSheaf n d` is the inverse image of
  the integral one along the projection to the integral model.

The two are isomorphic as schemes for an arbitrary coefficient ring, by
`Stacks.ProjectiveCohomology.projModelIso`. This file transports the question about the twisting
sheaves across that isomorphism: it identifies the inverse image of `𝒪(d)` along `projModelIso`
with the inverse image of the *integral* `𝒪(d)` along
`Stacks.ProjectiveCohomology.projModelMap`, and conversely derives the comparison of the two
`𝒪(d)`'s from an isomorphism for `projModelMap` alone.

## Main definitions

* `Stacks.ProjectiveCohomology.HasPolyTwistTransport`: the assertion that the inverse image of
  the integral twisting sheaf along `projModelMap` is the twisting sheaf of `S[T₀, …, Tₙ]`, in
  every degree. It is a hypothesis of the results below and is proved in
  `StacksFrontier.AlgebraicGeometry.TwistChartLocality.ChartGamma`.

## Main results

* `Stacks.ProjectiveCohomology.pullbackProjModelIsoHomProjectiveTwistingSheafIso`:
  **unconditionally**, the inverse image of the base-change model's `𝒪(d)` along
  `projModelIso` is the inverse image of the integral `𝒪(d)` along `projModelMap`.
* `Stacks.ProjectiveCohomology.nonempty_projectiveTwistingSheaf_iso_pullback_projModelIso_inv`:
  from `HasPolyTwistTransport` in one degree, the two models' `𝒪(d)` correspond under
  `projModelIso`.

## Implementation notes

Both results are a single application of `AlgebraicGeometry.Scheme.Modules.pullbackComp`
followed by `AlgebraicGeometry.Scheme.Modules.pullbackCongr` at the identity
`Stacks.ProjectiveCohomology.projModelIso_hom_toIntegralAtUniverse`, which says that
`projModelIso` carries the projection to the integral model to `projModelMap`. The base-change
model's twisting sheaf is *defined* as an inverse image along that projection, so no description
of either twisting sheaf on sections is used, and nothing here is specific to the degree `1`.

`HasPolyTwistTransport` is a hypothesis *of the statements in this file only*; it **is proved**,
unconditionally in `S` and `n`, by
`Stacks.AlgebraicGeometry.TwistChartLocality.hasPolyTwistTransport` in
`StacksFrontier.AlgebraicGeometry.TwistChartLocality.ChartGamma`. The hypothesis stays here only
because that module imports this one, so the result is not available at this point in the tree;
a consumer should
take it from there rather than assume it. What it asks to be invertible is the comparison
morphism `Stacks.AlgebraicGeometry.ProjTwistCompare.twistMap`, which exists for every graded
ring homomorphism; a coefficient base change along a non-surjective ring map is neither a graded
localization (`Stacks.AlgebraicGeometry.TwistBaseChange.isIso_twistMap`) nor surjective in all
large degrees (`Stacks.AlgebraicGeometry.ProjTwistMono.isIso_projMapData_twistMap`), and the
proof in `ChartGamma` instead checks invertibility on the chart spectra of the degree-one
variables.

Discharging the hypothesis makes the two models' `𝒪(d)` correspond with no hypothesis left; the
consequence for global sections is drawn in
`StacksFrontier.AlgebraicGeometry.ProjModelStructureMap.TwistSectionTransport`.

**No tag attribute is attached here**, and none is attached to
`Stacks.AlgebraicGeometry.TwistChartLocality.hasPolyTwistTransport` either: [Stacks, Tag 01N2]
clause (3) asserts that the canonical comparison `θ` is an isomorphism for a graded algebra over
an arbitrary base change, whereas `HasPolyTwistTransport` is specialized to the polynomial
grading and the single coefficient map `Stacks.ProjectiveCohomology.fromULiftInt`, and asserts
only that *some* isomorphism of the two twisting sheaves exists. The unconditional result below
is a comparison of two inverse images, which is a clause of no tag.

## References

* [Stacks Project, Tag 01N2](https://stacks.math.columbia.edu/tag/01N2)
* [Stacks Project, Tag 01MN](https://stacks.math.columbia.edu/tag/01MN)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.ProjectiveCohomology

variable (S : Type u) [CommRing S] (n : ℕ)

/-- **The inverse image of the base-change model's `𝒪(d)` along the comparison of models is the
inverse image of the integral `𝒪(d)` along `Stacks.ProjectiveCohomology.projModelMap`.**

Unconditional: the base-change model's twisting sheaf is defined as an inverse image along the
projection to the integral model, and `Stacks.ProjectiveCohomology.projModelIso` carries that
projection to `projModelMap`. -/
def pullbackProjModelIsoHomProjectiveTwistingSheafIso (d : ℤ) :
    (Scheme.Modules.pullback (projModelIso S n).hom).obj
        (Stacks.AlgebraicGeometry.ProjTwistFunctor.projectiveTwistingSheaf (R := S) n d) ≅
      (Scheme.Modules.pullback (projModelMap n (fromULiftInt S))).obj
        (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading (ULift.{u} ℤ) n) d) :=
  (Scheme.Modules.pullbackComp (projModelIso S n).hom
      (AlgebraicGeometry.projectiveSpaceOver.toIntegralAtUniverse n
        (Spec (CommRingCat.of S)))).app _ ≪≫
    (Scheme.Modules.pullbackCongr (projModelIso_hom_toIntegralAtUniverse S n)).app _

/-- The comparison of the two models carries `Stacks.ProjectiveCohomology.projModelMap` back to
the projection to the integral model. This is
`Stacks.ProjectiveCohomology.projModelIso_hom_toIntegralAtUniverse` read through the inverse. -/
theorem projModelIso_inv_comp_projModelMap :
    (projModelIso S n).inv ≫ projModelMap n (fromULiftInt S) =
      AlgebraicGeometry.projectiveSpaceOver.toIntegralAtUniverse n (Spec (CommRingCat.of S)) := by
  have h : (projModelIso S n).inv ≫ ((projModelIso S n).hom ≫
      AlgebraicGeometry.projectiveSpaceOver.toIntegralAtUniverse n
        (Spec (CommRingCat.of S))) =
      AlgebraicGeometry.projectiveSpaceOver.toIntegralAtUniverse n (Spec (CommRingCat.of S)) :=
    Iso.inv_hom_id_assoc _ _
  exact Eq.trans (congrArg (fun t => (projModelIso S n).inv ≫ t)
    (projModelIso_hom_toIntegralAtUniverse S n).symm) h

/-- **The twist transport for the polynomial grading and the coefficient map `ULift ℤ → S`**, as
a hypothesis: the inverse image along `Stacks.ProjectiveCohomology.projModelMap` of the integral
twisting sheaf is isomorphic to the twisting sheaf of `S[T₀, …, Tₙ]`, in every degree.

This is weaker than clause (3) of [Stacks, Tag 01N2], which asserts that the canonical comparison
is an isomorphism: it asks only that the two sheaves be isomorphic. -/
def HasPolyTwistTransport : Prop :=
  ∀ d : ℤ, Nonempty ((Scheme.Modules.pullback (projModelMap n (fromULiftInt S))).obj
      (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading (ULift.{u} ℤ) n) d) ≅
    ProjectiveSpectrum.Proj.twistingSheaf (polyGrading S n) d)

/-- **The two models' `𝒪(d)` correspond under the comparison of models**, given the transport
along `Stacks.ProjectiveCohomology.projModelMap` in the degree concerned.

The hypothesis is one degree of `Stacks.ProjectiveCohomology.HasPolyTwistTransport`; the
conclusion is the statement that the base-change model's twisting sheaf is the inverse image of
the `Proj`-model one along `Stacks.ProjectiveCohomology.projModelIso`. -/
theorem nonempty_projectiveTwistingSheaf_iso_pullback_projModelIso_inv (d : ℤ)
    (h : Nonempty ((Scheme.Modules.pullback (projModelMap n (fromULiftInt S))).obj
        (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading (ULift.{u} ℤ) n) d) ≅
      ProjectiveSpectrum.Proj.twistingSheaf (polyGrading S n) d)) :
    Nonempty (Stacks.AlgebraicGeometry.ProjTwistFunctor.projectiveTwistingSheaf (R := S) n d ≅
      (Scheme.Modules.pullback (projModelIso S n).inv).obj
        (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading S n) d)) := by
  obtain ⟨e⟩ := h
  refine ⟨Iso.symm (((Scheme.Modules.pullback (projModelIso S n).inv).mapIso e.symm) ≪≫ ?_)⟩
  exact (Scheme.Modules.pullbackComp (projModelIso S n).inv
      (projModelMap n (fromULiftInt S))).app _ ≪≫
    (Scheme.Modules.pullbackCongr (projModelIso_inv_comp_projModelMap S n)).app _

end Stacks.ProjectiveCohomology

end
