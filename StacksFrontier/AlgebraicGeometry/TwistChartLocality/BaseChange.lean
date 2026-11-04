module

public import StacksFrontier.AlgebraicGeometry.ProjModelStructureMap.TwistTransport
public import StacksFrontier.AlgebraicGeometry.ProjTwistMono.Trivialized
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Twist.Comparison

/-!
# The twist transport of a coefficient extension, reduced to the standard charts

The twist transport for a change of coefficient ring of a polynomial algebra is carried, in this
library, by the hypothesis `Stacks.ProjectiveCohomology.HasPolyTwistTransport`: that the inverse
image along `Stacks.ProjectiveCohomology.projModelMap` of the twisting sheaf of `ℤ[T₀, …, Tₙ]` is
isomorphic to the twisting sheaf of `S[T₀, …, Tₙ]`, in every degree. Six tags hang off it. This
file reduces it to a chart-local statement.

That hypothesis is weaker than Tag 01N2's twist assertion, which is about the canonical
comparison for an arbitrary graded algebra and an arbitrary base change, and nothing here or
downstream of it carries that tag.

Two steps, both of them changes of form rather than mathematics.

First, `projModelMap n f` is by definition `AlgebraicGeometry.Proj.map` of the graded map
`Stacks.ProjectiveCohomology.polyGradedMap`, and `Stacks.ProjTwistComparison.twistMap` is a
morphism of exactly the shape the hypothesis asks for an isomorphism of — its target is the
twisting sheaf itself, not an inverse image of it along the inclusion of a domain of definition.
So the hypothesis follows from invertibility of that comparison map, with nothing to transport.

Second, invertibility of a morphism of sheaves of modules is local on the base, and for a graded
map whose domain of definition is everything the standard opens `D₊(ψ f)` with `f` homogeneous of
positive degree cover the base. So invertibility of the comparison map follows from invertibility
of each of its restrictions to such an open.

## Main results

* `Stacks.AlgebraicGeometry.TwistChartLocality.isIso_projTwistComparison_of_forall_restrict`:
  **the reduction to the standard charts**, for the comparison map of a graded map whose domain
  of definition is all of `Proj ℬ`.
* `Stacks.AlgebraicGeometry.TwistChartLocality.hasPolyTwistTransport_of_isIso_twistMap`:
  **the bridge to the carried hypothesis.** If the comparison map of
  `Stacks.ProjectiveCohomology.polyGradedMap` at `ULift ℤ → S` is invertible in every degree,
  then `Stacks.ProjectiveCohomology.HasPolyTwistTransport` holds.

## What this does not prove

The reduction below is **not** the one that discharges
`Stacks.ProjectiveCohomology.HasPolyTwistTransport`, and **no project tag attribute is attached
here.** The hypothesis of the reduction is strictly stronger than its conclusion.
`HasPolyTwistTransport` is proved in
`StacksFrontier/AlgebraicGeometry/TwistChartLocality/ChartGamma.lean`, by
`Stacks.AlgebraicGeometry.TwistChartLocality.hasPolyTwistTransport`, along the chain the
implementation notes below describe.

The chart-local statement this file envisaged runs as follows. By
`Stacks.AlgebraicGeometry.TwistChartLocality.map_homEquiv_symm` the restriction of the
comparison map to a chart is again an inverse adjoint transpose, of a morphism built from
`Stacks.ProjTwistComparison.pushforwardTwistMap`, which has a formula on sections; by
`Stacks.AlgebraicGeometry.TwistChartLocality.isIso_transpose_of_isIso_extension` such a
transpose over an affine base is invertible as soon as the base change of its global sections
is; and the base change of the global sections in question is
`Stacks.ProjStandardOpenBaseChange.standardOpenBaseChange`, read in the chart-sections model
through `Stacks.AlgebraicGeometry.TwistAwayBridge.twistAwayEquiv`. The steps still missing
between those are listed in the implementation notes.

## Implementation notes

The reduction is stated for a hypothesis `Stacks.AlgebraicGeometry.ProjShared.mapDomain 𝒜 ℬ ψ =
⊤` rather than for `ℬ₊ ≤ 𝒜₊.map ψ`, which is what `AlgebraicGeometry.Proj.map` takes: the two
say the same thing, but only the first is in the form
`Stacks.AlgebraicGeometry.ProjShared.mem_mapDomain_iff` consumes, and that membership
characterisation is exactly the cover.

The reduction below is stated for the *restrictions* to the standard opens, and that is not the
form the chart algebra is available in. The chain that discharges it therefore does not pass
through this file: `StacksFrontier/AlgebraicGeometry/TwistChartLocality/AwayChart.lean` changes the
form to the inverse images along the chart spectra `AlgebraicGeometry.Proj.awayι`, which are
morphisms out of literal affine spectra, and from there

* `StacksFrontier/AlgebraicGeometry/TwistChartLocality/ChartTranspose.lean` identifies the chart
  inverse image of the comparison map with an inverse adjoint transpose along `Spec.map` of the
  chart ring homomorphism, which removes both the conjugation this file used to record as owed
  and the transport along `AlgebraicGeometry.Scheme.isoSpec`, the chart being a spectrum on the
  nose rather than only up to isomorphism;
* `StacksFrontier/AlgebraicGeometry/TwistChartLocality/ChartQcoh.lean` discharges the
  quasi-coherence of the two inverse images;
* `StacksFrontier/AlgebraicGeometry/TwistChartLocality/ChartBaseChange.lean` discharges the
  invertibility of the coefficient extension of the chart comparison, for `f` of degree one.

* `StacksFrontier/AlgebraicGeometry/TwistChartLocality/ChartGamma.lean` identifies the global
  sections of that transpose with the algebraic map of degree-zero localizations
  `𝒜(n)₍f₎ → ℬ(n)₍ψ f₎`, and closes the chain.

## References

* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 01N2](https://stacks.math.columbia.edu/tag/01N2)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory HomogeneousIdeal
open Stacks.AlgebraicGeometry.ProjShared

namespace Stacks.AlgebraicGeometry.TwistChartLocality

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj
attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local instance] MvPolynomial.gradedAlgebra

universe u

/-! ### The reduction to the standard charts -/

section Reduction

variable {A B : Type u} {σ τ : Type u}
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- **The reduction to the standard charts.** Let `ψ : 𝒜 →+*ᵍ ℬ` be a graded ring homomorphism
whose domain of definition is all of `Proj ℬ`. If the restriction of the comparison map
`Stacks.ProjTwistComparison.twistMap` to `D₊(ψ f)` is an isomorphism for every homogeneous `f`
of positive degree, then the comparison map is an isomorphism.

Those opens cover `Proj ℬ` precisely because the domain of definition is everything, which is
what `Stacks.AlgebraicGeometry.ProjShared.mem_mapDomain_iff` says. -/
public theorem isIso_projTwistComparison_of_forall_restrict (ψ : 𝒜 →+*ᵍ ℬ)
    (hψ : ℬ₊ ≤ 𝒜₊.map ψ) (hdom : mapDomain 𝒜 ℬ ψ = ⊤) (n : ℤ)
    (h : ∀ (d : ℕ) (f : A), 0 < d → f ∈ 𝒜 d →
      IsIso ((Scheme.Modules.restrictFunctor (AlgebraicGeometry.Proj.basicOpen ℬ (ψ f)).ι).map
        (Stacks.ProjTwistComparison.twistMap ψ hψ n))) :
    IsIso (Stacks.ProjTwistComparison.twistMap ψ hψ n) := by
  refine ProjTwistMono.isIso_of_isIso_restrict_locally _ fun y => ?_
  have hy : y ∈ mapDomain 𝒜 ℬ ψ := hdom ▸ trivial
  obtain ⟨d, f, hd, hf, hfy⟩ := (mem_mapDomain_iff 𝒜 ℬ ψ y).mp hy
  exact ⟨AlgebraicGeometry.Proj.basicOpen ℬ (ψ f),
    (AlgebraicGeometry.Proj.mem_basicOpen ℬ _ _).mpr hfy, h d f hd hf⟩

end Reduction

/-! ### The bridge to the carried hypothesis -/

section Transport

open Stacks.ProjectiveCohomology

variable (S : Type u) [CommRing S] (n : ℕ)

/-- **The carried hypothesis of the twist transport follows from invertibility of the comparison
map.** `Stacks.ProjectiveCohomology.projModelMap` is `AlgebraicGeometry.Proj.map` of
`Stacks.ProjectiveCohomology.polyGradedMap`, and the target of
`Stacks.ProjTwistComparison.twistMap` is the twisting sheaf itself, so an invertible comparison
map is literally the isomorphism that
`Stacks.ProjectiveCohomology.HasPolyTwistTransport` asserts to exist. -/
public theorem hasPolyTwistTransport_of_isIso_twistMap
    (h : ∀ d : ℤ, IsIso (Stacks.ProjTwistComparison.twistMap
      (polyGradedMap (Fin (n + 1)) (fromULiftInt S))
      (irrelevant_le_map_polyGradedMap (Fin (n + 1)) (fromULiftInt S)) d)) :
    HasPolyTwistTransport S n := by
  refine fun d => ⟨@asIso _ _ _ _ _ (h d)⟩

end Transport

end Stacks.AlgebraicGeometry.TwistChartLocality

end
