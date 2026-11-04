module

public import StacksFrontier.AlgebraicGeometry.ProjTwistCompare.Twist
public import StacksFrontier.AlgebraicGeometry.ProjTwistMono.Trivialized

/-!
# The comparison map on twists is an isomorphism as soon as it is one on the standard charts

Let `ψ : 𝒜 →+*ᵍ ℬ` be a homomorphism of nonnegatively graded rings, `U(ψ) ⊆ Proj ℬ` its domain
of definition and `θ n` Tag 01MY's comparison map on the `n`-th twist. The domain of definition
is by construction the union of the standard opens `D₊(ψ f)` for `f` homogeneous of positive
degree, so the opens `U(ψ) ∩ D₊(ψ f)` cover `U(ψ)` — and being an isomorphism is local. This
file records that reduction.

The point of isolating it is that each member of the cover is an *affine* chart on which both
sides of `θ n` are quasi-coherent, so the residual obligation is a statement about modules over
the degree-zero localizations, with no sheaf theory left in it.

## Main definitions

* `Stacks.AlgebraicGeometry.TwistChartLocality.chartOpen`: the open `U(ψ) ∩ D₊(ψ f)` of `U(ψ)`,
  as the inverse image of `D₊(ψ f)` along the open immersion of the domain of definition.

## Main results

* `Stacks.AlgebraicGeometry.TwistChartLocality.chartOpen_cover`: every point of `U(ψ)` lies in
  one of those opens, with `f` of positive degree.
* `Stacks.AlgebraicGeometry.TwistChartLocality.isIso_twistMap_of_forall_restrict`: **the
  reduction.** If the restriction of `θ n` to `U(ψ) ∩ D₊(ψ f)` is an isomorphism for every
  homogeneous `f` of positive degree, then `θ n` is an isomorphism.
* `Stacks.AlgebraicGeometry.TwistChartLocality.isIso_projMapData_twistMap_of_forall_restrict`:
  the same for the comparison map carried by Tag 01MY's bundle
  `Stacks.AlgebraicGeometry.ProjTwistCompare.projMapData`, which is the form the related statements
  quantify over. It is the previous result unchanged, the bundle's twist map being `twistMap`
  by definition.

## What this is for, and what it does not prove

Nothing here is specific to any hypothesis on `ψ`: the cover exists for every graded ring
homomorphism, which is why the hypothesis of the reduction is quantified over all homogeneous
`f` of positive degree rather than over a chosen generating family.

The reduction is **not** discharged for any `ψ`, and in particular the twist assertion of
Stacks Tag 01N2 — the base change `ℬ = R' ⊗_R 𝒜`, whose domain of definition is all of
`Proj (R' ⊗_R A)` by `Stacks.AlgebraicGeometry.ProjShared.mapDomain_baseChange` — is not proved
here. For that case the residual obligation is, chart by chart, the module statement

> `Γ(D₊(1 ⊗ f), 𝒪(n))` is the base change along `𝒜₍f₎ → (R' ⊗_R 𝒜)₍1 ⊗ f₎` of
> `Γ(D₊(f), 𝒪(n))`,

of which four of the five inputs are available, and none is new mathematics:

* invertibility on an affine scheme is detected on global sections for quasi-coherent modules,
  `Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_moduleSpecΓ`, with both sides
  quasi-coherent by `Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback` and
  `AlgebraicGeometry.associatedModuleSheaf_isQuasicoherent`;
* the global sections of a pullback along a morphism of spectra are the base change of the
  global sections, `Stacks.AlgebraicGeometry.SectionsColimit.sectionsPullbackIso`;
* the chart sections of an associated module sheaf are the degree-zero localization of its
  grading, `AlgebraicGeometry.ProjectiveSpectrum.Proj.chartDegreeZeroEquiv`;
* the base-change isomorphism of those localizations, for the graded ring and all of its twists
  at once and compatibly, `Stacks.ProjStandardOpenBaseChange.standardOpenBaseChange`.

Two things are genuinely absent. First, the identification of the global-sections map of `θ`
itself — `θ` is an inverse adjoint transpose, and what has a formula on sections is its adjoint
`Stacks.AlgebraicGeometry.ProjTwistCompare.twistPushforwardMap`, so the two have to be matched
across `Stacks.AlgebraicGeometry.SectionsColimit.sectionsPullbackIso`.
`Stacks.AlgebraicGeometry.PullbackStalkScheme.stalkPullbackIso` is the stalk-level analogue and
carries no formula on germs either. Second, the two inputs above speak **different models
of the same module**: the chart sections are the root-namespace
`GradedModuleDegreeZeroLocalization`, while `Stacks.ProjStandardOpenBaseChange.twistAway` is a
submodule of `Localization (Submonoid.powers f)`, and no bridge between the two is proved
anywhere.

No project tag is attached. Tag 01N2's twist assertion is not proved, and no assertion of any
tag is proved below: the reduction's hypothesis is strictly stronger than its conclusion.

## References

* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 01N2](https://stacks.math.columbia.edu/tag/01N2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.ProjTwistCompare

namespace Stacks.AlgebraicGeometry.TwistChartLocality

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj
attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top

universe u w w'

variable {A B : Type u} {σ : Type w} {τ : Type w'}
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]

/-- The open `U(ψ) ∩ D₊(ψ f)` of the domain of definition, as an open of `U(ψ)`. -/
public def chartOpen (ψ : 𝒜 →+*ᵍ ℬ) (f : A) : (mapDomain 𝒜 ℬ ψ).toScheme.Opens :=
  (mapDomain 𝒜 ℬ ψ).ι ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen ℬ (ψ f)

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
/-- **The standard charts cover the domain of definition.** A point of `U(ψ)` omits `ψ f` for
some homogeneous `f` of positive degree, which is what membership of `U(ψ)` says. -/
public theorem chartOpen_cover (ψ : 𝒜 →+*ᵍ ℬ) (x : (mapDomain 𝒜 ℬ ψ).toScheme) :
    ∃ (d : ℕ) (f : A), 0 < d ∧ f ∈ 𝒜 d ∧ x ∈ chartOpen 𝒜 ℬ ψ f := by
  have hrange : (mapDomain 𝒜 ℬ ψ).ι.base x ∈ (mapDomain 𝒜 ℬ ψ).ι.opensRange := ⟨x, rfl⟩
  rw [Scheme.Opens.opensRange_ι] at hrange
  obtain ⟨d, f, hd, hf, hfx⟩ := (mem_mapDomain_iff 𝒜 ℬ ψ _).mp hrange
  exact ⟨d, f, hd, hf, (AlgebraicGeometry.Proj.mem_basicOpen ℬ _ _).mpr hfx⟩

/-- **The reduction to the standard charts.** If the restriction of Tag 01MY's comparison map
`θ n` to `U(ψ) ∩ D₊(ψ f)` is an isomorphism for every homogeneous `f` of positive degree, then
`θ n` is an isomorphism. -/
public theorem isIso_twistMap_of_forall_restrict (ψ : 𝒜 →+*ᵍ ℬ) (n : ℤ)
    (h : ∀ (d : ℕ) (f : A), 0 < d → f ∈ 𝒜 d →
      IsIso ((Scheme.Modules.restrictFunctor (chartOpen 𝒜 ℬ ψ f).ι).map
        (twistMap 𝒜 ℬ ψ n))) :
    IsIso (twistMap 𝒜 ℬ ψ n) := by
  refine ProjTwistMono.isIso_of_isIso_restrict_locally _ fun x => ?_
  obtain ⟨d, f, hd, hf, hxf⟩ := chartOpen_cover 𝒜 ℬ ψ x
  exact ⟨chartOpen 𝒜 ℬ ψ f, hxf, h d f hd hf⟩

/-- The reduction, for the comparison map carried by Tag 01MY's bundle. -/
public theorem isIso_projMapData_twistMap_of_forall_restrict (ψ : 𝒜 →+*ᵍ ℬ) (n : ℤ)
    (h : ∀ (d : ℕ) (f : A), 0 < d → f ∈ 𝒜 d →
      IsIso ((Scheme.Modules.restrictFunctor (chartOpen 𝒜 ℬ ψ f).ι).map
        ((projMapData 𝒜 ℬ ψ).twistMap n))) :
    IsIso ((projMapData 𝒜 ℬ ψ).twistMap n) :=
  isIso_twistMap_of_forall_restrict 𝒜 ℬ ψ n h

end Stacks.AlgebraicGeometry.TwistChartLocality

end
