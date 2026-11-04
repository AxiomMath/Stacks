module

public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctors.IsomorphismLimit
public import StacksFrontier.AlgebraicGeometry.TwistChartLocality.DegreeOneCover

/-!
# The twist comparison, reduced to inverse images along the chart spectra

`Stacks.AlgebraicGeometry.TwistChartLocality.isIso_projTwistComparison_of_forall_restrict_one`
reduces invertibility of Tag 01MY's comparison map to its *restrictions* to the standard opens
`D₊(ψ f)` with `f` of degree one. A restriction to an open is not the form in which the chart
algebra is available: what is available is the cartesian square

`AlgebraicGeometry.Proj.isPullback_awayι_map`,

whose two vertical maps are `AlgebraicGeometry.Proj.awayι`, a morphism **out of a literal
spectrum** `Spec (𝒜₍f₎) ⟶ Proj 𝒜`, and whose horizontal map is `Spec.map` of the chart ring
homomorphism. So the useful chart statement is about the inverse image along `awayι`, not about
the restriction to `D₊(ψ f)`, and this file performs that change of form.

Doing so removes the need for any transport along `AlgebraicGeometry.Scheme.isoSpec`: the chart
is not merely isomorphic to a spectrum, it *is* the source of `awayι`, and both
`Stacks.AlgebraicGeometry.TwistChartLocality.isIso_transpose_of_isIso_extension` and
`Stacks.AlgebraicGeometry.SectionsColimit.sectionsPullbackIso`, which are stated for `Spec.map`
of a ring homomorphism, apply to the square's horizontal map on the nose.

## Main results

* `Stacks.AlgebraicGeometry.TwistChartLocality.isIso_of_isIso_pullback_awayι`: **the change of
  form.** Invertibility of the inverse image of a homomorphism of modules along `awayι ℬ (ψ f)`,
  for every `f` of degree one, gives invertibility of the homomorphism — the images of those
  morphisms being the standard opens `D₊(ψ f)`, which cover.
* `Stacks.AlgebraicGeometry.TwistChartLocality.isIso_projTwistComparison_of_forall_pullback_awayι`
  and
  `Stacks.AlgebraicGeometry.TwistChartLocality.hasPolyTwistTransport_of_forall_pullback_awayι`:
  the same reduction for Tag 01MY's comparison map and for the carried hypothesis
  `Stacks.ProjectiveCohomology.HasPolyTwistTransport`.

## What this does not prove

The hypothesis of each statement below is strictly stronger than its conclusion, and **no project
tag attribute is attached here.** What is discharged downstream, by
`Stacks.AlgebraicGeometry.TwistChartLocality.hasPolyTwistTransport` in
`StacksFrontier/AlgebraicGeometry/TwistChartLocality/ChartGamma.lean`, is the reduction below
applied at the chart algebra of
`Stacks.AlgebraicGeometry.TwistChartDegreeOne.isIso_of_tmul_eq_twistDegreeZeroMap` — the twist
transport for the polynomial grading, which is weaker than Tag 01N2's twist assertion in both
the grading and the coefficient map, and carries no tag either. All three of the steps this file
used to list as owed are proved:

* the inverse image along `awayι ℬ (ψ f)` of Tag 01MY's comparison map is identified with an
  inverse adjoint transpose along `Spec.map` of the chart ring homomorphism, in
  `StacksFrontier/AlgebraicGeometry/TwistChartLocality/ChartTranspose.lean`, by
  `Stacks.AlgebraicGeometry.TwistChartLocality.isIso_pullback_awayι_map_twistMap_iff`; the
  morphism whose transpose it is is
  `Stacks.AlgebraicGeometry.TwistChartLocality.chartAdjointTwistMap`;
* the two inverse images are quasi-coherent, in
  `StacksFrontier/AlgebraicGeometry/TwistChartLocality/ChartQcoh.lean`, by
  `Stacks.AlgebraicGeometry.TwistChartLocality.isQuasicoherent_pullback_awayι_twistingSheaf`;
* the global sections of that transpose are the algebraic chart comparison
  `Stacks.AlgebraicGeometry.TwistChartLocality.twistDegreeZeroMap`, in
  `StacksFrontier/AlgebraicGeometry/TwistChartLocality/ChartGamma.lean`: the `𝒜₍f₎`-module
  `Stacks.AlgebraicGeometry.SectionsColimit.moduleSpecΓFunctor` of the inverse image along
  `awayι 𝒜 f` of `𝒪_{Proj 𝒜}(n)` is `𝒜(n)₍f₎` by
  `Stacks.AlgebraicGeometry.TwistChartLocality.chartΓIso`, and `Γ(chartAdjointTwistMap)` is read
  off by
  `Stacks.AlgebraicGeometry.TwistChartLocality.chartΓIso_moduleSpecΓ_chartAdjointTwistMap`. The
  inputs were
  `AlgebraicGeometry.ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv` and
  `AlgebraicGeometry.ProjectiveSpectrum.Proj.imageSectionsIso` at `V = ⊤` — **not**
  `AlgebraicGeometry.ProjectiveSpectrum.Proj.chartDegreeZeroEquiv`, whose target carries a
  `Module.compHom` in its type and so is an equivalence for a second scalar action — together
  with `AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` for the restriction, and
  `Stacks.AlgebraicGeometry.TwistChartLocality.sectionsMap_degreeZeroToSection_val` for the
  chart formula of the adjoint comparison.

## Implementation notes

The covering family is indexed by the subtype of degree-one elements and its members are written
as `AlgebraicGeometry.Scheme.Hom.opensRange` of the chart morphisms rather than as
`AlgebraicGeometry.Proj.basicOpen`: the two are equal by
`AlgebraicGeometry.Proj.opensRange_awayι`, but `TopologicalSpace.Opens.ι` depends on its open, so
using the second spelling in the family would make the step from the chart morphism to the
inclusion a transport rather than `AlgebraicGeometry.Scheme.Hom.isoOpensRange_hom_ι`.

## References

* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 01N2](https://stacks.math.columbia.edu/tag/01N2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory HomogeneousIdeal HomogeneousLocalization

namespace Stacks.AlgebraicGeometry.TwistChartLocality

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj
attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local instance] MvPolynomial.gradedAlgebra

universe u

/-! ### The change of form -/

section AwayChart

variable {A B : Type u} {σ τ : Type u}
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
/-- **Invertibility of a homomorphism of modules on `Proj ℬ` is detected by the inverse images
along the chart spectra of the images of degree-one elements**, when those images generate the
irrelevant ideal of `ℬ`.

The chart morphism `awayι ℬ (ψ f)` is an open immersion onto `D₊(ψ f)`, so it factors as an
isomorphism onto that open followed by its inclusion; inverse image along an isomorphism detects
invertibility, and the opens `D₊(ψ f)` cover by
`Stacks.AlgebraicGeometry.TwistChartLocality.exists_mem_degreeOne_notMem`. -/
public theorem isIso_of_isIso_pullback_awayι (ψ : 𝒜 →+*ᵍ ℬ)
    (hone : (HomogeneousIdeal.irrelevant ℬ).toIdeal ≤ Ideal.span (ψ '' (𝒜 1 : Set A)))
    {M N : (AlgebraicGeometry.Proj ℬ).Modules} (φ : M ⟶ N)
    (h : ∀ (f : A) (hf : f ∈ 𝒜 1),
      IsIso ((Scheme.Modules.pullback (AlgebraicGeometry.Proj.awayι ℬ (ψ f)
        (ψ.map_mem hf) Nat.one_pos)).map φ)) :
    IsIso φ := by
  refine Scheme.Modules.isIso_of_isIso_pullback_ι
    (fun g : {g : A // g ∈ 𝒜 1} => (AlgebraicGeometry.Proj.awayι ℬ (ψ g.1)
      (ψ.map_mem g.2) Nat.one_pos).opensRange) ?_ φ ?_
  · refine eq_top_iff.mpr fun y _ => ?_
    obtain ⟨f, hf, hfy⟩ := exists_mem_degreeOne_notMem 𝒜 ℬ ψ hone y
    refine TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨f, hf⟩, ?_⟩
    rw [AlgebraicGeometry.Proj.opensRange_awayι]
    exact (AlgebraicGeometry.Proj.mem_basicOpen ℬ _ _).mpr hfy
  · intro g
    have h1 := h g.1 g.2
    rw [← Scheme.Hom.isoOpensRange_hom_ι (AlgebraicGeometry.Proj.awayι ℬ (ψ g.1)
      (ψ.map_mem g.2) Nat.one_pos)] at h1
    exact (Scheme.Modules.isIso_pullback_map_iff_of_isIso _ _).mp
      ((Scheme.Modules.isIso_pullback_comp_map_iff _ _ _).mp h1)

/-- **The reduction of Tag 01MY's comparison map to the inverse images along the chart
spectra.** -/
public theorem isIso_projTwistComparison_of_forall_pullback_awayι (ψ : 𝒜 →+*ᵍ ℬ)
    (hψ : ℬ₊ ≤ 𝒜₊.map ψ)
    (hone : (HomogeneousIdeal.irrelevant ℬ).toIdeal ≤ Ideal.span (ψ '' (𝒜 1 : Set A))) (n : ℤ)
    (h : ∀ (f : A) (hf : f ∈ 𝒜 1),
      IsIso ((Scheme.Modules.pullback (AlgebraicGeometry.Proj.awayι ℬ (ψ f)
          (ψ.map_mem hf) Nat.one_pos)).map
        (Stacks.ProjTwistComparison.twistMap ψ hψ n))) :
    IsIso (Stacks.ProjTwistComparison.twistMap ψ hψ n) :=
  isIso_of_isIso_pullback_awayι 𝒜 ℬ ψ hone _ h

end AwayChart

/-! ### The polynomial case -/

section Poly

open Stacks.ProjectiveCohomology

variable (S : Type u) [CommRing S] (n : ℕ)

/-- **The carried hypothesis of the twist transport, reduced to the inverse images along the
chart spectra of the coordinate variables.**

This is the form in which the remaining obligation of
`Stacks.ProjectiveCohomology.HasPolyTwistTransport` should be attacked: the chart is the source of
`AlgebraicGeometry.Proj.awayι`, hence a literal spectrum, and the chart algebra at a degree-one
element is `Stacks.AlgebraicGeometry.TwistChartDegreeOne.isIso_of_tmul_eq_twistDegreeZeroMap`. -/
public theorem hasPolyTwistTransport_of_forall_pullback_awayι
    (h : ∀ (d : ℤ) (f : MvPolynomial (Fin (n + 1)) (ULift.{u} ℤ))
      (hf : f ∈ polyGrading (ULift.{u} ℤ) n 1),
      IsIso ((Scheme.Modules.pullback (AlgebraicGeometry.Proj.awayι (polyGrading S n)
            (polyGradedMap (Fin (n + 1)) (fromULiftInt S) f)
            ((polyGradedMap (Fin (n + 1)) (fromULiftInt S)).map_mem hf) Nat.one_pos)).map
        (Stacks.ProjTwistComparison.twistMap (polyGradedMap (Fin (n + 1)) (fromULiftInt S))
          (irrelevant_le_map_polyGradedMap (Fin (n + 1)) (fromULiftInt S)) d))) :
    HasPolyTwistTransport S n :=
  hasPolyTwistTransport_of_isIso_twistMap S n fun d =>
    isIso_projTwistComparison_of_forall_pullback_awayι (polyGrading (ULift.{u} ℤ) n)
      (polyGrading S n) (polyGradedMap (Fin (n + 1)) (fromULiftInt S))
      (irrelevant_le_map_polyGradedMap (Fin (n + 1)) (fromULiftInt S))
      (irrelevant_le_span_image_degreeOne_poly (ULift.{u} ℤ) S n (fromULiftInt S)) d (h d)

end Poly

end Stacks.AlgebraicGeometry.TwistChartLocality

end
