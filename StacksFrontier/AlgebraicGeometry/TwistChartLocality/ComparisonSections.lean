module

public import StacksFrontier.AlgebraicGeometry.RelativeProj.Twist.Comparison
public import StacksFrontier.AlgebraicGeometry.TwistChartLocality.SectionsAlgebra

/-!
# The chart formula for the comparison map whose invertibility the twist transport needs

There are **two** comparison maps on twists in this library, built from the same fibre-level
localization of `ψ` but indexed differently:

* `Stacks.AlgebraicGeometry.ProjTwistCompare.twistMap`, whose adjoint
  `twistPushforwardMap` is indexed by the domain of definition `U(ψ)` and the opens
  `U(ψ).ι ''ᵁ (mapHom ⁻¹ᵁ U)`; and
* `Stacks.ProjTwistComparison.twistMap`, whose adjoint `pushforwardTwistMap` is indexed by
  `AlgebraicGeometry.Proj.map ψ hψ` and the opens `U.comap (ProjectiveSpectrum.comap ψ hψ)`.

`Stacks.ProjectiveCohomology.HasPolyTwistTransport` is reduced to invertibility of the **second**
by `Stacks.AlgebraicGeometry.TwistChartLocality.hasPolyTwistTransport_of_isIso_twistMap`, and it
is the second that
`StacksFrontier/AlgebraicGeometry/TwistChartLocality/AwayChart.lean` reduces to the chart spectra.
But the chart formula that is available —
`Stacks.AlgebraicGeometry.TwistChartLocality.twistSection_degreeZeroToSection_val` — is about the
**first**. So the formula the keystone needs was not available for the map the keystone is about.

This file proves it for the second map, directly rather than by transport. That is both shorter
and cleaner: no domain of definition, no `liftPt`, and no image-of-a-preimage open appears, the
chart on the target being simply the inverse image of `D₊(f)`.

## Main results

* `Stacks.AlgebraicGeometry.TwistChartLocality.fibreMap_moduleToFiber_comparison`: the fibre
  comparison of `Stacks.ProjTwistComparison.fibreMap` is the algebraic map
  `Stacks.AlgebraicGeometry.TwistChartLocality.awayModuleMap`, on the whole of `A[1/f]` and with
  no degree condition.
* `Stacks.AlgebraicGeometry.TwistChartLocality.sectionsMap_degreeZeroToSection_val`: **the chart
  formula.** On the chart of a homogeneous `f`, the comparison on sections of
  `Stacks.ProjTwistComparison.sectionsMap` carries the section attached to an element of
  `𝒜(n)₍f₎` to the section attached to its image under
  `Stacks.AlgebraicGeometry.TwistChartLocality.twistDegreeZeroMap`, for **every** element and not
  only for a homogeneous fraction.

## What this does not prove

**No project tag attribute is attached here.** This is the formula on sections; it becomes the
hypothesis of `Stacks.AlgebraicGeometry.TwistChartLocality.isIso_transpose_of_isIso_extension` in
`StacksFrontier/AlgebraicGeometry/TwistChartLocality/ChartGamma.lean`, where
`Stacks.AlgebraicGeometry.TwistChartLocality.chartΓIso` identifies
`Stacks.AlgebraicGeometry.SectionsColimit.moduleSpecΓFunctor` of the inverse image along
`AlgebraicGeometry.Proj.awayι` with `𝒜(n)₍f₎` and this formula computes the global sections of
`Stacks.AlgebraicGeometry.TwistChartLocality.chartAdjointTwistMap`, whose transpose
identification is
`StacksFrontier/AlgebraicGeometry/TwistChartLocality/ChartTranspose.lean`. With those, the twist
transport for the polynomial grading is discharged there; Tag 01N2's twist assertion, which is
about the canonical comparison for an arbitrary graded algebra and base change, is not.

## Implementation notes

For that identification, note that
`AlgebraicGeometry.ProjectiveSpectrum.Proj.chartDegreeZeroEquiv` is **not** the right input, in
spite of being the only statement of the library naming the chart sections and the degree-zero
localization together. It compares the sections over an open `V` of the chart of `f` with
`𝒜(n)₍g₎` for the `g` cutting out the image of `V`, and is therefore semilinear along a ring
homomorphism `α : 𝒜₍f₎ → 𝒜₍g₎` whose target module structure is a `Module.compHom` written into
the type; at `g = f` that `α` is the identity, but `Module.compHom M (RingHom.id _)` is not the
module structure `M` already carries, so the result is a linear equivalence for a second scalar
action and not for the one the invertibility criterion consumes.

The α-free ingredient is what to use instead:
`AlgebraicGeometry.ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv`, which is
`Γ(D₊(f), associatedModuleSheaf 𝒜 𝒨) ≃ₗ[𝒜₍f₎] GradedModuleDegreeZeroLocalization 𝒜 𝒨 f` for the
plain action, being `AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeZeroToSection` inverted.
Together with `AlgebraicGeometry.ProjGradedModuleQcoh.imageSectionsIso` at `V = ⊤` — the second
ingredient of `chartDegreeZeroEquiv`, also public — it gives the chart sections with no `α` in
sight.

Every step below is taken on elements. The identity is proved by `LocalizedModule.induction_on`,
so it holds for every element of the degree-zero localization rather than only for a homogeneous
fraction, which is what lets the consumer quantify over all of `𝒜(n)₍f₎`.

## References

* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 01N2](https://stacks.math.columbia.edu/tag/01N2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry HomogeneousIdeal HomogeneousLocalization TopologicalSpace
open AlgebraicGeometry.ProjectiveSpectrum.Proj

namespace Stacks.AlgebraicGeometry.TwistChartLocality

universe u

variable {A B : Type u} {σ τ : Type u}
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]

/-- **The fibre comparison is the algebraic map, on the whole localized module.** Pushing an
element of `A[1/f]` into the fibre at the point below and comparing is applying `ψ` to a
numerator and a denominator and then pushing into the fibre.

Nothing is restricted to a degree-zero part: both sides are additive and `LocalizedModule` is
generated by its fractions. -/
public theorem fibreMap_moduleToFiber_comparison (ψ : 𝒜 →+*ᵍ ℬ) (hψ : ℬ₊ ≤ 𝒜₊.map ψ) {f : A}
    (y : ↥((ProjectiveSpectrum.basicOpen 𝒜 f).comap (ProjectiveSpectrum.comap ψ hψ)))
    (hy : y.1 ∈ ProjectiveSpectrum.basicOpen ℬ (ψ f))
    (w : LocalizedModule.Away (R := A) f A) :
    Stacks.ProjTwistComparison.fibreMap ψ hψ y.1
        (moduleToFiber (M := A) 𝒜 f ⟨ProjectiveSpectrum.comapFun ψ hψ y.1, y.2⟩ w) =
      moduleToFiber (M := B) ℬ (ψ f) ⟨y.1, hy⟩ (awayModuleMap 𝒜 ℬ ψ f w) := by
  induction w using LocalizedModule.induction_on with
  | h m s =>
    obtain ⟨k, hk⟩ := s.2
    have hs : ψ (s : A) ∈ Submonoid.powers (ψ f) := ⟨k, by rw [← hk, map_pow]⟩
    rw [moduleToFiber_mk, Stacks.ProjTwistComparison.fibreMap_mk,
      awayModuleMap_mk 𝒜 ℬ ψ f m s hs, moduleToFiber_mk]

/-- **The chart formula for the comparison map the twist transport is about.**

Over the standard chart `D₊(f)` of `Proj 𝒜`, the comparison on sections
`Stacks.ProjTwistComparison.sectionsMap` carries the section of `𝒪_{Proj 𝒜}(n)` attached to an
element `v` of the degree-zero localization `𝒜(n)₍f₎` to the section of `𝒪_{Proj ℬ}(n)` attached
to `Stacks.AlgebraicGeometry.TwistChartLocality.twistDegreeZeroMap v`, which applies `ψ` to a
numerator and a denominator.

The identity holds for every `v`, not merely for a homogeneous fraction, and is stated pointwise
at a point of the inverse image of `D₊(f)`, which needs no identification of opens. -/
public theorem sectionsMap_degreeZeroToSection_val (ψ : 𝒜 →+*ᵍ ℬ) (hψ : ℬ₊ ≤ 𝒜₊.map ψ) (n : ℤ)
    {f : A} (v : GradedModuleDegreeZeroLocalization 𝒜 (twistGrading (S := A) 𝒜 n) f)
    (y : ↥((ProjectiveSpectrum.basicOpen 𝒜 f).comap (ProjectiveSpectrum.comap ψ hψ)))
    (hy : y.1 ∈ ProjectiveSpectrum.basicOpen ℬ (ψ f)) :
    (Stacks.ProjTwistComparison.sectionsMap ψ hψ n (ProjectiveSpectrum.basicOpen 𝒜 f)
        (degreeZeroToSection 𝒜 (twistGrading (S := A) 𝒜 n) f v)).1 y =
      (degreeZeroToSection ℬ (twistGrading (S := B) ℬ n) (ψ f)
        (twistDegreeZeroMap 𝒜 ℬ ψ f n v)).1 ⟨y.1, hy⟩ :=
  fibreMap_moduleToFiber_comparison 𝒜 ℬ ψ hψ y hy v.1

end Stacks.AlgebraicGeometry.TwistChartLocality

end
