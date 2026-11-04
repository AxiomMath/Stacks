module

public import StacksFrontier.AlgebraicGeometry.ProjectiveChart.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceSections.Preimage
public import StacksFrontier.AlgebraicGeometry.Segre.ProjMono

/-!
# When the morphism to projective space defined by generating sections is a monomorphism

`Stacks.ProjectiveSpaceSections.morphismAtUniverse` is the morphism `φ_{(L, s)} : X ⟶ ℙⁿ_ℤ`
attached to an invertible module `L` on `X` and `n + 1` global sections whose nonvanishing loci
cover. This file gives the criterion of
[Stacks, Tag 01NF](https://stacks.math.columbia.edu/tag/01NF) for it to be a **monomorphism**,
which is the chart criterion of the source and nothing more:

> if every chart `X_{sᵢ}` is affine and the ratios `s₀/sᵢ, …, sₙ/sᵢ` generate `Γ(X_{sᵢ}, 𝒪)` as a
> ring, then `φ_{(L, s)}` is a monomorphism.

"The ratios generate" is stated as surjectivity of
`Stacks.ProjectiveSpaceSections.chartHom`, the ring homomorphism `ℤ[T₀, …, Tₙ] → Γ(X_{sᵢ}, 𝒪)`
sending `Tₖ` to `sₖ / sᵢ`, which is the same thing and is the form the proof consumes.

Being a monomorphism is Zariski-local at the target
(Mathlib's `IsZariskiLocalAtTarget (MorphismProperty.monomorphisms Scheme)`), the standard opens
`D₊(Tᵢ)` cover `ℙⁿ`, and `Stacks.ProjectiveSpaceSections.morphismAtUniverse_preimage_basicOpen`
identifies `φ⁻¹D₊(Tᵢ)` with the chart `X_{sᵢ}`, over which `φ` *is* the chart morphism. So the
whole content is that each chart morphism is a monomorphism, and that is
`AlgebraicGeometry.Proj.mono_fromOfGlobalSections`.

## Main results

* `Stacks.ProjectiveSpaceSections.mono_chartMorphism`: the chart morphism out of an affine chart
  is a monomorphism when the ratios generate.
* `Stacks.ProjectiveSpaceSections.mono_morphismAtUniverse`: **`φ_{(L, s)}` is a monomorphism when
  every chart is affine and the ratios generate on every chart.**

## Implementation notes

No `@[stacks]` attribute is attached: Tag 01NF is the construction of `φ_{(L, s)}` together with
its characterizing identities, of which this is neither.

The restriction `φ ∣_ D₊(Tᵢ)` is handled by cancellation rather than by an arrow isomorphism:
`AlgebraicGeometry.morphismRestrict_ι` makes `φ ∣_ U ≫ U.ι` equal to `(φ⁻¹U).ι ≫ φ`, and
`CategoryTheory.mono_of_mono_fac` turns monicity of the latter into monicity of the restriction,
which is why no transport along `φ⁻¹D₊(Tᵢ) = X_{sᵢ}` beyond `AlgebraicGeometry.Scheme.isoOfEq` is
needed.

## References

* [Stacks Project, Tag 01NE](https://stacks.math.columbia.edu/tag/01NE)
* [Stacks Project, Tag 01NF](https://stacks.math.columbia.edu/tag/01NF)
* [Stacks Project, Tag 01NG](https://stacks.math.columbia.edu/tag/01NG)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry Limits
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace Stacks.ProjectiveSpaceSections

attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme.{u}} (L : X.Modules)
  [SheafOfModules.IsInvertible X.presheaf (structureSheafRing X.toRingedSpace).property L]

/-- **The chart morphism out of an affine chart is a monomorphism as soon as the ratios generate
the chart's ring.** The chart morphism is `AlgebraicGeometry.Proj.fromOfGlobalSections` for
`Stacks.ProjectiveSpaceSections.chartHom`, which sends the degree-one element `Tᵢ` to `1` by
`Stacks.ProjectiveSpaceSections.chartHom_X_self`, so
`AlgebraicGeometry.Proj.mono_fromOfGlobalSections` applies. -/
theorem mono_chartMorphism {n : ℕ} (s : Fin (n + 1) → L.sections) (i : Fin (n + 1))
    [IsAffine (nonvanishingChart L (s i)).toScheme]
    (hsurj : Function.Surjective (chartHom L s i)) :
    Mono (chartMorphism L s i) :=
  Proj.mono_fromOfGlobalSections _ (chartHom L s i) (map_irrelevant_chartHom_eq_top L s i)
    hsurj (ProjectiveChart.X_mem_degree_one _ i) (chartHom_X_self L s i)

/-- **The morphism to projective space defined by a family of generating sections of an invertible
module is a monomorphism**, provided every chart `X_{sᵢ}` is affine and the ratios `sₖ / sᵢ`
generate `Γ(X_{sᵢ}, 𝒪)` as a ring.

This is the criterion the proof of [Stacks, Tag 01WD](https://stacks.math.columbia.edu/tag/01WD)
uses for the Segre morphism, and the proof of [Stacks, Tag 01NA] for a projective embedding: being
a monomorphism is Zariski-local at the target, and over the standard open `D₊(Tᵢ)` the morphism is
the chart morphism `Stacks.ProjectiveSpaceSections.chartMorphism`. -/
theorem mono_morphismAtUniverse {n : ℕ} (s : Fin (n + 1) → L.sections)
    (hs : (⨆ i, nonvanishingChart L (s i)) = ⊤)
    (haff : ∀ i, IsAffine (nonvanishingChart L (s i)).toScheme)
    (hsurj : ∀ i, Function.Surjective (chartHom L s i)) :
    Mono (morphismAtUniverse L s hs) := by
  rw [← MorphismProperty.monomorphisms.iff]
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (fun i => standardOpen.{u} n i)
    (ProjectiveChart.iSup_basicOpen_X_eq_top (ULift.{u} ℤ) n) fun i => ?_
  rw [MorphismProperty.monomorphisms.iff]
  have := haff i
  have hchart : Mono (chartMorphism L s i) := mono_chartMorphism L s i (hsurj i)
  have hpre : morphismAtUniverse L s hs ⁻¹ᵁ standardOpen.{u} n i = nonvanishingChart L (s i) :=
    morphismAtUniverse_preimage_basicOpen L s hs i
  have hfac : Mono ((morphismAtUniverse L s hs ⁻¹ᵁ standardOpen.{u} n i).ι
      ≫ morphismAtUniverse L s hs) := by
    rw [← Scheme.isoOfEq_hom_ι X hpre, Category.assoc,
      nonvanishingChart_ι_morphismAtUniverse]
    infer_instance
  exact mono_of_mono_fac (morphismRestrict_ι _ _)

end Stacks.ProjectiveSpaceSections

end
