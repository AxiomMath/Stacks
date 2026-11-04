module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceSections.Glue
public import StacksFrontier.AlgebraicGeometry.AffineNonvanishing.Sum
public import StacksFrontier.AlgebraicGeometry.SectionExtension.Multiplication

/-!
# The preimage of a standard open under the morphism defined by generating sections

Let `L` be an invertible module on a scheme `X` and let `s₀, …, sₙ` be global sections of `L`
whose nonvanishing loci cover `X`, so that
`Stacks.ProjectiveSpaceSections.morphismAtUniverse` is the morphism `φ_{(L, s)} : X ⟶ ℙⁿ`. This
file identifies the preimage of the standard open `D₊(Tᵢ)` under `φ`:

`φ⁻¹(D₊(Tᵢ)) = X_{sᵢ}`,

the nonvanishing locus of `sᵢ`. It is the only property of `φ` used by the proof of
[Stacks, Tag 0A27](https://stacks.math.columbia.edu/tag/0A27), which reads it off as *"the
inverse image of `D₊(T₀)` is `U = X \ {x}`, as the section `s₀` of `𝓛` only vanishes at `x`"*.
In particular 0A27 needs neither of the two identities `φ^* 𝒪(1) ≅ L` and `φ^* Tᵢ = sᵢ` that
`Glue.lean` flags as missing, and which would require a twisting sheaf on
`projectiveSpaceAtUniverse` that this repository does not have.

## Main results

* `Stacks.ProjectiveSpaceSections.basicOpen_divBySection`: the basic open of the function
  `sₖ / sᵢ` on the chart `X_{sᵢ}` is `X_{sₖ} ⊓ X_{sᵢ}`.
* `Stacks.ProjectiveSpaceSections.ι_image_basicOpen_chartRatio`: the same statement read inside
  the chart, as an open of `X` through `Scheme.Opens.ι`.
* `Stacks.ProjectiveSpaceSections.morphismAtUniverse_preimage_basicOpen`:
  **`φ⁻¹(D₊(Tᵢ)) = X_{sᵢ}`.**
* `Stacks.ProjectiveSpaceSections.morphismOver_preimage_basicOpen`: the same for the lift of `φ`
  to relative projective space over a base.

## Implementation notes

The chart-level computation is already available: on `X_{sⱼ}` the morphism is
`AlgebraicGeometry.Proj.fromOfGlobalSections` for the ratios, and Mathlib's
`AlgebraicGeometry.Proj.fromOfGlobalSections_preimage_basicOpen` describes the preimage of
`D₊(Tᵢ)` as the basic open of `sᵢ / sⱼ`. That is
`Stacks.ProjectiveSpaceSections.chartMorphism_preimage_basicOpen`. Two things are added here.

The first is the identification of that basic open with an intersection of nonvanishing loci.
It is not a computation with ratios but the local-algebra fact that on `X_{sⱼ}` the germ of `sⱼ`
generates the stalk of `L`, so the germ of `sᵢ` escapes `𝔪ₓLₓ` exactly when the germ of
`sᵢ / sⱼ` is a unit. That is already proved as
`AlgebraicGeometry.Scheme.Modules.basicOpen_eq_inf_nonvanishingOpen_of_smul_eq`, whose
hypothesis `h • sⱼ|_T = sᵢ|_T` is the defining property
`Stacks.SheafOfModules.smul_divBySection` of the quotient; it is stated for global sections
presented as elements of `Γ(X, L)`, so `Stacks.SheafOfModules.Invertible`'s
`sectionsOfTop_eval_top_self` converts.

The second is globalisation. Opens of `X` are determined by their intersections with the members
of a cover because `TopologicalSpace.Opens` is a frame: `inf_iSup_eq` turns the cover hypothesis
`⨆ i, X_{sᵢ} = ⊤` into the needed descent, with no appeal to a sheaf condition. The intersection
of an open with a chart is the `ι`-image of its `ι`-preimage, by
`AlgebraicGeometry.Scheme.Hom.image_preimage_eq_opensRange_inf` and
`AlgebraicGeometry.Scheme.Opens.opensRange_ι`.

No `@[stacks]` attribute is attached. Tag 01NE is withheld for the reason `Glue.lean` records —
it is the representability statement, and the two pullback identities characterizing `φ` are not
proved — and this file is one property of the constructed morphism, not that tag.

## References

* [Stacks Project, Tag 01NE](https://stacks.math.columbia.edu/tag/01NE)
* [Stacks Project, Tag 01NF](https://stacks.math.columbia.edu/tag/01NF)
* [Stacks Project, Tag 0A27](https://stacks.math.columbia.edu/tag/0A27)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry Limits
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace Stacks.ProjectiveSpaceSections

attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme.{u}} (L : X.Modules)
  [SheafOfModules.IsInvertible X.presheaf (structureSheafRing X.toRingedSpace).property L]

section Chart

variable {n : ℕ} (s : Fin (n + 1) → L.sections) (i k : Fin (n + 1))

/-- **The basic open of the ratio `sₖ / sᵢ` on the chart `X_{sᵢ}` is `X_{sₖ} ⊓ X_{sᵢ}`.** The
function `sₖ / sᵢ` is a unit at a point of `X_{sᵢ}` exactly when `sₖ` is nonvanishing there,
because on `X_{sᵢ}` the germ of `sᵢ` generates the stalk of `L`. -/
theorem basicOpen_divBySection :
    X.basicOpen (SheafOfModules.divBySection (X := X.toRingedSpace) L (s i) le_rfl
        ((s k).eval (op (nonvanishingChart L (s i)))))
      = nonvanishingChart L (s k) ⊓ nonvanishingChart L (s i) := by
  have hsec : ∀ t : L.sections,
      SheafOfModules.sectionsOfTop (X := X.toRingedSpace) L (t.eval (op ⊤)) = t :=
    fun t => SheafOfModules.Invertible.sectionsOfTop_eval_top_self (X := X.toRingedSpace) L t
  have h := Scheme.Modules.basicOpen_eq_inf_nonvanishingOpen_of_smul_eq L
    (nonvanishingChart L (s i)) ((s k).eval (op ⊤)) ((s i).eval (op ⊤))
    (by rw [hsec (s i)]; exact le_rfl)
    (SheafOfModules.divBySection (X := X.toRingedSpace) L (s i) le_rfl
      ((s k).eval (op (nonvanishingChart L (s i)))))
    (by
      rw [hsec (s i), hsec (s k)]
      exact SheafOfModules.smul_divBySection (X := X.toRingedSpace) L (s i) le_rfl _)
  rwa [hsec (s k)] at h

/-- The previous statement read as an open of `X`: the `ι`-image of the basic open of
`chartRatio` inside the chart `X_{sᵢ}` is `X_{sₖ} ⊓ X_{sᵢ}`. -/
theorem ι_image_basicOpen_chartRatio :
    (nonvanishingChart L (s i)).ι ''ᵁ
        (nonvanishingChart L (s i)).toScheme.basicOpen (chartRatio L s i k)
      = nonvanishingChart L (s k) ⊓ nonvanishingChart L (s i) :=
  (Scheme.Opens.ι_image_basicOpen_topIso_inv (nonvanishingChart L (s i)) _).trans
    (basicOpen_divBySection L s i k)

end Chart

section Glue

/-- The standard open `D₊(Tᵢ)` of `ℙⁿ`, named for the statements below. -/
noncomputable abbrev standardOpen (n : ℕ) (i : Fin (n + 1)) :
    (projectiveSpaceAtUniverse.{u} n).Opens :=
  Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
    (MvPolynomial.X i)

variable {n : ℕ} (s : Fin (n + 1) → L.sections)
  (hs : (⨆ i, nonvanishingChart L (s i)) = ⊤)

/-- An open of `X` meets the chart `X_{sⱼ}` in the `ι`-image of its `ι`-preimage. -/
private theorem inf_chart_eq (j : Fin (n + 1)) (W : X.Opens) :
    (nonvanishingChart L (s j)).ι ''ᵁ ((nonvanishingChart L (s j)).ι ⁻¹ᵁ W)
      = nonvanishingChart L (s j) ⊓ W := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]

/-- The glued morphism and `X_{sᵢ}` cut out the same open of each chart. -/
private theorem chart_inf_preimage_eq (i j : Fin (n + 1)) :
    nonvanishingChart L (s j) ⊓ (morphismAtUniverse L s hs ⁻¹ᵁ standardOpen.{u} n i)
      = nonvanishingChart L (s j) ⊓ nonvanishingChart L (s i) := by
  rw [← inf_chart_eq L s j, ← Scheme.Hom.comp_preimage, nonvanishingChart_ι_morphismAtUniverse,
    standardOpen, chartMorphism_preimage_basicOpen, ι_image_basicOpen_chartRatio, inf_comm]

/-- **The preimage of the standard open `D₊(Tᵢ)` under the morphism to projective space defined
by a family of generating sections is the nonvanishing locus of `sᵢ`.**

This is the statement the proof of [Stacks, Tag 0A27](https://stacks.math.columbia.edu/tag/0A27)
uses: for `n = 1` and `s₀` a section of `𝒪_X(nx)` vanishing only at `x`, it says that
`φ⁻¹(D₊(T₀)) = X \ {x}`. -/
theorem morphismAtUniverse_preimage_basicOpen (i : Fin (n + 1)) :
    morphismAtUniverse L s hs ⁻¹ᵁ standardOpen.{u} n i = nonvanishingChart L (s i) := by
  calc morphismAtUniverse L s hs ⁻¹ᵁ standardOpen.{u} n i
      = (⨆ j, nonvanishingChart L (s j))
          ⊓ (morphismAtUniverse L s hs ⁻¹ᵁ standardOpen.{u} n i) := by rw [hs, top_inf_eq]
    _ = ⨆ j, nonvanishingChart L (s j)
          ⊓ (morphismAtUniverse L s hs ⁻¹ᵁ standardOpen.{u} n i) := iSup_inf_eq _ _
    _ = ⨆ j, nonvanishingChart L (s j) ⊓ nonvanishingChart L (s i) :=
        iSup_congr fun j => chart_inf_preimage_eq L s hs i j
    _ = (⨆ j, nonvanishingChart L (s j)) ⊓ nonvanishingChart L (s i) := (iSup_inf_eq _ _).symm
    _ = nonvanishingChart L (s i) := by rw [hs, top_inf_eq]

/-- The same identification for the lift of `φ` to relative projective space: the preimage of the
standard open of `ℙⁿ`, pulled back along the projection, is again `X_{sᵢ}`. -/
theorem morphismOver_preimage_basicOpen {S : Scheme.{u}} (f : X ⟶ S) (i : Fin (n + 1)) :
    morphismOver L s hs f ⁻¹ᵁ
        (projectiveSpaceOver.toIntegralAtUniverse n S ⁻¹ᵁ standardOpen.{u} n i)
      = nonvanishingChart L (s i) := by
  rw [← Scheme.Hom.comp_preimage, morphismOver_toIntegralAtUniverse,
    morphismAtUniverse_preimage_basicOpen]

end Glue

end Stacks.ProjectiveSpaceSections

end
