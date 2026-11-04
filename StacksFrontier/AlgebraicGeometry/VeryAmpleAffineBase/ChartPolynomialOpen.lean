module

public import StacksFrontier.AlgebraicGeometry.AmpleImmersionReduction.Charts
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The standard open of a homogeneous polynomial, pulled back to a chart

The coordinate cut of [Stacks, Tag 02NP] compares two covers of `X`: the charts
`α⁻¹(D₊(y_i f_j))` of the immersion into `Proj A`, and the standard opens of `ℙⁿ_S` cut out by
homogeneous polynomials `T_i F_j` in the chosen coordinates. The comparison it needs is an
*equality of opens of `X`*: the inverse image along the pinned morphism `p : X ⟶ ℙⁿ_S` of the
standard open of a homogeneous polynomial.

`Stacks.AmpleImmersionReduction.preimage_standardChart` is this statement for the *variables*,
`p⁻¹(D₊(T_i)) = X_{s_i}`. This file is the same statement for an arbitrary homogeneous polynomial
of positive degree: the hypothesis on `p` is the pinning of
`Stacks.ProjGlobalSectionsAppTop.exists_hom_projectiveSpaceOver_of_generatesStalks`, so on the
chart `X_{s_i}` the morphism *is* the one attached to the ratio family `s_k / s_i`, and Mathlib's
`AlgebraicGeometry.Proj.fromOfGlobalSections_preimage_basicOpen` computes the inverse image of
`D₊(F)` along that as the nonvanishing locus of the polynomial evaluated at the ratios.

## Main results

* `Stacks.SectionsToProjectiveSpace.preimage_basicOpen_homogeneous`: for the morphism attached to
  a spanning family of sections of `𝒪_X`, the inverse image of `D₊(F)` is the nonvanishing locus
  of `F` evaluated at the family. This is
  `Stacks.SectionsToProjectiveSpace.preimage_basicOpen` with the variable replaced by any
  homogeneous element of positive degree.
* `Stacks.ChartPolynomialOpen.preimage_basicOpen_chart`: the same for a pinned morphism to
  `ℙⁿ_S`, read inside the chart `X_{s_i}`.
* `Stacks.ChartPolynomialOpen.preimage_basicOpen_eq_basicOpen`: **the equality of opens of `X`.**
  For `F` homogeneous of positive degree whose standard open lies inside `D₊(T_i)`, the inverse
  image along `p` of the standard open of `F` is the nonvanishing locus in `X` of `F` evaluated
  at the coordinate ratios `s_k / s_i`.

## Implementation notes

The containment `D₊(F) ≤ D₊(T_i)` is what removes the chart from the statement: without it the
inverse image is only computed in intersection with `X_{s_i}`. In the application `F = T_i F_j`
and the containment is `Stacks.OverlapChart.basicOpen_mul_le_left`, so it costs nothing — the
same observation that lets the coordinate cut refine its charts by multiplying by the
coordinate.

Everything is phrased with inverse images. The one image that occurs,
`(nvCover s i).ι ''ᵁ _`, is taken along the *inclusion* of the chart and never along a morphism
that is rewritten, so no `IsOpenImmersion` instance argument has to move.

The polynomial has **integer** coefficients: the opens here are pulled back from the integral
model `ℙⁿ_ℤ`. That is the right generality for a cut by a monomial in the coordinates, and it is
*not* enough for a cut by an element whose expansion in the coordinates has coefficients in the
degree-zero part of the graded ring — such an element cuts a standard open of `ℙⁿ_S` that is not
the inverse image of one of `ℙⁿ_ℤ`, and its treatment goes through the section `t` of the affine
chart `D₊(T_i) ⊓ pr⁻¹(V)` instead, by
`Stacks.OverlapSurjectivity.preimage_basicOpen_eq`.

## References

* [Stacks Project, Tag 02NP](https://stacks.math.columbia.edu/tag/02NP)
* [Stacks Project, Tag 01NE](https://stacks.math.columbia.edu/tag/01NE)
* [Stacks Project, Tag 01VS](https://stacks.math.columbia.edu/tag/01VS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Ample Stacks.ProjectiveFromSections

universe u

namespace Stacks.SectionsToProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme.{u}} {n : ℕ} (s : Fin (n + 1) → Γ(X, ⊤))
  (hs : Ideal.span (Set.range s) = ⊤)

/-- **The inverse image of the standard open of a homogeneous polynomial** along the morphism
attached to a family of global sections of `𝒪_X` spanning the unit ideal: it is the nonvanishing
locus of the polynomial evaluated at the family.

This is `Stacks.SectionsToProjectiveSpace.preimage_basicOpen` with the variable `T_i` replaced by
an arbitrary homogeneous element of positive degree; both are
`AlgebraicGeometry.Proj.fromOfGlobalSections_preimage_basicOpen`. -/
@[ega "II 3.7.3" "(f), special case"]
theorem preimage_basicOpen_homogeneous {D : ℕ} (hD : 0 < D) {F : coordRing.{u} n}
    (hF : F ∈ coordGrading.{u} n D) :
    toProjectiveSpaceAtUniverse s hs ⁻¹ᵁ Proj.basicOpen (coordGrading.{u} n) F =
      X.basicOpen (sectionsHom s F) :=
  Proj.fromOfGlobalSections_preimage_basicOpen (coordGrading.{u} n) (sectionsHom s)
    (map_irrelevant_eq_top s hs) hD hF

end Stacks.SectionsToProjectiveSpace

namespace Stacks.ChartPolynomialOpen

attribute [local instance] MvPolynomial.gradedAlgebra

open Stacks.SectionsToProjectiveSpace

variable {X : Scheme.{u}} {L : X.Modules} [Stacks.Ample.IsInvertibleModule X L] {n : ℕ}
  {S : Scheme.{u}}

/-- **The inverse image of the standard open of a homogeneous polynomial, read inside the chart
`X_{s_i}`.** The pinning hypothesis says that on `X_{s_i}` the morphism to `ℙⁿ_S` is the one
attached to the ratio family `s_k / s_i`, and
`Stacks.SectionsToProjectiveSpace.preimage_basicOpen_homogeneous` computes the inverse image
there. -/
theorem preimage_basicOpen_chart (s : Fin (n + 1) → Γ(L, ⊤)) (p : X ⟶ projectiveSpaceOver n S)
    (hchart : ∀ k, (nvCover s k).ι ≫ p ≫ projectiveSpaceOver.toIntegralAtUniverse n S =
      toProjectiveSpaceAtUniverse (chartRatio s k) (span_range_chartRatio s k))
    (i : Fin (n + 1)) {D : ℕ} (hD : 0 < D) {F : coordRing.{u} n}
    (hF : F ∈ coordGrading.{u} n D) :
    (nvCover s i).ι ⁻¹ᵁ (p ⁻¹ᵁ (projectiveSpaceOver.toIntegralAtUniverse n S ⁻¹ᵁ
          Proj.basicOpen (coordGrading.{u} n) F)) =
      (nvCover s i).toScheme.basicOpen (sectionsHom (chartRatio s i) F) := by
  have hc : (nvCover s i).ι ⁻¹ᵁ (p ⁻¹ᵁ (projectiveSpaceOver.toIntegralAtUniverse n S ⁻¹ᵁ
        Proj.basicOpen (coordGrading.{u} n) F)) =
      ((nvCover s i).ι ≫ p ≫ projectiveSpaceOver.toIntegralAtUniverse n S) ⁻¹ᵁ
        Proj.basicOpen (coordGrading.{u} n) F := rfl
  rw [hc, hchart i]
  exact preimage_basicOpen_homogeneous (chartRatio s i) (span_range_chartRatio s i) hD hF

/-- **The equality of opens of `X` the coordinate cut of [Stacks, Tag 02NP] needs.** For `F`
homogeneous of positive degree whose standard open lies inside `D₊(T_i)`, the inverse image along
a pinned morphism `p : X ⟶ ℙⁿ_S` of the standard open of `F` is the nonvanishing locus in `X` of
`F` evaluated at the coordinate ratios `s_k / s_i`.

The containment `D₊(F) ≤ D₊(T_i)` puts the inverse image inside the chart `X_{s_i}`, by
`Stacks.AmpleImmersionReduction.preimage_standardChart`, so taking the image of
`Stacks.ChartPolynomialOpen.preimage_basicOpen_chart` along the inclusion of the chart loses
nothing. -/
theorem preimage_basicOpen_eq_basicOpen (s : Fin (n + 1) → Γ(L, ⊤)) (hgen : GeneratesStalks s)
    (p : X ⟶ projectiveSpaceOver n S)
    (hchart : ∀ k, (nvCover s k).ι ≫ p ≫ projectiveSpaceOver.toIntegralAtUniverse n S =
      toProjectiveSpaceAtUniverse (chartRatio s k) (span_range_chartRatio s k))
    (i : Fin (n + 1)) {D : ℕ} (hD : 0 < D) {F : coordRing.{u} n}
    (hF : F ∈ coordGrading.{u} n D)
    (hFi : Proj.basicOpen (coordGrading.{u} n) F ≤
      Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i)) :
    p ⁻¹ᵁ (projectiveSpaceOver.toIntegralAtUniverse n S ⁻¹ᵁ
        Proj.basicOpen (coordGrading.{u} n) F) =
      X.basicOpen ((nvCover s i).topIso.hom (sectionsHom (chartRatio s i) F)) := by
  set Z : X.Opens := p ⁻¹ᵁ (projectiveSpaceOver.toIntegralAtUniverse n S ⁻¹ᵁ
    Proj.basicOpen (coordGrading.{u} n) F) with hZ
  -- The inverse image lies inside the chart, because `D₊(F)` lies inside `D₊(T_i)`.
  have hZle : Z ≤ nvCover s i := by
    rw [← Stacks.AmpleImmersionReduction.preimage_standardChart s hgen p hchart i, hZ]
    exact fun x hx => hFi hx
  -- Taking the image of the chart-local computation along the inclusion of the chart.
  have himg := congrArg (fun W => (nvCover s i).ι ''ᵁ W)
    (preimage_basicOpen_chart s p hchart i hD hF)
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
    show (nvCover s i).toScheme.basicOpen (sectionsHom (chartRatio s i) F) =
      (nvCover s i).toScheme.basicOpen ((nvCover s i).topIso.inv
        ((nvCover s i).topIso.hom (sectionsHom (chartRatio s i) F))) by
      rw [← ConcreteCategory.comp_apply, (nvCover s i).topIso.hom_inv_id,
        ConcreteCategory.id_apply],
    Scheme.Opens.ι_image_basicOpen_topIso_inv] at himg
  rw [← himg, inf_eq_right.mpr hZle]

end Stacks.ChartPolynomialOpen

end
