module

public import StacksFrontier.Examples.Spaces.CurveFamilyNotScheme.Instance.CentralFibre
public import StacksFrontier.Examples.Spaces.CurveFamilyNotScheme.Blowup.StrictTransformConormal
public import StacksFrontier.AlgebraicGeometry.Surfaces.NegativeCurveFormalNeighborhoodConormalPowers
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.GeometricGenusNormalizationBound
public import StacksFrontier.AlgebraicGeometry.Stacks.WeierstrassFamilyFibres
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertSchemeOfCurve
public import StacksFrontier.AlgebraicGeometry.CurveLocalRing.ClosedPointDivisor

/-!
# The formal neighbourhood of the strict transform of the central fibre

In the construction of [Stacks, Tag 0D5E], `π : Z ⟶ Y` is the blowup of the cubic surface
`Y : T₀ ^ 3 + T₁ ^ 3 + T₂ ^ 3 - t T₀ T₁ T₂ = 0` at the chosen closed point `y` of the central
fibre `Y₀`, and `C ⊆ Z` is the strict transform of `Y₀`. This file instantiates the general
results on the blowup of a regular surface at a point of a regular curve
(`StacksFrontier/Examples/Spaces/CurveFamilyNotScheme/Blowup/`) for this `Y`, and concludes:

* `C` is an effective Cartier divisor on `Z`, isomorphic to `Y₀`, hence to the Fermat cubic;
  with the `k`-structure transported from the Fermat cubic it is proper and smooth of relative
  dimension one over `k`, with `H⁰(C, 𝒪_C) = k` and genus one;
* `C` meets the exceptional divisor in one `k`-point `p`, and the conormal sheaf of `C` is
  `𝒪_C(p)`;
* hence the ring `A^ = lim_n Γ(C_n, 𝒪)` of the formal neighbourhood of `C` is a complete
  Noetherian local domain of dimension two
  (`AlgebraicGeometry.Scheme.IdealSheafData.formalNeighborhoodRing_of_genusOne_of_iso`).

## Main definitions

* `Stacks.Examples.CurveFamilyNotScheme.cubicBlowup`: `Z`, the blowup of `Y` at `y`.
* `Stacks.Examples.CurveFamilyNotScheme.strictTransformCentralFibre`: the ideal sheaf of `C`.
* `Stacks.Examples.CurveFamilyNotScheme.strictTransformIsoFermat`: `C ≅` the Fermat cubic.

## Main results

* `Stacks.Examples.CurveFamilyNotScheme.formalNeighborhoodRing_strictTransformCentralFibre`:
  `A^` is a complete Noetherian local domain of Krull dimension two.

## References

* [Stacks Project, Tag 0D5E](https://stacks.math.columbia.edu/tag/0D5E)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry IsLocalRing TopologicalSpace
open Stacks.Divisors (IsEffectiveCartierDivisor)

universe u

namespace Stacks.Examples.CurveFamilyNotScheme

variable (k : Type u) [Field k]

/-! ### The Fermat cubic over `k` -/

/-- `H⁰(E, 𝒪_E)` of the Fermat cubic is one-dimensional. -/
theorem finrank_structureSheafCohomology_zero_fermatCurveToSpec :
    Module.finrank k (structureSheafCohomology (fermatCurveToSpec k) 0) = 1 := by
  have : IsProper (fermatModelToSpec k) := by
    rw [← fermatModelIso_inv_toSpec]
    infer_instance
  rw [← fermatModelIso_hom_toSpec,
    ModuliEllipticCurves.Weierstrass.finrank_structureSheafCohomology_iso_comp k
      (fermatModelToSpec k) (fermatModelIso k) 0]
  exact finrank_structureSheafCohomology_zero_fermatModelToSpec k

/-- The Fermat cubic is smooth of relative dimension one over `k`. -/
theorem smoothOfRelativeDimension_fermatCurveToSpec [IsAlgClosed k] (h3 : ringChar k ≠ 3) :
    SmoothOfRelativeDimension 1 (fermatCurveToSpec k) :=
  have := isCurve_fermatCurveToSpec k h3
  have := smooth_fermatCurveToSpec k h3
  Stacks.Hilbert.smoothOfRelativeDimension_one_of_isCurve _

/-! ### The blowup and the strict transform -/

variable [IsAlgClosed k] [Uncountable k] (h3 : ringChar k ≠ 3)

/-- The blowup `Z` of the cubic surface at the chosen point. -/
abbrev cubicBlowup : Scheme.{u} := pointBlowup (chosenPoint k h3) (isClosed_chosenPoint k h3)

/-- The ideal sheaf of the strict transform `C ⊆ Z` of the central fibre. -/
abbrev strictTransformCentralFibre : (cubicBlowup k h3).IdealSheafData :=
  strictTransformIdeal (chosenPoint k h3) (isClosed_chosenPoint k h3) (centralFibreIdeal k)

/-- **The strict transform of the central fibre is an effective Cartier divisor.** -/
instance isEffectiveCartierDivisor_strictTransformCentralFibre :
    IsEffectiveCartierDivisor (strictTransformCentralFibre k h3) :=
  have := isIntegral_subscheme_centralFibreIdeal k h3
  isEffectiveCartierDivisor_strictTransformIdeal _ _ (isRegular_cubicSurface k h3)
    (topologicalKrullDim_cubicSurface k h3)
    (ringKrullDim_stalk_cubicSurface k h3 _ (isClosed_chosenPoint k h3))
    (isEffectiveCartierDivisor_centralFibreIdeal k) (isRegular_subscheme_centralFibreIdeal k h3)
    (chosenPoint_mem_support_centralFibreIdeal k h3)

/-- **The strict transform maps isomorphically onto the central fibre.** -/
instance isIso_strictTransformToFibre_centralFibre :
    IsIso (strictTransformToFibre (chosenPoint k h3) (isClosed_chosenPoint k h3)
      (centralFibreIdeal k)) :=
  have := isIntegral_subscheme_centralFibreIdeal k h3
  isIso_strictTransformToFibre _ _ (topologicalKrullDim_cubicSurface k h3)
    (ringKrullDim_stalk_cubicSurface k h3 _ (isClosed_chosenPoint k h3))
    (isEffectiveCartierDivisor_centralFibreIdeal k) (isRegular_subscheme_centralFibreIdeal k h3)
    (chosenPoint_mem_support_centralFibreIdeal k h3)

/-- **The strict transform `C` of the central fibre is the Fermat cubic**, through
`C ≅ Y₀ ≅ E`. -/
def strictTransformIsoFermat : (strictTransformCentralFibre k h3).subscheme ≅ fermatCurve k :=
  asIso (strictTransformToFibre (chosenPoint k h3) (isClosed_chosenPoint k h3)
    (centralFibreIdeal k)) ≪≫ (centralFibreIso k).symm

/-- The structure of a scheme over `k` on `C`, transported from the Fermat cubic. -/
instance overSpecStrictTransformCentralFibre :
    (strictTransformCentralFibre k h3).subscheme.Over (Spec (.of k)) :=
  ⟨(strictTransformIsoFermat k h3).hom ≫ fermatCurveToSpec k⟩

/-- The structure morphism of `C` is that of the Fermat cubic, through `C ≅ E`. -/
theorem strictTransformCentralFibre_over :
    ((strictTransformCentralFibre k h3).subscheme ↘ Spec (.of k)) =
      (strictTransformIsoFermat k h3).hom ≫ fermatCurveToSpec k :=
  rfl

/-- `C` is proper over `k`. -/
instance isProper_strictTransformCentralFibre :
    IsProper ((strictTransformCentralFibre k h3).subscheme ↘ Spec (.of k)) := by
  rw [strictTransformCentralFibre_over]
  infer_instance

/-- `C` is smooth of relative dimension one over `k`. -/
instance smoothOfRelativeDimension_strictTransformCentralFibre :
    SmoothOfRelativeDimension 1 ((strictTransformCentralFibre k h3).subscheme ↘ Spec (.of k)) := by
  have := smoothOfRelativeDimension_fermatCurveToSpec k h3
  rw [strictTransformCentralFibre_over]
  exact inferInstanceAs (SmoothOfRelativeDimension (0 + 1) _)

/-- **`H⁰(C, 𝒪_C) = k`.** -/
theorem finrank_structureSheafCohomology_zero_strictTransformCentralFibre :
    Module.finrank k
      (structureSheafCohomology ((strictTransformCentralFibre k h3).subscheme ↘ Spec (.of k)) 0) =
      1 := by
  rw [strictTransformCentralFibre_over,
    ModuliEllipticCurves.Weierstrass.finrank_structureSheafCohomology_iso_comp k
      (fermatCurveToSpec k) (strictTransformIsoFermat k h3) 0]
  exact finrank_structureSheafCohomology_zero_fermatCurveToSpec k

/-- **`C` has genus one.** -/
theorem genus_strictTransformCentralFibre :
    genus ((strictTransformCentralFibre k h3).subscheme ↘ Spec (.of k)) = 1 := by
  rw [strictTransformCentralFibre_over, genus_comp_iso_eq k (fermatCurveToSpec k)]
  exact genus_fermatCurveToSpec k h3

/-- **`C` meets the exceptional divisor in a `k`-point `p`, and the conormal sheaf of `C` is
`𝒪_C(p)`.** -/
theorem exists_section_conormal_iso :
    ∃ (p : Spec (.of k) ⟶ (strictTransformCentralFibre k h3).subscheme)
      (hp : p ≫ ((strictTransformCentralFibre k h3).subscheme ↘ Spec (.of k)) = 𝟙 _),
      pointBlowupToBase (chosenPoint k h3) (isClosed_chosenPoint k h3)
          ((strictTransformCentralFibre k h3).subschemeι (GenusOne.point p)) = chosenPoint k h3 ∧
        Nonempty ((Scheme.Modules.pullback (strictTransformCentralFibre k h3).subschemeι).obj
          (Stacks.Divisors.negativeTwist (strictTransformCentralFibre k h3)) ≅
            GenusOne.pointDivisorSheaf p hp 1) := by
  have := isIntegral_subscheme_centralFibreIdeal k h3
  obtain ⟨p₀, hp₀, hover, -, -, -, hψ⟩ := exists_strictTransform_inter_exceptional _ _
    (isRegular_cubicSurface k h3) (topologicalKrullDim_cubicSurface k h3)
    (ringKrullDim_stalk_cubicSurface k h3 _ (isClosed_chosenPoint k h3))
    (isEffectiveCartierDivisor_centralFibreIdeal k) (isRegular_subscheme_centralFibreIdeal k h3)
    (chosenPoint_mem_support_centralFibreIdeal k h3) (cubicSurfaceCoordinate k) rfl
    (Γgerm_cubicSurfaceCoordinate_chosenPoint_notMem_sq k h3)
  obtain ⟨p, hp, hpt⟩ : ∃ p : Spec (.of k) ⟶ (strictTransformCentralFibre k h3).subscheme,
      p ≫ ((strictTransformCentralFibre k h3).subscheme ↘ Spec (.of k)) = 𝟙 _ ∧
        GenusOne.point p = p₀ :=
    ⟨pointOfClosedPoint _ p₀ hp₀, pointOfClosedPoint_comp _ p₀ hp₀,
      pointOfClosedPoint_apply _ p₀ hp₀ _⟩
  subst hpt
  refine ⟨p, hp, hover, ?_⟩
  have h0 := hψ 0
  rw [zero_add, pow_one (strictTransformCentralFibre k h3)] at h0
  exact h0

/-- **The formal neighbourhood of the strict transform of the central fibre**: the ring
`A^ = lim_n Γ(C_n, 𝒪)` is a complete Noetherian local domain of Krull dimension two. This is the
ring of the formal algebraic space `W` that the construction of [Stacks, Tag 0D5E] contracts
`C` to. -/
theorem formalNeighborhoodRing_strictTransformCentralFibre :
    IsNoetherianCompleteLocalRing (strictTransformCentralFibre k h3).formalNeighborhoodRing ∧
      ringKrullDim (strictTransformCentralFibre k h3).formalNeighborhoodRing = 2 ∧
      IsDomain (strictTransformCentralFibre k h3).formalNeighborhoodRing := by
  obtain ⟨p, hp, -, ⟨ψ⟩⟩ := exists_section_conormal_iso k h3
  have := isCurve_fermatCurveToSpec k h3
  have : IsCurve k ((strictTransformCentralFibre k h3).subscheme ↘ Spec (.of k)) :=
    GenusOne.isCurve _ (finrank_structureSheafCohomology_zero_strictTransformCentralFibre k h3)
  have : Smooth ((strictTransformCentralFibre k h3).subscheme ↘ Spec (.of k)) :=
    SmoothOfRelativeDimension.smooth 1 ((strictTransformCentralFibre k h3).subscheme ↘ Spec (.of k))
  have : IsEffectiveCartierDivisor (Scheme.IdealSheafData.vanishingIdeal
      (⟨{GenusOne.point p}, GenusOne.isClosed_point _ p hp⟩ :
        Closeds (strictTransformCentralFibre k h3).subscheme) ^ 1) := by
    rw [pow_one]
    have hcl : (⟨{GenusOne.point p}, GenusOne.isClosed_point _ p hp⟩ :
        Closeds (strictTransformCentralFibre k h3).subscheme) =
        Closeds.closure {GenusOne.point p} :=
      Closeds.ext (GenusOne.isClosed_point _ p hp).closure_eq.symm
    rw [hcl]
    exact IsCurve.isEffectiveCartierDivisor_vanishingIdeal_closure_singleton k
      ((strictTransformCentralFibre k h3).subscheme ↘ Spec (.of k)) (GenusOne.isClosed_point _ p hp)
  exact Scheme.IdealSheafData.formalNeighborhoodRing_of_genusOne_of_iso
    (finrank_structureSheafCohomology_zero_strictTransformCentralFibre k h3)
    (genus_strictTransformCentralFibre k h3) p hp ψ

end Stacks.Examples.CurveFamilyNotScheme

end
