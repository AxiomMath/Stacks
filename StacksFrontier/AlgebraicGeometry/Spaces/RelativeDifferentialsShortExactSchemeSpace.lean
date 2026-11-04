module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDifferentialsShortExact
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsChartMonoReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsSchemeComparisonMap
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The transitivity sequence of a formally smooth morphism, reduced to the scheme-to-space step

For morphisms `f : X ⟶ Y` and `g : Y ⟶ Z` of algebraic spaces with `f` formally smooth, the
transitivity sequence `0 ⟶ f^*Ω_{Y/Z} ⟶ Ω_{X/Z} ⟶ Ω_{X/Y} ⟶ 0` is short exact, granted
`AlgebraicGeometry.Space.PullbackDifferentialsMapSchemeSpaceComparison`: for a composable pair
`ψ : U ⟶ V`, `χ : V ⟶ W` of morphisms of schemes of the site, if the Zariski comparison map
`ψ^*Ω_{V/W} ⟶ Ω_{U/W}` is a monomorphism, so is the comparison map of `ψ` read as a morphism of
represented algebraic spaces.

## Main definitions

* `AlgebraicGeometry.Space.PullbackDifferentialsMapSchemeSpaceComparison`: the scheme-to-space
  step of Stacks 04CS for the first map of the transitivity sequence.

## Main results

* `AlgebraicGeometry.Space.mono_pullbackDifferentialsMap_of_formallySmooth`: the first map of the
  transitivity sequence of a formally smooth morphism is a monomorphism, granted that step.
* `AlgebraicGeometry.Space.triangleDifferentials_shortExact_of_schemeSpaceComparison`: the
  transitivity sequence of a formally smooth morphism is short exact, granted that step.

## References

* [Stacks Project, Tag 06BI](https://stacks.math.columbia.edu/tag/06BI)
* [Stacks Project, Tag 04CS](https://stacks.math.columbia.edu/tag/04CS)
* [Stacks Project, Tag 04CU](https://stacks.math.columbia.edu/tag/04CU)
* [Stacks Project, Tag 04CX](https://stacks.math.columbia.edu/tag/04CX)
* [Stacks Project, Tag 01UV](https://stacks.math.columbia.edu/tag/01UV)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

section ShortExact

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X Y Z : AlgebraicSpaces B S hS}

/-- The scheme-to-space step of Stacks 04CS for the first map of the transitivity sequence: for
every composable pair `ψ : U ⟶ V`, `χ : V ⟶ W` of morphisms of schemes of the site, the comparison
map of Stacks 04CX of `ψ`, read as a morphism of represented algebraic spaces over the represented
algebraic space of `W`, is a monomorphism as soon as the Zariski comparison map
`ψ^*Ω_{V/W} ⟶ Ω_{U/W}` of Stacks 01UV of the schemes is. -/
abbrev PullbackDifferentialsMapSchemeSpaceComparison : Prop :=
  ∀ (U V W : BigFppfOver B S hS) (ψ : U ⟶ V) (χ : V ⟶ W),
    Mono (schemeChartDifferentialsMap B S hS ψ χ) →
    Mono (pullbackDifferentialsMap B S hS (schemeSpaceMap ψ) (schemeSpaceMap χ))

/-- For morphisms `f : X ⟶ Y` and `g : Y ⟶ Z` of algebraic spaces with `f` formally smooth, the
first map `f^*Ω_{Y/Z} ⟶ Ω_{X/Z}` of the transitivity sequence is a monomorphism, granted
`AlgebraicGeometry.Space.PullbackDifferentialsMapSchemeSpaceComparison`. -/
theorem mono_pullbackDifferentialsMap_of_formallySmooth (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : FormallySmooth f.hom)
    (hchart : PullbackDifferentialsMapSchemeSpaceComparison B S hS) :
    Mono (pullbackDifferentialsMap B S hS f g) := by
  obtain ⟨U, V, W, a, b, c, ψ, χ, haEtale, hbEtale, hcEtale, haSurj, hsqψ, hsqχ⟩ :=
    exists_etale_chart_diagram B S hS f g
  have hψ : Stacks.Smooth.FormallySmoothAffineLocally
      ((BigFppfOver.toScheme B S hS).map ψ) :=
    holdsOnEveryEtaleChart_formallySmoothAffineLocally hf U V a b ψ haEtale hbEtale hsqψ
  have hscheme := Scheme.Hom.relativeDifferentialsMap_mono_of_formallySmoothAffineLocally
    ((BigFppfOver.toScheme B S hS).map ψ) ((BigFppfOver.toScheme B S hS).map χ) hψ
  refine mono_of_mono_modulePullback_chart B S hS f g U a haEtale haSurj ?_
  refine (mono_map_pullbackDifferentialsMap_iff_of_etaleChart B S hS f g
    (ObjectProperty.homMk a : schemeSpace U ⟶ X)
    (ObjectProperty.homMk b : schemeSpace V ⟶ Y) (schemeSpaceMap ψ)
    (isEtale_of_presheaf_etale B S hS haEtale) (isEtale_of_presheaf_etale B S hS hbEtale)
    (ObjectProperty.hom_ext _ hsqψ)).mpr ?_
  rw [← (ObjectProperty.hom_ext _ hsqχ : schemeSpaceMap χ ≫
    (ObjectProperty.homMk c : schemeSpace W ⟶ Z) =
    (ObjectProperty.homMk b : schemeSpace V ⟶ Y) ≫ g)]
  exact mono_pullbackDifferentialsMap_of_etaleBase B S hS (schemeSpaceMap ψ)
    (schemeSpaceMap χ) (ObjectProperty.homMk c : schemeSpace W ⟶ Z)
    (isEtale_of_presheaf_etale B S hS hcEtale) (hchart U V W ψ χ hscheme)

/-- For morphisms `f : X ⟶ Y` and `g : Y ⟶ Z` of algebraic spaces with `f` formally smooth, the
transitivity sequence `0 ⟶ f^*Ω_{Y/Z} ⟶ Ω_{X/Z} ⟶ Ω_{X/Y} ⟶ 0` of Stacks 05Z8 is short exact,
granted `AlgebraicGeometry.Space.PullbackDifferentialsMapSchemeSpaceComparison`. -/
@[sga "6 VIII 5.2" "partial"]
theorem triangleDifferentials_shortExact_of_schemeSpaceComparison (f : X ⟶ Y)
    (g : Y ⟶ Z) (hf : FormallySmooth f.hom)
    (hchart : PullbackDifferentialsMapSchemeSpaceComparison B S hS) :
    ∃ h : pullbackDifferentialsMap B S hS f g ≫ toRelativeDifferentials B S hS f g = 0,
      (ShortComplex.mk _ _ h).ShortExact :=
  triangleDifferentials_shortExact_of_mono B S hS f g
    (mono_pullbackDifferentialsMap_of_formallySmooth B S hS f g hf hchart)

end ShortExact

end AlgebraicGeometry.Space

end
