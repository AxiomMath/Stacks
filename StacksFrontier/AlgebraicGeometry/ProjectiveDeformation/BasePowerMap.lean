module

public import StacksFrontier.AlgebraicGeometry.ProjectiveDeformation.FunctorialityProj
public import StacksFrontier.AlgebraicGeometry.ProjectiveDeformation.TwistCanonical
public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.ClauseThreeMorphism

/-!
# The datum of [Stacks, Tag 01O8] of `g' ≫ r'₂` for a morphism of deformations

For a morphism `φ : D₁ ⟶ D₂` of admissible deformations over `g : S'₁ ⟶ S'₂`, with total part
`g' : X'₁ ⟶ X'₂`, pulling the sections of `𝒜'(D₂) ⊆ ⨁_d (f'₂)_*(ℒ'₂)^{⊗ d}` back along `g'` and
reading them in `(ℒ'₁)^{⊗ d}` through `g'^* ℒ'₂ ≅ ℒ'₁` gives a datum
`ψ : (f'₁ ≫ g)^* 𝒜'(D₂) ⟶ ⨁_d (ℒ'₁)^{⊗ d}` of [Stacks, Tag 01O8] on `X'₁` over `S'₂`
(`basePowerMap`). It generates everywhere and its morphism `r_{ℒ'₁, ψ}` of [Stacks, Tag 01O9] is
`g' ≫ r'₂`: over every affine open of `S'₂` its datum of [Stacks, Tag 01NK] is the inverse image of
that of `r'₂`.

## Main definitions

* `…AdmissibleDeformation.basePowerMap`.

## Main results

* `…AdmissibleDeformation.coveringOpen_basePowerMap`, `…globalMorphism_basePowerMap`.

## References

* [Stacks Project, Tag 0D4F](https://stacks.math.columbia.edu/tag/0D4F)
* [Stacks Project, Tag 01O8](https://stacks.math.columbia.edu/tag/01O8)
* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism
open Stacks.AmpleProjectiveImmersion (tensorPowerModule)
open Stacks.TensorPowers (natTensorPow)
open Stacks.AlgebraicGeometry.ProjChartGradedRingFunctoriality (comap)

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveDeformation

namespace PolarizedFamily.AdmissibleDeformation

-- `CategoryTheory.catToReflQuiver` offers a second route from `Category` to `Quiver`; see
-- `Stacks.AlgebraicGeometry.ProjectiveDeformation.TwistSections`.
attribute [-instance] CategoryTheory.catToReflQuiver

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {P : PolarizedFamily.{u}} {D₁ D₂ : P.AdmissibleDeformation} (φ : Hom D₁ D₂) (d₀ : ℕ)
  (hd₀ : 0 < d₀)

/-- The open `(f'₁ ≫ g)^{-1}(V)` lies in `g'^{-1}(f'₂^{-1}(V))`. -/
theorem preimage_comp_le_preimage_total (V : D₂.S'.Opens) :
    (D₁.f' ≫ φ.base) ⁻¹ᵁ V ≤ φ.total ⁻¹ᵁ (D₂.f' ⁻¹ᵁ V) :=
  Stacks.AlgebraicGeometry.SectionRingBaseChange.preimage_le_preimage φ.total D₂.f' D₁.f'
    φ.base φ.isPullback.w V (φ.base ⁻¹ᵁ V) le_rfl

/-- The degree-`n` component of the datum: the comparison of `D₂` followed by the inverse image
along `g'`. -/
def basePowerPiece (n : ℕ) :
    (D₂.truncatedSectionAlgebra d₀ hd₀).piece (n : ℤ) ⟶
      (Scheme.Modules.pushforward (D₁.f' ≫ φ.base)).obj (natTensorPow D₁.L' n) :=
  haveI := D₁.finitePresentation.quasiCompact
  haveI := D₁.finitePresentation.quasiSeparated
  haveI := D₂.finitePresentation.quasiCompact
  haveI := D₂.finitePresentation.quasiSeparated
  (D₂.sectionAlgebraComparison d₀ hd₀).app (n : ℤ) ≫
    Stacks.AlgebraicGeometry.SectionRingBaseChange.pushPieceMap φ.total D₂.f' D₁.f' φ.base
      φ.isPullback.w D₂.L' D₁.L' φ.polarization (n : ℤ) ≫
    (Scheme.Modules.pushforwardComp D₁.f' φ.base).inv.app _ ≫
    (Scheme.Modules.pushforward (D₁.f' ≫ φ.base)).map
      (Stacks.AlgebraicGeometry.CoherentMulSections.powCompare D₁.L' n).inv

/-- A section `a` of `𝒜'_n(D₂)` over `V` goes under `basePowerPiece` to the inverse image along
`g'` of the corresponding section of `(ℒ'₂)^{⊗ n}`, read in `(ℒ'₁)^{⊗ n}`. -/
theorem basePowerPiece_app (n : ℕ) (V : D₂.S'.Opens)
    (a : Γ((D₂.truncatedSectionAlgebra d₀ hd₀).piece (n : ℤ), V)) :
    (basePowerPiece φ d₀ hd₀ n).app V a =
      (Stacks.AlgebraicGeometry.CoherentMulSections.powCompare D₁.L' n).inv.app
        ((D₁.f' ≫ φ.base) ⁻¹ᵁ V)
        (Stacks.AlgebraicGeometry.SectionRingBaseChange.sectionPull φ.total D₂.L' D₁.L'
          φ.polarization (n : ℤ) (D₂.f' ⁻¹ᵁ V) ((D₁.f' ≫ φ.base) ⁻¹ᵁ V)
          (preimage_comp_le_preimage_total φ V)
          (show Γ(tensorPowerModule D₂.X' D₂.L' n, D₂.f' ⁻¹ᵁ V) from
            ((D₂.sectionAlgebraComparison d₀ hd₀).app (n : ℤ)).app V a)) := by
  have := D₁.finitePresentation.quasiCompact
  have := D₁.finitePresentation.quasiSeparated
  have := D₂.finitePresentation.quasiCompact
  have := D₂.finitePresentation.quasiSeparated
  have e := Stacks.AlgebraicGeometry.SectionRingBaseChange.pushPieceMap_app φ.total D₂.f' D₁.f'
    φ.base φ.isPullback.w D₂.L' D₁.L' φ.polarization (n : ℤ) V
    (((D₂.sectionAlgebraComparison d₀ hd₀).app (n : ℤ)).app V a)
  exact congrArg (fun z => (Stacks.AlgebraicGeometry.CoherentMulSections.powCompare D₁.L' n).inv.app
    ((D₁.f' ≫ φ.base) ⁻¹ᵁ V) z) e

/-- **The datum of [Stacks, Tag 01O8] of `g' ≫ r'₂`**: a section `a` of `𝒜'_n(D₂)` over `V` goes to
the inverse image along `g'` of the section `a` of `(ℒ'₂)^{⊗ n}` over `f'₂^{-1}(V)`, read in
`(ℒ'₁)^{⊗ n}` over `(f'₁ ≫ g)^{-1}(V)`. -/
def basePowerMap : GradedPowerMap (D₂.truncatedSectionAlgebra d₀ hd₀) (D₁.f' ≫ φ.base) where
  L := D₁.L'
  invertible := inferInstance
  ψ n := basePowerPiece φ d₀ hd₀ n
  map_mul n m V a b := by
    have e1 := basePowerPiece_app φ d₀ hd₀ (n + m) V
      (((D₂.truncatedSectionAlgebra d₀ hd₀).mul (n : ℤ) (m : ℤ)).app V a b)
    have e2 := basePowerPiece_app φ d₀ hd₀ n V a
    have e3 := basePowerPiece_app φ d₀ hd₀ m V b
    have hc := (D₂.sectionAlgebraComparison d₀ hd₀).app_mul (n : ℤ) (m : ℤ) V a b
    have hs := Stacks.AlgebraicGeometry.SectionRingBaseChange.sectionPull_mul φ.total D₂.L' D₁.L'
      φ.polarization (n : ℤ) (m : ℤ) (D₂.f' ⁻¹ᵁ V) ((D₁.f' ≫ φ.base) ⁻¹ᵁ V)
      (preimage_comp_le_preimage_total φ V)
      (((D₂.sectionAlgebraComparison d₀ hd₀).app (n : ℤ)).app V a)
      (((D₂.sectionAlgebraComparison d₀ hd₀).app (m : ℤ)).app V b)
    have k2 := Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul.hom_app_inv_app
      (Stacks.AlgebraicGeometry.CoherentMulSections.powCompare D₁.L' n) ((D₁.f' ≫ φ.base) ⁻¹ᵁ V)
      (Stacks.AlgebraicGeometry.SectionRingBaseChange.sectionPull φ.total D₂.L' D₁.L'
          φ.polarization (n : ℤ) (D₂.f' ⁻¹ᵁ V) ((D₁.f' ≫ φ.base) ⁻¹ᵁ V)
          (preimage_comp_le_preimage_total φ V)
          (((D₂.sectionAlgebraComparison d₀ hd₀).app (n : ℤ)).app V a))
    have k3 := Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul.hom_app_inv_app
      (Stacks.AlgebraicGeometry.CoherentMulSections.powCompare D₁.L' m) ((D₁.f' ≫ φ.base) ⁻¹ᵁ V)
      (Stacks.AlgebraicGeometry.SectionRingBaseChange.sectionPull φ.total D₂.L' D₁.L'
          φ.polarization (m : ℤ) (D₂.f' ⁻¹ᵁ V) ((D₁.f' ≫ φ.base) ⁻¹ᵁ V)
          (preimage_comp_le_preimage_total φ V)
          (((D₂.sectionAlgebraComparison d₀ hd₀).app (m : ℤ)).app V b))
    change (basePowerPiece φ d₀ hd₀ (n + m)).app V _ =
      (Stacks.AlgebraicGeometry.CoherentMulSections.powCompare D₁.L' (n + m)).inv.app
        ((D₁.f' ≫ φ.base) ⁻¹ᵁ V) (Stacks.TensorPowerDivision.localMul D₁.L'
          ((Stacks.AlgebraicGeometry.CoherentMulSections.powCompare D₁.L' n).hom.app _
            ((basePowerPiece φ d₀ hd₀ n).app V a))
          ((Stacks.AlgebraicGeometry.CoherentMulSections.powCompare D₁.L' m).hom.app _
            ((basePowerPiece φ d₀ hd₀ m).app V b)))
    rw [e1, e2, e3, k2, k3]
    exact congrArg (fun z => (Stacks.AlgebraicGeometry.CoherentMulSections.powCompare D₁.L'
      (n + m)).inv.app ((D₁.f' ≫ φ.base) ⁻¹ᵁ V) z)
      ((congrArg (Stacks.AlgebraicGeometry.SectionRingBaseChange.sectionPull φ.total D₂.L' D₁.L'
        φ.polarization ((n : ℤ) + (m : ℤ)) (D₂.f' ⁻¹ᵁ V) ((D₁.f' ≫ φ.base) ⁻¹ᵁ V)
        (preimage_comp_le_preimage_total φ V)) hc).trans hs)

/-- The invertible module of `basePowerMap` is `ℒ'₁`. -/
theorem basePowerMap_L : (basePowerMap φ d₀ hd₀).L = D₁.L' := rfl

/-- The value of `basePowerMap` on a section `a` of `𝒜'_n(D₂)` over `V`: the inverse image
along `g'` of the corresponding section of `(ℒ'₂)^{⊗ n}`, read in `(ℒ'₁)^{⊗ n}`. -/
theorem basePowerMap_value (n : ℕ) (V : D₂.S'.Opens)
    (a : Γ((D₂.truncatedSectionAlgebra d₀ hd₀).piece (n : ℤ), V)) :
    (basePowerMap φ d₀ hd₀).value n V a =
      (Stacks.AlgebraicGeometry.CoherentMulSections.powCompare D₁.L' n).inv.app
        ((D₁.f' ≫ φ.base) ⁻¹ᵁ V)
        (Stacks.AlgebraicGeometry.SectionRingBaseChange.sectionPull φ.total D₂.L' D₁.L'
          φ.polarization (n : ℤ) (D₂.f' ⁻¹ᵁ V) ((D₁.f' ≫ φ.base) ⁻¹ᵁ V)
          (preimage_comp_le_preimage_total φ V)
          (show Γ(tensorPowerModule D₂.X' D₂.L' n, D₂.f' ⁻¹ᵁ V) from
            ((D₂.sectionAlgebraComparison d₀ hd₀).app (n : ℤ)).app V a)) :=
  basePowerPiece_app φ d₀ hd₀ n V a

/-- **Over an open `V` of `S'₂`, the datum of [Stacks, Tag 01NK] of `basePowerMap` is the inverse
image along `g'` of that of `r'₂`**, in positive degrees, up to the comparisons of the tensor
powers. -/
theorem basePowerMap_affineDatum_degreewiseIso (V : D₂.S'.Opens) (n : ℕ) (_ : 0 < n)
    (a : (D₂.truncatedSectionAlgebra d₀ hd₀).grading V n) :
    (Stacks.AlgebraicGeometry.SectionRingBaseChange.restrictPowSectionIso φ.total D₂.L' D₁.L'
        φ.polarization ((D₁.f' ≫ φ.base) ⁻¹ᵁ V) n).hom.app ⊤
        (((basePowerMap φ d₀ hd₀).affineDatum V).toFun n a) =
      (Stacks.AlgebraicGeometry.SectionRingBaseChange.pullbackRestrictIso φ.total D₂.L'
        (D₂.f' ⁻¹ᵁ V) ((D₁.f' ≫ φ.base) ⁻¹ᵁ V) (preimage_comp_le_preimage_total φ V) n).hom.app ⊤
        (pullbackSectionHom (φ.total.resLE (D₂.f' ⁻¹ᵁ V) ((D₁.f' ≫ φ.base) ⁻¹ᵁ V)
            (preimage_comp_le_preimage_total φ V))
          (Stacks.TensorPowers.natTensorPow ((Scheme.Modules.pullback (D₂.f' ⁻¹ᵁ V).ι).obj D₂.L') n)
          ⊤ ⊤ (Stacks.AlgebraicGeometry.ProjChartRatioPullback.top_le_preimage_top _)
          ((D₂.chartDatum d₀ hd₀ V).toFun n a)) := by
  let y := (D₂.truncatedSectionAlgebra d₀ hd₀).componentEquiv V n a
  let c₂ := D₂.sectionAlgebraComparison d₀ hd₀
  have hΞ : ((basePowerMap φ d₀ hd₀).affineDatum V).toFun n a =
      Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul.restrictPowSection D₁.L'
        ((D₁.f' ≫ φ.base) ⁻¹ᵁ V) n
        ((Stacks.AlgebraicGeometry.CoherentMulSections.powCompare D₁.L' n).inv.app
          ((D₁.f' ≫ φ.base) ⁻¹ᵁ V)
          (Stacks.AlgebraicGeometry.SectionRingBaseChange.sectionPull φ.total D₂.L' D₁.L'
            φ.polarization (n : ℤ) (D₂.f' ⁻¹ᵁ V) ((D₁.f' ≫ φ.base) ⁻¹ᵁ V)
            (preimage_comp_le_preimage_total φ V) ((c₂.app (n : ℤ)).app V y))) :=
    congrArg (Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul.restrictPowSection D₁.L'
      ((D₁.f' ≫ φ.base) ⁻¹ᵁ V) n) (basePowerMap_value φ d₀ hd₀ n V y)
  have k5 := componentEquiv_sectionHom c₂ V n a
  have hψ : (D₂.chartDatum d₀ hd₀ V).toFun n a =
      Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul.restrictPowSection D₂.L'
        (D₂.f' ⁻¹ᵁ V) n ((Stacks.AlgebraicGeometry.CoherentMulSections.powCompare D₂.L' n).inv.app
          (D₂.f' ⁻¹ᵁ V) ((c₂.app (n : ℤ)).app V y)) :=
    congrArg (fun t => Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul.restrictPowSection
      D₂.L' (D₂.f' ⁻¹ᵁ V) n
      ((Stacks.AlgebraicGeometry.CoherentMulSections.powCompare D₂.L' n).inv.app
        (D₂.f' ⁻¹ᵁ V) t)) k5
  refine (congrArg (fun t => (Stacks.AlgebraicGeometry.SectionRingBaseChange.restrictPowSectionIso
    φ.total D₂.L' D₁.L' φ.polarization ((D₁.f' ≫ φ.base) ⁻¹ᵁ V) n).hom.app ⊤ t) hΞ).trans ?_
  refine (Stacks.AlgebraicGeometry.SectionRingBaseChange.restrictPowSectionIso_sectionPull
    φ.total D₂.L' D₁.L' φ.polarization (D₂.f' ⁻¹ᵁ V) ((D₁.f' ≫ φ.base) ⁻¹ᵁ V)
    (preimage_comp_le_preimage_total φ V) n ((c₂.app (n : ℤ)).app V y)).trans ?_
  refine Eq.trans ?_ (congrArg (fun t =>
    (Stacks.AlgebraicGeometry.SectionRingBaseChange.pullbackRestrictIso φ.total D₂.L'
      (D₂.f' ⁻¹ᵁ V) ((D₁.f' ≫ φ.base) ⁻¹ᵁ V) (preimage_comp_le_preimage_total φ V) n).hom.app ⊤
      (pullbackSectionHom (φ.total.resLE (D₂.f' ⁻¹ᵁ V) ((D₁.f' ≫ φ.base) ⁻¹ᵁ V)
          (preimage_comp_le_preimage_total φ V))
        (Stacks.TensorPowers.natTensorPow ((Scheme.Modules.pullback (D₂.f' ⁻¹ᵁ V).ι).obj D₂.L') n)
        ⊤ ⊤ (Stacks.AlgebraicGeometry.ProjChartRatioPullback.top_le_preimage_top _) t)) hψ).symm
  exact (Stacks.AlgebraicGeometry.SectionRingBaseChange.pullbackRestrictIso_pullbackSection
    φ.total D₂.L' (D₂.f' ⁻¹ᵁ V) ((D₁.f' ≫ φ.base) ⁻¹ᵁ V) (preimage_comp_le_preimage_total φ V) n
    ((c₂.app (n : ℤ)).app V y)).symm

/-- The covering open of the datum over `V` is the inverse image of that of `r'₂`. -/
theorem coveringOpen_basePowerMap_affineDatum (V : D₂.S'.Opens) :
    ((basePowerMap φ d₀ hd₀).affineDatum V).coveringOpen =
      φ.total.resLE (D₂.f' ⁻¹ᵁ V) ((D₁.f' ≫ φ.base) ⁻¹ᵁ V) (preimage_comp_le_preimage_total φ V) ⁻¹ᵁ
        (D₂.chartDatum d₀ hd₀ V).coveringOpen :=
  ProjChartFullGraded.GradedSections.coveringOpen_eq_preimage_of_degreewiseIsoVia
    _ (D₂.chartDatum d₀ hd₀ V) ((basePowerMap φ d₀ hd₀).affineDatum V) _
    (fun n => Stacks.AlgebraicGeometry.SectionRingBaseChange.restrictPowSectionIso
      φ.total D₂.L' D₁.L' φ.polarization ((D₁.f' ≫ φ.base) ⁻¹ᵁ V) n)
    (fun n => Stacks.AlgebraicGeometry.SectionRingBaseChange.pullbackRestrictIso φ.total D₂.L'
      (D₂.f' ⁻¹ᵁ V) ((D₁.f' ≫ φ.base) ⁻¹ᵁ V) (preimage_comp_le_preimage_total φ V) n)
    (basePowerMap_affineDatum_degreewiseIso φ d₀ hd₀ V)

/-- **`basePowerMap` generates everywhere**: `U(ψ) = X'₁`. -/
theorem coveringOpen_basePowerMap : (basePowerMap φ d₀ hd₀).coveringOpen = ⊤ := by
  refine eq_top_iff.mpr fun x _ => ?_
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset
    (Opens.mem_top ((D₁.f' ≫ φ.base).base x))
  have e := (basePowerMap φ d₀ hd₀).image_coveringOpen_affineDatum_eq hV
  rw [coveringOpen_basePowerMap_affineDatum, D₂.coveringOpen_chartDatum d₀ hd₀ hV,
    Scheme.Hom.preimage_top, Scheme.Opens.ι_image_top] at e
  have hx : x ∈ (D₁.f' ≫ φ.base) ⁻¹ᵁ V := hxV
  rw [e] at hx
  exact hx.1


/-- **The morphism `r_{ℒ'₁, ψ}` of [Stacks, Tag 01O9] of `basePowerMap` is `g' ≫ r'₂`.** -/
theorem globalMorphism_basePowerMap :
    (basePowerMap φ d₀ hd₀).coveringOpen.ι ≫ φ.total ≫ D₂.canonicalProjHom d₀ hd₀ =
      (basePowerMap φ d₀ hd₀).globalMorphism
        (relativeProj (D₂.truncatedSectionAlgebra d₀ hd₀)) := by
  refine (basePowerMap φ d₀ hd₀).eq_globalMorphism_of_clauseThree _ fun V => ?_
  obtain ⟨V, hV⟩ := V
  let Q := basePowerMap φ d₀ hd₀
  let Ξ := Q.affineDatum V
  let ψ₂ := D₂.chartDatum d₀ hd₀ V
  have hV' := preimage_comp_le_preimage_total φ V
  let J := φ.total.resLE (D₂.f' ⁻¹ᵁ V) ((D₁.f' ≫ φ.base) ⁻¹ᵁ V) hV'
  have hcov₂ : ψ₂.coveringOpen = ⊤ := D₂.coveringOpen_chartDatum d₀ hd₀ hV
  obtain ⟨e₂, he₂⟩ : ∃ e₂ : (D₂.f' ⁻¹ᵁ V).toScheme ⟶ ψ₂.coveringOpen.toScheme,
      e₂ ≫ ψ₂.coveringOpen.ι = 𝟙 _ :=
    ⟨(D₂.f' ⁻¹ᵁ V).toScheme.topIso.inv ≫ ((D₂.f' ⁻¹ᵁ V).toScheme.isoOfEq hcov₂.symm).hom,
      by simp only [Category.assoc, Scheme.isoOfEq_hom_ι, Scheme.toIso_inv_ι]⟩
  have hpre := coveringOpen_basePowerMap_affineDatum φ d₀ hd₀ V
  have hglue := ProjChartFullGraded.GradedSections.resLE_glued_of_degreewiseIsoVia
    J ψ₂ Ξ _ (fun n => Stacks.AlgebraicGeometry.SectionRingBaseChange.restrictPowSectionIso
      φ.total D₂.L' D₁.L' φ.polarization ((D₁.f' ≫ φ.base) ⁻¹ᵁ V) n)
    (fun n => Stacks.AlgebraicGeometry.SectionRingBaseChange.pullbackRestrictIso φ.total D₂.L'
      (D₂.f' ⁻¹ᵁ V) ((D₁.f' ≫ φ.base) ⁻¹ᵁ V) hV' n)
    (basePowerMap_affineDatum_degreewiseIso φ d₀ hd₀ V)
  calc Q.affineDatumInclusion ⟨V, hV⟩ ≫ Q.coveringOpen.ι ≫ φ.total ≫ D₂.canonicalProjHom d₀ hd₀
      = (Q.affineDatumInclusion ⟨V, hV⟩ ≫ Q.coveringOpen.ι) ≫ φ.total ≫
          D₂.canonicalProjHom d₀ hd₀ := (Category.assoc _ _ _).symm
    _ = (Ξ.coveringOpen.ι ≫ ((D₁.f' ≫ φ.base) ⁻¹ᵁ V).ι) ≫ φ.total ≫
          D₂.canonicalProjHom d₀ hd₀ := by rw [Q.affineDatumInclusion_ι ⟨V, hV⟩]
    _ = Ξ.coveringOpen.ι ≫ (((D₁.f' ≫ φ.base) ⁻¹ᵁ V).ι ≫ φ.total) ≫
          D₂.canonicalProjHom d₀ hd₀ := by simp only [Category.assoc]
    _ = Ξ.coveringOpen.ι ≫ (J ≫ (D₂.f' ⁻¹ᵁ V).ι) ≫ D₂.canonicalProjHom d₀ hd₀ := by
          rw [← Scheme.Hom.resLE_comp_ι φ.total hV']
    _ = Ξ.coveringOpen.ι ≫ J ≫ ((D₂.f' ⁻¹ᵁ V).ι ≫ D₂.canonicalProjHom d₀ hd₀) := by
          simp only [Category.assoc]
    _ = Ξ.coveringOpen.ι ≫ J ≫ (e₂ ≫ ψ₂.glued ≫
          (relativeProj (D₂.truncatedSectionAlgebra d₀ hd₀)).chart V hV) := by
          rw [D₂.ι_canonicalProjHom d₀ hd₀ hV e₂ he₂]
    _ = (Ξ.coveringOpen.ι ≫ J ≫ e₂) ≫ ψ₂.glued ≫
          (relativeProj (D₂.truncatedSectionAlgebra d₀ hd₀)).chart V hV := by
          simp only [Category.assoc]
    _ = J.resLE ψ₂.coveringOpen Ξ.coveringOpen hpre.le ≫ ψ₂.glued ≫
          (relativeProj (D₂.truncatedSectionAlgebra d₀ hd₀)).chart V hV := by
          congr 1
          rw [← cancel_mono ψ₂.coveringOpen.ι, Category.assoc, Category.assoc, he₂,
            Category.comp_id, Scheme.Hom.resLE_comp_ι]
    _ = (J.resLE ψ₂.coveringOpen Ξ.coveringOpen hpre.le ≫ ψ₂.glued) ≫
          (relativeProj (D₂.truncatedSectionAlgebra d₀ hd₀)).chart V hV :=
          (Category.assoc _ _ _).symm
    _ = Ξ.glued ≫ (relativeProj (D₂.truncatedSectionAlgebra d₀ hd₀)).chart V hV := by
          rw [hglue]


end PolarizedFamily.AdmissibleDeformation

end Stacks.AlgebraicGeometry.ProjectiveDeformation

end
