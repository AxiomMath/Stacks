module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartGradedDivision

/-!
# Clause (2) of Stacks Tag 01NK on a chart

Let `A = ⨁_{n ≥ 0} 𝒜 n` be a graded ring, `T` a scheme, `L` an invertible `𝒪_T`-module and
`ψ : A → Γ_*(T, L)` a graded map. For `f ∈ 𝒜 d` homogeneous and `V` an open on which `ψ(f)` does
not vanish, `Stacks.AlgebraicGeometry.ProjChartGradedDivision.chartSection` is the map

  `θ_f : (A_f)_n ⟶ Γ(L ^⊗ n, V)`,   `x / f ^ j ↦ ψ(x) / ψ(f ^ j)`.

This file shows that `θ_f(x / 1) = ψ(x)|_V` for `x ∈ 𝒜 n`, that `θ_f(x / f ^ j)` is the unique
section of `L ^⊗ n` over `V` whose product with `ψ(f ^ j)` is `ψ(x)|_V`, and that `θ_f` commutes
with restriction to a smaller open.

## Main results

* `Stacks.AlgebraicGeometry.ProjChartGradedClauseTwo.chartSection_mk_one`: `θ_f(x / 1) = ψ(x)|_V`
  for `x` homogeneous of degree `n`.
* `Stacks.AlgebraicGeometry.ProjChartGradedClauseTwo.existsUnique_mul_chartSection`:
  `θ_f(x / f ^ j)` is the unique section of `L ^⊗ n` over `V` whose product with `ψ(f ^ j)` is
  `ψ(x)|_V`.
* `Stacks.AlgebraicGeometry.ProjChartGradedClauseTwo.map_chartSection`: `θ_f` commutes with
  restriction to a smaller open.

## References

* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj (integerGrading)
open Stacks.AlgebraicGeometry.ProjChartFromRatios (secOf)
open Stacks.AlgebraicGeometry.ProjChartFullGraded (GradedSections)
open Stacks.AlgebraicGeometry.ProjChartGradedDivision (chartSection chartSectionOf chartSection_mk
  divTop_toFun_congr exists_rep)
open Stacks.AlgebraicGeometry.ProjVeroneseRestrict (mem_graded_of_eq)
open Stacks.GradedLocalization (gradedPiece)
open Stacks.GradedSections (mulMap)
open Stacks.MorphismToProj (HomogeneousRatios)
open Stacks.NonvanishingOpen (nonvanishingOpen)
open Stacks.TensorPowerDivision (divTop_mulSections mul_divTop divOf_eq_of_mul_eq map_divTop)
open Stacks.TensorPowerTrivialize (resTop)
open Stacks.TensorPowers (natTensorPow)
open scoped Stacks.GradedLocalization

universe u w

namespace Stacks.AlgebraicGeometry.ProjChartGradedClauseTwo

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜] {T : Scheme.{u}} {L : T.Modules}
  [Stacks.Ample.IsInvertibleModule T L] (ψ : GradedSections 𝒜 L)
  {d : ℕ} {f : A} {V : T.Opens} (hf : f ∈ 𝒜 d)
  (hV : V ≤ nonvanishingOpen T (natTensorPow L d) (ψ.toFun d ⟨f, hf⟩))

/-! ### The commuting square of clause (2) -/

/-- The value `ψ(f x) / ψ(f)` of `chartSectionOf` on the representative `f x / f ^ 1` is the
restriction of `ψ(x)` to `V`. -/
theorem chartSectionOf_den_one (n : ℕ) {x : A} (hx : x ∈ 𝒜 n)
    (hfx : f * x ∈ 𝒜 (1 * d + n)) :
    chartSectionOf ψ hf hV n 1 hfx
      = resTop (natTensorPow L n) (ψ.toFun n ⟨x, hx⟩) V := by
  have hfx' : f * x ∈ 𝒜 (d + n) := SetLike.mul_mem_graded hf hx
  rw [chartSectionOf, (divTop_toFun_congr ψ hf (HomogeneousRatios.pow_mem hf 1) n hfx' hfx hV
      (ψ.le_nonvanishingOpen_pow hf hV 1) (one_mul d).symm (pow_one f).symm rfl).symm,
    ψ.map_mul d n ⟨f, hf⟩ ⟨x, hx⟩ ⟨f * x, hfx'⟩ rfl, divTop_mulSections]

/-- For `x` homogeneous of degree `n`, the map `θ_f` carries the fraction `x / 1` of
`A_f`-degree `n` to the restriction of `ψ(x)` to `V`. -/
theorem chartSection_mk_one (n : ℕ) {x : A} (hx : x ∈ 𝒜 n)
    (y : gradedPiece 𝒜 (integerGrading (S := A) 𝒜) f (n : ℤ))
    (hrep : (y : LocalizedModule.Away f A)
      = LocalizedModule.mk x (1 : Submonoid.powers f)) :
    chartSection ψ hf hV n y = resTop (natTensorPow L n) (ψ.toFun n ⟨x, hx⟩) V := by
  have hfx : f * x ∈ 𝒜 (1 * d + n) :=
    mem_graded_of_eq 𝒜 (by ring) (SetLike.mul_mem_graded hf hx)
  have hrep' : (y : LocalizedModule.Away f A)
      = LocalizedModule.mk (f * x) (⟨f ^ 1, ⟨1, rfl⟩⟩ : Submonoid.powers f) :=
    hrep.trans (LocalizedModule.mk_eq.2 ⟨1, by simp [Submonoid.smul_def, smul_eq_mul]⟩)
  rw [chartSection_mk ψ hf hV n y 1 (f * x) hfx hrep', chartSectionOf_den_one ψ hf hV n hx hfx]

/-! ### The identity that pins the comparison down -/

/-- The product of `θ_f(x / f ^ j)` with `ψ(f ^ j)` is the restriction of `ψ(x)` to `V`. -/
theorem mul_chartSection (n j : ℕ) {x : A} (hx : x ∈ 𝒜 (j * d + n))
    (y : gradedPiece 𝒜 (integerGrading (S := A) 𝒜) f (n : ℤ))
    (hrep : (y : LocalizedModule.Away f A)
      = LocalizedModule.mk x (⟨f ^ j, ⟨j, rfl⟩⟩ : Submonoid.powers f)) :
    (mulMap (secOf L (ψ.toFun (j * d) ⟨f ^ j, HomogeneousRatios.pow_mem hf j⟩)) n).app V
        (chartSection ψ hf hV n y)
      = resTop (natTensorPow L (j * d + n)) (ψ.toFun (j * d + n) ⟨x, hx⟩) V := by
  rw [chartSection_mk ψ hf hV n y j x hx hrep, chartSectionOf]
  exact mul_divTop L _ (ψ.le_nonvanishingOpen_pow hf hV j) n _

/-- A section of `L ^⊗ n` over `V` whose product with `ψ(f ^ j)` is the restriction of `ψ(x)` is
`θ_f(x / f ^ j)`. -/
theorem eq_chartSection_of_mul_eq (n j : ℕ) {x : A} (hx : x ∈ 𝒜 (j * d + n))
    (y : gradedPiece 𝒜 (integerGrading (S := A) 𝒜) f (n : ℤ))
    (hrep : (y : LocalizedModule.Away f A)
      = LocalizedModule.mk x (⟨f ^ j, ⟨j, rfl⟩⟩ : Submonoid.powers f))
    {s : Γ(natTensorPow L n, V)}
    (h : (mulMap (secOf L (ψ.toFun (j * d) ⟨f ^ j, HomogeneousRatios.pow_mem hf j⟩)) n).app V s
      = resTop (natTensorPow L (j * d + n)) (ψ.toFun (j * d + n) ⟨x, hx⟩) V) :
    s = chartSection ψ hf hV n y := by
  rw [chartSection_mk ψ hf hV n y j x hx hrep, chartSectionOf]
  exact (divOf_eq_of_mul_eq L _ (ψ.le_nonvanishingOpen_pow hf hV j) n le_rfl h).symm

include hV in
/-- `θ_f(x / f ^ j)` is the unique section of `L ^⊗ n` over `V` whose product with `ψ(f ^ j)` is
`ψ(x)|_V`. -/
theorem existsUnique_mul_chartSection (n j : ℕ) {x : A} (hx : x ∈ 𝒜 (j * d + n))
    (y : gradedPiece 𝒜 (integerGrading (S := A) 𝒜) f (n : ℤ))
    (hrep : (y : LocalizedModule.Away f A)
      = LocalizedModule.mk x (⟨f ^ j, ⟨j, rfl⟩⟩ : Submonoid.powers f)) :
    ∃! s : Γ(natTensorPow L n, V),
      (mulMap (secOf L (ψ.toFun (j * d) ⟨f ^ j, HomogeneousRatios.pow_mem hf j⟩)) n).app V s
        = resTop (natTensorPow L (j * d + n)) (ψ.toFun (j * d + n) ⟨x, hx⟩) V :=
  ⟨chartSection ψ hf hV n y, mul_chartSection ψ hf hV n j hx y hrep,
    fun _ hs => eq_chartSection_of_mul_eq ψ hf hV n j hx y hrep hs⟩

/-! ### Restriction to a smaller open -/

/-- The map `θ_f` commutes with restriction to a smaller open `V' ≤ V`. -/
theorem map_chartSection (n : ℕ) (y : gradedPiece 𝒜 (integerGrading (S := A) 𝒜) f (n : ℤ))
    {V' : T.Opens} (i : V' ⟶ V) :
    (natTensorPow L n).presheaf.map i.op (chartSection ψ hf hV n y)
      = chartSection ψ hf (i.le.trans hV) n y := by
  obtain ⟨j, x, hx, hy⟩ := exists_rep n y hf
  rw [chartSection_mk ψ hf hV n y j x hx hy,
    chartSection_mk ψ hf (i.le.trans hV) n y j x hx hy, chartSectionOf, chartSectionOf,
    map_divTop]
  rfl

end Stacks.AlgebraicGeometry.ProjChartGradedClauseTwo

end
