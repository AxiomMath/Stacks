module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.AffineScaleRepresentation
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ChartClassifyingTransport

/-!
# The chart-wise morphism of a transition `F_d → F_{a d}`

Let `S` be a scheme, `𝒜` a quasi-coherent graded `𝒪_S`-algebra (Situation 01NN), `U` an affine
open of the base and `d, a ≥ 1`. For a point of `F_d(T)` for the restriction `𝒜|_U`,
`...RelativeProjQcohSheaf.Fd.chartHom` attaches a morphism `T ⟶ X` into a relative homogeneous
spectrum of `𝒜`. This file proves that the transition `...RelativeProjQcohSheaf.Fd.scale` to
the degree `a d` does not change it.

## Implementation notes

The statement is `...RelativeProjQcohSheaf.Quadruple.toProj_classifyingHomOfClass_scale` over
the affine base `U` for `𝒜|_U`, transported along the identification
`...RelativeProjQcohSheaf.restrict_ι_proj` of the two projective spectra, which does not depend
on the degree.

## Main results

* `...RelativeProjQcohSheaf.Fd.toProj_chartEquiv_scale` and
  `...RelativeProjQcohSheaf.Fd.chartHom_scale`: the transition to the degree `a d` classifies
  the same chart-wise morphism.

## References

* [Stacks Project, Tag 01NU](https://stacks.math.columbia.edu/tag/01NU)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01NY](https://stacks.math.columbia.edu/tag/01NY)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.Proj (degreeOpen)
open Stacks.AlgebraicGeometry.MorphismsIntoProj (toProj)
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S) (U : S.Opens)

/-- The transition `F_d → F_{a d}` classifies the same chart-wise morphism into
`Proj 𝒜(U)`. -/
theorem Fd.toProj_chartEquiv_scale (hU : IsAffineOpen U) {k a : ℕ} (hk : 0 < k) (ha : 0 < a)
    (T : Scheme.{u}) (ξ : Fd (situationAlgebra (A.restrict U.ι)) (k : ℤ) T) :
    toProj (A.grading U) (Fd.chartEquiv A U hU (Nat.mul_pos ha hk) T
        (Fd.scale (show (0 : ℤ) < (a : ℤ) by exact_mod_cast ha) ξ))
      = toProj (A.grading U) (Fd.chartEquiv A U hU hk T ξ) := by
  have : IsAffine U.toScheme := hU
  have hqc : ∀ n : ℤ, ((situationAlgebra (A.restrict U.ι)).piece n).IsQuasicoherent :=
    fun n => (A.restrict U.ι).isQuasicoherent n
  -- the chart-wise morphism read into `Proj 𝒜(U)`, for an arbitrary degree
  have key : ∀ (m : ℕ) (hm : 0 < m) (η : Fd (situationAlgebra (A.restrict U.ι)) (m : ℤ) T),
      toProj (A.grading U) (Fd.chartEquiv A U hU hm T η)
        = toProj ((A.restrict U.ι).grading (⊤ : U.toScheme.Opens))
            (Quadruple.classifyingHomOfClass hm hqc η.2)
          ≫ eqToHom (restrict_ι_proj A U) := by
    intro m hm η
    show (Quadruple.classifyingHomOfClass hm hqc η.2
        ≫ eqToHom (SheafGradedAlgebra.restrict_ι_degreeOpen_toScheme A U m))
        ≫ (degreeOpen (A.grading U) m).ι = _
    rw [Category.assoc, eqToHom_comp_ι (restrict_ι_proj A U)
      (restrict_ι_degreeOpen_heq A U m)
      (SheafGradedAlgebra.restrict_ι_degreeOpen_toScheme A U m)]
    exact (Category.assoc _ _ _).symm
  rw [key _ (Nat.mul_pos ha hk) _, key _ hk ξ]
  exact congrArg (fun z => z ≫ eqToHom (restrict_ι_proj A U))
    (Quadruple.toProj_classifyingHomOfClass_scale (B := A.restrict U.ι) hk ha hqc T ξ)

/-- The transition `F_d → F_{a d}` does not change the chart-wise morphism into a relative
homogeneous spectrum. -/
theorem Fd.chartHom_scale (P : RelativeProjData A) (hU : IsAffineOpen U) {k a : ℕ}
    (hk : 0 < k) (ha : 0 < a) (T : Scheme.{u})
    (ξ : Fd (situationAlgebra (A.restrict U.ι)) (k : ℤ) T) :
    Fd.chartHom A U P hU (Nat.mul_pos ha hk) T
        (Fd.scale (show (0 : ℤ) < (a : ℤ) by exact_mod_cast ha) ξ)
      = Fd.chartHom A U P hU hk T ξ := by
  rw [Fd.chartHom_eq_comp A U P hU (Nat.mul_pos ha hk) T, Fd.chartHom_eq_comp A U P hU hk T]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z => z ≫ P.chart U hU) (Fd.toProj_chartEquiv_scale A U hU hk ha T ξ)).trans
      (Category.assoc _ _ _))

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
