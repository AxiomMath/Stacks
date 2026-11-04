/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuotOverSpace.AffineFramedReduction
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuotOverSpace.AffineFramedRepresentability

/-!
# `Quot^P` of a module of finite presentation on `B × ℙⁿ_ℤ` is proper over `B`

Let `B` be an algebraic space, `X = B × ℙⁿ_ℤ`, `𝓛` the pullback of `𝒪(1)` to `X` and `F` an
`𝒪_X`-module of finite presentation.  For a numerical polynomial `P`, the algebraic space
`Quot^P_{F/X/B}` of quotients of `F` with Hilbert polynomial `P` with respect to `𝓛` is proper
over `B` (Stacks 0DPB).

## Main results

* `isProperAlgebraicSpaceOver_hilbertPolynomialQuot_productSpace`: `Quot^P_{F/X/B}` is proper
  over `B`.

## References

* [Stacks Project, Tag 0DPB](https://stacks.math.columbia.edu/tag/0DPB)
-/

@[expose] public noncomputable section

open CategoryTheory

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace AlgebraicGeometry.ProjectiveQuotOverSpace

universe u

variable {B : BigFppfSite.{u}} (n : ℕ)

/-- Let `Y` be an algebraic space, `X = Y × ℙⁿ_ℤ`, `𝓛` the pullback of `𝒪_{ℙⁿ}(1)` to `X` and `F`
an `𝒪_X`-module of finite presentation.  For a numerical polynomial `P : ℤ → ℤ` (the function of a
rational polynomial `p`), the algebraic space `Quot^P_{F/X/Y}` parametrizing quotients of `F`
having Hilbert polynomial `P` with respect to `𝓛` is proper over `Y`. -/
@[stacks 0DPB]
theorem isProperAlgebraicSpaceOver_hilbertPolynomialQuot_productSpace
    (Y : AlgebraicSpaces B integerBase B.contains_integerBase)
    (F : Space.Modules.{u, u} B integerBase B.contains_integerBase (productSpace n Y).1
      (productSpace n Y).2) (hF : SheafOfModules.IsFinitePresentationOnSite F)
    {P : ℤ → ℤ} {p : Polynomial ℚ} (hP : ∀ m : ℤ, p.eval (m : ℚ) = (P m : ℚ)) :
    (situation n Y F (@SheafOfModules.isQuasicoherentOnSite_of_isFinitePresentationOnSite
        _ _ _ _ F hF)).IsProperAlgebraicSpaceOver
      ((situation n Y F (@SheafOfModules.isQuasicoherentOnSite_of_isFinitePresentationOnSite
          _ _ _ _ F hF)).hilbertPolynomialQuot
        (twistingModule (situationFrame n Y F
          (@SheafOfModules.isQuasicoherentOnSite_of_isFinitePresentationOnSite _ _ _ _ F hF)))
        (hL := isInvertible_twistingModule (situationFrame n Y F
          (@SheafOfModules.isQuasicoherentOnSite_of_isFinitePresentationOnSite _ _ _ _ F hF))) P) :=
  isProperAlgebraicSpaceOver_hilbertPolynomialQuot_twistingModule_of_affine
    (fun D' E' _ φ _ hft =>
      isRepresentedProper_hilbertPolynomialQuot_twistingModule_of_affine D' E' φ hft hP)
    _ _ (@SheafOfModules.isFiniteTypeOnSite_of_isFinitePresentationOnSite _ _ _ _ F hF)

end AlgebraicGeometry.ProjectiveQuotOverSpace

end
