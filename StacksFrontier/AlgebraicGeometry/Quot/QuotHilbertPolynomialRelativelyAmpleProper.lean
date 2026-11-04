/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Quot.QuotHilbertPolynomialAmpleEmbedding
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuotOverSpace.AffineFramedRepresentability

/-!
# Properness of `Quot^P` for a relatively ample invertible module (Stacks 0DPC)

Let `f : X ⟶ B` be a proper morphism of finite presentation of algebraic spaces, `F` a finitely
presented `𝒪_X`-module, `L` an invertible `𝒪_X`-module ample on `X/B` (Stacks 0D31) and `P` a
numerical polynomial.  The algebraic space `Quot^P_{F/X/B}` of quotients of `F` with Hilbert
polynomial `P` with respect to `L` is proper over `B`.

The proof is that of the Stacks project.  The question is étale local over `B` (Stacks 083R), so
`B` may be taken affine; then `X` embeds into `ℙⁿ_B` by a closed immersion `i` with
`i^*𝒪(1) ≅ L^{⊗ d}` (Stacks 01VS); replacing `(L, P(t))` by `(L^{⊗ d}, P(dt))` (Stacks 0DP8) and
transporting along `i` (Stacks 0DP4), `Quot^P_{F/X/B}` becomes `Quot^{P(d·)}_{i_*F/ℙⁿ_B/B}`, which
is proper over `B` by Stacks 0DPB.  The reduction is
`QuotSituation.isProperAlgebraicSpaceOver_hilbertPolynomialQuot_of_isRelativelyAmple_of_projective`
and the affine case of Stacks 0DPB is
`ProjectiveQuotOverSpace.isRepresentedProper_hilbertPolynomialQuot_twistingModule_of_affine`.

## Main results

* `QuotSituation.isProperAlgebraicSpaceOver_hilbertPolynomialQuot_of_isRelativelyAmple`:
  **Stacks 0DPC.**

## References

* [Stacks Project, Tag 0DPC](https://stacks.math.columbia.edu/tag/0DPC)
* [Stacks Project, Tag 0DPB](https://stacks.math.columbia.edu/tag/0DPB)
* [Stacks Project, Tag 0D31](https://stacks.math.columbia.edu/tag/0D31)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.Space.QuotSituation

open ProjectiveQuot ProjectiveQuotOverSpace

variable {B : BigFppfSite.{u}}

/-- **Stacks 0DPC.**  Let `f : X ⟶ B` be a proper morphism of finite presentation of algebraic
spaces (over `Spec ℤ`), `F` a finitely presented `𝒪_X`-module, `L` an invertible `𝒪_X`-module
ample on `X/B` (Stacks 0D31) and `P` a numerical polynomial.  Then the algebraic space
`Quot^P_{F/X/B}` parametrizing quotients of `F` having Hilbert polynomial `P` with respect to `L`
is proper over `B`. -/
@[stacks 0DPC]
theorem isProperAlgebraicSpaceOver_hilbertPolynomialQuot_of_isRelativelyAmple
    (D : QuotSituation B integerBase B.contains_integerBase)
    (hf : IsProper B integerBase B.contains_integerBase D.f.hom)
    (hF : SheafOfModules.IsFinitePresentationOnSite D.F)
    (L : Modules.{u, u} B integerBase B.contains_integerBase D.X.1 D.X.2)
    [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B integerBase
      B.contains_integerBase D.X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B integerBase B.contains_integerBase D.X.1 D.X.2).O)).property L]
    (hamp : IsRelativelyAmple B integerBase B.contains_integerBase D.f L)
    {P : ℤ → ℤ} {p : Polynomial ℚ} (hP : ∀ m : ℤ, p.eval (m : ℚ) = (P m : ℚ)) :
    D.IsProperAlgebraicSpaceOver (D.hilbertPolynomialQuot L P) :=
  isProperAlgebraicSpaceOver_hilbertPolynomialQuot_of_isRelativelyAmple_of_projective D hf
    (@SheafOfModules.isFiniteTypeOnSite_of_isFinitePresentationOnSite _ _ _ _ D.F hF) L hamp hP
    (fun n W => (modulePullback B integerBase B.contains_integerBase
      (productFst n (schemeSpace W))).obj (twistingModuleBase B n))
    (hM := fun n W => stacksIsInvertible_modulePullback_obj B integerBase B.contains_integerBase
      (productFst n (schemeSpace W)) (twistingModuleBase B n))
    (fun n W => isoReadingTwistingModuleIso n W)
    (fun n W hW G hG hGft _P' _p' hP' =>
      have : IsAffine ((BigFppfOver.toScheme B integerBase B.contains_integerBase).obj W) := hW
      isRepresentedProper_hilbertPolynomialQuot_twistingModule_of_affine
        (situation n (schemeSpace W) G hG) (situationFrame n (schemeSpace W) G hG) (Iso.refl _)
        hGft hP')

end AlgebraicGeometry.Space.QuotSituation

end
