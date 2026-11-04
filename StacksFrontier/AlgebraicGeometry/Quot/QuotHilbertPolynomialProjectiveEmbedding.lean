/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Quot.QuotSubfunctorRepresentedProper
public import StacksFrontier.AlgebraicGeometry.Quot.QuotHilbertPolynomialReindex
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuotOverSpace.Bridge

/-!
# `Quot^P` along a projective embedding

Let `F/X/B` be a Quot situation over `Spec ℤ` with `X ⟶ B` separated, `L` an invertible
`𝒪_X`-module, `P` a numerical polynomial, and `π : X ⟶ B × ℙⁿ_ℤ` a closed immersion over `B`
with `π^*M ≅ L^{⊗ d}` for an invertible module `M` on `B × ℙⁿ_ℤ` and some `d ≠ 0`.  The proof
of Stacks 0DPC replaces `L` by `L^{⊗ d}` and `P(t)` by `P(dt)` (Stacks 0DP8), and then
`Quot^{P(d·), π^*M}_{F/X/B}` by `Quot^{P(d·), M}_{π_*F/(B × ℙⁿ)/B}` (Stacks 0DP4).  So if the
latter is represented by a scheme proper over `B` (the affine case of Stacks 0DPB, with `M` the
pullback of `𝒪(1)`), so is `Quot^{P, L}_{F/X/B}`.

## Main results

* `isRepresentedProper_hilbertPolynomialQuot_of_closedImmersion`: if `π` is a closed immersion
  over `B` with `π^*M ≅ L^{⊗ d}` and `Quot^{P(d·), M}_{π_*F/(B × ℙⁿ)/B}` is represented by a
  scheme proper over `B`, then so is `Quot^{P, L}_{F/X/B}`.

## References

* [Stacks Project, Tag 0DP4](https://stacks.math.columbia.edu/tag/0DP4)
* [Stacks Project, Tag 0DP8](https://stacks.math.columbia.edu/tag/0DP8)
* [Stacks Project, Tag 0DPC](https://stacks.math.columbia.edu/tag/0DPC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.Space.QuotSituation

open ProjectiveQuot ProjectiveQuotOverSpace

variable {B : BigFppfSite.{u}}

local notation "ℤS" => B.contains_integerBase

/-- The projection `B × ℙⁿ_ℤ ⟶ B` is proper, being a base change of `ℙⁿ_ℤ ⟶ Spec ℤ`. -/
theorem isProper_productSnd (n : ℕ) (Y : AlgebraicSpaces B integerBase ℤS) :
    IsProper B integerBase ℤS (productSnd n Y).hom :=
  (isProper_isStableUnderBaseChange B integerBase ℤS).of_isPullback (isPullback_productSpace n Y)
    ((isProper_yoneda_map_iff B integerBase ℤS _).2
      (inferInstanceAs
        (_root_.AlgebraicGeometry.IsProper (projectiveSpaceOver n integerBase ↘ integerBase))))

/-- **Stacks 0DPC, the projective step.**  For `X ⟶ B` separated, a closed immersion
`π : X ⟶ B × ℙⁿ_ℤ` over `B`, an invertible `M` on `B × ℙⁿ_ℤ` with `π^*M ≅ L^{⊗ d}`, `d ≠ 0`, and
a numerical polynomial `P`: if `Quot^{P(d·), M}_{π_*F/(B × ℙⁿ)/B}` is represented by a scheme
proper over `B`, so is `Quot^{P, L}_{F/X/B}`. -/
theorem isRepresentedProper_hilbertPolynomialQuot_of_closedImmersion
    (D : QuotSituation B integerBase ℤS) (hsep : IsSeparated B integerBase ℤS D.f.hom)
    (L : Modules.{u, u} B integerBase ℤS D.X.1 D.X.2)
    [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B integerBase ℤS D.X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B integerBase ℤS D.X.1 D.X.2).O)).property L]
    {P : ℤ → ℤ} {p : Polynomial ℚ} (hP : ∀ m : ℤ, p.eval (m : ℚ) = (P m : ℚ))
    (n : ℕ) (π : D.X ⟶ productSpace n D.Y) (hπ : IsClosedImmersion B integerBase ℤS π.hom)
    (hcomp : π ≫ productSnd n D.Y = D.f)
    (M : Modules.{u, u} B integerBase ℤS (productSpace n D.Y).1 (productSpace n D.Y).2)
    [hM : Stacks.SheafOfModules.IsInvertible
      (structurePresheaf B integerBase ℤS (productSpace n D.Y).1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B integerBase ℤS (productSpace n D.Y).1
          (productSpace n D.Y).2).O)).property M]
    {d : ℤ} (hd : d ≠ 0)
    (eL : (modulePullback B integerBase ℤS π).obj M ≅
      invertibleTensorPower B integerBase ℤS D.X.1 D.X.2 L d)
    (hG : ((modulePushforward B integerBase ℤS π).obj D.F).IsQuasicoherentOnSite)
    (h : (situation n D.Y ((modulePushforward B integerBase ℤS π).obj D.F) hG).IsRepresentedProper
      ((situation n D.Y ((modulePushforward B integerBase ℤS π).obj D.F) hG).hilbertPolynomialQuot M
        (hL := hM) (fun m => P (d * m)))) :
    D.IsRepresentedProper (D.hilbertPolynomialQuot L P) := by
  let PS : QuotPushforwardSituation B integerBase ℤS :=
    { base := D.Y
      X := D.X
      Y := productSpace n D.Y
      π := π
      structureX := D.f
      structureY := productSnd n D.Y
      comp := hcomp
      F := D.F
      quasicoherent := D.quasicoherent
      affine := isAffineHom_of_isClosedImmersion B integerBase ℤS π.hom hπ
      quasiFinite := isQuasiFinite_of_isFinite B integerBase ℤS π.hom D.X.2 (productSpace n D.Y).2
        (isFinite_of_isClosedImmersion B integerBase ℤS π.hom hπ)
      separatedX := hsep
      separatedY := (isProper_productSnd n D.Y).isSeparated
      finitePresentationX := D.finitePresentation
      finitePresentationY := isFinitePresentation_productSnd n D.Y }
  have h1 := PS.isRepresentedProper_hilbertPolynomialQuot_of_directImage hπ M
    (fun m => P (d * m)) h
  have e1 : D.hilbertPolynomialQuot L P =
      D.hilbertPolynomialQuot ((modulePullback B integerBase ℤS π).obj M)
        (hL := isInvertible_modulePullback B integerBase ℤS π M) (fun m => P (d * m)) :=
    (D.hilbertPolynomialQuot_invertibleTensorPower L hP hd).symm.trans
      (@hilbertPolynomialQuot_congr B integerBase ℤS D _
        (isInvertible_invertibleTensorPower B integerBase ℤS D.X.1 D.X.2 L d) _
        (isInvertible_modulePullback B integerBase ℤS π M) eL.symm _)
  exact IsRepresentedProper.of_eq e1.symm h1

end AlgebraicGeometry.Space.QuotSituation

end
