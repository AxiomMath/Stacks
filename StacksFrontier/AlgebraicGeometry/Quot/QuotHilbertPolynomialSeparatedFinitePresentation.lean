/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.C1746Private.QuotHilbertPolynomialAffineSeparated
public import StacksFrontier.AlgebraicGeometry.Quot.C1746Private.QuotHilbertPolynomialNoetherianImmersion
public import StacksFrontier.AlgebraicGeometry.Quot.C1746Private.QuotHilbertPolynomialNoetherianApproximation

/-!
# `Quot^P_{F/X/B}` is separated and of finite presentation (Stacks 0DPD)

Let `f : X ⟶ B` be a separated morphism of finite presentation of algebraic spaces, `F` a finitely
presented `𝒪_X`-module, `L` an invertible `𝒪_X`-module ample on `X/B` (Stacks 0D31) and `P` a
numerical polynomial.  The algebraic space `Quot^P_{F/X/B}` parametrizing quotients of `F` having
Hilbert polynomial `P` with respect to `L` is separated and of finite presentation over `B`.

## Main results

* `QuotSituation.exists_model_isSeparated_isFinitePresentation_hilbertPolynomialQuot`: for `f`
  separated, `F` of finite presentation and `L` ample on `X/B`, `Quot^P_{F/X/B}` has a model which
  is an algebraic space separated and of finite presentation over `B`.

## References

* [Stacks Project, Tag 0DPD](https://stacks.math.columbia.edu/tag/0DPD)
* [Stacks Project, Tag 0D31](https://stacks.math.columbia.edu/tag/0D31)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.Space.QuotSituation

variable {B : BigFppfSite.{u}}

/-- Let `F/X/B` be a Quot situation over `Spec ℤ` (Stacks 09TR): `f : X ⟶ B` a morphism of finite
presentation of algebraic spaces and `F` a quasi-coherent `𝒪_X`-module.  If `f` is separated, `F`
is of finite presentation, `L` is an invertible `𝒪_X`-module ample on `X/B` (Stacks 0D31) and `P`
is a numerical polynomial, then `Quot^P_{F/X/B}` (the quotients of `F` having Hilbert polynomial
`P` with respect to `L`) has a model `M` in the universe of the site, identified with it over `B`,
which is an algebraic space whose morphism to `B` is separated and of finite presentation. -/
@[stacks 0DPD]
theorem exists_model_isSeparated_isFinitePresentation_hilbertPolynomialQuot
    (D : QuotSituation B integerBase B.contains_integerBase)
    (hsep : IsSeparated B integerBase B.contains_integerBase D.f.hom)
    (hF : SheafOfModules.IsFinitePresentationOnSite D.F)
    (L : Modules.{u, u} B integerBase B.contains_integerBase D.X.1 D.X.2)
    [hL : Stacks.SheafOfModules.IsInvertible
      (structurePresheaf B integerBase B.contains_integerBase D.X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B integerBase B.contains_integerBase D.X.1 D.X.2).O)).property L]
    (hamp : IsRelativelyAmple B integerBase B.contains_integerBase D.f L)
    {P : ℤ → ℤ} {p : Polynomial ℚ} (hP : ∀ m : ℤ, p.eval (m : ℚ) = (P m : ℚ)) :
    ∃ M : D.SubfunctorModel (D.hilbertPolynomialQuot L P),
      IsAlgebraicSpace B integerBase B.contains_integerBase M.presheaf ∧
        IsSeparated B integerBase B.contains_integerBase M.toBase ∧
        IsFinitePresentation B integerBase B.contains_integerBase M.toBase :=
  isSeparatedFinitePresentationAlgebraicSpaceOver_hilbertPolynomialQuot_of_immersion
    (isRepresentedSeparatedFinitePresentation_hilbertPolynomialQuot_of_noetherian
      isRepresentedSeparatedFinitePresentation_hilbertPolynomialQuot_of_isNoetherian)
    D hsep hF L hamp hP

end AlgebraicGeometry.Space.QuotSituation

end
