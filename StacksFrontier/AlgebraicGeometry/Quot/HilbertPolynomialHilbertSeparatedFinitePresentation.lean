/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Quot.C1746Private.HilbertPolynomialHilbertQuot
public import StacksFrontier.AlgebraicGeometry.Quot.C1746Private.QuotHilbertPolynomialAffineSeparated
public import StacksFrontier.AlgebraicGeometry.Quot.C1746Private.QuotHilbertPolynomialNoetherianImmersion
public import StacksFrontier.AlgebraicGeometry.Quot.C1746Private.QuotHilbertPolynomialNoetherianApproximation
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherentLocallyNoetherian

/-!
# `Hilb^P_{X/B}` is separated and of finite presentation (Stacks 0DPI)

Let `f : X ⟶ B` be a separated morphism of finite presentation of algebraic spaces, `L` an
invertible `𝒪_X`-module ample on `X/B` (Stacks 0D31) and `P` a numerical polynomial. The
algebraic space `Hilb^P_{X/B}` parametrizing closed subschemes having Hilbert polynomial `P` with
respect to `L` is separated and of finite presentation over `B`.

The proof is that of the Stacks project: `Hilb_{X/B} = Quot_{𝒪_X/X/B}` (Stacks 0D00), so the
statement is Stacks 0DPD for `F = 𝒪_X`. Stacks 0DPD is proved as in the source: the question is
étale local on `B` (Stacks 03KG); over an affine `W`, `X_W` is a scheme `U` embedded in `ℙⁿ_W`
with `𝒪(1)` restricting to a power of `L_U` (Stacks 01VS, 0DP8); Noetherian approximation
(Stacks 01ZM) reduces to a Noetherian `W`; there `U` is open in its scheme-theoretic closure `X'`
(Stacks 01RG), `𝒪_U` extends to `X'` (Stacks 0G41), `Quot^P` of `X'` is proper (Stacks 0DPC's
argument: 0DPB and 0DP4), and `Quot^P` of `U` is an open subspace of it (Stacks 0DP3), hence
quasi-compact as `W` is Noetherian.

## Main results

* `AlgebraicGeometry.Space.exists_hilbertPolynomialHilbert_isSeparated_isFinitePresentation`:
  `Hilb^P_{X/Y}` is an algebraic space, separated and of finite presentation over `Y`.

## References

* [Stacks Project, Tag 0DPI](https://stacks.math.columbia.edu/tag/0DPI)
* [Stacks Project, Tag 0DPD](https://stacks.math.columbia.edu/tag/0DPD)
* [Stacks Project, Tag 0D00](https://stacks.math.columbia.edu/tag/0D00)
* [Stacks Project, Tag 0D31](https://stacks.math.columbia.edu/tag/0D31)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.Space

open QuotSituation

variable {B : BigFppfSite.{u}}

/-- Let `f : X ⟶ Y` be a separated morphism of finite presentation of algebraic spaces (over
`Spec ℤ`), `L` an invertible `𝒪_X`-module ample on `X/Y` (Stacks 0D31) and `P` a numerical
polynomial. Then the algebraic space `Hilb^P_{X/Y}` parametrizing closed subschemes having Hilbert
polynomial `P` with respect to `L` is separated and of finite presentation over `Y`: the subfunctor
`Hilb^{P, L}_{X/Y}` of the Hilbert presheaf has a model `M` in the universe of the site, identified
with it over `Y`, which is an algebraic space whose morphism to `Y` is separated and of finite
presentation. -/
@[stacks 0DPI]
theorem exists_hilbertPolynomialHilbert_isSeparated_isFinitePresentation
    {X Y : AlgebraicSpaces B integerBase B.contains_integerBase} (f : X ⟶ Y)
    (hsep : IsSeparated B integerBase B.contains_integerBase f.hom)
    (hf : IsFinitePresentation B integerBase B.contains_integerBase f.hom)
    (L : Modules.{u, u} B integerBase B.contains_integerBase X.1 X.2)
    [hL : Stacks.SheafOfModules.IsInvertible
      (structurePresheaf B integerBase B.contains_integerBase X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B integerBase B.contains_integerBase X.1 X.2).O)).property L]
    (hamp : IsRelativelyAmple B integerBase B.contains_integerBase f L)
    {P : ℤ → ℤ} {p : Polynomial ℚ} (hP : ∀ m : ℤ, p.eval (m : ℚ) = (P m : ℚ)) :
    ∃ (M : (BigFppfOver B integerBase B.contains_integerBase)ᵒᵖ ⥤ Type u)
      (e : M ⋙ uliftFunctor.{u + 1, u} ≅ (hilbertPolynomialHilbert f hf L P).toFunctor)
      (q : M ⟶ Y.obj),
      Functor.whiskerRight q uliftFunctor.{u + 1, u} =
          e.hom ≫ (hilbertPolynomialHilbert f hf L P).ι ≫ hilbertPresheafToBase f ∧
        IsAlgebraicSpace B integerBase B.contains_integerBase M ∧
        IsSeparated B integerBase B.contains_integerBase q ∧
        IsFinitePresentation B integerBase B.contains_integerBase q :=
  exists_hilbertPolynomialHilbert_model_of_quot f hf L P
    (isSeparatedFinitePresentationAlgebraicSpaceOver_hilbertPolynomialQuot_of_immersion
      (isRepresentedSeparatedFinitePresentation_hilbertPolynomialQuot_of_noetherian
        isRepresentedSeparatedFinitePresentation_hilbertPolynomialQuot_of_isNoetherian)
      (structureSheafQuotSituation f hf) hsep SheafOfModules.isFinitePresentationOnSite_unit L
      (hL := hL) hamp hP)

end AlgebraicGeometry.Space

end
