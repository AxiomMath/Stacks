/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Quot.C1746Private.HilbertPolynomialHilbertQuot
public import StacksFrontier.AlgebraicGeometry.Quot.QuotHilbertPolynomialRelativelyAmpleProper

/-!
# `Hilb^P_{X/B}` is proper (Stacks 0DPH)

Let `f : X ⟶ B` be a proper morphism of finite presentation of algebraic spaces, `L` an
invertible `𝒪_X`-module ample on `X/B` (Stacks 0D31) and `P` a numerical polynomial. The
algebraic space `Hilb^P_{X/B}` parametrizing closed subschemes having Hilbert polynomial `P` with
respect to `L` is proper over `B`. Under `Hilb_{X/B} = Quot_{𝒪_X/X/B}` (Stacks 0D00),
`Hilb^{P, L}_{X/B}` is `Quot^{P, L}_{𝒪_X/X/B}` (Stacks 0DPG), whose properness is Stacks 0DPC for
the finitely presented module `F = 𝒪_X`.

## Main results

* `AlgebraicGeometry.Space.exists_hilbertPolynomialHilbert_isProper_model_of_quot`: a model of
  `Quot^{P, L}_{𝒪_X/X/Y}` which is an algebraic space proper over `Y` gives one of
  `Hilb^{P, L}_{X/Y}`.
* `AlgebraicGeometry.Space.exists_hilbertPolynomialHilbert_isProper`: `Hilb^P_{X/Y}` is proper
  over `Y`.

## References

* [Stacks Project, Tag 0DPH](https://stacks.math.columbia.edu/tag/0DPH)
* [Stacks Project, Tag 0DPC](https://stacks.math.columbia.edu/tag/0DPC)
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

/-- A model of `Quot^{P, L}_{𝒪_X/X/Y}` which is an algebraic space proper over `Y` is a model of
`Hilb^{P, L}_{X/Y}` over `Y`, through `Hilb^{P, L}_{X/Y} ≅ Quot^{P, L}_{𝒪_X/X/Y}`
(Stacks 0D00). -/
theorem exists_hilbertPolynomialHilbert_isProper_model_of_quot {S : Scheme.{u}} {hS : B.Contains S}
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsFinitePresentation B S hS f.hom)
    (L : Modules.{u, u} B S hS X.1 X.2)
    [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).property L]
    (P : ℤ → ℤ)
    (h : (structureSheafQuotSituation f hf).IsProperAlgebraicSpaceOver
      ((structureSheafQuotSituation f hf).hilbertPolynomialQuot L (hL := hL) P)) :
    ∃ (M : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
      (e : M ⋙ uliftFunctor.{u + 1, u} ≅ (hilbertPolynomialHilbert f hf L P).toFunctor)
      (p : M ⟶ Y.obj),
      Functor.whiskerRight p uliftFunctor.{u + 1, u} =
          e.hom ≫ (hilbertPolynomialHilbert f hf L P).ι ≫ hilbertPresheafToBase f ∧
        IsAlgebraicSpace B S hS M ∧ IsProper B S hS p := by
  obtain ⟨N, halg, hprop⟩ := h
  let i := subfunctorPreimageIsoOfIso (hilbertPresheafIsoQuotSitePresheaf f hf)
    ((structureSheafQuotSituation f hf).hilbertPolynomialQuot L (hL := hL) P)
  have h1 : (hilbertPolynomialHilbert f hf L P).ι ≫ hilbertPresheafToBase f =
      i.hom ≫ ((structureSheafQuotSituation f hf).hilbertPolynomialQuot L (hL := hL) P).ι ≫
        (structureSheafQuotSituation f hf).quotSitePresheafToBase := by
    rw [subfunctorPreimageIsoOfIso_hom_comp_ι_assoc,
      hilbertPresheafIsoQuotSitePresheaf_hom_comp_quotSitePresheafToBase]
    rfl
  refine ⟨N.presheaf, N.iso ≪≫ i.symm, N.toBase, ?_, halg, hprop⟩
  refine (N.whiskerRight_toBase).trans ?_
  rw [h1]
  exact (congrArg (N.iso.hom ≫ ·) (i.inv_hom_id_assoc _).symm).trans (Category.assoc _ _ _).symm

/-- Let `f : X ⟶ Y` be a proper morphism of finite presentation of algebraic spaces (over
`Spec ℤ`), `L` an invertible `𝒪_X`-module ample on `X/Y` (Stacks 0D31) and `P` a numerical
polynomial. Then the algebraic space `Hilb^P_{X/Y}` parametrizing closed subschemes
having Hilbert polynomial `P` with respect to `L` is proper over `Y`: the subfunctor
`Hilb^{P, L}_{X/Y}` of the Hilbert presheaf has a model `M` in the universe of the site,
identified with it over `Y`, which is an algebraic space whose morphism to `Y` is proper. -/
@[stacks 0DPH]
theorem exists_hilbertPolynomialHilbert_isProper
    {X Y : AlgebraicSpaces B integerBase B.contains_integerBase} (f : X ⟶ Y)
    (hprop : IsProper B integerBase B.contains_integerBase f.hom)
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
        IsProper B integerBase B.contains_integerBase q :=
  exists_hilbertPolynomialHilbert_isProper_model_of_quot f hf L P
    (isProperAlgebraicSpaceOver_hilbertPolynomialQuot_of_isRelativelyAmple
      (structureSheafQuotSituation f hf) hprop SheafOfModules.isFinitePresentationOnSite_unit L
      (hL := hL) hamp hP)

end AlgebraicGeometry.Space

end
