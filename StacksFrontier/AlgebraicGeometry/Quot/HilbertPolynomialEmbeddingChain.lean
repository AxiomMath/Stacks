/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Quot.HilbertFamilyImageTwistedEuler
public import StacksFrontier.AlgebraicGeometry.Quot.HilbertFunctorOpenImmersionCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.TwistedModulePushforward
public import StacksFrontier.AlgebraicGeometry.Quot.QuotHilbertPolynomialReindex
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackId

/-!
# Hilbert polynomials along a closed immersion followed by an open immersion

Let `π₁ : X ⟶ V` be a closed immersion and `π₂ : V ⟶ P` an open immersion of algebraic spaces over
`A`, `𝒪` an invertible module on `P` and `M` an invertible module on `X` with
`π₁^* π₂^* 𝒪 ≅ M^{⊗ d}`.  The composite of the induced morphisms of Hilbert functors (Stacks 0DPF,
then Stacks 0DPE) carries `Hilb^{P, M}_{X/A}` into `Hilb^{P(d ·), 𝒪}_{P/A}`: the image of a family
has the twisted Euler characteristics of the family with respect to the pullback of `𝒪`, which
are those with respect to `M` at the multiples of `d`.

This is the comparison of Hilbert polynomials in the embedding of `Mor^{P, ℳ}_T(Z, X)` into the
Hilbert space of `ℙⁿ_T` of the proof of Stacks 0DPR.

## Main results

* `AlgebraicGeometry.Space.hilbertModelMap_comp_toBase` and
  `AlgebraicGeometry.Space.hilbertModelMapOfClosed_comp_toBase`: the induced morphisms of models
  lie over the base.
* `AlgebraicGeometry.Space.familyEquiv_hilbertModelMapOfClosed_comp_mem`: the comparison of
  Hilbert polynomials.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section ToBase

variable {X Y A : AlgebraicSpaces B S hS} {π : X ⟶ Y} {bX : X ⟶ A} {bY : Y ⟶ A}
  (hπ : π ≫ bY = bX)

/-- The structure morphism of a model sends a section over `T` to the base morphism of the
corresponding Hilbert family. -/
theorem HilbertPresheafModel.toBase_app_apply {V W : AlgebraicSpaces B S hS} {f : V ⟶ W}
    (M : HilbertPresheafModel f) (T : BigFppfOver B S hS) (z : M.presheaf.obj (Opposite.op T)) :
    M.toBase.app (Opposite.op T) z = yonedaEquiv (M.familyEquiv T z).toBase := rfl

/-- The morphism of models induced by an open immersion (Stacks 0DPE) lies over the base. -/
theorem hilbertModelMap_comp_toBase (hopen : IsOpenImmersion B S hS π.hom)
    (hsep : IsSeparated B S hS bY.hom) (MX : HilbertPresheafModel bX)
    (MY : HilbertPresheafModel bY) :
    hilbertModelMap hπ hopen hsep MX MY ≫ MY.toBase = MX.toBase := by
  ext ⟨T⟩ z
  exact congrArg (fun w : HilbertFamilyOver bY T => yonedaEquiv w.toBase)
    (familyEquiv_hilbertModelMap hπ hopen hsep MX MY T z)

/-- The morphism of models induced by a closed immersion (Stacks 0DPF) lies over the base. -/
theorem hilbertModelMapOfClosed_comp_toBase (hclosed : IsClosedImmersion B S hS π.hom)
    (MX : HilbertPresheafModel bX) (MY : HilbertPresheafModel bY) :
    hilbertModelMapOfClosed hπ hclosed MX MY ≫ MY.toBase = MX.toBase := by
  ext ⟨T⟩ z
  exact congrArg (fun w : HilbertFamilyOver bY T => yonedaEquiv w.toBase)
    (familyEquiv_hilbertModelMapOfClosed hπ hclosed MX MY T z)

end ToBase

section Chain

variable {X V P A : AlgebraicSpaces B S hS} {π₁ : X ⟶ V} {π₂ : V ⟶ P} {bX : X ⟶ A}
  {bV : V ⟶ A} {bP : P ⟶ A}
  (hπ₁ : π₁ ≫ bV = bX) (hclosed : IsClosedImmersion B S hS π₁.hom)
  (hπ₂ : π₂ ≫ bP = bV) (hopen : IsOpenImmersion B S hS π₂.hom)
  (hsep : IsSeparated B S hS bP.hom)
  (hfX : IsFinitePresentation B S hS bX.hom) (hfV : IsFinitePresentation B S hS bV.hom)
  (hfP : IsFinitePresentation B S hS bP.hom)

include hπ₁ hclosed hπ₂ hopen hsep hfV in
/-- **The comparison of Hilbert polynomials along `X ⟶ V ⟶ P`.** If `π₁^* π₂^* 𝒪 ≅ M^{⊗ d}`,
the composite of the induced morphisms of models carries `Hilb^{P, M}_{X/A}` into
`Hilb^{P(d ·), 𝒪}_{P/A}`. -/
theorem familyEquiv_hilbertModelMapOfClosed_comp_mem (MX : HilbertPresheafModel bX)
    (MV : HilbertPresheafModel bV) (MP : HilbertPresheafModel bP)
    (O : Modules.{u, u} B S hS P.1 P.2)
    [hO : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS P.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS P.1 P.2).O)).property O]
    (M : Modules.{u, u} B S hS X.1 X.2)
    [hM : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).property M]
    (d : ℤ)
    (eM : (modulePullback B S hS π₁).obj ((modulePullback B S hS π₂).obj O) ≅
      invertibleTensorPower B S hS X.1 X.2 M d)
    (Pol : ℤ → ℤ) {T : BigFppfOver B S hS} (w : MX.presheaf.obj (Opposite.op T))
    (hw : MX.familyEquiv T w ∈ (hilbertPolynomialSubfunctor bX hfX M Pol).obj (Opposite.op T)) :
    MP.familyEquiv T ((hilbertModelMapOfClosed hπ₁ hclosed MX MV ≫
        hilbertModelMap hπ₂ hopen hsep MV MP).app (Opposite.op T) w) ∈
      (hilbertPolynomialSubfunctor bP hfP O (fun m => Pol (d * m))).obj (Opposite.op T) := by
  have h₂ := stacksIsInvertible_modulePullback_obj B S hS π₂ O
  have h₁ := stacksIsInvertible_modulePullback_obj B S hS π₁ ((modulePullback B S hS π₂).obj O)
  rw [NatTrans.comp_app, types_comp_apply, familyEquiv_hilbertModelMap,
    familyEquiv_hilbertModelMapOfClosed]
  refine hilbertFamilyOverImage_mem_hilbertPolynomialSubfunctor hπ₂ hfV hfP hopen hsep _ O _ ?_
  refine hilbertFamilyOverImageOfClosed_mem_hilbertPolynomialSubfunctor hπ₁ hfX hfV hclosed _
    ((modulePullback B S hS π₂).obj O) _ ?_
  intro t n
  let : Stacks.SheafOfModules.IsInvertible
      (structurePresheaf B S hS (structureSheafQuotSituation bX hfX).toCoherentSituation.X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
        (structureSheafQuotSituation bX hfX).toCoherentSituation.X.1
        (structureSheafQuotSituation bX hfX).toCoherentSituation.X.2).O)).property M := hM
  have h1 : Pol (d * n) = CoherentObject.twistedEuler M
      (hilbertCohObject bX hfX (MX.familyEquiv T w)) t (d * n) := hw t (d * n)
  have h2 := @CoherentObject.twistedEuler_invertibleTensorPower B S hS
    (structureSheafQuotSituation bX hfX).toCoherentSituation M this
    (hilbertCohObject bX hfX (MX.familyEquiv T w)) t d n
  have h3 := @CoherentObject.twistedEuler_congr B S hS
    (structureSheafQuotSituation bX hfX).toCoherentSituation _ _
    (isInvertible_invertibleTensorPower B S hS X.1 X.2 M d) h₁ eM.symm
    (hilbertCohObject bX hfX (MX.familyEquiv T w)) t n
  exact h1.trans (h2.symm.trans h3)

end Chain

section TwistIso

/-- **Transporting `M^{⊗ d} ≅ ρ^* 𝒦` along an isomorphism `X ≅ h_U`.**  If `p' : h_U ⟶ X` has
inverse `p⁻¹` and `ρ^* 𝒦 ≅ (p'^* M)^{⊗ d}` on `h_U`, then `(p⁻¹ ≫ ρ)^* 𝒦 ≅ M^{⊗ d}` on `X`. -/
def modulePullbackCompIsoInvertibleTensorPower {X U P : AlgebraicSpaces B S hS}
    (pinv : X ⟶ U) (p' : U ⟶ X) (h : pinv ≫ p' = 𝟙 X) (ρ : U ⟶ P)
    (K : Modules.{u, u} B S hS P.1 P.2) (M : Modules.{u, u} B S hS X.1 X.2)
    [hM : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).property M]
    (d : ℤ)
    (eρ : (modulePullback B S hS ρ).obj K ≅
      haveI := stacksIsInvertible_modulePullback_obj B S hS p' M
      invertibleTensorPower B S hS U.1 U.2 ((modulePullback B S hS p').obj M) d) :
    (modulePullback B S hS (pinv ≫ ρ)).obj K ≅ invertibleTensorPower B S hS X.1 X.2 M d :=
  haveI := stacksIsInvertible_modulePullback_obj B S hS p' M
  haveI h₂ := stacksIsInvertible_modulePullback_obj B S hS pinv ((modulePullback B S hS p').obj M)
  ((modulePullbackCompIso B S hS pinv ρ).app K).symm ≪≫
    (modulePullback B S hS pinv).mapIso eρ ≪≫
    modulePullbackInvertibleTensorPowerIso B S hS pinv ((modulePullback B S hS p').obj M) d ≪≫
    invertibleTensorPowerCongr B S hS X.1 X.2 (hL := h₂) (hL' := hM)
      (((modulePullbackCompIso B S hS pinv p').app M : (modulePullback B S hS pinv).obj
        ((modulePullback B S hS p').obj M) ≅ _) ≪≫
        eqToIso (congrArg (fun k => (modulePullback B S hS k).obj M) h) ≪≫
        ((modulePullbackIdIso B S hS X).app M : _ ≅ M)) d

end TwistIso

end AlgebraicGeometry.Space

end
