module

public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuotOverSpace.FramedRepresentability
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuotOverSpace.HilbertPolynomialComparison
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.TwistAdd
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackId

/-!
# `Quot^P_{𝒪^{⊕ r}/ℙⁿ_ℤ/ℤ}` is proper over `Spec ℤ`

Let `n ≥ 0`, `r ≥ 1` and `P ∈ ℚ[t]`.  The algebraic space `Quot^P_{𝒪^{⊕ r}/ℙⁿ_ℤ/ℤ}`
parametrizing quotients of `𝒪^{⊕ r}_{ℙⁿ_ℤ}` with Hilbert polynomial `P` is proper over
`Spec ℤ` (Stacks 0DPA).

The Quot situation `𝒪^{⊕ r}/ℙⁿ_ℤ/ℤ` on the big fppf site over `Spec ℤ` is
`AlgebraicGeometry.ProjectiveQuot.quotSituation`.  It carries the projective frame
`ℙⁿ_ℤ = Spec ℤ × ℙⁿ_ℤ` whose projection to `ℙⁿ_ℤ` is the identity
(`AlgebraicGeometry.ProjectiveQuot.quotSituationFrame`); through it a quotient over a scheme `T`
is read as a quotient of `𝒪^{⊕ r}` on the scheme `ℙⁿ_T`, and `Quot^P` is the subfunctor of the
quotients whose reading has Hilbert polynomial `P` on every fibre
(`AlgebraicGeometry.ProjectiveQuotOverSpace.hilbertSubfunctor`).

## Main definitions

* `AlgebraicGeometry.ProjectiveQuot.quotSituationFrame`: the projective frame of
  `𝒪^{⊕ r}/ℙⁿ_ℤ/ℤ`.

## Main results

* `AlgebraicGeometry.Space.QuotSituation.IsRepresentedProper.isProperAlgebraicSpaceOver`: a
  subfunctor of the Quot presheaf represented by a scheme proper over the base is an algebraic
  space proper over the base.
* `AlgebraicGeometry.ProjectiveQuot.isProperAlgebraicSpaceOver_hilbertSubfunctor_quotSituation`:
  `Quot^P_{𝒪^{⊕ r}/ℙⁿ_ℤ/ℤ}` is an algebraic space proper over `Spec ℤ`.
* `ProjectiveQuot.isProperAlgebraicSpaceOver_hilbertPolynomialQuot_quotSituation`: the same, with
  the Hilbert polynomial taken with respect to `𝒪(1)` in the sense of Stacks 0DP6.

## References

* [Stacks Project, Tag 0DPA](https://stacks.math.columbia.edu/tag/0DPA)
* [Stacks Project, Tag 0DP6](https://stacks.math.columbia.edu/tag/0DP6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.Space.QuotSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {D : QuotSituation B S hS}

/-- A subfunctor of the Quot presheaf represented by a scheme proper over the base is an algebraic
space proper over the base. -/
theorem IsRepresentedProper.isProperAlgebraicSpaceOver {Q : Subfunctor D.quotSitePresheaf}
    (h : D.IsRepresentedProper Q) : D.IsProperAlgebraicSpaceOver Q := by
  obtain ⟨Z, e, q, he, hq⟩ := h
  let M : D.SubfunctorModel Q := ⟨yoneda.obj Z, e⟩
  have hM : M.toBase = q := by
    ext T z
    exact congrArg (fun k => (k.app T ⟨z⟩).down) (M.whiskerRight_toBase.trans he)
  exact ⟨M, isAlgebraicSpace_yoneda B S hS Z, hM ▸ hq⟩

end AlgebraicGeometry.Space.QuotSituation

namespace AlgebraicGeometry.ProjectiveQuot

open ProjectiveQuotOverSpace

variable (B : BigFppfSite.{u}) (n r : ℕ)

local notation "𝒯" => BigFppfOver.toScheme B integerBase B.contains_integerBase

/-! ### The projective frame -/

/-- The projective frame of `𝒪^{⊕ r}/ℙⁿ_ℤ/ℤ`: `ℙⁿ_ℤ` is the base change of `ℙⁿ_ℤ ⟶ Spec ℤ`
along the identity of `Spec ℤ`, with the identity as its projection to `ℙⁿ_ℤ`. -/
def quotSituationFrame : ProjectiveFrame B n (quotSituation B n r) where
  toProjective := 𝟙 _
  isPullback :=
    @IsPullback.of_horiz_isIso _ _ _ _ _ _ _ _ _ _ (IsIso.id _)
      ⟨⟨𝟙 _, (subsingleton_hom_schemeSpace_siteBase B _).elim _ _,
        (subsingleton_hom_schemeSpace_siteBase B _).elim _ _⟩⟩
      ⟨(subsingleton_hom_schemeSpace_siteBase B _).elim _ _⟩

variable {B n r}

/-- The identification of `ℙⁿ_ℤ` with the base change of `ℙⁿ_ℤ` to `Spec ℤ` given by the frame
is the identity. -/
theorem baseSpaceIso_quotSituationFrame_hom :
    (baseSpaceIso (quotSituationFrame B n r) (Iso.refl (schemeSpace (siteBase B)))).hom = 𝟙 _ := by
  have h := baseSpaceIso_hom_toProjective (quotSituationFrame B n r)
    (Iso.refl (schemeSpace (siteBase B)))
  have h₁ : toSiteBase B (siteBase B) = 𝟙 _ := Subsingleton.elim _ _
  have h₂ : projectiveSiteMap B n (𝟙 (siteBase B)) = 𝟙 _ :=
    (𝒯).map_injective ((congrArg (projectiveSpaceOverMap n) ((𝒯).map_id _)).trans
      ((projectiveSpaceOverMap_id n _).trans ((𝒯).map_id (projectiveSite B n (siteBase B))).symm))
  rw [h₁, h₂] at h
  exact h.trans ((schemeSpaceFunctor B integerBase B.contains_integerBase).map_id _)

/-- The inverse of the identification of `ℙⁿ_ℤ` with the base change of `ℙⁿ_ℤ` to `Spec ℤ` given
by the frame is the identity. -/
theorem baseSpaceIso_quotSituationFrame_inv :
    (baseSpaceIso (quotSituationFrame B n r) (Iso.refl (schemeSpace (siteBase B)))).inv = 𝟙 _ :=
  Iso.inv_ext ((Category.comp_id _).trans baseSpaceIso_quotSituationFrame_hom)

variable (n r) in
/-- The free module `𝒪^{⊕ r}` of the situation is its own pullback along the inverse of the
identification of the frame. -/
def freeModuleFramedIso :
    (quotSituation B n r).F ≅
      framedModule (quotSituationFrame B n r) (Iso.refl (schemeSpace (siteBase B)))
        (quotSituation B n r).F :=
  ((Space.modulePullbackIdIso B integerBase B.contains_integerBase (quotSituation B n r).X).app
      (quotSituation B n r).F).symm ≪≫
    eqToIso (congrArg (fun g => (Space.modulePullback B integerBase B.contains_integerBase g).obj
      (quotSituation B n r).F) baseSpaceIso_quotSituationFrame_inv.symm)

variable (n r) in
/-- The reading of `𝒪^{⊕ r}` on `ℙⁿ_ℤ` is `𝒪(-0)^{⊕ r}` (Stacks 03DX). -/
def framedBaseReadingFreeIso :
    framedBaseReading (n := n) (W := siteBase B) (quotSituation B n r).F ≅
      twist (-((0 : ℕ) : ℤ)) (freeModule n r ((𝒯).obj (siteBase B))) :=
  Space.representedZariskiModuleQuasicoherentSchemeIso B integerBase B.contains_integerBase
      (projectiveSiteBase B n) ⟨freeModule n r integerBase, isQuasicoherent_freeModule n r _⟩ ≪≫
    (twistZeroIso _ _).symm

/-! ### Properness of `Quot^P_{𝒪^{⊕ r}/ℙⁿ_ℤ/ℤ}` -/

variable (B n r) in
/-- Let `n ≥ 0`, `r ≥ 1` and `P ∈ ℚ[t]`.  The algebraic space `Quot^P_{𝒪^{⊕ r}_{ℙⁿ_ℤ}/ℙⁿ_ℤ/ℤ}`
parametrizing quotients of `𝒪^{⊕ r}_{ℙⁿ_ℤ}` with Hilbert polynomial `P` is proper over `Spec ℤ`:
the subfunctor of the Quot presheaf (Stacks 09TR) of `𝒪^{⊕ r}/ℙⁿ_ℤ/ℤ` of the quotients which,
read on `ℙⁿ_T`, have Hilbert polynomial `P` on every fibre is an algebraic space proper over
`Spec ℤ`. -/
@[stacks 0DPA]
theorem isProperAlgebraicSpaceOver_hilbertSubfunctor_quotSituation (hr : 1 ≤ r)
    (P : Polynomial ℚ) :
    (quotSituation B n r).IsProperAlgebraicSpaceOver
      (hilbertSubfunctor (quotSituationFrame B n r) P) :=
  (isRepresentedProper_hilbertSubfunctor_framed (quotSituationFrame B n r)
    (Iso.refl (schemeSpace (siteBase B))) (quotSituation B n r).F
    (quotSituation B n r).quasicoherent (freeModuleFramedIso n r) hr
    (framedBaseReadingFreeIso n r) P).isProperAlgebraicSpaceOver

variable (B n r) in
/-- For `r ≥ 1` and a function `P : ℤ → ℤ` taking the values of `p ∈ ℚ[t]`, the subfunctor
`Quot^{P, 𝒪(1)}_{𝒪^{⊕ r}/ℙⁿ_ℤ/ℤ}` of the Quot presheaf, with the Hilbert polynomial taken with
respect to `𝒪(1)` (Stacks 0DP6), is an algebraic space proper over `Spec ℤ`. -/
theorem isProperAlgebraicSpaceOver_hilbertPolynomialQuot_quotSituation (hr : 1 ≤ r)
    {P : ℤ → ℤ} {p : Polynomial ℚ} (hP : ∀ m : ℤ, p.eval (m : ℚ) = (P m : ℚ)) :
    (quotSituation B n r).IsProperAlgebraicSpaceOver
      ((quotSituation B n r).hilbertPolynomialQuot
        (twistingModule (quotSituationFrame B n r)) P) := by
  rw [hilbertPolynomialQuot_twistingModule_eq (quotSituationFrame B n r) hP]
  exact isProperAlgebraicSpaceOver_hilbertSubfunctor_quotSituation B n r hr p

end AlgebraicGeometry.ProjectiveQuot

end
