/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuotOverSpace.Hilbert
public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorPresheafBaseChange

/-!
# `Quot^P` commutes with base change of the algebraic space `B`

Let `F/X/B` carry a projective frame `X = B × ℙⁿ_ℤ` and let `p : B' ⟶ B` be a morphism of
algebraic spaces.  The base-changed situation `F'/X'/B'` of Stacks 08IT
(`AlgebraicGeometry.Space.QuotSituation.canonicalBaseChanged`) carries the pasted frame
`X' = X ×_B B' = B' × ℙⁿ_ℤ`, the identification `X'_T ≅ X_T` of the two base changes is compatible
with the identifications of both with `h_{ℙⁿ_T}`, and so the readings on `ℙⁿ_T` of corresponding
quotients agree.  Hence a quotient of `F'/X'/B'` has Hilbert polynomial `P` exactly when the
corresponding quotient of `F/X/B` does: `Quot^P_{F'/X'/B'} = Quot^P_{F/X/B} ×_B B'`.

## Main definitions

* `AlgebraicGeometry.ProjectiveQuotOverSpace.ProjectiveFrame.baseChange`: the pasted frame.

## Main results

* `AlgebraicGeometry.ProjectiveQuotOverSpace.mem_hilbertQuotients_baseChange_iff`
* `AlgebraicGeometry.ProjectiveQuotOverSpace.mem_hilbertSubfunctor_baseChange_iff`

## References

* [Stacks Project, Tag 08IT](https://stacks.math.columbia.edu/tag/08IT)
* [Stacks Project, Tag 0DPB](https://stacks.math.columbia.edu/tag/0DPB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProjectiveQuotOverSpace

open ProjectiveQuot

universe u

variable {B : BigFppfSite.{u}} {n : ℕ}
  {D : Space.QuotSituation B integerBase B.contains_integerBase}
  (E : ProjectiveFrame B n D) {Y' : AlgebraicSpaces B integerBase B.contains_integerBase}
  (p : Y' ⟶ D.Y)

/-- **The pasted frame** `X ×_B B' = B' × ℙⁿ_ℤ` on the base-changed situation. -/
def ProjectiveFrame.baseChange : ProjectiveFrame B n (D.canonicalBaseChanged p) where
  toProjective := D.toQuotientSituation.baseChangedSourceProjection p ≫ E.toProjective
  isPullback := by
    have h₁ : IsPullback (D.toQuotientSituation.baseChangedSourceProjection p)
        (D.canonicalBaseChanged p).f D.f p :=
      AlgebraicSpaces.isPullback_fiberProduct B integerBase B.contains_integerBase D.f p
    have e : p ≫ toBaseSpace D.Y = toBaseSpace Y' :=
      Subsingleton.elim (α := Y' ⟶ schemeSpace (siteBase B)) _ _
    rw [← e]
    exact h₁.paste_horiz E.isPullback

/-- The identification `X'_T ≅ X_T` is compatible with the identifications with `h_{ℙⁿ_T}`. -/
theorem spaceIso_baseChange_hom (T : Space.SchemesOver Y') :
    (spaceIso (E.baseChange p) T).hom ≫ (D.canonicalBaseChangeFiberIso p T).hom =
      (spaceIso E ((CostructuredArrow.map p).obj T)).hom := by
  have h₁ := D.toQuotientSituation.baseChangeFiberIso_hom_comp_sourceProjection p
    (D.toQuotientSituation.isQuasicoherentOnSite_baseChangedSourceModule p) T
  have h₂ := spaceIso_hom_sourceProjection_toProjective (E.baseChange p) T
  have h₃ := spaceIso_hom_sourceProjection_toProjective E ((CostructuredArrow.map p).obj T)
  have k₁ := D.toQuotientSituation.baseChangeFiberIso_hom_comp_projection p
    (D.toQuotientSituation.isQuasicoherentOnSite_baseChangedSourceModule p) T
  have k₂ := spaceIso_hom_projection (E.baseChange p) T
  have k₃ := spaceIso_hom_projection E ((CostructuredArrow.map p).obj T)
  refine (isPullback_space E ((CostructuredArrow.map p).obj T)).hom_ext ?_ ?_
  · refine Eq.trans ?_ h₃.symm
    refine Eq.trans ?_ h₂
    refine (Category.assoc _ _ _).trans ?_
    refine congrArg (fun k => (spaceIso (E.baseChange p) T).hom ≫ k) ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (fun k => k ≫ E.toProjective) h₁).trans ?_
    exact Category.assoc _ _ _
  · refine Eq.trans ?_ k₃.symm
    refine Eq.trans ?_ k₂
    refine (Category.assoc _ _ _).trans ?_
    exact congrArg (fun k => (spaceIso (E.baseChange p) T).hom ≫ k) k₁

/-- **The readings of corresponding modules agree**: the reading on `ℙⁿ_T` of the inverse image
along `X'_T ≅ X_T` of a module on `X_T` is its reading. -/
def readingBaseChangeIso (T : Space.SchemesOver Y')
    (M : Space.Modules.{u, u} B integerBase B.contains_integerBase
      (D.space ((CostructuredArrow.map p).obj T)).1
      (D.space ((CostructuredArrow.map p).obj T)).2) :
    (reading (E.baseChange p) T).obj ((Space.modulePullback B integerBase B.contains_integerBase
        (D.canonicalBaseChangeFiberIso p T).hom).obj M) ≅
      (reading E ((CostructuredArrow.map p).obj T)).obj M :=
  ((Space.representedSmallEtaleModuleEquivalence B integerBase B.contains_integerBase
      (projectiveSite B n T.left)).inverse ⋙
    _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B integerBase B.contains_integerBase).obj (projectiveSite B n T.left))
      (projectiveSite B n T.left).left.property).mapIso
    ((Space.modulePullbackCompIso B integerBase B.contains_integerBase _ _).app M ≪≫
      eqToIso (congrArg (fun k => (Space.modulePullback B integerBase B.contains_integerBase
        k).obj M) (spaceIso_baseChange_hom E p T)))

/-- **The Hilbert polynomial condition moves across Stacks 08IT.** -/
theorem mem_hilbertQuotients_baseChange_iff (P : Polynomial ℚ) (T : Space.SchemesOver Y')
    (K : Subobject (D.baseChangeModule ((CostructuredArrow.map p).obj T))) :
    D.canonicalBaseChangeSubobjectEquiv p T K ∈ hilbertQuotients (E.baseChange p) P T ↔
      K ∈ hilbertQuotients E P ((CostructuredArrow.map p).obj T) := by
  have hiff := D.mem_properlySupportedQuotients_canonicalBaseChanged_iff p T K
  let e := (reading (E.baseChange p) T).mapIso (D.canonicalBaseChangedQuotientModuleIso p T K) ≪≫
    readingBaseChangeIso E p T _
  constructor
  · rintro ⟨h₁, h₂⟩
    refine ⟨hiff.1 h₁, hasFibreHilbertPolynomial_of_iso ?_ e h₂⟩
    exact isFinitePresentation_reading (E.baseChange p) T _ h₁.1.1.1 h₁.1.2
  · rintro ⟨h₁, h₂⟩
    refine ⟨hiff.2 h₁, hasFibreHilbertPolynomial_of_iso ?_ e.symm h₂⟩
    exact isFinitePresentation_reading E _ _ h₁.1.1.1 h₁.1.2

/-- **`Quot^P_{F'/X'/B'}` is the preimage of `Quot^P_{F/X/B}`** under the comparison morphism of
Quot presheaves of Stacks 08IT. -/
theorem mem_hilbertSubfunctor_baseChange_iff (P : Polynomial ℚ)
    (T : (BigFppfOver B integerBase B.contains_integerBase)ᵒᵖ)
    (y : (D.canonicalBaseChanged p).quotSitePresheaf.obj T) :
    y ∈ (hilbertSubfunctor (E.baseChange p) P).obj T ↔
      (D.canonicalBaseChangedQuotSitePresheafHom p).app T y ∈
        (hilbertSubfunctor E P).obj T := by
  have h := mem_hilbertQuotients_baseChange_iff E p P (CostructuredArrow.mk y.toBase)
    ((D.canonicalBaseChangeSubobjectEquiv p (CostructuredArrow.mk y.toBase)).symm y.subobject)
  rwa [Equiv.apply_symm_apply] at h

end AlgebraicGeometry.ProjectiveQuotOverSpace

end
