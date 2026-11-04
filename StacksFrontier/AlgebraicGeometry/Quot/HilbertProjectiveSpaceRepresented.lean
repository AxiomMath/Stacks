/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuotOverSpace.AffineFramedRepresentability
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeMorphismsHilbertPolynomial
public import StacksFrontier.AlgebraicGeometry.Quot.HilbertQuotFunctorEquality
public import StacksFrontier.AlgebraicGeometry.Quot.HilbertFunctorOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.DefiningIdealFiniteTypeOfQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.ClopenLiftOverHenselianPair

/-!
# `Hilb^{P, 𝒪(1)}` of `ℙⁿ` over an affine scheme is represented by a proper scheme

Let `T` be an affine scheme and `h_T × ℙⁿ_ℤ ⟶ h_T` the projection (Stacks 0DPB).  Through
`Hilb = Quot_𝒪` (Stacks 0D00), the subfunctor `Hilb^{P, 𝒪(1)}_{(h_T × ℙⁿ_ℤ)/h_T}` of a model of
the Hilbert functor is the subfunctor `Quot^{P, 𝒪(1)}_{𝒪/(T × ℙⁿ)/T}` of the Quot functor of the
structure sheaf, which is represented by a scheme proper over `T` (Stacks 0DPB, the affine case of
the projective Quot space).  So that subfunctor of the model is the image of a monomorphism from
the functor of points of a scheme `H` proper over `T`.

This is the target of the embedding of `Mor^{P, ℳ}_T(Z, X)` in the proof of Stacks 0DPR.

## Main results

* `AlgebraicGeometry.Space.exists_mono_hilbertPolynomialSubfunctor_productSnd`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.ProjectiveQuotOverSpace

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}}

local notation "ℤS" => B.contains_integerBase

local notation "𝒯" => BigFppfOver.toScheme B integerBase ℤS

/-- The projective frame of `Y × ℙⁿ_ℤ ⟶ Y` on the Quot situation of its structure sheaf. -/
abbrev productStructureFrame (n : ℕ) (Y : AlgebraicSpaces B integerBase ℤS) :
    ProjectiveFrame B n
      (structureSheafQuotSituation (productSnd n Y) (isFinitePresentation_productSnd n Y)) :=
  ⟨productFst n Y, isPullback_productSpace n Y⟩

/-- `𝒪(1)` on `Y × ℙⁿ_ℤ`, the twisting module of the projective frame. -/
abbrev productTwistingModule (n : ℕ) (Y : AlgebraicSpaces B integerBase ℤS) :
    Modules.{u, u} B integerBase ℤS (ProjectiveQuotOverSpace.productSpace n Y).1
      (ProjectiveQuotOverSpace.productSpace n Y).2 :=
  twistingModule (productStructureFrame n Y)

/-- `𝒪(1)` on `Y × ℙⁿ_ℤ` is an invertible module. -/
instance isInvertible_productTwistingModule (n : ℕ) (Y : AlgebraicSpaces B integerBase ℤS) :
    Stacks.SheafOfModules.IsInvertible
      (structurePresheaf B integerBase ℤS (ProjectiveQuotOverSpace.productSpace n Y).1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B integerBase ℤS (ProjectiveQuotOverSpace.productSpace n Y).1
          (ProjectiveQuotOverSpace.productSpace n Y).2).O)).property (productTwistingModule n Y) :=
  isInvertible_twistingModule (productStructureFrame n Y)

/-- **`Hilb^{P, 𝒪(1)}_{(T × ℙⁿ)/T}` is represented by a scheme proper over `T`**, for `T` affine
and `P` numerical: the corresponding subfunctor of any model of the Hilbert functor is the image of
a monomorphism from `h_H`, with `H` proper over `T`, lying over `T`. -/
theorem exists_mono_hilbertPolynomialSubfunctor_productSnd (n : ℕ)
    (T : BigFppfOver B integerBase ℤS) [IsAffine ((𝒯).obj T)]
    (MP : HilbertPresheafModel (productSnd n (schemeSpace T))) {P : ℤ → ℤ} {p : Polynomial ℚ}
    (hP : ∀ m : ℤ, p.eval (m : ℚ) = (P m : ℚ)) :
    ∃ (H : BigFppfOver B integerBase ℤS) (ξ : yoneda.obj H ⟶ MP.presheaf) (qH : H ⟶ T),
      Mono ξ ∧
      (∀ (T' : BigFppfOver B integerBase ℤS) (w : MP.presheaf.obj (Opposite.op T')),
        w ∈ Set.range (ξ.app (Opposite.op T')) ↔
          MP.familyEquiv T' w ∈ (hilbertPolynomialSubfunctor (productSnd n (schemeSpace T))
            (isFinitePresentation_productSnd n (schemeSpace T))
            (productTwistingModule n (schemeSpace T)) P).obj (Opposite.op T')) ∧
      ξ ≫ MP.toBase = yoneda.map qH ∧ _root_.AlgebraicGeometry.IsProper ((𝒯).map qH) := by
  let f := productSnd n (schemeSpace T)
  let hf := isFinitePresentation_productSnd n (schemeSpace T)
  let D := structureSheafQuotSituation f hf
  let E := productStructureFrame n (schemeSpace T)
  obtain ⟨H, e, q', hcomm, hprop⟩ :=
    isRepresentedProper_hilbertPolynomialQuot_twistingModule_of_affine D E (W := T) (Iso.refl _)
      (isFiniteTypeOnSite_unit_structureRingSheaf B integerBase ℤS
        (ProjectiveQuotOverSpace.productSpace n (schemeSpace T))) hP
  let qH : H ⟶ T := Yoneda.fullyFaithful.preimage q'
  have hqH : yoneda.map qH = q' := Yoneda.fullyFaithful.map_preimage q'
  let Q := D.hilbertPolynomialQuot (twistingModule E) P
  let ι0 := hilbertPresheafIsoQuotSitePresheaf f hf
  let ξ : yoneda.obj H ⟶ MP.presheaf := MP.mapFrom (e.hom ≫ Q.ι ≫ ι0.inv)
  have hξ : ∀ (T' : BigFppfOver B integerBase ℤS) (g : (yoneda.obj H).obj (Opposite.op T')),
      MP.familyEquiv T' (ξ.app (Opposite.op T') g) =
        ι0.inv.app _ (Q.ι.app _ (e.hom.app _ (ULift.up g))) := fun T' g =>
    types_congr_hom (MP.iso.inv_hom_id_app (Opposite.op T'))
      ((e.hom ≫ Q.ι ≫ ι0.inv).app (Opposite.op T') (ULift.up g))
  refine ⟨H, ξ, qH, ?_, fun T' w => ?_, ?_, (isProper_yoneda_map_iff B integerBase ℤS qH).1
    (hqH ▸ hprop)⟩
  · rw [NatTrans.mono_iff_mono_app]
    refine fun T' => (mono_iff_injective _).2 fun a b hab => ?_
    have h := congrArg (MP.familyEquiv T'.unop) hab
    rw [hξ, hξ] at h
    have h2 := congrArg (ι0.hom.app _) h
    simp only [Iso.inv_hom_id_app_apply] at h2
    exact congrArg ULift.down ((e.app T').toEquiv.injective (Subtype.ext h2))
  · constructor
    · rintro ⟨g, rfl⟩
      show ι0.hom.app _ (MP.familyEquiv T' (ξ.app (Opposite.op T') g)) ∈ Q.obj _
      rw [hξ, Iso.inv_hom_id_app_apply]
      exact (e.hom.app _ (ULift.up g)).2
    · intro hw
      let qv : Q.toFunctor.obj (Opposite.op T') := ⟨ι0.hom.app _ (MP.familyEquiv T' w), hw⟩
      refine ⟨(e.inv.app _ qv).down, (MP.familyEquiv T').injective ?_⟩
      rw [hξ, show e.hom.app (Opposite.op T') (ULift.up (e.inv.app _ qv).down) = qv from
        Iso.inv_hom_id_app_apply e (Opposite.op T') qv]
      exact Iso.hom_inv_id_app_apply ι0 _ _
  · ext T' g
    refine (MP.toBase_mapFrom_app_apply _ T' g).trans ?_
    have hbase : ι0.inv ≫ hilbertPresheafToBase f = D.quotSitePresheafToBase := by
      rw [← hilbertPresheafIsoQuotSitePresheaf_hom_comp_quotSitePresheafToBase f hf]
      exact Iso.inv_hom_id_assoc ι0 _
    have h1 := congrArg ULift.down (types_congr_hom (NatTrans.congr_app hbase T' :
      (ι0.inv ≫ hilbertPresheafToBase f).app T' = D.quotSitePresheafToBase.app T')
        (Q.ι.app _ (e.hom.app _ (ULift.up g))))
    have h2 := congrArg ULift.down (types_congr_hom (NatTrans.congr_app hcomm T' :
      (e.hom ≫ Q.ι ≫ D.quotSitePresheafToBase).app T' =
        (Functor.whiskerRight q' uliftFunctor.{u + 1, u}).app T') (ULift.up g))
    exact h1.trans (h2.trans (by rw [hqH]; rfl))

end AlgebraicGeometry.Space

end
