/-
Copyright (c) 2026 Stacks Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.PolarizationSeesaw
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.CurvePowerDegreeTransport

/-!
# The trace of `φ^*` on the Jacobian from a polarization

Let `X` be a smooth projective curve over an algebraically closed field `k`, `φ : X ⟶ X` a
morphism over `k`, `α = φ^*` on the Jacobian `J`, and `L` an invertible module on `J` whose
polarization class `Λ_L` (`Stacks.PicardFunctor.polarizationClass`) has classifying map `-𝟙_J`.

The seesaw on `C^2` (`C = X`) gives
`B(aj ∘ p₀, α ∘ aj ∘ p₁) = p₁^*[φ(c₀)] - (φ × 1)^*Δ + (φ × 1)^* F₀`, and restricting to the
diagonal, `deg B(α ∘ aj, aj) = 1 + deg φ - V(φ)`
(`Stacks.PicardFunctor.curveDeg_classYα_jacobianPullback`). Together with
`Stacks.CurvePower.abelianVarietyTrace_eq_curveDeg` this is
`Tr(φ^* | J) = 1 + deg φ - V(φ)` (`Stacks.PicardFunctor.abelianVarietyTrace_jacobianPullback`),
the formula of [Stacks, Tag 03U1].
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite MonoidalCategory
open CartesianMonoidalCategory Stacks.CurvePower
open scoped CategoryTheory.MonObj

universe u

namespace Stacks.PicardFunctor

variable {k : Type u} [Field k] (B : BigFppfSite.{u}) {X : Scheme.{u}} (hX : B.Contains X)
  (hk : B.Contains (Spec (.of k))) (f : B.obj hX ⟶ B.obj hk)
  [IsCurve k (B.inclusion.map f)] [GeometricallyIrreducible (B.inclusion.map f)]
  [Smooth (B.inclusion.map f)] [IsProper (B.inclusion.map f)]
  [IsProjectiveVariety k (B.inclusion.map f)]
  (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ B.inclusion.map f = 𝟙 _)
  [(picardFunctor B hX hk f).IsRepresentable] [IsAlgClosed k]

attribute [local instance] isAbelianVariety_jacobian

instance isCurve_curveOver : IsCurve k (curveOver B hX hk f).hom :=
  inferInstanceAs (IsCurve k (B.inclusion.map f))

instance smooth_curveOver : Smooth (curveOver B hX hk f).hom :=
  inferInstanceAs (Smooth (B.inclusion.map f))

variable (φ : X ⟶ X) (w : φ ≫ B.inclusion.map f = B.inclusion.map f)

/-- `φ` as an endomorphism of the curve over `k`. -/
abbrev curveEndo : curveOver B hX hk f ⟶ curveOver B hX hk f :=
  Over.homMk φ w

omit [IsCurve k (B.inclusion.map f)] [GeometricallyIrreducible (B.inclusion.map f)]
  [Smooth (B.inclusion.map f)] [IsProjectiveVariety k (B.inclusion.map f)]
  [(picardFunctor B hX hk f).IsRepresentable] [IsAlgClosed k] in
/-- **The base change `φ × 1` on `C^(m+1)`.** -/
theorem endoBaseChangeMap_powerObj (m : ℕ) :
    endoBaseChangeMap B hX hk f φ w (powerObj B hX hk f m) =
      (CartesianMonoidalCategory.lift
        (fst (curveOver B hX hk f) (power (curveOver B hX hk f) m) ≫ curveEndo B hX hk f φ w)
        (snd (curveOver B hX hk f) (power (curveOver B hX hk f) m)) :
          power (curveOver B hX hk f) (m + 1) ⟶ power (curveOver B hX hk f) (m + 1)).left := by
  apply pullback.hom_ext
  · refine (endoBaseChangeMap_fst B hX hk f φ w _).trans ?_
    exact (congrArg Over.Hom.left (lift_fst
      (fst (curveOver B hX hk f) (power (curveOver B hX hk f) m) ≫ curveEndo B hX hk f φ w)
      (snd (curveOver B hX hk f) (power (curveOver B hX hk f) m)))).symm
  · refine (endoBaseChangeMap_snd B hX hk f φ w _).trans ?_
    exact (congrArg Over.Hom.left (lift_snd
      (fst (curveOver B hX hk f) (power (curveOver B hX hk f) m) ≫ curveEndo B hX hk f φ w)
      (snd (curveOver B hX hk f) (power (curveOver B hX hk f) m)))).symm

omit [IsCurve k (B.inclusion.map f)] [GeometricallyIrreducible (B.inclusion.map f)]
  [Smooth (B.inclusion.map f)] [IsProper (B.inclusion.map f)]
  [IsProjectiveVariety k (B.inclusion.map f)]
  [(picardFunctor B hX hk f).IsRepresentable] [IsAlgClosed k] in
/-- `φ × 1` composed with the section through `c` is the section through `φ(c)`. -/
theorem insertPoint_comp_endo (c : power (curveOver B hX hk f) 0 ⟶ curveOver B hX hk f) :
    insertPoint (curveOver B hX hk f) c 1 0 ≫
      (CartesianMonoidalCategory.lift
        (fst (curveOver B hX hk f) (power (curveOver B hX hk f) 1) ≫ curveEndo B hX hk f φ w)
        (snd (curveOver B hX hk f) (power (curveOver B hX hk f) 1)) :
          power (curveOver B hX hk f) (1 + 1) ⟶ power (curveOver B hX hk f) (1 + 1)) =
      insertPoint (curveOver B hX hk f) (c ≫ curveEndo B hX hk f φ w) 1 0 := by
  have hsa : (0 : Fin (1 + 1)).succAbove 0 = Fin.succ 0 := rfl
  have h1 := insertPoint_coord_succAbove (curveOver B hX hk f) c 1 0 0
  have h2 := insertPoint_coord_succAbove (curveOver B hX hk f) (c ≫ curveEndo B hX hk f φ w) 1 0 0
  rw [hsa, coord_succ] at h1 h2
  refine hom_ext 2 (Fin.cases ?_ (Fin.cases ?_ (fun i => i.elim0)))
  · change _ ≫ fst _ _ = _ ≫ coord (curveOver B hX hk f) (1 + 1) 0
    refine (congrArg (insertPoint (curveOver B hX hk f) c 1 0 ≫ ·) (lift_fst _ _)).trans ?_
    refine (insertPoint_coord_self_assoc (curveOver B hX hk f) c 1 0 _).trans ?_
    exact (Category.assoc _ _ _).trans
      (insertPoint_coord_self (curveOver B hX hk f) (c ≫ curveEndo B hX hk f φ w) 1 0).symm
  · rw [coord_succ]
    refine (Category.assoc _ _ _).trans ((congrArg (insertPoint (curveOver B hX hk f) c 1 0 ≫ ·)
      (lift_snd_assoc _ _ (coord (curveOver B hX hk f) 1 0))).trans ?_)
    exact h1.trans h2.symm

omit [IsCurve k (B.inclusion.map f)] [GeometricallyIrreducible (B.inclusion.map f)]
  [Smooth (B.inclusion.map f)] [IsProjectiveVariety k (B.inclusion.map f)]
  [(picardFunctor B hX hk f).IsRepresentable] [IsAlgClosed k] in
theorem sectionRestrict_endo (c : power (curveOver B hX hk f) 0 ⟶ curveOver B hX hk f)
    (x : picardAt B hX hk f (powerObj B hX hk f 1)) :
    sectionRestrict B hX hk f c
        (Stacks.Picard.schemePullbackClass (endoBaseChangeMap B hX hk f φ w (powerObj B hX hk f 1))
          x) =
      sectionRestrict B hX hk f (c ≫ curveEndo B hX hk f φ w) x := by
  refine (Stacks.Picard.schemePullbackClass_comp (insertPoint (curveOver B hX hk f) c 1 0).left
    _ x).trans ?_
  rw [endoBaseChangeMap_powerObj, ← Over.comp_left, insertPoint_comp_endo]
  rfl

omit [IsAlgClosed k] in
/-- **The seesaw on `C^2`, general form**: two classes with inverse classifying maps over `C^1`
differ by a class pulled back from `C^1`. -/
theorem exists_eq_pullSndP_sub {E R : picardAt B hX hk f (powerObj B hX hk f 1)}
    (hE : HasDegreeZero B hX hk f σ hσ _ E) (hR : HasDegreeZero B hX hk f σ hσ _ R)
    (h : classifyingMap B hX hk f σ hσ _ E hE = (classifyingMap B hX hk f σ hσ _ R hR)⁻¹) :
    ∃ N : PowerPic (curveOver B hX hk f) 1, E = pullSndP B hX hk f N - R := by
  have hR' := hasDegreeZero_neg B hX hk f σ hσ hR
  obtain ⟨N, hN⟩ := (classifyingMap_eq_classifyingMap_iff B hX hk f σ hσ _ hE hR').1
    (by rw [h, classifyingMap_neg B hX hk f σ hσ _ hR])
  refine ⟨N, ?_⟩
  change pullSndP B hX hk f N = E - -R at hN
  rw [hN]
  abel

/-- **The seesaw for `φ^*`, general form.** A class `E` on `C^2 = C × C^1` with degree-zero
fibres, classifying map `-(φ^* ∘ aj)` over `C^1`, and vanishing along the section through `c₀`, is
`p₁^*[φ(c₀)] - (φ × 1)^*(Δ - F₀)`. -/
theorem eq_pullSndP_sub_of_classifyingMap {E : picardAt B hX hk f (powerObj B hX hk f 1)}
    (hE : HasDegreeZero B hX hk f σ hσ _ E)
    (hcE : classifyingMap B hX hk f σ hσ _ E hE = (coord (curveOver B hX hk f) 1 0 ≫
      abelJacobi B hX hk f σ hσ ≫ jacobianPullback B hX hk f φ w σ hσ)⁻¹)
    (hs : sectionRestrict B hX hk f (curvePowerZeroBasePoint B hX hk f σ hσ) E = 0) :
    E = pullSndP B hX hk f (pointClass (curveOver B hX hk f)
          (curvePowerZeroBasePoint B hX hk f σ hσ ≫ curveEndo B hX hk f φ w)) -
        Stacks.Picard.schemePullbackClass
          (endoBaseChangeMap B hX hk f φ w (powerObj B hX hk f 1))
          (diagP B hX hk f - fibreP B hX hk f σ hσ) := by
  set α := jacobianPullback B hX hk f φ w σ hσ
  set R := picardMap B hX hk f (powerHomCurve B hX hk f (coord (curveOver B hX hk f) 1 0))
    (abelJacobiClass B hX hk f σ hσ)
  have hR : HasDegreeZero B hX hk f σ hσ _ R :=
    hasDegreeZero_picardMap B hX hk f σ hσ _ (hasDegreeZero_familyClass_sub B hX hk f σ hσ _ _ _)
  have hcR : classifyingMap B hX hk f σ hσ _ R hR =
      coord (curveOver B hX hk f) 1 0 ≫ abelJacobi B hX hk f σ hσ := by
    rw [← classifyingMap_comp, post_map_powerHomCurve]
    rfl
  have hR' := hasDegreeZero_endoBaseChangeMap B hX hk f σ hσ φ w _ hR
  have hcR' := classifyingMap_endoBaseChangeMap B hX hk f σ hσ φ w _ hR
  have key : classifyingMap B hX hk f σ hσ _ _ hR' =
      coord (curveOver B hX hk f) 1 0 ≫ abelJacobi B hX hk f σ hσ ≫ α := by
    rw [hcR', hcR]
    exact Category.assoc _ _ _
  obtain ⟨N, hN⟩ := exists_eq_pullSndP_sub B hX hk f σ hσ hE hR'
    (hcE.trans (congrArg (fun x => x⁻¹) key.symm))
  have hRv : R = diagP B hX hk f - fibreP B hX hk f σ hσ :=
    picardMap_abelJacobiClass_coord B hX hk f σ hσ
  rw [hRv] at hN
  have h2 := congrArg (sectionRestrict B hX hk f (curvePowerZeroBasePoint B hX hk f σ hσ)) hN
  rw [hs, map_sub, sectionRestrict_pullSndP,
    sectionRestrict_endo, map_sub, sectionRestrict_diagP, sectionRestrict_fibreP, sub_zero] at h2
  rw [hN, sub_eq_zero.1 h2.symm]

variable {L : SheafOfModules.{u}
    (structureSheafRing (jacobianGrp B hX hk f σ hσ).X.left.toRingedSpace)}
  {hL : Stacks.SheafOfModules.IsInvertible (jacobianGrp B hX hk f σ hσ).X.left.presheaf
    (jacobianGrp B hX hk f σ hσ).X.left.ringCatIsSheaf L}

/-- The restriction of `B(aj ∘ p₀, z)` along the section through `c₀` vanishes, as
`aj(c₀) = 0`. -/
theorem sectionRestrict_cubeBilin_coord_zero
    (z : Additive (power (curveOver B hX hk f) 2 ⟶ (jacobianGrp B hX hk f σ hσ).X)) :
    sectionRestrict B hX hk f (curvePowerZeroBasePoint B hX hk f σ hσ)
      (Stacks.QuadraticMap.cubeBilin (classQ (jacobianGrp B hX hk f σ hσ).X L hL)
        (Additive.ofMul (coord (curveOver B hX hk f) 2 0 ≫ abelJacobi B hX hk f σ hσ)) z) = 0 := by
  refine (schemePullbackClass_cubeBilin_classQ (jacobianGrp B hX hk f σ hσ).X L hL
    (insertPoint (curveOver B hX hk f) (curvePowerZeroBasePoint B hX hk f σ hσ) 1 0) _ _).trans ?_
  simp only [precompHom_apply, toMul_ofMul]
  rw [insertPoint_coord_self_assoc, curvePowerZeroBasePoint_comp_abelJacobi, MonObj.comp_one,
    ofMul_one]
  have hQ0 := classQ_toPowerZero_comp B hX hk f σ hσ L hL (m := 1) 1
  rw [MonObj.comp_one, ofMul_one] at hQ0
  rw [Stacks.QuadraticMap.cubeBilin, zero_add, hQ0, sub_zero, sub_self]

variable (hΛ : HasDegreeZero B hX hk f σ hσ _ (polarizationClass B hX hk f σ hσ L hL))
  (hcl : classifyingMap B hX hk f σ hσ _ _ hΛ = (𝟙 (jacobianGrp B hX hk f σ hσ).X)⁻¹)

include hcl in
/-- **The seesaw for `φ^*`**: `B(aj ∘ p₀, φ^* ∘ aj ∘ p₁) = p₁^*[φ(c₀)] - (φ × 1)^*(Δ - F₀)`. -/
theorem cubeBilin_jacobianPullback_eq :
    Stacks.QuadraticMap.cubeBilin (classQ (jacobianGrp B hX hk f σ hσ).X L hL)
        (Additive.ofMul (coord (curveOver B hX hk f) 2 0 ≫ abelJacobi B hX hk f σ hσ))
        (Additive.ofMul (coord (curveOver B hX hk f) 2 1 ≫ abelJacobi B hX hk f σ hσ ≫
          jacobianPullback B hX hk f φ w σ hσ)) =
      pullSndP B hX hk f (pointClass (curveOver B hX hk f)
          (curvePowerZeroBasePoint B hX hk f σ hσ ≫ curveEndo B hX hk f φ w)) -
        Stacks.Picard.schemePullbackClass
          (endoBaseChangeMap B hX hk f φ w (powerObj B hX hk f 1))
          (diagP B hX hk f - fibreP B hX hk f σ hσ) := by
  set α := jacobianPullback B hX hk f φ w σ hσ
  set g := powerHomJac B hX hk f σ hσ
    (coord (curveOver B hX hk f) 1 0 ≫ abelJacobi B hX hk f σ hσ ≫ α)
  have hEq : picardMap B hX hk f g (polarizationClass B hX hk f σ hσ L hL) =
      Stacks.QuadraticMap.cubeBilin (classQ (jacobianGrp B hX hk f σ hσ).X L hL)
        (Additive.ofMul (coord (curveOver B hX hk f) 2 0 ≫ abelJacobi B hX hk f σ hσ))
        (Additive.ofMul (coord (curveOver B hX hk f) 2 1 ≫ abelJacobi B hX hk f σ hσ ≫ α)) := by
    rw [picardMap_polarizationClass, post_map_powerHomJac]
    congr 2
  have hc := classifyingMap_picardMap_polarizationClass B hX hk f σ hσ hΛ hcl g
  have hg : (Over.post (X := B.obj hk) B.inclusion).map g =
      coord (curveOver B hX hk f) 1 0 ≫ abelJacobi B hX hk f σ hσ ≫ α :=
    post_map_powerHomJac B hX hk f σ hσ _
  rw [hg] at hc
  replace hc := hc.trans (congrArg (fun x => x⁻¹)
    (Category.comp_id (coord (curveOver B hX hk f) 1 0 ≫ abelJacobi B hX hk f σ hσ ≫ α)))
  have h0 : sectionRestrict B hX hk f (curvePowerZeroBasePoint B hX hk f σ hσ)
      (picardMap B hX hk f g (polarizationClass B hX hk f σ hσ L hL)) = 0 :=
    (congrArg (sectionRestrict B hX hk f (curvePowerZeroBasePoint B hX hk f σ hσ)) hEq).trans
      (sectionRestrict_cubeBilin_coord_zero B hX hk f σ hσ _)
  rw [← hEq]
  exact eq_pullSndP_sub_of_classifyingMap B hX hk f σ hσ φ w
    (hasDegreeZero_picardMap B hX hk f σ hσ g hΛ) hc h0

/-- Restriction along the diagonal `C^1 ⟶ C^2`, as a homomorphism on `picardAt (powerObj 1)`. -/
abbrev diagRestrict :
    picardAt B hX hk f (powerObj B hX hk f 1) →+ PowerPic (curveOver B hX hk f) 1 :=
  Stacks.Picard.schemePullbackClassHom (doubleFirst (curveOver B hX hk f) 0).left

omit [IsCurve k (B.inclusion.map f)] [GeometricallyIrreducible (B.inclusion.map f)]
  [Smooth (B.inclusion.map f)] [IsProper (B.inclusion.map f)]
  [IsProjectiveVariety k (B.inclusion.map f)]
  [(picardFunctor B hX hk f).IsRepresentable] [IsAlgClosed k] in
theorem doubleFirst_comp_endo :
    doubleFirst (curveOver B hX hk f) 0 ≫
      (CartesianMonoidalCategory.lift
        (fst (curveOver B hX hk f) (power (curveOver B hX hk f) 1) ≫ curveEndo B hX hk f φ w)
        (snd (curveOver B hX hk f) (power (curveOver B hX hk f) 1)) :
          power (curveOver B hX hk f) (0 + 2) ⟶ power (curveOver B hX hk f) (0 + 2)) =
      lift 2 (Fin.cons (coord (curveOver B hX hk f) 1 0 ≫ curveEndo B hX hk f φ w)
        fun _ => coord (curveOver B hX hk f) 1 0) := by
  refine hom_ext 2 (Fin.cases ?_ (Fin.cases ?_ (fun i => i.elim0)))
  · change _ ≫ fst _ _ = _ ≫ coord (curveOver B hX hk f) 2 0
    refine (congrArg (doubleFirst (curveOver B hX hk f) 0 ≫ ·) (lift_fst _ _)).trans ?_
    rw [lift_coord]
    exact (lift_coord_assoc (C := curveOver B hX hk f) 2 _ 0 _)
  · refine Eq.trans ?_ (lift_coord (C := curveOver B hX hk f) 2
      (Fin.cons (coord (curveOver B hX hk f) 1 0 ≫ curveEndo B hX hk f φ w)
        fun _ => coord (curveOver B hX hk f) 1 0) (Fin.succ 0)).symm
    refine (Category.assoc _ _ _).trans ((congrArg (doubleFirst (curveOver B hX hk f) 0 ≫ ·)
      (lift_snd_assoc _ _ (coord (curveOver B hX hk f) 1 0))).trans ?_)
    exact lift_coord (C := curveOver B hX hk f) 2 (Fin.cons (coord (curveOver B hX hk f) 1 0)
      (coord (curveOver B hX hk f) 1)) (Fin.succ 0)

omit [IsCurve k (B.inclusion.map f)] [GeometricallyIrreducible (B.inclusion.map f)]
  [Smooth (B.inclusion.map f)] [IsProjectiveVariety k (B.inclusion.map f)]
  [(picardFunctor B hX hk f).IsRepresentable] [IsAlgClosed k] in
theorem doubleFirst_comp_snd :
    (doubleFirst (curveOver B hX hk f) 0).left ≫
      baseChangeProj B hX hk f (powerObj B hX hk f 1) = 𝟙 _ := by
  have h : doubleFirst (curveOver B hX hk f) 0 ≫
      (snd (curveOver B hX hk f) (power (curveOver B hX hk f) 1) :
        power (curveOver B hX hk f) (0 + 2) ⟶ power (curveOver B hX hk f) 1) = 𝟙 _ := by
    refine hom_ext 1 fun i => ?_
    fin_cases i
    exact (Category.assoc _ _ _).trans ((lift_coord (C := curveOver B hX hk f) 2
      (Fin.cons (coord (curveOver B hX hk f) 1 0) (coord (curveOver B hX hk f) 1))
      (Fin.succ 0)).trans (Category.id_comp _).symm)
  exact congrArg Over.Hom.left h

omit [GeometricallyIrreducible (B.inclusion.map f)]
  [(picardFunctor B hX hk f).IsRepresentable] [IsAlgClosed k] in
theorem fibreP_eq : fibreP B hX hk f σ hσ = Stacks.Picard.schemePullbackClass
    (firstProj (curveOver B hX hk f) 1).left
      (pointClass (curveOver B hX hk f) (curvePowerZeroBasePoint B hX hk f σ hσ)) := by
  change fibreClass (curveOver B hX hk f) (curvePowerZeroBasePoint B hX hk f σ hσ) 1 = _
  exact (schemePullbackClass_firstProj_pointClass (curveOver B hX hk f)
    (curvePowerZeroBasePoint B hX hk f σ hσ) 1).symm

omit [GeometricallyIrreducible (B.inclusion.map f)]
  [(picardFunctor B hX hk f).IsRepresentable] in
/-- **The diagonal restriction of the seesaw identity has degree `1 + deg φ - V(φ)`.** -/
theorem curveDeg_diagRestrict_of_eq {E : picardAt B hX hk f (powerObj B hX hk f 1)}
    (hE : E = pullSndP B hX hk f (pointClass (curveOver B hX hk f)
          (curvePowerZeroBasePoint B hX hk f σ hσ ≫ curveEndo B hX hk f φ w)) -
        Stacks.Picard.schemePullbackClass
          (endoBaseChangeMap B hX hk f φ w (powerObj B hX hk f 1))
          (diagP B hX hk f - fibreP B hX hk f σ hσ)) :
    curveDeg (curveOver B hX hk f) (topologicalKrullDim_curveOver B hX hk f)
        (diagRestrict B hX hk f E) =
      1 + (CurveGraph.curveMapDegree (B.inclusion.map f) φ w : ℤ) -
        CurveGraph.fixedPointIntersection (B.inclusion.map f)
          (topologicalKrullDim_left_le_one (curveOver B hX hk f)) φ w := by
  set C := curveOver B hX hk f
  have e2 : diagRestrict B hX hk f (pullSndP B hX hk f
      (pointClass C (curvePowerZeroBasePoint B hX hk f σ hσ ≫ curveEndo B hX hk f φ w))) =
      pointClass C (curvePowerZeroBasePoint B hX hk f σ hσ ≫ curveEndo B hX hk f φ w) := by
    refine (Stacks.Picard.schemePullbackClass_comp (doubleFirst C 0).left _ _).trans ?_
    rw [doubleFirst_comp_snd, Stacks.Picard.schemePullbackClass_id]
  have hγ : (doubleFirst C 0).left ≫ endoBaseChangeMap B hX hk f φ w (powerObj B hX hk f 1) =
      (lift 2 (Fin.cons (coord C 1 0 ≫ curveEndo B hX hk f φ w) fun _ => coord C 1 0)).left := by
    rw [endoBaseChangeMap_powerObj, ← Over.comp_left, doubleFirst_comp_endo]
  have e3 : diagRestrict B hX hk f (Stacks.Picard.schemePullbackClass
      (endoBaseChangeMap B hX hk f φ w (powerObj B hX hk f 1)) (diagP B hX hk f)) =
      Stacks.Picard.schemePullbackClass
        (lift 2 (Fin.cons (coord C 1 0 ≫ curveEndo B hX hk f φ w) fun _ => coord C 1 0)).left
        (diagClass C) := by
    refine (Stacks.Picard.schemePullbackClass_comp (doubleFirst C 0).left _ _).trans ?_
    rw [hγ]
    rfl
  have e4 : diagRestrict B hX hk f (Stacks.Picard.schemePullbackClass
      (endoBaseChangeMap B hX hk f φ w (powerObj B hX hk f 1)) (fibreP B hX hk f σ hσ)) =
      Stacks.Picard.schemePullbackClass
        (lift 1 fun _ => coord C 1 0 ≫ curveEndo B hX hk f φ w).left
        (pointClass C (curvePowerZeroBasePoint B hX hk f σ hσ)) := by
    have hφ1 : lift 2 (Fin.cons (coord C 1 0 ≫ curveEndo B hX hk f φ w) fun _ => coord C 1 0) ≫
        firstProj C 1 = lift 1 fun _ => coord C 1 0 ≫ curveEndo B hX hk f φ w := by
      refine hom_ext 1 fun i => ?_
      fin_cases i
      rw [Category.assoc, reindex_coord]
      exact (lift_coord (C := C) 2 _ 0).trans
        (lift_coord (C := C) 1 (fun _ => coord C 1 0 ≫ curveEndo B hX hk f φ w) 0).symm
    rw [fibreP_eq]
    refine (Stacks.Picard.schemePullbackClass_comp (doubleFirst C 0).left _ _).trans ?_
    refine (Stacks.Picard.schemePullbackClass_comp _ (firstProj C 1).left _).trans ?_
    rw [hγ, ← Over.comp_left, hφ1]
  have m2 := (congrArg (diagRestrict B hX hk f) (schemePullbackClass_sub
    (endoBaseChangeMap B hX hk f φ w (powerObj B hX hk f 1)) (diagP B hX hk f)
    (fibreP B hX hk f σ hσ))).trans (map_sub _ _ _)
  have m1 := (congrArg (diagRestrict B hX hk f) hE).trans (map_sub _ _ _)
  rw [m2, e2, e3, e4] at m1
  have hd := congrArg (curveDegHom C (topologicalKrullDim_curveOver B hX hk f)) m1
  rw [map_sub, map_sub] at hd
  change curveDeg C (topologicalKrullDim_curveOver B hX hk f) _ =
    curveDeg C (topologicalKrullDim_curveOver B hX hk f) _ -
      (curveDeg C (topologicalKrullDim_curveOver B hX hk f) _ -
        curveDeg C (topologicalKrullDim_curveOver B hX hk f) _) at hd
  rw [hd, curveDeg_pointClass, curveDeg_graph_diagClass, curveDeg_graph_pointClass]
  change 1 - (CurveGraph.fixedPointIntersection (B.inclusion.map f) _ φ w -
    (CurveGraph.curveMapDegree (B.inclusion.map f) φ w : ℤ)) = _
  ring


include hcl in
/-- **`deg B(φ^* ∘ aj, aj) = 1 + deg φ - V(φ)`** on the curve. -/
theorem curveDeg_classYα_jacobianPullback :
    curveDeg (curveOver B hX hk f) (topologicalKrullDim_curveOver B hX hk f)
        (classYα (jacobianGrp B hX hk f σ hσ).X L hL (jacobianPullback B hX hk f φ w σ hσ)
          (power (curveOver B hX hk f) 1)
          (Additive.ofMul (coord (curveOver B hX hk f) 1 0 ≫ abelJacobi B hX hk f σ hσ))) =
      1 + (CurveGraph.curveMapDegree (B.inclusion.map f) φ w : ℤ) -
        CurveGraph.fixedPointIntersection (B.inclusion.map f)
          (topologicalKrullDim_left_le_one (curveOver B hX hk f)) φ w := by
  set α := jacobianPullback B hX hk f φ w σ hσ
  set C := curveOver B hX hk f
  have e1 : diagRestrict B hX hk f
      (Stacks.QuadraticMap.cubeBilin (classQ (jacobianGrp B hX hk f σ hσ).X L hL)
        (Additive.ofMul (coord C 2 0 ≫ abelJacobi B hX hk f σ hσ))
        (Additive.ofMul (coord C 2 1 ≫ abelJacobi B hX hk f σ hσ ≫ α))) =
      classYα (jacobianGrp B hX hk f σ hσ).X L hL α (power C 1)
        (Additive.ofMul (coord C 1 0 ≫ abelJacobi B hX hk f σ hσ)) := by
    refine (schemePullbackClass_cubeBilin_classQ (jacobianGrp B hX hk f σ hσ).X L hL
      (doubleFirst C 0) _ _).trans ?_
    simp only [precompHom_apply, toMul_ofMul]
    rw [Stacks.QuadraticMap.cubeBilin_comm]
    congr 2
    · exact lift_coord_assoc (C := C) 2 _ 1 _
    · exact lift_coord_assoc (C := C) 2 _ 0 _
  rw [← e1]
  exact curveDeg_diagRestrict_of_eq B hX hk f σ hσ φ w
    (cubeBilin_jacobianPullback_eq B hX hk f σ hσ φ w hΛ hcl)

include hcl in
/-- **The trace of `φ^*` on the Jacobian is `1 + deg φ - V(φ)`**, for any invertible `L` on `J`
whose polarization class has classifying map `-𝟙_J` and with `deg aj^* L = dim J > 0`. -/
theorem abelianVarietyTrace_jacobianPullback
    (hg : 0 < Stacks.Groupoids.abelianVarietyDimension (jacobianGrp B hX hk f σ hσ).X)
    (hq : curveDeg (curveOver B hX hk f) (topologicalKrullDim_curveOver B hX hk f)
        (classQ (jacobianGrp B hX hk f σ hσ).X L hL
          (Additive.ofMul (coord (curveOver B hX hk f) 1 0 ≫ abelJacobi B hX hk f σ hσ))) =
      Stacks.Groupoids.abelianVarietyDimension (jacobianGrp B hX hk f σ hσ).X) :
    Stacks.Groupoids.abelianVarietyTrace (jacobianGrp B hX hk f σ hσ).X
        (jacobianPullback B hX hk f φ w σ hσ) =
      ((1 + (CurveGraph.curveMapDegree (B.inclusion.map f) φ w : ℤ) -
        CurveGraph.fixedPointIntersection (B.inclusion.map f)
          (topologicalKrullDim_left_le_one (curveOver B hX hk f)) φ w : ℤ) : ℚ) := by
  rw [abelianVarietyTrace_eq_curveDeg (curveOver B hX hk f)
    (topologicalKrullDim_curveOver B hX hk f)
    (curvePowerZeroBasePoint B hX hk f σ hσ) (jacobianGrp B hX hk f σ hσ).X
    (abelJacobi B hX hk f σ hσ) L hL
    (curvePowerZeroBasePoint_comp_abelJacobi B hX hk f σ hσ) hg
    (cubeBilin_abelJacobi_eq_graphCorrespondence B hX hk f σ hσ hΛ hcl) hq,
    curveDeg_classYα_jacobianPullback B hX hk f σ hσ φ w hΛ hcl]

end Stacks.PicardFunctor

end
