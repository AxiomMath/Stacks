module

public import StacksFrontier.AlgebraicGeometry.SectionRingProjTheta.TwistRemark

/-!
# The twist square of Stacks Tag 01QK for nonnegative twists

In the situation of Stacks Tag 01QH, with `θ_𝓕 : f^*M̃ ⟶ 𝓕` the comparison of Stacks Tag 01QJ
(`Stacks.SectionRingProjQuasicoherent.pullbackTildeComparison`), this file proves that the square
of Stacks Tag 01QK commutes for every natural number `n`: `θ_𝓕 ⊗ θ_{𝓛^{⊗ n}}` is the pullback of
the multiplication `M̃ ⊗ 𝒪_Y(n) ⟶ M(n)~` of Equation 01MQ followed by `θ_{𝓕 ⊗ 𝓛^{⊗ n}}`, read
through the obvious identification `M(n) = Γ_*(X, 𝓛, 𝓕 ⊗ 𝓛^{⊗ n})`, with `𝓛^{⊗ n}` the iterated
tensor power. The square is checked on fractions over the basic opens `D₊(s)`
(`twistSquare_basicOpen`) and glued over the good charts.

The statement for every integer `n` and Tag 01CU's powers `𝓛^{⊗ n}` is
`Stacks.SectionRingProjTheta.twistSquareInt`.

## Main results

* `Stacks.SectionRingProjTheta.twistSquare`: the square commutes, for `n : ℕ`.

## References

* [Stacks Project, Tag 01QK](https://stacks.math.columbia.edu/tag/01QK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory TopologicalSpace Opposite
open Stacks.TensorPowers (natTensorPow)
open Stacks.GradedSections (powSections sectionRing mul)
open Stacks.TwistedSections (twistPow twistSections twistModule moduleGrading)
open Stacks.AmpleFiniteAvoidance (nvOpen grading)
open Stacks.SectionRingProjMorphism (projHomOfIsAmple)
open Stacks.SectionRingProjQuasicoherent (tildeFunctor pullbackTildeFunctor
  pullbackTildeComparison gluedComparison GoodChart localDivision unitSec powMul tildeModule)
open scoped TensorProduct
open AlgebraicGeometry.ProjectiveSpectrum.Proj (degreeZeroFraction)

universe u

namespace Stacks.SectionRingProjTheta

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

attribute [local instance] ProjectiveSpectrum.isPrime

variable {X : Scheme.{u}} (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
  (hL : Stacks.Ample.IsAmple X L)






open AlgebraicGeometry.ProjectiveSpectrum.Proj (associatedModuleSheafStandardOpenEquiv) in
/-- **Every section of `(Γ_*(X, 𝓛, 𝓖))~` over `D₊(s)` is a fraction `t / sᵖ`** of a twisted
section `t ∈ Γ(X, 𝓖 ⊗ 𝓛^{⊗ p d})`, for `s` of degree `d > 0`. -/
theorem exists_twistSection_fraction (G : X.Modules) {d : ℕ} (s₀ : powSections L d) (hd : 0 < d)
    (y : Γ((tildeFunctor L).obj G,
      ProjectiveSpectrum.basicOpen (grading L) (DirectSum.of (powSections L) d s₀))) :
    ∃ (p : ℕ) (t : twistSections G L (p * d))
      (h : DirectSum.of (twistSections G L) (p * d) t ∈ moduleGrading G L (p • (d : ℤ))),
      y = (associatedModuleSheafStandardOpenEquiv (grading L) (moduleGrading G L)
        (Stacks.ExternalGrading.of_mem_summand d s₀) hd).symm
          (degreeZeroFraction (grading L) (moduleGrading G L)
            (Stacks.ExternalGrading.of_mem_summand d s₀) p _ h) := by
  have h2 := AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeZeroFraction_surjective
    (grading L) (moduleGrading G L) (Stacks.ExternalGrading.of_mem_summand d s₀)
  have h3 := h2 (associatedModuleSheafStandardOpenEquiv (grading L)
    (moduleGrading G L) (Stacks.ExternalGrading.of_mem_summand d s₀) hd y)
  clear h2
  obtain ⟨p, h4⟩ := h3
  obtain ⟨m, h5⟩ := h4
  obtain ⟨hm, ha⟩ := h5
  have hy := ((congrArg (associatedModuleSheafStandardOpenEquiv (grading L)
    (moduleGrading G L) (Stacks.ExternalGrading.of_mem_summand d s₀) hd).symm ha).trans
    ((associatedModuleSheafStandardOpenEquiv (grading L)
      (moduleGrading G L) (Stacks.ExternalGrading.of_mem_summand d s₀) hd).symm_apply_apply y))
  clear ha
  subst hy
  have hidx : p • (d : ℤ) = ((p * d : ℕ) : ℤ) := by push_cast; rw [nsmul_eq_mul]
  have hm' : m ∈ moduleGrading G L ((p * d : ℕ) : ℤ) := hidx ▸ hm
  obtain ⟨t, ht⟩ := hm'
  subst ht
  exact ⟨p, t, hm, rfl⟩

/-- An isomorphism of modules on `Proj`, applied after its inverse, on sections. -/
theorem hom_app_inv_app {A B : (AlgebraicGeometry.Proj (grading L)).Modules} (φ : A ⟶ B) [IsIso φ]
    (U : (AlgebraicGeometry.Proj (grading L)).Opens) (y : B.val.obj (op U)) :
    φ.val.app (op U) ((inv φ).val.app (op U) y) = y :=
  congrArg (fun ψ : B ⟶ B => (ψ.val.app (op U)).hom y) (IsIso.inv_hom_id φ)

open AlgebraicGeometry.ProjectiveSpectrum.Proj (associatedModuleSheafStandardOpenEquiv) in
/-- **The square on a standard open `D₊(s)`**, after the reduction to fractions. -/
theorem twistSquare_basicOpen (F : X.Modules) (n : ℕ) {d : ℕ} (s₀ : powSections L d)
    (hd : 0 < d) (hU : nvOpen L s₀ ≤ nvOpen L s₀)
    (a : Γ((tildeFunctor L).obj F,
      ProjectiveSpectrum.basicOpen (grading L) (DirectSum.of (powSections L) d s₀)))
    (b : Γ(twistY L n,
      ProjectiveSpectrum.basicOpen (grading L) (DirectSum.of (powSections L) d s₀))) :
    Stacks.SectionTensorFormula.tensorSection F (natTensorPow L n)
        (localDivision L F s₀ hU
          (associatedModuleSheafStandardOpenEquiv (grading L)
            (moduleGrading F L) (Stacks.ExternalGrading.of_mem_summand d s₀) hd a))
        (localDivision L (natTensorPow L n) s₀ hU
          (associatedModuleSheafStandardOpenEquiv (grading L)
            (moduleGrading (natTensorPow L n) L)
            (Stacks.ExternalGrading.of_mem_summand d s₀) hd
            ((inv (unitSheafNat L n)).val.app
              (op (ProjectiveSpectrum.basicOpen (grading L) (DirectSum.of (powSections L) d s₀)))
              b))) =
      localDivision L (F ⊗ natTensorPow L n) s₀ hU
        (associatedModuleSheafStandardOpenEquiv (grading L)
          (moduleGrading (F ⊗ natTensorPow L n) L)
          (Stacks.ExternalGrading.of_mem_summand d s₀) hd
          ((inv (identSheafNat L F n)).val.app
            (op (ProjectiveSpectrum.basicOpen (grading L) (DirectSum.of (powSections L) d s₀)))
            ((Stacks.AlgebraicGeometry.ProjShifted.moduleTwistMap
              (grading L) (moduleGrading F L) n).val.app
              (op (ProjectiveSpectrum.basicOpen (grading L) (DirectSum.of (powSections L) d s₀)))
              (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection
                (AlgebraicGeometry.Proj (grading L)).toRingedSpace _ _
                (op (ProjectiveSpectrum.basicOpen (grading L) (DirectSum.of (powSections L) d s₀)))
                (a ⊗ₜ b))))) := by
  have ea := exists_twistSection_fraction L F s₀ hd a
  obtain ⟨p, ea⟩ := ea
  obtain ⟨t, ea⟩ := ea
  obtain ⟨hm, ha⟩ := ea
  subst ha
  have eb := exists_twistSection_fraction L (natTensorPow L n) s₀ hd
    ((inv (unitSheafNat L n)).val.app
      (op (ProjectiveSpectrum.basicOpen (grading L) (DirectSum.of (powSections L) d s₀))) b)
  obtain ⟨q, eb⟩ := eb
  obtain ⟨t', eb⟩ := eb
  obtain ⟨ht', hw⟩ := eb
  have hb := (hom_app_inv_app L (unitSheafNat L n) _ b).symm.trans
    ((congrArg (fun y => (unitSheafNat L n).val.app
      (op (ProjectiveSpectrum.basicOpen (grading L) (DirectSum.of (powSections L) d s₀))) y)
        hw).trans
      (associatedModuleSheafMap_fraction (grading L) (moduleGrading (natTensorPow L n) L)
        (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistGrading (grading L) n)
        (unitShiftLinearMap L n) (unitShiftLinearMap_mem n)
        (Stacks.ExternalGrading.of_mem_summand d s₀) hd q _ ht'))
  subst hb
  have hr := unitShiftLinearMap_mem n _ _ ht'
  have hrm : unitShiftLinearMap L n (DirectSum.of (twistSections (natTensorPow L n) L) (q * d) t') •
      DirectSum.of (twistSections F L) (p * d) t ∈
        Stacks.GradedModule.shiftedGrading (moduleGrading F L) n ((p + q) • (d : ℤ)) := by
    rw [unitShiftLinearMap_apply, unitShiftHom_of, Stacks.TwistedSections.of_smul_of]
    refine mem_moduleGrading_of_eq (L := L) ?_
      ((Stacks.TwistedSections.mem_moduleGrading_natCast_iff (F := F) (L := L)).2 ⟨_, rfl⟩)
    push_cast
    rw [nsmul_eq_mul]
    push_cast
    ring
  have e4 := moduleTwistMap_fraction (grading L) (moduleGrading F L) (n : ℤ)
    (Stacks.ExternalGrading.of_mem_summand d s₀) hd p q _ hm _ hr hrm
  have ex := identNat_surjective F n ((p + q) • (d : ℤ))
    (nsmul_nonneg (Int.natCast_nonneg d) _) _ hrm
  obtain ⟨x, ex⟩ := ex
  obtain ⟨hx, hxe⟩ := ex
  have hidx : (p + q) • (d : ℤ) = (((p + q) * d : ℕ) : ℤ) := by rw [nsmul_eq_mul]; push_cast; ring
  have hx' : x ∈ moduleGrading (F ⊗ natTensorPow L n) L (((p + q) * d : ℕ) : ℤ) := hidx ▸ hx
  obtain ⟨z, hz⟩ := hx'
  subst hz
  have : IsIso (Stacks.AlgebraicGeometry.ProjSheafFunctoriality.associatedModuleSheafMap
      (grading L) (moduleGrading (F ⊗ natTensorPow L n) L)
      (Stacks.GradedModule.shiftedGrading (moduleGrading F L) n) (identNat F n)
      (identNat_mem F n)) := isIso_identSheafNat L F n
  have e5 := (congrArg (fun y => (inv (identSheafNat L F n)).val.app
      (op (ProjectiveSpectrum.basicOpen (grading L) (DirectSum.of (powSections L) d s₀)))
      ((associatedModuleSheafStandardOpenEquiv (grading L)
        (Stacks.GradedModule.shiftedGrading (moduleGrading F L) n)
        (Stacks.ExternalGrading.of_mem_summand d s₀) hd).symm y))
    (Stacks.Veronese.degreeZeroFraction_congr (grading L)
      (Stacks.GradedModule.shiftedGrading (moduleGrading F L) n)
      (Stacks.ExternalGrading.of_mem_summand d s₀) rfl hxe.symm hrm
      (identNat_mem F n _ _ hx))).trans
    (inv_app_fraction L (moduleGrading (F ⊗ natTensorPow L n) L)
      (Stacks.GradedModule.shiftedGrading (moduleGrading F L) n) (identNat F n) (identNat_mem F n)
      (Stacks.ExternalGrading.of_mem_summand d s₀) hd (p + q) _ hx)
  have h1 : unitShiftLinearMap L n (DirectSum.of (twistSections (natTensorPow L n) L) (q * d) t') =
      DirectSum.of (powSections L) (n + q * d)
        (t' ≫ eqToHom (twistPow_natTensorPow L n (q * d))) :=
    unitShiftHom_of n (q * d) t'
  have h2 := hxe.trans (congrArg (· • DirectSum.of (twistSections F L) (p * d) t) h1)
  have hz0 := eq_extProd_of_ident F t t' _ z (by ring) h1 h2
  have hz : Stacks.TwistedSections.twistCongr (Nat.mul_comm (p + q) d) z =
      (λ_ (𝟙_ X.Modules)).inv ≫ (Stacks.TwistedSections.twistCongr (Nat.mul_comm p d) t ⊗ₘ
        Stacks.TwistedSections.twistCongr (Nat.mul_comm q d) t') ≫
          extProd F (natTensorPow L n) (d * p) (d * q) ≫
            eqToHom (congrArg (twistPow (F ⊗ natTensorPow L n) L)
              ((Nat.add_comm (d * q) (d * p)).trans (Nat.mul_add d p q).symm)) := by
    rw [reassoc_of% (twistCongr_tensorHom_extProd F (natTensorPow L n) (Nat.mul_comm p d)
      (Nat.mul_comm q d) t t'), hz0]
    simp [Stacks.TwistedSections.twistCongr]
  have key := tensorSection_localDivision L F (natTensorPow L n) s₀ hU p q
    (degreeZeroFraction (grading L) (moduleGrading F L)
      (Stacks.ExternalGrading.of_mem_summand d s₀) p _ hm)
    (degreeZeroFraction (grading L) (moduleGrading (natTensorPow L n) L)
      (Stacks.ExternalGrading.of_mem_summand d s₀) q _ ht')
    (degreeZeroFraction (grading L) (moduleGrading (F ⊗ natTensorPow L n) L)
      (Stacks.ExternalGrading.of_mem_summand d s₀) (p + q) _ hx) t t' z rfl rfl rfl hz
  have l1 := (associatedModuleSheafStandardOpenEquiv (grading L) (moduleGrading F L)
    (Stacks.ExternalGrading.of_mem_summand d s₀) hd).apply_symm_apply
      (degreeZeroFraction (grading L) (moduleGrading F L)
        (Stacks.ExternalGrading.of_mem_summand d s₀) p _ hm)
  have l2 := (congrArg (associatedModuleSheafStandardOpenEquiv (grading L)
    (moduleGrading (natTensorPow L n) L) (Stacks.ExternalGrading.of_mem_summand d s₀) hd) hw).trans
      ((associatedModuleSheafStandardOpenEquiv (grading L) (moduleGrading (natTensorPow L n) L)
        (Stacks.ExternalGrading.of_mem_summand d s₀) hd).apply_symm_apply
        (degreeZeroFraction (grading L) (moduleGrading (natTensorPow L n) L)
          (Stacks.ExternalGrading.of_mem_summand d s₀) q _ ht'))
  have l3 := (congrArg (fun y => associatedModuleSheafStandardOpenEquiv (grading L)
      (moduleGrading (F ⊗ natTensorPow L n) L) (Stacks.ExternalGrading.of_mem_summand d s₀) hd
      ((inv (identSheafNat L F n)).val.app
        (op (ProjectiveSpectrum.basicOpen (grading L) (DirectSum.of (powSections L) d s₀))) y))
      e4).trans ((congrArg (associatedModuleSheafStandardOpenEquiv (grading L)
      (moduleGrading (F ⊗ natTensorPow L n) L) (Stacks.ExternalGrading.of_mem_summand d s₀) hd)
        e5).trans ((associatedModuleSheafStandardOpenEquiv (grading L)
          (moduleGrading (F ⊗ natTensorPow L n) L)
          (Stacks.ExternalGrading.of_mem_summand d s₀) hd).apply_symm_apply _))
  exact ((congrArg₂ (fun x y => Stacks.SectionTensorFormula.tensorSection F (natTensorPow L n)
    (localDivision L F s₀ hU x) (localDivision L (natTensorPow L n) s₀ hU y)) l1 l2).trans
      key).trans (congrArg (localDivision L (F ⊗ natTensorPow L n) s₀ hU) l3).symm

variable [IsOpenImmersion (projHomOfIsAmple L hL)] in
/-- **The square on a chart**, after the reduction to fractions. -/
theorem twistSquare_chart (F : X.Modules) (n : ℕ) (c : GoodChart L hL)
    (a : Γ((tildeFunctor L).obj F, chartOpen L hL c)) (b : Γ(twistY L n, chartOpen L hL c)) :
    Stacks.SectionTensorFormula.tensorSection F (natTensorPow L n)
        (localDivision L F c.1.val le_rfl
          (ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv (grading L)
            (moduleGrading F L) (Stacks.ExternalGrading.of_mem_summand c.1.deg c.1.val)
            c.1.deg_pos a))
        (localDivision L (natTensorPow L n) c.1.val le_rfl
          (ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv (grading L)
            (moduleGrading (natTensorPow L n) L)
            (Stacks.ExternalGrading.of_mem_summand c.1.deg c.1.val) c.1.deg_pos
            (Scheme.Modules.Hom.app (inv (unitSheafNat L n)) (chartOpen L hL c) b))) =
      localDivision L (F ⊗ natTensorPow L n) c.1.val le_rfl
        (ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv (grading L)
          (moduleGrading (F ⊗ natTensorPow L n) L)
          (Stacks.ExternalGrading.of_mem_summand c.1.deg c.1.val) c.1.deg_pos
          (Scheme.Modules.Hom.app (inv (identSheafNat L F n)) (chartOpen L hL c)
            (Scheme.Modules.Hom.app (Stacks.AlgebraicGeometry.ProjShifted.moduleTwistMap
              (grading L) (moduleGrading F L) n) (chartOpen L hL c)
              (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection
                (AlgebraicGeometry.Proj (grading L)).toRingedSpace _ _
                (op (chartOpen L hL c)) (a ⊗ₜ b))))) :=
  twistSquare_basicOpen L F n c.1.val c.1.deg_pos le_rfl a b

/-- **`θ_{𝓛^{⊗ n}}`, read on `f^*𝒪_Y(n)`**: Tag 01QJ's comparison for `𝓛^{⊗ n}`, precomposed with
the pullback of the identification `𝒪_Y(n) ≅ (Γ_*(X, 𝓛, 𝓛^{⊗ n}))~`. Assertion (i) of Stacks Tag
01QK is that this is the map `f^*𝒪_Y(n) ⟶ 𝓛^{⊗ n}` of Stacks Tag 01QI. -/
def twistTheta (n : ℕ) :
    (Scheme.Modules.pullback (projHomOfIsAmple L hL)).obj (twistY L n) ⟶ natTensorPow L n :=
  (Scheme.Modules.pullback (projHomOfIsAmple L hL)).map (inv (unitSheafNat L n)) ≫
    (pullbackTildeComparison L hL).app (natTensorPow L n)

/-- **Assertion (ii) of Stacks Tag 01QK: the twist square commutes.** For every
`𝒪_X`-module `𝓕` and every `n ≥ 0`,

```
      f^*M̃ ⊗ f^*𝒪_Y(n)  ──twistTop──▶  f^*(M(n)~)  ──≅──▶  f^*(Γ_*(X, 𝓛, 𝓕 ⊗ 𝓛^{⊗ n}))~
           │                                                        │
   θ_𝓕 ⊗ θ_{𝓛^{⊗ n}}                                        θ_{𝓕 ⊗ 𝓛^{⊗ n}}
           ▼                                                        ▼
       𝓕 ⊗ 𝓛^{⊗ n}  ═══════════════════ id ═══════════════════  𝓕 ⊗ 𝓛^{⊗ n}
```

commutes, where `θ` is Tag 01QJ's comparison `pullbackTildeComparison`, the top arrow is the
pullback of Equation 01MQ's multiplication (`twistTop`), and the identification
`M(n) = Γ_*(X, 𝓛, 𝓕 ⊗ 𝓛^{⊗ n})` is `identSheafNat`. -/
theorem twistSquare (F : X.Modules) (n : ℕ) :
    ((pullbackTildeComparison L hL).app F ⊗ₘ twistTheta L hL n) =
      twistTop L hL F n ≫
        (Scheme.Modules.pullback (projHomOfIsAmple L hL)).map (inv (identSheafNat L F n)) ≫
        (pullbackTildeComparison L hL).app (F ⊗ natTensorPow L n) := by
  have := Stacks.SectionRingProjImmersion.isOpenImmersion_projHomOfIsAmple L hL
  refine monoidal_hom_ext_of_isBasis (fun c : GoodChart L hL => nvOpen L c.1.val)
    (Stacks.SectionRingProjQuasicoherent.isBasis_goodChart L hL) fun c x y => ?_
  obtain ⟨a, rfl⟩ := pullbackSection_surjective L hL _ c x
  obtain ⟨b, rfl⟩ := pullbackSection_surjective L hL _ c y
  refine (tensorHom_app_pullbackSection L hL F (natTensorPow L n) c (inv (unitSheafNat L n)) a
    b).trans (Eq.trans ?_ (twistTop_comp_app_pullbackSection L hL F (F ⊗ natTensorPow L n) n c
      (inv (identSheafNat L F n)) a b).symm)
  exact twistSquare_chart L hL F n c a b

end Stacks.SectionRingProjTheta

end
