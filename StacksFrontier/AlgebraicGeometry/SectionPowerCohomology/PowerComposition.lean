module

public import StacksFrontier.AlgebraicGeometry.Properties.PrincipalOpens.GradedSectionInjective
public import StacksFrontier.AlgebraicGeometry.TwistedCohomologyLocalization.GradedModule
public import StacksFrontier.AlgebraicGeometry.TwistedCohomologyLocalization.PowerSectionGradedRing
import all StacksFrontier.AlgebraicGeometry.Properties.PrincipalOpens.GradedSectionInjective

/-!
# Multiplying by two powers of a section in turn

Let `X` be a scheme, `ℒ` an invertible `𝒪_X`-module, `s ∈ Γ(X, ℒ)` and `𝒢` an `𝒪_X`-module.
This file computes multiplication `𝒢 ⟶ 𝒢 ⊗ ℒ^{⊗ k}` by a power `sᵏ` on sections over an arbitrary
open, in terms of the section `sᵏ|_U` of `ℒ^{⊗ k}`, and composes two such multiplications.

## Main results

* `Stacks.SheafOfModules.SectionPowerComposition.powerSectionValue_eq_sectionPower`: the value of
  the morphism representing `sᵏ` on the unit section is the `k`-th power of `s` in the graded
  section ring.
* `Stacks.SheafOfModules.SectionPowerComposition.mul_app`: multiplication by `sᵏ` sends a section
  `x` over `U` to `x ⊗ sᵏ|_U`.
* `Stacks.SheafOfModules.SectionPowerComposition.mul_comp`: multiplying by `sᵃ` and then by `sᵇ` is
  multiplying by `s^{a + b}`, after the identification
  `(𝒢 ⊗ ℒ^{⊗ a}) ⊗ ℒ^{⊗ b} ≅ 𝒢 ⊗ ℒ^{⊗ (a + b)}`.
* `Stacks.SheafOfModules.SectionPowerComposition.map_eq_zero_of_le`: on cohomology a class killed
  by `sᵃ` is killed by every higher power of `s`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.Cohomology Stacks.Cohomology.TwistedGradedModule

universe u

namespace Stacks.SheafOfModules.SectionPowerComposition

attribute [local implicit_reducible] _root_.SheafOfModules.forget
  PresheafOfModules.restrictScalars TensorSheafification.structureSheaf

variable (X : Scheme.{u})
  (L : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
  [IsInvertible X.presheaf (structureSheafRing X.toRingedSpace).property L]

attribute [local instance] Stacks.SheafOfModules.tensorRightEquiv

variable (s : L.sections)

/-- Multiplication by `sᵏ`, the morphism `𝒢 ⟶ 𝒢 ⊗ ℒ^{⊗ k}`. -/
abbrev mul (G : X.Modules) (k : ℕ) : G ⟶ twist X L G (k : ℤ) :=
  sectionPowerAction (sectionSiteRing X) (sectionSiteSheaf X) L G (k : ℤ)
    (sectionPowerHom (sectionSiteRing X) (sectionSiteSheaf X) L s k)

/-- The value of the morphism representing `sᵏ` on the unit global section is the `k`-th power
of `s` in the graded section ring. -/
theorem powerSectionValue_eq_sectionPower (k : ℕ) :
    Stacks.Cohomology.PowerSection.powerSectionValue X L s k = sectionPower X L s k :=
  DirectSum.of_injective (β := fun n : ℕ =>
      (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ)).val.obj
        (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace)))) k
    ((Stacks.Cohomology.PowerSection.of_powerSectionValue X L s k).trans
      (homogeneousSection_pow_eq_of_sectionPower X L s k))

/-- The value over an open `U` of the morphism representing `sᵏ` on the unit section is the
restriction of `sᵏ` to `U`. -/
theorem sectionPowerHom_app_one (k : ℕ) (U : Opens X.toRingedSpace) :
    (sectionPowerHom (sectionSiteRing X) (sectionSiteSheaf X) L s k).val.app (op U)
        (1 : (sectionSiteRing X).obj (op U)) =
      (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (k : ℤ)).val.map
        (terminal.from U).op (sectionPower X L s k) := by
  rw [TwistAction.unitHom_app_eq_map]
  exact congrArg (fun q =>
    (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (k : ℤ)).val.map
      (terminal.from U).op q) (powerSectionValue_eq_sectionPower X L s k)

/-- **Multiplication by `sᵏ` on sections**: a section `x` over `U` goes to `x ⊗ sᵏ|_U`. -/
theorem mul_app (G : X.Modules) (k : ℕ) (U : Opens X.toRingedSpace) (x : G.val.obj (op U)) :
    (mul X L s G k).val.app (op U) x =
      tensorSectionAtOpen X L G U k x
        ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (k : ℤ)).val.map
          (terminal.from U).op (sectionPower X L s k)) := by
  refine (SectionPower.sectionPowerAction_app (sectionSiteRing X) (sectionSiteSheaf X) L G
    (k : ℤ) _ (op U) x).trans ?_
  rw [sectionPowerHom_app_one]
  rfl

/-- The identification `(𝒢 ⊗ ℒ^{⊗ a}) ⊗ ℒ^{⊗ b} ≅ 𝒢 ⊗ ℒ^{⊗ (a + b)}`, as a morphism of
`𝒪_X`-modules. -/
abbrev assocHom (G : X.Modules) (a b : ℕ) :
    twist X L (twist X L G (a : ℤ)) (b : ℤ) ⟶ twist X L G ((a + b : ℕ) : ℤ) :=
  (twistedPowerAddIso X L G a b).hom

/-- **Multiplying by `sᵃ` and then by `sᵇ` is multiplying by `s^{a + b}`**, after the
identification `(𝒢 ⊗ ℒ^{⊗ a}) ⊗ ℒ^{⊗ b} ≅ 𝒢 ⊗ ℒ^{⊗ (a + b)}`. -/
theorem mul_comp (G : X.Modules) (a b : ℕ) :
    mul X L s G a ≫ mul X L s (twist X L G (a : ℤ)) b ≫ assocHom X L G a b =
      mul X L s G (a + b) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  obtain ⟨U⟩ := U
  ext x
  refine (congrArg (fun y => (twistedPowerAddIso X L G a b).hom.val.app (op U)
    ((mul X L s (twist X L G (a : ℤ)) b).val.app (op U) y)) (mul_app X L s G a U x)).trans ?_
  refine (congrArg (fun y => (twistedPowerAddIso X L G a b).hom.val.app (op U) y)
    (mul_app X L s (twist X L G (a : ℤ)) b U _)).trans ?_
  refine (twistSectionByPower_tensorSectionAtOpen X L G s a b U x _).trans ?_
  refine Eq.trans ?_ (mul_app X L s G (a + b) U x).symm
  exact congrArg (tensorSectionAtOpen X L G U (a + b) x)
    (sectionRingMulIso_sectionPower X L s U a b)

attribute [local instance] Stacks.SheafOfModules.sectionDegreeVAdd

/-- **On cohomology, `sᵇ (sᵃ ξ) = 0` forces `s^{a + b} ξ = 0`.** -/
theorem map_add_eq_zero (W : X.Opens) (p : ℕ) (G : X.Modules) (a b : ℕ)
    (ξ : Hgroup X.ringCatSheaf W p G)
    (h : (Hfunctor X.ringCatSheaf W p).map (mul X L s (twist X L G (a : ℤ)) b)
      ((Hfunctor X.ringCatSheaf W p).map (mul X L s G a) ξ) = 0) :
    (Hfunctor X.ringCatSheaf W p).map (mul X L s G (a + b)) ξ = 0 := by
  rw [← mul_comp]
  refine (map_comp_apply X.ringCatSheaf p W _ _ ξ).trans ?_
  refine (map_comp_apply X.ringCatSheaf p W _ _ _).trans ?_
  exact (congrArg _ h).trans (map_zero _)

/-- **On cohomology, `sᵃ ξ = 0` forces `sᵏ ξ = 0` for every `k ≥ a`.** -/
theorem map_eq_zero_of_le (W : X.Opens) (p : ℕ) (G : X.Modules) {a k : ℕ} (hak : a ≤ k)
    (ξ : Hgroup X.ringCatSheaf W p G)
    (h : (Hfunctor X.ringCatSheaf W p).map (mul X L s G a) ξ = 0) :
    (Hfunctor X.ringCatSheaf W p).map (mul X L s G k) ξ = 0 := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hak
  exact map_add_eq_zero X L s W p G a b ξ (by rw [h, map_zero])

end Stacks.SheafOfModules.SectionPowerComposition

end
