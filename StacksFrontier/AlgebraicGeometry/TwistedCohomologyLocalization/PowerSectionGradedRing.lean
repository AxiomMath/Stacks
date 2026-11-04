module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SectionPowerSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.NonvanishingSections

/-!
# The morphism representing `sⁿ` and the `n`-th power in the graded section ring

Let `X` be a scheme, `ℒ` an invertible `𝒪_X`-module and `s` a global section of `ℒ`. The morphism
`Stacks.SheafOfModules.sectionPowerHom : 𝒪_X ⟶ ℒ^{⊗ n}` is defined by the recursion `s⁰ = 𝟙`,
`sⁿ⁺¹ = sⁿ ⊗ s` of [Stacks, Tag 01CU], and `Stacks.SheafOfModules.homogeneousSection X ℒ s ^ n`
is the `n`-th power of `s` in the graded section ring `Γ_*(X, ℒ) = ⨁_{n ≥ 0} Γ(X, ℒ^{⊗ n})` of
[Stacks, Tag 01CV]. This file shows that the value of the morphism on the unit global section is
the degree-`n` homogeneous component of the ring-theoretic power.

## Main definitions

* `Stacks.Cohomology.PowerSection.powerSectionValue`: the value on the unit global section of the
  morphism representing `sⁿ`, a global section of `ℒ^{⊗ n}`.

## Main results

* `Stacks.Cohomology.PowerSection.powerSectionValue_one`: in degree one it is `s` itself, read
  through the comparison `ℒ^{⊗ 1} ≅ ℒ`.
* `Stacks.Cohomology.PowerSection.powerSectionValue_succ`: it satisfies the recursion of the
  graded section ring.
* `Stacks.Cohomology.PowerSection.of_powerSectionValue`: the degree-`n` homogeneous element it
  determines is the `n`-th power of `Stacks.SheafOfModules.homogeneousSection` in `Γ_*(X, ℒ)`.
* `Stacks.Cohomology.PowerSection.powerSectionValue_add`: it is multiplicative in `n`.
* `Stacks.Cohomology.PowerSection.sectionPowerAction_sectionHom_powerSectionValue`:
  multiplication by the morphism representing `sⁿ` is multiplication by the global section
  `powerSectionValue X L s n`.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 09MR](https://stacks.math.columbia.edu/tag/09MR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Stacks.SheafOfModules Stacks.SheafOfModules.TwistAction
open Stacks.SheafOfModules.TensorSheafification
open scoped DirectSum

universe u

namespace Stacks.Cohomology.PowerSection

attribute [local implicit_reducible] _root_.SheafOfModules.forget
  PresheafOfModules.restrictScalars TensorSheafification.structureSheaf

variable (X : Scheme.{u})
  (L : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
  [IsInvertible X.presheaf
    (structureSheafRing X.toRingedSpace).property L]

attribute [local instance] Stacks.SheafOfModules.tensorRightEquiv

/-- The terminal open of `X`, at which global sections are taken. -/
abbrev terminalOpen := op (⊤_ (TopologicalSpace.Opens X.toRingedSpace.toPresheafedSpace))

/-- The degree-`n` homogeneous component `Γ(X, ℒ^{⊗ n})` of the graded section ring. -/
abbrev piece (n : ℕ) : Type u :=
  (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L
    (n : ℤ)).val.obj (terminalOpen X)

/-- The value on the unit global section of the morphism `sectionPowerHom` representing `sⁿ`, a
global section of `ℒ^{⊗ n}`. -/
def powerSectionValue (s : L.sections) (n : ℕ) : piece X L n :=
  (sectionPowerHom (sectionSiteRing X) (sectionSiteSheaf X) L s n).val.app (terminalOpen X)
    (1 : (sectionSiteRing X).obj (terminalOpen X))

/-- The value of the morphism representing `s⁰` is the unit section. -/
theorem powerSectionValue_zero (s : L.sections) :
    powerSectionValue X L s 0 = (1 : (sectionSiteRing X).obj (terminalOpen X)) := rfl

/-- The graded unit of the section ring, as a homogeneous element of degree zero, is the unit of
the ring. -/
theorem of_zero_one :
    (DirectSum.of _ 0 (1 : (sectionSiteRing X).obj (terminalOpen X)) :
      sectionRing (sectionSiteRing X) (sectionSiteSheaf X) L) = 1 := by
  rw [← sectionRingGradedOne_eq (sectionSiteRing X) (sectionSiteSheaf X) L]
  rfl

/-- The product of two homogeneous elements `a`, `b` of the section ring is the homogeneous
element `sectionRingMul … n m a b` of degree `n + m`. -/
theorem of_mul_of (n m : ℕ) (a : piece X L n) (b : piece X L m) :
    (DirectSum.of _ n a : sectionRing (sectionSiteRing X) (sectionSiteSheaf X) L) *
        DirectSum.of _ m b =
      DirectSum.of _ (n + m)
        (sectionRingMul (sectionSiteRing X) (sectionSiteSheaf X) L n m a b) := by
  rw [DirectSum.of_mul_of]
  exact congrArg (DirectSum.of _ (n + m))
    ((chosenRingStructure (sectionSiteRing X) (sectionSiteSheaf X) L).mul_eq n m a b)

/-- Multiplying a section `b` of `ℒ^{⊗ m}` on the left by the unit section gives `b` back, up to
the reindexing comparison `ℒ^{⊗ (0 + m)} ≅ ℒ^{⊗ m}`. -/
theorem reindex_mulSectionAt_zero_left (m : ℤ)
    (b : (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L m).val.obj
      (terminalOpen X)) :
    (TensorPower.tensorPowerReindex (sectionSiteRing X) (sectionSiteSheaf X) L
        (Int.zero_add m)).hom.val.app (terminalOpen X)
      (tensorPowerMulSectionAt (sectionSiteRing X) (sectionSiteSheaf X) (terminalOpen X) L 0 m
        (1 : (sectionSiteRing X).obj (terminalOpen X)) b) = b := by
  have he := TensorPower.coherentMulIso_zero_left (sectionSiteRing X) (sectionSiteSheaf X) L m
  have h := tensorSections_leftUnitorAt (sectionSiteRing X) (sectionSiteSheaf X) (terminalOpen X)
    (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L m) b
  rw [← he] at h
  exact h

/-- Multiplying a section of `ℒ^{⊗ 1}` on the left by the unit section gives it back. -/
theorem mulSectionAt_zero_left_one (b : piece X L 1) :
    tensorPowerMulSectionAt (sectionSiteRing X) (sectionSiteSheaf X) (terminalOpen X) L 0 1
      (1 : (sectionSiteRing X).obj (terminalOpen X)) b = b := by
  have h := reindex_mulSectionAt_zero_left X L 1 b
  rwa [reindexAt_self] at h

/-- The value of the morphism representing `sⁿ⁺¹` is the product of the value in degree `n` with
`s`, read through the comparison `ℒ^{⊗ 1} ≅ ℒ`. -/
private theorem powerSectionValue_succ_eq_mulSectionAt (s : L.sections) (n : ℕ) :
    powerSectionValue X L s (n + 1) =
      tensorPowerMulSectionAt (sectionSiteRing X) (sectionSiteSheaf X) (terminalOpen X) L
        (n : ℤ) 1 (powerSectionValue X L s n)
        ((TensorPower.tensorPowerOneIso (sectionSiteRing X) (sectionSiteSheaf X) L).inv.val.app
          (terminalOpen X) (s.eval (terminalOpen X))) :=
  SectionPower.sectionPowerSucc_app_one (sectionSiteRing X) (sectionSiteSheaf X) L s (n : ℤ)
    (sectionPowerHom (sectionSiteRing X) (sectionSiteSheaf X) L s n) (terminalOpen X)

/-- In degree one, the value of the morphism representing `s¹` is `s`, read through the
comparison `ℒ^{⊗ 1} ≅ ℒ`. -/
theorem powerSectionValue_one (s : L.sections) :
    powerSectionValue X L s 1 = (TensorPower.tensorPowerOneIso (sectionSiteRing X)
      (sectionSiteSheaf X) L).inv.val.app (terminalOpen X) (s.eval (terminalOpen X)) := by
  exact (powerSectionValue_succ_eq_mulSectionAt X L s 0).trans (mulSectionAt_zero_left_one X L _)

/-- The degree-one homogeneous element determined by the morphism representing `s¹` is
`Stacks.SheafOfModules.homogeneousSection`. -/
theorem of_powerSectionValue_one (s : L.sections) :
    (DirectSum.of _ 1 (powerSectionValue X L s 1) :
      sectionRing (sectionSiteRing X) (sectionSiteSheaf X) L) = homogeneousSection X L s :=
  congrArg (DirectSum.of _ 1) (powerSectionValue_one X L s)

/-- The value of the morphism representing `sⁿ⁺¹` is the product `sectionRingMul` of the values in
degrees `n` and `1`. -/
theorem powerSectionValue_succ (s : L.sections) (n : ℕ) :
    powerSectionValue X L s (n + 1) =
      sectionRingMul (sectionSiteRing X) (sectionSiteSheaf X) L n 1
        (powerSectionValue X L s n) (powerSectionValue X L s 1) := by
  rw [sectionRingMul_eq, reindexAt_self]
  rw [powerSectionValue_succ_eq_mulSectionAt, ← powerSectionValue_one]
  rfl

/-- The degree-`n` homogeneous element determined by the value of the morphism representing `sⁿ`
is the `n`-th power of `Stacks.SheafOfModules.homogeneousSection` in `Γ_*(X, ℒ)`. -/
theorem of_powerSectionValue (s : L.sections) (n : ℕ) :
    (DirectSum.of _ n (powerSectionValue X L s n) :
      sectionRing (sectionSiteRing X) (sectionSiteSheaf X) L) =
      homogeneousSection X L s ^ n := by
  induction n with
  | zero =>
      rw [pow_zero]
      exact of_zero_one X L
  | succ n ih =>
      rw [pow_succ, ← ih, ← of_powerSectionValue_one X L s, of_mul_of, ← powerSectionValue_succ]

/-- The values of the morphisms representing the powers of `s` are multiplicative: the value at
`k + m` is the product of the values at `k` and at `m`. -/
theorem powerSectionValue_add (s : L.sections) (k m : ℕ) :
    powerSectionValue X L s (k + m) =
      tensorPowerMulSectionAt (sectionSiteRing X) (sectionSiteSheaf X) (terminalOpen X) L
        (k : ℤ) (m : ℤ)
        (powerSectionValue X L s k) (powerSectionValue X L s m) := by
  have h : (DirectSum.of _ (k + m) (powerSectionValue X L s (k + m)) :
      sectionRing (sectionSiteRing X) (sectionSiteSheaf X) L) =
      DirectSum.of _ (k + m) (sectionRingMul (sectionSiteRing X) (sectionSiteSheaf X) L k m
        (powerSectionValue X L s k) (powerSectionValue X L s m)) := by
    rw [← of_mul_of, of_powerSectionValue, of_powerSectionValue, of_powerSectionValue, pow_add]
  rw [DirectSum.of_injective (β := fun n : ℕ => piece X L n) (k + m) h, sectionRingMul_eq,
    reindexAt_self]

/-- Multiplication by the morphism representing `sⁿ` is multiplication by the global section
`powerSectionValue X L s n` of `ℒ^{⊗ n}`. -/
theorem sectionPowerAction_sectionHom_powerSectionValue (s : L.sections) (F : X.Modules)
    (n : ℕ) :
    sectionPowerAction (sectionSiteRing X) (sectionSiteSheaf X) L F (n : ℤ)
        (globalSectionHom (sectionSiteRing X) (sectionSiteSheaf X)
          (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ))
          (powerSectionValue X L s n)) =
      sectionPowerAction (sectionSiteRing X) (sectionSiteSheaf X) L F (n : ℤ)
        (sectionPowerHom (sectionSiteRing X) (sectionSiteSheaf X) L s n) :=
  SectionPower.sectionPowerAction_congr (sectionSiteRing X) (sectionSiteSheaf X) L F (n : ℤ)
    (globalSectionHom_apply (sectionSiteRing X) (sectionSiteSheaf X) _ (powerSectionValue X L s n))

end Stacks.Cohomology.PowerSection

end
