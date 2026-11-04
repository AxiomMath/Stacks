module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.RingCohomologyMapConstruction
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# The base-change map of a ring square as a base change of modules

For a square of rings `R → A`, `R → R'`, `A → A'`, `R' → A'`, a complex `K` of `A`-modules and a
map `K ⊗^L_A A' ⟶ K'`, the map of Stacks 0DJ7 in degree `n`,

`H^n(K ⊗^L_R R') ⊗_{A ⊗_R R'} A' ⟶ H^n(K')`,

is an isomorphism exactly when `H^n(K ⊗^L_R R') ⟶ H^n(K')` exhibits its target as the base
change of its source along `A ⊗_R R' ⟶ A'`.

## Main results

* `RingTheory.TorIndependence.isIso_ringBaseChangeCohomologyMap_iff_isBaseChange`: the base-change
  map in degree `n` is an isomorphism if and only if the comparison map is a base change.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings

universe u

namespace RingTheory.TorIndependence

attribute [local instance] HasDerivedCategory.standard

variable {R A R' A' : Type u}
  [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
  [Algebra R A] [Algebra R R'] [Algebra R A']
  [Algebra A A'] [Algebra R' A']
  [IsScalarTower R A A'] [IsScalarTower R R' A']

variable (K : DerivedCategory (ModuleCat.{u} A)) (K' : DerivedCategory (ModuleCat.{u} A'))
  (φ : (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
    (algebraMap A A')).functor.obj K ⟶ K') (n : ℤ)

/-- The base-change map `H^n(K ⊗^L_R R') ⊗_{A ⊗_R R'} A' ⟶ H^n(K')` is an isomorphism if and
only if the comparison map `H^n(K ⊗^L_R R') ⟶ H^n(K')` exhibits `H^n(K')` as the base change of
`H^n(K ⊗^L_R R')` along `A ⊗_R R' ⟶ A'`. -/
theorem isIso_ringBaseChangeCohomologyMap_iff_isBaseChange :
    letI := (baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A')).toAlgebra
    letI : IsScalarTower (A ⊗[R] R') A'
        ((ModuleCat.restrictScalars (baseChangeTensorRingMap (R := R) (A := A) (R' := R')
          (A' := A'))).obj ((DerivedCategory.homologyFunctor (ModuleCat.{u} A') n).obj K')) :=
      ⟨fun b a x =>
        mul_smul (baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A') b) a x⟩
    IsIso (ringBaseChangeCohomologyMap (R := R) (R' := R') K K' φ n) ↔
      IsBaseChange A' (cohomologyComparisonLinearMap (R := R) (R' := R') K K' φ n).hom := by
  let := (baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A')).toAlgebra
  let : IsScalarTower (A ⊗[R] R') A'
      ((ModuleCat.restrictScalars (baseChangeTensorRingMap (R := R) (A := A) (R' := R')
        (A' := A'))).obj ((DerivedCategory.homologyFunctor (ModuleCat.{u} A') n).obj K')) :=
    ⟨fun b a x => mul_smul (baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A') b) a x⟩
  set b := ringBaseChangeCohomologyMap (R := R) (R' := R') K K' φ n
  set l := (cohomologyComparisonLinearMap (R := R) (R' := R') K K' φ n).hom
  have hb : ∀ (a : A') (m : baseChangeCohomologyCat (R := R) (R' := R') K n),
      b.hom (a ⊗ₜ[A ⊗[R] R', baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A')] m) =
        a • l m := by
    intro a m
    have h3 := ModuleCat.ExtendScalars.smul_tmul
      (baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A')) a (1 : A') m
    rw [mul_one] at h3
    exact (congrArg b.hom h3.symm).trans ((b.hom.map_smul a _).trans
      (congrArg (a • ·) (ringBaseChangeCohomologyMap_one_tmul (R := R) (R' := R') K K' φ n m)))
  refine ⟨fun _ => IsBaseChange.of_equiv (asIso b).toLinearEquiv
    fun m => (hb 1 m).trans (one_smul _ _), fun hbc => ?_⟩
  let e := hbc.equiv
  have hfe : ∀ x, b.hom x = e x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact (map_zero b.hom).trans (map_zero e).symm
    | tmul a m => exact (hb a m).trans (IsBaseChange.equiv_tmul hbc a m).symm
    | add x y hx hy =>
      exact (map_add b.hom x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add e x y).symm)
  rw [ConcreteCategory.isIso_iff_bijective,
    show (ConcreteCategory.hom b : _ → _) = e from funext hfe]
  exact e.bijective

end RingTheory.TorIndependence
