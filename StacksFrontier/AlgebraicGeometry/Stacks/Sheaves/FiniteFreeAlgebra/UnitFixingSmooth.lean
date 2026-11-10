module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.RingHom.Smooth
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.UnitFixingGroupScheme

/-!
# The unit-fixing subgroup of `GL_d` is smooth over the integers

The functor in groups `G(T) = {g ∈ GL_d(Γ(T, 𝒪_T)) | g(e_1) = e_1}` is the closed subgroup
scheme of `GL_d` cut out by `x_{11} = 1` and `x_{i1} = 0` for `i > 1`. This file proves that `G`
is a smooth affine group scheme over `Spec(ℤ)` (Stacks 05YQ).

## Main results

* `AlgebraicGeometry.FiniteFreeAlgebra.formallySmooth_unitFixingCoordinateRing`: the coordinate
  ring of `G` is formally smooth over the integers.
* `AlgebraicGeometry.FiniteFreeAlgebra.finitePresentation_unitFixingCoordinateRing`: it is of
  finite presentation over the integers.
* `AlgebraicGeometry.FiniteFreeAlgebra.smooth_unitFixingCoordinateRing`: it is smooth over the
  integers.
* `AlgebraicGeometry.FiniteFreeAlgebra.smooth_unitFixingScheme`: **the scheme `G` is smooth over
  `Spec(ℤ)`**.

## References

* [Stacks Project, Tag 00TN](https://stacks.math.columbia.edu/tag/00TN)
* [Stacks Project, Tag 022W](https://stacks.math.columbia.edu/tag/022W)
* [Stacks Project, Tag 05YQ](https://stacks.math.columbia.edu/tag/05YQ)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **A unit modulo a square-zero ideal is a unit.** If `φ` is a surjective ring homomorphism
whose kernel has square zero and `φ x` is a unit, then `x` is a unit. -/
theorem isUnit_of_isUnit_map_of_ker_sq_eq_bot {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (hsurj : Function.Surjective φ) (hsq : RingHom.ker φ ^ 2 = ⊥)
    {x : R} (h : IsUnit (φ x)) : IsUnit x := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨y, hy⟩ := hsurj ↑u⁻¹
  have hxy : φ (x * y) = 1 := by
    rw [map_mul, ← hu, hy]
    exact u.mul_inv
  have hmem : x * y - 1 ∈ RingHom.ker φ := by
    rw [RingHom.mem_ker, map_sub, hxy, map_one, sub_self]
  have hnil : IsNilpotent (x * y - 1) := ⟨2, by simpa [hsq] using Ideal.pow_mem_pow hmem 2⟩
  have hone : IsUnit (x * y) := by simpa using hnil.isUnit_one_add
  exact isUnit_of_mul_isUnit_left hone

namespace FiniteFreeAlgebra

variable (d : ℕ) [NeZero d]

/-- The substitution replacing the first column of the generic `d` by `d` matrix by the first
standard basis vector, as an endomorphism of the generic matrix ring over the integers.

Geometrically it is the linear projection of `𝔸^{d^2}` onto the subspace cut out by the
unit-fixing relations. -/
noncomputable def unitFixingSubstitution :
    MvPolynomial (Fin d × Fin d) (ULift.{u} ℤ) →ₐ[ULift.{u} ℤ]
      MvPolynomial (Fin d × Fin d) (ULift.{u} ℤ) :=
  MvPolynomial.aeval fun ij =>
    if ij.2 = 0 then (if ij.1 = 0 then 1 else 0) else MvPolynomial.X ij

/-- The substitution sends the first-column variable `x_{i1}` to `1` or `0`. -/
private theorem unitFixingSubstitution_X_zero (i : Fin d) :
    unitFixingSubstitution.{u} d (MvPolynomial.X (i, 0)) = if i = 0 then 1 else 0 := by
  simp [unitFixingSubstitution]

/-- **The substitution is the identity modulo the unit-fixing relations.** -/
theorem mk_comp_unitFixingSubstitution :
    (Ideal.Quotient.mkₐ (ULift.{u} ℤ) (Ideal.span (unitFixingRelations.{u} d))).comp
        ((IsScalarTower.toAlgHom (ULift.{u} ℤ)
            (MvPolynomial (Fin d × Fin d) (ULift.{u} ℤ))
            (generalLinearCoordinateRing.{u} d)).comp (unitFixingSubstitution.{u} d)) =
      (Ideal.Quotient.mkₐ (ULift.{u} ℤ) (Ideal.span (unitFixingRelations.{u} d))).comp
        (IsScalarTower.toAlgHom (ULift.{u} ℤ)
          (MvPolynomial (Fin d × Fin d) (ULift.{u} ℤ))
          (generalLinearCoordinateRing.{u} d)) := by
  classical
  refine MvPolynomial.algHom_ext fun ij => ?_
  obtain ⟨i, j⟩ := ij
  by_cases hj : j = 0
  · subst hj
    simp only [AlgHom.comp_apply, unitFixingSubstitution_X_zero]
    rw [show (IsScalarTower.toAlgHom (ULift.{u} ℤ)
          (MvPolynomial (Fin d × Fin d) (ULift.{u} ℤ))
          (generalLinearCoordinateRing.{u} d)) (MvPolynomial.X (i, (0 : Fin d))) =
            generalLinearCoordinate.{u} d i 0 from rfl,
      show (Ideal.Quotient.mkₐ (ULift.{u} ℤ) (Ideal.span (unitFixingRelations.{u} d)))
          (generalLinearCoordinate.{u} d i 0) =
        Ideal.Quotient.mk (Ideal.span (unitFixingRelations.{u} d))
          (generalLinearCoordinate.{u} d i 0) from rfl,
      quotientMk_generalLinearCoordinate d i]
    split <;> simp
  · have hL : (unitFixingSubstitution.{u} d) (MvPolynomial.X (i, j)) =
        MvPolynomial.X (i, j) := by
      simp only [unitFixingSubstitution, MvPolynomial.aeval_X, ite_eq_right hj]
    simp only [AlgHom.comp_apply, hL]

/-- **The coordinate ring of the unit-fixing subgroup is formally smooth over the integers.** -/
theorem formallySmooth_unitFixingCoordinateRing :
    Algebra.FormallySmooth (ULift.{u} ℤ) (unitFixingCoordinateRing.{u} d) := by
  classical
  have hPsm : Algebra.FormallySmooth (ULift.{u} ℤ)
      (MvPolynomial (Fin d × Fin d) (ULift.{u} ℤ)) := inferInstance
  have hloc : Algebra.FormallySmooth (MvPolynomial (Fin d × Fin d) (ULift.{u} ℤ))
      (generalLinearCoordinateRing.{u} d) :=
    Algebra.FormallySmooth.of_isLocalization
      (Submonoid.powers (generalLinearDeterminant.{u} d))
  have hRsm : Algebra.FormallySmooth (ULift.{u} ℤ) (generalLinearCoordinateRing.{u} d) :=
    Algebra.FormallySmooth.comp (ULift.{u} ℤ)
      (MvPolynomial (Fin d × Fin d) (ULift.{u} ℤ)) (generalLinearCoordinateRing.{u} d)
  let f : generalLinearCoordinateRing.{u} d →ₐ[ULift.{u} ℤ] unitFixingCoordinateRing.{u} d :=
    Ideal.Quotient.mkₐ (ULift.{u} ℤ) (Ideal.span (unitFixingRelations.{u} d))
  have hfsurj : Function.Surjective f := Ideal.Quotient.mk_surjective
  have hliftsurj : Function.Surjective f.kerSquareLift := by
    intro x
    obtain ⟨r, hr⟩ := hfsurj x
    exact ⟨Ideal.Quotient.mk _ r, (AlgHom.kerSquareLift_mk f r).trans hr⟩
  have hkersq : RingHom.ker f.kerSquareLift.toRingHom ^ 2 = ⊥ := by
    rw [AlgHom.ker_kerSquareLift]
    exact Ideal.cotangentIdeal_square _
  let τ : MvPolynomial (Fin d × Fin d) (ULift.{u} ℤ) →ₐ[ULift.{u} ℤ]
      generalLinearCoordinateRing.{u} d ⧸ RingHom.ker f.toRingHom ^ 2 :=
    (Ideal.Quotient.mkₐ (ULift.{u} ℤ) (RingHom.ker f.toRingHom ^ 2)).comp
      ((IsScalarTower.toAlgHom (ULift.{u} ℤ)
        (MvPolynomial (Fin d × Fin d) (ULift.{u} ℤ))
        (generalLinearCoordinateRing.{u} d)).comp (unitFixingSubstitution.{u} d))
  have hτ (p : MvPolynomial (Fin d × Fin d) (ULift.{u} ℤ)) :
      f.kerSquareLift (τ p) =
        f (IsScalarTower.toAlgHom (ULift.{u} ℤ)
          (MvPolynomial (Fin d × Fin d) (ULift.{u} ℤ))
          (generalLinearCoordinateRing.{u} d) p) := by
    have h1 : f.kerSquareLift (τ p) =
        f ((IsScalarTower.toAlgHom (ULift.{u} ℤ)
          (MvPolynomial (Fin d × Fin d) (ULift.{u} ℤ))
          (generalLinearCoordinateRing.{u} d)).comp (unitFixingSubstitution.{u} d) p) :=
      AlgHom.kerSquareLift_mk f _
    rw [h1]
    exact congrFun (congrArg (fun q : MvPolynomial (Fin d × Fin d) (ULift.{u} ℤ) →ₐ[ULift.{u} ℤ]
      unitFixingCoordinateRing.{u} d => (q : _ → _)) (mk_comp_unitFixingSubstitution.{u} d)) p
  have hdet : IsUnit (τ (generalLinearDeterminant.{u} d)) := by
    refine isUnit_of_isUnit_map_of_ker_sq_eq_bot f.kerSquareLift.toRingHom hliftsurj hkersq ?_
    rw [show f.kerSquareLift.toRingHom (τ (generalLinearDeterminant.{u} d)) =
      f.kerSquareLift (τ (generalLinearDeterminant.{u} d)) from rfl,
      hτ (generalLinearDeterminant.{u} d)]
    exact (IsLocalization.Away.algebraMap_isUnit
      (S := generalLinearCoordinateRing.{u} d) (generalLinearDeterminant.{u} d)).map f
  let σ : generalLinearCoordinateRing.{u} d →ₐ[ULift.{u} ℤ]
      generalLinearCoordinateRing.{u} d ⧸ RingHom.ker f.toRingHom ^ 2 :=
    IsLocalization.Away.liftAlgHom (generalLinearDeterminant.{u} d) hdet
  have hσalg (p : MvPolynomial (Fin d × Fin d) (ULift.{u} ℤ)) :
      σ (algebraMap (MvPolynomial (Fin d × Fin d) (ULift.{u} ℤ))
        (generalLinearCoordinateRing.{u} d) p) = τ p :=
    IsLocalization.Away.lift_eq (generalLinearDeterminant.{u} d) hdet p
  have hcomp (r : generalLinearCoordinateRing.{u} d) : f.kerSquareLift (σ r) = f r := by
    have hring : (f.kerSquareLift.toRingHom.comp σ.toRingHom) = f.toRingHom := by
      refine IsLocalization.ringHom_ext
        (Submonoid.powers (generalLinearDeterminant.{u} d)) ?_
      refine RingHom.ext fun p => ?_
      change f.kerSquareLift (σ (algebraMap _ _ p)) = f (algebraMap _ _ p)
      rw [hσalg p]
      exact hτ p
    exact congrFun (congrArg (fun q : generalLinearCoordinateRing.{u} d →+*
      unitFixingCoordinateRing.{u} d => (q : _ → _)) hring) r
  have hIker : Ideal.span (unitFixingRelations.{u} d) ≤ RingHom.ker σ.toRingHom := by
    rw [Ideal.span_le]
    rintro x ⟨k, rfl⟩
    have hX : σ (generalLinearCoordinate.{u} d k 0) =
        (if k = 0 then (1 : generalLinearCoordinateRing.{u} d ⧸ RingHom.ker f.toRingHom ^ 2)
          else 0) := by
      rw [show generalLinearCoordinate.{u} d k 0 =
        algebraMap (MvPolynomial (Fin d × Fin d) (ULift.{u} ℤ))
          (generalLinearCoordinateRing.{u} d) (MvPolynomial.X (k, (0 : Fin d))) from rfl,
        hσalg]
      change (Ideal.Quotient.mkₐ (ULift.{u} ℤ) (RingHom.ker f.toRingHom ^ 2))
        ((IsScalarTower.toAlgHom (ULift.{u} ℤ) _ _)
          ((unitFixingSubstitution.{u} d) (MvPolynomial.X (k, (0 : Fin d))))) = _
      rw [unitFixingSubstitution_X_zero]
      split <;> simp only [map_one, map_zero]
    have hite : σ ((if k = 0 then 1 else 0 : generalLinearCoordinateRing.{u} d)) =
        (if k = 0 then (1 : generalLinearCoordinateRing.{u} d ⧸ RingHom.ker f.toRingHom ^ 2)
          else 0) := by
      split <;> simp only [map_one, map_zero]
    change σ _ = 0
    rw [map_sub, hX, hite, sub_self]
  have hI0 : ∀ a ∈ Ideal.span (unitFixingRelations.{u} d), σ a = 0 := fun _ ha => hIker ha
  rw [Algebra.FormallySmooth.iff_split_surjection f hfsurj]
  refine ⟨Ideal.Quotient.liftₐ (Ideal.span (unitFixingRelations.{u} d)) σ hI0,
    AlgHom.ext fun x => ?_⟩
  obtain ⟨r, hr⟩ := hfsurj x
  subst hr
  exact hcomp r

/-- **The coordinate ring of the unit-fixing subgroup is of finite presentation over the
integers.** -/
theorem finitePresentation_unitFixingCoordinateRing :
    Algebra.FinitePresentation (ULift.{u} ℤ) (unitFixingCoordinateRing.{u} d) := by
  have h2 : Algebra.FinitePresentation (MvPolynomial (Fin d × Fin d) (ULift.{u} ℤ))
      (generalLinearCoordinateRing.{u} d) :=
    IsLocalization.Away.finitePresentation (generalLinearDeterminant.{u} d)
  have h3 : Algebra.FinitePresentation (ULift.{u} ℤ) (generalLinearCoordinateRing.{u} d) :=
    Algebra.FinitePresentation.trans (ULift.{u} ℤ)
      (MvPolynomial (Fin d × Fin d) (ULift.{u} ℤ)) (generalLinearCoordinateRing.{u} d)
  exact Algebra.FinitePresentation.quotient (Submodule.fg_span (Set.finite_range _))

/-- **The coordinate ring of the unit-fixing subgroup is smooth over the integers.** -/
theorem smooth_unitFixingCoordinateRing :
    Algebra.Smooth (ULift.{u} ℤ) (unitFixingCoordinateRing.{u} d) where
  formallySmooth := formallySmooth_unitFixingCoordinateRing.{u} d
  finitePresentation := finitePresentation_unitFixingCoordinateRing.{u} d

/-- **Part of Stacks 05YQ: the group `G` is smooth over `Spec(ℤ)`.** The unit-fixing subgroup
scheme of `GL_d` is a smooth affine scheme over the integers. -/
theorem smooth_unitFixingScheme :
    Smooth (specULiftZIsTerminal.from (unitFixingScheme.{u} d)) := by
  have he : specULiftZIsTerminal.from (unitFixingScheme.{u} d) =
      Spec.map (CommRingCat.ofHom
        (algebraMap (ULift.{u} ℤ) (unitFixingCoordinateRing.{u} d))) :=
    specULiftZIsTerminal.hom_ext _ _
  rw [he, HasRingHomProperty.Spec_iff (P := @Smooth)]
  exact RingHom.smooth_algebraMap.mpr (smooth_unitFixingCoordinateRing.{u} d)

end FiniteFreeAlgebra

end AlgebraicGeometry

end
