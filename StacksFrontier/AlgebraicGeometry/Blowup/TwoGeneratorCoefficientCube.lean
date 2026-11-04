module

public import StacksFrontier.AlgebraicGeometry.Blowup.TwoGeneratorCoefficientBaseChange

/-!
# The cube of two-generator squares attached to a morphism of coefficient algebras

Let `A` be a ring with two elements `f₁, f₂`, and let `B`, `B'` be two `A`-algebras with an
`A`-algebra map `φ : B →ₐ[A] B'`.  Over each of `A`, `B`, `B'` there is the two-generator almost
blowup square of [Stacks, Example 0EVH] at the images of `f₁, f₂`, and
`StacksFrontier/AlgebraicGeometry/Blowup/TwoGeneratorCoefficientBaseChange.lean` exhibits each corner
over `B` as the base change along `Spec B ⟶ Spec A` of the corresponding corner over `A`.

This file supplies the four morphisms from the corners over `B'` to the corners over `B` that
`φ` induces, and the four side faces of the resulting cube.  The square over `B'` is the
*canonical* one, at the generators `algebraMap A B' fᵢ`, and not the coefficient extension of the
square over `B` along `φ`, whose generators would be `φ (algebraMap A B fᵢ)`: those elements are
equal but not syntactically, and the two-generator square depends on its generators.  So the
four morphisms are not built from `φ` directly but obtained by the universal property of the
cartesian squares over `B`: each corner over `B` is a fibre product of the corner over `A` with
`Spec B` (or, for the exceptional line, with the centre over `B`), and the morphism from the
corner over `B'` is the pair of its coefficient morphism to the corner over `A` and its structure
morphism followed by the morphism one level down.  Every commutativity is then a uniqueness
statement for morphisms into a fibre product.

## Main definitions

* `Stacks.AlmostBlowUp.coeffCubeBase`, `…coeffCubeCenter`, `…coeffCubeModification` and
  `…coeffCubeExceptional`: the four morphisms of the cube.

## Main results

* `Stacks.AlmostBlowUp.coeffCubeBase_comp`, `…coeffCubeCenter_comp`,
  `…coeffCubeModification_comp` and `…coeffCubeExceptional_comp`: each of them, followed by the
  coefficient morphism of `B` over `A`, is the coefficient morphism of `B'` over `A`.
* `Stacks.AlmostBlowUp.coeffCube_sb`, `…_sz`, `…_se` and `…_sq`: the four side faces of the cube.

## References

* [Stacks Project, Example 0EVH](https://stacks.math.columbia.edu/tag/0EVH)
* [Stacks Project, Tag 0EXD](https://stacks.math.columbia.edu/tag/0EXD)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry CommRingCat
open Stacks.ProjectiveCohomology

universe u

namespace Stacks.AlmostBlowUp

attribute [local instance] MvPolynomial.gradedAlgebra

variable (A : Type u) [CommRing A] (f₁ f₂ : A) {B B' : Type u} [CommRing B] [CommRing B']
  [Algebra A B] [Algebra A B'] (φ : B →ₐ[A] B')

/-- The morphism of bases of the cube: `Spec φ`. -/
def coeffCubeBase : Spec (.of B') ⟶ Spec (.of B) :=
  Spec.map (ofHom φ.toRingHom)

/-- `Spec φ` followed by the structure morphism of `B` is the structure morphism of `B'`. -/
@[reassoc]
theorem coeffCubeBase_comp :
    coeffCubeBase A φ ≫ Spec.map (ofHom (algebraMap A B)) =
      Spec.map (ofHom (algebraMap A B')) := by
  rw [coeffCubeBase, ← Spec.map_comp, ← ofHom_comp]
  congr 2
  exact φ.comp_algebraMap

/-- **The morphism of centres of the cube**, by the universal property of the centre over `B` as
a fibre product. -/
def coeffCubeCenter :
    Spec (.of (centerRing B' (algebraMap A B' f₁) (algebraMap A B' f₂))) ⟶
      Spec (.of (centerRing B (algebraMap A B f₁) (algebraMap A B f₂))) :=
  (isPullback_centerToBase_coeff A B f₁ f₂).lift
    (centerToBase B' (algebraMap A B' f₁) (algebraMap A B' f₂) ≫ coeffCubeBase A φ)
    (Spec.map (ofHom (centerCoeffHom A B' f₁ f₂)))
    (by rw [Category.assoc, coeffCubeBase_comp, (isPullback_centerToBase_coeff A B' f₁ f₂).w])

/-- The side face of the cube at the centre: `z' ≫ Spec φ = κ_Z ≫ z`. -/
@[reassoc]
theorem coeffCube_sz :
    centerToBase B' (algebraMap A B' f₁) (algebraMap A B' f₂) ≫ coeffCubeBase A φ =
      coeffCubeCenter A f₁ f₂ φ ≫ centerToBase B (algebraMap A B f₁) (algebraMap A B f₂) :=
  ((isPullback_centerToBase_coeff A B f₁ f₂).lift_fst _ _ _).symm

/-- The morphism of centres followed by the coefficient morphism of `B` is that of `B'`. -/
@[reassoc]
theorem coeffCubeCenter_comp :
    coeffCubeCenter A f₁ f₂ φ ≫ Spec.map (ofHom (centerCoeffHom A B f₁ f₂)) =
      Spec.map (ofHom (centerCoeffHom A B' f₁ f₂)) :=
  (isPullback_centerToBase_coeff A B f₁ f₂).lift_snd _ _ _

/-- **The morphism of modifications of the cube**, by the universal property of the modification
over `B` as a fibre product. -/
def coeffCubeModification :
    letI := (twoGeneratorSquare B' (algebraMap A B' f₁) (algebraMap A B' f₂)).modificationGraded
    letI := (twoGeneratorSquare B (algebraMap A B f₁) (algebraMap A B f₂)).modificationGraded
    AlgebraicGeometry.Proj (modificationGrading B' (algebraMap A B' f₁) (algebraMap A B' f₂)) ⟶
      AlgebraicGeometry.Proj (modificationGrading B (algebraMap A B f₁) (algebraMap A B f₂)) :=
  letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
  letI := (twoGeneratorSquare B' (algebraMap A B' f₁) (algebraMap A B' f₂)).modificationGraded
  letI := (twoGeneratorSquare B (algebraMap A B f₁) (algebraMap A B f₂)).modificationGraded
  (isPullback_modificationToBase_coeff A B f₁ f₂).lift
    (modificationToBase B' (algebraMap A B' f₁) (algebraMap A B' f₂) ≫ coeffCubeBase A φ)
    (modificationCoeffProjMap A B' f₁ f₂)
    (by rw [Category.assoc, coeffCubeBase_comp,
      (isPullback_modificationToBase_coeff A B' f₁ f₂).w])

/-- The side face of the cube at the modification: `b' ≫ Spec φ = κ_{X'} ≫ b`. -/
@[reassoc]
theorem coeffCube_sb :
    letI := (twoGeneratorSquare B' (algebraMap A B' f₁) (algebraMap A B' f₂)).modificationGraded
    letI := (twoGeneratorSquare B (algebraMap A B f₁) (algebraMap A B f₂)).modificationGraded
    modificationToBase B' (algebraMap A B' f₁) (algebraMap A B' f₂) ≫ coeffCubeBase A φ =
      coeffCubeModification A f₁ f₂ φ ≫
        modificationToBase B (algebraMap A B f₁) (algebraMap A B f₂) :=
  let := (twoGeneratorSquare A f₁ f₂).modificationGraded
  let := (twoGeneratorSquare B' (algebraMap A B' f₁) (algebraMap A B' f₂)).modificationGraded
  let := (twoGeneratorSquare B (algebraMap A B f₁) (algebraMap A B f₂)).modificationGraded
  ((isPullback_modificationToBase_coeff A B f₁ f₂).lift_fst _ _ _).symm

/-- The morphism of modifications followed by the coefficient morphism of `B` is that of `B'`. -/
@[reassoc]
theorem coeffCubeModification_comp :
    letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
    letI := (twoGeneratorSquare B' (algebraMap A B' f₁) (algebraMap A B' f₂)).modificationGraded
    letI := (twoGeneratorSquare B (algebraMap A B f₁) (algebraMap A B f₂)).modificationGraded
    coeffCubeModification A f₁ f₂ φ ≫ modificationCoeffProjMap A B f₁ f₂ =
      modificationCoeffProjMap A B' f₁ f₂ :=
  let := (twoGeneratorSquare A f₁ f₂).modificationGraded
  let := (twoGeneratorSquare B' (algebraMap A B' f₁) (algebraMap A B' f₂)).modificationGraded
  let := (twoGeneratorSquare B (algebraMap A B f₁) (algebraMap A B f₂)).modificationGraded
  (isPullback_modificationToBase_coeff A B f₁ f₂).lift_snd _ _ _

/-- **The morphism of exceptional lines of the cube**, by the universal property of the
exceptional line over `B` as a fibre product over the centres. -/
def coeffCubeExceptional :
    AlgebraicGeometry.Proj (exceptionalGrading B' (algebraMap A B' f₁) (algebraMap A B' f₂)) ⟶
      AlgebraicGeometry.Proj (exceptionalGrading B (algebraMap A B f₁) (algebraMap A B f₂)) :=
  (isPullback_exceptionalToCenter_coeff A B f₁ f₂).lift
    (exceptionalToCenter B' (algebraMap A B' f₁) (algebraMap A B' f₂) ≫
      coeffCubeCenter A f₁ f₂ φ)
    (projModelMap 1 (centerCoeffHom A B' f₁ f₂))
    (by rw [Category.assoc, coeffCubeCenter_comp,
      (isPullback_exceptionalToCenter_coeff A B' f₁ f₂).w])

/-- The side face of the cube at the exceptional line over the centre: `e' ≫ κ_Z = κ_E ≫ e`. -/
@[reassoc]
theorem coeffCube_se :
    exceptionalToCenter B' (algebraMap A B' f₁) (algebraMap A B' f₂) ≫
        coeffCubeCenter A f₁ f₂ φ =
      coeffCubeExceptional A f₁ f₂ φ ≫
        exceptionalToCenter B (algebraMap A B f₁) (algebraMap A B f₂) :=
  ((isPullback_exceptionalToCenter_coeff A B f₁ f₂).lift_fst _ _ _).symm

/-- The morphism of exceptional lines followed by the coefficient morphism of `B` is that of
`B'`. -/
@[reassoc]
theorem coeffCubeExceptional_comp :
    coeffCubeExceptional A f₁ f₂ φ ≫ projModelMap 1 (centerCoeffHom A B f₁ f₂) =
      projModelMap 1 (centerCoeffHom A B' f₁ f₂) :=
  (isPullback_exceptionalToCenter_coeff A B f₁ f₂).lift_snd _ _ _

/-- The side face of the cube at the exceptional line inside the modification:
`q' ≫ κ_{X'} = κ_E ≫ q`.  Both sides are morphisms into the modification over `B`, which is a
fibre product, so they are compared after its two projections. -/
@[reassoc]
theorem coeffCube_sq :
    letI := (twoGeneratorSquare B' (algebraMap A B' f₁) (algebraMap A B' f₂)).modificationGraded
    letI := (twoGeneratorSquare B (algebraMap A B f₁) (algebraMap A B f₂)).modificationGraded
    exceptionalToModification B' (algebraMap A B' f₁) (algebraMap A B' f₂) ≫
        coeffCubeModification A f₁ f₂ φ =
      coeffCubeExceptional A f₁ f₂ φ ≫
        exceptionalToModification B (algebraMap A B f₁) (algebraMap A B f₂) := by
  let := (twoGeneratorSquare A f₁ f₂).modificationGraded
  let := (twoGeneratorSquare B' (algebraMap A B' f₁) (algebraMap A B' f₂)).modificationGraded
  let := (twoGeneratorSquare B (algebraMap A B f₁) (algebraMap A B f₂)).modificationGraded
  refine (isPullback_modificationToBase_coeff A B f₁ f₂).hom_ext ?_ ?_
  · rw [Category.assoc, ← coeffCube_sb, ← Category.assoc,
      (twoGenerator_isPullback B' (algebraMap A B' f₁) (algebraMap A B' f₂)).w, Category.assoc,
      coeffCube_sz, ← Category.assoc, coeffCube_se, Category.assoc, Category.assoc,
      ← (twoGenerator_isPullback B (algebraMap A B f₁) (algebraMap A B f₂)).w]
  · rw [Category.assoc, coeffCubeModification_comp,
      exceptionalToModification_comp_modificationCoeffProjMap, Category.assoc,
      exceptionalToModification_comp_modificationCoeffProjMap, ← Category.assoc,
      coeffCubeExceptional_comp]

end Stacks.AlmostBlowUp

end
