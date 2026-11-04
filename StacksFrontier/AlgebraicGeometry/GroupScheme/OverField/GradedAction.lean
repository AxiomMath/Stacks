module

public import Mathlib.RingTheory.GradedAlgebra.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Examples.Multiplicative
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.ModObj

/-!
# The multiplicative-group action associated to a graded ring

An integer grading on a commutative ring gives a coaction by Laurent polynomials, sending a
homogeneous element of degree `n` to `a ⊗ Tⁿ`, and hence an action of the multiplicative group
scheme on its spectrum.

## Main definitions

* `AlgebraicGeometry.gradedActionTensorMap` identifies the source's tensor product with the
  coordinate ring over the lifted integer base.
* `AlgebraicGeometry.GradedGmAction` records the source-ordered coaction and the induced
  group-scheme action, including the formula on homogeneous elements and the identification of
  the action morphism.

## Main results

* `ringHom_eq_of_homogeneous`: two ring maps out of a graded ring agree as soon as they agree
  on homogeneous elements.
* `AlgebraicGeometry.gradedGmAction` constructs the action for every integer-graded commutative
  ring.

## Implementation notes

The coaction `μ` has the source's tensor-factor order, `A ⊗ ℤ[T,T⁻¹]`.  The affine coordinate
ring of `Gₘ × Spec A` has the factors in the opposite order, so the action-morphism formula
uses the canonical tensor symmetry.  For `A : Type u`, the scheme construction uses the
universe-polymorphic integral model of the multiplicative group.  Only its integer base is
lifted; the coaction retains its source-ordered tensor product over `ℤ`, and the action is on
`Spec A`.

The module structure on the spectrum is transported from the opposite category of algebras by
`CategoryTheory.Functor.LaxMonoidal.modObj` along the monoidal functor `algSpec`.

## References

* [Stacks Project, Tag 0EKJ](https://stacks.math.columbia.edu/tag/0EKJ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v

/-- Two ring maps out of a graded ring agree when they agree on every homogeneous component. -/
theorem ringHom_eq_of_homogeneous
    {A B : Type*} [CommRing A] {σ : Type*} [SetLike σ A] [AddSubmonoidClass σ A]
    (𝒜 : ℤ → σ) [GradedRing 𝒜] [Semiring B]
    (f g : A →+* B) (h : ∀ (i : ℤ) (x : 𝒜 i), f x = g x) : f = g :=
  RingHom.ext <| DirectSum.Decomposition.inductionOn 𝒜 (by simp) (fun x => h _ x)
    fun _ _ hx hy => by simp [hx, hy]

namespace AlgebraicGeometry

attribute [local instance 100] ULift.algebra'

/-- Identify the source's tensor product with the coordinate ring over the lifted integer base.
The coefficient map is the canonical inclusion of integers, and `A` is unchanged. -/
noncomputable def gradedActionTensorMap (A : Type u) [CommRing A] :
    TensorProduct ℤ A (LaurentPolynomial ℤ) →+*
      TensorProduct (ULift.{u} ℤ) A (LaurentPolynomial (ULift.{u} ℤ)) :=
  (Algebra.TensorProduct.mapOfCompatibleSMul (ULift.{u} ℤ) ℤ ℤ A
    (LaurentPolynomial (ULift.{u} ℤ))).toRingHom.comp
    (Algebra.TensorProduct.map (AlgHom.id ℤ A)
      (AddMonoidAlgebra.mapAlgEquiv ℤ ℤ ULift.algEquiv.symm).toAlgHom).toRingHom

/-- The identification of coordinate rings sends `a ⊗ Tⁿ` to `a ⊗ Tⁿ`. -/
@[simp] theorem gradedActionTensorMap_tmul_T (A : Type u) [CommRing A] (a : A) (n : ℤ) :
    gradedActionTensorMap A (a ⊗ₜ[ℤ] LaurentPolynomial.T n) =
      a ⊗ₜ[ULift.{u} ℤ] LaurentPolynomial.T n := by
  simp [gradedActionTensorMap, LaurentPolynomial.T, AddMonoidAlgebra.mapAlgEquiv,
    -LaurentPolynomial.single_eq_C_mul_T]

/-- The Laurent-polynomial coaction of a grading, together with its induced action on the
spectrum. The equation on homogeneous elements specifies `μ` uniquely. -/
structure GradedGmAction {A : Type u} [CommRing A] {σ : Type v}
    [SetLike σ A] [AddSubmonoidClass σ A]
    (𝒜 : ℤ → σ) where
  /-- The coordinate-ring map `μ : A → A ⊗ ℤ[T,T⁻¹]` of the action. -/
  μ : A →+* TensorProduct ℤ A (LaurentPolynomial ℤ)
  /-- The group-scheme action on `Spec A`. -/
  action : ModObj
    (multiplicativeGroupULift.asOver (Spec (.of (ULift.{u} ℤ))))
    ((Spec (.of A)).asOver (Spec (.of (ULift.{u} ℤ))))
  /-- On a homogeneous element of degree `n`, the coaction is `a ⊗ Tⁿ`. -/
  μ_homogeneous : ∀ (n : ℤ) (a : A), a ∈ 𝒜 n →
    μ a = a ⊗ₜ[ℤ] (LaurentPolynomial.T n)
  /-- The action morphism is induced by the coaction under the affine fibre-product
  identification. -/
  action_eq_spec_map : action.smul.left =
    (pullbackSpecIso (ULift.{u} ℤ) (LaurentPolynomial (ULift.{u} ℤ)) A).hom ≫
      Spec.map (CommRingCat.ofHom
        ((Algebra.TensorProduct.comm (ULift.{u} ℤ) A
          (LaurentPolynomial (ULift.{u} ℤ))).toRingEquiv.toRingHom.comp
            ((gradedActionTensorMap A).comp μ)))

section Coaction

variable {A : Type u} [CommRing A] {σ : Type v} [SetLike σ A] [AddSubmonoidClass σ A]

/-- The Laurent-polynomial coaction of a grading, sending `a ∈ 𝒜 n` to `a ⊗ Tⁿ`. -/
noncomputable def gradedCoaction (𝒜 : ℤ → σ) [GradedRing 𝒜] :
    A →+* TensorProduct ℤ A (LaurentPolynomial ℤ) :=
  (DirectSum.toSemiring
    (fun n =>
      { toFun := fun a : 𝒜 n => (a : A) ⊗ₜ[ℤ] LaurentPolynomial.T n
        map_zero' := by simp
        map_add' := fun a b => by simp [TensorProduct.add_tmul] })
    (by simp [GradedMonoid.GOne.one, Algebra.TensorProduct.one_def])
    (by
      intro i j ai aj
      change ((ai : A) * (aj : A)) ⊗ₜ[ℤ] LaurentPolynomial.T (i + j) =
        ((ai : A) ⊗ₜ[ℤ] LaurentPolynomial.T i) *
          ((aj : A) ⊗ₜ[ℤ] LaurentPolynomial.T j)
      rw [Algebra.TensorProduct.tmul_mul_tmul, LaurentPolynomial.T_add])).comp
    (DirectSum.decomposeRingEquiv 𝒜).toRingHom

/-- The coaction of a grading sends a homogeneous element `a ∈ 𝒜 n` to `a ⊗ Tⁿ`. -/
theorem gradedCoaction_of_mem (𝒜 : ℤ → σ) [GradedRing 𝒜] {n : ℤ} {a : A} (ha : a ∈ 𝒜 n) :
    gradedCoaction 𝒜 a = a ⊗ₜ[ℤ] LaurentPolynomial.T n := by
  rw [gradedCoaction, RingHom.comp_apply]
  show DirectSum.toSemiring _ _ _ (DirectSum.decompose 𝒜 a) = _
  rw [DirectSum.decompose_of_mem 𝒜 ha, DirectSum.toSemiring_of]
  rfl

/-- The coaction of a grading as an algebra map over the lifted integer base, with the
Laurent-polynomial factor first. -/
noncomputable def gradedCoactionAlgHom (𝒜 : ℤ → σ) [GradedRing 𝒜] :
    A →ₐ[ULift.{u} ℤ] TensorProduct (ULift.{u} ℤ) (LaurentPolynomial (ULift.{u} ℤ)) A :=
  let φ : A →+* TensorProduct (ULift.{u} ℤ) (LaurentPolynomial (ULift.{u} ℤ)) A :=
    (Algebra.TensorProduct.comm (ULift.{u} ℤ) A
      (LaurentPolynomial (ULift.{u} ℤ))).toRingEquiv.toRingHom.comp
      ((gradedActionTensorMap A).comp (gradedCoaction 𝒜))
  AlgHom.mk φ (by
    rintro ⟨z⟩
    change φ (z : A) = (z : TensorProduct (ULift.{u} ℤ) (LaurentPolynomial (ULift.{u} ℤ)) A)
    exact map_intCast φ z)

/-- The coaction algebra map of a grading sends a homogeneous element `a ∈ 𝒜 n` to `Tⁿ ⊗ a`. -/
theorem gradedCoactionAlgHom_of_mem (𝒜 : ℤ → σ) [GradedRing 𝒜] {n : ℤ} {a : A} (ha : a ∈ 𝒜 n) :
    gradedCoactionAlgHom 𝒜 a = LaurentPolynomial.T n ⊗ₜ[ULift.{u} ℤ] a := by
  simp [gradedCoactionAlgHom, gradedCoaction_of_mem 𝒜 ha]

/-- The coaction of a grading is compatible with the counit of the Laurent polynomials. -/
theorem gradedCoactionAlgHom_counit (𝒜 : ℤ → σ) [GradedRing 𝒜] :
    ((Algebra.TensorProduct.map (Bialgebra.counitAlgHom (ULift.{u} ℤ)
        (LaurentPolynomial (ULift.{u} ℤ))) (AlgHom.id (ULift.{u} ℤ) A)).comp
          (gradedCoactionAlgHom 𝒜)).toRingHom =
      ((MonoidalCategoryStruct.leftUnitor (CommAlgCat.of (ULift.{u} ℤ) A)).inv.hom.toRingHom :
        A →+* TensorProduct (ULift.{u} ℤ) (ULift.{u} ℤ) A) := by
  apply ringHom_eq_of_homogeneous 𝒜
  intro n a
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.coe_comp,
    Function.comp_apply, gradedCoactionAlgHom_of_mem 𝒜 a.property,
    Algebra.TensorProduct.map_tmul, Bialgebra.counitAlgHom_apply, LaurentPolynomial.counit_T,
    AlgHom.coe_id, id_eq, CommAlgCat.coe_tensorObj, CommAlgCat.coe_tensorUnit]
  show (1 : ULift.{u} ℤ) ⊗ₜ[ULift.{u} ℤ] (a : A) =
    (Algebra.TensorProduct.lid (ULift.{u} ℤ) A).symm a
  apply (Algebra.TensorProduct.lid (ULift.{u} ℤ) A).injective
  simp

/-- The coaction of a grading is compatible with the comultiplication of the Laurent
polynomials. -/
theorem gradedCoactionAlgHom_comul (𝒜 : ℤ → σ) [GradedRing 𝒜] :
    ((Algebra.TensorProduct.map (Bialgebra.comulAlgHom (ULift.{u} ℤ)
        (LaurentPolynomial (ULift.{u} ℤ))) (AlgHom.id (ULift.{u} ℤ) A)).comp
          (gradedCoactionAlgHom 𝒜)).toRingHom =
      ((Algebra.TensorProduct.assoc (ULift.{u} ℤ) (ULift.{u} ℤ) (ULift.{u} ℤ)
        (LaurentPolynomial (ULift.{u} ℤ)) (LaurentPolynomial (ULift.{u} ℤ)) A).symm.toAlgHom.comp
          ((Algebra.TensorProduct.map (AlgHom.id (ULift.{u} ℤ) (LaurentPolynomial (ULift.{u} ℤ)))
            (gradedCoactionAlgHom 𝒜)).comp (gradedCoactionAlgHom 𝒜))).toRingHom := by
  apply ringHom_eq_of_homogeneous 𝒜
  intro n a
  simp [gradedCoactionAlgHom_of_mem 𝒜 a.property]

end Coaction

/-- **Stacks Project, Tag 0EKJ.** An integer grading defines the multiplicative-group action
on the spectrum whose coordinate map sends a homogeneous element of degree `n` to `a ⊗ Tⁿ`. -/
@[stacks 0EKJ "graded_ring_gm_action", ega "II 8.3.9" "partial"]
noncomputable def gradedGmAction {A : Type u} [CommRing A] {σ : Type v}
    [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ℤ → σ) [GradedRing 𝒜] :
    GradedGmAction 𝒜 := by
  refine ⟨gradedCoaction 𝒜, ?_, fun _ _ => gradedCoaction_of_mem 𝒜, ?_⟩
  · let R := ULift.{u} ℤ
    let Msrc : Mon (CommAlgCat R)ᵒᵖ := ⟨Opposite.op (CommAlgCat.of R (LaurentPolynomial R))⟩
    let Xsrc := Opposite.op (CommAlgCat.of R A)
    letI : ModObj Msrc.X Xsrc := by
      refine ⟨(CommAlgCat.ofHom (gradedCoactionAlgHom 𝒜)).op, ?_, ?_⟩
      · apply Quiver.Hom.unop_inj
        apply CommAlgCat.hom_ext
        exact AlgHom.ext (RingHom.congr_fun (gradedCoactionAlgHom_counit 𝒜))
      · apply Quiver.Hom.unop_inj
        apply CommAlgCat.hom_ext
        exact AlgHom.ext (RingHom.congr_fun (gradedCoactionAlgHom_comul 𝒜))
    let F := algSpec (CommRingCat.of R)
    letI : F.Braided := AlgebraicGeometry.braidedAlgSpec
    letI : F.Monoidal := Functor.Braided.toMonoidal
    let M' : MonObj (F.obj Msrc.X) := by
      change MonObj (multiplicativeGroupULift.asOver (Spec (.of R)))
      infer_instance
    exact CategoryTheory.Functor.LaxMonoidal.modObj F (X := Xsrc) M'
      (Over.OverMorphism.ext rfl) (Over.OverMorphism.ext rfl)
  · rfl

end AlgebraicGeometry

end
