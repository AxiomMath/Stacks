module

public import Mathlib.CategoryTheory.Monoidal.Mon
public import StacksCore.CategoryTheory.GradedObject.GradedVectorSpace
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ProjectionFormula.Setup
public import StacksFrontier.CategoryTheory.GradedObject.KoszulBraiding

/-!
# Monoid objects in graded vector spaces are graded algebras

Let `F` be a field. A monoid object `V` of the monoidal category `GradedObject ℤ (ModuleCat F)` of
`ℤ`-graded `F`-vector spaces (Stacks, Homology, Example 0FFX) is a graded `F`-algebra: by the
degreewise formula `(V ⊗ V)ⁿ = ⨁_{i+j=n} Vⁱ ⊗_F Vʲ`, its multiplication `V ⊗ V ⟶ V` is a family of
bilinear maps `Vⁱ × Vʲ → V^{i+j}`, and its unit `𝟏 ⟶ V` is an element of `V⁰`. This file records
that algebra as an `ExternallyGradedAlgebra`. If `V` is commutative for the Koszul-signed symmetry
of 0FFX, the algebra is graded commutative, and a morphism of monoid objects is degreewise
multiplicative and unital.

## Main definitions

* `CategoryTheory.GradedObject.Monoidal.monObjMul`: the bilinear map `Vⁱ × Vʲ → Vᵏ`, `i + j = k`,
  of a monoid object.
* `CategoryTheory.GradedObject.Monoidal.monObjOne`: the unit of a monoid object, in `V⁰`.
* `CategoryTheory.GradedObject.Monoidal.toExternallyGradedAlgebra`: the graded algebra of a
  monoid object.

## Main results

* `CategoryTheory.GradedObject.Monoidal.toExternallyGradedAlgebra_isGradedCommutative`: a monoid
  object which is commutative for the Koszul braiding gives a graded commutative algebra.
* `CategoryTheory.GradedObject.Monoidal.map_toExternallyGradedAlgebra_mul` and
  `CategoryTheory.GradedObject.Monoidal.map_toExternallyGradedAlgebra_one`: a morphism of monoid
  objects is multiplicative and unital on elements.

## References

* [Stacks Project, Tag 0FFX](https://stacks.math.columbia.edu/tag/0FFX)
* [Stacks Project, Tag 0FH1](https://stacks.math.columbia.edu/tag/0FH1)
-/

@[expose] public section

namespace CategoryTheory.GradedObject.Monoidal

open CategoryTheory Category Limits MonoidalCategory MonObj
open scoped TensorProduct

universe u

variable {F : Type u} [Field F] (V : GradedObject ℤ (ModuleCat.{u} F)) [MonObj V]

/-- The multiplication `Vⁱ × Vʲ → Vᵏ`, for `i + j = k`, of a monoid object `V` of graded vector
spaces: the restriction of `μ : V ⊗ V ⟶ V` to the summand `Vⁱ ⊗ Vʲ` of `(V ⊗ V)ᵏ`. -/
noncomputable def monObjMul (i j k : ℤ) (h : i + j = k) : V i →ₗ[F] V j →ₗ[F] V k :=
  TensorProduct.curry (ιTensorObj V V i j k h ≫ μ[V] k).hom

/-- `monObjMul V i j k h a b` is `μ` applied to `a ⊗ b` in the summand `Vⁱ ⊗ Vʲ` of `(V ⊗ V)ᵏ`. -/
lemma monObjMul_apply (i j k : ℤ) (h : i + j = k) (a : V i) (b : V j) :
    monObjMul V i j k h a b = (ιTensorObj V V i j k h ≫ μ[V] k) (a ⊗ₜ b) :=
  rfl

/-- The product does not depend on how its degree is written. -/
lemma monObjMul_heq {i j k k' : ℤ} (h : i + j = k) (h' : i + j = k') (a : V i) (b : V j) :
    monObjMul V i j k h a b ≍ monObjMul V i j k' h' a b := by
  subst h h'
  rfl

/-- The unit of a monoid object `V` of graded vector spaces, as an element of `V⁰`: the image of
`1` under `η : 𝟏 ⟶ V` in degree `0`. -/
noncomputable def monObjOne : V 0 :=
  (η[V] 0) ((tensorUnit₀ (I := ℤ) (C := ModuleCat.{u} F)).inv (1 : F))

/-- Associativity of a monoid object, on the summand `Vⁱ ⊗ Vʲ ⊗ Vˡ`. -/
lemma monObjMul_assoc_hom (i j l k : ℤ) (h : i + j + l = k) :
    (ιTensorObj V V i j (i + j) rfl ≫ μ[V] (i + j)) ▷ V l ≫
        ιTensorObj V V (i + j) l k h ≫ μ[V] k =
      (α_ (V i) (V j) (V l)).hom ≫ V i ◁ (ιTensorObj V V j l (j + l) rfl ≫ μ[V] (j + l)) ≫
        ιTensorObj V V i (j + l) k (by rw [← h, add_assoc]) ≫ μ[V] k := by
  have H := ιTensorObj₃' V V V i j l k h ≫= congr($(MonObj.mul_assoc V) k)
  simp only [categoryOfGradedObjects_comp, Monoidal.whiskerRight_apply,
    Monoidal.whiskerLeft_apply, Monoidal.associator_hom_apply] at H
  rw [ιTensorObj₃'_associator_hom_assoc, ιTensorObj₃'_eq V V V i j l k h (i + j) rfl,
    ιTensorObj₃_eq V V V i j l k h (j + l) rfl] at H
  simpa using H

/-- The left unit law of a monoid object, on the summand `V⁰ ⊗ Vⁱ`. -/
lemma monObjMul_one_left_hom (i : ℤ) :
    η[V] 0 ▷ V i ≫ ιTensorObj V V 0 i i (zero_add i) ≫ μ[V] i =
      (tensorUnit₀ (I := ℤ) (C := ModuleCat.{u} F)).hom ▷ V i ≫ (λ_ (V i)).hom := by
  have H := ιTensorObj (𝟙_ _) V 0 i i (zero_add i) ≫= congr($(MonObj.one_mul V) i)
  simp only [categoryOfGradedObjects_comp, Monoidal.whiskerRight_apply,
    Monoidal.leftUnitor_hom_apply, ιTensorObj_leftUnitor_hom] at H
  simpa using H

/-- The right unit law of a monoid object, on the summand `Vⁱ ⊗ V⁰`. -/
lemma monObjMul_one_right_hom (i : ℤ) :
    V i ◁ η[V] 0 ≫ ιTensorObj V V i 0 i (add_zero i) ≫ μ[V] i =
      V i ◁ (tensorUnit₀ (I := ℤ) (C := ModuleCat.{u} F)).hom ≫ (ρ_ (V i)).hom := by
  have H := ιTensorObj V (𝟙_ _) i 0 i (add_zero i) ≫= congr($(MonObj.mul_one V) i)
  simp only [categoryOfGradedObjects_comp, Monoidal.whiskerLeft_apply,
    Monoidal.rightUnitor_hom_apply, ιTensorObj_rightUnitor_hom] at H
  simpa using H

/-- Associativity of the product: `(a b) c = a (b c)` for `a ∈ Vⁱ`, `b ∈ Vʲ`, `c ∈ Vˡ`. -/
lemma monObjMul_assoc (i j l k : ℤ) (h : i + j + l = k) (a : V i) (b : V j) (c : V l) :
    monObjMul V (i + j) l k h (monObjMul V i j (i + j) rfl a b) c =
      monObjMul V i (j + l) k (by rw [← h, add_assoc]) a (monObjMul V j l (j + l) rfl b c) := by
  have H := ConcreteCategory.congr_hom (monObjMul_assoc_hom V i j l k h) ((a ⊗ₜ b) ⊗ₜ c)
  simp only [ConcreteCategory.comp_apply] at H
  exact H

/-- The unit is a left identity: `1 a = a` for `a ∈ Vⁱ`. -/
lemma monObjMul_one_left (i : ℤ) (a : V i) :
    monObjMul V 0 i i (zero_add i) (monObjOne V) a = a := by
  have H := ConcreteCategory.congr_hom (monObjMul_one_left_hom V i)
    ((tensorUnit₀ (I := ℤ) (C := ModuleCat.{u} F)).inv (1 : F) ⊗ₜ a)
  simp only [ConcreteCategory.comp_apply, ModuleCat.MonoidalCategory.whiskerRight_apply,
    Iso.inv_hom_id_apply, ModuleCat.MonoidalCategory.leftUnitor_hom_apply, one_smul] at H
  exact H

/-- The unit is a right identity: `a 1 = a` for `a ∈ Vⁱ`. -/
lemma monObjMul_one_right (i : ℤ) (a : V i) :
    monObjMul V i 0 i (add_zero i) a (monObjOne V) = a := by
  have H := ConcreteCategory.congr_hom (monObjMul_one_right_hom V i)
    (a ⊗ₜ (tensorUnit₀ (I := ℤ) (C := ModuleCat.{u} F)).inv (1 : F))
  simp only [ConcreteCategory.comp_apply, ModuleCat.MonoidalCategory.whiskerLeft_apply,
    Iso.inv_hom_id_apply, ModuleCat.MonoidalCategory.rightUnitor_hom_apply, one_smul] at H
  exact H

/-- The graded `F`-algebra of a monoid object `V` of `ℤ`-graded `F`-vector spaces: the piece of
degree `n` is `Vⁿ`, the product `Vⁱ × Vʲ → V^{i+j}` is `μ` on the summand `Vⁱ ⊗ Vʲ`, and the
unit is the image of `1` under `η`. -/
noncomputable def toExternallyGradedAlgebra : ExternallyGradedAlgebra.{u, u} F where
  piece n := V n
  mul i j := monObjMul V i j (i + j) rfl
  one := monObjOne V
  mul_assoc i j l a b c := by
    rw [monObjMul_assoc V i j l (i + j + l) rfl a b c]
    exact monObjMul_heq V _ _ _ _
  one_mul i a := (monObjMul_heq V _ (zero_add i) _ _).trans (heq_of_eq (monObjMul_one_left V i a))
  mul_one i a := (monObjMul_heq V _ (add_zero i) _ _).trans (heq_of_eq (monObjMul_one_right V i a))

/-- The piece of degree `n` of `toExternallyGradedAlgebra V` is `Vⁿ`. -/
@[simp]
lemma toExternallyGradedAlgebra_piece (n : ℤ) :
    (toExternallyGradedAlgebra V).piece n = V n :=
  rfl

/-- The product of `a ∈ Vⁱ` and `b ∈ Vʲ` in `toExternallyGradedAlgebra V` is `μ` applied to `a ⊗ b`
in the summand `Vⁱ ⊗ Vʲ` of `(V ⊗ V)^{i+j}`. -/
lemma toExternallyGradedAlgebra_mul_apply (i j : ℤ) (a : V i) (b : V j) :
    (toExternallyGradedAlgebra V).mul i j a b =
      (ιTensorObj V V i j (i + j) rfl ≫ μ[V] (i + j)) (a ⊗ₜ b) :=
  rfl

/-- The unit of `toExternallyGradedAlgebra V` is the image of `1` under `η` in degree `0`. -/
lemma toExternallyGradedAlgebra_one :
    (toExternallyGradedAlgebra V).one =
      (η[V] 0) ((tensorUnit₀ (I := ℤ) (C := ModuleCat.{u} F)).inv (1 : F)) :=
  rfl

section Commutative

/-- If `μ` is invariant under the Koszul braiding, then `a b = (-1)^{ij} b a` for `a ∈ Vⁱ`,
`b ∈ Vʲ`, in any degree `k = i + j`. -/
lemma monObjMul_comm_of_koszul (hV : (koszulBraiding V V).hom ≫ μ[V] = μ[V])
    (i j k : ℤ) (h : i + j = k) (a : V i) (b : V j) :
    monObjMul V i j k h a b =
      DifferentialGraded.gradedSign F (i * j) •
        monObjMul V j i k (by rw [add_comm]; exact h) b a := by
  have H := ConcreteCategory.congr_hom (ιTensorObj V V i j k h ≫= congr($hV k)) (a ⊗ₜ b)
  simp only [categoryOfGradedObjects_comp, ι_koszulBraiding_hom_assoc, Units.smul_def,
    Preadditive.zsmul_comp, ModuleCat.hom_zsmul, LinearMap.smul_apply,
    ConcreteCategory.comp_apply] at H
  simp only [monObjMul_apply, ConcreteCategory.comp_apply]
  rw [← H, ModuleCat.MonoidalCategory.braiding_hom_apply, ← Int.cast_smul_eq_zsmul F,
    DifferentialGraded.intCast_negOnePow]

/-- **Graded commutativity.** A monoid object of `ℤ`-graded vector spaces which is commutative
for the Koszul-signed symmetry of Stacks 0FFX gives a graded commutative algebra:
`a b = (-1)^{ij} b a` for `a ∈ Vⁱ`, `b ∈ Vʲ`. -/
theorem toExternallyGradedAlgebra_isGradedCommutative
    [@IsCommMonObj (GradedObject ℤ (ModuleCat.{u} F)) _ _ koszulBraidedCategory V _] :
    (toExternallyGradedAlgebra V).IsGradedCommutative where
  graded_comm i j a b := by
    have hV : (koszulBraiding V V).hom ≫ μ[V] = μ[V] :=
      @IsCommMonObj.mul_comm _ _ _ koszulBraidedCategory V _ _
    have key : monObjMul V i j (i + j) rfl a b ≍
        DifferentialGraded.gradedSign F (i * j) • monObjMul V j i (j + i) rfl b a := by
      rw [monObjMul_comm_of_koszul V hV i j (i + j) rfl a b]
      exact ExternallyGraded.scalar_heq (X := fun n => V n) (add_comm i j) rfl
        (monObjMul_heq V _ _ _ _)
    exact key

end Commutative

section Hom

variable {V} {W : GradedObject ℤ (ModuleCat.{u} F)} [MonObj W] (f : V ⟶ W) [IsMonHom f]

/-- A morphism of monoid objects is multiplicative degreewise. -/
lemma map_monObjMul (i j k : ℤ) (h : i + j = k) (a : V i) (b : V j) :
    f k (monObjMul V i j k h a b) = monObjMul W i j k h (f i a) (f j b) := by
  have H := ConcreteCategory.congr_hom (ιTensorObj V V i j k h ≫= congr($(IsMonHom.mul_hom f) k))
    (a ⊗ₜ b)
  have hff : (f ⊗ₘ f) = Monoidal.tensorHom f f := rfl
  simp only [categoryOfGradedObjects_comp, hff, ι_tensorHom_assoc,
    ConcreteCategory.comp_apply, ModuleCat.MonoidalCategory.tensorHom_tmul] at H
  exact H

/-- A morphism of monoid objects of graded vector spaces is multiplicative on the graded
algebras. -/
theorem map_toExternallyGradedAlgebra_mul (i j : ℤ) (a : V i) (b : V j) :
    f (i + j) ((toExternallyGradedAlgebra V).mul i j a b) =
      (toExternallyGradedAlgebra W).mul i j (f i a) (f j b) :=
  map_monObjMul f i j (i + j) rfl a b

/-- A morphism of monoid objects of graded vector spaces sends the unit to the unit. -/
theorem map_toExternallyGradedAlgebra_one :
    f 0 (toExternallyGradedAlgebra V).one = (toExternallyGradedAlgebra W).one := by
  have H := ConcreteCategory.congr_hom (congr($(IsMonHom.one_hom f) 0))
    ((tensorUnit₀ (I := ℤ) (C := ModuleCat.{u} F)).inv (1 : F))
  simp only [categoryOfGradedObjects_comp, ConcreteCategory.comp_apply] at H
  exact H

end Hom

end CategoryTheory.GradedObject.Monoidal
