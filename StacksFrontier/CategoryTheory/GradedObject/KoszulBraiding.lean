module

public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.CategoryTheory.GradedObject.Braiding
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive

/-!
# The Koszul sign rule on `ℤ`-graded objects

Let `C` be a braided monoidal preadditive category. Mathlib's braiding on `GradedObject ℤ C`
(`CategoryTheory.GradedObject.Monoidal.braiding`) is built summand by summand from the braiding
of `C` and carries no sign. This file constructs the *signed* commutativity constraint, which on
the summand `X^p ⊗ Y^q` of `(X ⊗ Y)^{p+q}` is `(-1)^{pq}` times the braiding of `C` followed by
the inclusion of `Y^q ⊗ X^p` into `(Y ⊗ X)^{p+q}`. For graded `F`-vector spaces this is the
constraint `v ⊗ w ↦ (-1)^{pq} w ⊗ v` of Stacks, Homology, Example 0FFX.

## Main definitions

* `CategoryTheory.GradedObject.Monoidal.koszulBraiding`: the signed commutativity isomorphism
  `X ⊗ Y ≅ Y ⊗ X`.
* `CategoryTheory.GradedObject.koszulBraidedCategory`: the braided structure on
  `GradedObject ℤ C` with the signed constraint.
* `CategoryTheory.GradedObject.koszulSymmetricCategory`: it is symmetric when `C` is.

## Main results

* `CategoryTheory.GradedObject.Monoidal.ι_koszulBraiding_hom`: the signed constraint on the
  summand `X^p ⊗ Y^q` is `(-1)^{pq}` times the braiding of `C`.
* `CategoryTheory.GradedObject.Monoidal.ι_koszulBraiding_hom_eq_smul`: it is `(-1)^{pq}` times the
  sign-free constraint of Mathlib on that summand.
* `CategoryTheory.GradedObject.Monoidal.koszulHexagon_forward` and
  `CategoryTheory.GradedObject.Monoidal.koszulHexagon_reverse`: the two hexagon identities.

## References

* [Stacks Project, Tag 0FFX](https://stacks.math.columbia.edu/tag/0FFX)
-/

@[expose] public section

namespace CategoryTheory

open Category Limits MonoidalCategory

variable {C : Type*} [Category* C] [MonoidalCategory C] [Preadditive C] [MonoidalPreadditive C]

namespace GradedObject

namespace Monoidal

private lemma units_smul_whiskerRight {A B : C} (u : ℤˣ) (f : A ⟶ B) (W : C) :
    (u • f) ▷ W = u • (f ▷ W) := by
  rw [Units.smul_def, Units.smul_def]
  exact (tensorRight W).map_zsmul (f := f) (r := (u : ℤ))

private lemma whiskerLeft_units_smul (W : C) {A B : C} (u : ℤˣ) (f : A ⟶ B) :
    W ◁ (u • f) = u • (W ◁ f) := by
  rw [Units.smul_def, Units.smul_def]
  exact (tensorLeft W).map_zsmul (f := f) (r := (u : ℤ))

variable (X Y Z : GradedObject ℤ C)

section Braided

variable [BraidedCategory C]

/-- The Koszul-signed commutativity isomorphism `X ⊗ Y ≅ Y ⊗ X` of `ℤ`-graded objects: on the
summand `X^p ⊗ Y^q` it is `(-1)^{pq}` times the braiding of `C`. -/
noncomputable def koszulBraiding [HasTensor X Y] [HasTensor Y X] :
    tensorObj X Y ≅ tensorObj Y X where
  hom k := tensorObjDesc (fun i j hij ↦ (i * j).negOnePow • ((β_ _ _).hom ≫
    ιTensorObj Y X j i k (by rw [add_comm j i]; exact hij)))
  inv k := tensorObjDesc (fun j i hij ↦ (i * j).negOnePow • ((β_ _ _).inv ≫
    ιTensorObj X Y i j k (by rw [add_comm i j]; exact hij)))
  hom_inv_id := by
    ext k i j h
    simp [Linear.units_smul_comp, Linear.comp_units_smul, smul_smul]
  inv_hom_id := by
    ext k j i h
    simp [Linear.units_smul_comp, Linear.comp_units_smul, smul_smul]

omit [MonoidalPreadditive C] in
/-- On the summand `X^p ⊗ Y^q` the Koszul braiding is `(-1)^{pq}` times the braiding
`X^p ⊗ Y^q ≅ Y^q ⊗ X^p` of `C`, followed by the inclusion of `Y^q ⊗ X^p`. -/
@[reassoc (attr := simp)]
lemma ι_koszulBraiding_hom [HasTensor X Y] [HasTensor Y X] (i j k : ℤ) (h : i + j = k) :
    ιTensorObj X Y i j k h ≫ (koszulBraiding X Y).hom k =
      (i * j).negOnePow • ((β_ _ _).hom ≫
        ιTensorObj Y X j i k (by rw [add_comm j i]; exact h)) := by
  simp [koszulBraiding]

omit [MonoidalPreadditive C] in
/-- On the summand `Y^q ⊗ X^p` the inverse of the Koszul braiding is `(-1)^{pq}` times the inverse
braiding `Y^q ⊗ X^p ≅ X^p ⊗ Y^q` of `C`, followed by the inclusion of `X^p ⊗ Y^q`. -/
@[reassoc (attr := simp)]
lemma ι_koszulBraiding_inv [HasTensor X Y] [HasTensor Y X] (j i k : ℤ) (h : j + i = k) :
    ιTensorObj Y X j i k h ≫ (koszulBraiding X Y).inv k =
      (i * j).negOnePow • ((β_ _ _).inv ≫
        ιTensorObj X Y i j k (by rw [add_comm i j]; exact h)) := by
  simp [koszulBraiding]

omit [MonoidalPreadditive C] in
/-- On the summand `X^p ⊗ Y^q`, the Koszul braiding is `(-1)^{pq}` times Mathlib's sign-free
braiding. -/
@[reassoc]
lemma ι_koszulBraiding_hom_eq_smul [HasTensor X Y] [HasTensor Y X] (i j k : ℤ)
    (h : i + j = k) :
    ιTensorObj X Y i j k h ≫ (koszulBraiding X Y).hom k =
      (i * j).negOnePow • (ιTensorObj X Y i j k h ≫ (braiding X Y).hom k) := by
  simp [braiding]

omit [MonoidalPreadditive C] in
variable {Y Z} in
/-- The Koszul braiding is natural in its second argument. -/
lemma koszulBraiding_naturality_right [HasTensor X Y] [HasTensor Y X] [HasTensor X Z]
    [HasTensor Z X] (f : Y ⟶ Z) :
    whiskerLeft X f ≫ (koszulBraiding X Z).hom = (koszulBraiding X Y).hom ≫ whiskerRight f X := by
  ext k i j h
  simp [Linear.units_smul_comp, Linear.comp_units_smul]

omit [MonoidalPreadditive C] in
variable {X Y} in
/-- The Koszul braiding is natural in its first argument. -/
lemma koszulBraiding_naturality_left [HasTensor Y Z] [HasTensor Z Y] [HasTensor X Z]
    [HasTensor Z X] (f : X ⟶ Y) :
    whiskerRight f Z ≫ (koszulBraiding Y Z).hom = (koszulBraiding X Z).hom ≫ whiskerLeft Z f := by
  ext k i j h
  simp [Linear.units_smul_comp, Linear.comp_units_smul]

omit [MonoidalPreadditive C] in
/-- On a summand `A^a ⊗ (B ⊗ W)^{b + c}`, read through `A^a ⊗ B^b ⊗ W^c`, the Koszul braiding of
`A` with `B ⊗ W` is `(-1)^{a(b+c)}` times the sign-free one. -/
@[reassoc]
lemma ιTensorObj₃_koszulBraiding_hom (A B W : GradedObject ℤ C) [HasTensor B W]
    [HasTensor A (tensorObj B W)] [HasTensor (tensorObj B W) A] (a b c k : ℤ)
    (h : a + b + c = k) :
    ιTensorObj₃ A B W a b c k h ≫ (koszulBraiding A (tensorObj B W)).hom k =
      (a * (b + c)).negOnePow •
        (ιTensorObj₃ A B W a b c k h ≫ (braiding A (tensorObj B W)).hom k) := by
  rw [ιTensorObj₃_eq A B W a b c k h _ rfl, assoc, assoc, ι_koszulBraiding_hom_eq_smul,
    Linear.comp_units_smul]

omit [MonoidalPreadditive C] in
/-- On a summand `(A ⊗ B)^{a + b} ⊗ W^c`, read through `(A^a ⊗ B^b) ⊗ W^c`, the Koszul braiding of
`A ⊗ B` with `W` is `(-1)^{(a+b)c}` times the sign-free one. -/
@[reassoc]
lemma ιTensorObj₃'_koszulBraiding_hom (A B W : GradedObject ℤ C) [HasTensor A B]
    [HasTensor (tensorObj A B) W] [HasTensor W (tensorObj A B)] (a b c k : ℤ)
    (h : a + b + c = k) :
    ιTensorObj₃' A B W a b c k h ≫ (koszulBraiding (tensorObj A B) W).hom k =
      ((a + b) * c).negOnePow •
        (ιTensorObj₃' A B W a b c k h ≫ (braiding (tensorObj A B) W).hom k) := by
  rw [ιTensorObj₃'_eq A B W a b c k h _ rfl, assoc, assoc, ι_koszulBraiding_hom_eq_smul,
    Linear.comp_units_smul]

/-- On a summand `(A^a ⊗ B^b) ⊗ W^c`, whiskering the Koszul braiding of `A` and `B` by `W` is
`(-1)^{ab}` times whiskering the sign-free one. -/
@[reassoc]
lemma ιTensorObj₃'_whiskerRight_koszulBraiding_hom (A B W : GradedObject ℤ C) [HasTensor A B]
    [HasTensor B A] [HasTensor (tensorObj A B) W] [HasTensor (tensorObj B A) W] (a b c k : ℤ)
    (h : a + b + c = k) :
    ιTensorObj₃' A B W a b c k h ≫ whiskerRight (koszulBraiding A B).hom W k =
      (a * b).negOnePow •
        (ιTensorObj₃' A B W a b c k h ≫ whiskerRight (braiding A B).hom W k) := by
  simp only [ιTensorObj₃'_eq A B W a b c k h _ rfl, assoc, ι_tensorHom,
    categoryOfGradedObjects_id, tensorHom_id, ← comp_whiskerRight_assoc,
    ι_koszulBraiding_hom_eq_smul, units_smul_whiskerRight, Linear.units_smul_comp]

/-- On a summand `A^a ⊗ B^b ⊗ W^c`, whiskering the Koszul braiding of `B` and `W` by `A` is
`(-1)^{bc}` times whiskering the sign-free one. -/
@[reassoc]
lemma ιTensorObj₃_whiskerLeft_koszulBraiding_hom (A B W : GradedObject ℤ C) [HasTensor B W]
    [HasTensor W B] [HasTensor A (tensorObj B W)] [HasTensor A (tensorObj W B)] (a b c k : ℤ)
    (h : a + b + c = k) :
    ιTensorObj₃ A B W a b c k h ≫ whiskerLeft A (koszulBraiding B W).hom k =
      (b * c).negOnePow •
        (ιTensorObj₃ A B W a b c k h ≫ whiskerLeft A (braiding B W).hom k) := by
  simp only [ιTensorObj₃_eq A B W a b c k h _ rfl, assoc, ι_tensorHom,
    categoryOfGradedObjects_id, id_tensorHom, ← whiskerLeft_comp_assoc,
    ι_koszulBraiding_hom_eq_smul, whiskerLeft_units_smul, Linear.units_smul_comp]

omit [Preadditive C] [MonoidalPreadditive C] in
/-- On a summand, whiskering Mathlib's sign-free braiding of `A` and `B` by `W` is the braiding of
`C` on the corresponding factors. -/
@[reassoc]
lemma ιTensorObj₃'_whiskerRight_braiding_hom (A B W : GradedObject ℤ C) [HasTensor A B]
    [HasTensor B A] [HasTensor (tensorObj A B) W] [HasTensor (tensorObj B A) W] (a b c k : ℤ)
    (h : a + b + c = k) :
    ιTensorObj₃' A B W a b c k h ≫ whiskerRight (braiding A B).hom W k =
      ((β_ (A a) (B b)).hom ▷ W c) ≫
        ιTensorObj₃' B A W b a c k (by rw [add_comm b a]; exact h) := by
  simp only [ιTensorObj₃'_eq A B W a b c k h _ rfl,
    ιTensorObj₃'_eq B A W b a c k (by rwa [add_comm b a]) (a + b) (add_comm b a),
    assoc, ι_tensorHom, categoryOfGradedObjects_id, tensorHom_id, ← comp_whiskerRight_assoc]
  simp [braiding]

omit [Preadditive C] [MonoidalPreadditive C] in
/-- On a summand, whiskering Mathlib's sign-free braiding of `B` and `W` by `A` is the braiding of
`C` on the corresponding factors. -/
@[reassoc]
lemma ιTensorObj₃_whiskerLeft_braiding_hom (A B W : GradedObject ℤ C) [HasTensor B W]
    [HasTensor W B] [HasTensor A (tensorObj B W)] [HasTensor A (tensorObj W B)] (a b c k : ℤ)
    (h : a + b + c = k) :
    ιTensorObj₃ A B W a b c k h ≫ whiskerLeft A (braiding B W).hom k =
      (A a ◁ (β_ (B b) (W c)).hom) ≫
        ιTensorObj₃ A W B a c b k (by rw [add_assoc, add_comm c b, ← add_assoc]; exact h) := by
  simp only [ιTensorObj₃_eq A B W a b c k h _ rfl,
    ιTensorObj₃_eq A W B a c b k (by rwa [add_assoc, add_comm c b, ← add_assoc]) (b + c)
      (add_comm c b),
    assoc, ι_tensorHom, categoryOfGradedObjects_id, id_tensorHom, ← whiskerLeft_comp_assoc]
  simp [braiding]

/-- The first hexagon identity for the Koszul braiding. -/
lemma koszulHexagon_forward [HasTensor X Y] [HasTensor Y X] [HasTensor Y Z]
    [HasTensor Z X] [HasTensor X Z]
    [HasTensor (tensorObj X Y) Z] [HasTensor X (tensorObj Y Z)]
    [HasTensor (tensorObj Y Z) X] [HasTensor Y (tensorObj Z X)]
    [HasTensor (tensorObj Y X) Z] [HasTensor Y (tensorObj X Z)]
    [HasGoodTensor₁₂Tensor X Y Z] [HasGoodTensorTensor₂₃ X Y Z]
    [HasGoodTensor₁₂Tensor Y Z X] [HasGoodTensorTensor₂₃ Y Z X]
    [HasGoodTensor₁₂Tensor Y X Z] [HasGoodTensorTensor₂₃ Y X Z] :
    (associator X Y Z).hom ≫ (koszulBraiding X (tensorObj Y Z)).hom ≫ (associator Y Z X).hom =
      whiskerRight (koszulBraiding X Y).hom Z ≫ (associator Y X Z).hom ≫
        whiskerLeft Y (koszulBraiding X Z).hom := by
  ext k i₁ i₂ i₃ h
  have H := congrArg (fun φ ↦ ιTensorObj₃' X Y Z i₁ i₂ i₃ k h ≫ φ k)
    (Monoidal.hexagon_forward X Y Z)
  simp only [categoryOfGradedObjects_comp] at H ⊢
  conv_lhs => rw [ιTensorObj₃'_associator_hom_assoc, ιTensorObj₃_koszulBraiding_hom_assoc,
    Linear.units_smul_comp, assoc, Linear.comp_units_smul,
    ← ιTensorObj₃'_associator_hom_assoc X Y Z i₁ i₂ i₃ k h]
  conv_rhs => rw [ιTensorObj₃'_whiskerRight_koszulBraiding_hom_assoc, Linear.units_smul_comp,
    assoc, ιTensorObj₃'_whiskerRight_braiding_hom_assoc, ιTensorObj₃'_associator_hom_assoc,
    ιTensorObj₃_whiskerLeft_koszulBraiding_hom, Linear.comp_units_smul, Linear.comp_units_smul,
    ← ιTensorObj₃'_associator_hom_assoc Y X Z i₂ i₁ i₃ k (by omega),
    ← ιTensorObj₃'_whiskerRight_braiding_hom_assoc X Y Z i₁ i₂ i₃ k h, smul_smul]
  rw [mul_add, Int.negOnePow_add, H]

/-- The second hexagon identity for the Koszul braiding. -/
lemma koszulHexagon_reverse [HasTensor X Y] [HasTensor Y Z] [HasTensor Z X]
    [HasTensor Z Y] [HasTensor X Z]
    [HasTensor (tensorObj X Y) Z] [HasTensor X (tensorObj Y Z)]
    [HasTensor Z (tensorObj X Y)] [HasTensor (tensorObj Z X) Y]
    [HasTensor X (tensorObj Z Y)] [HasTensor (tensorObj X Z) Y]
    [HasGoodTensor₁₂Tensor X Y Z] [HasGoodTensorTensor₂₃ X Y Z]
    [HasGoodTensor₁₂Tensor Z X Y] [HasGoodTensorTensor₂₃ Z X Y]
    [HasGoodTensor₁₂Tensor X Z Y] [HasGoodTensorTensor₂₃ X Z Y] :
    (associator X Y Z).inv ≫ (koszulBraiding (tensorObj X Y) Z).hom ≫ (associator Z X Y).inv =
      whiskerLeft X (koszulBraiding Y Z).hom ≫ (associator X Z Y).inv ≫
        whiskerRight (koszulBraiding X Z).hom Y := by
  ext k i₁ i₂ i₃ h
  have H := congrArg (fun φ ↦ ιTensorObj₃ X Y Z i₁ i₂ i₃ k h ≫ φ k)
    (Monoidal.hexagon_reverse X Y Z)
  simp only [categoryOfGradedObjects_comp] at H ⊢
  conv_lhs => rw [ιTensorObj₃_associator_inv_assoc, ιTensorObj₃'_koszulBraiding_hom_assoc,
    Linear.units_smul_comp, assoc, Linear.comp_units_smul,
    ← ιTensorObj₃_associator_inv_assoc X Y Z i₁ i₂ i₃ k h]
  conv_rhs => rw [ιTensorObj₃_whiskerLeft_koszulBraiding_hom_assoc, Linear.units_smul_comp,
    assoc, ιTensorObj₃_whiskerLeft_braiding_hom_assoc, ιTensorObj₃_associator_inv_assoc,
    ιTensorObj₃'_whiskerRight_koszulBraiding_hom, Linear.comp_units_smul, Linear.comp_units_smul,
    ← ιTensorObj₃_associator_inv_assoc X Z Y i₁ i₃ i₂ k (by omega),
    ← ιTensorObj₃_whiskerLeft_braiding_hom_assoc X Y Z i₁ i₂ i₃ k h, smul_smul]
  rw [add_mul, Int.negOnePow_add, mul_comm, H]

end Braided

omit [MonoidalPreadditive C] in
/-- The Koszul braiding is symmetric when the braiding of `C` is. -/
@[reassoc (attr := simp)]
lemma koszulBraiding_symmetry [SymmetricCategory C] [HasTensor X Y] [HasTensor Y X] :
    (koszulBraiding X Y).hom ≫ (koszulBraiding Y X).hom = 𝟙 _ := by
  ext k i j h
  simp [Linear.units_smul_comp, Linear.comp_units_smul, smul_smul, mul_comm j i]

end Monoidal

section Instances

variable
  [∀ (X₁ X₂ : GradedObject ℤ C), HasTensor X₁ X₂]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasInitial C]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C)
    ((MonoidalCategory.curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C)
    ((MonoidalCategory.curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), HasTensor₄ObjExt X₁ X₂ X₃ X₄]

/-- The braided structure on `ℤ`-graded objects given by the Koszul sign rule. -/
@[instance_reducible]
noncomputable def koszulBraidedCategory [BraidedCategory C] :
    BraidedCategory (GradedObject ℤ C) where
  braiding X Y := Monoidal.koszulBraiding X Y
  braiding_naturality_left _ _ := Monoidal.koszulBraiding_naturality_left _ _
  braiding_naturality_right _ _ _ _ := Monoidal.koszulBraiding_naturality_right _ _
  hexagon_forward _ _ _ := Monoidal.koszulHexagon_forward _ _ _
  hexagon_reverse _ _ _ := Monoidal.koszulHexagon_reverse _ _ _

/-- The symmetric monoidal structure on `ℤ`-graded objects given by the Koszul sign rule: for
graded `F`-vector spaces, `v ⊗ w ↦ (-1)^{pq} w ⊗ v` on `V^p ⊗ W^q`. -/
@[instance_reducible]
noncomputable def koszulSymmetricCategory [SymmetricCategory C] :
    SymmetricCategory (GradedObject ℤ C) where
  __ := koszulBraidedCategory
  symmetry X Y := Monoidal.koszulBraiding_symmetry X Y

/-- The commutativity constraint of `koszulBraidedCategory` is the Koszul braiding. -/
lemma koszulBraidedCategory_braiding [BraidedCategory C] (X Y : GradedObject ℤ C) :
    @BraidedCategory.braiding _ _ _ koszulBraidedCategory X Y = Monoidal.koszulBraiding X Y :=
  rfl

end Instances

end GradedObject

end CategoryTheory
