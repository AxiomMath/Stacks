module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import StacksFrontier.Algebra.Homology.KoszulSymmetric

/-!
# Tensoring a degreewise split short exact sequence of complexes

Let `C` be a monoidal preadditive category for which Mathlib's monoidal structure on
`CochainComplex C ℤ` (the total complex of the degreewise tensor product) exists. Then:

* the tensor product of complexes is additive in each variable, i.e. `CochainComplex C ℤ` is
  monoidal preadditive;
* if `0 → A → B → C → 0` is a short exact sequence of complexes which is split in each degree,
  then so is `0 → A ⊗ X → B ⊗ X → C ⊗ X → 0` for every complex `X`; in particular it is short
  exact;
* if `2 • 𝟙` is invertible on every object of `C`, it is invertible on every complex.

## Main definitions

* `CochainComplex.tensorRightSplitting`: the degreewise splitting of `S ⊗ X` built from a
  degreewise splitting of `S`, summand by summand.

## Main results

* `CochainComplex.monoidalPreadditive_of_monoidalPreadditive`: complexes are monoidal
  preadditive.
* `CochainComplex.shortExact_map_tensorRight_of_degreewiseSplit`: `S ⊗ X` is short exact.
* `CochainComplex.isIso_two_smul_id`: `2` is invertible on complexes.

## Implementation notes

Every identity is checked on the homogeneous summands `K^p ⊗ X^q` of the total complex, by
`HomologicalComplex.mapBifunctor.hom_ext` and `CochainComplex.ιTensorObj_whiskerRight`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe v u

namespace CochainComplex

/-- **`2` is invertible on complexes** as soon as it is invertible on every object. -/
instance isIso_two_smul_id {C : Type u} [Category.{v} C] [Preadditive C]
    [∀ X : C, IsIso ((2 : ℤ) • 𝟙 X)] (K : CochainComplex C ℤ) : IsIso ((2 : ℤ) • 𝟙 K) := by
  have (n : ℤ) : IsIso (((2 : ℤ) • 𝟙 K).f n) := by
    rw [HomologicalComplex.zsmul_f_apply, HomologicalComplex.id_f]
    infer_instance
  exact HomologicalComplex.Hom.isIso_of_components _

section Preadditive

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] [HasZeroObject C]
  [∀ (X₁ X₂ : GradedObject ℤ C), GradedObject.HasTensor X₁ X₂]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

/-! ### Additivity of the tensor product of complexes -/

/-- **The tensor product of complexes is additive in each variable.** -/
instance monoidalPreadditive_of_monoidalPreadditive :
    MonoidalPreadditive (CochainComplex C ℤ) where
  whiskerLeft_zero {K _ _} := by
    ext n : 1
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro i j h
    simp [ιTensorObj_whiskerLeft]
  zero_whiskerRight {K _ _} := by
    ext n : 1
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro i j h
    simp [ιTensorObj_whiskerRight]
  whiskerLeft_add {K _ _} f g := by
    ext n : 1
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro i j h
    simp [ιTensorObj_whiskerLeft, MonoidalPreadditive.whiskerLeft_add]
  add_whiskerRight {K _ _} f g := by
    ext n : 1
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro i j h
    simp [ιTensorObj_whiskerRight, MonoidalPreadditive.add_whiskerRight]

/-! ### Degreewise split short exact sequences -/

variable (S : ShortComplex (CochainComplex C ℤ))
  (σ : ∀ n, (S.map (HomologicalComplex.eval C (ComplexShape.up ℤ) n)).Splitting)
  (X : CochainComplex C ℤ)

/-- **The degreewise splitting of `S ⊗ X`**: on the summand `B^p ⊗ X^q` the retraction and the
section are those of `S` in degree `p`, whiskered by `X^q`. -/
def tensorRightSplitting (n : ℤ) :
    ((S.map (tensorRight X)).map (HomologicalComplex.eval C (ComplexShape.up ℤ) n)).Splitting
    where
  r := HomologicalComplex.mapBifunctorDesc (K₁ := S.X₂) (K₂ := X) (F := curriedTensor C)
    (c := ComplexShape.up ℤ) (j := n)
    (fun p q h => (σ p).r ▷ X.X q ≫ HomologicalComplex.ιTensorObj S.X₁ X p q n h)
  s := HomologicalComplex.mapBifunctorDesc (K₁ := S.X₃) (K₂ := X) (F := curriedTensor C)
    (c := ComplexShape.up ℤ) (j := n)
    (fun p q h => (σ p).s ▷ X.X q ≫ HomologicalComplex.ιTensorObj S.X₂ X p q n h)
  f_r := by
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q h
    have := (σ p).f_r
    dsimp at this ⊢
    simp only [ιTensorObj_whiskerRight_assoc, HomologicalComplex.ι_mapBifunctorDesc,
      ← comp_whiskerRight_assoc, this, id_whiskerRight, Category.id_comp]
    exact (Category.comp_id _).symm
  s_g := by
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q h
    have := (σ p).s_g
    dsimp at this ⊢
    simp only [HomologicalComplex.ι_mapBifunctorDesc_assoc, Category.assoc,
      ιTensorObj_whiskerRight, ← comp_whiskerRight_assoc, this, id_whiskerRight,
      Category.id_comp]
    exact (Category.comp_id _).symm
  id := by
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q h
    have := (σ p).id
    dsimp at this ⊢
    simp only [Preadditive.comp_add, HomologicalComplex.ι_mapBifunctorDesc_assoc,
      Category.assoc, ιTensorObj_whiskerRight, ιTensorObj_whiskerRight_assoc]
    simp only [HomologicalComplex.ιTensorObj, HomologicalComplex.ι_mapBifunctorDesc,
      ← comp_whiskerRight_assoc, ← Preadditive.add_comp, ← MonoidalPreadditive.add_whiskerRight,
      this, id_whiskerRight, Category.id_comp]
    exact (Category.comp_id _).symm

end Preadditive

section Abelian

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C]
  [∀ (X₁ X₂ : GradedObject ℤ C), GradedObject.HasTensor X₁ X₂]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  (S : ShortComplex (CochainComplex C ℤ))
  (σ : ∀ n, (S.map (HomologicalComplex.eval C (ComplexShape.up ℤ) n)).Splitting)
  (X : CochainComplex C ℤ)

include σ in
/-- **Tensoring a degreewise split short exact sequence of complexes with a complex gives a
short exact sequence.** -/
theorem shortExact_map_tensorRight_of_degreewiseSplit :
    (S.map (tensorRight X)).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _
    (fun n => (tensorRightSplitting S σ X n).shortExact)

end Abelian

end CochainComplex

end
