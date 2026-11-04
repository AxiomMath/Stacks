module

public import Mathlib.Algebra.Homology.BifunctorShift

/-!
# The translation of a total complex is natural in the first variable

Let `F : C₁ ⥤ C₂ ⥤ D` be an additive bifunctor for which the total complexes `Tot(F(K₁, K₂))` of
cochain complexes exist. This file shows that the isomorphism
`Tot(F(K₁, K₂⟦y⟧)) ≅ Tot(F(K₁, K₂))⟦y⟧` of `CochainComplex.mapBifunctorShift₂Iso` is natural in
`K₁`.

## Main results

* `CochainComplex.mapBifunctorMap_comp_mapBifunctorShift₂Iso`: the isomorphism
  `Tot(F(K₁, K₂⟦y⟧)) ≅ Tot(F(K₁, K₂))⟦y⟧` is natural in the first variable.

## References

* [Stacks Project, Tag 0FNG](https://stacks.math.columbia.edu/tag/0FNG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace CochainComplex

section Naturality

variable {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]
  [Preadditive C₁] [Preadditive C₂] [Preadditive D]
  (F : C₁ ⥤ C₂ ⥤ D) [F.Additive] [∀ X₁ : C₁, (F.obj X₁).Additive]
  [∀ (K₁ : CochainComplex C₁ ℤ) (K₂ : CochainComplex C₂ ℤ), HasMapBifunctor K₁ K₂ F]

/-- **`CochainComplex.mapBifunctorShift₂Iso` is natural in the first variable.** For
`h : K₁ ⟶ L₁`, tensoring `h` with the identity of `K₂⟦y⟧` and then identifying
`Tot(F(L₁, K₂⟦y⟧))` with `Tot(F(L₁, K₂))⟦y⟧` is the same as identifying first and then
translating `h ⊗ 𝟙 K₂`. -/
@[reassoc]
theorem mapBifunctorMap_comp_mapBifunctorShift₂Iso
    {K₁ L₁ : CochainComplex C₁ ℤ} (h : K₁ ⟶ L₁) (K₂ : CochainComplex C₂ ℤ) (y : ℤ) :
    HomologicalComplex.mapBifunctorMap h
          (𝟙 ((CategoryTheory.shiftFunctor (CochainComplex C₂ ℤ) y).obj K₂)) F
          (ComplexShape.up ℤ) ≫
        (mapBifunctorShift₂Iso L₁ K₂ F y).hom =
      (mapBifunctorShift₂Iso K₁ K₂ F y).hom ≫
        (CategoryTheory.shiftFunctor (CochainComplex D ℤ) y).map
          (HomologicalComplex.mapBifunctorMap h (𝟙 K₂) F (ComplexShape.up ℤ)) :=
  (NatTrans.shift_app_comm (F.map₂CochainComplex.map h) y K₂).symm

end Naturality

end CochainComplex

end

end
