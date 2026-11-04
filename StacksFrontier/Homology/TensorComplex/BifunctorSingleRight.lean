module

public import StacksFrontier.Homology.TensorComplex.SingleBifunctorTensor

/-!
# The total complex of a bifunctor whose second argument is concentrated in degree zero

Let `F : C₁ ⥤ C₂ ⥤ D` be a bifunctor between preadditive categories which preserves zero
morphisms in each variable, let `K` be a cochain complex in `C₁` and let `N` be an object of `C₂`.
In degree `i` the total complex `Tot(F(K, N[0]))` is a biproduct over the pairs `(a, b)` with
`a + b = i` of the objects `F(K^a, N[0]^b)`, and all of them vanish except the one at `(i, 0)`;
so the degree-`i` term is `F(K^i, N)`.

## Main results

* `HomologicalComplex.mapBifunctorSingleRightXIso`: the degree-`i` term of `Tot(F(K, N[0]))` is
  `F(K^i, N)`.

## Implementation notes

Only the terms are identified; the differentials are not compared. The hypotheses are exactly
those of `HomologicalComplex.mapBifunctor`, and additivity of `F` is not assumed.

## References

* [Stacks Project, Tag 0662](https://stacks.math.columbia.edu/tag/0662)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

universe v₁ v₂ v u₁ u₂ u

variable {C₁ : Type u₁} {C₂ : Type u₂} {D : Type u} [Category.{v₁} C₁] [Category.{v₂} C₂]
  [Category.{v} D] [HasZeroMorphisms C₁] [Preadditive C₂] [Preadditive D] [HasZeroObject C₂]
  (F : C₁ ⥤ C₂ ⥤ D) [∀ M : C₁, (F.obj M).PreservesZeroMorphisms]
  (K : CochainComplex C₁ ℤ) (N : C₂)

/-- Away from degree zero in the second variable, the bifunctor applied to the terms of `K` and
of a complex concentrated in degree zero vanishes. -/
theorem isZero_obj_obj_single_obj_X_right (a b : ℤ) (hb : b ≠ 0) :
    IsZero ((F.obj (K.X a)).obj (((CochainComplex.singleFunctor C₂ 0).obj N).X b)) :=
  (F.obj (K.X a)).map_isZero (isZero_single_obj_X _ 0 N b hb)

variable [F.PreservesZeroMorphisms]
  [HasMapBifunctor K ((CochainComplex.singleFunctor C₂ 0).obj N) F (ComplexShape.up ℤ)]

/-- **The degree-`i` term of `Tot(F(K, N[0]))` is `F(K^i, N)`**: the summand at `(i, 0)` is the
whole biproduct. -/
def mapBifunctorSingleRightXIso (i : ℤ) :
    (mapBifunctor K ((CochainComplex.singleFunctor C₂ 0).obj N) F (ComplexShape.up ℤ)).X i ≅
      (F.obj (K.X i)).obj N := by
  let L := (CochainComplex.singleFunctor C₂ 0).obj N
  let q := ιMapBifunctor K L F (ComplexShape.up ℤ) i 0 i (by simp)
  let p : (mapBifunctor K L F (ComplexShape.up ℤ)).X i ⟶ (F.obj (K.X i)).obj (L.X 0) :=
    mapBifunctorDesc fun a b hab =>
      if h : b = 0 then by
        subst h
        have ha : a = i := by simpa using hab
        subst ha
        exact 𝟙 _
      else 0
  have hqp : q ≫ p = 𝟙 _ := by simp [q, p]
  have hpq : p ≫ q = 𝟙 _ := by
    refine mapBifunctor.hom_ext fun a b hab => ?_
    by_cases hb : b = 0
    · subst hb
      obtain rfl : a = i := by simpa using hab
      simp [q, p]
    · exact (isZero_obj_obj_single_obj_X_right F K N a b hb).eq_of_src _ _
  exact (⟨q, p, hqp, hpq⟩ : (F.obj (K.X i)).obj (L.X 0) ≅ _).symm ≪≫
    (F.obj (K.X i)).mapIso (singleObjXSelf (ComplexShape.up ℤ) 0 N)

end HomologicalComplex

end
