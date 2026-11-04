module

public import Mathlib.Algebra.Homology.BifunctorAssociator
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

/-!
# The total complex of a bifunctor applied to two complexes concentrated in degree zero

Let `F : C₁ ⥤ C₂ ⥤ D` be a bifunctor between preadditive categories which is additive in each
variable, and let `M` and `N` be objects of `C₁` and `C₂`. The total complex
`Tot(F(M[0], N[0]))` has a single possibly nonzero summand, in degree zero, so it is
`F(M, N)[0]`.

## Main definitions

* `HomologicalComplex.mapBifunctorSingleIso`: the isomorphism
  `Tot(F(M[0], N[0])) ≅ F(M, N)[0]`.

## Implementation notes

The degree-`k` term of the total complex is a biproduct over the pairs `(i, j)` with `i + j = k`
of the objects `F(M[0]^i, N[0]^j)`, and all of those vanish unless `i = j = 0`; so the term
vanishes for `k ≠ 0` and is `F(M, N)` for `k = 0`. The isomorphism in degree zero is the
inclusion of the `(0, 0)` summand, with the dual description by `mapBifunctorDesc` as its
inverse, and the differentials are between objects one of which is zero.

This is the companion, in the other variable, of
`TotalTensorComplex.SingleTensor.singleTensorIso`, which identifies `Tot(N[0] ⊗ D)` for an
*arbitrary* second complex `D` but needs a monoidal structure on the ambient category and the
total complexes of every pair of complexes. Here both factors are concentrated in degree zero
and the bifunctor is arbitrary, so neither hypothesis is needed and only the one total complex
has to exist. The specialization of `singleTensorIso` would be the same statement for a
monoidal category; it is not used because the instances it asks for are stated at
`curriedTensor` and a derived tensor product presents the same bifunctor under a different
name.

## References

* [Stacks Project, Tag 0662](https://stacks.math.columbia.edu/tag/0662)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

universe v₁ v₂ v u₁ u₂ u

variable {C₁ : Type u₁} {C₂ : Type u₂} {D : Type u} [Category.{v₁} C₁] [Category.{v₂} C₂]
  [Category.{v} D] [Preadditive C₁] [Preadditive C₂] [Preadditive D]
  [HasZeroObject C₁] [HasZeroObject C₂] [HasZeroObject D]
  (F : C₁ ⥤ C₂ ⥤ D) [F.Additive] [∀ M : C₁, (F.obj M).Additive] (M : C₁) (N : C₂)
  [HasMapBifunctor ((CochainComplex.singleFunctor C₁ 0).obj M)
    ((CochainComplex.singleFunctor C₂ 0).obj N) F (ComplexShape.up ℤ)]

omit [HasZeroObject D]
  [HasMapBifunctor ((CochainComplex.singleFunctor C₁ 0).obj M)
    ((CochainComplex.singleFunctor C₂ 0).obj N) F (ComplexShape.up ℤ)] in
/-- Off the pair `(0, 0)` the bifunctor applied to the terms of two complexes concentrated in
degree zero vanishes. -/
theorem isZero_obj_obj_single_obj_X (i j : ℤ) (h : i ≠ 0 ∨ j ≠ 0) :
    IsZero ((F.obj (((CochainComplex.singleFunctor C₁ 0).obj M).X i)).obj
      (((CochainComplex.singleFunctor C₂ 0).obj N).X j)) := by
  rcases h with hi | hj
  · exact (F.flip.obj (((CochainComplex.singleFunctor C₂ 0).obj N).X j)).map_isZero
      (isZero_single_obj_X _ 0 M i hi)
  · exact (F.obj (((CochainComplex.singleFunctor C₁ 0).obj M).X i)).map_isZero
      (isZero_single_obj_X _ 0 N j hj)

omit [HasZeroObject D] in
/-- The total complex of a bifunctor applied to two complexes concentrated in degree zero
vanishes outside degree zero. -/
theorem isZero_mapBifunctor_single_X (k : ℤ) (hk : k ≠ 0) :
    IsZero ((mapBifunctor ((CochainComplex.singleFunctor C₁ 0).obj M)
      ((CochainComplex.singleFunctor C₂ 0).obj N) F (ComplexShape.up ℤ)).X k) := by
  rw [IsZero.iff_id_eq_zero]
  refine mapBifunctor.hom_ext fun i j hij => ?_
  refine (isZero_obj_obj_single_obj_X F M N i j ?_).eq_of_src _ _
  change i + j = k at hij
  omega

/-- In degree zero, the total complex of a bifunctor applied to two complexes concentrated in
degree zero is the value of the bifunctor: the `(0, 0)` summand is the whole biproduct. -/
def mapBifunctorSingleXZeroIso :
    (mapBifunctor ((CochainComplex.singleFunctor C₁ 0).obj M)
      ((CochainComplex.singleFunctor C₂ 0).obj N) F (ComplexShape.up ℤ)).X 0 ≅
      (F.obj M).obj N := by
  let K := (CochainComplex.singleFunctor C₁ 0).obj M
  let L := (CochainComplex.singleFunctor C₂ 0).obj N
  let q := ιMapBifunctor K L F (ComplexShape.up ℤ) 0 0 0 (by simp)
  let p : (mapBifunctor K L F (ComplexShape.up ℤ)).X 0 ⟶ (F.obj (K.X 0)).obj (L.X 0) :=
    mapBifunctorDesc fun a b hab =>
      if h : a = 0 then by
        subst a
        have hb : b = 0 := by simpa using hab
        subst b
        exact 𝟙 _
      else 0
  have hqp : q ≫ p = 𝟙 _ := by simp [q, p]
  have hpq : p ≫ q = 𝟙 _ := by
    refine mapBifunctor.hom_ext fun a b hab => ?_
    by_cases ha : a = 0
    · subst a
      obtain rfl : b = 0 := by simpa using hab
      simp [q, p]
    · exact (isZero_obj_obj_single_obj_X F M N a b (Or.inl ha)).eq_of_src _ _
  exact (⟨q, p, hqp, hpq⟩ : (F.obj (K.X 0)).obj (L.X 0) ≅ _).symm ≪≫
    (F.mapIso (singleObjXSelf (ComplexShape.up ℤ) 0 M)).app (L.X 0) ≪≫
    (F.obj M).mapIso (singleObjXSelf (ComplexShape.up ℤ) 0 N)

/-- **The total complex of a bifunctor applied to two complexes concentrated in degree zero is
the value of the bifunctor, in degree zero.** -/
def mapBifunctorSingleIso :
    mapBifunctor ((CochainComplex.singleFunctor C₁ 0).obj M)
      ((CochainComplex.singleFunctor C₂ 0).obj N) F (ComplexShape.up ℤ) ≅
      (CochainComplex.singleFunctor D 0).obj ((F.obj M).obj N) := by
  refine Hom.isoOfComponents (fun k => ?_) ?_
  · by_cases hk : k = 0
    · subst hk
      exact mapBifunctorSingleXZeroIso F M N
    · exact (isZero_mapBifunctor_single_X F M N k hk).iso (isZero_single_obj_X _ 0 _ k hk)
  · intro i j hij
    by_cases hi : i = 0
    · subst hi
      have hj : j ≠ 0 := by
        change (0 : ℤ) + 1 = j at hij
        omega
      exact (isZero_single_obj_X _ 0 _ j hj).eq_of_tgt _ _
    · exact (isZero_mapBifunctor_single_X F M N i hi).eq_of_src _ _

end HomologicalComplex

end
