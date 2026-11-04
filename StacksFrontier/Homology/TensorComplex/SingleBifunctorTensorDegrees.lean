module

public import StacksFrontier.Homology.TensorComplex.SingleBifunctorTensor

/-!
# The total complex of a bifunctor applied to two complexes concentrated in one degree each

Let `F : C₁ ⥤ C₂ ⥤ D` be a bifunctor between preadditive categories which is additive in each
variable, and let `M` and `N` be objects of `C₁` and `C₂` placed in the degrees `a` and `b`. The
total complex `Tot(F(M[-a], N[-b]))` has a single possibly nonzero summand, the one indexed by
`(a, b)`, so it is `F(M, N)` placed in degree `a + b`.

## Main definitions

* `HomologicalComplex.mapBifunctorSingleSingleIso`: the isomorphism
  `Tot(F(M[-a], N[-b])) ≅ F(M, N)[-a-b]`.

## Main results

* `HomologicalComplex.ι_mapBifunctorSingleSingleIso_hom_f`: on the summand `(a, b)` the
  isomorphism is the identification of the two terms with `M` and `N`.

The case `a = b = 0` is `HomologicalComplex.mapBifunctorSingleIso`.

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
  (F : C₁ ⥤ C₂ ⥤ D) [F.Additive] [∀ M : C₁, (F.obj M).Additive] (M : C₁) (N : C₂) (a b : ℤ)
  [HasMapBifunctor ((single C₁ (ComplexShape.up ℤ) a).obj M)
    ((single C₂ (ComplexShape.up ℤ) b).obj N) F (ComplexShape.up ℤ)]

omit [HasZeroObject D]
  [HasMapBifunctor ((single C₁ (ComplexShape.up ℤ) a).obj M)
    ((single C₂ (ComplexShape.up ℤ) b).obj N) F (ComplexShape.up ℤ)] in
/-- Off the pair `(a, b)` the bifunctor applied to the terms of two single complexes vanishes. -/
theorem isZero_obj_obj_single_obj_X_X (i j : ℤ) (h : i ≠ a ∨ j ≠ b) :
    IsZero ((F.obj (((single C₁ (ComplexShape.up ℤ) a).obj M).X i)).obj
      (((single C₂ (ComplexShape.up ℤ) b).obj N).X j)) := by
  rcases h with hi | hj
  · exact (F.flip.obj (((single C₂ (ComplexShape.up ℤ) b).obj N).X j)).map_isZero
      (isZero_single_obj_X _ a M i hi)
  · exact (F.obj (((single C₁ (ComplexShape.up ℤ) a).obj M).X i)).map_isZero
      (isZero_single_obj_X _ b N j hj)

omit [HasZeroObject D] in
/-- The total complex vanishes outside degree `a + b`. -/
theorem isZero_mapBifunctor_single_single_X (k : ℤ) (hk : k ≠ a + b) :
    IsZero ((mapBifunctor ((single C₁ (ComplexShape.up ℤ) a).obj M)
      ((single C₂ (ComplexShape.up ℤ) b).obj N) F (ComplexShape.up ℤ)).X k) := by
  rw [IsZero.iff_id_eq_zero]
  refine mapBifunctor.hom_ext fun i j hij => ?_
  refine (isZero_obj_obj_single_obj_X_X F M N a b i j ?_).eq_of_src _ _
  have hij' : i + j = k := hij
  by_cases hi : i = a
  · exact Or.inr (by omega)
  · exact Or.inl hi

omit [HasZeroObject D] in
/-- In degree `a + b` the total complex is the summand `(a, b)`: its inclusion is an
isomorphism. -/
theorem isIso_ιMapBifunctor_single_single :
    IsIso (ιMapBifunctor ((single C₁ (ComplexShape.up ℤ) a).obj M)
      ((single C₂ (ComplexShape.up ℤ) b).obj N) F (ComplexShape.up ℤ) a b (a + b) rfl) := by
  refine ⟨mapBifunctorDesc fun i j hij => if h : i = a ∧ j = b then
    eqToHom (by rw [h.1, h.2]) else 0, ?_, ?_⟩
  · simp
  · refine mapBifunctor.hom_ext fun i j hij => ?_
    by_cases h : i = a ∧ j = b
    · obtain ⟨rfl, rfl⟩ := h
      simp
    · exact (isZero_obj_obj_single_obj_X_X F M N a b i j (not_and_or.mp h)).eq_of_src _ _

/-- In degree `a + b`, the total complex of a bifunctor applied to `M[-a]` and `N[-b]` is the
value of the bifunctor at `M` and `N`. -/
def mapBifunctorSingleSingleXIso :
    (mapBifunctor ((single C₁ (ComplexShape.up ℤ) a).obj M)
      ((single C₂ (ComplexShape.up ℤ) b).obj N) F (ComplexShape.up ℤ)).X (a + b) ≅
      (F.obj M).obj N :=
  haveI := isIso_ιMapBifunctor_single_single F M N a b
  (asIso (ιMapBifunctor ((single C₁ (ComplexShape.up ℤ) a).obj M)
      ((single C₂ (ComplexShape.up ℤ) b).obj N) F (ComplexShape.up ℤ) a b (a + b) rfl)).symm ≪≫
    (F.mapIso (singleObjXSelf (ComplexShape.up ℤ) a M)).app _ ≪≫
    (F.obj M).mapIso (singleObjXSelf (ComplexShape.up ℤ) b N)

/-- **The total complex of a bifunctor applied to two single complexes is a single complex**:
`Tot(F(M[-a], N[-b])) ≅ F(M, N)[-a-b]`. -/
def mapBifunctorSingleSingleIso :
    mapBifunctor ((single C₁ (ComplexShape.up ℤ) a).obj M)
      ((single C₂ (ComplexShape.up ℤ) b).obj N) F (ComplexShape.up ℤ) ≅
      (single D (ComplexShape.up ℤ) (a + b)).obj ((F.obj M).obj N) := by
  refine Hom.isoOfComponents (fun k => if hk : k = a + b then
      (mapBifunctor ((single C₁ (ComplexShape.up ℤ) a).obj M)
        ((single C₂ (ComplexShape.up ℤ) b).obj N) F (ComplexShape.up ℤ)).XIsoOfEq hk ≪≫
        mapBifunctorSingleSingleXIso F M N a b ≪≫
        (singleObjXIsoOfEq (ComplexShape.up ℤ) (a + b) _ k hk).symm
    else (isZero_mapBifunctor_single_single_X F M N a b k hk).iso
      (isZero_single_obj_X _ (a + b) _ k hk)) ?_
  · intro i j hij
    by_cases hi : i = a + b
    · subst hi
      have hj : j ≠ a + b := by
        have hij' : a + b + 1 = j := hij
        omega
      exact (isZero_single_obj_X _ (a + b) _ j hj).eq_of_tgt _ _
    · exact (isZero_mapBifunctor_single_single_X F M N a b i hi).eq_of_src _ _

/-- The isomorphism in degree `a + b`. -/
theorem mapBifunctorSingleSingleIso_hom_f :
    (mapBifunctorSingleSingleIso F M N a b).hom.f (a + b) =
      (mapBifunctorSingleSingleXIso F M N a b).hom ≫
        (singleObjXSelf (ComplexShape.up ℤ) (a + b) ((F.obj M).obj N)).inv := by
  simp [mapBifunctorSingleSingleIso, singleObjXSelf]

/-- **On the summand `(a, b)`, the isomorphism is the identification of the two terms with `M`
and `N`.** -/
@[reassoc]
theorem ι_mapBifunctorSingleSingleIso_hom_f :
    ιMapBifunctor ((single C₁ (ComplexShape.up ℤ) a).obj M)
        ((single C₂ (ComplexShape.up ℤ) b).obj N) F (ComplexShape.up ℤ) a b (a + b) rfl ≫
      (mapBifunctorSingleSingleIso F M N a b).hom.f (a + b) =
    (F.map (singleObjXSelf (ComplexShape.up ℤ) a M).hom).app _ ≫
      (F.obj M).map (singleObjXSelf (ComplexShape.up ℤ) b N).hom ≫
      (singleObjXSelf (ComplexShape.up ℤ) (a + b) ((F.obj M).obj N)).inv := by
  rw [mapBifunctorSingleSingleIso_hom_f]
  simp [mapBifunctorSingleSingleXIso]

end HomologicalComplex

end
