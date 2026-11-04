module

public import StacksFrontier.Homology.TensorComplex.SingleBifunctorTensor

/-!
# The identification `Tot(F(M[0], N[0])) ≅ F(M, N)[0]` in degree zero

`HomologicalComplex.mapBifunctorSingleIso` identifies the total complex of a bifunctor `F`
applied to two complexes concentrated in degree zero with `F(M, N)` placed in degree zero.  This
file computes its degree-zero component, in both directions, and on the `(0, 0)` summand of the
total complex; the other summands vanish, so this last equation determines the isomorphism.

## Main results

* `HomologicalComplex.mapBifunctorSingleIso_hom_f_zero` and
  `HomologicalComplex.mapBifunctorSingleIso_inv_f_zero`: the degree-zero components.
* `HomologicalComplex.ι_mapBifunctorSingleIso_hom`: the isomorphism on the `(0, 0)` summand.
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

/-- **The degree-zero component of
`HomologicalComplex.mapBifunctorSingleIso`** is
`HomologicalComplex.mapBifunctorSingleXZeroIso`: that is how the isomorphism is defined there,
and the two targets are the same object. -/
lemma mapBifunctorSingleIso_hom_f_zero :
    (mapBifunctorSingleIso F M N).hom.f 0 = (mapBifunctorSingleXZeroIso F M N).hom :=
  rfl

/-- **The inverse of the identification of `Tot(F(M[0], N[0]))` with `F(M, N)[0]` in degree
zero** is the coprojection of the `(0, 0)` summand, preceded by the bifunctor applied to the two
identifications of the degree-zero terms of `M[0]` and `N[0]` read backwards.  This is the
definition of `HomologicalComplex.mapBifunctorSingleXZeroIso` unfolded. -/
@[reassoc]
lemma mapBifunctorSingleIso_inv_f_zero :
    (mapBifunctorSingleIso F M N).inv.f 0 =
      ((F.obj M).map (singleObjXSelf (ComplexShape.up ℤ) 0 N).inv ≫
          (F.map (singleObjXSelf (ComplexShape.up ℤ) 0 M).inv).app
            (((CochainComplex.singleFunctor C₂ 0).obj N).X 0)) ≫
        ιMapBifunctor ((CochainComplex.singleFunctor C₁ 0).obj M)
          ((CochainComplex.singleFunctor C₂ 0).obj N) F (ComplexShape.up ℤ) 0 0 0 (by simp) :=
  rfl

/-- **The identification of `Tot(F(M[0], N[0]))` with `F(M, N)[0]` on the `(0, 0)` summand.**
Every other summand of the total complex vanishes, so this determines the isomorphism: it
inverts the coprojection of the `(0, 0)` summand, and what is left is the bifunctor applied to
the two identifications of the degree-zero terms of `M[0]` and `N[0]`. -/
@[reassoc]
lemma ι_mapBifunctorSingleIso_hom :
    ιMapBifunctor ((CochainComplex.singleFunctor C₁ 0).obj M)
          ((CochainComplex.singleFunctor C₂ 0).obj N) F (ComplexShape.up ℤ) 0 0 0 (by simp) ≫
        (mapBifunctorSingleIso F M N).hom.f 0 =
      (F.map (singleObjXSelf (ComplexShape.up ℤ) 0 M).hom).app
          (((CochainComplex.singleFunctor C₂ 0).obj N).X 0) ≫
        (F.obj M).map (singleObjXSelf (ComplexShape.up ℤ) 0 N).hom := by
  refine Eq.trans ((Iso.inv_comp_eq
    ((F.mapIso (singleObjXSelf (ComplexShape.up ℤ) 0 M)).app
          (((CochainComplex.singleFunctor C₂ 0).obj N).X 0) ≪≫
        (F.obj M).mapIso (singleObjXSelf (ComplexShape.up ℤ) 0 N))).mp ?_) (Category.comp_id _)
  show ((F.obj M).map (singleObjXSelf (ComplexShape.up ℤ) 0 N).inv ≫
        (F.map (singleObjXSelf (ComplexShape.up ℤ) 0 M).inv).app
          (((CochainComplex.singleFunctor C₂ 0).obj N).X 0)) ≫
      (ιMapBifunctor ((CochainComplex.singleFunctor C₁ 0).obj M)
            ((CochainComplex.singleFunctor C₂ 0).obj N) F (ComplexShape.up ℤ) 0 0 0 (by simp) ≫
          (mapBifunctorSingleIso F M N).hom.f 0) = 𝟙 _
  rw [← Category.assoc, ← mapBifunctorSingleIso_inv_f_zero]
  exact congrArg (fun φ => HomologicalComplex.Hom.f φ 0)
    (Iso.inv_hom_id (mapBifunctorSingleIso F M N))


end HomologicalComplex

end
