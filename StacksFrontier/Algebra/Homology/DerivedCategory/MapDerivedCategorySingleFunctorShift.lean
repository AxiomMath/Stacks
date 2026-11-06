module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Shift.SingleFunctors

/-!
# The single-functor comparison of an exact functor commutes with shifts

Let `F : C₁ ⥤ C₂` be an exact additive functor between abelian categories and write
`F.mapDerivedCategory : D(C₁) ⥤ D(C₂)` for the induced functor. Mathlib's
`CategoryTheory.Functor.mapDerivedCategorySingleFunctor n` identifies `F(A[-n])` with `(F A)[-n]`
separately in each degree `n`. This file proves that these identifications are compatible with
the identifications `A[-q] ≅ (A[0])[-q]` of a single complex with the shift of the single complex
in degree `0` (`DerivedCategory.singleFunctors`), the derived functor being moved past the shift
by its `CommShift` structure: the family is an isomorphism of `CategoryTheory.SingleFunctors`.

## Main definitions

* `Stacks.MapDerivedCategorySingleShift.precomp`: precomposition of a family of single functors
  with a functor.
* `Stacks.MapDerivedCategorySingleShift.mapDerivedCategorySingleFunctorsIso`: the isomorphism of
  single functors `(single ⋙ F.mapDerivedCategory) ≅ (F ⋙ single)` whose components are
  `CategoryTheory.Functor.mapDerivedCategorySingleFunctor`.

## Main results

* `Stacks.MapDerivedCategorySingleShift.commShiftIso_inv_app_comp_map_singleFunctors_shiftIso_hom`
  and its inverse form
  `Stacks.MapDerivedCategorySingleShift.map_singleFunctors_shiftIso_inv_comp_commShiftIso_hom`:
  for `A : C₁` and `q : ℤ`, transporting `(A[0])[-q] ≅ A[-q]` along `F.mapDerivedCategory`
  through the shift comparison of `F.mapDerivedCategory` and the single-functor comparisons in
  degrees `0` and `q` gives `((F A)[0])[-q] ≅ (F A)[-q]`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w₁ w₂ v₁ v₂ v₃ u₁ u₂ u₃

namespace Stacks.MapDerivedCategorySingleShift

section Precomp

variable {C₁ : Type u₁} [Category.{v₁} C₁] {C₂ : Type u₂} [Category.{v₂} C₂]
  {D : Type u₃} [Category.{v₃} D] [Preadditive D] [HasShift D ℤ]

/-- **Precomposition of a family of single functors with a functor** `F : C₁ ⥤ C₂`: the functors
`F ⋙ S.functor a`, with the shift isomorphisms of `S` whiskered by `F`. -/
@[simps functor]
def precomp (F : C₁ ⥤ C₂) (S : SingleFunctors C₂ D ℤ) : SingleFunctors C₁ D ℤ where
  functor a := F ⋙ S.functor a
  shiftIso n a a' ha' :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft F (S.shiftIso n a a' ha')
  shiftIso_zero a := by
    ext X
    simp [S.shiftIso_zero_hom_app]
  shiftIso_add n m a a' a'' ha' ha'' := by
    ext X
    simp [S.shiftIso_add_hom_app n m a a' a'' ha' ha'']

omit [Preadditive D] in
/-- The shift isomorphisms of `precomp F S` at `X` are those of `S` at `F.obj X`. -/
@[simp]
lemma precomp_shiftIso_hom_app (F : C₁ ⥤ C₂) (S : SingleFunctors C₂ D ℤ) (n a a' : ℤ)
    (ha' : n + a = a') (X : C₁) :
    ((precomp F S).shiftIso n a a' ha').hom.app X = (S.shiftIso n a a' ha').hom.app (F.obj X) := by
  simp [precomp]

end Precomp

section Exact

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂]
  (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- At the level of cochain complexes, applying `F` degreewise to the single complexes is
precomposing the single complexes with `F`, compatibly with shifts. -/
def mapHomologicalComplexSingleFunctorsIso :
    (CochainComplex.singleFunctors C₁).postcomp (F.mapHomologicalComplex (ComplexShape.up ℤ)) ≅
      precomp F (CochainComplex.singleFunctors C₂) :=
  SingleFunctors.isoMk
    (fun a => HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) a)
    (fun n a a' ha' => by
      ext X i
      obtain rfl : a' = a + n := by omega
      by_cases h : i = a
      · subst h
        simp only [CochainComplex.singleFunctors, Functor.comp_obj,
          CochainComplex.shiftFunctor_obj_X', SingleFunctors.postcomp_functor,
          Functor.mapHomologicalComplex_obj_X, NatTrans.comp_app,
          SingleFunctors.postcomp_shiftIso_hom_app, NatIso.ofComponents_hom_app, Category.assoc,
          HomologicalComplex.comp_f, Functor.mapHomologicalComplex_commShiftIso_inv_app_f,
          Functor.mapHomologicalComplex_map_f, HomologicalComplex.Hom.isoOfComponents_hom_f,
          eqToIso.hom, eqToHom_map, HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
          HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq, eqToIso.inv,
          eqToHom_trans, Category.id_comp, Functor.whiskerRight_app, precomp_shiftIso_hom_app]
        change _ = ((shiftFunctor (HomologicalComplex C₂ (ComplexShape.up ℤ)) n).map
            ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) (i + n)).hom.app
              X)).f i ≫ (HomologicalComplex.Hom.isoOfComponents _ _).hom.f i
        rw [CochainComplex.shiftFunctor_map_f',
          HomologicalComplex.singleMapHomologicalComplex_hom_app_self]
        simp only [HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq,
          eqToHom_map, eqToIso.hom]
        dsimp only [HomologicalComplex.Hom.isoOfComponents]
        simp only [eqToIso.hom, eqToIso.inv, eqToHom_trans]
        exact (eqToHom_trans _ _).trans (eqToHom_trans _ _).symm
      · apply IsZero.eq_of_tgt
        exact HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) a (F.obj X) i h)

variable [HasDerivedCategory.{w₁} C₁] [HasDerivedCategory.{w₂} C₂]

/-- The isomorphism `(single ⋙ F.mapDerivedCategory) ≅ (F ⋙ single)` of families of single
functors into `D(C₂)`. Its components are `CategoryTheory.Functor.mapDerivedCategorySingleFunctor`
(`mapDerivedCategorySingleFunctorsIso_hom_hom_app`); being an isomorphism of single functors, it
is compatible with the shift isomorphisms. -/
def mapDerivedCategorySingleFunctorsIso :
    (DerivedCategory.singleFunctors C₁).postcomp F.mapDerivedCategory ≅
      precomp F (DerivedCategory.singleFunctors C₂) :=
  SingleFunctors.postcompPostcompIso (CochainComplex.singleFunctors C₁) DerivedCategory.Q
      F.mapDerivedCategory ≪≫
    SingleFunctors.postcompIsoOfIso (CochainComplex.singleFunctors C₁)
      F.mapDerivedCategoryFactors ≪≫
    (SingleFunctors.postcompPostcompIso (CochainComplex.singleFunctors C₁)
      (F.mapHomologicalComplex (ComplexShape.up ℤ)) DerivedCategory.Q).symm ≪≫
    (SingleFunctors.postcompFunctor C₁ ℤ DerivedCategory.Q).mapIso
      (mapHomologicalComplexSingleFunctorsIso F) ≪≫
    SingleFunctors.isoMk (fun _ => Functor.associator _ _ _) (fun n a a' ha' => by
      ext X
      simp [precomp, DerivedCategory.singleFunctors])

/-- The components of `mapDerivedCategorySingleFunctorsIso` are Mathlib's single-functor
comparisons. -/
lemma mapDerivedCategorySingleFunctorsIso_hom_hom_app (a : ℤ) (A : C₁) :
    ((mapDerivedCategorySingleFunctorsIso F).hom.hom a).app A =
      (F.mapDerivedCategorySingleFunctor a).hom.app A := by
  simp only [SingleFunctors.postcomp_functor, Functor.comp_obj,
    mapDerivedCategorySingleFunctorsIso, SingleFunctors.postcompFunctor_obj,
    mapHomologicalComplexSingleFunctorsIso, SingleFunctors.isoMk, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, SingleFunctors.comp_hom, SingleFunctors.postcompFunctor_map_hom,
    NatTrans.comp_app, SingleFunctors.postcompPostcompIso_hom_hom_app,
    SingleFunctors.postcompIsoOfIso_hom_hom_app, SingleFunctors.postcompPostcompIso_inv_hom_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Category.id_comp,
    Functor.mapDerivedCategorySingleFunctor, DerivedCategory.singleFunctorIsoCompQ,
    Functor.isoWhiskerRight_refl, Functor.isoWhiskerLeft_refl, Iso.refl_symm, Iso.refl_trans,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Iso.refl_hom,
    Functor.whiskerLeft_app, Functor.associator_inv_app, DerivedCategory.Q_obj_single_obj,
    NatTrans.id_app, Category.comp_id]
  erw [Category.comp_id, Category.id_comp]
  rfl

/-- **The single-functor comparisons of an exact functor commute with shifts.** For `A : C₁` and
`q : ℤ`, write `s : (A[0])[-q] ≅ A[-q]` for the shift isomorphism of the single functors. Then
undoing the shift comparison of `F.mapDerivedCategory`, applying `F(s)` and the comparison
`F(A[-q]) ≅ (F A)[-q]` is the same as shifting `F(A[0]) ≅ (F A)[0]` and applying `s` for `F A`. -/
theorem commShiftIso_inv_app_comp_map_singleFunctors_shiftIso_hom (q : ℤ) (A : C₁) :
    (F.mapDerivedCategory.commShiftIso (-q)).inv.app
        ((DerivedCategory.singleFunctor C₁ 0).obj A) ≫
      F.mapDerivedCategory.map
        (((DerivedCategory.singleFunctors C₁).shiftIso (-q) q 0 (by omega)).hom.app A) ≫
      (F.mapDerivedCategorySingleFunctor q).hom.app A =
    ((F.mapDerivedCategorySingleFunctor 0).hom.app A)⟦-q⟧' ≫
      ((DerivedCategory.singleFunctors C₂).shiftIso (-q) q 0 (by omega)).hom.app (F.obj A) := by
  have hc := congrArg (fun t => NatTrans.app t A)
    ((mapDerivedCategorySingleFunctorsIso F).hom.comm (-q) q 0 (by omega))
  simp only [NatTrans.comp_app, SingleFunctors.postcomp_shiftIso_hom_app,
    Functor.whiskerRight_app, precomp_shiftIso_hom_app,
    mapDerivedCategorySingleFunctorsIso_hom_hom_app] at hc
  exact (Category.assoc _ _ _).symm.trans hc

/-- `commShiftIso_inv_app_comp_map_singleFunctors_shiftIso_hom`, with the shift isomorphisms of
the single functors inverted: `F(s⁻¹)` followed by the shift comparison and by
`(F(A[0]) ≅ (F A)[0])[-q]` is the comparison `F(A[-q]) ≅ (F A)[-q]` followed by `s⁻¹`. -/
theorem map_singleFunctors_shiftIso_inv_comp_commShiftIso_hom (q : ℤ) (A : C₁) :
    F.mapDerivedCategory.map
        (((DerivedCategory.singleFunctors C₁).shiftIso (-q) q 0 (by omega)).inv.app A) ≫
      (F.mapDerivedCategory.commShiftIso (-q)).hom.app
        ((DerivedCategory.singleFunctor C₁ 0).obj A) ≫
      ((F.mapDerivedCategorySingleFunctor 0).hom.app A)⟦-q⟧' =
    (F.mapDerivedCategorySingleFunctor q).hom.app A ≫
      ((DerivedCategory.singleFunctors C₂).shiftIso (-q) q 0 (by omega)).inv.app (F.obj A) := by
  rw [← cancel_mono (((DerivedCategory.singleFunctors C₂).shiftIso (-q) q 0 (by omega)).hom.app
    (F.obj A))]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [← commShiftIso_inv_app_comp_map_singleFunctors_shiftIso_hom F q A]
  simp [← Functor.map_comp_assoc]

end Exact

end Stacks.MapDerivedCategorySingleShift

end
