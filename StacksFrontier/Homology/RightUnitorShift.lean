module

public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import StacksFrontier.Homology.MapHomologicalComplexCommShift

/-!
# The right unitor of cochain complexes commutes with the shift

Let `C` be a monoidal preadditive category. For a cochain complex `K` of objects of `C` the right
unitor `K ⊗ 𝟙 ≅ K` of the tensor product of complexes is compatible with the shift in `K`: the
isomorphism `K⟦n⟧ ⊗ 𝟙 ≅ (K ⊗ 𝟙)⟦n⟧` of `CochainComplex.mapBifunctorShift₁Iso`, which involves no
sign, followed by the shift of the right unitor of `K`, is the right unitor of `K⟦n⟧`.

## Main results

* `CochainComplex.mapBifunctorShift₁Iso_hom_comp_shift_rightUnitor_hom` — the compatibility.
* `CochainComplex.commShift_rightUnitorNatIso_hom` — the same, as the statement that the right
  unitor `(- ⊗ 𝟙) ⟶ 𝟭` of the monoidal category of cochain complexes commutes with the shift.
* `CochainComplex.map₂CochainComplex_flip_obj_eq` and
  `CochainComplex.commShift_eqToHom_map₂CochainComplex_flip_obj` — two equal bifunctors give
  equal functors `K ↦ Tot(F(K, L))`, and the identification commutes with the shift.
-/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory

namespace CochainComplex

variable {C : Type*} [Category C] [MonoidalCategory C] [Preadditive C] [HasZeroObject C]
  [(curriedTensor C).Additive] [∀ X₁ : C, ((curriedTensor C).obj X₁).Additive]
  [∀ X₁ : C, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  (K : CochainComplex C ℤ) (n : ℤ)

/-- The inverse of the right unitor of `K⟦n⟧` followed by `K⟦n⟧ ⊗ 𝟙 ≅ (K ⊗ 𝟙)⟦n⟧` is the shift
of the inverse of the right unitor of `K`. -/
theorem rightUnitor_inv_comp_mapBifunctorShift₁Iso_hom :
    (HomologicalComplex.rightUnitor (K⟦n⟧)).inv ≫
        (mapBifunctorShift₁Iso K (HomologicalComplex.tensorUnit C (ComplexShape.up ℤ))
          (curriedTensor C) n).hom =
      (HomologicalComplex.rightUnitor K).inv⟦n⟧' := by
  have h (L : CochainComplex C ℤ) (i : ℤ) :
      (HomologicalComplex.rightUnitor L).inv.f i = (HomologicalComplex.rightUnitor' L).inv i :=
    rfl
  ext m
  rw [HomologicalComplex.comp_f, h, shiftFunctor_map_f', h, HomologicalComplex.rightUnitor'_inv,
    HomologicalComplex.rightUnitor'_inv, Category.assoc, Category.assoc,
    ι_mapBifunctorShift₁Iso_hom_f _ _ _ _ m 0 m (add_zero m) (m + n) (m + n) rfl rfl]
  simp [shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq]

/-- **The right unitor of cochain complexes commutes with the shift.** -/
theorem mapBifunctorShift₁Iso_hom_comp_shift_rightUnitor_hom :
    (mapBifunctorShift₁Iso K (HomologicalComplex.tensorUnit C (ComplexShape.up ℤ))
          (curriedTensor C) n).hom ≫ (HomologicalComplex.rightUnitor K).hom⟦n⟧' =
      (HomologicalComplex.rightUnitor (K⟦n⟧)).hom := by
  rw [← cancel_epi (HomologicalComplex.rightUnitor (K⟦n⟧)).inv, Iso.inv_hom_id,
    reassoc_of% (rightUnitor_inv_comp_mapBifunctorShift₁Iso_hom K n), ← Functor.map_comp,
    Iso.inv_hom_id, CategoryTheory.Functor.map_id]

section Monoidal

variable {E : Type*} [Category E] [MonoidalCategory E] [Preadditive E] [HasZeroObject E]
  [(curriedTensor E).Additive] [∀ X₁ : E, ((curriedTensor E).obj X₁).Additive]
  [∀ (X₁ X₂ : GradedObject ℤ E), GradedObject.HasTensor X₁ X₂]
  [∀ X₁ : E, PreservesColimit (Functor.empty.{0} E) ((curriedTensor E).obj X₁)]
  [∀ X₂ : E, PreservesColimit (Functor.empty.{0} E) ((curriedTensor E).flip.obj X₂)]
  [∀ X₁ X₂ X₃ X₄ : GradedObject ℤ E, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ X₁ X₂ X₃ : GradedObject ℤ E, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ X₁ X₂ X₃ : GradedObject ℤ E, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

/-- **The right unitor of the monoidal category of cochain complexes commutes with the shift**,
for the commutation of `- ⊗ 𝟙` with the shift of `CochainComplex.Monoidal.tensorRight_commShift`.
-/
instance commShift_rightUnitorNatIso_hom :
    NatTrans.CommShift (rightUnitorNatIso (CochainComplex E ℤ)).hom ℤ where
  shift_comm n := by
    refine NatTrans.ext (funext fun K => ?_)
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.commShiftIso_id_hom_app, rightUnitorNatIso_hom_app,
      Monoidal.tensorRight_commShiftIso_hom_app]
    exact (mapBifunctorShift₁Iso_hom_comp_shift_rightUnitor_hom K n).trans
      (Category.comp_id _).symm

/-- `- ⊗ L` on cochain complexes is `K ↦ Tot(K ⊗ L)`, the functor `map₂CochainComplex` of the
tensor bifunctor at `L`; this is the identity between the two spellings. -/
def map₂CochainComplexFlipObjToTensorRight (L : CochainComplex E ℤ) :
    (curriedTensor E).map₂CochainComplex.flip.obj L ⟶ tensorRight L :=
  𝟙 (tensorRight L)

/-- The identity between the two spellings of `- ⊗ L` commutes with the shift. -/
instance commShift_map₂CochainComplexFlipObjToTensorRight (L : CochainComplex E ℤ) :
    NatTrans.CommShift (map₂CochainComplexFlipObjToTensorRight L) ℤ :=
  inferInstanceAs (NatTrans.CommShift (𝟙 (tensorRight L)) ℤ)

end Monoidal

section Transport

variable {C₁ C₂ D : Type*} [Category C₁] [Category C₂] [Category D] [Preadditive C₁]
  [Preadditive C₂] [Preadditive D]

/-- Two equal bifunctors `F = G` give equal functors `K ↦ Tot(F(K, L))` and `K ↦ Tot(G(K, L))`,
whatever instances are used to form the total complexes. -/
theorem map₂CochainComplex_flip_obj_eq (F G : C₁ ⥤ C₂ ⥤ D) (h : F = G)
    [F.Additive] [∀ X₁ : C₁, (F.obj X₁).Additive]
    [∀ (K₁ : CochainComplex C₁ ℤ) (K₂ : CochainComplex C₂ ℤ), HasMapBifunctor K₁ K₂ F]
    [G.Additive] [∀ X₁ : C₁, (G.obj X₁).Additive]
    [∀ (K₁ : CochainComplex C₁ ℤ) (K₂ : CochainComplex C₂ ℤ), HasMapBifunctor K₁ K₂ G]
    (L : CochainComplex C₂ ℤ) :
    F.map₂CochainComplex.flip.obj L = G.map₂CochainComplex.flip.obj L := by
  subst h
  rfl

/-- The identification of `map₂CochainComplex_flip_obj_eq` commutes with the shift. -/
theorem commShift_eqToHom_map₂CochainComplex_flip_obj (F G : C₁ ⥤ C₂ ⥤ D) (h : F = G)
    [F.Additive] [∀ X₁ : C₁, (F.obj X₁).Additive]
    [∀ (K₁ : CochainComplex C₁ ℤ) (K₂ : CochainComplex C₂ ℤ), HasMapBifunctor K₁ K₂ F]
    [G.Additive] [∀ X₁ : C₁, (G.obj X₁).Additive]
    [∀ (K₁ : CochainComplex C₁ ℤ) (K₂ : CochainComplex C₂ ℤ), HasMapBifunctor K₁ K₂ G]
    (L : CochainComplex C₂ ℤ) :
    NatTrans.CommShift (eqToHom (map₂CochainComplex_flip_obj_eq F G h L)) ℤ := by
  subst h
  exact (inferInstance : NatTrans.CommShift (𝟙 (F.map₂CochainComplex.flip.obj L)) ℤ)

end Transport

end CochainComplex

end
