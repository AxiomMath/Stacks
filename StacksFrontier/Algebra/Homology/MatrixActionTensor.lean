module

public import StacksFrontier.Algebra.Homology.MatrixActionTotal

/-!
# The matrix action as tensoring with a finite free module

Let `A` be a commutative ring and `C` an `A`-linear category with finite biproducts, equipped
with a bifunctor `T : C ⥤ C ⥤ C` (a tensor product), an object `U` (its unit) and a right unitor
`T(-, U) ≅ 𝟭 C`.  If `T(X, -)` is additive and carries the scalar `a • 𝟙 U` to `a • 𝟙`, then
tensoring with the finite free module `⨁_ι U` is the matrix action:

`T(X, ⨁_ι U) ≅ ⨁_ι X`,

naturally in `X` and in the finite free module with its basis.  Consequently the total complex
`Tot(T(K, realize Q))` of a complex `K` with the realization of a complex `Q` of finite free
`A`-modules with chosen bases is the total complex `Tot(K ⊗_A Q)` of the matrix action.

## Main definitions

* `CategoryTheory.MatrixAction.tensorRealizeIso`: `T(X, ⨁_ι U) ≅ ⨁_ι X`.
* `CategoryTheory.MatrixAction.tensorRealizeBifunctorIso`: the same as an isomorphism of
  bifunctors `C ⥤ Mat_ (SingleObj A) ⥤ C`.
* `CategoryTheory.MatrixAction.bicomplexTensorRealizeIso`: the bicomplex `T(K, realize Q)` is the
  bicomplex of the matrix action.
* `CategoryTheory.MatrixAction.mapBifunctorTensorRealizeIso`:
  `Tot(T(K, realize Q)) ≅ Tot(K ⊗_A Q)` for cochain complexes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace CategoryTheory.MatrixAction

variable (A : Type w) [CommRing A]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear A C] [HasFiniteBiproducts C]
  (T : C ⥤ C ⥤ C) [T.Additive] [∀ X, (T.obj X).Additive] (U : C) (ρ : T.flip.obj U ≅ 𝟭 C)
  (hT : ∀ (X : C) (a : A), (T.obj X).map (a • 𝟙 U) = a • 𝟙 ((T.obj X).obj U))

/-- **Tensoring with a finite free module is the matrix action**: `T(X, ⨁_ι U) ≅ ⨁_ι X`. -/
def tensorRealizeIso (X : C) (M : Mat_ (SingleObj A)) :
    (T.obj X).obj ((realize A U).obj M) ≅ ((matrixAction A).obj X).obj M where
  hom := biproduct.lift fun i => (T.obj X).map (biproduct.π (fun _ : M.ι => U) i) ≫ ρ.hom.app X
  inv := biproduct.desc fun i => ρ.inv.app X ≫ (T.obj X).map (biproduct.ι (fun _ : M.ι => U) i)
  hom_inv_id := by
    rw [biproduct.lift_desc]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Functor.flip_obj_obj, ← Functor.map_comp,
      ← Functor.map_sum, biproduct.total, Functor.map_id]
  inv_hom_id := by
    refine biproduct.hom_ext _ _ fun j => biproduct.hom_ext' _ _ fun i => ?_
    simp only [Category.assoc, biproduct.lift_π, biproduct.ι_desc_assoc, ← Functor.map_comp_assoc]
    by_cases h : i = j
    · subst h
      simp
    · simp [biproduct.ι_π_ne _ h]

omit [T.Additive] in
/-- The `i`-th component of `T(X, ⨁_ι U) ≅ ⨁_ι X` is `T(X, π_i)` followed by the right unitor. -/
@[reassoc (attr := simp)]
lemma tensorRealizeIso_hom_π (X : C) (M : Mat_ (SingleObj A)) (i : M.ι) :
    (tensorRealizeIso A T U ρ X M).hom ≫ biproduct.π _ i =
      (T.obj X).map (biproduct.π (fun _ : M.ι => U) i) ≫ ρ.hom.app X :=
  biproduct.lift_π _ _

omit [T.Additive] in
include hT in
/-- The isomorphism `T(X, ⨁_ι U) ≅ ⨁_ι X` is natural in the finite free module. -/
@[reassoc]
lemma tensorRealizeIso_hom_naturality_right (X : C) {M N : Mat_ (SingleObj A)} (f : M ⟶ N) :
    (T.obj X).map ((realize A U).map f) ≫ (tensorRealizeIso A T U ρ X N).hom =
      (tensorRealizeIso A T U ρ X M).hom ≫ ((matrixAction A).obj X).map f := by
  classical
  refine biproduct.hom_ext _ _ fun j => ?_
  rw [Category.assoc, tensorRealizeIso_hom_π, ← Functor.map_comp_assoc, Category.assoc]
  show _ = _ ≫ realizeMap A X f ≫ _
  simp only [realizeMap, biproduct.matrix_π, biproduct.desc_eq, Functor.map_sum,
    Preadditive.sum_comp, Preadditive.comp_sum, Linear.comp_smul, Category.comp_id]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show entry A f i j • biproduct.π (fun _ : M.ι => U) i =
      biproduct.π (fun _ : M.ι => U) i ≫ (entry A f i j • 𝟙 U) by
    rw [Linear.comp_smul, Category.comp_id], Functor.map_comp, hT, Linear.comp_smul,
    Category.comp_id, Linear.smul_comp, tensorRealizeIso_hom_π]

omit [T.Additive] in
/-- The isomorphism `T(X, ⨁_ι U) ≅ ⨁_ι X` is natural in `X`. -/
@[reassoc]
lemma tensorRealizeIso_hom_naturality_left {X X' : C} (φ : X ⟶ X') (M : Mat_ (SingleObj A)) :
    (T.map φ).app ((realize A U).obj M) ≫ (tensorRealizeIso A T U ρ X' M).hom =
      (tensorRealizeIso A T U ρ X M).hom ≫ ((matrixAction A).map φ).app M := by
  refine biproduct.hom_ext _ _ fun j => ?_
  simp only [Category.assoc, tensorRealizeIso_hom_π, realizeNatTrans_app, biproduct.map_π,
    tensorRealizeIso_hom_π_assoc]
  rw [← NatTrans.naturality_assoc]
  congr 1
  exact ρ.hom.naturality φ

/-- **Tensoring with finite free modules is the matrix action**, as an isomorphism of bifunctors
`C ⥤ Mat_ (SingleObj A) ⥤ C`. -/
def tensorRealizeBifunctorIso :
    T ⋙ (Functor.whiskeringLeft _ _ _).obj (realize A U) ≅ matrixAction A :=
  NatIso.ofComponents
    (fun X => NatIso.ofComponents (fun M => tensorRealizeIso A T U ρ X M)
      fun f => tensorRealizeIso_hom_naturality_right A T U ρ hT X f)
    fun φ => NatTrans.ext (funext fun M => by
      simpa only [NatTrans.comp_app, NatIso.ofComponents_hom_app, Functor.comp_map,
        Functor.whiskeringLeft_obj_map, Functor.whiskerLeft_app] using
        tensorRealizeIso_hom_naturality_left A T U ρ φ M)

include hT in
/-- The bicomplex `T(Kᵖ, ⨁_{ι_q} U)` is the bicomplex of the matrix action. -/
def bicomplexTensorRealizeIso (K : CochainComplex C ℤ)
    (Q : CochainComplex (Mat_ (SingleObj A)) ℤ) :
    ((T.mapBifunctorHomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj K).obj
        (((realize A U).mapHomologicalComplex (ComplexShape.up ℤ)).obj Q) ≅
      (((matrixAction A).mapBifunctorHomologicalComplex (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)).obj K).obj Q :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p => HomologicalComplex.Hom.isoOfComponents
      (fun q => tensorRealizeIso A T U ρ (K.X p) (Q.X q))
      (fun q q' _ => (tensorRealizeIso_hom_naturality_right A T U ρ hT (K.X p) (Q.d q q')).symm))
    (fun p p' _ => by
      ext q
      exact (tensorRealizeIso_hom_naturality_left A T U ρ (K.d p p') (Q.X q)).symm)

variable [∀ (K : CochainComplex C ℤ) (Q : CochainComplex (Mat_ (SingleObj A)) ℤ),
      HomologicalComplex.HasMapBifunctor K Q (matrixAction A (C := C)) (ComplexShape.up ℤ)]

include ρ hT in
/-- The bicomplex `T(K, realize Q)` has a total complex. -/
lemma hasMapBifunctor_tensor_realize (K : CochainComplex C ℤ)
    (Q : CochainComplex (Mat_ (SingleObj A)) ℤ) :
    HomologicalComplex.HasMapBifunctor K
      (((realize A U).mapHomologicalComplex (ComplexShape.up ℤ)).obj Q) T (ComplexShape.up ℤ) :=
  HomologicalComplex₂.hasTotal_of_iso (bicomplexTensorRealizeIso A T U ρ hT K Q).symm _

include hT in
/-- **`Tot(T(K, realize Q)) ≅ Tot(K ⊗_A Q)`**: the total complex of the tensor product of a
complex with the realization of a complex of finite free `A`-modules with chosen bases is the
total complex of the matrix action. -/
def mapBifunctorTensorRealizeIso (K : CochainComplex C ℤ)
    (Q : CochainComplex (Mat_ (SingleObj A)) ℤ)
    [HomologicalComplex.HasMapBifunctor K
      (((realize A U).mapHomologicalComplex (ComplexShape.up ℤ)).obj Q) T (ComplexShape.up ℤ)] :
    HomologicalComplex.mapBifunctor K
        (((realize A U).mapHomologicalComplex (ComplexShape.up ℤ)).obj Q) T (ComplexShape.up ℤ) ≅
      (tot A Q).obj K :=
  HomologicalComplex₂.total.mapIso (bicomplexTensorRealizeIso A T U ρ hT K Q) _

end CategoryTheory.MatrixAction

end
