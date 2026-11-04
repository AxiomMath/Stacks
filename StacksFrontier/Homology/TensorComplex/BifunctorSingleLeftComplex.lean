module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
public import Mathlib.Algebra.Homology.Single

/-!
# `Tot(F(N[0], K))` is `F(N, -)` applied degreewise to `K`

Let `F : C₁ ⥤ C₂ ⥤ D` be a bifunctor between preadditive categories preserving zero morphisms in
each variable, let `N` be an object of `C₁` and let `K` be a cochain complex in `C₂`. In degree
`i` the total complex `Tot(F(N[0], K))` is a biproduct over the pairs `(a, b)` with `a + b = i` of
the objects `F(N[0]^a, K^b)`, and all of them vanish except the one at `(0, i)`; so the degree-`i`
term is `F(N, K^i)`. The differential coming from the first variable vanishes because `N[0]` has
zero differential, and the sign the second one carries at bidegree `(0, i)` is `+1`, so the
comparison is an isomorphism of complexes onto the degreewise image of `K` under `F(N, -)`.

## Main results

* `HomologicalComplex.singleLeftXIso`: the degree-`i` term of `Tot(F(N[0], K))` is `F(N, K^i)`.
* `HomologicalComplex.mapBifunctorSingleLeftIso`: `Tot(F(N[0], K)) ≅ F(N, -)` applied degreewise
  to `K`, as an isomorphism of complexes.

## References

* [Stacks Project, Tag 0662](https://stacks.math.columbia.edu/tag/0662)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

universe v₁ v₂ v u₁ u₂ u

variable {C₁ : Type u₁} {C₂ : Type u₂} {D : Type u} [Category.{v₁} C₁] [Category.{v₂} C₂]
  [Category.{v} D] [Preadditive C₁] [Preadditive C₂] [Preadditive D] [HasZeroObject C₁]
  (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms]
  [∀ M : C₁, (F.obj M).PreservesZeroMorphisms]
  (N : C₁) (K : CochainComplex C₂ ℤ)

/-- A bifunctor preserving zero morphisms in its first variable does so after flipping. -/
instance preservesZeroMorphisms_flip_obj (Y : C₂) :
    (F.flip.obj Y).PreservesZeroMorphisms where
  map_zero X X' := by
    change (F.map (0 : X ⟶ X')).app Y = 0
    rw [F.map_zero]
    rfl

omit [∀ M : C₁, (F.obj M).PreservesZeroMorphisms] in
/-- Away from degree zero in the first variable, the bifunctor applied to the terms of a complex
concentrated in degree zero and of `K` vanishes. -/
theorem isZero_obj_obj_single_obj_X_left (a b : ℤ) (ha : a ≠ 0) :
    IsZero ((F.obj (((CochainComplex.singleFunctor C₁ 0).obj N).X a)).obj (K.X b)) :=
  (F.flip.obj (K.X b)).map_isZero (isZero_single_obj_X _ 0 N a ha)

variable [HasMapBifunctor ((CochainComplex.singleFunctor C₁ 0).obj N) K F (ComplexShape.up ℤ)]

/-- The inclusion of the summand of bidegree `(0, i)` into the degree-`i` term of
`Tot(F(N[0], K))`. It is the only summand that does not vanish. -/
def singleLeftι (i : ℤ) :
    (F.obj (((CochainComplex.singleFunctor C₁ 0).obj N).X 0)).obj (K.X i) ⟶
      (mapBifunctor ((CochainComplex.singleFunctor C₁ 0).obj N) K F
        (ComplexShape.up ℤ)).X i :=
  ιMapBifunctor ((CochainComplex.singleFunctor C₁ 0).obj N) K F (ComplexShape.up ℤ) 0 i i
    (by simp)

/-- The projection of the degree-`i` term of `Tot(F(N[0], K))` onto the summand of bidegree
`(0, i)`. -/
def singleLeftπ (i : ℤ) :
    (mapBifunctor ((CochainComplex.singleFunctor C₁ 0).obj N) K F
        (ComplexShape.up ℤ)).X i ⟶
      (F.obj (((CochainComplex.singleFunctor C₁ 0).obj N).X 0)).obj (K.X i) :=
  mapBifunctorDesc fun a b hab =>
    if h : a = 0 then by
      subst h
      have hb : b = i := by simpa using hab
      subst hb
      exact 𝟙 _
    else 0

/-- The projection `singleLeftπ` is a retraction of the inclusion `singleLeftι`. -/
theorem singleLeftι_π (i : ℤ) :
    singleLeftι F N K i ≫ singleLeftπ F N K i = 𝟙 _ := by
  simp [singleLeftι, singleLeftπ]

/-- The projection `singleLeftπ` followed by the inclusion `singleLeftι` is the identity of the
degree-`i` term of `Tot(F(N[0], K))`. -/
theorem singleLeftπ_ι (i : ℤ) :
    singleLeftπ F N K i ≫ singleLeftι F N K i = 𝟙 _ := by
  refine mapBifunctor.hom_ext fun a b hab => ?_
  by_cases ha : a = 0
  · subst ha
    have hb : b = i := by simpa using hab
    subst hb
    simp [singleLeftι, singleLeftπ]
  · exact (isZero_obj_obj_single_obj_X_left F N K a b ha).eq_of_src _ _

/-- **The degree-`i` term of `Tot(F(N[0], K))` is `F(N, K^i)`**: the summand of bidegree `(0, i)`
is the whole biproduct. -/
def singleLeftXIso (i : ℤ) :
    (mapBifunctor ((CochainComplex.singleFunctor C₁ 0).obj N) K F
        (ComplexShape.up ℤ)).X i ≅
      (F.obj N).obj (K.X i) :=
  (⟨singleLeftι F N K i, singleLeftπ F N K i, singleLeftι_π F N K i,
      singleLeftπ_ι F N K i⟩ :
    (F.obj (((CochainComplex.singleFunctor C₁ 0).obj N).X 0)).obj (K.X i) ≅ _).symm ≪≫
    ((F.mapIso (singleObjXSelf (ComplexShape.up ℤ) 0 N)).app (K.X i))

/-- The inverse of `singleLeftXIso` is the identification of `N` with the degree-zero term of
`N[0]`, followed by the inclusion `singleLeftι` of the summand of bidegree `(0, i)`. -/
theorem singleLeftXIso_inv (i : ℤ) :
    (singleLeftXIso F N K i).inv =
      (F.map (singleObjXSelf (ComplexShape.up ℤ) 0 N).inv).app (K.X i) ≫
        singleLeftι F N K i :=
  rfl

/-- On the summand of bidegree `(0, i)`, the comparison `singleLeftXIso` is the identification of
the degree-zero term of `N[0]` with `N`. -/
@[reassoc]
theorem singleLeftι_singleLeftXIso_hom (i : ℤ) :
    singleLeftι F N K i ≫ (singleLeftXIso F N K i).hom =
      (F.map (singleObjXSelf (ComplexShape.up ℤ) 0 N).hom).app (K.X i) := by
  have h : (singleLeftXIso F N K i).hom =
      singleLeftπ F N K i ≫
        (F.map (singleObjXSelf (ComplexShape.up ℤ) 0 N).hom).app (K.X i) := rfl
  rw [h, ← Category.assoc, singleLeftι_π, Category.id_comp]

/-- **The total differential of `Tot(F(N[0], K))` is the differential of `K`.** The summand of
bidegree `(0, i)` is carried to the summand of bidegree `(0, i + 1)` by `F(N, d_K)`, with no sign;
the first total differential vanishes because `N[0]` has zero differential. -/
theorem singleLeftι_d (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
    singleLeftι F N K i ≫
        (mapBifunctor ((CochainComplex.singleFunctor C₁ 0).obj N) K F
          (ComplexShape.up ℤ)).d i j =
      (F.obj (((CochainComplex.singleFunctor C₁ 0).obj N).X 0)).map (K.d i j) ≫
        singleLeftι F N K j := by
  have hd₁ : mapBifunctor.d₁ ((CochainComplex.singleFunctor C₁ 0).obj N) K F
      (ComplexShape.up ℤ) 0 i j = 0 := by
    rw [mapBifunctor.d₁_eq' ((CochainComplex.singleFunctor C₁ 0).obj N) K F
      (ComplexShape.up ℤ) (show (ComplexShape.up ℤ).Rel 0 1 by simp) i j]
    simp
  rw [mapBifunctor.d_eq, Preadditive.comp_add, singleLeftι, mapBifunctor.ι_D₁,
    mapBifunctor.ι_D₂, hd₁, zero_add,
    mapBifunctor.d₂_eq ((CochainComplex.singleFunctor C₁ 0).obj N) K F (ComplexShape.up ℤ)
      0 hij j (by simp)]
  simp [singleLeftι]

/-- **`F(N, -)` applied degreewise to `K` is `Tot(F(N[0], K))`.** -/
def singleLeftIsoMapBifunctor [(F.obj N).Additive] :
    ((F.obj N).mapHomologicalComplex (ComplexShape.up ℤ)).obj K ≅
      mapBifunctor ((CochainComplex.singleFunctor C₁ 0).obj N) K F (ComplexShape.up ℤ) :=
  Hom.isoOfComponents (fun i => (singleLeftXIso F N K i).symm) fun i j hij => by
    rw [Iso.symm_hom, Iso.symm_hom, singleLeftXIso_inv, singleLeftXIso_inv,
      Category.assoc, singleLeftι_d F N K i j hij]
    simp only [Functor.mapHomologicalComplex_obj_d, ← Category.assoc]
    exact congrArg (fun g => g ≫ singleLeftι F N K j)
      (((F.map (singleObjXSelf (ComplexShape.up ℤ) 0 N).inv)).naturality (K.d i j)).symm

/-- **`Tot(F(N[0], K))` is `F(N, -)` applied degreewise to `K`.** -/
def mapBifunctorSingleLeftIso [(F.obj N).Additive] :
    mapBifunctor ((CochainComplex.singleFunctor C₁ 0).obj N) K F (ComplexShape.up ℤ) ≅
      ((F.obj N).mapHomologicalComplex (ComplexShape.up ℤ)).obj K :=
  (singleLeftIsoMapBifunctor F N K).symm

section Naturality

variable {M : C₁} [(F.obj M).Additive] [(F.obj N).Additive]
  [HasMapBifunctor ((CochainComplex.singleFunctor C₁ 0).obj M) K F (ComplexShape.up ℤ)]

/-- **The identification `Tot(F(N[0], K)) ≅ F(N, -)` applied degreewise is natural in `N`.** A
map `ψ : M ⟶ N` acts on the total complex of the first variable through the summand of bidegree
`(0, i)`, where it is `F(ψ, K^i)` conjugated by the identifications of the degree-zero terms of
`M[0]` and `N[0]`; those identifications are exactly the ones the comparison contains, so they
cancel. -/
theorem singleLeftIsoMapBifunctor_hom_naturality_left (ψ : M ⟶ N) :
    (singleLeftIsoMapBifunctor F M K).hom ≫
        mapBifunctorMap ((CochainComplex.singleFunctor C₁ 0).map ψ) (𝟙 K) F
          (ComplexShape.up ℤ) =
      (NatTrans.mapHomologicalComplex (F.map ψ) (ComplexShape.up ℤ)).app K ≫
        (singleLeftIsoMapBifunctor F N K).hom := by
  ext i
  have hmid : (F.map (singleObjXSelf (ComplexShape.up ℤ) 0 M).inv).app (K.X i) ≫
        (F.map (((CochainComplex.singleFunctor C₁ 0).map ψ).f 0)).app (K.X i) =
      (F.map ψ).app (K.X i) ≫
        (F.map (singleObjXSelf (ComplexShape.up ℤ) 0 N).inv).app (K.X i) := by
    have hψ0 : ((CochainComplex.singleFunctor C₁ 0).map ψ).f 0 =
        (singleObjXSelf (ComplexShape.up ℤ) 0 M).hom ≫ ψ ≫
          (singleObjXSelf (ComplexShape.up ℤ) 0 N).inv :=
      single_map_f_self (ComplexShape.up ℤ) 0 ψ
    rw [← NatTrans.comp_app, ← F.map_comp, ← NatTrans.comp_app, ← F.map_comp, hψ0,
      Iso.inv_hom_id_assoc]
  have hι : singleLeftι F M K i ≫
        (mapBifunctorMap ((CochainComplex.singleFunctor C₁ 0).map ψ) (𝟙 K) F
          (ComplexShape.up ℤ)).f i =
      (F.map (((CochainComplex.singleFunctor C₁ 0).map ψ).f 0)).app (K.X i) ≫
        singleLeftι F N K i := by
    rw [singleLeftι, ι_mapBifunctorMap]
    simp [singleLeftι]
  show (singleLeftXIso F M K i).inv ≫
      (mapBifunctorMap ((CochainComplex.singleFunctor C₁ 0).map ψ) (𝟙 K) F
        (ComplexShape.up ℤ)).f i =
    (F.map ψ).app (K.X i) ≫ (singleLeftXIso F N K i).inv
  rw [singleLeftXIso_inv, singleLeftXIso_inv, Category.assoc, hι, ← Category.assoc, hmid,
    Category.assoc]

end Naturality

end HomologicalComplex

end
