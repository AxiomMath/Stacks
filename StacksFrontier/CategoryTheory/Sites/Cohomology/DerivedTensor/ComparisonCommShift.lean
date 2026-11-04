module

public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
public import StacksFrontier.CategoryTheory.Shift.CommShiftTwoLocalization
public import StacksFrontier.CategoryTheory.Shift.DetectingCommShift
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackRightUnitor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BifunctorCommShiftTwo
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Existence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ExactnessCommShiftTwo

/-!
# The comparisons of the derived tensor product commute with the shift

Let `(C, 𝒪)` be a ringed site. For a complex `N`, the K-flat comparison
`Q P ⊗^L Q N ≅ Q Tot(P ⊗ N)` is natural in the K-flat complex `P` and commutes with the shift in
`P`; the unit law `- ⊗^L 𝒪 ≅ id` of the canonical derived tensor product commutes with the
shift.

## Main results

* `CochainComplex.commShift_of_ιMapBifunctor`: a comparison `G(Tot(K ⊗ L)) ⟶ Tot(GK ⊗ GL)`
  given summandwise commutes with the shift in `K`.
* `CochainComplex.commShift_of_ιMapBifunctor_single`: a transformation `Tot(F(K, L)) ⟶ K`, for
  `L` concentrated in degree zero, given summandwise commutes with the shift in `K`.
* `Stacks.SheafOfModules.kFlatComparisonFlipIso`, `Stacks.SheafOfModules.kFlatComparisonFlipIsoOf`:
  the K-flat comparison as an isomorphism of functors of the K-flat variable, commuting with
  the shift.
* `Stacks.SheafOfModules.tensorComplexUnitNatIso`: `Tot(K ⊗ 𝒪[0]) ≅ K`, commuting with the
  shift.
* `Stacks.SheafOfModules.unitNatIso_commShift`: the unit law of the canonical derived tensor
  product commutes with the shift.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe c u d v w

namespace CochainComplex

variable {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
  (G : C ⥤ D) [G.Additive] (FC : C ⥤ C ⥤ C) (FD : D ⥤ D ⥤ D)
  [FC.Additive] [∀ X, (FC.obj X).Additive] [FD.Additive] [∀ X, (FD.obj X).Additive]
  [∀ K₁ K₂ : CochainComplex C ℤ, HomologicalComplex.HasMapBifunctor K₁ K₂ FC (ComplexShape.up ℤ)]
  [∀ K₁ K₂ : CochainComplex D ℤ, HomologicalComplex.HasMapBifunctor K₁ K₂ FD (ComplexShape.up ℤ)]

omit [G.Additive] [FC.Additive] [∀ X, (FC.obj X).Additive] [FD.Additive]
  [∀ X, (FD.obj X).Additive] in
/-- The inclusion of the summand `(K₁[x])^{n₁} ⊗ K₂^{n₂}` into `Tot(K₁[x] ⊗ K₂)^n`, followed by
the shift isomorphism `Tot(K₁[x] ⊗ K₂) ≅ Tot(K₁ ⊗ K₂)[x]` in degree `n`, is the inclusion of the
summand `K₁^{n₁ + x} ⊗ K₂^{n₂}` into `Tot(K₁ ⊗ K₂)^{n + x}`. -/
lemma ιMapBifunctor_comp_mapBifunctorShift₁Iso_hom_f {E₁ E₂ E : Type*} [Category E₁]
    [Category E₂] [Category E] [Preadditive E₁] [Preadditive E₂] [Preadditive E]
    (K₁ : CochainComplex E₁ ℤ) (K₂ : CochainComplex E₂ ℤ) (F : E₁ ⥤ E₂ ⥤ E) [F.Additive]
    [∀ X, (F.obj X).Additive] (x : ℤ)
    [HomologicalComplex.HasMapBifunctor K₁ K₂ F (ComplexShape.up ℤ)]
    [HomologicalComplex.HasMapBifunctor
      ((CategoryTheory.shiftFunctor (CochainComplex E₁ ℤ) x).obj K₁) K₂ F (ComplexShape.up ℤ)]
    (n₁ n₂ n : ℤ) (h : n₁ + n₂ = n) :
    HomologicalComplex.ιMapBifunctor
          ((CategoryTheory.shiftFunctor (CochainComplex E₁ ℤ) x).obj K₁) K₂ F (ComplexShape.up ℤ)
          n₁ n₂ n h ≫
        (CochainComplex.mapBifunctorShift₁Iso K₁ K₂ F x).hom.f n =
      CochainComplex.ιMapBifunctor K₁ K₂ F (n₁ + x) n₂ (n + x) (by lia) := by
  simpa [CochainComplex.shiftFunctorObjXIso] using
    CochainComplex.ι_mapBifunctorShift₁Iso_hom_f K₁ K₂ F x n₁ n₂ n h (n₁ + x) (n + x) rfl rfl

/-- Auxiliary for `commShift_of_ιMapBifunctor`: the shift compatibility of `Φ` in degree `d`,
precomposed with the image under `G` of the inclusion of the summand `(K[n])^p ⊗ L^q`. -/
lemma commShift_of_ιMapBifunctor_aux (L K : CochainComplex C ℤ)
    (Φ : FC.map₂CochainComplex.flip.obj L ⋙ G.mapHomologicalComplex (ComplexShape.up ℤ) ⟶
      G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        FD.map₂CochainComplex.flip.obj ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj L))
    (σ : ∀ a b : C, G.obj ((FC.obj a).obj b) ⟶ (FD.obj (G.obj a)).obj (G.obj b))
    (hΦ : ∀ (K : CochainComplex C ℤ) (p q n : ℤ) (h : p + q = n),
      G.map (HomologicalComplex.ιMapBifunctor K L FC (ComplexShape.up ℤ) p q n h) ≫
          (Φ.app K).f n =
        σ (K.X p) (L.X q) ≫
          HomologicalComplex.ιMapBifunctor ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
            ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) FD (ComplexShape.up ℤ) p q n h)
    (n p q d : ℤ) (h : p + q = d) :
    G.map (HomologicalComplex.ιMapBifunctor
          ((CategoryTheory.shiftFunctor (CochainComplex C ℤ) n).obj K) L FC (ComplexShape.up ℤ)
          p q d h) ≫
        G.map ((CochainComplex.mapBifunctorShift₁Iso K L FC n).hom.f d) ≫ (Φ.app K).f (d + n) =
      G.map (HomologicalComplex.ιMapBifunctor
          ((CategoryTheory.shiftFunctor (CochainComplex C ℤ) n).obj K) L FC (ComplexShape.up ℤ)
          p q d h) ≫
        (Φ.app ((CategoryTheory.shiftFunctor (CochainComplex C ℤ) n).obj K)).f d ≫
          (HomologicalComplex.mapBifunctorMap
            (((G.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso n).hom.app K)
            (𝟙 ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj L)) FD (ComplexShape.up ℤ)).f d ≫
          (CochainComplex.mapBifunctorShift₁Iso
            ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
            ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) FD n).hom.f d := by
  have e1 := ιMapBifunctor_comp_mapBifunctorShift₁Iso_hom_f K L FC n p q d h
  have e2 := (G.map_comp _ _).symm.trans (congrArg G.map e1)
  have e3 := ιMapBifunctor_comp_mapBifunctorShift₁Iso_hom_f
    ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
    ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) FD n p q d h
  have e4 := HomologicalComplex.ι_mapBifunctorMap
    (((G.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso n).hom.app K)
    (𝟙 ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj L)) FD (ComplexShape.up ℤ) p q d h
  simp only [Functor.mapHomologicalComplex_commShiftIso_hom_app_f, HomologicalComplex.id_f,
    CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp] at e4
  refine ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (Φ.app K).f (d + n)) e2).trans
    (hΦ K (p + n) q (d + n) (by lia)))).trans ?_
  refine Eq.symm ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) (hΦ _ p q d h)).trans ?_))
  refine (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ?_)
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) e4).trans e3)

/-- A comparison of total complexes `G(Tot(K ⊗ L)) ≅ Tot(GK ⊗ GL)`, natural in `K` and given on
each summand by a comparison `σ` of the terms, commutes with the shift in `K`. -/
theorem commShift_of_ιMapBifunctor (L : CochainComplex C ℤ)
    (Φ : FC.map₂CochainComplex.flip.obj L ⋙ G.mapHomologicalComplex (ComplexShape.up ℤ) ⟶
      G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        FD.map₂CochainComplex.flip.obj ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj L))
    (σ : ∀ a b : C, G.obj ((FC.obj a).obj b) ⟶ (FD.obj (G.obj a)).obj (G.obj b))
    (hΦ : ∀ (K : CochainComplex C ℤ) (p q n : ℤ) (h : p + q = n),
      G.map (HomologicalComplex.ιMapBifunctor K L FC (ComplexShape.up ℤ) p q n h) ≫
          (Φ.app K).f n =
        σ (K.X p) (L.X q) ≫
          HomologicalComplex.ιMapBifunctor ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
            ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) FD (ComplexShape.up ℤ) p q n h)
    (hext : ∀ (K : CochainComplex C ℤ) (n : ℤ) {A : D}
      (u v : G.obj ((HomologicalComplex.mapBifunctor K L FC (ComplexShape.up ℤ)).X n) ⟶ A),
      (∀ (p q : ℤ) (h : p + q = n),
        G.map (HomologicalComplex.ιMapBifunctor K L FC (ComplexShape.up ℤ) p q n h) ≫ u =
          G.map (HomologicalComplex.ιMapBifunctor K L FC (ComplexShape.up ℤ) p q n h) ≫ v) →
      u = v) :
    NatTrans.CommShift Φ ℤ where
  shift_comm n := by
    ext K d
    dsimp
    refine hext _ d _ _ (fun p q h => ?_)
    rw [Functor.commShiftIso_comp_hom_app, Functor.commShiftIso_comp_hom_app,
      HomologicalComplex.comp_f, HomologicalComplex.comp_f]
    simp only [Functor.mapHomologicalComplex_commShiftIso_hom_app_f, Functor.comp_obj,
      Category.comp_id]
    exact commShift_of_ιMapBifunctor_aux G FC FD L K Φ σ hΦ n p q d h


section Single

variable {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
  (FC : C ⥤ D ⥤ C) [FC.Additive] [∀ X, (FC.obj X).Additive]
  [∀ (K₁ : CochainComplex C ℤ) (K₂ : CochainComplex D ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ FC (ComplexShape.up ℤ)]

/-- A transformation `Tot(F(K, L)) ⟶ K`, natural in `K`, for a complex `L` concentrated in
degree zero, given on the summand `F(K^p, L^0)` by a morphism `σ` independent of the complex,
commutes with the shift in `K`. -/
theorem commShift_of_ιMapBifunctor_single (L : CochainComplex D ℤ)
    (hL : ∀ q : ℤ, q ≠ 0 → IsZero (L.X q))
    (Φ : FC.map₂CochainComplex.flip.obj L ⟶ 𝟭 (CochainComplex C ℤ))
    (σ : ∀ A : C, (FC.obj A).obj (L.X 0) ⟶ A)
    (hΦ : ∀ (K : CochainComplex C ℤ) (n : ℤ) (h : n + 0 = n),
      HomologicalComplex.ιMapBifunctor K L FC (ComplexShape.up ℤ) n 0 n h ≫ (Φ.app K).f n =
        σ (K.X n)) :
    NatTrans.CommShift Φ ℤ where
  shift_comm m := by
    ext K d
    dsimp
    refine HomologicalComplex.mapBifunctor.hom_ext (fun p q h => ?_)
    rw [Functor.commShiftIso_id_hom_app, HomologicalComplex.id_f]
    refine Eq.trans ?_ (congrArg (_ ≫ ·) (Category.comp_id _).symm)
    by_cases hq : q = 0
    · subst hq
      obtain rfl : p = d := by simpa using h
      have e1 := ιMapBifunctor_comp_mapBifunctorShift₁Iso_hom_f K L FC m p 0 p h
      have e2 : ((CategoryTheory.shiftFunctor (CochainComplex C ℤ) m).map (Φ.app K)).f p =
          (Φ.app K).f (p + m) := rfl
      refine Eq.trans ?_ (hΦ _ p h).symm
      exact ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ (Φ.app K).f (p + m)) e1).trans (hΦ K (p + m) (by lia))))
    · exact (Functor.map_isZero _ (hL q hq)).eq_of_src _ _

end Single

end CochainComplex

namespace Stacks.SheafOfModules

variable (X : AlgebraicGeometry.RingedSite.{c, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u, u, u} X.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [HasDerivedCategory.{d}
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O))]

attribute [local instance] derivedTensorBifunctorLifting

/-- For a complex `N`, the K-flat comparison `Q P ⊗^L Q N ≅ Q Tot(P ⊗ N)` as an isomorphism of
functors of the K-flat complex `P`. -/
noncomputable def kFlatComparisonFlipIso
    (N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    kFlatComplexQ X ⋙ (derivedTensorBifunctor X).flip.obj (DerivedCategory.Q.obj N) ≅
      (kFlatComplexes X).ι ⋙
        (Stacks.SheafOfModules.Tensor.sheafTensor X.O).map₂CochainComplex.flip.obj N ⋙
        DerivedCategory.Q :=
  letI := Localization.Lifting₂.snd (kFlatComplexQ X) DerivedCategory.Q
    (kFlatComplexQuasiIso X)
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ))
    (kFlatTensorToDerived X) (derivedTensorBifunctor X) N
  Localization.Lifting.iso (kFlatComplexQ X) (kFlatComplexQuasiIso X)
    ((kFlatTensorToDerived X).flip.obj N)
    ((derivedTensorBifunctor X).flip.obj (DerivedCategory.Q.obj N))

/-- The component of `kFlatComparisonFlipIso` at a K-flat complex `P` is the K-flat comparison
of `P` and `N`. -/
lemma kFlatComparisonFlipIso_hom_app
    (N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (P : (kFlatComplexes X).FullSubcategory) :
    (kFlatComparisonFlipIso X N).hom.app P = (kFlatComparison X P.obj P.property N).hom := rfl

/-- The K-flat comparison commutes with the shift in the K-flat variable. -/
instance kFlatComparisonFlipIso_commShift
    (N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    NatTrans.CommShift (kFlatComparisonFlipIso X N).hom ℤ :=
  Localization.objCommShift_fst_iso_hom (M := ℤ) DerivedCategory.Q
    (kFlatComplexQ X)
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ))
    (kFlatComplexQuasiIso X) (kFlatTensorToDerived X).flip (derivedTensorBifunctor X).flip N

/-- For a K-flat complex `P`, the canonical map to the total tensor complex is the K-flat
comparison. -/
lemma toTensor_eq_kFlatComparison
    {P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (hP : IsKFlat X.O P)
    (N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    toTensor X P N = (kFlatComparison X P hP N).hom := by
  simpa using toTensor_comp_of_kFlat X hP (𝟙 P) N

variable {X} in
/-- The K-flat comparison `Q P ⊗^L Q N ≅ Q Tot(P ⊗ N)` as an isomorphism of functors of `V`, for a
functor `ι'` to complexes commuting with the shift whose values are K-flat. -/
noncomputable def kFlatComparisonFlipIsoOf {V : Type*} [Category V] [HasShift V ℤ]
    (ι' : V ⥤ CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [ι'.CommShift ℤ] (hι' : ∀ P, IsKFlat X.O (ι'.obj P))
    (N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    ι' ⋙ DerivedCategory.Q ⋙ (derivedTensorBifunctor X).flip.obj (DerivedCategory.Q.obj N) ≅
      ι' ⋙ (Stacks.SheafOfModules.Tensor.sheafTensor X.O).map₂CochainComplex.flip.obj N ⋙
        DerivedCategory.Q :=
  Functor.isoWhiskerRight ((kFlatComplexes X).liftCompιIso ι' hι').symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerLeft ((kFlatComplexes X).lift ι' hι') (kFlatComparisonFlipIso X N) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ((kFlatComplexes X).liftCompιIso ι' hι') _

variable {X} in
/-- The K-flat comparison `kFlatComparisonFlipIsoOf ι' hι' N` commutes with the shift. -/
instance kFlatComparisonFlipIsoOf_commShift {V : Type*} [Category V] [HasShift V ℤ]
    (ι' : V ⥤ CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [ι'.CommShift ℤ] (hι' : ∀ P, IsKFlat X.O (ι'.obj P))
    (N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    NatTrans.CommShift (kFlatComparisonFlipIsoOf ι' hι' N).hom ℤ := by
  -- Mathlib's instances for `ObjectProperty.lift` are not found by instance search here.
  let : ((kFlatComplexes X).lift ι' hι').CommShift ℤ :=
    ObjectProperty.instCommShiftFullSubcategoryLift _ _ _
  have : NatTrans.CommShift ((kFlatComplexes X).liftCompιIso ι' hι').hom ℤ :=
    Functor.CommShift.ofComp_compatibility _ _
  dsimp only [kFlatComparisonFlipIsoOf, Iso.trans_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Iso.symm_hom]
  infer_instance

variable {X} in
/-- The component of `kFlatComparisonFlipIsoOf ι' hι' N` at `P` is the K-flat comparison of
`ι'.obj P` and `N`. -/
lemma kFlatComparisonFlipIsoOf_hom_app {V : Type*} [Category V] [HasShift V ℤ]
    (ι' : V ⥤ CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [ι'.CommShift ℤ] (hι' : ∀ P, IsKFlat X.O (ι'.obj P))
    (N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (P : V) :
    (kFlatComparisonFlipIsoOf ι' hι' N).hom.app P =
      (kFlatComparison X (ι'.obj P) (hι' P) N).hom := by
  simp only [kFlatComparisonFlipIsoOf, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Iso.symm_hom, Functor.associator_hom_app,
    Functor.associator_inv_app, kFlatComparisonFlipIso_hom_app, ObjectProperty.liftCompιIso,
    Iso.refl_inv, Iso.refl_hom, NatTrans.id_app, CategoryTheory.Functor.map_id, Functor.comp_obj,
    ObjectProperty.ι_obj, Functor.comp_map, Category.id_comp, Category.comp_id]
  exact ((congrArg (· ≫ _) ((congrArg ((derivedTensorBifunctor X).flip.obj
    (DerivedCategory.Q.obj N)).map (DerivedCategory.Q.map_id _)).trans
      (CategoryTheory.Functor.map_id _ _))).trans (Category.id_comp _)).trans
        (Category.comp_id _)

variable {X} in
/-- The component of `kFlatComparisonFlipIsoOf ι' hι' N` at `P` is the K-flat comparison of
`ι'.obj P` and `N`, as an isomorphism. -/
lemma kFlatComparisonFlipIsoOf_app {V : Type*} [Category V] [HasShift V ℤ]
    (ι' : V ⥤ CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [ι'.CommShift ℤ] (hι' : ∀ P, IsKFlat X.O (ι'.obj P))
    (N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (P : V) :
    (kFlatComparisonFlipIsoOf ι' hι' N).app P = kFlatComparison X (ι'.obj P) (hι' P) N :=
  Iso.ext (kFlatComparisonFlipIsoOf_hom_app ι' hι' N P)

end Stacks.SheafOfModules

namespace Stacks.SheafOfModules

section Unit

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (S : Sheaf J CommRingCat.{w}) [HasWeakSheafify J AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} S).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} S).obj M).Additive]
  [∀ (K L : CochainComplex (_root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf S)) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor S)
      (ComplexShape.up ℤ)]

/-- The unit law `Tot(K ⊗_𝒪 𝒪[0]) ≅ K` as an isomorphism of functors of `K`. -/
noncomputable def tensorComplexUnitNatIso :
    (Stacks.SheafOfModules.Tensor.sheafTensor S).map₂CochainComplex.flip.obj
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
          (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf S))) ≅
      𝟭 (CochainComplex (_root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf S)) ℤ) :=
  NatIso.ofComponents (fun K => tensorComplexUnitIsoFreeSections S K)
    (fun φ => tensorComplexUnitIsoFreeSections_naturality S φ)

/-- The unit law `Tot(K ⊗_𝒪 𝒪[0]) ≅ K` commutes with the shift in `K`. -/
instance tensorComplexUnitNatIso_commShift :
    NatTrans.CommShift (tensorComplexUnitNatIso S).hom ℤ :=
  CochainComplex.commShift_of_ιMapBifunctor_single (Stacks.SheafOfModules.Tensor.sheafTensor S)
    ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
      (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf S)))
    (fun q hq => HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 _ q hq)
    (tensorComplexUnitNatIso S).hom
    (fun A => ((Stacks.SheafOfModules.Tensor.sheafTensor S).obj A).map
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf S))).hom ≫
      (sheafTensorUnitIsoFreeSections S A).hom)
    (fun K n h => ι_tensorComplexUnitIsoFreeSections_hom_f S K n h)

end Unit

end Stacks.SheafOfModules

namespace Stacks.SheafOfModules

variable (X : AlgebraicGeometry.RingedSite.{c, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u, u, u} X.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [HasDerivedCategory.{d}
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O))]

attribute [local instance] derivedTensorBifunctorLifting

/-- The unit law of the derived tensor product of
`Stacks.SheafOfModules.derivedTensorProductOfExact` commutes with the shift. -/
theorem unitNatIso_commShift_ofExact :
    NatTrans.CommShift (derivedTensorProductOfExact X inferInstance
      (fun _ ↦ inferInstance) (fun _ ↦ inferInstance)).unitComplexNatIso.hom ℤ := by
  show NatTrans.CommShift ((derivedTensorProductOfExact X inferInstance
      (fun _ ↦ inferInstance) (fun _ ↦ inferInstance)).unitComplexNatIso.hom :
    (derivedTensorBifunctor X).flip.obj
        (DerivedCategory.Q.obj (DerivedTensorProduct.unitComplex X)) ⟶ 𝟭 _) ℤ
  have := Localization.essSurj (kFlatComplexQ X) (kFlatComplexQuasiIso X)
  have i1 : NatTrans.CommShift (kFlatComparisonFlipIso X (DerivedTensorProduct.unitComplex X)).hom
    ℤ := inferInstance
  have i6 : NatTrans.CommShift (Functor.whiskerLeft (kFlatComplexes X).ι
      (Functor.whiskerRight (tensorComplexUnitNatIso X.O).hom DerivedCategory.Q ≫
        DerivedCategory.Q.leftUnitor.hom) ≫ (kFlatComplexQ X).rightUnitor.inv) ℤ := inferInstance
  -- instance search does not find the composite: the target instance of `i1` is that of
  -- `kFlatTensorToDerived`, so the factors are composed by hand
  have i8 := @NatTrans.CommShift.comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ i1 i6
  refine NatTrans.commShift_of_whiskerLeft (kFlatComplexQ X) _ ?_
  refine @NatTrans.commShift_of_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ i8 ?_
  ext P
  refine (DerivedTensorProduct.unitNatIso_hom_app_Q _ P.obj).trans ?_
  refine Eq.trans (congrArg (· ≫ _) (toTensor_eq_kFlatComparison X P.2 _)) ?_
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app, kFlatComparisonFlipIso_hom_app,
    Category.comp_id]
  exact congrArg (_ ≫ ·) (Category.comp_id _).symm

/-- **The unit law `K ⊗^L 𝒪 ≅ K` of the canonical derived tensor product commutes with the
shift.** -/
theorem unitNatIso_commShift :
    letI := (canonicalDerivedTensorProduct.{c, u, d} X).commShift_left
    NatTrans.CommShift (canonicalDerivedTensorProduct.{c, u, d} X).unitComplexNatIso.hom ℤ := by
  generalize hT : canonicalDerivedTensorProduct.{c, u, d} X = T
  rw [canonicalDerivedTensorProduct_def] at hT
  subst hT
  exact unitNatIso_commShift_ofExact X

end Stacks.SheafOfModules
