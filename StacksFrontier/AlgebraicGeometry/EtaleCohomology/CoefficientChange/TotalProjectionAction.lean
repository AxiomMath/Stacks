module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CoefficientChange.ConstantProjectionAction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CoefficientChange.ConstantProjectionDerived
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CoefficientChange.ExtendScalarsAction

/-!
# The projection map on total complexes is compatible with the action of `Λ₂`

For `φ : Λ₁ → Λ₂`, `g : X ⟶ Y`, a complex `J` of étale sheaves of `Λ₂`-modules on `X` and a
map `q : N ⟶ Λ₂` from a complex of `Λ₁`-modules, the chain-level action of `Λ₂` on
`res(g_*J) = g_*(res J)` against `N` is the projection map on total complexes followed by `g_*`
of the chain-level action on `J`.

Both sides are compared on the summands `res Jⁱ ⊗ c(Nʲ)` of the total complex.  Off the row
`j = 0` both vanish, since `q` factors through `Λ₂[0]`; on it, both are the sheaf-level
statement `Stacks.EtaleCohomology.etaleModuleConstantProjectionMapApp_coefficientAction` after
`res Jⁱ ⊗ c(q⁰)`, by naturality of the projection map in the module.

## Main results

* `Stacks.EtaleCohomology.etaleModuleTotalProjectionMap_coefficientAction`: the projection map
  on total complexes intertwines the chain-level actions of `Λ₂`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open CochainComplex.KFlatBifunctor

universe u r

namespace CochainComplex.KFlatBifunctor

variable {A B D : Type*} [Category A] [Category B] [Category D]
  [Abelian A] [Abelian B] [Abelian D]
  (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
  [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
      (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
      K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)]

/-- A four-fold composite out of a split summand, followed by a common last factor. -/
private theorem comp_four_of_split_comp {C : Type*} [Category C] {X Y Y' Z T T' : C}
    (i : X ⟶ Y) (m : Y ⟶ Z) (v : Z ⟶ T) (z : T ⟶ T') (e : X ⟶ Y') (j : Y' ⟶ Z)
    (s : Y' ⟶ T) (sinv : T ⟶ Y') (r : X ⟶ T)
    (hi : i ≫ m = e ≫ j) (hv : j ≫ v = s) (he : e = r ≫ sinv)
    (hsi : sinv ≫ s = CategoryStruct.id T) :
    i ≫ m ≫ v ≫ z = r ≫ z := by
  rw [← Category.assoc, hi, Category.assoc, ← Category.assoc j, hv, he, Category.assoc,
    ← Category.assoc sinv, hsi, Category.id_comp]

/-- **The components of the termwise identification of a total complex.** The inclusion of the
`(p, 0)`-summand of `Tot(F(K, M[0]))` in degree `n = p` followed by `totalSingleIso` is the image
under `F(K^p, -)` of the identification of `M[0]` in degree zero with `M`. -/
@[reassoc]
theorem ι_totalSingleIso_hom_f_of_eq (K : CochainComplex A ℤ) (M : B) (p n : ℤ) (h : p + 0 = n) :
    HomologicalComplex.ιMapBifunctor K
        ((HomologicalComplex.single B (ComplexShape.up ℤ) 0).obj M) F (ComplexShape.up ℤ)
        p 0 n h ≫ (totalSingleIso F K M).hom.f n =
      (F.obj (K.X p)).map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).hom ≫
        ((rowComplex F K M).XIsoOfEq (by omega : p = n)).hom := by
  obtain rfl : p = n + -0 := by omega
  let W := rowComplex F K M
  let _hT : (StacksDraft.TotalSingleRow.singleRow W 0).HasTotal (ComplexShape.up ℤ) :=
    HomologicalComplex₂.hasTotal_of_iso (mapBifunctorSingleIso F K M 0) _
  have hiso : IsIso (StacksDraft.TotalSingleRow.totalSingleRowUnit W 0) :=
    StacksDraft.TotalSingleRow.isIso_totalSingleRowUnit _ _
  have hK : (totalSingleIso F K M).hom.f n =
      (HomologicalComplex₂.total.map (mapBifunctorSingleIso F K M 0).hom
          (ComplexShape.up ℤ)).f n ≫
        (CategoryTheory.inv (StacksDraft.TotalSingleRow.totalSingleRowUnit W 0)).f n ≫
          ((CategoryTheory.shiftFunctorZero' (CochainComplex D ℤ) (-0 : ℤ)
            neg_zero).hom.app W).f n := rfl
  have hz : ((CategoryTheory.shiftFunctorZero' (CochainComplex D ℤ) (-0 : ℤ)
      neg_zero).hom.app W).f n = (W.XIsoOfEq (by omega : n + -0 = n)).hom := by
    simp [CategoryTheory.shiftFunctorZero', CochainComplex.shiftFunctorZero_hom_app_f]
  have hU : (StacksDraft.TotalSingleRow.totalSingleRowUnit W 0).f n =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (W.X (n + -0))).inv ≫
        (StacksDraft.TotalSingleRow.singleRow W 0).ιTotal (ComplexShape.up ℤ) (n + -0) 0 n
          (by dsimp; omega) := by
    dsimp only [StacksDraft.TotalSingleRow.totalSingleRowUnit]
    rw [show ((0 : ℤ) * n).negOnePow = 1 by simp, one_smul]
  have h1 : (StacksDraft.TotalSingleRow.totalSingleRowUnit W 0).f n ≫
      (CategoryTheory.inv (StacksDraft.TotalSingleRow.totalSingleRowUnit W 0)).f n = 𝟙 _ :=
    congrArg (fun φ => HomologicalComplex.Hom.f φ n)
      (IsIso.hom_inv_id (StacksDraft.TotalSingleRow.totalSingleRowUnit W 0))
  rw [hU, Category.assoc] at h1
  have hv : (StacksDraft.TotalSingleRow.singleRow W 0).ιTotal (ComplexShape.up ℤ) (n + -0) 0 n
        (by dsimp; omega) ≫
        (CategoryTheory.inv (StacksDraft.TotalSingleRow.totalSingleRowUnit W 0)).f n =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (W.X (n + -0))).hom :=
    ((Iso.inv_comp_eq _).1 h1).trans (Category.comp_id _)
  have hι : HomologicalComplex.ιMapBifunctor K
          ((HomologicalComplex.single B (ComplexShape.up ℤ) 0).obj M) F (ComplexShape.up ℤ)
          (n + -0) 0 n h ≫
        (HomologicalComplex₂.total.map (mapBifunctorSingleIso F K M 0).hom
          (ComplexShape.up ℤ)).f n =
      ((mapBifunctorSingleIso F K M 0).hom.f (n + -0)).f 0 ≫
        (StacksDraft.TotalSingleRow.singleRow W 0).ιTotal (ComplexShape.up ℤ) (n + -0) 0 n
          (by dsimp; omega) :=
    HomologicalComplex₂.ιTotal_map _ _ _ _ (n + -0) 0 n h
  have he : ((mapBifunctorSingleIso F K M 0).hom.f (n + -0)).f 0 =
      (F.obj (K.X (n + -0))).map
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).hom ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (W.X (n + -0))).inv :=
    HomologicalComplex.singleMapHomologicalComplex_hom_app_self (F.obj (K.X (n + -0)))
      (ComplexShape.up ℤ) 0 M
  rw [hK, hz]
  exact comp_four_of_split_comp _ _ _ _ _ _ _ _ _ hι hv he
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (W.X (n + -0))).inv_hom_id

/-- On a summand of `Tot(F(K, P))`, the map `Tot(F(K, y))` induced by `y : P ⟶ Q`, followed by a
chain map, is `F(Kⁱ, yʲ)` followed by the inclusion of the summand of `Tot(F(K, Q))`. -/
theorem ι_map₂HomologicalComplex_map_comp_f (K : CochainComplex A ℤ) {P Q : CochainComplex B ℤ}
    (y : P ⟶ Q) {R : CochainComplex D ℤ}
    (ρ : HomologicalComplex.mapBifunctor K Q F (ComplexShape.up ℤ) ⟶ R) (i₁ i₂ n : ℤ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (i₁, i₂) = n) :
    HomologicalComplex.ιMapBifunctor K P F (ComplexShape.up ℤ) i₁ i₂ n h ≫
        (((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
          (ComplexShape.up ℤ)).obj K).map y ≫ ρ).f n =
      (F.obj (K.X i₁)).map (y.f i₂) ≫
        HomologicalComplex.ιMapBifunctor K Q F (ComplexShape.up ℤ) i₁ i₂ n h ≫ ρ.f n :=
  (HomologicalComplex.ι_mapBifunctorMap_assoc (𝟙 K) y F (ComplexShape.up ℤ) i₁ i₂ n h
    (ρ.f n)).trans (by
      rw [HomologicalComplex.id_f, CategoryTheory.Functor.map_id, NatTrans.id_app,
        Category.id_comp])

end CochainComplex.KFlatBifunctor

namespace Stacks.EtaleCohomology

attribute [local instance] etaleModuleMonoidalCategory etaleModuleBraidedCategory

variable {Λ₁ Λ₂ : Type r} [CommRing Λ₁] [CommRing Λ₂] (φ : Λ₁ →+* Λ₂)

/-- On the `(n, 0)`-summand, the identification `Tot(K ⊗ Λ̲₂[0]) ≅ K ⊗ Λ̲₂` is the identification
of `Λ̲₂[0]` in degree zero with `Λ̲₂`. -/
theorem ι_totalSingleIso_trans_rowComplexIsoMapTensorRight_hom_f (X : Scheme.{u})
    (K : CochainComplex (EtaleModules.{u, r} Λ₁ X) ℤ) (n : ℤ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (n, 0) = n) :
    HomologicalComplex.ιMapBifunctor K
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj (coefficientSheaf.{u} φ X))
        (etaleModuleTensor.{u, r} Λ₁ X) (ComplexShape.up ℤ) n 0 n h ≫
      (totalSingleIso (etaleModuleTensor.{u, r} Λ₁ X) K (coefficientSheaf.{u} φ X) ≪≫
        rowComplexIsoMapTensorRight X K (coefficientSheaf.{u} φ X)).hom.f n =
      ((etaleModuleTensor.{u, r} Λ₁ X).obj (K.X n)).map
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (coefficientSheaf.{u} φ X)).hom := by
  rw [Iso.trans_hom, HomologicalComplex.comp_f,
    CochainComplex.KFlatBifunctor.ι_totalSingleIso_hom_f_of_eq_assoc]
  simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom]
  exact Category.comp_id _

/-- The degree-zero component of `coefficientSheafComplexMap`. -/
theorem coefficientSheafComplexMap_f_zero (X : Scheme.{u})
    (N : CochainComplex (ModuleCat.{max (u + 1) r} Λ₁) ℤ)
    (q : N ⟶ (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj (coefficientModule.{u} φ)) :
    (coefficientSheafComplexMap φ X N q).f 0 =
      (etaleModuleConstantSheafFunctor.{u, r} Λ₁ X).map
          (q.f 0 ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
            (coefficientModule.{u} φ)).hom) ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          ((etaleModuleConstantSheafFunctor.{u, r} Λ₁ X).obj (coefficientModule.{u} φ))).inv := by
  refine (congrArg ((etaleModuleConstantSheafFunctor.{u, r} Λ₁ X).map (q.f 0) ≫ ·)
    (HomologicalComplex.singleMapHomologicalComplex_hom_app_self
      (etaleModuleConstantSheafFunctor.{u, r} Λ₁ X) (ComplexShape.up ℤ) 0
      (coefficientModule.{u} φ))).trans ?_
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp]

/-- **The chain-level map against `Λ₂` on a summand.** For a complex `K` of étale sheaves of
`Λ₁`-modules, a chain map `θ` out of `K ⊗ Λ̲₂` and `q : N ⟶ Λ₂[0]`, the composite
`Tot(K ⊗ c(N)) ⟶ Tot(K ⊗ Λ̲₂[0]) ≅ K ⊗ Λ̲₂ ⟶ L` on the `(n, 0)`-summand is
`Kⁿ ⊗ c(q⁰)` followed by `θⁿ`. -/
theorem ι_totalCoefficient_f (X : Scheme.{u})
    (K : CochainComplex (EtaleModules.{u, r} Λ₁ X) ℤ)
    {L : CochainComplex (EtaleModules.{u, r} Λ₁ X) ℤ}
    (θ : ((MonoidalCategory.tensorRight (coefficientSheaf.{u} φ X)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K ⟶ L)
    (N : CochainComplex (ModuleCat.{max (u + 1) r} Λ₁) ℤ)
    (q : N ⟶ (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj (coefficientModule.{u} φ))
    (n : ℤ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (n, 0) = n) :
    HomologicalComplex.ιMapBifunctor K
        (((etaleModuleConstantSheafFunctor.{u, r} Λ₁ X).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj N)
        (etaleModuleTensor.{u, r} Λ₁ X) (ComplexShape.up ℤ) n 0 n h ≫
      ((((etaleModuleTensor.{u, r} Λ₁ X).map₂HomologicalComplex (ComplexShape.up ℤ)
          (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj K).map
          (coefficientSheafComplexMap φ X N q) ≫
        (totalSingleIso (etaleModuleTensor.{u, r} Λ₁ X) K (coefficientSheaf.{u} φ X) ≪≫
          rowComplexIsoMapTensorRight X K (coefficientSheaf.{u} φ X)).hom ≫ θ).f n =
      ((etaleModuleTensor.{u, r} Λ₁ X).obj (K.X n)).map
          ((etaleModuleConstantSheafFunctor.{u, r} Λ₁ X).map
            (q.f 0 ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
              (coefficientModule.{u} φ)).hom)) ≫ θ.f n := by
  have hA := CochainComplex.KFlatBifunctor.ι_map₂HomologicalComplex_map_comp_f
    (etaleModuleTensor.{u, r} Λ₁ X) K (coefficientSheafComplexMap φ X N q)
    ((totalSingleIso (etaleModuleTensor.{u, r} Λ₁ X) K (coefficientSheaf.{u} φ X) ≪≫
      rowComplexIsoMapTensorRight X K (coefficientSheaf.{u} φ X)).hom ≫ θ) n 0 n h
  have hB := ι_totalSingleIso_trans_rowComplexIsoMapTensorRight_hom_f φ X K n h
  have he := (congrArg ((etaleModuleTensor.{u, r} Λ₁ X).obj (K.X n)).map
    (coefficientSheafComplexMap_f_zero φ X N q)).trans (CategoryTheory.Functor.map_comp _ _ _)
  have hsi := (CategoryTheory.Functor.map_comp ((etaleModuleTensor.{u, r} Λ₁ X).obj (K.X n))
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        ((etaleModuleConstantSheafFunctor.{u, r} Λ₁ X).obj (coefficientModule.{u} φ))).inv
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        ((etaleModuleConstantSheafFunctor.{u, r} Λ₁ X).obj
          (coefficientModule.{u} φ))).hom).symm.trans
    ((congrArg _ (Iso.inv_hom_id _)).trans (CategoryTheory.Functor.map_id _ _))
  refine hA.trans ?_
  rw [HomologicalComplex.comp_f, ← Category.assoc
    (HomologicalComplex.ιMapBifunctor K
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj (coefficientSheaf.{u} φ X))
      (etaleModuleTensor.{u, r} Λ₁ X) (ComplexShape.up ℤ) n 0 n h), hB, he, Category.assoc,
    ← Category.assoc _ _ (θ.f n)]
  exact (congrArg (fun t => _ ≫ t ≫ θ.f n) hsi).trans (congrArg _ (Category.id_comp _))

/-- The components of the chain-level action of `Λ₂` on a complex `J` of `Λ₂`-modules are the
sheaf-level actions. -/
theorem etaleModuleCoefficientAction_mapHomologicalComplex_app_f (X : Scheme.{u})
    (J : CochainComplex (EtaleModules.{u, r} Λ₂ X) ℤ) (n : ℤ) :
    ((NatTrans.mapHomologicalComplex (etaleModuleCoefficientAction φ X)
        (ComplexShape.up ℤ)).app J).f n =
      (etaleModuleExtendRestrictScalarsIso.{u, r} φ X).inv.app
          ((etaleModuleRestrictScalarsUniv.{u, r} φ X).obj (J.X n)) ≫
        (etaleModuleRestrictScalarsUniv.{u, r} φ X).map
          ((etaleModuleExtendRestrictAdj.{u, r} φ X).counit.app (J.X n)) := by
  simp [etaleModuleCoefficientAction]

/-- **The chain-level action on a summand.** On the `(n, 0)`-summand `res Jⁿ ⊗ c(N⁰)` of
`Tot(res J ⊗ c(N))`, the chain-level action is `res Jⁿ ⊗ c(q⁰)` followed by the sheaf-level
action of `Λ₂` on `res Jⁿ`. -/
theorem ι_etaleModuleTotalCoefficientAction_f (X : Scheme.{u})
    (J : CochainComplex (EtaleModules.{u, r} Λ₂ X) ℤ)
    (N : CochainComplex (ModuleCat.{max (u + 1) r} Λ₁) ℤ)
    (q : N ⟶ (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj (coefficientModule.{u} φ))
    (n : ℤ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (n, 0) = n) :
    HomologicalComplex.ιMapBifunctor
        (((etaleModuleRestrictScalarsUniv.{u, r} φ X).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj J)
        (((etaleModuleConstantSheafFunctor.{u, r} Λ₁ X).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj N)
        (etaleModuleTensor.{u, r} Λ₁ X) (ComplexShape.up ℤ) n 0 n h ≫
      (etaleModuleTotalCoefficientAction φ X J N q).f n =
      (etaleModuleRestrictScalarsUniv.{u, r} φ X).obj (J.X n) ◁
          (etaleModuleConstantSheafFunctor.{u, r} Λ₁ X).map
            (q.f 0 ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
              (coefficientModule.{u} φ)).hom) ≫
        (etaleModuleExtendRestrictScalarsIso.{u, r} φ X).inv.app
            ((etaleModuleRestrictScalarsUniv.{u, r} φ X).obj (J.X n)) ≫
          (etaleModuleRestrictScalarsUniv.{u, r} φ X).map
            ((etaleModuleExtendRestrictAdj.{u, r} φ X).counit.app (J.X n)) :=
  (ι_totalCoefficient_f φ X _ _ N q n h).trans
    (congrArg _ (etaleModuleCoefficientAction_mapHomologicalComplex_app_f φ X J n))

/-- **The chain-level action vanishes off the row `0`.** -/
theorem ι_etaleModuleTotalCoefficientAction_f_of_ne (X : Scheme.{u})
    (J : CochainComplex (EtaleModules.{u, r} Λ₂ X) ℤ)
    (N : CochainComplex (ModuleCat.{max (u + 1) r} Λ₁) ℤ)
    (q : N ⟶ (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj (coefficientModule.{u} φ))
    (i₁ i₂ n : ℤ) (hi₂ : i₂ ≠ 0)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (i₁, i₂) = n) :
    HomologicalComplex.ιMapBifunctor
        (((etaleModuleRestrictScalarsUniv.{u, r} φ X).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj J)
        (((etaleModuleConstantSheafFunctor.{u, r} Λ₁ X).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj N)
        (etaleModuleTensor.{u, r} Λ₁ X) (ComplexShape.up ℤ) i₁ i₂ n h ≫
      (etaleModuleTotalCoefficientAction φ X J N q).f n = 0 := by
  refine (CochainComplex.KFlatBifunctor.ι_map₂HomologicalComplex_map_comp_f
    (etaleModuleTensor.{u, r} Λ₁ X) _ (coefficientSheafComplexMap φ X N q) _ i₁ i₂ n h).trans ?_
  have hz : IsZero (((etaleModuleTensor.{u, r} Λ₁ X).obj
      ((etaleModuleRestrictScalarsUniv.{u, r} φ X).obj (J.X i₁))).obj
      (((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
        (coefficientSheaf.{u} φ X)).X i₂)) :=
    Functor.map_isZero _ (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi₂)
  exact (congrArg (_ ≫ ·) (hz.eq_of_src _ _)).trans Limits.comp_zero

/-- **The projection map on total complexes on a summand** is the sheaf-level projection map
followed by the direct image of the inclusion of the summand. -/
@[reassoc]
theorem ι_etaleModuleTotalProjectionMap_f (Λ : Type r) [CommRing Λ] {X Y : Scheme.{u}}
    (g : X ⟶ Y) (K : CochainComplex (EtaleModules.{u, r} Λ X) ℤ)
    (N : CochainComplex (ModuleCat.{max (u + 1) r} Λ) ℤ) (i₁ i₂ n : ℤ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (i₁, i₂) = n) :
    HomologicalComplex.ιMapBifunctor
        (((etaleModuleDirectImage.{u, r} Λ g).mapHomologicalComplex _).obj K)
        (((etaleModuleConstantSheafFunctor.{u, r} Λ Y).mapHomologicalComplex _).obj N)
        (etaleModuleTensor.{u, r} Λ Y) (ComplexShape.up ℤ) i₁ i₂ n h ≫
      (etaleModuleTotalProjectionMap Λ g K N).f n =
    etaleModuleConstantProjectionMapApp Λ g (K.X i₁) (N.X i₂) ≫
      (etaleModuleDirectImage.{u, r} Λ g).map
        (HomologicalComplex.ιMapBifunctor K
          (((etaleModuleConstantSheafFunctor.{u, r} Λ X).mapHomologicalComplex _).obj N)
          (etaleModuleTensor.{u, r} Λ X) (ComplexShape.up ℤ) i₁ i₂ n h) := by
  rw [etaleModuleTotalProjectionMap,
    Stacks.Cohomology.LinearCupProductFamily.mapBifunctorTotalMap, HomologicalComplex.comp_f]
  exact (HomologicalComplex₂.ιTotal_map_assoc _ _ _ _ i₁ i₂ n h _).trans
    (congrArg (_ ≫ ·) (HomologicalComplex₂.ι_totalMapf _ _ n i₁ i₂ h))

/-- Rewriting `a ≫ b` inside `F.map a ≫ F.map b` when `a ≫ b = c`. -/
private theorem comp_map_comp_of_comp_eq {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {T : D} {A B R : C} (p : T ⟶ F.obj A) (a : A ⟶ B) (b : B ⟶ R) {c : A ⟶ R}
    (hc : a ≫ b = c) : (p ≫ F.map a) ≫ F.map b = p ≫ F.map c := by
  rw [Category.assoc, ← F.map_comp, hc]

/-- **The projection map intertwines the chain-level actions of `Λ₂`.** -/
theorem etaleModuleTotalProjectionMap_coefficientAction {X Y : Scheme.{u}} (g : X ⟶ Y)
    (J : CochainComplex (EtaleModules.{u, r} Λ₂ X) ℤ)
    (N : CochainComplex (ModuleCat.{max (u + 1) r} Λ₁) ℤ)
    (q : N ⟶ (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj (coefficientModule.{u} φ)) :
    etaleModuleTotalCoefficientAction φ Y
        (((etaleModuleDirectImage.{u, r} Λ₂ g).mapHomologicalComplex (ComplexShape.up ℤ)).obj J)
        N q =
      etaleModuleTotalProjectionMap Λ₁ g
          (((etaleModuleRestrictScalarsUniv.{u, r} φ X).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj J)
          N ≫
        ((etaleModuleDirectImage.{u, r} Λ₁ g).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (etaleModuleTotalCoefficientAction φ X J N q) := by
  refine HomologicalComplex.hom_ext _ _ (fun n => ?_)
  refine HomologicalComplex.mapBifunctor.hom_ext (fun i₁ i₂ h => ?_)
  have h₁ := ι_etaleModuleTotalProjectionMap_f_assoc Λ₁ g
    (((etaleModuleRestrictScalarsUniv.{u, r} φ X).mapHomologicalComplex (ComplexShape.up ℤ)).obj J)
    N i₁ i₂ n h ((etaleModuleDirectImage.{u, r} Λ₁ g).map
      ((etaleModuleTotalCoefficientAction φ X J N q).f n))
  refine Eq.trans ?_ h₁.symm
  by_cases hi₂ : i₂ = 0
  · subst hi₂
    obtain rfl : i₁ = n := by
      change i₁ + 0 = n at h
      omega
    refine Eq.trans ?_ (comp_map_comp_of_comp_eq (etaleModuleDirectImage.{u, r} Λ₁ g) _ _ _
      (ι_etaleModuleTotalCoefficientAction_f φ X J N q i₁ h)).symm
    refine (ι_etaleModuleTotalCoefficientAction_f φ Y _ N q i₁ h).trans ?_
    refine (congrArg (_ ≫ ·)
      (etaleModuleConstantProjectionMapApp_coefficientAction φ g (J.X i₁))).trans ?_
    rw [Functor.map_comp (etaleModuleDirectImage.{u, r} Λ₁ g)]
    exact etaleModuleConstantProjectionMapApp_naturality_right_assoc Λ₁ g _ _ _
  · refine Eq.trans ?_ (comp_map_comp_of_comp_eq (etaleModuleDirectImage.{u, r} Λ₁ g) _ _ _
      (ι_etaleModuleTotalCoefficientAction_f_of_ne φ X J N q i₁ i₂ n hi₂ h)).symm
    rw [ι_etaleModuleTotalCoefficientAction_f_of_ne φ Y _ N q i₁ i₂ n hi₂ h, Functor.map_zero]
    exact Limits.comp_zero.symm

end Stacks.EtaleCohomology

end
