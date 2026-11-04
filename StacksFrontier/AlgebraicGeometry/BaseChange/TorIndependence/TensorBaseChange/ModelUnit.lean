module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.TensorBaseChange.ModelComplex

/-!
# The model map and the comparison of a square of rings

The model complex of a square of rings carries a map to `A' ⊗_A M`.  This file computes it on the
summands of the total tensor complex, and shows that, read over `R₀`, it is the comparison
`R' ⊗_R M ⟶ A' ⊗_A M` of the square precomposed with the augmentation of the resolution of `R'`.

## Main definitions

* `RingTheory.TorIndependence.modelMapE`: the model map, landing in `A' ⊗_A M`.
* `RingTheory.TorIndependence.baseSideMap`: the comparison `R' ⊗_R M ⟶ A' ⊗_A M`.

## Main results

* `RingTheory.TorIndependence.modelMapE_restrict`: read over `R₀`, the model map is the base model
  comparison followed by the comparison `R' ⊗_R M ⟶ A' ⊗_A M` of the square.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct ChangeOfRings

universe u

namespace RingTheory.TorIndependence

section SingleTensor

variable {S : Type u} [CommRing S] (N : ModuleCat.{u} S) (K L : CochainComplex (ModuleCat.{u} S) ℤ)
  (g : L ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} S) 0).obj N)

/-- On the summand `K^p ⊗ L^0`, the map `K ⊗ L ⟶ K ⊗ N[0] ≅ K ⊗ N` is `K^p ⊗ g^0`. -/
theorem ι_whiskerLeft_termwiseTensorSingleIso_inv (p : ℤ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, 0) = p) :
    HomologicalComplex.ιMapBifunctor K L (curriedTensor (ModuleCat.{u} S)) (ComplexShape.up ℤ)
        p 0 p h ≫ (K ◁ g).f p ≫
          ((tensorSingleIso N).inv.app K).f p =
      K.X p ◁ g.f 0 := by
  have h1 := HomologicalComplex.Monoidal.ι_whiskerLeft K g p 0 p h
  have h2 : HomologicalComplex.ιTensorObj K
        ((CochainComplex.singleFunctor (ModuleCat.{u} S) 0).obj N) p 0 p h ≫
      ((tensorSingleIso N).inv.app K).f p = 𝟙 _ := by
    have := HomologicalComplex.congr_hom ((tensorSingleIso N).hom_inv_id_app K) p
    rw [HomologicalComplex.comp_f, HomologicalComplex.id_f, tensorSingleIso_hom_f] at this
    exact this
  show HomologicalComplex.ιTensorObj K L p 0 p h ≫ (K ◁ g).f p ≫ _ = _
  rw [reassoc_of% h1, h2]
  exact Category.comp_id _

/-- On a summand `K^p ⊗ L^q` with `q ≠ 0`, the map `K ⊗ L ⟶ K ⊗ N[0]` vanishes. -/
theorem ι_whiskerLeft_single_eq_zero (p q n : ℤ) (hq : q ≠ 0)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n) :
    HomologicalComplex.ιMapBifunctor K L (curriedTensor (ModuleCat.{u} S)) (ComplexShape.up ℤ)
        p q n h ≫ (K ◁ g).f n = 0 := by
  have h1 := HomologicalComplex.Monoidal.ι_whiskerLeft K g p q n h
  show HomologicalComplex.ιTensorObj K L p q n h ≫ (K ◁ g).f n = 0
  rw [h1]
  have hz : IsZero (((CochainComplex.singleFunctor (ModuleCat.{u} S) 0).obj N).X q) :=
    HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 N q hq
  have : g.f q = 0 := hz.eq_of_tgt _ _
  rw [this, MonoidalPreadditive.whiskerLeft_zero, zero_comp]

end SingleTensor

variable {R A R' A' R₀ : Type u}
  [CommRing R] [CommRing A] [CommRing R'] [CommRing A'] [CommRing R₀]
  [Algebra R A] [Algebra R R'] [Algebra R A'] [Algebra A A'] [Algebra R' A']
  [IsScalarTower R A A'] [IsScalarTower R R' A']
  [Algebra R R₀] [Algebra R₀ R'] [IsScalarTower R R₀ R']

attribute [local instance] Algebra.TensorProduct.rightAlgebra

local notation "B₀" => A ⊗[R] R₀

variable (F : CochainComplex (ModuleCat.{u} R₀) ℤ)
  (ε : F ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} R₀) 0).obj (ModuleCat.of R₀ R'))

/-- The restriction of the model complex to `R₀` is `(R₀ ⊗_R M) ⊗_{R₀} F`. -/
def modelRestrictIso (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    ((ModuleCat.restrictScalars (algebraMap R₀ B₀)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (modelComplex A F M) ≅
      (baseModelFunctor R F).obj
        (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M) :=
  modelComplexRestrictIso M F

/-- The model map, landing in `A' ⊗_A M` with the structure of `ModuleCat.extendScalars`. -/
def modelMapE (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    modelComplex A F M ⟶
      ((ModuleCat.extendScalars (algebraMap A A') ⋙
        ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M :=
  modelMap (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) F ε M ≫
    (NatIso.mapHomologicalComplex (Functor.isoWhiskerRight (baseChangeIsoExtendScalars A A')
      (ModuleCat.restrictScalars (modelRingMap R A R' A' R₀))) (ComplexShape.up ℤ)).hom.app M

variable (R A R' A' R₀) in
/-- Restricting from `A'` to `R₀` through `R'` or through `A ⊗_R R₀` gives the same module. -/
def restrictScalarsSquareHom :
    ModuleCat.restrictScalars (algebraMap R' A') ⋙ ModuleCat.restrictScalars (algebraMap R₀ R') ⟶
      ModuleCat.restrictScalars (modelRingMap R A R' A' R₀) ⋙
        ModuleCat.restrictScalars (algebraMap R₀ B₀) where
  app X := ModuleCat.ofHom
    (X := (ModuleCat.restrictScalars (algebraMap R₀ R')).obj
      ((ModuleCat.restrictScalars (algebraMap R' A')).obj X))
    (Y := (ModuleCat.restrictScalars (algebraMap R₀ B₀)).obj
      ((ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).obj X))
    { toFun := fun x => x
      map_add' := fun _ _ => rfl
      map_smul' := fun r x => by
        have h : algebraMap R' A' (algebraMap R₀ R' r) =
            modelRingMap R A R' A' R₀ (algebraMap R₀ B₀ r) := by
          rw [Algebra.TensorProduct.right_algebraMap_apply, modelRingMap_tmul, map_one, one_mul]
        exact congrArg (fun a : A' => a • (show X from x)) h }
  naturality _ _ _ := rfl

attribute [local instance] HasDerivedCategory.standard

variable (R A R' A') in
/-- The comparison `R' ⊗_R M ⟶ A' ⊗_A M` of the square of rings, the first component of
`derivedBaseChangeComparison` for the square `baseChangeSquare`. -/
abbrev squareTermComparison :
    ModuleCat.restrictScalars (algebraMap R A) ⋙ ModuleCat.extendScalars (algebraMap R R') ⟶
      ModuleCat.extendScalars (algebraMap A A') ⋙ ModuleCat.restrictScalars (algebraMap R' A') :=
  (@derivedBaseChangeComparison.{u, u, u, u, u, u + 1, u + 1, u + 1, u + 1}
    R A R' A' _ _ _ _ _ _ _ _ (algebraMap R A) (algebraMap R R') (algebraMap A A')
    (algebraMap R' A') baseChangeSquare
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (algebraMap R R')).functor
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (algebraMap A A')).functor
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (algebraMap R R')).comparison
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (algebraMap A A')).comparison
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (algebraMap R R')).isLeftDerived
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (algebraMap A A')).isLeftDerived).1

/-- On the summand `(R₀ ⊗_R M^p) ⊗_{R₀} F^q`, the inverse of `modelRestrictIso` is the inverse of
`modelBifunctorIso` followed by the inclusion of the summand `M^p ⊗ F^q` of the model complex. -/
theorem ι_modelRestrictIso_inv (M : CochainComplex (ModuleCat.{u} A) ℤ) (p q n : ℤ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n) :
    (HomologicalComplex.ιMapBifunctor
        (((baseChangeFunctor R R₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj M))
        F (curriedTensor (ModuleCat.{u} R₀)) (ComplexShape.up ℤ) p q n h :
        _ ⟶ ((baseModelFunctor R F).obj
          (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj M)).X n) ≫
      (modelRestrictIso F M).inv.f n =
    (modelBifunctorIso (M.X p) (F.X q)).inv ≫
      (ModuleCat.restrictScalars (algebraMap R₀ B₀)).map
        (HomologicalComplex.ιMapBifunctor M F modelBifunctor (ComplexShape.up ℤ) p q n h) :=
  Functor.ι_mapBifunctorTotalIso_inv (modelBifunctor (R := R) (A := A) (R₀ := R₀))
    (curriedTensor (ModuleCat.{u} R₀))
    (ModuleCat.restrictScalars (algebraMap R A) ⋙ baseChangeFunctor R R₀) (𝟭 _)
    (ModuleCat.restrictScalars (algebraMap R₀ B₀)) modelBifunctorIso
    (ComplexShape.up ℤ) (ComplexShape.up ℤ) modelBifunctorIso_naturality_left
    modelBifunctorIso_naturality_right M F p q n h

/-- The augmentation `F^0 ⟶ R'` of `ε`, on elements. -/
def augmentation (w : F.X 0) : R' := (ε.f 0).hom w

/-- The augmentation is `R₀`-linear. -/
theorem augmentation_smul (r : R₀) (w : F.X 0) :
    augmentation F ε (r • w) = r • augmentation F ε w :=
  (ε.f 0).hom.map_smul r w

/-- The degree-`0` part of the map `B₀ ⊗_{R₀} F ⟶ B₀ ⊗_{R₀} R'` induced by `ε`. -/
abbrev modelUnitComponent :
    (baseChangeFunctor R₀ B₀).obj (F.X 0) ⟶ (baseChangeFunctor R₀ B₀).obj (ModuleCat.of R₀ R') :=
  (baseChangeFunctor R₀ B₀).map (ε.f 0)

/-- **The model map on a summand of degree `(p, 0)`.** -/
theorem ι_modelMapE (M : CochainComplex (ModuleCat.{u} A) ℤ) (p : ℤ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, 0) = p) :
    HomologicalComplex.ιMapBifunctor M F modelBifunctor (ComplexShape.up ℤ) p 0 p h ≫
        (modelMapE (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) F ε M).f p =
      (baseChangeFunctor A B₀).obj (M.X p) ◁ modelUnitComponent F ε ≫
        (modelTermMap (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀)).app (M.X p) ≫
        (Functor.isoWhiskerRight (baseChangeIsoExtendScalars A A')
          (ModuleCat.restrictScalars (modelRingMap R A R' A' R₀))).hom.app (M.X p) := by
  have h1 := ι_whiskerLeft_termwiseTensorSingleIso_inv
    ((baseChangeFunctor R₀ B₀).obj (ModuleCat.of R₀ R'))
    (((baseChangeFunctor A B₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)
    (((baseChangeFunctor R₀ B₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj F)
    (((baseChangeFunctor R₀ B₀).mapHomologicalComplex (ComplexShape.up ℤ)).map ε ≫
        (HomologicalComplex.singleMapHomologicalComplex (baseChangeFunctor R₀ B₀)
          (ComplexShape.up ℤ) 0).hom.app (ModuleCat.of R₀ R')) p h
  show HomologicalComplex.ιMapBifunctor
      (((baseChangeFunctor A B₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)
      (((baseChangeFunctor R₀ B₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj F)
      (curriedTensor (ModuleCat.{u} B₀)) (ComplexShape.up ℤ) p 0 p h ≫
      ((((baseChangeFunctor A B₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj M ◁
        (((baseChangeFunctor R₀ B₀).mapHomologicalComplex (ComplexShape.up ℤ)).map ε ≫
          (HomologicalComplex.singleMapHomologicalComplex (baseChangeFunctor R₀ B₀)
            (ComplexShape.up ℤ) 0).hom.app (ModuleCat.of R₀ R'))).f p ≫
        ((tensorSingleIso ((baseChangeFunctor R₀ B₀).obj (ModuleCat.of R₀ R'))).inv.app
          (((baseChangeFunctor A B₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)).f p) ≫
      (modelTermMap (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀)).app (M.X p) ≫
        (Functor.isoWhiskerRight (baseChangeIsoExtendScalars A A')
          (ModuleCat.restrictScalars (modelRingMap R A R' A' R₀))).hom.app (M.X p) = _
  rw [← Category.assoc, h1]
  rfl

/-- **The comparison of the base model on a summand of degree `(p, 0)`.** -/
theorem ι_baseModelComparison (X : CochainComplex (ModuleCat.{u} R) ℤ) (p : ℤ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, 0) = p) :
    (HomologicalComplex.ιMapBifunctor
        (((baseChangeFunctor R R₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj X) F
        (curriedTensor (ModuleCat.{u} R₀)) (ComplexShape.up ℤ) p 0 p h :
          _ ⟶ ((baseModelFunctor R F).obj X).X p) ≫
        ((baseModelComparison F ε).app X).f p =
      (baseChangeFunctor R R₀).obj (X.X p) ◁ ε.f 0 ≫
        (baseTensorIso ≪≫ Functor.isoWhiskerRight (baseChangeIsoExtendScalars R R')
          (ModuleCat.restrictScalars (algebraMap R₀ R'))).hom.app (X.X p) := by
  have h1 := ι_whiskerLeft_termwiseTensorSingleIso_inv (ModuleCat.of R₀ R')
    (((baseChangeFunctor R R₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj X) F ε p h
  show (HomologicalComplex.ιMapBifunctor
      (((baseChangeFunctor R R₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj X) F
      (curriedTensor (ModuleCat.{u} R₀)) (ComplexShape.up ℤ) p 0 p h ≫
      ((((baseChangeFunctor R R₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj X ◁ ε).f p ≫
        ((tensorSingleIso (ModuleCat.of R₀ R')).inv.app
          (((baseChangeFunctor R R₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj X)).f p)) ≫
      (baseTensorIso ≪≫ Functor.isoWhiskerRight (baseChangeIsoExtendScalars R R')
          (ModuleCat.restrictScalars (algebraMap R₀ R'))).hom.app (X.X p) ≫ 𝟙 _ = _
  rw [h1, Category.comp_id]
  rfl

/-- On a summand of degree `(p, q)` with `q ≠ 0`, the comparison of the base model vanishes. -/
theorem ι_baseModelComparison_eq_zero (X : CochainComplex (ModuleCat.{u} R) ℤ) (p q n : ℤ)
    (hq : q ≠ 0)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n) :
    (HomologicalComplex.ιMapBifunctor
        (((baseChangeFunctor R R₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj X) F
        (curriedTensor (ModuleCat.{u} R₀)) (ComplexShape.up ℤ) p q n h :
          _ ⟶ ((baseModelFunctor R F).obj X).X n) ≫
        ((baseModelComparison F ε).app X).f n = 0 := by
  have h1 := ι_whiskerLeft_single_eq_zero (ModuleCat.of R₀ R')
    (((baseChangeFunctor R R₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj X) F ε p q n hq h
  have hc : ((baseModelComparison F ε).app X).f n =
      ((((baseChangeFunctor R R₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj X ◁ ε).f n ≫
        ((tensorSingleIso (ModuleCat.of R₀ R')).inv.app
          (((baseChangeFunctor R R₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj X) ≫
        (Functor.mapHomologicalComplexCompIso (baseTensorIso ≪≫
          Functor.isoWhiskerRight (baseChangeIsoExtendScalars R R')
            (ModuleCat.restrictScalars (algebraMap R₀ R'))) (ComplexShape.up ℤ)).hom.app X ≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl _) (ComplexShape.up ℤ)).inv.app X).f n) :=
      rfl
  rw [hc, reassoc_of% h1, zero_comp]

/-- On a summand of degree `(p, q)` with `q ≠ 0`, the model map vanishes. -/
theorem ι_modelMapE_eq_zero (M : CochainComplex (ModuleCat.{u} A) ℤ) (p q n : ℤ) (hq : q ≠ 0)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n) :
    HomologicalComplex.ιMapBifunctor M F modelBifunctor (ComplexShape.up ℤ) p q n h ≫
        (modelMapE (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) F ε M).f n = 0 := by
  have h1 := ι_whiskerLeft_single_eq_zero
    ((baseChangeFunctor R₀ B₀).obj (ModuleCat.of R₀ R'))
    (((baseChangeFunctor A B₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)
    (((baseChangeFunctor R₀ B₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj F)
    (((baseChangeFunctor R₀ B₀).mapHomologicalComplex (ComplexShape.up ℤ)).map ε ≫
        (HomologicalComplex.singleMapHomologicalComplex (baseChangeFunctor R₀ B₀)
          (ComplexShape.up ℤ) 0).hom.app (ModuleCat.of R₀ R')) p q n hq h
  have hc : (modelMapE (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) F ε M).f n =
      ((((baseChangeFunctor A B₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj M ◁
        (((baseChangeFunctor R₀ B₀).mapHomologicalComplex (ComplexShape.up ℤ)).map ε ≫
          (HomologicalComplex.singleMapHomologicalComplex (baseChangeFunctor R₀ B₀)
            (ComplexShape.up ℤ) 0).hom.app (ModuleCat.of R₀ R'))).f n ≫
      ((tensorSingleIso ((baseChangeFunctor R₀ B₀).obj (ModuleCat.of R₀ R'))).inv.app
        (((baseChangeFunctor A B₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) ≫
      (NatTrans.mapHomologicalComplex (modelTermMap (R := R) (A := A) (R' := R') (A' := A')
        (R₀ := R₀)) (ComplexShape.up ℤ)).app M ≫
      (NatIso.mapHomologicalComplex (Functor.isoWhiskerRight (baseChangeIsoExtendScalars A A')
        (ModuleCat.restrictScalars (modelRingMap R A R' A' R₀))) (ComplexShape.up ℤ)).hom.app
          M).f n) := rfl
  show HomologicalComplex.ιMapBifunctor
      (((baseChangeFunctor A B₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)
      (((baseChangeFunctor R₀ B₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj F)
      (curriedTensor (ModuleCat.{u} B₀)) (ComplexShape.up ℤ) p q n h ≫ _ = _
  rw [hc, reassoc_of% h1, zero_comp]
  rfl

/-- The comparison of the square sends `s ⊗ m` to `s ⊗ m`, with `s` viewed in `A'`. -/
theorem squareTermComparison_tmul (X : ModuleCat.{u} A) (s : R')
    (m : (ModuleCat.restrictScalars (algebraMap R A)).obj X) :
    ((squareTermComparison R A R' A').app X).hom (s ⊗ₜ[R, algebraMap R R'] m) =
      (algebraMap R' A' s ⊗ₜ[A, algebraMap A A'] (show X from m) :
        (ModuleCat.extendScalars (algebraMap A A')).obj X) :=
  (@derivedBaseChangeComparison.{u, u, u, u, u, u + 1, u + 1, u + 1, u + 1}
    R A R' A' _ _ _ _ _ _ _ _ (algebraMap R A) (algebraMap R R') (algebraMap A A')
    (algebraMap R' A') baseChangeSquare
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (algebraMap R R')).functor
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (algebraMap A A')).functor
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (algebraMap R R')).comparison
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (algebraMap A A')).comparison
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (algebraMap R R')).isLeftDerived
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (algebraMap A A')).isLeftDerived).2.2.1 X s m

/-- The map `(R₀ ⊗_R X) ⊗_{R₀} F^0 ⟶ A' ⊗_A X` given by the augmentation `F^0 ⟶ R'` followed by
the comparison `R' ⊗_R X ⟶ A' ⊗_A X` of the square, as a map of `R₀`-modules. -/
abbrev baseSideMap (X : ModuleCat.{u} A) :=
  ((baseChangeFunctor R R₀).obj ((ModuleCat.restrictScalars (algebraMap R A)).obj X) ◁ ε.f 0 ≫
      (baseTensorIso ≪≫ Functor.isoWhiskerRight (baseChangeIsoExtendScalars R R')
        (ModuleCat.restrictScalars (algebraMap R₀ R'))).hom.app
          ((ModuleCat.restrictScalars (algebraMap R A)).obj X)) ≫
    (ModuleCat.restrictScalars (algebraMap R₀ R')).map ((squareTermComparison R A R' A').app X) ≫
    (restrictScalarsSquareHom R A R' A' R₀).app ((ModuleCat.extendScalars (algebraMap A A')).obj X)

/-- `baseSideMap` sends `(s ⊗ y) ⊗ w` to `(s • ε(w)) ⊗ y`, with `ε(w)` the augmentation of `w`. -/
theorem baseSideMap_tmul (X : ModuleCat.{u} A) (s : R₀)
    (y : (ModuleCat.restrictScalars (algebraMap R A)).obj X) (w : F.X 0) :
    (baseSideMap (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) F ε X).hom
        ((s ⊗ₜ[R] y) ⊗ₜ[R₀] w) =
      (algebraMap R' A' (s • augmentation F ε w) ⊗ₜ[A, algebraMap A A'] (show X from y) :
        (ModuleCat.extendScalars (algebraMap A A')).obj X) := by
  have e1 : ((baseTensorIso ≪≫ Functor.isoWhiskerRight (baseChangeIsoExtendScalars R R')
        (ModuleCat.restrictScalars (algebraMap R₀ R'))).hom.app
          ((ModuleCat.restrictScalars (algebraMap R A)).obj X)).hom
        ((s ⊗ₜ[R] y) ⊗ₜ[R₀] augmentation F ε w) =
      ((s • augmentation F ε w) ⊗ₜ[R, algebraMap R R'] y :
        (ModuleCat.extendScalars (algebraMap R R')).obj
          ((ModuleCat.restrictScalars (algebraMap R A)).obj X)) := by
    show (TensorProduct.congr (algebraRestrictLinearEquiv R R')
      (LinearEquiv.refl R ((ModuleCat.restrictScalars (algebraMap R A)).obj X)))
        (baseTensorLinearEquiv (R := R) (R₀ := R₀) (R' := R')
          ((ModuleCat.restrictScalars (algebraMap R A)).obj X)
          ((s ⊗ₜ[R] y) ⊗ₜ[R₀] augmentation F ε w)) = _
    rw [baseTensorLinearEquiv_tmul, TensorProduct.congr_tmul]
    rfl
  show ((restrictScalarsSquareHom R A R' A' R₀).app
      ((ModuleCat.extendScalars (algebraMap A A')).obj X)).hom
        (((squareTermComparison R A R' A').app X).hom
          (((baseTensorIso ≪≫ Functor.isoWhiskerRight (baseChangeIsoExtendScalars R R')
            (ModuleCat.restrictScalars (algebraMap R₀ R'))).hom.app
              ((ModuleCat.restrictScalars (algebraMap R A)).obj X)).hom
            ((s ⊗ₜ[R] y) ⊗ₜ[R₀] augmentation F ε w))) = _
  rw [e1, squareTermComparison_tmul]
  rfl

/-- `baseChangeSwap` sends `(c₁ ⊗ c₂) • ((a ⊗ r) ⊗ x)` to `(c₂ * r) ⊗ ((c₁ * a) • x)`. -/
theorem baseChangeSwap_smul_tmul (X : ModuleCat.{u} A) (c₁ a : A) (c₂ r : R₀)
    (x : (ModuleCat.restrictScalars (algebraMap R A)).obj X) :
    baseChangeSwap (R := R) (A := A) (R₀ := R₀) ((ModuleCat.restrictScalars (algebraMap R A)).obj X)
        ((c₁ ⊗ₜ[R] c₂) • ((a ⊗ₜ[R] r) ⊗ₜ[A] x)) =
      (c₂ * r) ⊗ₜ[R] (show (ModuleCat.restrictScalars (algebraMap R A)).obj X from
        (show X from (c₁ * a) • (show X from x))) := by
  rw [TensorProduct.smul_tmul', smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul]
  rfl

/-- Maps out of `res (B₀ ⊗_A X ⊗_{B₀} B₀ ⊗_{R₀} W)` agree as soon as they agree on the
elements `((a ⊗ r) ⊗ x) ⊗ ((c ⊗ s) ⊗ w)`. -/
theorem tensorBaseChange_hom_ext' {X : ModuleCat.{u} A} {W : ModuleCat.{u} R₀}
    {N : ModuleCat.{u} R₀}
    {φ ψ : (ModuleCat.restrictScalars (algebraMap R₀ B₀)).obj
        ((baseChangeFunctor A B₀).obj X ⊗ (baseChangeFunctor R₀ B₀).obj W) ⟶ N}
    (h : ∀ (a : A) (r : R₀) (x : X) (c : A) (s : R₀) (w : W),
      φ.hom (((a ⊗ₜ[R] r) ⊗ₜ[A] x) ⊗ₜ[B₀] ((c ⊗ₜ[R] s) ⊗ₜ[R₀] w)) =
        ψ.hom (((a ⊗ₜ[R] r) ⊗ₜ[A] x) ⊗ₜ[B₀] ((c ⊗ₜ[R] s) ⊗ₜ[R₀] w))) : φ = ψ := by
  refine tensorBaseChange_hom_ext fun a r x b w => ?_
  induction b using TensorProduct.induction_on with
  | zero =>
    have e : (((a ⊗ₜ[R] r) ⊗ₜ[A] x) ⊗ₜ[B₀] ((0 : B₀) ⊗ₜ[R₀] w) :
        (ModuleCat.restrictScalars (algebraMap R₀ B₀)).obj
          ((baseChangeFunctor A B₀).obj X ⊗ (baseChangeFunctor R₀ B₀).obj W)) = 0 :=
      (congrArg (fun t : (baseChangeFunctor R₀ B₀).obj W => ((a ⊗ₜ[R] r) ⊗ₜ[A] x) ⊗ₜ[B₀] t)
        (TensorProduct.zero_tmul B₀ w)).trans
        (TensorProduct.tmul_zero _ _)
    rw [e]
    exact (map_zero φ.hom).trans (map_zero ψ.hom).symm
  | add b₁ b₂ h₁ h₂ =>
    have e : (((a ⊗ₜ[R] r) ⊗ₜ[A] x) ⊗ₜ[B₀] ((b₁ + b₂) ⊗ₜ[R₀] w) :
        (ModuleCat.restrictScalars (algebraMap R₀ B₀)).obj
          ((baseChangeFunctor A B₀).obj X ⊗ (baseChangeFunctor R₀ B₀).obj W)) =
        ((a ⊗ₜ[R] r) ⊗ₜ[A] x) ⊗ₜ[B₀] (b₁ ⊗ₜ[R₀] w) +
          ((a ⊗ₜ[R] r) ⊗ₜ[A] x) ⊗ₜ[B₀] (b₂ ⊗ₜ[R₀] w) :=
      (congrArg (fun t : (baseChangeFunctor R₀ B₀).obj W => ((a ⊗ₜ[R] r) ⊗ₜ[A] x) ⊗ₜ[B₀] t)
        (TensorProduct.add_tmul b₁ b₂ w)).trans
        (TensorProduct.tmul_add _ _ _)
    rw [e]
    exact (map_add φ.hom _ _).trans ((congrArg₂ (· + ·) h₁ h₂).trans (map_add ψ.hom _ _).symm)
  | tmul c s => exact h a r x c s w

/-- A scalar of `C` moves across the tensor product of an extension of scalars. -/
theorem extendScalars_mul_tmul {C D : Type u} [CommRing C] [CommRing D] (φ : C →+* D)
    (X : ModuleCat.{u} C) (c : C) (d : D) (x : X) :
    (φ c * d) ⊗ₜ[C, φ] x = d ⊗ₜ[C, φ] (c • x) := by
  let : Module C D := Module.compHom D φ
  exact TensorProduct.smul_tmul c d x

/-- On the summand `M^p ⊗ F^0`, the model map read over `R₀` is `modelBifunctorIso` followed by
`baseSideMap`. -/
theorem modelMapE_restrict_summand (M : CochainComplex (ModuleCat.{u} A) ℤ) (p : ℤ) :
    (ModuleCat.restrictScalars (algebraMap R₀ B₀)).map
        ((baseChangeFunctor A B₀).obj (M.X p) ◁ modelUnitComponent F ε ≫
          (modelTermMap (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀)).app (M.X p) ≫
          (Functor.isoWhiskerRight (baseChangeIsoExtendScalars A A')
            (ModuleCat.restrictScalars (modelRingMap R A R' A' R₀))).hom.app (M.X p)) =
      (modelBifunctorIso (M.X p) (F.X 0)).hom ≫
        ((baseChangeFunctor R R₀).obj ((ModuleCat.restrictScalars (algebraMap R A)).obj (M.X p)) ◁
            ε.f 0 ≫
          (baseTensorIso ≪≫ Functor.isoWhiskerRight (baseChangeIsoExtendScalars R R')
            (ModuleCat.restrictScalars (algebraMap R₀ R'))).hom.app
              ((ModuleCat.restrictScalars (algebraMap R A)).obj (M.X p))) ≫
        (ModuleCat.restrictScalars (algebraMap R₀ R')).map
          ((squareTermComparison R A R' A').app (M.X p)) ≫
        (restrictScalarsSquareHom R A R' A' R₀).app
          ((ModuleCat.extendScalars (algebraMap A A')).obj (M.X p)) := by
  refine tensorBaseChange_hom_ext' fun a r x c₁ c₂ w => ?_
  show (TensorProduct.congr (algebraRestrictLinearEquiv A A') (LinearEquiv.refl A (M.X p)))
      (modelTermAdd (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) (M.X p)
        (((a ⊗ₜ[R] r) ⊗ₜ[A] x) ⊗ₜ[B₀] ((c₁ ⊗ₜ[R] c₂) ⊗ₜ[R₀] augmentation F ε w))) = _
  rw [modelTermAdd_tmul, TensorProduct.congr_tmul]
  show _ = (baseSideMap (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) F ε (M.X p)).hom
      (baseChangeSwap (R := R) (A := A) (R₀ := R₀)
        ((ModuleCat.restrictScalars (algebraMap R A)).obj (M.X p))
        ((c₁ ⊗ₜ[R] c₂) • ((a ⊗ₜ[R] r) ⊗ₜ[A] x)) ⊗ₜ[R₀] w)
  refine Eq.trans ?_ (congrArg (fun t : R₀ ⊗[R] (ModuleCat.restrictScalars (algebraMap R A)).obj
    (M.X p) => (baseSideMap (R := R) (A := A) (R' := R') (A' := A')
    (R₀ := R₀) F ε (M.X p)).hom (t ⊗ₜ[R₀] w))
    (baseChangeSwap_smul_tmul (R := R) (M.X p) c₁ a c₂ r x)).symm
  refine Eq.trans ?_ (baseSideMap_tmul (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) F ε
    (M.X p) (c₂ * r) _ w).symm
  rw [modelUnitAddHom_tmul, modelRingMap_tmul, modelRingMap_tmul]
  show ((algebraMap A A' c₁ * algebraMap R' A' (algebraMap R₀ R' c₂) *
      algebraMap R' A' (augmentation F ε w) *
        (algebraMap A A' a * algebraMap R' A' (algebraMap R₀ R' r))) ⊗ₜ[A, algebraMap A A'] x :
      (ModuleCat.extendScalars (algebraMap A A')).obj (M.X p)) =
    (algebraMap R' A' ((c₂ * r) • augmentation F ε w) ⊗ₜ[A, algebraMap A A'] ((c₁ * a) • x))
  refine Eq.trans ?_ (extendScalars_mul_tmul (algebraMap A A') (M.X p) (c₁ * a) _ x)
  congr 1
  rw [Algebra.smul_def, map_mul, map_mul, map_mul, map_mul]
  ring_nf
  rfl

/-- **The model map, read over `R₀`, is the comparison of the square.** -/
theorem modelMapE_restrict (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    (modelRestrictIso F M).inv ≫
        ((ModuleCat.restrictScalars (algebraMap R₀ B₀)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (modelMapE (R := R) (A := A) (R' := R') (A' := A')
            (R₀ := R₀) F ε M) =
      (baseModelComparison F ε).app
          (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj M) ≫
        ((ModuleCat.restrictScalars (algebraMap R₀ R')).mapHomologicalComplex
          (ComplexShape.up ℤ)).map
            ((NatTrans.mapHomologicalComplex (squareTermComparison R A R' A')
              (ComplexShape.up ℤ)).app M) ≫
        (NatTrans.mapHomologicalComplex (restrictScalarsSquareHom R A R' A' R₀)
          (ComplexShape.up ℤ)).app
            (((ModuleCat.extendScalars (algebraMap A A')).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj M) := by
  ext n : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, HomologicalComplex.comp_f]
  have hL := congrArg (fun t => t ≫
      (((ModuleCat.restrictScalars (algebraMap R₀ B₀)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map (modelMapE (R := R) (A := A) (R' := R') (A' := A')
        (R₀ := R₀) F ε M)).f n)
    (ι_modelRestrictIso_inv (R := R) (A := A) (R₀ := R₀) F M p q n hpq)
  refine (Category.assoc _ _ _).symm.trans (hL.trans ?_)
  show (modelBifunctorIso (M.X p) (F.X q)).inv ≫
    (ModuleCat.restrictScalars (algebraMap R₀ B₀)).map
      (HomologicalComplex.ιMapBifunctor M F modelBifunctor (ComplexShape.up ℤ) p q n hpq ≫
        (modelMapE (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) F ε M).f n) = _
  by_cases hq : q = 0
  · subst hq
    obtain rfl : n = p := by simpa using hpq.symm
    have hR := congrArg (fun t => t ≫
        (((ModuleCat.restrictScalars (algebraMap R₀ R')).mapHomologicalComplex
          (ComplexShape.up ℤ)).map
            ((NatTrans.mapHomologicalComplex (squareTermComparison R A R' A')
              (ComplexShape.up ℤ)).app M)).f n ≫
        ((NatTrans.mapHomologicalComplex (restrictScalarsSquareHom R A R' A' R₀)
          (ComplexShape.up ℤ)).app
            (((ModuleCat.extendScalars (algebraMap A A')).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj M)).f n)
      (ι_baseModelComparison F ε
        (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj M) n hpq)
    refine Eq.trans ?_ ((Category.assoc _ _ _).symm.trans hR).symm
    rw [ι_modelMapE]
    refine (congrArg (fun t => (modelBifunctorIso (M.X n) (F.X 0)).inv ≫ t)
      (modelMapE_restrict_summand (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀)
        F ε M n)).trans ((Iso.inv_hom_id_assoc _ _).trans ?_)
    exact (Category.assoc _ _ _).symm
  · have hR := congrArg (fun t => t ≫
        (((ModuleCat.restrictScalars (algebraMap R₀ R')).mapHomologicalComplex
          (ComplexShape.up ℤ)).map
            ((NatTrans.mapHomologicalComplex (squareTermComparison R A R' A')
              (ComplexShape.up ℤ)).app M)).f n ≫
        ((NatTrans.mapHomologicalComplex (restrictScalarsSquareHom R A R' A' R₀)
          (ComplexShape.up ℤ)).app
            (((ModuleCat.extendScalars (algebraMap A A')).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj M)).f n)
      (ι_baseModelComparison_eq_zero F ε
        (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M) p q n hq hpq)
    refine Eq.trans ?_ ((Category.assoc _ _ _).symm.trans hR).symm
    rw [ι_modelMapE_eq_zero F ε M p q n hq hpq, Functor.map_zero, comp_zero, zero_comp]

end RingTheory.TorIndependence
