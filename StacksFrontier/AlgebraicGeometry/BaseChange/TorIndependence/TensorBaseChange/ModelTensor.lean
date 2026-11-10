module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.TensorBaseChange.LocalizedModuleCriterion

/-!
# The model complex of a tensor product

For complexes `P`, `N` of `A`-modules, the model map of `P ⊗_A N` is `A' ⊗_A P` tensored with the
model map of `N`, through the projection formula
`(B₀ ⊗_A P) ⊗_{B₀} Z ≅ (A' ⊗_A P) ⊗_{A'} Z` and the monoidality of base change
`A' ⊗_A (P ⊗_A N) ≅ (A' ⊗_A P) ⊗_{A'} (A' ⊗_A N)`.

## Main results

* `RingTheory.TorIndependence.projectionComplexIso`: the projection formula
  `(B₀ ⊗_A P) ⊗_{B₀} Z ≅ (A' ⊗_A P) ⊗_{A'} Z` for complexes.
* `RingTheory.TorIndependence.extTensorIso`: the isomorphism
  `A' ⊗_A (P ⊗_A N) ≅ (A' ⊗_A P) ⊗_{A'} (A' ⊗_A N)`.
* `RingTheory.TorIndependence.modelMapX_tensor`: the model map of `P ⊗_A N` is `A' ⊗_A P`
  tensored with the model map of `N`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct ChangeOfRings
open CochainComplex.DerivedExtensionScalars

universe u

namespace RingTheory.TorIndependence

section BaseChangeTensor

variable (C D : Type u) [CommRing C] [CommRing D] [Algebra C D]

/-- Base change `D ⊗_C -` preserves small colimits. -/
instance : PreservesColimitsOfSize.{0, 0} (baseChangeFunctor C D) :=
  preservesColimits_of_natIso (baseChangeIsoExtendScalars C D).symm

/-- Base change is monoidal: `D ⊗_C (X ⊗_C Y) ≅ (D ⊗_C X) ⊗_D (D ⊗_C Y)`. -/
def bcTensorEquiv (X Y : ModuleCat.{u} C) :
    (baseChangeFunctor C D).obj (X ⊗ Y) ≃ₗ[D]
      ((baseChangeFunctor C D).obj X ⊗ (baseChangeFunctor C D).obj Y : ModuleCat.{u} D) :=
  TensorProduct.AlgebraTensorModule.distribBaseChange C D X Y

/-- `bcTensorEquiv` sends `d ⊗ (x ⊗ y)` to `(d ⊗ x) ⊗ (1 ⊗ y)`. -/
theorem bcTensorEquiv_tmul (X Y : ModuleCat.{u} C) (d : D) (x : X) (y : Y) :
    bcTensorEquiv C D X Y (d ⊗ₜ[C] (x ⊗ₜ[C] y)) = (d ⊗ₜ[C] x) ⊗ₜ[D] ((1 : D) ⊗ₜ[C] y) := rfl

/-- Induction on `D ⊗_C (X ⊗_C Y)`: it suffices to treat the elements `d ⊗ (x ⊗ y)`. -/
private theorem induction_on_tmul_tmul_right {X Y : Type u} [AddCommGroup X] [Module C X]
    [AddCommGroup Y] [Module C Y] {motive : D ⊗[C] (X ⊗[C] Y) → Prop} (t : D ⊗[C] (X ⊗[C] Y))
    (add : ∀ t t', motive t → motive t' → motive (t + t'))
    (tmul : ∀ d x y, motive (d ⊗ₜ[C] (x ⊗ₜ[C] y))) : motive t := by
  induction t using TensorProduct.inductionOn with
  | add t t' ht ht' => exact add _ _ ht ht'
  | tmul d z =>
    induction z using TensorProduct.inductionOn with
    | add z z' hz hz' => simpa [TensorProduct.tmul_add] using add _ _ hz hz'
    | tmul x y => exact tmul d x y

/-- The isomorphism `D ⊗_C (X ⊗_C Y) ≃ (D ⊗_C X) ⊗_D (D ⊗_C Y)` is natural in `X`. -/
theorem distribBaseChange_naturality_left {X X' Y : Type u} [AddCommGroup X] [Module C X]
    [AddCommGroup X'] [Module C X'] [AddCommGroup Y] [Module C Y] (f : X →ₗ[C] X')
    (t : D ⊗[C] (X ⊗[C] Y)) :
    TensorProduct.AlgebraTensorModule.distribBaseChange C D X' Y
        ((f.rTensor Y).baseChange D t) =
      LinearMap.rTensor _ (f.baseChange D)
        (TensorProduct.AlgebraTensorModule.distribBaseChange C D X Y t) := by
  induction t using induction_on_tmul_tmul_right with
  | add t t' ht ht' => simp only [map_add, ht, ht']
  | tmul d x y => rfl

/-- The isomorphism `D ⊗_C (X ⊗_C Y) ≃ (D ⊗_C X) ⊗_D (D ⊗_C Y)` is natural in `Y`. -/
theorem distribBaseChange_naturality_right {X Y Y' : Type u} [AddCommGroup X] [Module C X]
    [AddCommGroup Y] [Module C Y] [AddCommGroup Y'] [Module C Y'] (g : Y →ₗ[C] Y')
    (t : D ⊗[C] (X ⊗[C] Y)) :
    TensorProduct.AlgebraTensorModule.distribBaseChange C D X Y'
        ((g.lTensor X).baseChange D t) =
      LinearMap.lTensor _ (g.baseChange D)
        (TensorProduct.AlgebraTensorModule.distribBaseChange C D X Y t) := by
  induction t using induction_on_tmul_tmul_right with
  | add t t' ht ht' => simp only [map_add, ht, ht']
  | tmul d x y => rfl

/-- The comparison `D ⊗_C (X ⊗_C Y) ≅ (D ⊗_C X) ⊗_D (D ⊗_C Y)`, as an isomorphism. -/
def bcTensorIso (X Y : ModuleCat.{u} C) :
    (baseChangeFunctor C D).obj (((curriedTensor (ModuleCat.{u} C)).obj X).obj Y) ≅
      ((curriedTensor (ModuleCat.{u} D)).obj ((baseChangeFunctor C D).obj X)).obj
        ((baseChangeFunctor C D).obj Y) :=
  (bcTensorEquiv C D X Y).toModuleIso

variable (M N : CochainComplex (ModuleCat.{u} C) ℤ)

/-- **Base change of a total tensor complex**: `D ⊗_C (M ⊗_C N) ≅ (D ⊗_C M) ⊗_D (D ⊗_C N)`
for complexes `M`, `N` of `C`-modules. -/
def bcComplexTensorIso :
    ((baseChangeFunctor C D).mapHomologicalComplex (ComplexShape.up ℤ)).obj (M ⊗ N) ≅
      ((baseChangeFunctor C D).mapHomologicalComplex (ComplexShape.up ℤ)).obj M ⊗
        ((baseChangeFunctor C D).mapHomologicalComplex (ComplexShape.up ℤ)).obj N :=
  CategoryTheory.Functor.mapBifunctorTotalIso (curriedTensor (ModuleCat.{u} C))
    (curriedTensor (ModuleCat.{u} D)) (baseChangeFunctor C D) (baseChangeFunctor C D)
    (baseChangeFunctor C D) (bcTensorIso C D)
    (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
    (fun f Y => by ext t; exact distribBaseChange_naturality_left C D f.hom t)
    (fun X _ _ g => by ext t; exact distribBaseChange_naturality_right C D g.hom t) M N

/-- On the summand `D ⊗_C (M^p ⊗_C N^q)`, the forward map of `bcComplexTensorIso` is
`bcTensorIso` followed by the inclusion of `(D ⊗_C M^p) ⊗_D (D ⊗_C N^q)`. -/
@[reassoc]
theorem ι_bcComplexTensorIso_hom (p q n : ℤ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n) :
    (baseChangeFunctor C D).map (HomologicalComplex.ιMapBifunctor M N
        (curriedTensor (ModuleCat.{u} C)) (ComplexShape.up ℤ) p q n h) ≫
      (bcComplexTensorIso C D M N).hom.f n =
    (bcTensorIso C D (M.X p) (N.X q)).hom ≫
      HomologicalComplex.ιMapBifunctor
        (((baseChangeFunctor C D).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)
        (((baseChangeFunctor C D).mapHomologicalComplex (ComplexShape.up ℤ)).obj N)
        (curriedTensor (ModuleCat.{u} D)) (ComplexShape.up ℤ) p q n h :=
  CategoryTheory.Functor.ι_mapBifunctorTotalIso_hom (curriedTensor (ModuleCat.{u} C))
    (curriedTensor (ModuleCat.{u} D)) (baseChangeFunctor C D) (baseChangeFunctor C D)
    (baseChangeFunctor C D) (bcTensorIso C D)
    (ComplexShape.up ℤ) (ComplexShape.up ℤ)
    _ _ M N p q n h

/-- On the summand `(D ⊗_C M^p) ⊗_D (D ⊗_C N^q)`, the inverse of `bcComplexTensorIso` is the
inverse of `bcTensorIso` followed by the base change of the inclusion of `M^p ⊗_C N^q`. -/
theorem ι_bcComplexTensorIso_inv (p q n : ℤ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n) :
    HomologicalComplex.ιMapBifunctor
        (((baseChangeFunctor C D).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)
        (((baseChangeFunctor C D).mapHomologicalComplex (ComplexShape.up ℤ)).obj N)
        (curriedTensor (ModuleCat.{u} D)) (ComplexShape.up ℤ) p q n h ≫
      (bcComplexTensorIso C D M N).inv.f n =
    (bcTensorIso C D (M.X p) (N.X q)).inv ≫
      (baseChangeFunctor C D).map (HomologicalComplex.ιMapBifunctor M N
        (curriedTensor (ModuleCat.{u} C)) (ComplexShape.up ℤ) p q n h) :=
  CategoryTheory.Functor.ι_mapBifunctorTotalIso_inv (curriedTensor (ModuleCat.{u} C))
    (curriedTensor (ModuleCat.{u} D)) (baseChangeFunctor C D) (baseChangeFunctor C D)
    (baseChangeFunctor C D) (bcTensorIso C D)
    (ComplexShape.up ℤ) (ComplexShape.up ℤ)
    _ _ M N p q n h

end BaseChangeTensor

section Projection

variable {R A R' A' R₀ : Type u}
  [CommRing R] [CommRing A] [CommRing R'] [CommRing A'] [CommRing R₀]
  [Algebra R A] [Algebra R R'] [Algebra R A'] [Algebra A A'] [Algebra R' A']
  [IsScalarTower R A A'] [IsScalarTower R R' A']
  [Algebra R R₀] [Algebra R₀ R'] [IsScalarTower R R₀ R']

attribute [local instance] Algebra.TensorProduct.rightAlgebra

local notation "B₀" => A ⊗[R] R₀

variable (X : Type u) [AddCommGroup X] [Module A X] (W : ModuleCat.{u} A')

/-- `(B₀ ⊗_A X) ⊗_{B₀} W ≃ (A' ⊗_A X) ⊗_{A'} W` for an `A'`-module `W`, additively. -/
def projectionAddEquiv :
    (B₀ ⊗[A] X) ⊗[B₀] ((ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).obj W) ≃+
      (A' ⊗[A] X) ⊗[A'] W :=
  letI : Module A' ((ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).obj W) := W.isModule
  letI : Module A W := Module.compHom W (algebraMap A A')
  letI : Module A ((ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).obj W) :=
    Module.compHom W (algebraMap A A')
  haveI : IsScalarTower A A' W := ⟨fun a a' w => by
    change (a • a') • w = algebraMap A A' a • a' • w
    rw [Algebra.smul_def, mul_smul]⟩
  haveI : IsScalarTower A B₀ ((ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).obj W) :=
    ⟨fun a b w => by
      change modelRingMap R A R' A' R₀ (a • b) • (show W from w) =
        algebraMap A A' a • modelRingMap R A R' A' R₀ b • (show W from w)
      rw [Algebra.smul_def, map_mul, Algebra.TensorProduct.algebraMap_apply, modelRingMap_tmul,
        Algebra.algebraMap_self, RingHom.id_apply, map_one, map_one, mul_one, mul_smul]⟩
  ((TensorProduct.comm B₀ (B₀ ⊗[A] X) _).trans
      (TensorProduct.AlgebraTensorModule.cancelBaseChange A B₀ B₀
        ((ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).obj W) X)).toAddEquiv.trans
    ((TensorProduct.comm A' (A' ⊗[A] X) W).trans
      (TensorProduct.AlgebraTensorModule.cancelBaseChange A A' A' W X)).toAddEquiv.symm

/-- `projectionAddEquiv` sends `(c ⊗ x) ⊗ w` to `(1 ⊗ x) ⊗ c w`, where `c` acts on `w` through
`modelRingMap`. -/
theorem projectionAddEquiv_tmul (c : B₀) (x : X)
    (w : (ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).obj W) :
    projectionAddEquiv (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) X W
        ((c ⊗ₜ[A] x) ⊗ₜ[B₀] w) =
      ((1 : A') ⊗ₜ[A] x) ⊗ₜ[A'] (modelRingMap R A R' A' R₀ c • (show W from w)) := rfl

/-- Induction on `(B₀ ⊗_A Y) ⊗_{B₀} V`: it suffices to treat the elements `(c ⊗ y) ⊗ v`. -/
private theorem induction_on_tmul_tmul_left {Y V : Type u} [AddCommGroup Y] [Module A Y]
    [AddCommGroup V] [Module B₀ V] {motive : (B₀ ⊗[A] Y) ⊗[B₀] V → Prop}
    (t : (B₀ ⊗[A] Y) ⊗[B₀] V)
    (add : ∀ t t', motive t → motive t' → motive (t + t'))
    (tmul : ∀ c y v, motive ((c ⊗ₜ[A] y) ⊗ₜ[B₀] v)) : motive t := by
  induction t using TensorProduct.inductionOn with
  | add t t' ht ht' => exact add _ _ ht ht'
  | tmul m v =>
    induction m using TensorProduct.inductionOn with
    | add m m' hm hm' => simpa [TensorProduct.add_tmul] using add _ _ hm hm'
    | tmul c y => exact tmul c y v

/-- `projectionAddEquiv` is semilinear along `modelRingMap : A ⊗_R R₀ → A'`. -/
theorem projectionAddEquiv_smul (b : B₀)
    (t : (B₀ ⊗[A] X) ⊗[B₀] ((ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).obj W)) :
    projectionAddEquiv (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) X W (b • t) =
      modelRingMap R A R' A' R₀ b •
        projectionAddEquiv (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) X W t := by
  induction t using induction_on_tmul_tmul_left with
  | add t t' ht ht' => rw [smul_add, map_add, map_add, ht, ht', smul_add]
  | tmul c x w =>
    rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, projectionAddEquiv_tmul,
      projectionAddEquiv_tmul, TensorProduct.smul_tmul', ← TensorProduct.smul_tmul,
      TensorProduct.smul_tmul', map_mul, mul_smul]
    rw [smul_comm _ (modelRingMap R A R' A' R₀ c), ← TensorProduct.smul_tmul',
      TensorProduct.smul_tmul, TensorProduct.smul_tmul']

/-- `projectionAddEquiv` is natural in the `A`-module `X`. -/
theorem projectionAddEquiv_naturality_left {X X' : Type u} [AddCommGroup X] [Module A X]
    [AddCommGroup X'] [Module A X'] (f : X →ₗ[A] X') (W : ModuleCat.{u} A')
    (t : (B₀ ⊗[A] X) ⊗[B₀] ((ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).obj W)) :
    projectionAddEquiv (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) X' W
        (LinearMap.rTensor _ (f.baseChange B₀) t) =
      LinearMap.rTensor W (f.baseChange A')
        (projectionAddEquiv (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) X W t) := by
  induction t using induction_on_tmul_tmul_left with
  | add t t' ht ht' => rw [map_add, map_add, ht, ht', map_add, map_add]
  | tmul c x w =>
    rw [LinearMap.rTensor_tmul, LinearMap.baseChange_tmul, projectionAddEquiv_tmul,
      projectionAddEquiv_tmul, LinearMap.rTensor_tmul, LinearMap.baseChange_tmul]

/-- `projectionAddEquiv` is natural in the `A'`-module `W`. -/
theorem projectionAddEquiv_naturality_right (X : Type u) [AddCommGroup X] [Module A X]
    {W W' : ModuleCat.{u} A'} (g : W ⟶ W')
    (t : (B₀ ⊗[A] X) ⊗[B₀] ((ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).obj W)) :
    projectionAddEquiv (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) X W'
        (LinearMap.lTensor _
          ((ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).map g).hom t) =
      LinearMap.lTensor _ g.hom
        (projectionAddEquiv (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) X W t) := by
  induction t using induction_on_tmul_tmul_left with
  | add t t' ht ht' => rw [map_add, map_add, ht, ht', map_add, map_add]
  | tmul c x w =>
    rw [LinearMap.lTensor_tmul, projectionAddEquiv_tmul, projectionAddEquiv_tmul,
      LinearMap.lTensor_tmul]
    congr 1
    exact (g.hom.map_smul _ _).symm

/-- The projection formula `(B₀ ⊗_A X) ⊗_{B₀} W ≅ (A' ⊗_A X) ⊗_{A'} W` as modules over
`A ⊗_R R₀`. -/
def projectionLinearEquiv (X : ModuleCat.{u} A) (W : ModuleCat.{u} A') :
    (((curriedTensor (ModuleCat.{u} B₀)).obj ((baseChangeFunctor A B₀).obj X)).obj
        ((ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).obj W)) ≃ₗ[B₀]
      ((ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).obj
        (((baseChangeFunctor A A' ⋙ curriedTensor (ModuleCat.{u} A')).obj X).obj W)) where
  toFun t := projectionAddEquiv (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) X W t
  invFun t := (projectionAddEquiv (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) X W).symm t
  map_add' := map_add _
  map_smul' := projectionAddEquiv_smul X W
  left_inv := (projectionAddEquiv (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) X W).left_inv
  right_inv := (projectionAddEquiv (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) X W).right_inv

/-- The projection formula, as the comparison isomorphism of a bifunctor. -/
def projectionIso (X : ModuleCat.{u} A) (W : ModuleCat.{u} A') :
    (ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).obj
        (((baseChangeFunctor A A' ⋙ curriedTensor (ModuleCat.{u} A')).obj X).obj W) ≅
      ((curriedTensor (ModuleCat.{u} B₀)).obj ((baseChangeFunctor A B₀).obj X)).obj
        ((ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).obj W) :=
  (projectionLinearEquiv (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) X W).toModuleIso.symm

/-- If `e'` intertwines `f` and `g` along `e`, then `e'.symm` intertwines `g` and `f`. -/
private theorem addEquiv_symm_comm {α β α' β' : Type*} [Add α] [Add β] [Add α'] [Add β']
    (e : α ≃+ β) (e' : α' ≃+ β') {f : α → α'} {g : β → β'} (h : ∀ t, e' (f t) = g (e t))
    (s : β) : e'.symm (g s) = f (e.symm s) := by
  rw [AddEquiv.symm_apply_eq, h, e.apply_symm_apply]

/-- `projectionIso` is natural in the `A`-module `X`. -/
theorem projectionIso_naturality_left {X X' : ModuleCat.{u} A} (f : X ⟶ X') (W : ModuleCat.{u} A') :
    (ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).map
        (((baseChangeFunctor A A' ⋙ curriedTensor (ModuleCat.{u} A')).map f).app W) ≫
      (projectionIso (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) X' W).hom =
    (projectionIso (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) X W).hom ≫
      ((curriedTensor (ModuleCat.{u} B₀)).map ((baseChangeFunctor A B₀).map f)).app
        ((ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).obj W) := by
  ext s
  exact addEquiv_symm_comm _ _ (projectionAddEquiv_naturality_left f.hom W) s

/-- `projectionIso` is natural in the `A'`-module `W`. -/
theorem projectionIso_naturality_right (X : ModuleCat.{u} A) {W W' : ModuleCat.{u} A'}
    (g : W ⟶ W') :
    (ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).map
        (((baseChangeFunctor A A' ⋙ curriedTensor (ModuleCat.{u} A')).obj X).map g) ≫
      (projectionIso (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) X W').hom =
    (projectionIso (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) X W).hom ≫
      ((curriedTensor (ModuleCat.{u} B₀)).obj ((baseChangeFunctor A B₀).obj X)).map
        ((ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).map g) := by
  ext s
  exact addEquiv_symm_comm _ _ (projectionAddEquiv_naturality_right X g) s

/-- For an `A`-module `X`, the functor `W ↦ (A' ⊗_A X) ⊗_{A'} W` preserves zero morphisms. -/
instance (X : ModuleCat.{u} A) :
    ((baseChangeFunctor A A' ⋙ curriedTensor (ModuleCat.{u} A')).obj X).PreservesZeroMorphisms :=
  inferInstanceAs (((curriedTensor (ModuleCat.{u} A')).obj
    ((baseChangeFunctor A A').obj X)).PreservesZeroMorphisms)

/-- The bifunctor `(X, W) ↦ (A' ⊗_A X) ⊗_{A'} W` preserves zero morphisms in `X`. -/
instance : (baseChangeFunctor A A' ⋙ curriedTensor (ModuleCat.{u} A')).PreservesZeroMorphisms :=
  inferInstance

/-- **The projection formula for complexes**: `(B₀ ⊗_A P) ⊗_{B₀} Z ≅ (A' ⊗_A P) ⊗_{A'} Z`,
read over `A ⊗_R R₀`. -/
def projectionComplexIso (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (Z : CochainComplex (ModuleCat.{u} A') ℤ) :
    ((ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
        (HomologicalComplex.mapBifunctor P Z (baseChangeFunctor A A' ⋙
          curriedTensor (ModuleCat.{u} A')) (ComplexShape.up ℤ)) ≅
      ((baseChangeFunctor A B₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj P ⊗
        ((ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj Z :=
  CategoryTheory.Functor.mapBifunctorTotalIso
    (baseChangeFunctor A A' ⋙ curriedTensor (ModuleCat.{u} A'))
    (curriedTensor (ModuleCat.{u} B₀)) (baseChangeFunctor A B₀)
    (ModuleCat.restrictScalars (modelRingMap R A R' A' R₀))
    (ModuleCat.restrictScalars (modelRingMap R A R' A' R₀))
    (projectionIso (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀))
    (ComplexShape.up ℤ) (ComplexShape.up ℤ) (c := ComplexShape.up ℤ)
    projectionIso_naturality_left projectionIso_naturality_right P Z

/-- On the summand `(B₀ ⊗_A P^p) ⊗_{B₀} Z^q`, the inverse of `projectionComplexIso` is the
inverse of `projectionIso` followed by the inclusion of `(A' ⊗_A P^p) ⊗_{A'} Z^q`. -/
theorem ι_projectionComplexIso_inv (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (Z : CochainComplex (ModuleCat.{u} A') ℤ) (p q n : ℤ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n) :
    HomologicalComplex.ιMapBifunctor
        (((baseChangeFunctor A B₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
        (((ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj Z)
        (curriedTensor (ModuleCat.{u} B₀)) (ComplexShape.up ℤ) p q n h ≫
      (projectionComplexIso P Z).inv.f n =
    (projectionIso (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) (P.X p) (Z.X q)).inv ≫
      (ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).map
        (HomologicalComplex.ιMapBifunctor P Z
          (baseChangeFunctor A A' ⋙ curriedTensor (ModuleCat.{u} A')) (ComplexShape.up ℤ)
          p q n h) :=
  CategoryTheory.Functor.ι_mapBifunctorTotalIso_inv
    (baseChangeFunctor A A' ⋙ curriedTensor (ModuleCat.{u} A'))
    (curriedTensor (ModuleCat.{u} B₀)) (baseChangeFunctor A B₀)
    (ModuleCat.restrictScalars (modelRingMap R A R' A' R₀))
    (ModuleCat.restrictScalars (modelRingMap R A R' A' R₀))
    (projectionIso (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀))
    (ComplexShape.up ℤ) (ComplexShape.up ℤ)
    projectionIso_naturality_left projectionIso_naturality_right P Z p q n h

/-- `projectionComplexIso`, with its source spelled as a tensor product of complexes. -/
def projectionComplexIso' (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (Z : CochainComplex (ModuleCat.{u} A') ℤ) :
    ((ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
        (((baseChangeFunctor A A').mapHomologicalComplex (ComplexShape.up ℤ)).obj P ⊗ Z) ≅
      ((baseChangeFunctor A B₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj P ⊗
        ((ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj Z :=
  projectionComplexIso P Z

/-- On the summand `(B₀ ⊗_A P^p) ⊗_{B₀} Z^q`, the inverse of `projectionComplexIso'` is the
inverse of `projectionIso` followed by the inclusion of `(A' ⊗_A P^p) ⊗_{A'} Z^q`. -/
theorem ι_projectionComplexIso'_inv (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (Z : CochainComplex (ModuleCat.{u} A') ℤ) (p q n : ℤ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n) :
    HomologicalComplex.ιTensorObj
        (((baseChangeFunctor A B₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
        (((ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj Z) p q n h ≫
      (projectionComplexIso' P Z).inv.f n =
    (projectionIso (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) (P.X p) (Z.X q)).inv ≫
      (ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).map
        (HomologicalComplex.ιTensorObj
          (((baseChangeFunctor A A').mapHomologicalComplex (ComplexShape.up ℤ)).obj P) Z
          p q n h) :=
  ι_projectionComplexIso_inv P Z p q n h

end Projection

end RingTheory.TorIndependence

namespace RingTheory.TorIndependence

section TensorModel

variable {R A R' A' R₀ : Type u}
  [CommRing R] [CommRing A] [CommRing R'] [CommRing A'] [CommRing R₀]
  [Algebra R A] [Algebra R R'] [Algebra R A'] [Algebra A A'] [Algebra R' A']
  [IsScalarTower R A A'] [IsScalarTower R R' A']
  [Algebra R R₀] [Algebra R₀ R'] [IsScalarTower R R₀ R']

attribute [local instance] Algebra.TensorProduct.rightAlgebra

local notation "B₀" => A ⊗[R] R₀

variable (F : CochainComplex (ModuleCat.{u} R₀) ℤ)
  (ε : F ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} R₀) 0).obj (ModuleCat.of R₀ R'))

/-- `A' ⊗_A (P ⊗_A N) ≅ (A' ⊗_A P) ⊗_{A'} (A' ⊗_A N)`, with the extension of scalars of
Mathlib on the outer factors. -/
def extTensorIso (P N : CochainComplex (ModuleCat.{u} A) ℤ) :
    ((ModuleCat.extendScalars (algebraMap A A')).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (P ⊗ N) ≅
      ((baseChangeFunctor A A').mapHomologicalComplex (ComplexShape.up ℤ)).obj P ⊗
        ((ModuleCat.extendScalars (algebraMap A A')).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj N :=
  (NatIso.mapHomologicalComplex (baseChangeIsoExtendScalars A A') (ComplexShape.up ℤ)).symm.app
      (P ⊗ N) ≪≫ bcComplexTensorIso A A' P N ≪≫
    whiskerLeftIso (((baseChangeFunctor A A').mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
      ((NatIso.mapHomologicalComplex (baseChangeIsoExtendScalars A A') (ComplexShape.up ℤ)).app N)

/-- A pure tensor `s ⊗ m` is `s` times `1 ⊗ m`. -/
private theorem tmul_eq_smul_one_tmul {S M : Type*} (R : Type*) [CommSemiring R] [CommSemiring S]
    [Algebra R S] [AddCommMonoid M] [Module R M] (s : S) (m : M) :
    s ⊗ₜ[R] m = s • ((1 : S) ⊗ₜ[R] m) := by
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- Linear maps out of `((B₀ ⊗_A X) ⊗ (B₀ ⊗_A Y)) ⊗ (B₀ ⊗_{R₀} W)` agree as soon as they
agree on the elements `((1 ⊗ x) ⊗ (1 ⊗ y)) ⊗ (1 ⊗ w)`. -/
theorem tensorThree_linearMap_ext {X Y W T : Type u} [AddCommGroup X] [Module A X]
    [AddCommGroup Y] [Module A Y] [AddCommGroup W] [Module R₀ W] [AddCommGroup T] [Module B₀ T]
    {φ ψ : ((B₀ ⊗[A] X) ⊗[B₀] (B₀ ⊗[A] Y)) ⊗[B₀] (B₀ ⊗[R₀] W) →ₗ[B₀] T}
    (h : ∀ (x : X) (y : Y) (w : W),
      φ ((((1 : B₀) ⊗ₜ[A] x) ⊗ₜ[B₀] ((1 : B₀) ⊗ₜ[A] y)) ⊗ₜ[B₀] ((1 : B₀) ⊗ₜ[R₀] w)) =
        ψ ((((1 : B₀) ⊗ₜ[A] x) ⊗ₜ[B₀] ((1 : B₀) ⊗ₜ[A] y)) ⊗ₜ[B₀] ((1 : B₀) ⊗ₜ[R₀] w))) :
    φ = ψ := by
  refine LinearMap.ext fun t => ?_
  induction t using TensorProduct.inductionOn with
  | add t t' ht ht' => rw [map_add, map_add, ht, ht']
  | tmul m v =>
    induction v using TensorProduct.inductionOn with
    | add v v' hv hv' => rw [TensorProduct.tmul_add, map_add, map_add, hv, hv']
    | tmul b₃ w =>
      induction m using TensorProduct.inductionOn with
      | add m m' hm hm' => rw [TensorProduct.add_tmul, map_add, map_add, hm, hm']
      | tmul m₁ m₂ =>
        induction m₁ using TensorProduct.inductionOn with
        | add m m' hm hm' =>
          rw [TensorProduct.add_tmul, TensorProduct.add_tmul, map_add, map_add, hm, hm']
        | tmul b₁ x =>
          induction m₂ using TensorProduct.inductionOn with
          | add m m' hm hm' =>
            rw [TensorProduct.tmul_add, TensorProduct.add_tmul, map_add, map_add, hm, hm']
          | tmul b₂ y =>
            rw [tmul_eq_smul_one_tmul A b₁ x, tmul_eq_smul_one_tmul A b₂ y,
              tmul_eq_smul_one_tmul R₀ b₃ w]
            simp only [TensorProduct.tmul_smul, ← TensorProduct.smul_tmul', map_smul, h]

/-- The model map `modelMapX ε M` vanishes on the summands `(B₀ ⊗_A M^p) ⊗ (B₀ ⊗_{R₀} F^q)` with
`q ≠ 0`. -/
theorem ι_modelMapX_eq_zero (M : CochainComplex (ModuleCat.{u} A) ℤ) (p q n : ℤ) (hq : q ≠ 0)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n) :
    HomologicalComplex.ιMapBifunctor
        (((baseChangeFunctor A B₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)
        (((baseChangeFunctor R₀ B₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj F)
        (curriedTensor (ModuleCat.{u} B₀)) (ComplexShape.up ℤ) p q n h ≫
      (modelMapX (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) ε M).f n = 0 :=
  ι_modelMapE_eq_zero F ε M p q n hq h

/-- On the summand `(B₀ ⊗_A M^p) ⊗ (B₀ ⊗_{R₀} F^0)`, the model map `modelMapX ε M` is
`modelUnitComponent F ε` followed by `modelTermMap` at `M^p` and the comparison
`baseChangeIsoExtendScalars`. -/
theorem ι_modelMapX (M : CochainComplex (ModuleCat.{u} A) ℤ) (p : ℤ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, 0) = p) :
    HomologicalComplex.ιMapBifunctor
        (((baseChangeFunctor A B₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)
        (((baseChangeFunctor R₀ B₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj F)
        (curriedTensor (ModuleCat.{u} B₀)) (ComplexShape.up ℤ) p 0 p h ≫
      (modelMapX (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) ε M).f p =
    (baseChangeFunctor A B₀).obj (M.X p) ◁ modelUnitComponent F ε ≫
      (modelTermMap (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀)).app (M.X p) ≫
      (Functor.isoWhiskerRight (baseChangeIsoExtendScalars A A')
        (ModuleCat.restrictScalars (modelRingMap R A R' A' R₀))).hom.app (M.X p) :=
  ι_modelMapE F ε M p h

/-- On the summand indexed by `(i₁, i₂, 0)`, the right-hand side of `modelMapX_tensor` is
`P^{i₁}` tensored with the component of the model map of `N` at `N^{i₂}`, followed by the
inverse of `projectionIso` and the inclusion of `(A' ⊗_A P^{i₁}) ⊗_{A'} (A' ⊗_A N^{i₂})`. -/
theorem modelTensor_rhs (P N : CochainComplex (ModuleCat.{u} A) ℤ) (i₁ i₂ q n : ℤ)
    (hq : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (i₂, 0) = q)
    (hn : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (i₁, q) = n)
    (hn' : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (i₁, i₂) = n) :
    (α_ ((((baseChangeFunctor A B₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj P).X i₁)
        ((((baseChangeFunctor A B₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj N).X i₂)
        ((((baseChangeFunctor R₀ B₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj F).X 0)).hom ≫
      (((((baseChangeFunctor A B₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj P).X i₁ ◁
          HomologicalComplex.ιTensorObj
            (((baseChangeFunctor A B₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj N)
            (((baseChangeFunctor R₀ B₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj F)
            i₂ 0 q hq) ≫
        HomologicalComplex.ιTensorObj
          (((baseChangeFunctor A B₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
          (modelComplex A F N) i₁ q n hn) ≫
      (((baseChangeFunctor A B₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj P ◁
        modelMapX (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) ε N).f n ≫
      (projectionComplexIso' P (((ModuleCat.extendScalars (algebraMap A A')).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj N)).inv.f n =
    ((α_ ((((baseChangeFunctor A B₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj P).X i₁)
        ((((baseChangeFunctor A B₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj N).X i₂)
        ((((baseChangeFunctor R₀ B₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj F).X 0)).hom ≫
      ((((baseChangeFunctor A B₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj P).X i₁ ◁
        ((baseChangeFunctor A B₀).obj (N.X i₂) ◁ modelUnitComponent F ε ≫
          (modelTermMap (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀)).app (N.X i₂) ≫
          (Functor.isoWhiskerRight (baseChangeIsoExtendScalars A A')
            (ModuleCat.restrictScalars (modelRingMap R A R' A' R₀))).hom.app (N.X i₂))) ≫
      (projectionIso (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) (P.X i₁)
        ((((ModuleCat.extendScalars (algebraMap A A')).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj N).X i₂)).inv) ≫
      (ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).map
        (HomologicalComplex.ιTensorObj
          (((baseChangeFunctor A A').mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
          (((ModuleCat.extendScalars (algebraMap A A')).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj N) i₁ i₂ n hn') := by
  obtain rfl : q = i₂ := by rw [← hq]; exact add_zero i₂
  rw [Category.assoc, Category.assoc, HomologicalComplex.Monoidal.ι_whiskerLeft_assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc, ι_modelMapX, ι_projectionComplexIso'_inv]
  simp only [Category.assoc]

/-- On the summand `A' ⊗_A (P^p ⊗_A N^q)`, the forward map of `extTensorIso` is the composite of
`baseChangeIsoExtendScalars`, `bcTensorIso` and the inclusion of
`(A' ⊗_A P^p) ⊗_{A'} (A' ⊗_A N^q)`. -/
theorem ι_extTensorIso_hom (P N : CochainComplex (ModuleCat.{u} A) ℤ) (p q n : ℤ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n) :
    (ModuleCat.extendScalars (algebraMap A A')).map (HomologicalComplex.ιMapBifunctor P N
        (curriedTensor (ModuleCat.{u} A)) (ComplexShape.up ℤ) p q n h) ≫
      (extTensorIso P N).hom.f n =
    (baseChangeIsoExtendScalars A A').inv.app _ ≫ (bcTensorIso A A' (P.X p) (N.X q)).hom ≫
      ((baseChangeFunctor A A').obj (P.X p) ◁ (baseChangeIsoExtendScalars A A').hom.app (N.X q)) ≫
      HomologicalComplex.ιTensorObj
        (((baseChangeFunctor A A').mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
        (((ModuleCat.extendScalars (algebraMap A A')).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj N) p q n h := by
  dsimp only [extTensorIso, Iso.trans_hom, Iso.app_hom, Iso.symm_hom, NatIso.mapHomologicalComplex,
    whiskerLeftIso_hom]
  simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f]
  have hn := (baseChangeIsoExtendScalars A A').inv.naturality
    (HomologicalComplex.ιMapBifunctor P N (curriedTensor (ModuleCat.{u} A)) (ComplexShape.up ℤ)
      p q n h)
  rw [← Category.assoc]
  refine (congrArg (fun t => t ≫ _) hn).trans ?_
  rw [Category.assoc]
  congr 1
  rw [ι_bcComplexTensorIso_hom_assoc]
  congr 1
  exact HomologicalComplex.Monoidal.ι_whiskerLeft _ _ p q n h

/-- Two composites `x ≫ y ≫ (m ≫ i ≫ r₁) ≫ r₂` and `x ≫ y ≫ (m ≫ i ≫ r₁') ≫ r₂'` agree when
`r₁ ≫ r₂ = r₁' ≫ r₂'`. -/
theorem cancel_tail_helper {C : Type*} [Category C] {U₀ U V W₀ W Y Y' Z : C} (x : U₀ ⟶ U)
    (y : U ⟶ V) (m : V ⟶ W₀) (i : W₀ ⟶ W) (r₁ : W ⟶ Y) (r₂ : Y ⟶ Z) (r₁' : W ⟶ Y')
    (r₂' : Y' ⟶ Z) (h : r₁ ≫ r₂ = r₁' ≫ r₂') :
    x ≫ y ≫ (m ≫ i ≫ r₁) ≫ r₂ = x ≫ y ≫ (m ≫ i ≫ r₁') ≫ r₂' := by
  simp only [Category.assoc, h]

/-- The composite of `modelUnitComponent F ε`, `modelTermMap` and `baseChangeIsoExtendScalars`
is natural in the `A`-module `X`. -/
theorem modelUnit_naturality {X Y : ModuleCat.{u} A} (g : X ⟶ Y) :
    (baseChangeFunctor A B₀).map g ▷
        (((baseChangeFunctor R₀ B₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj F).X 0 ≫
      (baseChangeFunctor A B₀).obj Y ◁ modelUnitComponent F ε ≫
      (modelTermMap (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀)).app Y ≫
      (Functor.isoWhiskerRight (baseChangeIsoExtendScalars A A')
        (ModuleCat.restrictScalars (modelRingMap R A R' A' R₀))).hom.app Y =
    (baseChangeFunctor A B₀).obj X ◁ modelUnitComponent F ε ≫
      (modelTermMap (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀)).app X ≫
      (Functor.isoWhiskerRight (baseChangeIsoExtendScalars A A')
        (ModuleCat.restrictScalars (modelRingMap R A R' A' R₀))).hom.app X ≫
      (ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).map
        ((ModuleCat.extendScalars (algebraMap A A')).map g) := by
  have e2 := (modelTermMap (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀)).naturality g
  have e3 := (Functor.isoWhiskerRight (baseChangeIsoExtendScalars A A')
    (ModuleCat.restrictScalars (modelRingMap R A R' A' R₀))).hom.naturality g
  dsimp only [Functor.comp_map] at e2 e3
  rw [← whisker_exchange_assoc]
  exact congrArg (fun t => _ ≫ t) (((reassoc_of% e2) _).trans (congrArg (fun t => _ ≫ t) e3))

/-- On the summand indexed by `(i₁, i₂, 0)`, the left-hand side of `modelMapX_tensor` is the
inverse of `bcTensorIso`, the component of the model map of `P ⊗ N` at `P^{i₁} ⊗_A N^{i₂}`, the
component of `extTensorIso`, and the inclusion of `(A' ⊗_A P^{i₁}) ⊗_{A'} (A' ⊗_A N^{i₂})`. -/
theorem modelTensor_lhs (P N : CochainComplex (ModuleCat.{u} A) ℤ) (i₁ i₂ : ℤ)
    (h' : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (i₁ + i₂, 0) = i₁ + i₂) :
    (HomologicalComplex.ιTensorObj
        (((baseChangeFunctor A B₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
        (((baseChangeFunctor A B₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj N)
        i₁ i₂ (i₁ + i₂) rfl ▷
          (((baseChangeFunctor R₀ B₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj F).X 0) ≫
      HomologicalComplex.ιTensorObj
        ((((baseChangeFunctor A B₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ⊗
          (((baseChangeFunctor A B₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj N))
        (((baseChangeFunctor R₀ B₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj F)
        (i₁ + i₂) 0 (i₁ + i₂) h' ≫
      ((bcComplexTensorIso A B₀ P N).inv ▷
        ((baseChangeFunctor R₀ B₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj F).f (i₁ + i₂) ≫
      (modelMapX (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) ε (P ⊗ N)).f (i₁ + i₂) ≫
      (((ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (extTensorIso P N).hom).f (i₁ + i₂) =
    ((bcTensorIso A B₀ (P.X i₁) (N.X i₂)).inv ▷
        (((baseChangeFunctor R₀ B₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj F).X 0 ≫
      (baseChangeFunctor A B₀).obj ((P.X i₁) ⊗ (N.X i₂)) ◁ modelUnitComponent F ε ≫
      (modelTermMap (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀)).app ((P.X i₁) ⊗ (N.X i₂)) ≫
      (Functor.isoWhiskerRight (baseChangeIsoExtendScalars A A')
        (ModuleCat.restrictScalars (modelRingMap R A R' A' R₀))).hom.app ((P.X i₁) ⊗ (N.X i₂)) ≫
      (ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).map
        ((baseChangeIsoExtendScalars A A').inv.app ((P.X i₁) ⊗ (N.X i₂)) ≫
          (bcTensorIso A A' (P.X i₁) (N.X i₂)).hom ≫
          ((baseChangeFunctor A A').obj (P.X i₁) ◁
            (baseChangeIsoExtendScalars A A').hom.app (N.X i₂)))) ≫
      (ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).map
        (HomologicalComplex.ιTensorObj
          (((baseChangeFunctor A A').mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
          (((ModuleCat.extendScalars (algebraMap A A')).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj N) i₁ i₂ (i₁ + i₂) rfl) := by
  rw [HomologicalComplex.Monoidal.ι_whiskerRight_assoc, ← comp_whiskerRight_assoc,
    ι_bcComplexTensorIso_inv]
  have hι := ι_modelMapX (R := R) (A := A) (R' := R') (A' := A') F ε (P ⊗ N) (i₁ + i₂) h'
  rw [comp_whiskerRight, Category.assoc, reassoc_of% hι]
  simp only [Category.assoc]
  rw [reassoc_of% (modelUnit_naturality (R := R) (A' := A') F ε (Y := (P ⊗ N).X (i₁ + i₂))
    (HomologicalComplex.ιMapBifunctor P N
    (curriedTensor (ModuleCat.{u} A)) (ComplexShape.up ℤ) i₁ i₂ (i₁ + i₂) rfl))]
  rw [Functor.mapHomologicalComplex_map_f]
  have e4 : (ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).map
        ((ModuleCat.extendScalars (algebraMap A A')).map (HomologicalComplex.ιMapBifunctor P N
          (curriedTensor (ModuleCat.{u} A)) (ComplexShape.up ℤ) i₁ i₂ (i₁ + i₂) rfl)) ≫
      (ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).map
        ((extTensorIso P N).hom.f (i₁ + i₂)) =
      (ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).map
        ((baseChangeIsoExtendScalars A A').inv.app ((P.X i₁) ⊗ (N.X i₂)) ≫
          (bcTensorIso A A' (P.X i₁) (N.X i₂)).hom ≫
          ((baseChangeFunctor A A').obj (P.X i₁) ◁
            (baseChangeIsoExtendScalars A A').hom.app (N.X i₂))) ≫
      (ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).map
        (HomologicalComplex.ιTensorObj
          (((baseChangeFunctor A A').mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
          (((ModuleCat.extendScalars (algebraMap A A')).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj N) i₁ i₂ (i₁ + i₂) rfl) := by
    rw [← Functor.map_comp, ← Functor.map_comp, ι_extTensorIso_hom]
    exact congrArg _ (comp_assoc_helper _ _ _ _).symm
  exact cancel_tail_helper _ _ _ _ _ _ _ _ e4

/-- For `A`-modules `X` and `Y`, the model map component at `X ⊗_A Y`, composed with the inverse
of `bcTensorIso` and with `A' ⊗_A (X ⊗_A Y) ≅ (A' ⊗_A X) ⊗_{A'} (A' ⊗_A Y)`, equals `X`
tensored with the model map component at `Y`, followed by the inverse of `projectionIso`. -/
theorem modelTensor_bracket (X Y : ModuleCat.{u} A) :
    (bcTensorIso A B₀ X Y).inv ▷
        (((baseChangeFunctor R₀ B₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj F).X 0 ≫
      (baseChangeFunctor A B₀).obj (X ⊗ Y) ◁ modelUnitComponent F ε ≫
      (modelTermMap (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀)).app (X ⊗ Y) ≫
      (Functor.isoWhiskerRight (baseChangeIsoExtendScalars A A')
        (ModuleCat.restrictScalars (modelRingMap R A R' A' R₀))).hom.app (X ⊗ Y) ≫
      (ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).map
        ((baseChangeIsoExtendScalars A A').inv.app (X ⊗ Y) ≫
          (bcTensorIso A A' X Y).hom ≫
          ((baseChangeFunctor A A').obj X ◁ (baseChangeIsoExtendScalars A A').hom.app Y)) =
    (α_ ((baseChangeFunctor A B₀).obj X) ((baseChangeFunctor A B₀).obj Y)
        ((((baseChangeFunctor R₀ B₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj F).X 0)).hom ≫
      ((baseChangeFunctor A B₀).obj X ◁
        ((baseChangeFunctor A B₀).obj Y ◁ modelUnitComponent F ε ≫
          (modelTermMap (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀)).app Y ≫
          (Functor.isoWhiskerRight (baseChangeIsoExtendScalars A A')
            (ModuleCat.restrictScalars (modelRingMap R A R' A' R₀))).hom.app Y)) ≫
      (projectionIso (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) X
        ((ModuleCat.extendScalars (algebraMap A A')).obj Y)).inv := by
  have hc : (Functor.isoWhiskerRight (baseChangeIsoExtendScalars A A')
        (ModuleCat.restrictScalars (modelRingMap R A R' A' R₀))).hom.app (X ⊗ Y) ≫
      (ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).map
        ((baseChangeIsoExtendScalars A A').inv.app (X ⊗ Y) ≫
          (bcTensorIso A A' X Y).hom ≫
          ((baseChangeFunctor A A').obj X ◁ (baseChangeIsoExtendScalars A A').hom.app Y)) =
      (ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).map
          ((bcTensorIso A A' X Y).hom ≫
          ((baseChangeFunctor A A').obj X ◁ (baseChangeIsoExtendScalars A A').hom.app Y)) := by
    rw [Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, ← Functor.map_comp,
      Iso.hom_inv_id_app_assoc]
  rw [hc]
  have h1 : ∀ (x : X) (y : Y), (bcTensorIso A B₀ X Y).inv.hom
      (((1 : B₀) ⊗ₜ[A] x) ⊗ₜ[B₀] ((1 : B₀) ⊗ₜ[A] y)) = (1 : B₀) ⊗ₜ[A] (x ⊗ₜ[A] y) := by
    intro x y
    exact (bcTensorEquiv A B₀ X Y).symm_apply_apply ((1 : B₀) ⊗ₜ[A] (x ⊗ₜ[A] y))
  refine ModuleCat.hom_ext (tensorThree_linearMap_ext fun x y w => ?_)
  refine Eq.trans (congrArg (fun t => ((baseChangeFunctor A B₀).obj (X ⊗ Y) ◁
      modelUnitComponent F ε ≫
      (modelTermMap (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀)).app (X ⊗ Y) ≫
      (ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).map
          ((bcTensorIso A A' X Y).hom ≫
          ((baseChangeFunctor A A').obj X ◁ (baseChangeIsoExtendScalars A A').hom.app Y))).hom
      (t ⊗ₜ[B₀] ((1 : B₀) ⊗ₜ[R₀] w))) (h1 x y)) ?_
  refine Eq.trans (b := ((modelUnitAddHom (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀)
      ((1 : B₀) ⊗ₜ[R₀] augmentation F ε w) * modelRingMap R A R' A' R₀ 1) ⊗ₜ[A] x) ⊗ₜ[A']
      ((baseChangeIsoExtendScalars A A').hom.app Y).hom ((1 : A') ⊗ₜ[A] y)) rfl ?_
  refine Eq.trans (b := ((1 : A') ⊗ₜ[A] x) ⊗ₜ[A'] (modelRingMap R A R' A' R₀ 1 •
      ((baseChangeIsoExtendScalars A A').hom.app Y).hom
        (modelUnitAddHom (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀)
          ((1 : B₀) ⊗ₜ[R₀] augmentation F ε w) • (modelRingMap R A R' A' R₀ 1 ⊗ₜ[A] y)))) ?_ rfl
  rw [map_one, one_smul, mul_one]
  refine Eq.trans ?_ (congrArg (fun t => ((1 : A') ⊗ₜ[A] x) ⊗ₜ[A'] t)
    (((baseChangeIsoExtendScalars A A').hom.app Y).hom.map_smul _ _).symm)
  rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- **The model of a tensor product**: the model map of `P ⊗ N` is `P ⊗` the model map of
`N`, up to the base change and projection isomorphisms. -/
theorem modelMapX_tensor (P N : CochainComplex (ModuleCat.{u} A) ℤ) :
    ((bcComplexTensorIso A B₀ P N).inv ▷
        ((baseChangeFunctor R₀ B₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj F) ≫
      modelMapX (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) ε (P ⊗ N) ≫
      ((ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (extTensorIso P N).hom =
    (α_ _ _ _).hom ≫
      (((baseChangeFunctor A B₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj P ◁
        modelMapX (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) ε N) ≫
      (projectionComplexIso' P (((ModuleCat.extendScalars (algebraMap A A')).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj N)).inv := by
  ext n : 1
  apply HomologicalComplex.mapBifunctor₁₂.hom_ext
  intro i₁ i₂ i₃ h
  have h' : i₁ + i₂ + i₃ = n := h
  have h₂₃ : i₁ + (i₂ + i₃) = n := by rw [← h', add_assoc]
  simp only [HomologicalComplex.comp_f]
  rw [HomologicalComplex.Monoidal.ι₁₂_associator_hom_assoc,
    HomologicalComplex.mapBifunctor₂₃.ι_eq _ _ _ _ _ _ _ _ i₁ i₂ i₃ (i₂ + i₃) n rfl h₂₃,
    HomologicalComplex.mapBifunctor₁₂.ι_eq _ _ _ _ _ _ _ i₁ i₂ i₃ (i₁ + i₂) n rfl h']
  by_cases h₃ : i₃ = 0
  · subst h₃
    obtain rfl : n = i₁ + i₂ := by rw [← h', add_zero]
    refine (modelTensor_lhs (R := R) (A' := A') F ε P N i₁ i₂ h').trans (Eq.trans ?_
      (modelTensor_rhs (R := R) (A' := A') F ε P N i₁ i₂ (i₂ + 0) (i₁ + i₂) rfl h₂₃ rfl).symm)
    exact congrArg (fun t => t ≫ _) (modelTensor_bracket (R := R) (A' := A') F ε (P.X i₁) (N.X i₂))
  · have hL : HomologicalComplex.ιMapBifunctor
          (HomologicalComplex.mapBifunctor
            (((baseChangeFunctor A B₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
            (((baseChangeFunctor A B₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj N)
            (curriedTensor (ModuleCat.{u} B₀)) (ComplexShape.up ℤ))
          (((baseChangeFunctor R₀ B₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj F)
          (curriedTensor (ModuleCat.{u} B₀)) (ComplexShape.up ℤ) (i₁ + i₂) i₃ n h' ≫
        ((bcComplexTensorIso A B₀ P N).inv ▷
          ((baseChangeFunctor R₀ B₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj F).f n ≫
        (modelMapX (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) ε (P ⊗ N)).f n = 0 := by
      rw [HomologicalComplex.Monoidal.ι_whiskerRight_assoc,
        ι_modelMapX_eq_zero F ε (P ⊗ N) _ i₃ n h₃ h', comp_zero]
    rw [Category.assoc, reassoc_of% hL, zero_comp, comp_zero]
    have hR₀ : (((baseChangeFunctor A B₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj P).X i₁ ◁
          HomologicalComplex.ιTensorObj
            (((baseChangeFunctor A B₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj N)
            (((baseChangeFunctor R₀ B₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj F)
            i₂ i₃ (i₂ + i₃) rfl ≫
        HomologicalComplex.ιTensorObj
            (((baseChangeFunctor A B₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
            (modelComplex A F N) i₁ (i₂ + i₃) n (by rw [← h', add_assoc]) ≫
        (((baseChangeFunctor A B₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj P ◁
          modelMapX (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) ε N).f n = 0 := by
      rw [HomologicalComplex.Monoidal.ι_whiskerLeft, ← MonoidalCategory.whiskerLeft_comp_assoc]
      rw [show HomologicalComplex.ιTensorObj
            (((baseChangeFunctor A B₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj N)
            (((baseChangeFunctor R₀ B₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj F)
            i₂ i₃ (i₂ + i₃) rfl ≫
          (modelMapX (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) ε N).f (i₂ + i₃) = 0 from
        ι_modelMapX_eq_zero F ε N i₂ i₃ (i₂ + i₃) h₃ rfl]
      rw [MonoidalPreadditive.whiskerLeft_zero, zero_comp]
    rw [Category.assoc]
    refine Eq.symm ((congrArg (fun t => (α_ _ _ _).hom ≫ t)
      (((reassoc_of% hR₀) ((projectionComplexIso' P
        (((ModuleCat.extendScalars (algebraMap A A')).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj N)).inv.f n)).trans zero_comp)).trans comp_zero)

end TensorModel

end RingTheory.TorIndependence
