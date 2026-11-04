module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.TensorBaseChange.PolynomialModel

/-!
# The model complex of a square of rings

For a square of rings `R → A`, `R → R'`, `A → A'`, `R' → A'` and an `R`-algebra `R₀` over `R'`,
write `B₀ = A ⊗_R R₀`.  This file defines the ring map `B₀ ⟶ A'`, the termwise map

`(B₀ ⊗_A X) ⊗_{B₀} (B₀ ⊗_{R₀} R') ⟶ A' ⊗_A X`

and its assembly on complexes of `A`-modules: the model through which the map of Stacks 0DJ7 is
computed.

## Main definitions

* `RingTheory.TorIndependence.modelRingMap`: the ring map `A ⊗_R R₀ ⟶ A'`.
* `RingTheory.TorIndependence.modelComplex`: the complex `(B₀ ⊗_A M) ⊗_{B₀} (B₀ ⊗_{R₀} F)`.
* `RingTheory.TorIndependence.modelMap`: its map to `A' ⊗_A M` induced by `F ⟶ R'`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct ChangeOfRings

universe u

namespace RingTheory.TorIndependence

variable {R A R' A' R₀ : Type u}
  [CommRing R] [CommRing A] [CommRing R'] [CommRing A'] [CommRing R₀]
  [Algebra R A] [Algebra R R'] [Algebra R A'] [Algebra A A'] [Algebra R' A']
  [IsScalarTower R A A'] [IsScalarTower R R' A']
  [Algebra R R₀] [Algebra R₀ R'] [IsScalarTower R R₀ R']

attribute [local instance] Algebra.TensorProduct.rightAlgebra

local notation "B₀" => A ⊗[R] R₀

variable (R A R' A' R₀) in
/-- The ring map `A ⊗_R R₀ ⟶ A'` of the square, through `A ⊗_R R'`. -/
def modelRingMap : B₀ →+* A' :=
  (baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A')).comp
    (Algebra.TensorProduct.map (AlgHom.id R A) (IsScalarTower.toAlgHom R R₀ R')).toRingHom

/-- The ring map `modelRingMap` sends `a ⊗ r` to `a · r` in `A'`. -/
theorem modelRingMap_tmul (a : A) (r : R₀) :
    modelRingMap R A R' A' R₀ (a ⊗ₜ[R] r) =
      algebraMap A A' a * algebraMap R' A' (algebraMap R₀ R' r) := rfl

/-- The additive map `(A ⊗_R R₀) ⊗_{R₀} R' ⟶ A'`, `b ⊗ s ↦ k₀(b) s`. -/
def modelUnitAddHom : (B₀ ⊗[R₀] R') →+ A' :=
  letI : Module R₀ A' := Module.compHom A' ((algebraMap R' A').comp (algebraMap R₀ R'))
  ((TensorProduct.lift
    (LinearMap.mk₂ R₀ (fun b s => modelRingMap R A R' A' R₀ b * algebraMap R' A' s)
      (fun b b' s => by rw [map_add, add_mul])
      (fun r b s => by
        change modelRingMap R A R' A' R₀ ((1 ⊗ₜ[R] r) * b) * algebraMap R' A' s =
          algebraMap R' A' (algebraMap R₀ R' r) * (modelRingMap R A R' A' R₀ b * algebraMap R' A' s)
        rw [map_mul, modelRingMap_tmul, map_one, one_mul, mul_assoc])
      (fun b s s' => by rw [map_add, mul_add])
      (fun r b s => by
        change modelRingMap R A R' A' R₀ b * algebraMap R' A' (r • s) =
          algebraMap R' A' (algebraMap R₀ R' r) * (modelRingMap R A R' A' R₀ b * algebraMap R' A' s)
        rw [Algebra.smul_def, map_mul]
        ring)) : B₀ ⊗[R₀] R' →ₗ[R₀] A')).toAddMonoidHom

/-- The map `modelUnitAddHom` sends `b ⊗ s` to `modelRingMap b · s`. -/
theorem modelUnitAddHom_tmul (b : B₀) (s : R') :
    modelUnitAddHom (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) (b ⊗ₜ[R₀] s) =
      modelRingMap R A R' A' R₀ b * algebraMap R' A' s := rfl

/-- The ring map `A ⊗_R R₀ ⟶ A'`, read as a map of `A`-modules. -/
def modelRingMapA : B₀ →ₗ[A] A' where
  toFun := modelRingMap R A R' A' R₀
  map_add' := map_add _
  map_smul' a b := by
    change modelRingMap R A R' A' R₀ (a • b) = a • modelRingMap R A R' A' R₀ b
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, Algebra.TensorProduct.algebraMap_apply,
      modelRingMap_tmul, map_one, map_one, mul_one]
    rfl

/-- The `A`-linear map `modelRingMapA` agrees with `modelRingMap`. -/
theorem modelRingMapA_apply (b : B₀) :
    modelRingMapA (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) b =
      modelRingMap R A R' A' R₀ b := rfl

/-- `B₀ ⊗_A X ⟶ A' ⊗_A X`, `c ⊗ x ↦ k₀(c) ⊗ x`. -/
abbrev modelExtendMap (X : Type u) [AddCommGroup X] [Module A X] : B₀ ⊗[A] X →ₗ[A] A' ⊗[A] X :=
  LinearMap.rTensor X (modelRingMapA (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀))

/-- The map `modelExtendMap` is semilinear along `modelRingMap`: it sends `b • m` to
`modelRingMap b • modelExtendMap m`. -/
theorem modelExtendMap_smul (X : Type u) [AddCommGroup X] [Module A X] (b : B₀)
    (m : B₀ ⊗[A] X) :
    modelExtendMap (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) X (b • m) =
      modelRingMap R A R' A' R₀ b •
        modelExtendMap (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) X m := by
  refine TensorProduct.induction_on m ?_ ?_ ?_
  · rw [smul_zero, map_zero, smul_zero]
  · intro c x
    rw [TensorProduct.smul_tmul', LinearMap.rTensor_tmul, LinearMap.rTensor_tmul,
      TensorProduct.smul_tmul', modelRingMapA_apply, modelRingMapA_apply, smul_eq_mul, smul_eq_mul,
      map_mul]
  · intro m m' hm hm'
    rw [smul_add, map_add, hm, hm', map_add, smul_add]

/-- The map `modelUnitAddHom` sends `b • w` to `modelRingMap b * modelUnitAddHom w`. -/
theorem modelUnitAddHom_smul (b : B₀) (w : B₀ ⊗[R₀] R') :
    modelUnitAddHom (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) (b • w) =
      modelRingMap R A R' A' R₀ b * modelUnitAddHom w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add t t' ht ht' => rw [smul_add, map_add, ht, ht', map_add, mul_add]
  | tmul b' s =>
    rw [TensorProduct.smul_tmul', modelUnitAddHom_tmul, modelUnitAddHom_tmul, smul_eq_mul,
      map_mul, mul_assoc]

section Term

variable (X : Type u) [AddCommGroup X] [Module A X]

/-- The degreewise map of the model, `(B₀ ⊗_A X) ⊗_{B₀} (B₀ ⊗_{R₀} R') ⟶ A' ⊗_A X`,
`(c ⊗ x) ⊗ w ↦ ε(w) k₀(c) ⊗ x` with `ε(b ⊗ s) = k₀(b) s`, additively. -/
def modelTermAdd : (B₀ ⊗[A] X) ⊗[B₀] (B₀ ⊗[R₀] R') →+ A' ⊗[A] X :=
  letI : Module B₀ (A' ⊗[A] X) := Module.compHom _ (modelRingMap R A R' A' R₀)
  ((TensorProduct.lift
    (LinearMap.mk₂ B₀
      (fun (m : B₀ ⊗[A] X) (w : B₀ ⊗[R₀] R') =>
        modelUnitAddHom (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) w •
          modelExtendMap (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) X m)
      (fun m m' w => by rw [map_add, smul_add])
      (fun b m w => by
        change modelUnitAddHom (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) w •
            modelExtendMap (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) X (b • m) =
          modelRingMap R A R' A' R₀ b • (modelUnitAddHom (R := R) (A := A) (R' := R') (A' := A')
            (R₀ := R₀) w • modelExtendMap (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) X m)
        rw [modelExtendMap_smul, smul_comm])
      (fun m w w' => by rw [map_add, add_smul])
      (fun b m w => by
        change modelUnitAddHom (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) (b • w) •
            modelExtendMap (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) X m =
          modelRingMap R A R' A' R₀ b • (modelUnitAddHom (R := R) (A := A) (R' := R') (A' := A')
            (R₀ := R₀) w • modelExtendMap (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) X m)
        rw [modelUnitAddHom_smul, mul_smul])) :
    (B₀ ⊗[A] X) ⊗[B₀] (B₀ ⊗[R₀] R') →ₗ[B₀] A' ⊗[A] X)).toAddMonoidHom

/-- The map `modelTermAdd` sends `(c ⊗ x) ⊗ w` to `(modelUnitAddHom w * modelRingMap c) ⊗ x`. -/
theorem modelTermAdd_tmul (c : B₀) (x : X) (w : B₀ ⊗[R₀] R') :
    modelTermAdd (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) X ((c ⊗ₜ[A] x) ⊗ₜ[B₀] w) =
      (modelUnitAddHom (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) w *
        modelRingMap R A R' A' R₀ c) ⊗ₜ[A] x := by
  show modelUnitAddHom (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) w •
    ((modelRingMap R A R' A' R₀ c) ⊗ₜ[A] x) = _
  rw [TensorProduct.smul_tmul', smul_eq_mul]

/-- The map `modelTermAdd` sends `b • t` to `modelRingMap b • modelTermAdd t`. -/
theorem modelTermAdd_smul (b : B₀) (t : (B₀ ⊗[A] X) ⊗[B₀] (B₀ ⊗[R₀] R')) :
    modelTermAdd (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) X (b • t) =
      modelRingMap R A R' A' R₀ b • modelTermAdd (R := R) (A := A) (R' := R') (A' := A')
        (R₀ := R₀) X t := by
  let : Module B₀ (A' ⊗[A] X) := Module.compHom _ (modelRingMap R A R' A' R₀)
  exact (TensorProduct.lift _).map_smul b t

end Term

/-- The map `modelTermAdd` is natural in the `A`-module: it commutes with the maps induced by an
`A`-linear map `f : X →ₗ[A] Y`. -/
theorem modelTermAdd_naturality {X Y : Type u} [AddCommGroup X] [Module A X]
    [AddCommGroup Y] [Module A Y] (f : X →ₗ[A] Y) (t : (B₀ ⊗[A] X) ⊗[B₀] (B₀ ⊗[R₀] R')) :
    modelTermAdd (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) Y
        (LinearMap.rTensor _ (f.baseChange B₀) t) =
      f.baseChange A' (modelTermAdd (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) X t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add t t' ht ht' => simp only [map_add, ht, ht']
  | tmul m w =>
    induction m using TensorProduct.induction_on with
    | zero => simp only [TensorProduct.zero_tmul, map_zero]
    | add m m' hm hm' => simp only [TensorProduct.add_tmul, map_add, hm, hm']
    | tmul c x =>
      rw [LinearMap.rTensor_tmul, LinearMap.baseChange_tmul, modelTermAdd_tmul, modelTermAdd_tmul,
        LinearMap.baseChange_tmul]

/-- The degreewise map of the model, as a natural transformation of functors to
`A ⊗_R R₀`-modules. -/
def modelTermMap : baseChangeFunctor A B₀ ⋙
      StacksDraft.TorAmplitude.tensorModuleRight (ModuleCat.of B₀ (B₀ ⊗[R₀] R')) ⟶
    baseChangeFunctor A A' ⋙ ModuleCat.restrictScalars (modelRingMap R A R' A' R₀) where
  app X := ModuleCat.ofHom (X := (B₀ ⊗[A] X) ⊗[B₀] (B₀ ⊗[R₀] R'))
      (Y := (ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).obj
        (ModuleCat.of A' (A' ⊗[A] X)))
      { toFun := modelTermAdd (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) X
        map_add' := map_add _
        map_smul' := modelTermAdd_smul X }
  naturality {X Y} f := by
    ext t
    exact modelTermAdd_naturality f.hom t

section Complex

variable (F : CochainComplex (ModuleCat.{u} R₀) ℤ)
  (ε : F ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} R₀) 0).obj (ModuleCat.of R₀ R'))

variable (A) in
/-- The model complex `(B₀ ⊗_A M) ⊗_{B₀} (B₀ ⊗_{R₀} F)` of `B₀`-modules. -/
abbrev modelComplex (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    CochainComplex (ModuleCat.{u} B₀) ℤ :=
  ((baseChangeFunctor A B₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj M ⊗
    ((baseChangeFunctor R₀ B₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj F

/-- The map from the model complex to `A' ⊗_A M`, read over `B₀`, induced by `ε`. -/
def modelMap (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    modelComplex A F M ⟶
      ((baseChangeFunctor A A' ⋙
          ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj M :=
  ((baseChangeFunctor A B₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj M ◁
      (((baseChangeFunctor R₀ B₀).mapHomologicalComplex (ComplexShape.up ℤ)).map ε ≫
        (HomologicalComplex.singleMapHomologicalComplex (baseChangeFunctor R₀ B₀)
          (ComplexShape.up ℤ) 0).hom.app (ModuleCat.of R₀ R')) ≫
    (tensorSingleIso
      ((baseChangeFunctor R₀ B₀).obj (ModuleCat.of R₀ R'))).inv.app
        (((baseChangeFunctor A B₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) ≫
    (NatTrans.mapHomologicalComplex (modelTermMap (R := R) (A := A) (R' := R') (A' := A')
      (R₀ := R₀)) (ComplexShape.up ℤ)).app M

end Complex

end RingTheory.TorIndependence
