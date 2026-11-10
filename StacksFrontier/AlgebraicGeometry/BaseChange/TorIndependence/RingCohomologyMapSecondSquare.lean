module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.IsBaseChangeDescent
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.RingCohomologyMapFirstSquare
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.RingCohomologyMapFlat
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.FlatBaseChangeHomology

/-!
# The base-change map of Stacks 0DJ7 under a flat change of square

Let `(R, A, R', A') → (R₁, A₁, R₁', A₁')` be a morphism of commutative squares of rings with
`R₁` flat over `R`, `A₁` flat over `A`, `R₁'` flat over `R₁ ⊗_R R'` and `A₁'` flat over `A'`.
If the base-change map of Stacks 0DJ7 of the first square at `K`, `K'`, `φ` is an isomorphism,
so is the one of the second square at `K ⊗ᴸ_A A₁`, `K' ⊗ᴸ_{A'} A₁'` and the induced morphism; for
a family of second squares covering `Spec A'` the converse holds.

## Main definitions

* `RingTheory.TorIndependence.secondSquareTensorMap`: the ring map
  `A ⊗_R R' → A₁ ⊗_{R₁} R₁'`.
* `RingTheory.TorIndependence.secondSquareLinearMap`: the map induced on cohomology, as a
  semilinear map along it.
* `RingTheory.TorIndependence.middleModule`: the `A₁ ⊗_R R'`-module
  `Hⁿ((K ⊗ᴸ_A A₁)|_R ⊗ᴸ_R R')` through which that map factors.

## Main results

* `RingTheory.TorIndependence.isBaseChange_secondSquareLinearMap`: the map is a base change.
* `RingTheory.TorIndependence.isIso_ringBaseChangeCohomologyMap_secondSquare`: the base-change
  map of the second square is invertible when that of the first is.
* `RingTheory.TorIndependence.isIso_ringBaseChangeCohomologyMap_iff_forall_secondSquare`: the
  converse for a family covering `Spec A'`.

## References

* [Stacks Project, Tag 0DJ7](https://stacks.math.columbia.edu/tag/0DJ7)
* [Stacks Project, Tag 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace RingTheory.TorIndependence

attribute [local instance] HasDerivedCategory.standard

/-! ### The action of the second square's algebra -/

section RestrictedAction

variable {R R' P : Type u} [CommRing R] [CommRing R'] [CommRing P] [Algebra R R']

/-- **The action of `P` on `Hⁿ(F(X) ⊗ᴸ_R R')`** for an additive functor `F : D(P) ⥤ D(R)`: an
element of `P` acts by derived base change of `F` of multiplication by it on `X`. -/
def restrictedCohomologyAction
    (F : DerivedCategory (ModuleCat.{u} P) ⥤ DerivedCategory (ModuleCat.{u} R)) [F.Additive]
    (X : DerivedCategory (ModuleCat.{u} P)) (n : ℤ) :
    P →+* Module.End R'
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).obj
        ((dext (algebraMap R R')).obj (F.obj X))) :=
  let G := F ⋙ dext (algebraMap R R') ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} R') n
  { toFun := fun p => (G.map (p • (𝟙 X))).hom
    map_one' := by
      rw [one_smul, G.map_id]
      rfl
    map_mul' := fun a b => by
      have hab : (a * b) • (𝟙 X) = (b • (𝟙 X)) ≫ (a • (𝟙 X)) := by
        simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp, smul_smul]
      rw [hab, G.map_comp]
      rfl
    map_zero' := by
      rw [zero_smul, G.map_zero]
      rfl
    map_add' := fun a b => by
      rw [add_smul, G.map_add]
      rfl }

/-- The action of `p` is the map on cohomology induced by `p • 𝟙 X`. -/
theorem restrictedCohomologyAction_apply
    (F : DerivedCategory (ModuleCat.{u} P) ⥤ DerivedCategory (ModuleCat.{u} R)) [F.Additive]
    (X : DerivedCategory (ModuleCat.{u} P)) (n : ℤ) (p : P)
    (m : (DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).obj
        ((dext (algebraMap R R')).obj (F.obj X))) :
    restrictedCohomologyAction (R' := R') F X n p m =
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map
        ((dext (algebraMap R R')).map (F.map (p • 𝟙 X)))).hom m :=
  rfl

end RestrictedAction

/-- In `A ⊗_R S` a pure tensor is the product of the two inclusions. -/
private theorem tmul_eq_includeLeft_mul_includeRight {R A S : Type u} [CommRing R] [CommRing A]
    [CommRing S] [Algebra R A] [Algebra R S] (a : A) (s : S) :
    (a ⊗ₜ[R] s : A ⊗[R] S) =
      (Algebra.TensorProduct.includeLeft (R := R) (S := R) a : A ⊗[R] S) *
        Algebra.TensorProduct.includeRight s := by
  change a ⊗ₜ[R] s = (a ⊗ₜ[R] (1 : S)) * ((1 : A) ⊗ₜ[R] s)
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

section SecondSquare

variable {R A R' A' R₁ A₁ R₁' A₁' : Type u}
  [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
  [CommRing R₁] [CommRing A₁] [CommRing R₁'] [CommRing A₁']
  [Algebra R A] [Algebra R R'] [Algebra R A'] [Algebra A A'] [Algebra R' A']
  [IsScalarTower R A A'] [IsScalarTower R R' A']
  [Algebra R₁ A₁] [Algebra R₁ R₁'] [Algebra R₁ A₁'] [Algebra A₁ A₁'] [Algebra R₁' A₁']
  [IsScalarTower R₁ A₁ A₁'] [IsScalarTower R₁ R₁' A₁']
  [Algebra R R₁] [Algebra A A₁] [Algebra R' R₁'] [Algebra A' A₁']
  [Algebra R A₁] [IsScalarTower R A A₁] [IsScalarTower R R₁ A₁]
  [Algebra R R₁'] [IsScalarTower R R' R₁'] [IsScalarTower R R₁ R₁']
  [Algebra A A₁'] [IsScalarTower A A' A₁'] [IsScalarTower A A₁ A₁']
  [Algebra R' A₁'] [IsScalarTower R' A' A₁'] [IsScalarTower R' R₁' A₁']

/-- **The ring map `A ⊗_R R' → A₁ ⊗_{R₁} R₁'`** induced by a morphism of commutative squares. -/
def secondSquareTensorMap : A ⊗[R] R' →+* A₁ ⊗[R₁] R₁' :=
  (Algebra.TensorProduct.lift
    ({ toRingHom := (Algebra.TensorProduct.includeLeftRingHom (R := R₁)).comp (algebraMap A A₁)
       commutes' := fun r => by
        change (algebraMap A A₁ (algebraMap R A r)) ⊗ₜ[R₁] (1 : R₁') =
          algebraMap R (A₁ ⊗[R₁] R₁') r
        rw [← IsScalarTower.algebraMap_apply]
        rfl } : A →ₐ[R] A₁ ⊗[R₁] R₁')
    ({ toRingHom := (Algebra.TensorProduct.includeRight (R := R₁) (A := A₁)).toRingHom.comp
          (algebraMap R' R₁')
       commutes' := fun r => by
        change (1 : A₁) ⊗ₜ[R₁] (algebraMap R' R₁' (algebraMap R R' r)) =
          algebraMap R A₁ r ⊗ₜ[R₁] (1 : R₁')
        rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R R₁ R₁',
          IsScalarTower.algebraMap_apply R R₁ A₁,
          Algebra.algebraMap_eq_smul_one (A := R₁') (algebraMap R R₁ r),
          Algebra.algebraMap_eq_smul_one (A := A₁) (algebraMap R R₁ r)]
        exact (TensorProduct.smul_tmul (algebraMap R R₁ r) (1 : A₁) (1 : R₁')).symm } :
          R' →ₐ[R] A₁ ⊗[R₁] R₁')
    (fun _ _ => Commute.all _ _)).toRingHom

omit [Algebra R A'] [Algebra A A'] [Algebra R' A'] [IsScalarTower R A A'] [IsScalarTower R R' A']
  [Algebra R₁ A₁'] [Algebra A₁ A₁'] [Algebra R₁' A₁'] [IsScalarTower R₁ A₁ A₁']
  [IsScalarTower R₁ R₁' A₁'] [Algebra A' A₁'] [Algebra A A₁'] [IsScalarTower A A' A₁']
  [IsScalarTower A A₁ A₁'] [Algebra R' A₁'] [IsScalarTower R' A' A₁'] [IsScalarTower R' R₁' A₁'] in
/-- On pure tensors, `secondSquareTensorMap` is `a ⊗ r ↦ a ⊗ r`, read through `A → A₁` and
`R' → R₁'`. -/
theorem secondSquareTensorMap_tmul (a : A) (r : R') :
    secondSquareTensorMap (R := R) (A := A) (R' := R') (R₁ := R₁) (A₁ := A₁) (R₁' := R₁')
        (a ⊗ₜ[R] r) =
      algebraMap A A₁ a ⊗ₜ[R₁] algebraMap R' R₁' r := by
  simp only [secondSquareTensorMap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.lift_tmul]
  change (algebraMap A A₁ a ⊗ₜ[R₁] (1 : R₁')) * ((1 : A₁) ⊗ₜ[R₁] algebraMap R' R₁' r) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- The two ways around the cube from `A ⊗_R R'` to `A₁'` agree. -/
theorem baseChangeTensorRingMap_comp_secondSquareTensorMap :
    (baseChangeTensorRingMap (R := R₁) (A := A₁) (R' := R₁') (A' := A₁')).comp
        (secondSquareTensorMap (R := R) (A := A) (R' := R') (R₁ := R₁) (A₁ := A₁) (R₁' := R₁')) =
      (algebraMap A' A₁').comp
        (baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A')) := by
  refine RingHom.ext fun t => ?_
  induction t using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a r =>
    simp only [RingHom.comp_apply, secondSquareTensorMap_tmul, baseChangeTensorRingMap_tmul,
      map_mul]
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply A A' A₁', IsScalarTower.algebraMap_apply R' A' A₁']

/-- **The map induced on cohomology by a morphism of squares, as a semilinear map.**
`secondSquareHomologyMap` intertwines the action of `A ⊗_R R'` with that of `A₁ ⊗_{R₁} R₁'`
along `secondSquareTensorMap`. -/
theorem secondSquareHomologyMap_smul (K : DerivedCategory (ModuleCat.{u} A)) (n : ℤ)
    (t : A ⊗[R] R') (m : baseChangeCohomologyOverBase (R := R) (R' := R') K n) :
    letI := baseChangeCohomologyModule (R := R) (R' := R') K n
    letI := baseChangeCohomologyModule (R := R₁) (R' := R₁') ((dext (algebraMap A A₁)).obj K) n
    (show baseChangeCohomologyOverBase (R := R₁) (R' := R₁') ((dext (algebraMap A A₁)).obj K) n from
      (secondSquareHomologyMap (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) (R₁' := R₁') K n).hom
          (t • m)) =
      secondSquareTensorMap (R := R) (A := A) (R' := R') (R₁ := R₁) (A₁ := A₁) (R₁' := R₁') t •
        (show baseChangeCohomologyOverBase (R := R₁) (R' := R₁')
            ((dext (algebraMap A A₁)).obj K) n from
          (secondSquareHomologyMap (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) (R₁' := R₁')
            K n).hom m) := by
  let := baseChangeCohomologyModule (R := R) (R' := R') K n
  let := baseChangeCohomologyModule (R := R₁) (R' := R₁') ((dext (algebraMap A A₁)).obj K) n
  let H := baseChangeCohomologyOverBase (R := R) (R' := R') K n
  let H₁ := baseChangeCohomologyOverBase (R := R₁) (R' := R₁') ((dext (algebraMap A A₁)).obj K) n
  let θ : H → H₁ := fun m =>
      (secondSquareHomologyMap (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) (R₁' := R₁') K n).hom m
  have hadd : ∀ x y : H, θ (x + y) = θ x + θ y := fun x y =>
    (secondSquareHomologyMap (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) (R₁' := R₁')
      K n).hom.map_add x y
  have hR' : ∀ (r : R') (x : H), θ (r • x) = algebraMap R' R₁' r • θ x :=
    fun r x => (secondSquareHomologyMap (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) (R₁' := R₁')
      K n).hom.map_smul r x
  have hA : ∀ (a : A) (x : H), θ (baseChangeCohomologyAction (R := R) (R' := R') K n a x) =
      baseChangeCohomologyAction (R := R₁) (R' := R₁') ((dext (algebraMap A A₁)).obj K) n
        (algebraMap A A₁ a) (θ x) :=
    fun a x => secondSquareHomologyMap_action K n a x
  change θ (t • m) = secondSquareTensorMap (R := R) (A := A) (R' := R') (R₁ := R₁) (A₁ := A₁)
      (R₁' := R₁') t • θ m
  induction t using TensorProduct.inductionOn generalizing m with
  | add x y hx hy => rw [add_smul, hadd, hx, hy, map_add, add_smul]
  | tmul a r =>
    rw [secondSquareTensorMap_tmul, tmul_eq_includeLeft_mul_includeRight (R := R₁),
      tmul_eq_includeLeft_mul_includeRight (R := R), mul_smul, mul_smul,
      baseChangeCohomologyModule_includeLeft_smul, hA, baseChangeCohomologyModule_includeRight_smul,
      hR',
      baseChangeCohomologyModule_includeLeft_smul, baseChangeCohomologyModule_includeRight_smul]

/-- `secondSquareHomologyMap` as a linear map over `A ⊗_R R'`, which acts on the target through
`secondSquareTensorMap`. -/
def secondSquareLinearMap (K : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) :
    letI := baseChangeCohomologyModule (R := R) (R' := R') K n
    letI := baseChangeCohomologyModule (R := R₁) (R' := R₁') ((dext (algebraMap A A₁)).obj K) n
    letI : Module (A ⊗[R] R')
        (baseChangeCohomologyOverBase (R := R₁) (R' := R₁') ((dext (algebraMap A A₁)).obj K) n) :=
      Module.compHom _
          (secondSquareTensorMap (R := R) (A := A) (R' := R') (R₁ := R₁) (A₁ := A₁) (R₁' := R₁'))
    baseChangeCohomologyOverBase (R := R) (R' := R') K n →ₗ[A ⊗[R] R']
      baseChangeCohomologyOverBase (R := R₁) (R' := R₁') ((dext (algebraMap A A₁)).obj K) n :=
  letI := baseChangeCohomologyModule (R := R) (R' := R') K n
  letI := baseChangeCohomologyModule (R := R₁) (R' := R₁') ((dext (algebraMap A A₁)).obj K) n
  letI : Module (A ⊗[R] R')
      (baseChangeCohomologyOverBase (R := R₁) (R' := R₁') ((dext (algebraMap A A₁)).obj K) n) :=
    Module.compHom _
        (secondSquareTensorMap (R := R) (A := A) (R' := R') (R₁ := R₁) (A₁ := A₁) (R₁' := R₁'))
  { toFun := fun m =>
      (secondSquareHomologyMap (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) (R₁' := R₁') K n).hom m
    map_add' := fun x y =>
      (secondSquareHomologyMap (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) (R₁' := R₁')
        K n).hom.map_add x y
    map_smul' := fun t m => secondSquareHomologyMap_smul K n t m }

omit [Algebra R A] [IsScalarTower R A A₁] in
/-- `Hⁿ((K ⊗ᴸ_A A₁)|_R ⊗ᴸ_R R')`, the restriction to `R` taken through `R₁`. -/
abbrev middleCohomology (K : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) : ModuleCat.{u} R' :=
  baseChangeCohomologyOverBase (R := R) (A := R₁) (R' := R')
    ((ModuleCat.restrictScalars (algebraMap R₁ A₁)).mapDerivedCategory.obj
      ((dext (algebraMap A A₁)).obj K)) n

/-- The action of `A₁` on `Hⁿ((K ⊗ᴸ_A A₁)|_R ⊗ᴸ_R R')`, the restriction to `R` taken through
`R₁`. -/
abbrev middleAction (K : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) :
    A₁ →+* Module.End R' (middleCohomology (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) K n) :=
  restrictedCohomologyAction (R' := R')
    ((ModuleCat.restrictScalars (algebraMap R₁ A₁)).mapDerivedCategory ⋙
      (ModuleCat.restrictScalars (algebraMap R R₁)).mapDerivedCategory)
    ((dext (algebraMap A A₁)).obj K) n

omit [Algebra R A] [IsScalarTower R A A₁] [Algebra R A₁] [IsScalarTower R R₁ A₁] in
/-- On the image of `R₁`, the middle action is the action of `R₁` on the cohomology of the
derived base change of `(K ⊗ᴸ_A A₁)|_{R₁}`. -/
theorem middleAction_algebraMap₁ (K : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) (r : R₁) :
    middleAction (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) K n (algebraMap R₁ A₁ r) =
      baseChangeCohomologyAction (R := R) (A := R₁) (R' := R')
        ((ModuleCat.restrictScalars (algebraMap R₁ A₁)).mapDerivedCategory.obj
          ((dext (algebraMap A A₁)).obj K)) n r := by
  have h := Dualizing.FlatHomology.restrictScalars_mapDerivedCategory_map_smul_id.{u, u, u}
    (algebraMap R₁ A₁) r ((dext (algebraMap A A₁)).obj K)
  change ((DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map
      ((dext (algebraMap R R')).map
          ((ModuleCat.restrictScalars (algebraMap R R₁)).mapDerivedCategory.map
        ((ModuleCat.restrictScalars (algebraMap R₁ A₁)).mapDerivedCategory.map
          (algebraMap R₁ A₁ r • 𝟙 _))))).hom = _
  rw [h]
  rfl

omit [Algebra R A] [IsScalarTower R A A₁] in
/-- On the image of `R`, the middle action is multiplication through `R'`. -/
theorem middleAction_algebraMap (K : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) (r : R) :
    middleAction (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) K n (algebraMap R A₁ r) =
      algebraMap R R' r • 1 := by
  rw [IsScalarTower.algebraMap_apply R R₁ A₁, middleAction_algebraMap₁,
    baseChangeCohomologyAction_algebraMap]

omit [Algebra R A] [IsScalarTower R A A₁] in
/-- The `A₁ ⊗_R R'`-module structure on `Hⁿ((K ⊗ᴸ_A A₁)|_R ⊗ᴸ_R R')`, with its two restrictions. -/
def middleModuleData (K : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) :
    { M : Module (A₁ ⊗[R] R') (middleCohomology (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) K n) //
        letI := M
        (∀ (r : R') (m : middleCohomology (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) K n),
          (Algebra.TensorProduct.includeRight r : A₁ ⊗[R] R') • m = r • m) ∧
        (∀ (a : A₁) (m : middleCohomology (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) K n),
          (Algebra.TensorProduct.includeLeft (R := R) (S := R) a : A₁ ⊗[R] R') • m =
          middleAction (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) K n a m) } :=
  let H := middleCohomology (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) K n
  let ρ := middleAction (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) K n
  letI : Module R H := Module.compHom H (algebraMap R R')
  letI : IsScalarTower R R' H := IsScalarTower.of_compHom _ _ _
  letI : Module A₁ H := Module.compHom H ρ
  letI : IsScalarTower R A₁ H := ⟨fun r a m => by
    change ρ (r • a) m = algebraMap R R' r • ρ a m
    rw [Algebra.smul_def, map_mul, middleAction_algebraMap]
    rfl⟩
  letI : SMulCommClass A₁ R' H := ⟨fun a r m => (ρ a).map_smul r m⟩
  ⟨TensorProduct.Algebra.module,
    fun r m => by
      change (1 : A₁) • r • m = r • m
      exact one_smul _ _,
    fun a m => by
      change ρ a ((1 : R') • m) = ρ a m
      rw [one_smul]⟩

omit [Algebra R A] [IsScalarTower R A A₁] in
/-- **The `A₁ ⊗_R R'`-module structure on `Hⁿ((K ⊗ᴸ_A A₁)|_R ⊗ᴸ_R R')`.** -/
@[instance_reducible]
def middleModule (K : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) :
    Module (A₁ ⊗[R] R') (middleCohomology (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) K n) :=
  (middleModuleData (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) K n).1

/-- **The `A`-side part of the map induced by a morphism of squares**, on derived base changes:
`K|_R ⊗ᴸ_R R' ⟶ (K ⊗ᴸ_A A₁)|_R ⊗ᴸ_R R'`, the restriction to `R` taken through `R₁`. -/
abbrev middleDerivedMap (K : DerivedCategory (ModuleCat.{u} A)) :
    (dext (algebraMap R R')).obj
        ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj K) ⟶
      (dext (algebraMap R R')).obj
          ((ModuleCat.restrictScalars (algebraMap R R₁)).mapDerivedCategory.obj
        ((ModuleCat.restrictScalars (algebraMap R₁ A₁)).mapDerivedCategory.obj
          ((dext (algebraMap A A₁)).obj K))) :=
  (dext (algebraMap R R')).map
    ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.map
        ((totalDerivedExtensionScalarsAdjunction (algebraMap A A₁)).unit.app K) ≫
      (restrictSquareDerivedIso.{u, u, u, u, u} (algebraMap R A) (algebraMap R R₁)
        (algebraMap A A₁) (algebraMap R₁ A₁) squareRA₁).hom.app ((dext (algebraMap A A₁)).obj K))

/-- **The `A`-side part of the map induced by a morphism of squares**, on cohomology. -/
abbrev middleHomologyMap (K : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) :
    baseChangeCohomologyOverBase (R := R) (R' := R') K n ⟶
      middleCohomology (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) K n :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map
    (middleDerivedMap (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) K)

omit [Algebra R A'] [Algebra A A'] [Algebra R' A'] [IsScalarTower R A A'] [IsScalarTower R R' A']
  [Algebra R₁ A₁'] [Algebra A₁ A₁'] [Algebra R₁' A₁'] [IsScalarTower R₁ A₁ A₁']
  [IsScalarTower R₁ R₁' A₁'] [Algebra A' A₁'] [Algebra A A₁'] [IsScalarTower A A' A₁']
  [IsScalarTower A A₁ A₁'] [Algebra R' A₁'] [IsScalarTower R' A' A₁'] [IsScalarTower R' R₁' A₁']
  [Algebra R₁ R₁'] [Algebra R' R₁'] [Algebra R R₁'] [IsScalarTower R R' R₁']
      [IsScalarTower R R₁ R₁'] in
/-- The `A`-side part of the map carries the action of `a ∈ A` to the middle action of its image
in `A₁`. -/
theorem middleHomologyMap_action (K : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) (x : A)
    (m : baseChangeCohomologyOverBase (R := R) (R' := R') K n) :
    (middleHomologyMap (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) K n).hom
        (baseChangeCohomologyAction (R := R) (R' := R') K n x m) =
      middleAction (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) K n (algebraMap A A₁ x)
        ((middleHomologyMap (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) K n).hom m) := by
  let Rf := (ModuleCat.restrictScalars.{u} (algebraMap R A)).mapDerivedCategory
  let Rr := (ModuleCat.restrictScalars.{u} (algebraMap R R₁)).mapDerivedCategory
  let Rf₁ := (ModuleCat.restrictScalars.{u} (algebraMap R₁ A₁)).mapDerivedCategory
  let Ra := (ModuleCat.restrictScalars.{u} (algebraMap A A₁)).mapDerivedCategory
  let η := (totalDerivedExtensionScalarsAdjunction (algebraMap A A₁)).unit
  let ρ := restrictSquareDerivedIso.{u, u, u, u, u} (algebraMap R A) (algebraMap R R₁)
    (algebraMap A A₁) (algebraMap R₁ A₁) squareRA₁
  let G := dext (algebraMap R R') ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} R') n
  let u := x • 𝟙 K
  let u₁ := (dext (algebraMap A A₁)).map u
  have hsc : u₁ = algebraMap A A₁ x • 𝟙 ((dext (algebraMap A A₁)).obj K) :=
    derivedExtension_scalar (algebraMap A A₁) x K
  have h1 : u ≫ η.app K = η.app K ≫ Ra.map u₁ := η.naturality u
  have h2 : Rf.map (Ra.map u₁) ≫ ρ.hom.app ((dext (algebraMap A A₁)).obj K) =
      ρ.hom.app ((dext (algebraMap A A₁)).obj K) ≫ Rr.map (Rf₁.map u₁) := ρ.hom.naturality u₁
  have h12 : Rf.map u ≫ Rf.map (η.app K) ≫ ρ.hom.app ((dext (algebraMap A A₁)).obj K) =
      (Rf.map (η.app K) ≫ ρ.hom.app ((dext (algebraMap A A₁)).obj K)) ≫ Rr.map (Rf₁.map u₁) := by
    rw [← Rf.map_comp_assoc, h1, Rf.map_comp, Category.assoc, h2, Category.assoc]
  have hM : G.map (Rf.map u) ≫ G.map (Rf.map (η.app K) ≫
        ρ.hom.app ((dext (algebraMap A A₁)).obj K)) =
      G.map (Rf.map (η.app K) ≫ ρ.hom.app ((dext (algebraMap A A₁)).obj K)) ≫
        G.map (Rr.map (Rf₁.map u₁)) := by
    rw [← G.map_comp, ← G.map_comp, h12]
  have h := congrArg (fun t => t.hom m) hM
  refine h.trans ?_
  exact congrArg (fun t => (G.map (Rr.map (Rf₁.map t))).hom
    ((G.map (Rf.map (η.app K) ≫ ρ.hom.app ((dext (algebraMap A A₁)).obj K))).hom m)) hsc

omit [Algebra R A'] [Algebra A A'] [Algebra R' A'] [IsScalarTower R A A'] [IsScalarTower R R' A']
  [Algebra R₁ A₁'] [Algebra A₁ A₁'] [Algebra R₁' A₁'] [IsScalarTower R₁ A₁ A₁']
  [IsScalarTower R₁ R₁' A₁'] [Algebra A' A₁'] [Algebra A A₁'] [IsScalarTower A A' A₁']
  [IsScalarTower A A₁ A₁'] [Algebra R' A₁'] [IsScalarTower R' A' A₁'] [IsScalarTower R' R₁' A₁']
  [Algebra R₁ R₁'] [Algebra R' R₁'] [Algebra R R₁'] [IsScalarTower R R' R₁']
      [IsScalarTower R R₁ R₁'] in
/-- **The `A`-side part of the map is a base change along `A → A₁`** (Stacks 0DJ8, step (c)). -/
theorem isBaseChangeOfActions_middleHomologyMap [Module.Flat A A₁]
    (K : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) :
    IsBaseChangeOfActions
      (functorAction (A := A) ((ModuleCat.restrictScalars.{u} (algebraMap R A)).mapDerivedCategory ⋙
        baseChangeHomologyRestrict (algebraMap R R') n) K)
      (functorAction (A := A₁)
          (((ModuleCat.restrictScalars.{u} (algebraMap R₁ A₁)).mapDerivedCategory ⋙
          (ModuleCat.restrictScalars.{u} (algebraMap R R₁)).mapDerivedCategory) ⋙
            baseChangeHomologyRestrict (algebraMap R R') n) ((dext (algebraMap A A₁)).obj K))
      (middleHomologyMap (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) K n).hom.toAddMonoidHom := by
  let G₀ := baseChangeHomologyRestrict (algebraMap R R') n
  let Rf := (ModuleCat.restrictScalars.{u} (algebraMap R A)).mapDerivedCategory
  let ρ := restrictSquareDerivedIso.{u, u, u, u, u} (algebraMap R A) (algebraMap R R₁)
    (algebraMap A A₁) (algebraMap R₁ A₁) squareRA₁
  let η := (totalDerivedExtensionScalarsAdjunction (algebraMap A A₁)).unit
  refine (isBaseChangeOfActions_iff_of_natTrans (𝟙 (Rf ⋙ G₀)) (Functor.whiskerRight ρ.hom G₀)
    (G₀.map (Rf.map (η.app K)))
    (G₀.map (Rf.map (η.app K) ≫ ρ.hom.app ((dext (algebraMap A A₁)).obj K))) ?_).mp
    (isBaseChangeOfActions_derivedUnit (algebraMap R A) (algebraMap R R') K n)
  rw [G₀.map_comp, NatTrans.id_app, Category.id_comp]
  rfl

/-- The ring map `A ⊗_R R' → A₁ ⊗_R R'`. -/
abbrev firstFactorRingHom : A ⊗[R] R' →+* A₁ ⊗[R] R' :=
  (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R A A₁) (AlgHom.id R R')).toRingHom

omit [Algebra R A'] [Algebra A A'] [Algebra R' A'] [IsScalarTower R A A'] [IsScalarTower R R' A']
  [Algebra R₁ A₁'] [Algebra A₁ A₁'] [Algebra R₁' A₁'] [IsScalarTower R₁ A₁ A₁']
  [IsScalarTower R₁ R₁' A₁'] [Algebra A' A₁'] [Algebra A A₁'] [IsScalarTower A A' A₁']
  [IsScalarTower A A₁ A₁'] [Algebra R' A₁'] [IsScalarTower R' A' A₁'] [IsScalarTower R' R₁' A₁']
  [Algebra R₁ R₁'] [Algebra R' R₁'] [Algebra R R₁'] [IsScalarTower R R' R₁']
      [IsScalarTower R R₁ R₁'] in
/-- The `A`-side part of the map, as a linear map over `A ⊗_R R'`, which acts on the target
through `A₁ ⊗_R R'`. -/
def middleLinearMap (K : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) :
    letI := baseChangeCohomologyModule (R := R) (R' := R') K n
    letI := middleModule (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) K n
    letI : Module (A ⊗[R] R') (middleCohomology (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) K n) :=
      Module.compHom _ (firstFactorRingHom (R := R) (A := A) (R' := R') (A₁ := A₁))
    baseChangeCohomologyOverBase (R := R) (R' := R') K n →ₗ[A ⊗[R] R']
      middleCohomology (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) K n :=
  letI := baseChangeCohomologyModule (R := R) (R' := R') K n
  letI := middleModule (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) K n
  letI : Module (A ⊗[R] R') (middleCohomology (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) K n) :=
    Module.compHom _ (firstFactorRingHom (R := R) (A := A) (R' := R') (A₁ := A₁))
  let θ := (middleHomologyMap (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) K n).hom
  { toFun := θ
    map_add' := θ.map_add
    map_smul' := fun t m => by
      change θ (t • m) = firstFactorRingHom (R := R) (A := A) (R' := R') (A₁ := A₁) t • θ m
      induction t using TensorProduct.inductionOn generalizing m with
      | add x y hx hy => rw [add_smul, θ.map_add, hx, hy, map_add, add_smul]
      | tmul a r =>
        have ht : a ⊗ₜ[R] r =
            (Algebra.TensorProduct.includeLeft (R := R) (S := R) a : A ⊗[R] R') *
              Algebra.TensorProduct.includeRight r := by
          change a ⊗ₜ[R] r = (a ⊗ₜ[R] 1) * (1 ⊗ₜ[R] r)
          rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
        have ht₁ : firstFactorRingHom (R := R) (A := A) (R' := R') (A₁ := A₁) (a ⊗ₜ[R] r) =
            (Algebra.TensorProduct.includeLeft (R := R) (S := R) (algebraMap A A₁ a) :
              A₁ ⊗[R] R') * Algebra.TensorProduct.includeRight r := by
          change algebraMap A A₁ a ⊗ₜ[R] r = (algebraMap A A₁ a ⊗ₜ[R] 1) * (1 ⊗ₜ[R] r)
          rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
        rw [ht₁, ht, mul_smul, mul_smul, baseChangeCohomologyModule_includeLeft_smul,
          middleHomologyMap_action, baseChangeCohomologyModule_includeRight_smul, θ.map_smul,
          (middleModuleData (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) K n).2.2,
          (middleModuleData (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) K n).2.1] }

omit [Algebra R A'] [Algebra A A'] [Algebra R' A'] [IsScalarTower R A A'] [IsScalarTower R R' A']
  [Algebra R₁ A₁'] [Algebra A₁ A₁'] [Algebra R₁' A₁'] [IsScalarTower R₁ A₁ A₁']
  [IsScalarTower R₁ R₁' A₁'] [Algebra A' A₁'] [Algebra A A₁'] [IsScalarTower A A' A₁']
  [IsScalarTower A A₁ A₁'] [Algebra R' A₁'] [IsScalarTower R' A' A₁'] [IsScalarTower R' R₁' A₁']
  [Algebra R₁ R₁'] [Algebra R' R₁'] [Algebra R R₁'] [IsScalarTower R R' R₁']
      [IsScalarTower R R₁ R₁'] in
/-- **The `A`-side part of the map is a base change along `A ⊗_R R' → A₁ ⊗_R R'`.** -/
theorem isBaseChange_middleLinearMap [Module.Flat A A₁] (K : DerivedCategory (ModuleCat.{u} A))
    (n : ℤ) :
    letI : Algebra (A ⊗[R] R') (A₁ ⊗[R] R') :=
      (firstFactorRingHom (R := R) (A := A) (R' := R') (A₁ := A₁)).toAlgebra
    letI := baseChangeCohomologyModule (R := R) (R' := R') K n
    letI := middleModule (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) K n
    letI : Module (A ⊗[R] R') (middleCohomology (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) K n) :=
      Module.compHom _ (firstFactorRingHom (R := R) (A := A) (R' := R') (A₁ := A₁))
    letI : IsScalarTower (A ⊗[R] R') (A₁ ⊗[R] R')
        (middleCohomology (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) K n) :=
      IsScalarTower.of_compHom _ _ _
    IsBaseChange (A₁ ⊗[R] R') (middleLinearMap (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) K n) := by
  let C := A ⊗[R] R'
  let C' := A₁ ⊗[R] R'
  let H := baseChangeCohomologyOverBase (R := R) (R' := R') K n
  let N := middleCohomology (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) K n
  let φ := firstFactorRingHom (R := R) (A := A) (R' := R') (A₁ := A₁)
  let : Algebra C C' := φ.toAlgebra
  let := baseChangeCohomologyModule (R := R) (R' := R') K n
  let := middleModule (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) K n
  let : Module C N := Module.compHom _ φ
  have : IsScalarTower C C' N := IsScalarTower.of_compHom _ _ _
  let : Module A H := Module.compHom H (algebraMap A C)
  have : IsScalarTower A C H := IsScalarTower.of_compHom _ _ _
  let : Module A₁ N := Module.compHom N (algebraMap A₁ C')
  have : IsScalarTower A₁ C' N := IsScalarTower.of_compHom _ _ _
  let : Module A N := Module.compHom N (algebraMap A A₁)
  have : IsScalarTower A A₁ N := IsScalarTower.of_compHom _ _ _
  have hTC' : IsScalarTower A C C' := IsScalarTower.of_algebraMap_eq fun x => rfl
  have : IsScalarTower A C N := ⟨fun x c m => by
    change φ (x • c) • m = algebraMap A A₁ x • (φ c • m)
    rw [Algebra.smul_def, map_mul, mul_smul]
    rfl⟩
  have hj : IsBaseChange A₁
      ((middleLinearMap (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) K n).restrictScalars A) :=
    (isBaseChangeOfActions_middleHomologyMap (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁)
      K n).isBaseChange
      (fun x m => (baseChangeCohomologyModule_includeLeft_smul (R := R) (R' := R') K n x m).symm)
      (fun y m => ((middleModuleData (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) K n).2.2 y m).symm)
      _ (fun _ => rfl)
  refine isBaseChange_of_isBaseChange_of_span (T := A) (T' := A₁) _ hj fun x => ?_
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => exact Submodule.add_mem _ hx hy
  | tmul a r =>
    have : (a ⊗ₜ[R] r : C') = a • algebraMap C C' ((1 : A) ⊗ₜ[R] r) := by
      change a ⊗ₜ[R] r = a • (algebraMap A A₁ 1 ⊗ₜ[R] r)
      rw [map_one, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

omit [Algebra R A'] [Algebra A A'] [Algebra R' A'] [IsScalarTower R A A'] [IsScalarTower R R' A']
  [Algebra R₁ A₁'] [Algebra A₁ A₁'] [Algebra R₁' A₁'] [IsScalarTower R₁ A₁ A₁']
  [IsScalarTower R₁ R₁' A₁'] [Algebra A' A₁'] [Algebra A A₁'] [IsScalarTower A A' A₁']
  [IsScalarTower A A₁ A₁'] [Algebra R' A₁'] [IsScalarTower R' A' A₁'] [IsScalarTower R' R₁' A₁'] in
/-- The comparison of Stacks 065Z for the square `(R, R₁, R', R₁')`, on cohomology, is natural. -/
theorem cohomologyComparisonMap_id_naturality {Y Y' : DerivedCategory (ModuleCat.{u} R₁)}
    (v : Y ⟶ Y') (n : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map ((dext (algebraMap R R')).map
        ((ModuleCat.restrictScalars (algebraMap R R₁)).mapDerivedCategory.map v)) ≫
      cohomologyComparisonMap (R := R) (A := R₁) (R' := R') (A' := R₁') Y'
        ((dext (algebraMap R₁ R₁')).obj Y') (𝟙 _) n =
    cohomologyComparisonMap (R := R) (A := R₁) (R' := R') (A' := R₁') Y
        ((dext (algebraMap R₁ R₁')).obj Y) (𝟙 _) n ≫
      (ModuleCat.restrictScalars (algebraMap R' R₁')).map
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} R₁') n).map
          ((dext (algebraMap R₁ R₁')).map v)) := by
  let HR' := DerivedCategory.homologyFunctor (ModuleCat.{u} R') n
  let Rb := (ModuleCat.restrictScalars.{u} (algebraMap R' R₁')).mapDerivedCategory
  let τ := squareDerivedComparison (R := R) (A := R₁) (R' := R') (A' := R₁')
  let ι := ((ModuleCat.restrictScalars.{u} (algebraMap R' R₁')).mapDerivedCategoryHomologyIso n).hom
  have hFS : ∀ Z : DerivedCategory (ModuleCat.{u} R₁),
      cohomologyComparisonMap (R := R) (A := R₁) (R' := R') (A' := R₁') Z
        ((dext (algebraMap R₁ R₁')).obj Z) (𝟙 _) n =
      HR'.map (τ.app Z) ≫ ι.app ((dext (algebraMap R₁ R₁')).obj Z) := by
    intro Z
    have e : τ.app Z ≫ Rb.map (𝟙 ((dext (algebraMap R₁ R₁')).obj Z)) = τ.app Z := by
      rw [CategoryTheory.Functor.map_id]
      exact Category.comp_id _
    exact congrArg (fun t => HR'.map t ≫ ι.app ((dext (algebraMap R₁ R₁')).obj Z)) e
  have hτ : (dext (algebraMap R R')).map
        ((ModuleCat.restrictScalars (algebraMap R R₁)).mapDerivedCategory.map v) ≫ τ.app Y' =
      τ.app Y ≫ Rb.map ((dext (algebraMap R₁ R₁')).map v) := τ.naturality v
  have hι : HR'.map (Rb.map ((dext (algebraMap R₁ R₁')).map v)) ≫
        ι.app ((dext (algebraMap R₁ R₁')).obj Y') =
      ι.app ((dext (algebraMap R₁ R₁')).obj Y) ≫
        (ModuleCat.restrictScalars (algebraMap R' R₁')).map
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} R₁') n).map
            ((dext (algebraMap R₁ R₁')).map v)) := ι.naturality ((dext (algebraMap R₁ R₁')).map v)
  rw [hFS, hFS, ← HR'.map_comp_assoc, hτ, HR'.map_comp, Category.assoc, hι, Category.assoc]

/-- The ring map `A₁ ⊗_R R' → A₁ ⊗_{R₁} R₁'`. -/
abbrev middleRingHom : A₁ ⊗[R] R' →+* A₁ ⊗[R₁] R₁' :=
  secondSquareTensorMap (R := R) (A := A₁) (R' := R') (R₁ := R₁) (A₁ := A₁) (R₁' := R₁')

omit [Algebra R A'] [Algebra A A'] [Algebra R' A'] [IsScalarTower R A A'] [IsScalarTower R R' A']
  [Algebra R₁ A₁'] [Algebra A₁ A₁'] [Algebra R₁' A₁'] [IsScalarTower R₁ A₁ A₁']
  [IsScalarTower R₁ R₁' A₁'] [Algebra A' A₁'] [Algebra A A₁'] [IsScalarTower A A' A₁']
  [IsScalarTower A A₁ A₁'] [Algebra R' A₁'] [IsScalarTower R' A' A₁'] [IsScalarTower R' R₁' A₁']
  [Algebra R A] [IsScalarTower R A A₁] in
/-- On pure tensors, `middleRingHom` is `a ⊗ r ↦ a ⊗ r`, with `r` read in `R₁'`. -/
theorem middleRingHom_tmul (a : A₁) (r : R') :
    middleRingHom (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) (R₁' := R₁') (a ⊗ₜ[R] r) =
      a ⊗ₜ[R₁] algebraMap R' R₁' r :=
  secondSquareTensorMap_tmul (R := R) (A := A₁) (R' := R') (R₁ := R₁) (A₁ := A₁) (R₁' := R₁') a r

omit [Algebra R A'] [Algebra A A'] [Algebra R' A'] [IsScalarTower R A A'] [IsScalarTower R R' A']
  [Algebra R₁ A₁'] [Algebra A₁ A₁'] [Algebra R₁' A₁'] [IsScalarTower R₁ A₁ A₁']
  [IsScalarTower R₁ R₁' A₁'] [Algebra A' A₁'] [Algebra A A₁'] [IsScalarTower A A' A₁']
  [IsScalarTower A A₁ A₁'] [Algebra R' A₁'] [IsScalarTower R' A' A₁'] [IsScalarTower R' R₁' A₁']
  [Algebra R A] [IsScalarTower R A A₁] in
/-- The comparison of Stacks 065Z for the square `(R, R₁, R', R₁')` at `(K ⊗ᴸ_A A₁)|_{R₁}`, on
cohomology. -/
abbrev middleComparisonMap (K : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) :
    middleCohomology (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) K n ⟶
      (ModuleCat.restrictScalars (algebraMap R' R₁')).obj
        (baseChangeCohomologyOverBase (R := R₁) (R' := R₁') ((dext (algebraMap A A₁)).obj K) n) :=
  cohomologyComparisonMap (R := R) (A := R₁) (R' := R') (A' := R₁')
    ((ModuleCat.restrictScalars (algebraMap R₁ A₁)).mapDerivedCategory.obj
      ((dext (algebraMap A A₁)).obj K))
    ((dext (algebraMap R₁ R₁')).obj
        ((ModuleCat.restrictScalars (algebraMap R₁ A₁)).mapDerivedCategory.obj
      ((dext (algebraMap A A₁)).obj K))) (𝟙 _) n

omit [Algebra R A'] [Algebra A A'] [Algebra R' A'] [IsScalarTower R A A'] [IsScalarTower R R' A']
  [Algebra R₁ A₁'] [Algebra A₁ A₁'] [Algebra R₁' A₁'] [IsScalarTower R₁ A₁ A₁']
  [IsScalarTower R₁ R₁' A₁'] [Algebra A' A₁'] [Algebra A A₁'] [IsScalarTower A A' A₁']
  [IsScalarTower A A₁ A₁'] [Algebra R' A₁'] [IsScalarTower R' A' A₁'] [IsScalarTower R' R₁' A₁']
  [Algebra R A] [IsScalarTower R A A₁] [Algebra R A₁] [IsScalarTower R R₁ A₁] in
/-- The comparison carries the middle action to the action of `A₁` on the second square. -/
theorem middleComparisonMap_action (K : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) (x : A₁)
    (m : middleCohomology (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) K n) :
    (middleComparisonMap (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) (R₁' := R₁') K n).hom
        (middleAction (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) K n x m) =
      baseChangeCohomologyAction (R := R₁) (R' := R₁') ((dext (algebraMap A A₁)).obj K) n x
        ((middleComparisonMap (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) (R₁' := R₁') K n).hom m) :=
  congrArg (fun t => t.hom m) (cohomologyComparisonMap_id_naturality (R := R) (R' := R')
    (R₁' := R₁') ((ModuleCat.restrictScalars (algebraMap R₁ A₁)).mapDerivedCategory.map
      (x • 𝟙 ((dext (algebraMap A A₁)).obj K))) n)

omit [Algebra R A'] [Algebra A A'] [Algebra R' A'] [IsScalarTower R A A'] [IsScalarTower R R' A']
  [Algebra R₁ A₁'] [Algebra A₁ A₁'] [Algebra R₁' A₁'] [IsScalarTower R₁ A₁ A₁']
  [IsScalarTower R₁ R₁' A₁'] [Algebra A' A₁'] [Algebra A A₁'] [IsScalarTower A A' A₁']
  [IsScalarTower A A₁ A₁'] [Algebra R' A₁'] [IsScalarTower R' A' A₁'] [IsScalarTower R' R₁' A₁']
  [Algebra R A] [IsScalarTower R A A₁] in
/-- The comparison of Stacks 065Z for the square `(R, R₁, R', R₁')` at `(K ⊗ᴸ_A A₁)|_{R₁}`, as a
linear map over `A₁ ⊗_R R'`, which acts on the target through `A₁ ⊗_{R₁} R₁'`. -/
def middleComparisonLinearMap (K : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) :
    letI := middleModule (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) K n
    letI := baseChangeCohomologyModule (R := R₁) (R' := R₁') ((dext (algebraMap A A₁)).obj K) n
    letI : Module (A₁ ⊗[R] R')
        (baseChangeCohomologyOverBase (R := R₁) (R' := R₁') ((dext (algebraMap A A₁)).obj K) n) :=
      Module.compHom _ (middleRingHom (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) (R₁' := R₁'))
    middleCohomology (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) K n →ₗ[A₁ ⊗[R] R']
      baseChangeCohomologyOverBase (R := R₁) (R' := R₁') ((dext (algebraMap A A₁)).obj K) n :=
  letI := middleModule (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) K n
  letI := baseChangeCohomologyModule (R := R₁) (R' := R₁') ((dext (algebraMap A A₁)).obj K) n
  letI : Module (A₁ ⊗[R] R')
      (baseChangeCohomologyOverBase (R := R₁) (R' := R₁') ((dext (algebraMap A A₁)).obj K) n) :=
    Module.compHom _ (middleRingHom (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) (R₁' := R₁'))
  let q := middleComparisonMap (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) (R₁' := R₁') K n
  have hA := middleComparisonMap_action (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) (R₁' := R₁') K n
  { toFun := q.hom
    map_add' := q.hom.map_add
    map_smul' := fun t m => by
      change q.hom (t • m) =
        middleRingHom (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) (R₁' := R₁') t •
          (@id (baseChangeCohomologyOverBase (R := R₁) (R' := R₁')
            ((dext (algebraMap A A₁)).obj K) n) (q.hom m))
      induction t using TensorProduct.inductionOn generalizing m with
      | add x y hx hy =>
        rw [add_smul, q.hom.map_add, hx, hy, map_add, add_smul]
        all_goals rfl
      | tmul a r =>
        have ht : a ⊗ₜ[R] r =
            (Algebra.TensorProduct.includeLeft (R := R) (S := R) a : A₁ ⊗[R] R') *
              Algebra.TensorProduct.includeRight r := by
          change a ⊗ₜ[R] r = (a ⊗ₜ[R] 1) * (1 ⊗ₜ[R] r)
          rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
        have ht₁ : middleRingHom (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) (R₁' := R₁')
            (a ⊗ₜ[R] r) =
            (Algebra.TensorProduct.includeLeft (R := R₁) (S := R₁) a : A₁ ⊗[R₁] R₁') *
              Algebra.TensorProduct.includeRight (algebraMap R' R₁' r) := by
          rw [middleRingHom_tmul]
          change _ = (a ⊗ₜ[R₁] 1) * (1 ⊗ₜ[R₁] algebraMap R' R₁' r)
          rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
        rw [ht₁, ht, mul_smul, mul_smul,
          (middleModuleData (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) K n).2.2,
          (middleModuleData (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) K n).2.1, hA,
          q.hom.map_smul, baseChangeCohomologyModule_includeLeft_smul,
          baseChangeCohomologyModule_includeRight_smul]
        rfl }

omit [Algebra R A'] [Algebra A A'] [Algebra R' A'] [IsScalarTower R A A'] [IsScalarTower R R' A']
  [Algebra R₁ A₁'] [Algebra A₁ A₁'] [Algebra R₁' A₁'] [IsScalarTower R₁ A₁ A₁']
  [IsScalarTower R₁ R₁' A₁'] [Algebra A' A₁'] [Algebra A A₁'] [IsScalarTower A A' A₁']
  [IsScalarTower A A₁ A₁'] [Algebra R' A₁'] [IsScalarTower R' A' A₁'] [IsScalarTower R' R₁' A₁']
  [Algebra R A] [IsScalarTower R A A₁] in
/-- **The `R`-side part of the map is a base change along `A₁ ⊗_R R' → A₁ ⊗_{R₁} R₁'`**, for `R₁`
flat over `R` and `R₁'` flat over `R₁ ⊗_R R'` (Stacks 0DJ8, the flat square). -/
theorem isBaseChange_middleComparisonLinearMap [Module.Flat R R₁]
    (hR₁' : letI := (baseChangeTensorRingMap (R := R) (A := R₁) (R' := R') (A' := R₁')).toAlgebra
      Module.Flat (R₁ ⊗[R] R') R₁')
    (K : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) :
    letI : Algebra (A₁ ⊗[R] R') (A₁ ⊗[R₁] R₁') :=
      (middleRingHom (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) (R₁' := R₁')).toAlgebra
    letI := middleModule (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) K n
    letI := baseChangeCohomologyModule (R := R₁) (R' := R₁') ((dext (algebraMap A A₁)).obj K) n
    letI : Module (A₁ ⊗[R] R')
        (baseChangeCohomologyOverBase (R := R₁) (R' := R₁') ((dext (algebraMap A A₁)).obj K) n) :=
      Module.compHom _ (middleRingHom (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) (R₁' := R₁'))
    letI : IsScalarTower (A₁ ⊗[R] R') (A₁ ⊗[R₁] R₁')
        (baseChangeCohomologyOverBase (R := R₁) (R' := R₁') ((dext (algebraMap A A₁)).obj K) n) :=
      IsScalarTower.of_compHom _ _ _
    IsBaseChange (A₁ ⊗[R₁] R₁')
      (middleComparisonLinearMap (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) (R₁' := R₁') K n) := by
  let T := R₁ ⊗[R] R'
  let C := A₁ ⊗[R] R'
  let C₁ := A₁ ⊗[R₁] R₁'
  let K₁ := (dext (algebraMap A A₁)).obj K
  let Y := (ModuleCat.restrictScalars (algebraMap R₁ A₁)).mapDerivedCategory.obj K₁
  let M := middleCohomology (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) K n
  let N := baseChangeCohomologyOverBase (R := R₁) (R' := R₁') K₁ n
  let κ := baseChangeTensorRingMap (R := R) (A := R₁) (R' := R') (A' := R₁')
  let ψ := middleRingHom (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) (R₁' := R₁')
  let ν : T →+* C :=
    (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R R₁ A₁) (AlgHom.id R R')).toRingHom
  let ι' : R₁' →+* C₁ := Algebra.TensorProduct.includeRight.toRingHom
  let : Algebra T R₁' := κ.toAlgebra
  let : Algebra T C := ν.toAlgebra
  let : Algebra C C₁ := ψ.toAlgebra
  let : Algebra R₁' C₁ := ι'.toAlgebra
  let : Algebra T C₁ := (ψ.comp ν).toAlgebra
  have hνtmul : ∀ (r : R₁) (s : R'), ν (r ⊗ₜ[R] s) = algebraMap R₁ A₁ r ⊗ₜ[R] s := fun _ _ => rfl
  have hTT' : ∀ t : T, ι' (κ t) = ψ (ν t) := by
    intro t
    induction t using TensorProduct.inductionOn with
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
    | tmul r s =>
      rw [hνtmul, middleRingHom_tmul, baseChangeTensorRingMap_tmul]
      change (1 : A₁) ⊗ₜ[R₁] (algebraMap R₁ R₁' r * algebraMap R' R₁' s) = _
      rw [← smul_eq_mul, algebraMap_smul, ← TensorProduct.smul_tmul,
        Algebra.algebraMap_eq_smul_one (A := A₁)]
  have : IsScalarTower T R₁' C₁ := IsScalarTower.of_algebraMap_eq fun t => (hTT' t).symm
  have : IsScalarTower T C C₁ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  -- the modules
  let := middleModule (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) K n
  let : Module T M := baseChangeCohomologyModule (R := R) (A := R₁) (R' := R') Y n
  let := baseChangeCohomologyModule (R := R₁) (R' := R₁') K₁ n
  let : Module C N := Module.compHom _ ψ
  have : IsScalarTower C C₁ N := IsScalarTower.of_compHom _ _ _
  let : Module T N := Module.compHom _ κ
  have : IsScalarTower T R₁' N := IsScalarTower.of_compHom _ _ _
  have hMT : ∀ (t : T) (m : M), ν t • m = t • m := by
    intro t m
    induction t using TensorProduct.inductionOn generalizing m with
    | add x y hx hy => rw [map_add, add_smul, add_smul, hx, hy]
    | tmul r s =>
      rw [hνtmul, tmul_eq_includeLeft_mul_includeRight (R := R) (algebraMap R₁ A₁ r) s,
        tmul_eq_includeLeft_mul_includeRight (R := R) r s, mul_smul, mul_smul,
        (middleModuleData (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) K n).2.2,
        (middleModuleData (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) K n).2.1,
        middleAction_algebraMap₁, baseChangeCohomologyModule_includeLeft_smul,
        baseChangeCohomologyModule_includeRight_smul]
  have : IsScalarTower T C M := ⟨fun t c m => by
    rw [Algebra.smul_def, mul_smul]
    exact hMT t (c • m)⟩
  have : IsScalarTower R₁' C₁ N := ⟨fun r c m => by
    rw [Algebra.smul_def, mul_smul]
    exact baseChangeCohomologyModule_includeRight_smul (R := R₁) (R' := R₁') K₁ n r (c • m)⟩
  have hNT : ∀ (t : T) (m : N), ψ (ν t) • m = κ t • m := by
    intro t m
    rw [← hTT']
    exact baseChangeCohomologyModule_includeRight_smul (R := R₁) (R' := R₁') K₁ n (κ t) m
  have : IsScalarTower T C N := ⟨fun t c m => by
    change ψ (ν t * c) • m = κ t • (ψ c • m)
    rw [map_mul, mul_smul, hNT]⟩
  -- the flat square
  have hfs := (isIso_ringBaseChangeCohomologyMap_iff_isBaseChange_compHom (R := R) (A := R₁)
    (R' := R') (A' := R₁') Y ((dext (algebraMap R₁ R₁')).obj Y) (𝟙 _) n).mp
    (isIso_ringBaseChangeCohomologyMap_of_flat_of_flat_tensor (R := R) (A := R₁) (R' := R')
      (A' := R₁') hR₁' Y n)
  have hj : IsBaseChange R₁'
      ((middleComparisonLinearMap (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) (R₁' := R₁')
        K n).restrictScalars T) :=
    (IsBaseChange.iff_of_equiv_comm (LinearEquiv.refl T M) (LinearEquiv.refl R₁' N)
      (LinearMap.ext fun _ => rfl)).mp hfs
  refine isBaseChange_of_isBaseChange_of_span (T := T) (T' := R₁') _ hj fun x => ?_
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => exact Submodule.add_mem _ hx hy
  | tmul a s =>
    have : (a ⊗ₜ[R₁] s : C₁) = s • algebraMap C C₁ (a ⊗ₜ[R] (1 : R')) := by
      change a ⊗ₜ[R₁] s = ι' s * ψ (a ⊗ₜ[R] 1)
      rw [middleRingHom_tmul, map_one]
      change a ⊗ₜ[R₁] s = ((1 : A₁) ⊗ₜ[R₁] s) * (a ⊗ₜ[R₁] (1 : R₁'))
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

omit [Algebra R A'] [Algebra A A'] [Algebra R' A'] [IsScalarTower R A A'] [IsScalarTower R R' A']
  [Algebra R₁ A₁'] [Algebra A₁ A₁'] [Algebra R₁' A₁'] [IsScalarTower R₁ A₁ A₁']
  [IsScalarTower R₁ R₁' A₁'] [Algebra A' A₁'] [Algebra A A₁'] [IsScalarTower A A' A₁']
  [IsScalarTower A A₁ A₁'] [Algebra R' A₁'] [IsScalarTower R' A' A₁'] [IsScalarTower R' R₁' A₁'] in
/-- The map induced by a morphism of squares factors through the `A`-side part. -/
theorem secondSquareHomologyMap_eq (K : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) :
    secondSquareHomologyMap (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) (R₁' := R₁') K n =
      middleHomologyMap (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) K n ≫
        middleComparisonMap (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) (R₁' := R₁') K n := by
  let HR' := DerivedCategory.homologyFunctor (ModuleCat.{u} R') n
  let Rb := (ModuleCat.restrictScalars.{u} (algebraMap R' R₁')).mapDerivedCategory
  let Y := (ModuleCat.restrictScalars (algebraMap R₁ A₁)).mapDerivedCategory.obj
    ((dext (algebraMap A A₁)).obj K)
  let τ := squareDerivedComparison (R := R) (A := R₁) (R' := R') (A' := R₁')
  let ι := ((ModuleCat.restrictScalars.{u} (algebraMap R' R₁')).mapDerivedCategoryHomologyIso n).hom
  have e : τ.app Y ≫ Rb.map (𝟙 ((dext (algebraMap R₁ R₁')).obj Y)) = τ.app Y := by
    rw [CategoryTheory.Functor.map_id]
    exact Category.comp_id _
  have e' : middleComparisonMap (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) (R₁' := R₁') K n =
      HR'.map (τ.app Y) ≫ ι.app ((dext (algebraMap R₁ R₁')).obj Y) :=
    congrArg (fun t => HR'.map t ≫ ι.app ((dext (algebraMap R₁ R₁')).obj Y)) e
  rw [e']
  change HR'.map (middleDerivedMap (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) K ≫ τ.app Y) ≫
    ι.app _ = _
  rw [HR'.map_comp, Category.assoc]

/-- **The base-change property of the second-square map.** For `R₁` flat over `R`, `A₁` flat over
`A` and `R₁'` flat over `R₁ ⊗_R R'`, the map `Hⁿ(K ⊗ᴸ_R R') → Hⁿ((K ⊗ᴸ_A A₁) ⊗ᴸ_{R₁} R₁')`
induced by the morphism of squares exhibits the target as the base change along
`A ⊗_R R' → A₁ ⊗_{R₁} R₁'`. -/
theorem isBaseChange_secondSquareLinearMap [Module.Flat R R₁] [Module.Flat A A₁]
    (hR₁' : letI := (baseChangeTensorRingMap (R := R) (A := R₁) (R' := R') (A' := R₁')).toAlgebra
      Module.Flat (R₁ ⊗[R] R') R₁')
    (K : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) :
    letI : Algebra (A ⊗[R] R') (A₁ ⊗[R₁] R₁') :=
        (secondSquareTensorMap (R := R) (A := A) (R' := R') (R₁ := R₁) (A₁ := A₁)
            (R₁' := R₁')).toAlgebra
    letI := baseChangeCohomologyModule (R := R) (R' := R') K n
    letI := baseChangeCohomologyModule (R := R₁) (R' := R₁') ((dext (algebraMap A A₁)).obj K) n
    letI : Module (A ⊗[R] R')
        (baseChangeCohomologyOverBase (R := R₁) (R' := R₁') ((dext (algebraMap A A₁)).obj K) n) :=
      Module.compHom _
          (secondSquareTensorMap (R := R) (A := A) (R' := R') (R₁ := R₁) (A₁ := A₁) (R₁' := R₁'))
    letI : IsScalarTower (A ⊗[R] R') (A₁ ⊗[R₁] R₁')
        (baseChangeCohomologyOverBase (R := R₁) (R' := R₁') ((dext (algebraMap A A₁)).obj K) n) :=
      IsScalarTower.of_compHom _ _ _
    IsBaseChange (A₁ ⊗[R₁] R₁')
        (secondSquareLinearMap (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) (R₁' := R₁') K n) := by
  let C := A ⊗[R] R'
  let C' := A₁ ⊗[R] R'
  let C₁ := A₁ ⊗[R₁] R₁'
  let σ := secondSquareTensorMap (R := R) (A := A) (R' := R') (R₁ := R₁) (A₁ := A₁) (R₁' := R₁')
  let φ := firstFactorRingHom (R := R) (A := A) (R' := R') (A₁ := A₁)
  let ψ := middleRingHom (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) (R₁' := R₁')
  let K₁ := (dext (algebraMap A A₁)).obj K
  let H := baseChangeCohomologyOverBase (R := R) (R' := R') K n
  let M := middleCohomology (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) K n
  let H₁ := baseChangeCohomologyOverBase (R := R₁) (R' := R₁') K₁ n
  have hσ : ∀ t : C, σ t = ψ (φ t) := by
    intro t
    induction t using TensorProduct.inductionOn with
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
    | tmul a r =>
      rw [secondSquareTensorMap_tmul]
      change _ = ψ (algebraMap A A₁ a ⊗ₜ[R] r)
      rw [middleRingHom_tmul]
  let : Algebra C C₁ := σ.toAlgebra
  let : Algebra C C' := φ.toAlgebra
  let : Algebra C' C₁ := ψ.toAlgebra
  have : IsScalarTower C C' C₁ := IsScalarTower.of_algebraMap_eq fun t => hσ t
  let := baseChangeCohomologyModule (R := R) (R' := R') K n
  let := middleModule (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) K n
  let : Module C M := Module.compHom _ φ
  have : IsScalarTower C C' M := IsScalarTower.of_compHom _ _ _
  let := baseChangeCohomologyModule (R := R₁) (R' := R₁') K₁ n
  let : Module C' H₁ := Module.compHom _ ψ
  have : IsScalarTower C' C₁ H₁ := IsScalarTower.of_compHom _ _ _
  let : Module C H₁ := Module.compHom _ σ
  have : IsScalarTower C C₁ H₁ := IsScalarTower.of_compHom _ _ _
  have : IsScalarTower C C' H₁ := ⟨fun c c' m => by
    change ψ (φ c * c') • m = σ c • (ψ c' • m)
    rw [map_mul, mul_smul, hσ]⟩
  have h1 := isBaseChange_middleLinearMap (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) K n
  have h2 := isBaseChange_middleComparisonLinearMap (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁)
    (R₁' := R₁') hR₁' K n
  have h := h1.comp h2
  refine (IsBaseChange.iff_of_equiv_comm (LinearEquiv.refl C H) (LinearEquiv.refl C₁ H₁)
    (LinearMap.ext fun m => ?_)).mp h
  change (secondSquareHomologyMap (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) (R₁' := R₁')
      K n).hom m =
    (middleComparisonMap (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) (R₁' := R₁') K n).hom
      ((middleHomologyMap (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) K n).hom m)
  exact congrArg (fun t => t.hom m) (secondSquareHomologyMap_eq (R := R) (R' := R') (R₁ := R₁)
    (A₁ := A₁) (R₁' := R₁') K n)

/-- **The base-change map of the second square, against that of the first.** Under the flatness
hypotheses, the base-change map of the second square at `K ⊗ᴸ_A A₁`, `K' ⊗ᴸ_{A'} A₁'` is invertible
exactly when the base-change map `A' ⊗_{A ⊗_R R'} Hⁿ(K ⊗ᴸ_R R') ⟶ Hⁿ(K')` of the first square,
in the form `TensorProduct.isBaseChange`-lift of the comparison, becomes bijective after base
change to `A₁'`. -/
theorem isIso_secondSquare_iff_bijective_lTensor [Module.Flat R R₁] [Module.Flat A A₁]
    [Module.Flat A' A₁']
    (hR₁' : letI := (baseChangeTensorRingMap (R := R) (A := R₁) (R' := R') (A' := R₁')).toAlgebra
      Module.Flat (R₁ ⊗[R] R') R₁')
    (K : DerivedCategory (ModuleCat.{u} A)) (K' : DerivedCategory (ModuleCat.{u} A'))
    (φ : (dext (algebraMap A A')).obj K ⟶ K') (n : ℤ) :
    letI : Algebra (A ⊗[R] R') A' :=
      (baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A')).toAlgebra
    letI := baseChangeCohomologyModule (R := R) (R' := R') K n
    letI : Module (A ⊗[R] R') ((DerivedCategory.homologyFunctor (ModuleCat.{u} A') n).obj K') :=
      Module.compHom _ (algebraMap (A ⊗[R] R') A')
    letI : IsScalarTower (A ⊗[R] R') A'
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A') n).obj K') :=
      IsScalarTower.of_compHom _ _ _
    IsIso (ringBaseChangeCohomologyMap (R := R₁) (A := A₁) (R' := R₁') (A' := A₁')
        ((dext (algebraMap A A₁)).obj K) ((dext (algebraMap A' A₁')).obj K')
        (extendScalarsBaseChangeHom K K' φ) n) ↔
      Function.Bijective
        (((TensorProduct.isBaseChange (A ⊗[R] R') (baseChangeCohomologyOverBase (R := R)
            (R' := R') K n) A').lift
          (show baseChangeCohomologyOverBase (R := R) (R' := R') K n →ₗ[A ⊗[R] R']
              (DerivedCategory.homologyFunctor (ModuleCat.{u} A') n).obj K' from
            (cohomologyComparisonLinearMap (R := R) (R' := R') K K' φ n).hom)).lTensor A₁') := by
  let C := A ⊗[R] R'
  let C₁ := A₁ ⊗[R₁] R₁'
  let σ : C →+* C₁ := secondSquareTensorMap (R := R) (A := A) (R' := R') (R₁ := R₁) (A₁ := A₁)
      (R₁' := R₁')
  let τ := baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A')
  let τ₁ := baseChangeTensorRingMap (R := R₁) (A := A₁) (R' := R₁') (A' := A₁')
  let K₁ := (dext (algebraMap A A₁)).obj K
  let K₁' := (dext (algebraMap A' A₁')).obj K'
  let H := baseChangeCohomologyOverBase (R := R) (R' := R') K n
  let H₁ := baseChangeCohomologyOverBase (R := R₁) (R' := R₁') K₁ n
  let H' := (DerivedCategory.homologyFunctor (ModuleCat.{u} A') n).obj K'
  let H₁' := (DerivedCategory.homologyFunctor (ModuleCat.{u} A₁') n).obj K₁'
  let : Algebra C C₁ := σ.toAlgebra
  let : Algebra C A' := τ.toAlgebra
  let : Algebra C₁ A₁' := τ₁.toAlgebra
  let : Algebra C A₁' := ((algebraMap A' A₁').comp τ).toAlgebra
  have hcube : τ₁.comp σ = (algebraMap A' A₁').comp τ :=
    baseChangeTensorRingMap_comp_secondSquareTensorMap
  have : IsScalarTower C A' A₁' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower C C₁ A₁' := IsScalarTower.of_algebraMap_eq fun x =>
    (RingHom.congr_fun hcube x).symm
  let := baseChangeCohomologyModule (R := R) (R' := R') K n
  let := baseChangeCohomologyModule (R := R₁) (R' := R₁') K₁ n
  let : Module C H₁ := Module.compHom _ (algebraMap C C₁)
  have : IsScalarTower C C₁ H₁ := IsScalarTower.of_compHom _ _ _
  let : Module C H' := Module.compHom _ (algebraMap C A')
  have : IsScalarTower C A' H' := IsScalarTower.of_compHom _ _ _
  let : Module C₁ H₁' := Module.compHom _ (algebraMap C₁ A₁')
  have : IsScalarTower C₁ A₁' H₁' := IsScalarTower.of_compHom _ _ _
  let : Module A' H₁' := Module.compHom _ (algebraMap A' A₁')
  have : IsScalarTower A' A₁' H₁' := IsScalarTower.of_compHom _ _ _
  let : Module C H₁' := Module.compHom _ (algebraMap C A₁')
  have : IsScalarTower C A₁' H₁' := IsScalarTower.of_compHom _ _ _
  have : IsScalarTower C C₁ H₁' := ⟨fun c x y => by
    change τ₁ (c • x) • y = algebraMap C A₁' c • (τ₁ x • y)
    rw [Algebra.smul_def, map_mul, mul_smul]
    exact congrArg (· • (τ₁ x • y)) (RingHom.congr_fun hcube c)⟩
  have : IsScalarTower C A' H₁' := ⟨fun c x y => by
    change algebraMap A' A₁' (c • x) • y = algebraMap C A₁' c • (algebraMap A' A₁' x • y)
    rw [Algebra.smul_def, map_mul, mul_smul, ← IsScalarTower.algebraMap_apply C A' A₁']⟩
  let q : H →ₗ[C] H' := (cohomologyComparisonLinearMap (R := R) (R' := R') K K' φ n).hom
  let q₁ : H₁ →ₗ[C₁] H₁' := (cohomologyComparisonLinearMap (R := R₁) (R' := R₁') K₁ K₁'
      (extendScalarsBaseChangeHom K K' φ) n).hom
  let θ : H →ₗ[C] H₁ :=
    secondSquareLinearMap (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) (R₁' := R₁') K n
  let j' : H' →ₗ[A'] H₁' := (derivedUnitHomologyMap (S := A') (T := A₁') K' n).hom
  have hj : IsBaseChange C₁ θ := isBaseChange_secondSquareLinearMap (R := R) (R' := R')
    (R₁ := R₁) (A₁ := A₁) (R₁' := R₁') hR₁' K n
  have hj' : IsBaseChange A₁' j' :=
    isBaseChange_derivedUnitHomologyMap (S := A') (T := A₁') inferInstance K' n
  have hcomm : (q₁.restrictScalars C).comp θ = (j'.restrictScalars C).comp q :=
    LinearMap.ext fun m => cohomologyComparisonMap_secondSquare K K' φ n m
  have hmk := TensorProduct.isBaseChange C H A'
  let L : A' ⊗[C] H →ₗ[A'] H' := hmk.lift q
  have hL : (L.restrictScalars C) ∘ₗ TensorProduct.mk C A' H 1 = q := hmk.lift_comp q
  have e1 : IsIso (ringBaseChangeCohomologyMap (R := R₁) (A := A₁) (R' := R₁') (A' := A₁')
        K₁ K₁' (extendScalarsBaseChangeHom K K' φ) n) ↔ IsBaseChange A₁' q₁ :=
    isIso_ringBaseChangeCohomologyMap_iff_isBaseChange_compHom (R := R₁) (R' := R₁') K₁ K₁'
      (extendScalarsBaseChangeHom K K' φ) n
  have e2 : IsBaseChange A₁' ((q₁.restrictScalars C).comp θ) ↔ IsBaseChange A₁' q₁ :=
    hj.comp_iff
  have e3 : (j'.restrictScalars C).comp q =
      ((j' ∘ₗ L).restrictScalars C) ∘ₗ TensorProduct.mk C A' H 1 := by
    rw [← hL]
    rfl
  have e4 : IsBaseChange A₁' (((j' ∘ₗ L).restrictScalars C) ∘ₗ TensorProduct.mk C A' H 1) ↔
      IsBaseChange A₁' (j' ∘ₗ L) := hmk.comp_iff
  have e5 := isBaseChange_comp_iff_bijective_lTensor L j' hj'
  exact e1.trans (e2.symm.trans ((by rw [hcomm, e3] :
      IsBaseChange A₁' ((q₁.restrictScalars C).comp θ) ↔
    IsBaseChange A₁' (((j' ∘ₗ L).restrictScalars C) ∘ₗ TensorProduct.mk C A' H 1)).trans
      (e4.trans e5)))

/-- **The base-change map under a flat change of square (Stacks 0DJ8, ring-level core).** Let
`(R, A, R', A') → (R₁, A₁, R₁', A₁')` be a morphism of commutative squares of rings with `R₁` flat
over `R`, `A₁` flat over `A`, `A₁'` flat over `A'` and `R₁'` flat over `R₁ ⊗_R R'`. If the
base-change map of Stacks 0DJ7 of the first square at `K`, `K'`, `φ` is invertible, so is the one
of the second square at `K ⊗ᴸ_A A₁`, `K' ⊗ᴸ_{A'} A₁'` and the induced morphism. -/
theorem isIso_ringBaseChangeCohomologyMap_secondSquare [Module.Flat R R₁] [Module.Flat A A₁]
    [Module.Flat A' A₁']
    (hR₁' : letI := (baseChangeTensorRingMap (R := R) (A := R₁) (R' := R') (A' := R₁')).toAlgebra
      Module.Flat (R₁ ⊗[R] R') R₁')
    (K : DerivedCategory (ModuleCat.{u} A)) (K' : DerivedCategory (ModuleCat.{u} A'))
    (φ : (dext (algebraMap A A')).obj K ⟶ K') (n : ℤ)
    (h : IsIso (ringBaseChangeCohomologyMap (R := R) (R' := R') K K' φ n)) :
    IsIso (ringBaseChangeCohomologyMap (R := R₁) (A := A₁) (R' := R₁') (A' := A₁')
      ((dext (algebraMap A A₁)).obj K) ((dext (algebraMap A' A₁')).obj K')
      (extendScalarsBaseChangeHom K K' φ) n) := by
  let : Algebra (A ⊗[R] R') A' :=
    (baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A')).toAlgebra
  let := baseChangeCohomologyModule (R := R) (R' := R') K n
  let : Module (A ⊗[R] R') ((DerivedCategory.homologyFunctor (ModuleCat.{u} A') n).obj K') :=
    Module.compHom _ (algebraMap (A ⊗[R] R') A')
  let : IsScalarTower (A ⊗[R] R') A'
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A') n).obj K') :=
    IsScalarTower.of_compHom _ _ _
  have hq := (isIso_ringBaseChangeCohomologyMap_iff_isBaseChange_compHom (R := R) (R' := R')
    K K' φ n).mp h
  replace hq := (isBaseChange_iff_bijective_lift (C := A ⊗[R] R') (T := A') _).mp hq
  refine (isIso_secondSquare_iff_bijective_lTensor (R₁ := R₁) (A₁ := A₁) (R₁' := R₁') (A₁' := A₁')
    hR₁' K K' φ n).mpr ?_
  exact (LinearEquiv.lTensor A₁' (LinearEquiv.ofBijective _ hq)).bijective

end SecondSquare

/-! ### A family of second squares -/

section Family

variable {R A R' A' : Type u}
  [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
  [Algebra R A] [Algebra R R'] [Algebra R A'] [Algebra A A'] [Algebra R' A']
  [IsScalarTower R A A'] [IsScalarTower R R' A']
  {ι : Type*} {R₁ A₁ R₁' A₁' : ι → Type u}
  [∀ i, CommRing (R₁ i)] [∀ i, CommRing (A₁ i)] [∀ i, CommRing (R₁' i)] [∀ i, CommRing (A₁' i)]
  [∀ i, Algebra (R₁ i) (A₁ i)] [∀ i, Algebra (R₁ i) (R₁' i)] [∀ i, Algebra (R₁ i) (A₁' i)]
  [∀ i, Algebra (A₁ i) (A₁' i)] [∀ i, Algebra (R₁' i) (A₁' i)]
  [∀ i, IsScalarTower (R₁ i) (A₁ i) (A₁' i)] [∀ i, IsScalarTower (R₁ i) (R₁' i) (A₁' i)]
  [∀ i, Algebra R (R₁ i)] [∀ i, Algebra A (A₁ i)] [∀ i, Algebra R' (R₁' i)]
  [∀ i, Algebra A' (A₁' i)]
  [∀ i, Algebra R (A₁ i)] [∀ i, IsScalarTower R A (A₁ i)] [∀ i, IsScalarTower R (R₁ i) (A₁ i)]
  [∀ i, Algebra R (R₁' i)] [∀ i, IsScalarTower R R' (R₁' i)]
  [∀ i, IsScalarTower R (R₁ i) (R₁' i)]
  [∀ i, Algebra A (A₁' i)] [∀ i, IsScalarTower A A' (A₁' i)] [∀ i, IsScalarTower A (A₁ i) (A₁' i)]
  [∀ i, Algebra R' (A₁' i)] [∀ i, IsScalarTower R' A' (A₁' i)]
  [∀ i, IsScalarTower R' (R₁' i) (A₁' i)]

/-- **Stacks 0DJ8, ring-level core, for a covering family of flat second squares.** For a family
of morphisms of commutative squares `(R, A, R', A') → (R₁ i, A₁ i, R₁' i, A₁' i)` with `R₁ i` flat
over `R`, `A₁ i` flat over `A`, `A₁' i` flat over `A'` and `R₁' i` flat over `R₁ i ⊗_R R'`, whose
`Spec A₁' i` cover `Spec A'`, the base-change map of Stacks 0DJ7 of the first square at `K`, `K'`,
`φ` is invertible exactly when all those of the second squares are. -/
theorem isIso_ringBaseChangeCohomologyMap_iff_forall_secondSquare
    [∀ i, Module.Flat R (R₁ i)] [∀ i, Module.Flat A (A₁ i)] [∀ i, Module.Flat A' (A₁' i)]
    (hR₁' : ∀ i, letI := (baseChangeTensorRingMap (R := R) (A := R₁ i) (R' := R')
      (A' := R₁' i)).toAlgebra; Module.Flat (R₁ i ⊗[R] R') (R₁' i))
    (hcov : ∀ q : PrimeSpectrum A', ∃ i,
      q ∈ Set.range (PrimeSpectrum.comap (algebraMap A' (A₁' i))))
    (K : DerivedCategory (ModuleCat.{u} A)) (K' : DerivedCategory (ModuleCat.{u} A'))
    (φ : (dext (algebraMap A A')).obj K ⟶ K') (n : ℤ) :
    IsIso (ringBaseChangeCohomologyMap (R := R) (R' := R') K K' φ n) ↔
      ∀ i, IsIso (ringBaseChangeCohomologyMap (R := R₁ i) (A := A₁ i) (R' := R₁' i) (A' := A₁' i)
        ((dext (algebraMap A (A₁ i))).obj K) ((dext (algebraMap A' (A₁' i))).obj K')
        (extendScalarsBaseChangeHom K K' φ) n) := by
  refine ⟨fun h i => isIso_ringBaseChangeCohomologyMap_secondSquare (hR₁' i) K K' φ n h,
    fun h => ?_⟩
  let : Algebra (A ⊗[R] R') A' :=
    (baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A')).toAlgebra
  let := baseChangeCohomologyModule (R := R) (R' := R') K n
  let : Module (A ⊗[R] R') ((DerivedCategory.homologyFunctor (ModuleCat.{u} A') n).obj K') :=
    Module.compHom _ (algebraMap (A ⊗[R] R') A')
  let : IsScalarTower (A ⊗[R] R') A'
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A') n).obj K') :=
    IsScalarTower.of_compHom _ _ _
  refine (isIso_ringBaseChangeCohomologyMap_iff_isBaseChange_compHom (R := R) (R' := R')
    K K' φ n).mpr ?_
  refine (isBaseChange_iff_bijective_lift (C := A ⊗[R] R') (T := A') _).mpr ?_
  exact bijective_of_forall_bijective_lTensor A₁' hcov _ fun i =>
    (isIso_secondSquare_iff_bijective_lTensor (hR₁' i) K K' φ n).mp (h i)

end Family

end RingTheory.TorIndependence

end
