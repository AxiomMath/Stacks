module

public import StacksFrontier.Homology.Tor.ChangeOfRingsSystem

/-!
# Flat base change for `Tor` in the second variable

Let `R → A` and `R → R'` be homomorphisms of commutative rings. The module `Tor_i^R(R', A)`
carries an action of `R' ⊗[R] A`, hence by restriction along the right tensor inclusion an action
of `A`; that action is functoriality of `Tor_i^R(R', ·)` in its second variable. For a flat
homomorphism `A → A₂` the canonical `A₂`-linear comparison

`A₂ ⊗_A Tor_i^R(R', A) ⟶ Tor_i^R(R', A₂)`

is an isomorphism.

## Main definitions

* `RingTheory.TorIndependence.torModule`: `Tor_i^R(R', A)` read as an `A`-module through the
  right tensor inclusion `A → R' ⊗[R] A`.
* `RingTheory.TorIndependence.torModuleMap`: `Tor_i^R(R', ·)` applied to the structure map
  `A → A₂`, as a map of `A`-modules.

## Main results

* `RingTheory.TorIndependence.torModule_smul`: the action of `A` on `Tor_i^R(R', A)` is
  functoriality of `Tor_i^R(R', ·)` applied to multiplication by the scalar.
* `RingTheory.TorIndependence.isIso_torModuleFlatBaseChange`: **flat base change for `Tor` in the
  second variable**.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped TensorProduct ChangeOfRings

universe u

namespace RingTheory.TorIndependence

/-- The canonical `R' ⊗[R] A`-module structure on `Tor_i^R(R', A)`. -/
private instance torTensorModule (R A R' : Type u) [CommRing R] [CommRing A] [CommRing R']
    [Algebra R A] [Algebra R R'] (i : ℕ) :
    Module (R' ⊗[R] A) (TorChangeOfRings.torObj R i R' A) :=
  TorChangeOfRings.moduleStructure TorChangeOfRings.canonicalSystem_nonempty R R' A i

/-- `Tor_i^R(R', A)` read as an `A`-module through the right tensor inclusion. -/
abbrev torModule (R A R' : Type u) [CommRing R] [CommRing A] [CommRing R']
    [Algebra R A] [Algebra R R'] (i : ℕ) : ModuleCat.{u} A :=
  letI := TorChangeOfRings.moduleStructure TorChangeOfRings.canonicalSystem_nonempty R R' A i
  (ModuleCat.restrictScalars
      (Algebra.TensorProduct.includeRight (R := R) (A := R') (B := A)).toRingHom).obj
    (ModuleCat.of (R' ⊗[R] A) (TorChangeOfRings.torObj R i R' A))

/-- The action of `A` on `Tor_i^R(R', A)` is functoriality of `Tor_i^R(R', ·)`. -/
theorem torModule_smul (R A R' : Type u) [CommRing R] [CommRing A] [CommRing R']
    [Algebra R A] [Algebra R R'] (i : ℕ) (a : A) (x : torModule R A R' i) :
    (a • x : torModule R A R' i) =
      (((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R R')).map
        (ModuleCat.ofHom (TorChangeOfRings.mulLinear R A a))).hom x := by
  let _ := TorChangeOfRings.moduleStructure TorChangeOfRings.canonicalSystem_nonempty R R' A i
  have hone : ModuleCat.ofHom (TorChangeOfRings.mulLinear R R' 1) = 𝟙 (ModuleCat.of R R') := by
    ext y
    simp [TorChangeOfRings.mulLinear]
  refine ((TorChangeOfRings.canonicalLaws
    TorChangeOfRings.canonicalSystem_nonempty).action_tmul R R' A i (1 : R') a
    (x : TorChangeOfRings.torObj R i R' A)).trans ?_
  simp only [hone, CategoryTheory.Functor.map_id, NatTrans.id_app]
  rfl

/-- Restriction of scalars along the identity of `R` acts as the identity on the homology of a
complex of the form `A ⊗_R P` for `P` a projective resolution. -/
private lemma homologyRestrictIso_tensor (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (i : ℕ)
    (y : (((MonoidalCategory.tensoringLeft (ModuleCat.{u} R)).obj
          (ModuleCat.of R A)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (projectiveResolution (ModuleCat.of R B)).complex |>.homology i) :
    (TorChangeOfRings.homologyRestrictIso R R
        ((((MonoidalCategory.tensoringLeft (ModuleCat.{u} R)).obj
            (ModuleCat.of R A)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (projectiveResolution (ModuleCat.of R B)).complex) i).hom y = y := by
  let F := (MonoidalCategory.tensoringLeft (ModuleCat.{u} R)).obj (ModuleCat.of R A)
  let P := projectiveResolution (ModuleCat.of R B)
  let psi := ProjectiveResolution.lift (𝟙 (ModuleCat.of R B)) P P
  obtain ⟨x, rfl⟩ := ((ConcreteCategory.isIso_iff_bijective
    (P.isoLeftDerivedObj F i).hom).mp inferInstance).2 y
  have hA := (TorChangeOfRings.canonicalLaws
      TorChangeOfRings.canonicalSystem_nonempty).map_resolution
    R R A B A B i (AlgHom.id R A) (AlgHom.id R B) P P psi
    ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map psi)
    (fun p ↦ congrArg (fun h : P.complex.X 0 ⟶ ModuleCat.of R B ↦ h p)
      ((ProjectiveResolution.lift_commutes_zero (𝟙 (ModuleCat.of R B)) P P).trans
        (Category.comp_id _)))
    (fun _ _ _ ↦ rfl) x
  have hB := ProjectiveResolution.isoLeftDerivedObj_hom_naturality
    (𝟙 (ModuleCat.of R B)) P P psi
    (ProjectiveResolution.lift_commutes_zero (𝟙 (ModuleCat.of R B)) P P) F i
  rw [CategoryTheory.Functor.map_id, Category.id_comp] at hB
  dsimp only at hA
  have hBx := DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp hB.symm) x
  simp only [Functor.comp_map, ModuleCat.hom_comp, LinearMap.comp_apply] at hBx
  exact (congrArg _ hBx.symm).trans (hA.symm.trans (congrArg _
    ((TorChangeOfRings.canonicalLaws TorChangeOfRings.canonicalSystem_nonempty).map_id
      R A B i x)))

/-- Over a fixed base ring and with the identity in the first variable, the canonical system's
change-of-rings map is functoriality of `Tor_i^R(A, ·)`. -/
private lemma systemMap_eq_torMap (R A B B' : Type u) [CommRing R] [CommRing A] [CommRing B]
    [CommRing B'] [Algebra R A] [Algebra R B] [Algebra R B'] (fB : B →ₐ[R] B') (i : ℕ)
    (x : TorChangeOfRings.torObj R i A B) :
    (TorChangeOfRings.canonicalSystem TorChangeOfRings.canonicalSystem_nonempty).1.map
        R R A B A B' i (AlgHom.id R A) fB x =
      (((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R A)).map
        (ModuleCat.ofHom fB.toLinearMap)).hom x := by
  let F := (MonoidalCategory.tensoringLeft (ModuleCat.{u} R)).obj (ModuleCat.of R A)
  let f : ModuleCat.of R B ⟶ ModuleCat.of R B' := ModuleCat.ofHom fB.toLinearMap
  let psi := ProjectiveResolution.lift f (projectiveResolution (ModuleCat.of R B))
    (projectiveResolution (ModuleCat.of R B'))
  have hA := (TorChangeOfRings.canonicalLaws
      TorChangeOfRings.canonicalSystem_nonempty).map_resolution
    R R A B A B' i (AlgHom.id R A) fB (projectiveResolution (ModuleCat.of R B))
    (projectiveResolution (ModuleCat.of R B')) psi
    ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map psi)
    (fun p ↦ congrArg
      (fun h : (projectiveResolution (ModuleCat.of R B)).complex.X 0 ⟶ ModuleCat.of R B' ↦ h p)
      (ProjectiveResolution.lift_commutes_zero f (projectiveResolution (ModuleCat.of R B))
        (projectiveResolution (ModuleCat.of R B'))))
    (fun _ _ _ ↦ rfl) x
  have hB := ProjectiveResolution.isoLeftDerivedObj_hom_naturality f
    (projectiveResolution (ModuleCat.of R B)) (projectiveResolution (ModuleCat.of R B')) psi
    (ProjectiveResolution.lift_commutes_zero f (projectiveResolution (ModuleCat.of R B))
      (projectiveResolution (ModuleCat.of R B'))) F i
  dsimp only at hA
  have hBx := DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp hB) x
  simp only [Functor.comp_map, ModuleCat.hom_comp] at hBx
  exact ((ConcreteCategory.isIso_iff_bijective
    ((projectiveResolution (ModuleCat.of R B')).isoLeftDerivedObj F i).hom).mp
      inferInstance).1 (hA.trans ((homologyRestrictIso_tensor R A B' i _).trans hBx.symm))

variable {R A A₂ R' : Type u} [CommRing R] [CommRing A] [CommRing A₂] [CommRing R']
  [Algebra R A] [Algebra A A₂] [Algebra R A₂] [IsScalarTower R A A₂] [Algebra R R']

/-- `Tor_i^R(R', ·)` applied to the structure map `A → A₂`, as an `A`-linear map. -/
def torModuleLinear (i : ℕ) :
    torModule R A R' i →ₗ[A]
      (ModuleCat.restrictScalars.{u} (algebraMap A A₂)).obj (torModule R A₂ R' i) where
  toFun x := (((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R R')).map
    (ModuleCat.ofHom (IsScalarTower.toAlgHom R A A₂).toLinearMap)).hom x
  map_add' x y := map_add _ x y
  map_smul' a x := by
    let _ := TorChangeOfRings.moduleStructure TorChangeOfRings.canonicalSystem_nonempty R R' A₂ i
    have hone : ModuleCat.ofHom (TorChangeOfRings.mulLinear R R' 1) = 𝟙 (ModuleCat.of R R') := by
      ext y
      simp [TorChangeOfRings.mulLinear]
    have hsmul : ∀ y : TorChangeOfRings.torObj R i R' A₂,
        ((1 : R') ⊗ₜ[R] algebraMap A A₂ a) • y =
          (((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R R')).map
            (ModuleCat.ofHom (TorChangeOfRings.mulLinear R A₂ (algebraMap A A₂ a)))).hom y := by
      intro y
      refine ((TorChangeOfRings.canonicalLaws
        TorChangeOfRings.canonicalSystem_nonempty).action_tmul R R' A₂ i (1 : R')
        (algebraMap A A₂ a) y).trans ?_
      simp only [hone, CategoryTheory.Functor.map_id, NatTrans.id_app]
      rfl
    have hsq : ModuleCat.ofHom (TorChangeOfRings.mulLinear R A a) ≫
        ModuleCat.ofHom (IsScalarTower.toAlgHom R A A₂).toLinearMap =
        ModuleCat.ofHom (IsScalarTower.toAlgHom R A A₂).toLinearMap ≫
          ModuleCat.ofHom (TorChangeOfRings.mulLinear R A₂ (algebraMap A A₂ a)) := by
      ext z
      simp [TorChangeOfRings.mulLinear, map_mul]
    have key : ((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R R')).map
          (ModuleCat.ofHom (TorChangeOfRings.mulLinear R A a)) ≫
        ((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R R')).map
          (ModuleCat.ofHom (IsScalarTower.toAlgHom R A A₂).toLinearMap) =
        ((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R R')).map
          (ModuleCat.ofHom (IsScalarTower.toAlgHom R A A₂).toLinearMap) ≫
        ((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R R')).map
          (ModuleCat.ofHom (TorChangeOfRings.mulLinear R A₂ (algebraMap A A₂ a))) := by
      rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, hsq]
    have keyx := DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp key) x
    simp only [ModuleCat.hom_comp] at keyx
    change _ = ((1 : R') ⊗ₜ[R] algebraMap A A₂ a) •
      (((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R R')).map
        (ModuleCat.ofHom (IsScalarTower.toAlgHom R A A₂).toLinearMap)).hom x
    rw [hsmul, torModule_smul R A R' i a x]
    exact keyx

/-- `Tor_i^R(R', ·)` applied to the structure map `A → A₂`, as a map of `A`-modules. -/
def torModuleMap (i : ℕ) :
    torModule R A R' i ⟶
      (ModuleCat.restrictScalars.{u} (algebraMap A A₂)).obj (torModule R A₂ R' i) :=
  ModuleCat.homEquiv.symm (torModuleLinear (R := R) (A := A) (A₂ := A₂) (R' := R') i)

/-- `torModuleMap` is `Tor_i^R(R', ·)` applied to `A → A₂`. -/
theorem torModuleMap_apply (i : ℕ) (x : torModule R A R' i) :
    (torModuleMap (R := R) (A := A) (A₂ := A₂) (R' := R') i).hom x =
      (((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R R')).map
        (ModuleCat.ofHom (IsScalarTower.toAlgHom R A A₂).toLinearMap)).hom x := rfl

/-- The homomorphism of tensor-product algebras `R' ⊗[R] A → R' ⊗[R] A₂` induced by `A → A₂`. -/
private abbrev gmap (R A A₂ R' : Type u) [CommRing R] [CommRing A] [CommRing A₂] [CommRing R']
    [Algebra R A] [Algebra A A₂] [Algebra R A₂] [IsScalarTower R A A₂] [Algebra R R'] :
    (R' ⊗[R] A) →+* (R' ⊗[R] A₂) :=
  TorChangeOfRings.tensorProductMap R R R' A R' A₂ (AlgHom.id R R')
    (IsScalarTower.toAlgHom R A A₂)

/-- `A₂`, viewed as an `A`-module along `A → A₂`: the left tensor factor of the extension of
scalars along `A → A₂`. -/
private abbrev smallLeft (A A₂ : Type u) [CommRing A] [CommRing A₂] [Algebra A A₂] : Type u :=
  ((ModuleCat.restrictScalars.{u, u, u} (algebraMap A A₂)).obj (ModuleCat.of A₂ A₂) : Type u)

/-- `R' ⊗[R] A₂`, viewed as an `R' ⊗[R] A`-module along `gmap`: the left tensor factor of the
extension of scalars along `gmap`. -/
private abbrev bigLeft (R A A₂ R' : Type u) [CommRing R] [CommRing A] [CommRing A₂] [CommRing R']
    [Algebra R A] [Algebra A A₂] [Algebra R A₂] [IsScalarTower R A A₂] [Algebra R R'] :
    Type u :=
  ((ModuleCat.restrictScalars.{u, u, u} (gmap R A A₂ R')).obj
    (ModuleCat.of (R' ⊗[R] A₂) (R' ⊗[R] A₂)) : Type u)

/-- The carrier of `A₂ ⊗_A Tor_i^R(R', A)`. -/
private abbrev smallT (R A A₂ R' : Type u) [CommRing R] [CommRing A] [CommRing A₂] [CommRing R']
    [Algebra R A] [Algebra A A₂] [Algebra R A₂] [IsScalarTower R A A₂] [Algebra R R']
    (i : ℕ) : Type u :=
  ((ModuleCat.extendScalars.{u, u, u} (algebraMap A A₂)).obj (torModule R A R' i) : Type u)

/-- The carrier of `(R' ⊗[R] A₂) ⊗_{R' ⊗[R] A} Tor_i^R(R', A)`. -/
private abbrev bigT (R A A₂ R' : Type u) [CommRing R] [CommRing A] [CommRing A₂] [CommRing R']
    [Algebra R A] [Algebra A A₂] [Algebra R A₂] [IsScalarTower R A A₂] [Algebra R R']
    (i : ℕ) : Type u :=
  ((ModuleCat.extendScalars.{u, u, u} (gmap R A A₂ R')).obj
    (ModuleCat.of (R' ⊗[R] A) (TorChangeOfRings.torObj R i R' A)) : Type u)

/-- A pure tensor of `A₂ ⊗_A Tor_i^R(R', A)`. -/
private abbrev sTmul (i : ℕ) (a₂ : A₂) (t : TorChangeOfRings.torObj R i R' A) :
    smallT R A A₂ R' i :=
  a₂ ⊗ₜ[A, algebraMap A A₂] t

/-- A pure tensor of `(R' ⊗[R] A₂) ⊗_{R' ⊗[R] A} Tor_i^R(R', A)`. -/
private abbrev bTmul (i : ℕ) (z : R' ⊗[R] A₂) (t : TorChangeOfRings.torObj R i R' A) :
    bigT R A A₂ R' i :=
  z ⊗ₜ[R' ⊗[R] A, gmap R A A₂ R'] t

/-- The value of `gmap` on a pure tensor. -/
private lemma gmap_tmul (r' : R') (a : A) :
    gmap R A A₂ R' (r' ⊗ₜ[R] a) = r' ⊗ₜ[R] algebraMap A A₂ a := by
  simp [gmap, TorChangeOfRings.tensorProductMap]

/-- Additivity of `sTmul` in its first argument. -/
private lemma sTmul_add_left (i : ℕ) (a₂ a₂' : A₂) (t : TorChangeOfRings.torObj R i R' A) :
    sTmul (A₂ := A₂) i (a₂ + a₂') t = sTmul i a₂ t + sTmul i a₂' t :=
  TensorProduct.add_tmul _ _ _

/-- Additivity of `sTmul` in its second argument. -/
private lemma sTmul_add_right (i : ℕ) (a₂ : A₂) (t t' : TorChangeOfRings.torObj R i R' A) :
    sTmul (A₂ := A₂) i a₂ (t + t') = sTmul i a₂ t + sTmul i a₂ t' :=
  TensorProduct.tmul_add _ _ _

/-- Additivity of `bTmul` in its first argument. -/
private lemma bTmul_add_left (i : ℕ) (z z' : R' ⊗[R] A₂)
    (t : TorChangeOfRings.torObj R i R' A) :
    bTmul (A := A) i (z + z') t = bTmul (A := A) i z t + bTmul (A := A) i z' t :=
  TensorProduct.add_tmul _ _ _

/-- Additivity of `bTmul` in its second argument. -/
private lemma bTmul_add_right (i : ℕ) (z : R' ⊗[R] A₂)
    (t t' : TorChangeOfRings.torObj R i R' A) :
    bTmul (A := A) i z (t + t') = bTmul (A := A) i z t + bTmul (A := A) i z t' :=
  TensorProduct.tmul_add _ _ _

/-- A pure tensor of `(R' ⊗[R] A₂) ⊗_{R' ⊗[R] A} Tor_i^R(R', A)` with zero first factor. -/
private lemma bTmul_zero_left (i : ℕ) (t : TorChangeOfRings.torObj R i R' A) :
    bTmul (A := A) (A₂ := A₂) i 0 t = 0 :=
  TensorProduct.zero_tmul _ _

/-- Scalars from `A` move across the tensor sign in `A₂ ⊗_A Tor_i^R(R', A)`. -/
private lemma sTmul_smul (i : ℕ) (a : A) (a₂ : A₂) (t : TorChangeOfRings.torObj R i R' A) :
    sTmul (A₂ := A₂) i (algebraMap A A₂ a * a₂) t =
      sTmul (A₂ := A₂) i a₂ (((1 : R') ⊗ₜ[R] a) • t) :=
  (TensorProduct.tmul_smul (R := A) (M := smallLeft A A₂)
    (N := (torModule R A R' i : Type u)) a a₂ t).symm

/-- Scalars from `R' ⊗[R] A` move across the tensor sign in
`(R' ⊗[R] A₂) ⊗_{R' ⊗[R] A} Tor_i^R(R', A)`. -/
private lemma bTmul_smul (i : ℕ) (w : R' ⊗[R] A) (z : R' ⊗[R] A₂)
    (t : TorChangeOfRings.torObj R i R' A) :
    bTmul (A := A) i (gmap R A A₂ R' w * z) t = bTmul (A := A) i z (w • t) :=
  (TensorProduct.tmul_smul (R := R' ⊗[R] A) (M := bigLeft R A A₂ R')
    (N := (TorChangeOfRings.torObj R i R' A)) w z t).symm

/-- One slot of the comparison `A₂ ⊗_A Tor_i^R(R', A) → (R' ⊗[R] A₂) ⊗_{R' ⊗[R] A} Tor_i^R(R', A)`:
for a fixed `a₂` the additive map `t ↦ (1 ⊗ a₂) ⊗ t`. -/
private def forwardAux (i : ℕ) (a₂ : A₂) :
    TorChangeOfRings.torObj R i R' A →+ bigT R A A₂ R' i :=
  AddMonoidHom.mk' (fun t ↦ bTmul (A := A) i ((1 : R') ⊗ₜ[R] a₂) t)
    (fun t t' ↦ bTmul_add_right i _ t t')

/-- Additivity of `forwardAux` in the scalar `a₂`. -/
private lemma forwardAux_add (i : ℕ) (a₂ a₂' : A₂) :
    forwardAux (R := R) (A := A) (R' := R') i (a₂ + a₂') =
      forwardAux (R := R) (A := A) (R' := R') i a₂ +
        forwardAux (R := R) (A := A) (R' := R') i a₂' :=
  AddMonoidHom.ext fun t ↦ by
    change bTmul (A := A) i ((1 : R') ⊗ₜ[R] (a₂ + a₂')) t = _
    rw [TensorProduct.tmul_add, bTmul_add_left]
    rfl

/-- `forwardAux` is balanced over `A`. -/
private lemma forwardAux_smul (i : ℕ) (a : A) (a₂ : A₂)
    (t : TorChangeOfRings.torObj R i R' A) :
    forwardAux (R := R) (A := A) (R' := R') i (algebraMap A A₂ a * a₂) t =
      forwardAux (R := R) (A := A) (R' := R') i a₂ (((1 : R') ⊗ₜ[R] a) • t) := by
  change bTmul (A := A) i ((1 : R') ⊗ₜ[R] (algebraMap A A₂ a * a₂)) t =
    bTmul (A := A) i ((1 : R') ⊗ₜ[R] a₂) (((1 : R') ⊗ₜ[R] a) • t)
  rw [← bTmul_smul, gmap_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

/-- The additive comparison `A₂ ⊗_A Tor_i^R(R', A) → (R' ⊗[R] A₂) ⊗_{R' ⊗[R] A} Tor_i^R(R', A)`
sending `a₂ ⊗ t` to `(1 ⊗ a₂) ⊗ t`. -/
private def comparisonForward (i : ℕ) : smallT R A A₂ R' i →+ bigT R A A₂ R' i :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun a₂ ↦ forwardAux (R := R) (A := A) (A₂ := A₂) (R' := R') i a₂)
      (fun a₂ a₂' ↦ forwardAux_add (R := R) (A := A) (A₂ := A₂) (R' := R') i a₂ a₂'))
    (fun a a₂ t ↦ forwardAux_smul (R := R) (A := A) (A₂ := A₂) (R' := R') i a a₂ t)

/-- The value of `comparisonForward` on a pure tensor. -/
private lemma comparisonForward_sTmul (i : ℕ) (a₂ : A₂)
    (t : TorChangeOfRings.torObj R i R' A) :
    comparisonForward (R := R) (A := A) (A₂ := A₂) (R' := R') i (sTmul i a₂ t) =
      bTmul (A := A) i ((1 : R') ⊗ₜ[R] a₂) t := rfl

/-- Innermost slot of the inverse comparison: for fixed `r'` and `a₂` the additive map
`t ↦ a₂ ⊗ ((r' ⊗ 1) • t)`. -/
private def backwardAux₀ (i : ℕ) (r' : R') (a₂ : A₂) :
    TorChangeOfRings.torObj R i R' A →+ smallT R A A₂ R' i :=
  AddMonoidHom.mk' (fun t ↦ sTmul (A₂ := A₂) i a₂ ((r' ⊗ₜ[R] (1 : A)) • t))
    (fun t t' ↦ by rw [smul_add]; exact sTmul_add_right i a₂ _ _)

/-- `backwardAux₀` as an additive function of the scalar `a₂`. -/
private def backwardAux₁ (i : ℕ) (r' : R') :
    A₂ →+ (TorChangeOfRings.torObj R i R' A →+ smallT R A A₂ R' i) :=
  AddMonoidHom.mk' (fun a₂ ↦ backwardAux₀ (R := R) (A := A) (R' := R') i r' a₂)
    (fun a₂ a₂' ↦ AddMonoidHom.ext fun _ ↦ sTmul_add_left i a₂ a₂' _)

/-- Additivity of `backwardAux₁` in `r'`. -/
private lemma backwardAux₁_add (i : ℕ) (r' r'' : R') :
    backwardAux₁ (R := R) (A := A) (A₂ := A₂) (R' := R') i (r' + r'') =
      backwardAux₁ (R := R) (A := A) (A₂ := A₂) (R' := R') i r' +
        backwardAux₁ (R := R) (A := A) (A₂ := A₂) (R' := R') i r'' :=
  AddMonoidHom.ext fun a₂ ↦ AddMonoidHom.ext fun t ↦ by
    change sTmul (A₂ := A₂) i a₂ (((r' + r'') ⊗ₜ[R] (1 : A)) • t) =
      sTmul (A₂ := A₂) i a₂ ((r' ⊗ₜ[R] (1 : A)) • t) +
        sTmul (A₂ := A₂) i a₂ ((r'' ⊗ₜ[R] (1 : A)) • t)
    rw [TensorProduct.add_tmul, add_smul, sTmul_add_right]

/-- `backwardAux₁` is balanced over `R`. -/
private lemma backwardAux₁_smul (i : ℕ) (r : R) (r' : R') (a₂ : A₂) :
    backwardAux₁ (R := R) (A := A) (A₂ := A₂) (R' := R') i (r • r') a₂ =
      backwardAux₁ (R := R) (A := A) (A₂ := A₂) (R' := R') i r' (r • a₂) :=
  AddMonoidHom.ext fun t ↦ by
    change sTmul (A₂ := A₂) i a₂ (((r • r') ⊗ₜ[R] (1 : A)) • t) =
      sTmul (A₂ := A₂) i (r • a₂) ((r' ⊗ₜ[R] (1 : A)) • t)
    have h1 : ((r • r') ⊗ₜ[R] (1 : A) : R' ⊗[R] A) = r' ⊗ₜ[R] algebraMap R A r := by
      rw [TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]
    have h2 : (r • a₂ : A₂) = algebraMap A A₂ (algebraMap R A r) * a₂ := by
      rw [← IsScalarTower.algebraMap_apply, Algebra.smul_def]
    rw [h1, h2, sTmul_smul, ← mul_smul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

/-- The bilinear datum of the inverse comparison: `(r' ⊗ a₂, t) ↦ a₂ ⊗ ((r' ⊗ 1) • t)`. -/
private def backwardAux (i : ℕ) :
    (R' ⊗[R] A₂) →+ (TorChangeOfRings.torObj R i R' A →+ smallT R A A₂ R' i) :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun r' ↦ backwardAux₁ (R := R) (A := A) (A₂ := A₂) (R' := R') i r')
      (fun r' r'' ↦ backwardAux₁_add i r' r''))
    (fun r r' a₂ ↦ backwardAux₁_smul i r r' a₂)

/-- The value of `backwardAux` on a pure tensor. -/
private lemma backwardAux_tmul (i : ℕ) (r' : R') (a₂ : A₂)
    (t : TorChangeOfRings.torObj R i R' A) :
    backwardAux (R := R) (A := A) (A₂ := A₂) (R' := R') i (r' ⊗ₜ[R] a₂) t =
      sTmul (A₂ := A₂) i a₂ ((r' ⊗ₜ[R] (1 : A)) • t) := rfl

/-- `backwardAux` is balanced over `R' ⊗[R] A`. -/
private lemma backwardAux_smul (i : ℕ) (w : R' ⊗[R] A) (z : R' ⊗[R] A₂)
    (t : TorChangeOfRings.torObj R i R' A) :
    backwardAux (R := R) (A := A) (A₂ := A₂) (R' := R') i (gmap R A A₂ R' w * z) t =
      backwardAux (R := R) (A := A) (A₂ := A₂) (R' := R') i z (w • t) := by
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero, zero_mul, zero_smul, AddMonoidHom.zero_apply]
  | tmul r' a =>
    induction z using TensorProduct.induction_on with
    | zero => simp only [mul_zero, map_zero, AddMonoidHom.zero_apply]
    | tmul s' a₂ =>
      rw [gmap_tmul, Algebra.TensorProduct.tmul_mul_tmul, backwardAux_tmul, backwardAux_tmul,
        sTmul_smul, ← mul_smul, ← mul_smul, Algebra.TensorProduct.tmul_mul_tmul,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, one_mul, mul_comm s' r']
    | add z z' hz hz' =>
      rw [mul_add, map_add, AddMonoidHom.add_apply, hz, hz', map_add, AddMonoidHom.add_apply]
  | add w w' hw hw' =>
    rw [map_add, add_mul, map_add, AddMonoidHom.add_apply, hw, hw', add_smul, map_add]

/-- The additive comparison `(R' ⊗[R] A₂) ⊗_{R' ⊗[R] A} Tor_i^R(R', A) → A₂ ⊗_A Tor_i^R(R', A)`
sending `(r' ⊗ a₂) ⊗ t` to `a₂ ⊗ ((r' ⊗ 1) • t)`. -/
private def comparisonBackward (i : ℕ) : bigT R A A₂ R' i →+ smallT R A A₂ R' i :=
  TensorProduct.liftAddHom (backwardAux (R := R) (A := A) (A₂ := A₂) (R' := R') i)
    (fun w z t ↦ backwardAux_smul (R := R) (A := A) (A₂ := A₂) (R' := R') i w z t)

/-- The value of `comparisonBackward` on a pure tensor. -/
private lemma comparisonBackward_bTmul (i : ℕ) (z : R' ⊗[R] A₂)
    (t : TorChangeOfRings.torObj R i R' A) :
    comparisonBackward (R := R) (A := A) (A₂ := A₂) (R' := R') i (bTmul i z t) =
      backwardAux (R := R) (A := A) (A₂ := A₂) (R' := R') i z t := rfl

/-- `comparisonBackward` undoes `comparisonForward` on a pure tensor. -/
private lemma comparisonBackward_forward_sTmul (i : ℕ) (a₂ : A₂)
    (t : TorChangeOfRings.torObj R i R' A) :
    comparisonBackward (R := R) (A := A) (A₂ := A₂) (R' := R') i
        (comparisonForward i (sTmul i a₂ t)) = sTmul i a₂ t := by
  rw [comparisonForward_sTmul, comparisonBackward_bTmul, backwardAux_tmul,
    ← Algebra.TensorProduct.one_def, one_smul]

/-- `comparisonForward` undoes `comparisonBackward` on a pure tensor. -/
private lemma comparisonForward_backward_bTmul (i : ℕ) (z : R' ⊗[R] A₂)
    (t : TorChangeOfRings.torObj R i R' A) :
    comparisonForward (R := R) (A := A) (A₂ := A₂) (R' := R') i
        (comparisonBackward i (bTmul i z t)) = bTmul i z t := by
  induction z using TensorProduct.induction_on with
  | zero => rw [bTmul_zero_left, map_zero, map_zero]
  | tmul r' a₂ =>
    rw [comparisonBackward_bTmul, backwardAux_tmul, comparisonForward_sTmul, ← bTmul_smul,
      gmap_tmul, map_one, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  | add z z' hz hz' => rw [bTmul_add_left, map_add, map_add, hz, hz']

/-- Additive maps out of a tensor product are equal when they agree on pure tensors. -/
private lemma tensor_addMonoidHom_ext {S M N X : Type*} [CommRing S] [AddCommGroup M]
    [Module S M] [AddCommGroup N] [Module S N] [AddCommGroup X] {f g : M ⊗[S] N →+ X}
    (h : ∀ m n, f (m ⊗ₜ n) = g (m ⊗ₜ n)) : f = g :=
  AddMonoidHom.ext fun x ↦ TensorProduct.induction_on x (by simp) h
    (fun x y hx hy ↦ by simp [hx, hy])

/-- `comparisonBackward` is a left inverse of `comparisonForward`. -/
private lemma comparisonBackward_forward (i : ℕ) (x : smallT R A A₂ R' i) :
    comparisonBackward (R := R) (A := A) (A₂ := A₂) (R' := R') i
      (comparisonForward i x) = x := by
  exact DFunLike.congr_fun (tensor_addMonoidHom_ext (S := A) (M := smallLeft A A₂)
    (N := (torModule R A R' i : Type u)) (f := (comparisonBackward (R := R) (A := A)
    (A₂ := A₂) (R' := R') i).comp (comparisonForward i)) (g := AddMonoidHom.id _)
    (fun a₂ t ↦ comparisonBackward_forward_sTmul (R := R) (A := A) (A₂ := A₂) (R' := R') i a₂ t)) x

/-- `comparisonBackward` is a right inverse of `comparisonForward`. -/
private lemma comparisonForward_backward (i : ℕ) (y : bigT R A A₂ R' i) :
    comparisonForward (R := R) (A := A) (A₂ := A₂) (R' := R') i
      (comparisonBackward i y) = y :=
  DFunLike.congr_fun (tensor_addMonoidHom_ext (S := R' ⊗[R] A) (M := bigLeft R A A₂ R')
    (N := (TorChangeOfRings.torObj R i R' A)) (f := (comparisonForward (R := R) (A := A)
    (A₂ := A₂) (R' := R') i).comp (comparisonBackward i)) (g := AddMonoidHom.id _)
    (fun z t ↦ comparisonForward_backward_bTmul (R := R) (A := A) (A₂ := A₂) (R' := R') i z t)) y

/-- The scalar-extended change-of-rings map on a pure tensor: it is the scalar multiple of the
change-of-rings map itself. -/
private lemma extensionMap_bTmul (i : ℕ) (z : R' ⊗[R] A₂)
    (t : TorChangeOfRings.torObj R i R' A) :
    ((TorChangeOfRings.canonicalSystem TorChangeOfRings.canonicalSystem_nonempty).1.extensionMap
        R R R' A R' A₂ i (AlgHom.id R R') (IsScalarTower.toAlgHom R A A₂)).hom
      (bTmul (A := A) i z t) =
      z • (TorChangeOfRings.canonicalSystem TorChangeOfRings.canonicalSystem_nonempty).1.map
        R R R' A R' A₂ i (AlgHom.id R R') (IsScalarTower.toAlgHom R A A₂) t := by
  have h0 : z • bTmul (A := A) (A₂ := A₂) i (1 : R' ⊗[R] A₂) t =
      bTmul (A := A) (A₂ := A₂) i (z * 1) t := rfl
  rw [mul_one] at h0
  rw [← h0, map_smul]
  exact congrArg (fun y ↦ z • y)
    ((TorChangeOfRings.canonicalLaws
      TorChangeOfRings.canonicalSystem_nonempty).extension_one_tmul
      R R R' A R' A₂ i (AlgHom.id R R') (IsScalarTower.toAlgHom R A A₂) t)

/-- The base-change comparison of the statement, evaluated on a pure tensor. -/
private lemma theta_sTmul (i : ℕ) (a₂ : A₂) (t : TorChangeOfRings.torObj R i R' A) :
    ((ModuleCat.extendScalars.{u, u, u} (algebraMap A A₂)).map
          (torModuleMap (R := R) (A := A) (A₂ := A₂) (R' := R') i) ≫
        (ModuleCat.extendRestrictScalarsAdj.{u, u, u} (algebraMap A A₂)).counit.app
          (torModule R A₂ R' i)).hom (sTmul i a₂ t) =
      ((1 : R') ⊗ₜ[R] a₂) •
        (((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R R')).map
          (ModuleCat.ofHom (IsScalarTower.toAlgHom R A A₂).toLinearMap)).hom t := rfl

/-- On a pure tensor, the base-change comparison of the statement is the scalar-extended
change-of-rings map precomposed with `comparisonForward`. -/
private lemma theta_eq_extensionMap_sTmul (i : ℕ) (a₂ : A₂)
    (t : TorChangeOfRings.torObj R i R' A) :
    ((ModuleCat.extendScalars.{u, u, u} (algebraMap A A₂)).map
          (torModuleMap (R := R) (A := A) (A₂ := A₂) (R' := R') i) ≫
        (ModuleCat.extendRestrictScalarsAdj.{u, u, u} (algebraMap A A₂)).counit.app
          (torModule R A₂ R' i)).hom (sTmul i a₂ t) =
      ((TorChangeOfRings.canonicalSystem
          TorChangeOfRings.canonicalSystem_nonempty).1.extensionMap
          R R R' A R' A₂ i (AlgHom.id R R') (IsScalarTower.toAlgHom R A A₂)).hom
        (comparisonForward (R := R) (A := A) (A₂ := A₂) (R' := R') i (sTmul i a₂ t)) := by
  rw [theta_sTmul, comparisonForward_sTmul, extensionMap_bTmul,
    systemMap_eq_torMap R R' A A₂ (IsScalarTower.toAlgHom R A A₂) i t]

/-- **Flat base change for `Tor` in the second variable.** For `A → A₂` flat the canonical
`A₂`-linear map `A₂ ⊗_A Tor_i^R(R', A) ⟶ Tor_i^R(R', A₂)` is an isomorphism. -/
theorem isIso_torModuleFlatBaseChange (hflat : (algebraMap A A₂).Flat) (i : ℕ) :
    IsIso ((ModuleCat.extendScalars.{u, u, u} (algebraMap A A₂)).map
        (torModuleMap (R := R) (A := A) (A₂ := A₂) (R' := R') i) ≫
      (ModuleCat.extendRestrictScalarsAdj.{u, u, u} (algebraMap A A₂)).counit.app
        (torModule R A₂ R' i)) := by
  have hE : IsIso ((TorChangeOfRings.canonicalSystem
      TorChangeOfRings.canonicalSystem_nonempty).1.extensionMap
      R R R' A R' A₂ i (AlgHom.id R R') (IsScalarTower.toAlgHom R A A₂)) :=
    TorChangeOfRings.isIso_extensionMap_of_flat_algebra
      TorChangeOfRings.canonicalSystem_nonempty R R' A R' A₂ (AlgHom.id R R')
      (IsScalarTower.toAlgHom R A A₂) (RingHom.Flat.id R') hflat i
  have hEbij := (ConcreteCategory.isIso_iff_bijective _).mp hE
  have hpi : Function.Bijective
      (comparisonForward (R := R) (A := A) (A₂ := A₂) (R' := R') i) :=
    Function.bijective_iff_has_inverse.mpr
      ⟨comparisonBackward (R := R) (A := A) (A₂ := A₂) (R' := R') i,
        comparisonBackward_forward i, comparisonForward_backward i⟩
  have hcomp : ∀ x : smallT R A A₂ R' i,
      ((ModuleCat.extendScalars.{u, u, u} (algebraMap A A₂)).map
            (torModuleMap (R := R) (A := A) (A₂ := A₂) (R' := R') i) ≫
          (ModuleCat.extendRestrictScalarsAdj.{u, u, u} (algebraMap A A₂)).counit.app
            (torModule R A₂ R' i)).hom x =
        ((TorChangeOfRings.canonicalSystem
            TorChangeOfRings.canonicalSystem_nonempty).1.extensionMap
            R R R' A R' A₂ i (AlgHom.id R R') (IsScalarTower.toAlgHom R A A₂)).hom
          (comparisonForward (R := R) (A := A) (A₂ := A₂) (R' := R') i x) := by
    intro x
    refine TensorProduct.induction_on x ?_ ?_ ?_
    · exact (map_zero _).trans ((congrArg _ (map_zero
        (comparisonForward (R := R) (A := A) (A₂ := A₂) (R' := R') i))).trans
        (map_zero _)).symm
    · intro a₂ t
      exact theta_eq_extensionMap_sTmul (R := R) (A := A) (A₂ := A₂) (R' := R') i a₂ t
    · intro x y hx hy
      refine (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans ?_)
      exact ((congrArg _ (map_add
        (comparisonForward (R := R) (A := A) (A₂ := A₂) (R' := R') i) x y)).trans
        (map_add _ _ _)).symm
  refine (ConcreteCategory.isIso_iff_bijective _).mpr ⟨?_, ?_⟩
  · intro x y hxy
    exact hpi.1 (hEbij.1 (((hcomp x).symm.trans hxy).trans (hcomp y)))
  · intro y
    obtain ⟨x, hx⟩ := (hEbij.comp hpi).2 y
    exact ⟨x, (hcomp x).trans hx⟩

end RingTheory.TorIndependence

end
