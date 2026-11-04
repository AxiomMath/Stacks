module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffinePointwiseCriterion
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.PureSpreadoutLocalizedFibre

/-!
# The model of a square of rings under localization

Let `R → A`, `R → R'`, `A → B`, `R' → B` be a square of rings and `R₁ → A₁`, `R₁ → R'₁`,
`A₁ → B`, `R'₁ → B` a second one, with localizations `R → R₁`, `A → A₁`, `R₀ → R₀₁` compatible
with both.  A model `(R₀, F)` of the first square localizes to a model `(R₀₁, R₀₁ ⊗_{R₀} F)` of
the second, and the model map of the second square, read over `A ⊗_R R₀`, is the localization of
the model map of the first.  Consequently the cohomology of the model map of the first square is
a localization at the elements becoming units in `B` exactly when that of the second is.

## Main definitions

* `RingTheory.TorIndependence.modelComplexLocMap`: the localization map from the model complex of
  the first square to that of the second.

## Main results

* `RingTheory.TorIndependence.modelKappa_modelComplexLocMap`: the model map of the second square
  composed with `modelComplexLocMap` is the model map of the first.
* `RingTheory.TorIndependence.isLocalizedModule_modelKappa_iff_local`: the cohomology of the model
  map of the first square is a localization at the elements becoming units in `B` if and only if
  that of the second is.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct ChangeOfRings
open CochainComplex.DerivedExtensionScalars

universe u

namespace RingTheory.TorIndependence

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Algebra.TensorProduct.rightAlgebra

section TensorChange

variable {B₀ B₁ : Type u} [CommRing B₀] [CommRing B₁] [Algebra B₀ B₁]

variable (B₀ B₁) in
/-- The unit `Z ⟶ B₁ ⊗_{B₀} Z` of base change, on complexes, read over `B₀`. -/
def baseChangeUnitComplex (Z : CochainComplex (ModuleCat.{u} B₀) ℤ) :
    Z ⟶ ((ModuleCat.restrictScalars (algebraMap B₀ B₁)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (((baseChangeFunctor B₀ B₁).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj Z) where
  f n := ModuleCat.ofHom (X := Z.X n) (Y := (ModuleCat.restrictScalars (algebraMap B₀ B₁)).obj
      ((baseChangeFunctor B₀ B₁).obj (Z.X n)))
    { toFun := fun x => ((1 : B₁) ⊗ₜ[B₀] x : B₁ ⊗[B₀] Z.X n)
      map_add' := fun x y => TensorProduct.tmul_add _ _ _
      map_smul' := fun b x => by
        change ((1 : B₁) ⊗ₜ[B₀] (b • x) : B₁ ⊗[B₀] Z.X n) =
          (algebraMap B₀ B₁ b) • ((1 : B₁) ⊗ₜ[B₀] x : B₁ ⊗[B₀] Z.X n)
        rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul', Algebra.smul_def, smul_eq_mul] }
  comm' i j _ := ModuleCat.hom_ext (LinearMap.ext fun x => rfl)

/-- In degree `n`, `baseChangeUnitComplex` sends `x` to `1 ⊗ x`. -/
theorem baseChangeUnitComplex_f_apply (Z : CochainComplex (ModuleCat.{u} B₀) ℤ) (n : ℤ)
    (x : Z.X n) :
    ((baseChangeUnitComplex B₀ B₁ Z).f n).hom x = ((1 : B₁) ⊗ₜ[B₀] x : B₁ ⊗[B₀] Z.X n) :=
  rfl

variable {X Y : CochainComplex (ModuleCat.{u} B₀) ℤ} {X₁ Y₁ : CochainComplex (ModuleCat.{u} B₁) ℤ}
  (eX : ((baseChangeFunctor B₀ B₁).mapHomologicalComplex (ComplexShape.up ℤ)).obj X ≅ X₁)
  (eY : ((baseChangeFunctor B₀ B₁).mapHomologicalComplex (ComplexShape.up ℤ)).obj Y ≅ Y₁)

/-- **The comparison of tensor complexes along a change of rings**:
`X ⊗_{B₀} Y ⟶ X₁ ⊗_{B₁} Y₁`, `x ⊗ y ↦ eX(1 ⊗ x) ⊗ eY(1 ⊗ y)`, read over `B₀`. -/
def tensorChangeMap : X ⊗ Y ⟶ ((ModuleCat.restrictScalars (algebraMap B₀ B₁)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj (X₁ ⊗ Y₁) :=
  baseChangeUnitComplex B₀ B₁ (X ⊗ Y) ≫
    ((ModuleCat.restrictScalars (algebraMap B₀ B₁)).mapHomologicalComplex (ComplexShape.up ℤ)).map
      ((bcComplexTensorIso B₀ B₁ X Y).hom ≫ MonoidalCategory.tensorHom eX.hom eY.hom)

/-- On the summand of degree `(p, q)`, `tensorChangeMap eX eY` sends `x ⊗ y` to
`eX(1 ⊗ x) ⊗ eY(1 ⊗ y)`. -/
theorem tensorChangeMap_ι_apply (p q n : ℤ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n)
    (x : X.X p) (y : Y.X q) :
    ((tensorChangeMap eX eY).f n).hom ((HomologicalComplex.ιMapBifunctor X Y
        (curriedTensor (ModuleCat.{u} B₀)) (ComplexShape.up ℤ) p q n h).hom (x ⊗ₜ[B₀] y)) =
      (HomologicalComplex.ιMapBifunctor X₁ Y₁ (curriedTensor (ModuleCat.{u} B₁))
        (ComplexShape.up ℤ) p q n h).hom
          ((eX.hom.f p).hom ((1 : B₁) ⊗ₜ[B₀] x) ⊗ₜ[B₁] (eY.hom.f q).hom ((1 : B₁) ⊗ₜ[B₀] y)) := by
  have h1 := congrArg (fun φ => φ.hom ((1 : B₁) ⊗ₜ[B₀] (x ⊗ₜ[B₀] y)))
    (ι_bcComplexTensorIso_hom_assoc B₀ B₁ X Y p q n h
      ((MonoidalCategory.tensorHom eX.hom eY.hom).f n))
  have h2 := congrArg (fun φ => φ.hom (((1 : B₁) ⊗ₜ[B₀] x) ⊗ₜ[B₁] ((1 : B₁) ⊗ₜ[B₀] y)))
    (HomologicalComplex.ι_mapBifunctorMap eX.hom eY.hom (curriedTensor (ModuleCat.{u} B₁))
      (ComplexShape.up ℤ) p q n h)
  exact h1.trans h2

/-- **The comparison is a localization in every degree** when `B₁` is a localization of `B₀`. -/
theorem isLocalizedModule_tensorChangeMap (T : Submonoid B₀) [IsLocalization T B₁] (n : ℤ) :
    IsLocalizedModule T ((tensorChangeMap eX eY).f n).hom := by
  let W := (X ⊗ Y).X n
  let e1 : (B₁ ⊗[B₀] W) ≃ₗ[B₀] (ModuleCat.restrictScalars (algebraMap B₀ B₁)).obj
      ((baseChangeFunctor B₀ B₁).obj W) :=
    { toFun := fun t => t
      invFun := fun t => t
      map_add' := fun _ _ => rfl
      map_smul' := fun b t => (algebraMap_smul B₁ b t).symm
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h1 : IsLocalizedModule T (e1.toLinearMap ∘ₗ TensorProduct.mk B₀ B₁ W 1) :=
    IsLocalizedModule.of_linearEquiv T _ e1
  let e2 := (asIso ((((ModuleCat.restrictScalars (algebraMap B₀ B₁)).mapHomologicalComplex
    (ComplexShape.up ℤ)).map ((bcComplexTensorIso B₀ B₁ X Y).hom ≫
      MonoidalCategory.tensorHom eX.hom eY.hom)).f n)).toLinearEquiv
  convert IsLocalizedModule.of_linearEquiv T (e1.toLinearMap ∘ₗ TensorProduct.mk B₀ B₁ W 1) e2
    using 1
  exact LinearMap.ext fun x => rfl

end TensorChange



section Cancel

variable {C D C₁ E : Type u} [CommRing C] [CommRing D] [CommRing C₁] [CommRing E]
  [Algebra C D] [Algebra C C₁] [Algebra C E] [Algebra D E] [Algebra C₁ E]
  [IsScalarTower C D E] [IsScalarTower C C₁ E]

/-- `E ⊗_D (D ⊗_C X) ≅ E ⊗_{C₁} X₁` for an identification `C₁ ⊗_C X ≅ X₁`. -/
def cancelBaseChangeEquiv {X : ModuleCat.{u} C} {X₁ : ModuleCat.{u} C₁}
    (e : (baseChangeFunctor C C₁).obj X ≅ X₁) :
    (baseChangeFunctor D E).obj ((baseChangeFunctor C D).obj X) ≃ₗ[E]
      (baseChangeFunctor C₁ E).obj X₁ :=
  TensorProduct.AlgebraTensorModule.cancelBaseChange C D E E X ≪≫ₗ
    (TensorProduct.AlgebraTensorModule.cancelBaseChange C C₁ E E X).symm ≪≫ₗ
      TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl E E) e.toLinearEquiv

/-- `cancelBaseChangeEquiv e` sends `y ⊗ (d ⊗ x)` to `(d • y) ⊗ e(1 ⊗ x)`. -/
theorem cancelBaseChangeEquiv_tmul {X : ModuleCat.{u} C} {X₁ : ModuleCat.{u} C₁}
    (e : (baseChangeFunctor C C₁).obj X ≅ X₁) (y : E) (d : D) (x : X) :
    cancelBaseChangeEquiv (D := D) (E := E) e (y ⊗ₜ[D] (d ⊗ₜ[C] x)) =
      (d • y) ⊗ₜ[C₁] (e.hom.hom ((1 : C₁) ⊗ₜ[C] x)) :=
  rfl

omit [Algebra C C₁] [Algebra C E] [Algebra C₁ E] [IsScalarTower C D E]
  [IsScalarTower C C₁ E] in
/-- Maps out of `E ⊗_D (D ⊗_C X)` agree as soon as they agree on the elements `y ⊗ (d ⊗ x)`. -/
theorem baseChangeFunctor_hom_ext₂ {X : ModuleCat.{u} C} {M : ModuleCat.{u} E}
    {φ ψ : (baseChangeFunctor D E).obj ((baseChangeFunctor C D).obj X) ⟶ M}
    (h : ∀ (y : E) (d : D) (x : X), φ.hom (y ⊗ₜ[D] (d ⊗ₜ[C] x)) = ψ.hom (y ⊗ₜ[D] (d ⊗ₜ[C] x))) :
    φ = ψ := by
  apply baseChangeFunctor_hom_ext
  intro y t
  induction t using TensorProduct.induction_on with
  | zero =>
    exact (congrArg φ.hom (TensorProduct.tmul_zero (D ⊗[C] X) y)).trans ((map_zero φ.hom).trans
      ((map_zero ψ.hom).symm.trans (congrArg ψ.hom (TensorProduct.tmul_zero (D ⊗[C] X) y).symm)))
  | add t t' ht ht' =>
    exact (congrArg φ.hom (TensorProduct.tmul_add y t t')).trans ((map_add φ.hom _ _).trans
      ((congrArg₂ (· + ·) ht ht').trans ((map_add ψ.hom _ _).symm.trans
        (congrArg ψ.hom (TensorProduct.tmul_add y t t').symm))))
  | tmul d x => exact h y d x

/-- `E ⊗_D (D ⊗_C N) ≅ E ⊗_{C₁} N₁` on complexes, for an identification `C₁ ⊗_C N ≅ N₁`. -/
def cancelBaseChangeComplexIso {N : CochainComplex (ModuleCat.{u} C) ℤ}
    {N₁ : CochainComplex (ModuleCat.{u} C₁) ℤ}
    (e : ((baseChangeFunctor C C₁).mapHomologicalComplex (ComplexShape.up ℤ)).obj N ≅ N₁) :
    ((baseChangeFunctor D E).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((baseChangeFunctor C D).mapHomologicalComplex (ComplexShape.up ℤ)).obj N) ≅
      ((baseChangeFunctor C₁ E).mapHomologicalComplex (ComplexShape.up ℤ)).obj N₁ :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p => (cancelBaseChangeEquiv (D := D) (E := E)
      ((HomologicalComplex.eval _ _ p).mapIso e)).toModuleIso) (by
    intro p q _
    apply baseChangeFunctor_hom_ext₂
    intro y d x
    have hc := congrArg (fun φ => φ.hom ((1 : C₁) ⊗ₜ[C] x)) (e.hom.comm p q)
    change (d • y) ⊗ₜ[C₁] (N₁.d p q).hom ((e.hom.f p).hom ((1 : C₁) ⊗ₜ[C] x)) =
      (d • y) ⊗ₜ[C₁] (e.hom.f q).hom ((1 : C₁) ⊗ₜ[C] (N.d p q).hom x)
    exact congrArg _ hc)

/-- In degree `p`, `cancelBaseChangeComplexIso e` sends `y ⊗ (d ⊗ x)` to `(d • y) ⊗ e(1 ⊗ x)`. -/
theorem cancelBaseChangeComplexIso_hom_f_tmul {N : CochainComplex (ModuleCat.{u} C) ℤ}
    {N₁ : CochainComplex (ModuleCat.{u} C₁) ℤ}
    (e : ((baseChangeFunctor C C₁).mapHomologicalComplex (ComplexShape.up ℤ)).obj N ≅ N₁)
    (p : ℤ) (y : E) (d : D) (x : N.X p) :
    ((cancelBaseChangeComplexIso (D := D) (E := E) e).hom.f p).hom (y ⊗ₜ[D] (d ⊗ₜ[C] x)) =
      (d • y) ⊗ₜ[C₁] ((e.hom.f p).hom ((1 : C₁) ⊗ₜ[C] x)) :=
  rfl

end Cancel

section ModelElement

variable {R A R' A' R₀ : Type u}
  [CommRing R] [CommRing A] [CommRing R'] [CommRing A'] [CommRing R₀]
  [Algebra R A] [Algebra R R'] [Algebra R A'] [Algebra A A'] [Algebra R' A']
  [IsScalarTower R A A'] [IsScalarTower R R' A']
  [Algebra R R₀] [Algebra R₀ R'] [IsScalarTower R R₀ R']

local notation "B₀" => A ⊗[R] R₀

variable (F : CochainComplex (ModuleCat.{u} R₀) ℤ)
  (ε : F ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} R₀) 0).obj (ModuleCat.of R₀ R'))

/-- On the summand of degree `(p, 0)`, the model map sends `(b ⊗ x) ⊗ (b' ⊗ w)` to
`(b' · ε(w) · b) ⊗ x`. -/
theorem modelMapE_ι_tmul (M : CochainComplex (ModuleCat.{u} A) ℤ) (p : ℤ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, 0) = p)
    (b : B₀) (x : M.X p) (b' : B₀) (w : F.X 0) :
    ((modelMapE (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) F ε M).f p).hom
        ((HomologicalComplex.ιMapBifunctor
          (((baseChangeFunctor A B₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)
          (((baseChangeFunctor R₀ B₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj F)
          (curriedTensor (ModuleCat.{u} B₀)) (ComplexShape.up ℤ) p 0 p h).hom
          ((b ⊗ₜ[A] x) ⊗ₜ[B₀] (b' ⊗ₜ[R₀] w))) =
      ((modelRingMap R A R' A' R₀ b' * algebraMap R' A' (augmentation F ε w) *
        modelRingMap R A R' A' R₀ b) ⊗ₜ[A, algebraMap A A'] x :
          (ModuleCat.extendScalars (algebraMap A A')).obj (M.X p)) := by
  refine (congrArg (fun φ => φ.hom ((b ⊗ₜ[A] x) ⊗ₜ[B₀] (b' ⊗ₜ[R₀] w)))
    (ι_modelMapE (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) F ε M p h)).trans ?_
  show (TensorProduct.congr (algebraRestrictLinearEquiv A A') (LinearEquiv.refl A (M.X p)))
      (modelTermAdd (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) (M.X p)
        ((b ⊗ₜ[A] x) ⊗ₜ[B₀] (b' ⊗ₜ[R₀] augmentation F ε w))) = _
  rw [modelTermAdd_tmul, TensorProduct.congr_tmul]
  rfl

/-- The model map vanishes on the summands of degree `(p, q)` with `q ≠ 0`. -/
theorem modelMapE_ι_eq_zero (M : CochainComplex (ModuleCat.{u} A) ℤ) (p q n : ℤ) (hq : q ≠ 0)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n) :
    HomologicalComplex.ιMapBifunctor
        (((baseChangeFunctor A B₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)
        (((baseChangeFunctor R₀ B₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj F)
        (curriedTensor (ModuleCat.{u} B₀)) (ComplexShape.up ℤ) p q n h ≫
      (modelMapE (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) F ε M).f n = 0 :=
  ι_modelMapE_eq_zero (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) F ε M p q n hq h

end ModelElement

/-- In the extension of scalars, `c ⊗ m = c • (1 ⊗ m)`. -/
private theorem extendScalars_tmul_eq_smul {A S : Type u} [CommRing A] [CommRing S] [Algebra A S]
    {M : ModuleCat.{u} A} (c : S) (m : M)
    (y : (ModuleCat.extendScalars (algebraMap A S)).obj M)
    (hy : y = (1 : S) ⊗ₜ[A,algebraMap A S] m) :
    (c ⊗ₜ[A, algebraMap A S] m : (ModuleCat.extendScalars (algebraMap A S)).obj M) = c • y := by
  subst hy
  change _ = (c * 1) ⊗ₜ[A, algebraMap A S] m
  rw [mul_one]
  rfl

section Change

variable {R A R' B R₁ A₁ R'₁ R₀ R₀₁ : Type u} [CommRing R] [CommRing A] [CommRing R'] [CommRing B]
  [CommRing R₁] [CommRing A₁] [CommRing R'₁] [CommRing R₀] [CommRing R₀₁]
  [Algebra R A] [Algebra R R'] [Algebra R B] [Algebra A B] [Algebra R' B]
  [IsScalarTower R A B] [IsScalarTower R R' B]
  [Algebra R₁ A₁] [Algebra R₁ R'₁] [Algebra R₁ B] [Algebra A₁ B] [Algebra R'₁ B]
  [IsScalarTower R₁ A₁ B] [IsScalarTower R₁ R'₁ B]
  [Algebra R R₁] [Algebra A A₁] [Algebra R' R'₁] [Algebra R A₁]
  [IsScalarTower R A A₁] [IsScalarTower R R₁ A₁] [IsScalarTower A A₁ B] [IsScalarTower R' R'₁ B]
  [Algebra R R₀] [Algebra R₀ R'] [IsScalarTower R R₀ R']
  [Algebra R₁ R₀₁] [Algebra R₀₁ R'₁] [IsScalarTower R₁ R₀₁ R'₁]
  [Algebra R₀ R₀₁] [Algebra R R₀₁] [IsScalarTower R R₀ R₀₁] [IsScalarTower R R₁ R₀₁]

local notation "B₀" => A ⊗[R] R₀
local notation "B₁" => A₁ ⊗[R₁] R₀₁

local notation "β" => IsLocalization.tensorLocalizationMap R R₁ A A₁ R₀ R₀₁

/-- The ring map `A₁ ⊗_{R₁} R₀₁ → B` of the second square composed with the localization map
`A ⊗_R R₀ → A₁ ⊗_{R₁} R₀₁` is the ring map `A ⊗_R R₀ → B` of the first square. -/
theorem modelRingMap_tensorLocalizationMap
    (hσ : ∀ x : R₀, algebraMap R₀₁ R'₁ (algebraMap R₀ R₀₁ x) =
      algebraMap R' R'₁ (algebraMap R₀ R' x)) (b : B₀) :
    modelRingMap R₁ A₁ R'₁ B R₀₁ (β b) = modelRingMap R A R' B R₀ b := by
  induction b using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]
  | tmul a r =>
    rw [IsLocalization.tensorLocalizationMap_tmul, modelRingMap_tmul, modelRingMap_tmul, hσ,
      ← IsScalarTower.algebraMap_apply A A₁ B, ← IsScalarTower.algebraMap_apply R' R'₁ B]

variable (R R₁ A A₁ R₀ R₀₁) in
/-- `A₁ ⊗_{R₁} R₀₁` as an algebra over `A ⊗_R R₀`. -/
abbrev modelLocAlgebra : Algebra B₀ B₁ :=
  (IsLocalization.tensorLocalizationMap R R₁ A A₁ R₀ R₀₁).toAlgebra

variable (R₁ A₁ R₀ R₀₁) in
/-- `A₁ ⊗_{R₁} R₀₁` as an algebra over `R₀`. -/
abbrev modelLocAlgebraBase : Algebra R₀ B₁ :=
  ((algebraMap R₀₁ B₁).comp (algebraMap R₀ R₀₁)).toAlgebra

attribute [local instance] modelLocAlgebra modelLocAlgebraBase

/-- The scalar tower `R₀ → R₀₁ → A₁ ⊗_{R₁} R₀₁`. -/
instance : IsScalarTower R₀ R₀₁ B₁ := IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The scalar tower `A → A ⊗_R R₀ → A₁ ⊗_{R₁} R₀₁`. -/
instance : IsScalarTower A B₀ B₁ := IsScalarTower.of_algebraMap_eq fun a => by
  change _ = β (a ⊗ₜ[R] (1 : R₀))
  rw [IsLocalization.tensorLocalizationMap_tmul, map_one]
  rfl

/-- The scalar tower `R₀ → A ⊗_R R₀ → A₁ ⊗_{R₁} R₀₁`. -/
instance : IsScalarTower R₀ B₀ B₁ := IsScalarTower.of_algebraMap_eq fun r => by
  change _ = β ((1 : A) ⊗ₜ[R] r)
  rw [IsLocalization.tensorLocalizationMap_tmul, map_one]
  rfl

variable {N : CochainComplex (ModuleCat.{u} A) ℤ} {N₁ : CochainComplex (ModuleCat.{u} A₁) ℤ}
  (eN : ((baseChangeFunctor A A₁).mapHomologicalComplex (ComplexShape.up ℤ)).obj N ≅ N₁)
  (F : CochainComplex (ModuleCat.{u} R₀) ℤ)

variable (R₀₁) in
/-- **The localization of the model complex**:
`(B₀ ⊗_A N) ⊗_{B₀} (B₀ ⊗_{R₀} F) ⟶ (B₁ ⊗_{A₁} N₁) ⊗_{B₁} (B₁ ⊗_{R₀₁} (R₀₁ ⊗_{R₀} F))`. -/
def modelComplexLocMap :
    modelComplex (R := R) A F N ⟶
      ((ModuleCat.restrictScalars (algebraMap B₀ B₁)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (modelComplex (R := R₁) A₁
        (((baseChangeFunctor R₀ R₀₁).mapHomologicalComplex (ComplexShape.up ℤ)).obj F) N₁) :=
  tensorChangeMap (cancelBaseChangeComplexIso (C := A) (D := B₀) (C₁ := A₁) (E := B₁) eN)
    (cancelBaseChangeComplexIso (C := R₀) (D := B₀) (C₁ := R₀₁) (E := B₁) (Iso.refl _))

/-- In every degree, `modelComplexLocMap` is a localization at `T` when `A₁ ⊗_{R₁} R₀₁` is the
localization of `A ⊗_R R₀` at `T`. -/
theorem isLocalizedModule_modelComplexLocMap (T : Submonoid B₀) [IsLocalization T B₁] (n : ℤ) :
    IsLocalizedModule T ((modelComplexLocMap (R := R) (R₁ := R₁) R₀₁ eN F).f n).hom :=
  isLocalizedModule_tensorChangeMap _ _ T n

/-- `modelComplexLocMap` sends `(b ⊗ x) ⊗ (b' ⊗ w)` in the summand of degree `(p, q)` to
`(β b ⊗ eN(1 ⊗ x)) ⊗ (β b' ⊗ (1 ⊗ w))`, where `β : A ⊗_R R₀ → A₁ ⊗_{R₁} R₀₁` is the localization
map. -/
theorem modelComplexLocMap_ι_tmul (p q n : ℤ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n)
    (b : B₀) (x : N.X p) (b' : B₀) (w : F.X q) :
    ((modelComplexLocMap (R := R) (R₁ := R₁) R₀₁ eN F).f n).hom
        ((HomologicalComplex.ιMapBifunctor
          (((baseChangeFunctor A B₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj N)
          (((baseChangeFunctor R₀ B₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj F)
          (curriedTensor (ModuleCat.{u} B₀)) (ComplexShape.up ℤ) p q n h).hom
          ((b ⊗ₜ[A] x) ⊗ₜ[B₀] (b' ⊗ₜ[R₀] w))) =
      (HomologicalComplex.ιMapBifunctor
          (((baseChangeFunctor A₁ B₁).mapHomologicalComplex (ComplexShape.up ℤ)).obj N₁)
          (((baseChangeFunctor R₀₁ B₁).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (((baseChangeFunctor R₀ R₀₁).mapHomologicalComplex (ComplexShape.up ℤ)).obj F))
          (curriedTensor (ModuleCat.{u} B₁)) (ComplexShape.up ℤ) p q n h).hom
        ((β b ⊗ₜ[A₁] (eN.hom.f p).hom ((1 : A₁) ⊗ₜ[A] x)) ⊗ₜ[B₁]
          (β b' ⊗ₜ[R₀₁] ((1 : R₀₁) ⊗ₜ[R₀] w))) := by
  have h1 := tensorChangeMap_ι_apply
    (cancelBaseChangeComplexIso (C := A) (D := B₀) (C₁ := A₁) (E := B₁) eN)
    (cancelBaseChangeComplexIso (C := R₀) (D := B₀) (C₁ := R₀₁) (E := B₁)
      (Iso.refl (((baseChangeFunctor R₀ R₀₁).mapHomologicalComplex (ComplexShape.up ℤ)).obj F)))
    p q n h (b ⊗ₜ[A] x) (b' ⊗ₜ[R₀] w)
  refine h1.trans ?_
  rw [cancelBaseChangeComplexIso_hom_f_tmul, cancelBaseChangeComplexIso_hom_f_tmul,
    ← Algebra.algebraMap_eq_smul_one, ← Algebra.algebraMap_eq_smul_one]
  rfl

/-- The ring map `A ⊗_R R₀ → B` of the first square is the one of the second square composed with
the localization map. -/
private theorem modelRingMap_eq_comp_algebraMap
    (hσ : ∀ x : R₀, algebraMap R₀₁ R'₁ (algebraMap R₀ R₀₁ x) =
      algebraMap R' R'₁ (algebraMap R₀ R' x)) :
    modelRingMap R A R' B R₀ = (modelRingMap R₁ A₁ R'₁ B R₀₁).comp (algebraMap B₀ B₁) :=
  RingHom.ext fun b => (modelRingMap_tensorLocalizationMap hσ b).symm

omit [Algebra R R'] [Algebra R B] [Algebra A B] [Algebra R' B] [IsScalarTower R A B]
  [IsScalarTower R R' B] [Algebra R₁ A₁] [Algebra R₁ R'₁] [Algebra R₁ B] [Algebra A₁ B]
  [Algebra R'₁ B] [IsScalarTower R₁ A₁ B] [IsScalarTower R₁ R'₁ B] [Algebra R R₁] [Algebra A A₁]
  [Algebra R' R'₁] [Algebra R A₁] [IsScalarTower R A A₁] [IsScalarTower R R₁ A₁]
  [IsScalarTower A A₁ B] [IsScalarTower R' R'₁ B] [Algebra R₀ R'] [IsScalarTower R R₀ R']
  [Algebra R₁ R₀₁] [Algebra R₀₁ R'₁] [IsScalarTower R₁ R₀₁ R'₁] [Algebra R₀ R₀₁] [Algebra R R₀₁]
  [IsScalarTower R R₀ R₀₁] [IsScalarTower R R₁ R₀₁] in
/-- Maps out of `(B₀ ⊗_A X) ⊗_{B₀} (B₀ ⊗_{R₀} W)` agree as soon as they agree on the elements
`(b ⊗ x) ⊗ (b' ⊗ w)`. -/
theorem baseChangeTensor_hom_ext {X : ModuleCat.{u} A} {W : ModuleCat.{u} R₀} {M : ModuleCat.{u} B₀}
    {φ ψ : (baseChangeFunctor A B₀).obj X ⊗ (baseChangeFunctor R₀ B₀).obj W ⟶ M}
    (h : ∀ (b : B₀) (x : X) (b' : B₀) (w : W),
      φ.hom ((b ⊗ₜ[A] x) ⊗ₜ[B₀] (b' ⊗ₜ[R₀] w)) = ψ.hom ((b ⊗ₜ[A] x) ⊗ₜ[B₀] (b' ⊗ₜ[R₀] w))) :
    φ = ψ := by
  refine ModuleCat.MonoidalCategory.tensor_ext fun s t => ?_
  have key : ∀ z z' : ((baseChangeFunctor A B₀).obj X ⊗ (baseChangeFunctor R₀ B₀).obj W :
      ModuleCat.{u} B₀), z = z' →
      φ.hom z' = ψ.hom z' → φ.hom z = ψ.hom z := fun z z' e h' => e ▸ h'
  induction s using TensorProduct.induction_on with
  | zero =>
    exact key _ 0 (TensorProduct.zero_tmul _ t) ((map_zero φ.hom).trans (map_zero ψ.hom).symm)
  | add s s' hs hs' =>
    exact key _ _ (TensorProduct.add_tmul s s' t) ((map_add φ.hom _ _).trans
      ((congrArg₂ (· + ·) hs hs').trans (map_add ψ.hom _ _).symm))
  | tmul b x =>
    induction t using TensorProduct.induction_on with
    | zero =>
      exact key _ 0 (TensorProduct.tmul_zero _ _) ((map_zero φ.hom).trans (map_zero ψ.hom).symm)
    | add t t' ht ht' =>
      exact key _ _ (TensorProduct.tmul_add _ t t') ((map_add φ.hom _ _).trans
        ((congrArg₂ (· + ·) ht ht').trans (map_add ψ.hom _ _).symm))
    | tmul b' w => exact h b x b' w

variable {Z : CochainComplex (ModuleCat.{u} B) ℤ}
  (ε : F ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} R₀) 0).obj (ModuleCat.of R₀ R'))
  (ε₁ : ((baseChangeFunctor R₀ R₀₁).mapHomologicalComplex (ComplexShape.up ℤ)).obj F ⟶
    (CochainComplex.singleFunctor (ModuleCat.{u} R₀₁) 0).obj (ModuleCat.of R₀₁ R'₁))
  (α : ((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj N ⟶ Z)
  (α₁ : ((ModuleCat.extendScalars (algebraMap A₁ B)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj N₁ ⟶ Z)

/-- **The model map commutes with the localization of the model complex.** -/
theorem modelKappa_modelComplexLocMap
    (hσ : ∀ x : R₀, algebraMap R₀₁ R'₁ (algebraMap R₀ R₀₁ x) =
      algebraMap R' R'₁ (algebraMap R₀ R' x))
    (hε : ∀ w : F.X 0, augmentation _ ε₁ ((1 : R₀₁) ⊗ₜ[R₀] w) =
      algebraMap R' R'₁ (augmentation F ε w))
    (hα : ∀ i (m : N.X i), (α₁.f i).hom ((1 : B) ⊗ₜ[A₁, algebraMap A₁ B]
      (eN.hom.f i).hom ((1 : A₁) ⊗ₜ[A] m)) = (α.f i).hom ((1 : B) ⊗ₜ[A, algebraMap A B] m))
    (n : ℤ) (z : (modelComplex (R := R) A F N).X n) :
    ((modelKappa (R := R₁) (A := A₁) (R' := R'₁) (A' := B) (R₀ := R₀₁) ε₁ N₁ Z α₁).f n).hom
        (((modelComplexLocMap (R := R) (R₁ := R₁) R₀₁ eN F).f n).hom z) =
      ((modelKappa (R := R) (A := A) (R' := R') (A' := B) (R₀ := R₀) ε N Z α).f n).hom z := by
  let φ : modelComplex (R := R) A F N ⟶ _ := modelComplexLocMap (R := R) (R₁ := R₁) R₀₁ eN F ≫
    ((ModuleCat.restrictScalars (algebraMap B₀ B₁)).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (modelKappa (R := R₁) (A := A₁) (R' := R'₁) (A' := B) (R₀ := R₀₁) ε₁ N₁ Z α₁)
  have hρ := modelRingMap_eq_comp_algebraMap (R := R) (A := A) (R' := R') (B := B) (R₁ := R₁)
    (A₁ := A₁) (R'₁ := R'₁) (R₀ := R₀) (R₀₁ := R₀₁) hσ
  have key : φ.f n ≫ (ModuleCat.restrictScalarsComp'App (algebraMap B₀ B₁)
      (modelRingMap R₁ A₁ R'₁ B R₀₁) (modelRingMap R A R' B R₀) hρ (Z.X n)).inv =
      (modelKappa (R := R) (A := A) (R' := R') (A' := B) (R₀ := R₀) ε N Z α).f n := by
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    apply baseChangeTensor_hom_ext
    intro b x b' w
    simp only [φ, ModuleCat.hom_comp, LinearMap.comp_apply, HomologicalComplex.comp_f,
      Functor.mapHomologicalComplex_map_f]
    rw [modelComplexLocMap_ι_tmul (R := R) (R₁ := R₁) (R₀₁ := R₀₁) eN F p q n hpq b x b' w]
    show (α₁.f n).hom (((modelMapE (R := R₁) (A := A₁) (R' := R'₁) (A' := B) (R₀ := R₀₁) _ ε₁
        N₁).f n).hom ((HomologicalComplex.ιMapBifunctor _ _ (curriedTensor (ModuleCat.{u} B₁))
          (ComplexShape.up ℤ) p q n hpq).hom
            ((β b ⊗ₜ[A₁] (eN.hom.f p).hom ((1 : A₁) ⊗ₜ[A] x)) ⊗ₜ[B₁]
              (β b' ⊗ₜ[R₀₁] ((1 : R₀₁) ⊗ₜ[R₀] w))))) =
      (α.f n).hom (((modelMapE (R := R) (A := A) (R' := R') (A' := B) (R₀ := R₀) F ε N).f n).hom
        ((HomologicalComplex.ιMapBifunctor _ _ (curriedTensor (ModuleCat.{u} B₀))
          (ComplexShape.up ℤ) p q n hpq).hom ((b ⊗ₜ[A] x) ⊗ₜ[B₀] (b' ⊗ₜ[R₀] w))))
    by_cases hq : q = 0
    · subst hq
      obtain rfl : n = p := by simpa using hpq.symm
      have e1 := modelMapE_ι_tmul (R := R₁) (A := A₁) (R' := R'₁) (A' := B) (R₀ := R₀₁) _ ε₁ N₁ n
        hpq (β b) ((eN.hom.f n).hom ((1 : A₁) ⊗ₜ[A] x)) (β b') ((1 : R₀₁) ⊗ₜ[R₀] w)
      have e2 := modelMapE_ι_tmul (R := R) (A := A) (R' := R') (A' := B) (R₀ := R₀) F ε N n
        hpq b x b' w
      refine (congrArg (α₁.f n).hom e1).trans (Eq.trans ?_ (congrArg (α.f n).hom e2).symm)
      rw [hε, modelRingMap_tensorLocalizationMap hσ, modelRingMap_tensorLocalizationMap hσ,
        ← IsScalarTower.algebraMap_apply R' R'₁ B]
      set c := modelRingMap R A R' B R₀ b' * algebraMap R' B (augmentation F ε w) *
        modelRingMap R A R' B R₀ b
      let y₁ : (ModuleCat.extendScalars (algebraMap A₁ B)).obj (N₁.X n) :=
        (1 : B) ⊗ₜ[A₁, algebraMap A₁ B] (eN.hom.f n).hom ((1 : A₁) ⊗ₜ[A] x)
      let y : (ModuleCat.extendScalars (algebraMap A B)).obj (N.X n) :=
        (1 : B) ⊗ₜ[A, algebraMap A B] x
      have t1 := extendScalars_tmul_eq_smul c _ y₁ rfl
      have t2 := extendScalars_tmul_eq_smul c _ y rfl
      refine (congrArg (α₁.f n).hom t1).trans (Eq.trans ?_ (congrArg (α.f n).hom t2).symm)
      rw [map_smul, map_smul, hα]
    · have h1 := congrArg (fun ψ => ψ.hom ((β b ⊗ₜ[A₁] (eN.hom.f p).hom ((1 : A₁) ⊗ₜ[A] x)) ⊗ₜ[B₁]
          (β b' ⊗ₜ[R₀₁] ((1 : R₀₁) ⊗ₜ[R₀] w))))
        (modelMapE_ι_eq_zero (R := R₁) (A := A₁) (R' := R'₁) (A' := B) (R₀ := R₀₁) _ ε₁ N₁ p q n
          hq hpq)
      have h2 := congrArg (fun ψ => ψ.hom ((b ⊗ₜ[A] x) ⊗ₜ[B₀] (b' ⊗ₜ[R₀] w)))
        (modelMapE_ι_eq_zero (R := R) (A := A) (R' := R') (A' := B) (R₀ := R₀) F ε N p q n hq hpq)
      rw [ModuleCat.hom_comp, LinearMap.comp_apply] at h1 h2
      refine (congrArg (α₁.f n).hom h1).trans (Eq.trans ?_ (congrArg (α.f n).hom h2).symm)
      exact (map_zero (α₁.f n).hom).trans (map_zero (α.f n).hom).symm
  exact congrArg (fun ψ => ψ.hom z) key

/-- The identification of the cohomology of a restriction of scalars along `B₀ ⟶ B₁`. -/
abbrev derivedHomologyRestrictScalarsIso (n : ℤ) (Y : CochainComplex (ModuleCat.{u} B₁) ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} B₀) n).obj
        (DerivedCategory.Q.obj
          (((ModuleCat.restrictScalars (algebraMap B₀ B₁)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj Y)) ≅
      (ModuleCat.restrictScalars (algebraMap B₀ B₁)).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} B₁) n).obj (DerivedCategory.Q.obj Y)) :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} B₀) n).mapIso
      (((ModuleCat.restrictScalars (algebraMap B₀ B₁)).mapDerivedCategoryFactors.app Y).symm) ≪≫
    ((ModuleCat.restrictScalars (algebraMap B₀ B₁)).mapDerivedCategoryHomologyIso n).app
      (DerivedCategory.Q.obj Y)

/-- `derivedHomologyRestrictScalarsIso` is natural in the complex. -/
theorem derivedHomologyRestrictScalarsIso_naturality (n : ℤ)
    {Y Y' : CochainComplex (ModuleCat.{u} B₁) ℤ} (f : Y ⟶ Y') :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} B₀) n).map (DerivedCategory.Q.map
        (((ModuleCat.restrictScalars (algebraMap B₀ B₁)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map f)) ≫
        (derivedHomologyRestrictScalarsIso (R := R) (R₁ := R₁) (A := A)
          (A₁ := A₁) (R₀ := R₀) (R₀₁ := R₀₁) n Y').hom =
      (derivedHomologyRestrictScalarsIso (R := R) (R₁ := R₁) (A := A) (A₁ := A₁) (R₀ := R₀)
        (R₀₁ := R₀₁) n Y).hom ≫ (ModuleCat.restrictScalars (algebraMap B₀ B₁)).map
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} B₁) n).map
            (DerivedCategory.Q.map f)) := by
  have n1 := ((ModuleCat.restrictScalars (algebraMap B₀ B₁)).mapDerivedCategoryHomologyIso
    n).hom.naturality (DerivedCategory.Q.map f)
  have n2 :=
    ((ModuleCat.restrictScalars (algebraMap B₀ B₁)).mapDerivedCategoryFactors).inv.naturality f
  dsimp only [Functor.comp_map] at n1 n2
  dsimp only [derivedHomologyRestrictScalarsIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    Iso.app_inv, Iso.app_hom]
  have n2' := congrArg (DerivedCategory.homologyFunctor (ModuleCat.{u} B₀) n).map n2
  simp only [Functor.map_comp] at n2'
  simp only [Category.assoc]
  rw [← n1, reassoc_of% n2']

/-- **The model map of a square is a localization exactly when the model map of a localized
square is.**  Let `R → R₁`, `A → A₁`, `R₀ → R₀₁` be localizations, compatible with the two squares
through `B`.  The cohomology of the model map of the localized square is a localization at the
elements becoming units in `B` exactly when that of the original square is. -/
theorem isLocalizedModule_modelKappa_iff_local (U : Submonoid R) [IsLocalization U R₁]
    (W : Submonoid A) [IsLocalization W A₁] (Zs : Submonoid R₀) [IsLocalization Zs R₀₁]
    (hσ : ∀ x : R₀, algebraMap R₀₁ R'₁ (algebraMap R₀ R₀₁ x) =
      algebraMap R' R'₁ (algebraMap R₀ R' x))
    (hε : ∀ w : F.X 0, augmentation _ ε₁ ((1 : R₀₁) ⊗ₜ[R₀] w) =
      algebraMap R' R'₁ (augmentation F ε w))
    (hα : ∀ i (m : N.X i), (α₁.f i).hom ((1 : B) ⊗ₜ[A₁, algebraMap A₁ B]
      (eN.hom.f i).hom ((1 : A₁) ⊗ₜ[A] m)) = (α.f i).hom ((1 : B) ⊗ₜ[A, algebraMap A B] m))
    (n : ℤ) :
    IsLocalizedModule (IsLocalizedModule.unitsComap (modelRingMap R₁ A₁ R'₁ B R₀₁))
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} B₁) n).map (DerivedCategory.Q.map
        (modelKappa (R := R₁) (A := A₁) (R' := R'₁) (A' := B) (R₀ := R₀₁) ε₁ N₁ Z α₁))).hom ↔
    IsLocalizedModule (IsLocalizedModule.unitsComap (modelRingMap R A R' B R₀))
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} B₀) n).map (DerivedCategory.Q.map
        (modelKappa (R := R) (A := A) (R' := R') (A' := B) (R₀ := R₀) ε N Z α))).hom := by
  let T := IsLocalization.tensorSubmonoid (R := R) A R₀ W Zs
  have : IsLocalization T B₁ := IsLocalization.isLocalization_tensorLocalizationMap U W Zs
  have hρ := modelRingMap_eq_comp_algebraMap (R := R) (A := A) (R' := R') (B := B) (R₁ := R₁)
    (A₁ := A₁) (R'₁ := R'₁) (R₀ := R₀) (R₀₁ := R₀₁) hσ
  let Φ := ModuleCat.restrictScalars (algebraMap B₀ B₁)
  let Λ := modelComplexLocMap (R := R) (R₁ := R₁) R₀₁ eN F
  let ιZ : (Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((ModuleCat.restrictScalars (modelRingMap R₁ A₁ R'₁ B R₀₁)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj Z) ⟶
      ((ModuleCat.restrictScalars (modelRingMap R A R' B R₀)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj Z :=
    { f := fun i => (ModuleCat.restrictScalarsComp'App (algebraMap B₀ B₁)
        (modelRingMap R₁ A₁ R'₁ B R₀₁) (modelRingMap R A R' B R₀) hρ (Z.X i)).inv
      comm' := fun i j _ => rfl }
  have hιZ : IsIso ιZ := by
    have : ∀ i, IsIso (ιZ.f i) := fun i => inferInstanceAs (IsIso (Iso.inv _))
    exact HomologicalComplex.Hom.isIso_of_components ιZ
  have hκ : modelKappa (R := R) (A := A) (R' := R') (A' := B) (R₀ := R₀) ε N Z α =
      Λ ≫ (Φ.mapHomologicalComplex (ComplexShape.up ℤ)).map
        (modelKappa (R := R₁) (A := A₁) (R' := R'₁) (A' := B) (R₀ := R₀₁) ε₁ N₁ Z α₁) ≫ ιZ := by
    ext i z
    exact (modelKappa_modelComplexLocMap (R := R) (R₁ := R₁) (R₀₁ := R₀₁) eN F ε ε₁ α α₁ hσ hε hα
      i z).symm
  let H₀ := DerivedCategory.homologyFunctor (ModuleCat.{u} B₀) n
  let H₁ := DerivedCategory.homologyFunctor (ModuleCat.{u} B₁) n
  let eM := derivedHomologyRestrictScalarsIso (R := R) (R₁ := R₁) (A := A) (A₁ := A₁) (R₀ := R₀)
    (R₀₁ := R₀₁) n
    (modelComplex (R := R₁) A₁ (((baseChangeFunctor R₀ R₀₁).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj F) N₁)
  let eZ := derivedHomologyRestrictScalarsIso (R := R) (R₁ := R₁) (A := A) (A₁ := A₁) (R₀ := R₀)
    (R₀₁ := R₀₁) n
    (((ModuleCat.restrictScalars (modelRingMap R₁ A₁ R'₁ B R₀₁)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj Z)
  let g := H₁.map (DerivedCategory.Q.map
    (modelKappa (R := R₁) (A := A₁) (R' := R'₁) (A' := B) (R₀ := R₀₁) ε₁ N₁ Z α₁))
  have hnat := derivedHomologyRestrictScalarsIso_naturality (R := R) (R₁ := R₁) (A := A)
    (A₁ := A₁) (R₀ := R₀) (R₀₁ := R₀₁) n
    (modelKappa (R := R₁) (A := A₁) (R' := R'₁) (A' := B) (R₀ := R₀₁) ε₁ N₁ Z α₁)
  have hsplit : H₀.map (DerivedCategory.Q.map
      (modelKappa (R := R) (A := A) (R' := R') (A' := B) (R₀ := R₀) ε N Z α)) =
      (H₀.map (DerivedCategory.Q.map Λ) ≫ eM.hom) ≫ Φ.map g ≫ (eZ.inv ≫
        H₀.map (DerivedCategory.Q.map ιZ)) := by
    rw [hκ, DerivedCategory.Q.map_comp, DerivedCategory.Q.map_comp, H₀.map_comp, H₀.map_comp,
      (Iso.eq_comp_inv eZ).2 hnat]
    simp only [Category.assoc]
    rfl
  have hψ : Function.Bijective (eZ.inv ≫ H₀.map (DerivedCategory.Q.map ιZ)).hom := by
    rw [← ConcreteCategory.isIso_iff_bijective]
    infer_instance
  have hlam : IsLocalizedModule T (H₀.map (DerivedCategory.Q.map Λ) ≫ eM.hom).hom := by
    rw [ModuleCat.hom_comp]
    refine (IsLocalizedModule.comp_iff_of_bijective_left _ _ eM.toLinearEquiv.bijective).2 ?_
    exact (isLocalizedModule_homologyFunctor_map_Q_iff T Λ n).2
      (CochainComplex.isLocalizedModule_homologyMap T Λ
        (isLocalizedModule_modelComplexLocMap (R := R) (R₁ := R₁) (R₀₁ := R₀₁) eN F T) n)
  let : Module B₀ (H₁.obj (DerivedCategory.Q.obj (modelComplex (R := R₁) A₁
      (((baseChangeFunctor R₀ R₀₁).mapHomologicalComplex (ComplexShape.up ℤ)).obj F) N₁))) :=
    Module.compHom _ (algebraMap B₀ B₁)
  let : Module B₀ (H₁.obj (DerivedCategory.Q.obj
      (((ModuleCat.restrictScalars (modelRingMap R₁ A₁ R'₁ B R₀₁)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj Z))) := Module.compHom _ (algebraMap B₀ B₁)
  have : IsScalarTower B₀ B₁ (H₁.obj (DerivedCategory.Q.obj (modelComplex (R := R₁) A₁
      (((baseChangeFunctor R₀ R₀₁).mapHomologicalComplex (ComplexShape.up ℤ)).obj F) N₁))) :=
    .of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower B₀ B₁ (H₁.obj (DerivedCategory.Q.obj
      (((ModuleCat.restrictScalars (modelRingMap R₁ A₁ R'₁ B R₀₁)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj Z))) :=
    .of_algebraMap_smul fun _ _ => rfl
  have hgi := IsLocalizedModule.iff_restrictScalars_unitsComap (modelRingMap R₁ A₁ R'₁ B R₀₁) T
    g.hom
  have hTV : T ≤ IsLocalizedModule.unitsComap ((modelRingMap R₁ A₁ R'₁ B R₀₁).comp
      (algebraMap B₀ B₁)) := fun t ht =>
    (IsLocalization.map_units B₁ (⟨t, ht⟩ : T)).map (modelRingMap R₁ A₁ R'₁ B R₀₁)
  have hU : IsLocalizedModule.unitsComap (modelRingMap R A R' B R₀) =
      IsLocalizedModule.unitsComap ((modelRingMap R₁ A₁ R'₁ B R₀₁).comp (algebraMap B₀ B₁)) :=
    congrArg _ hρ
  rw [hsplit, ModuleCat.hom_comp, ModuleCat.hom_comp, hU, LinearMap.comp_assoc,
    IsLocalizedModule.comp_iff_of_bijective_left _ _ hψ]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have : IsLocalizedModule (IsLocalizedModule.unitsComap ((modelRingMap R₁ A₁ R'₁ B R₀₁).comp
        (algebraMap B₀ B₁))) (Φ.map g).hom := hgi.1 h
    exact IsLocalizedModule.comp_of_le T _ hTV
      (H₀.map (DerivedCategory.Q.map Λ) ≫ eM.hom).hom (Φ.map g).hom
  · exact hgi.2 (IsLocalizedModule.of_comp_of_le hTV
      (H₀.map (DerivedCategory.Q.map Λ) ≫ eM.hom).hom (Φ.map g).hom)

end Change

end RingTheory.TorIndependence
