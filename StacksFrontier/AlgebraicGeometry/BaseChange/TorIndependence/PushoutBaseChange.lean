module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import StacksFrontier.Homology.TotalComplexTransport
public import StacksFrontier.Homology.MapHomologicalComplexMonoidal

/-!
# Base change along a pushout square of rings, for modules and complexes

Let `R → A` and `R → R₀` be algebras and `B₀ = A ⊗_R R₀` their pushout. For an `A`-module `X`
and an `R₀`-module `W` the `B₀`-module `(B₀ ⊗_A X) ⊗_{B₀} (B₀ ⊗_{R₀} W)`, read over `R₀`, is
`(R₀ ⊗_R X) ⊗_{R₀} W`. This file records that identification, naturally in both modules, and
its consequence for total tensor complexes. It is the identification that lets a complex of
`B₀`-modules compute a derived base change from `R` to a quotient of `R₀`.

## Main definitions

* `RingTheory.TorIndependence.baseChangeFunctor`: base change `X ↦ D ⊗_C X` along an algebra,
  with its standard module structures, and `baseChangeIsoExtendScalars` its identification with
  `ModuleCat.extendScalars (algebraMap C D)`.
* `RingTheory.TorIndependence.baseChangeSwap`: `(A ⊗_R R₀) ⊗_A X ≃ R₀ ⊗_R X` over `R₀`.
* `RingTheory.TorIndependence.tensorBaseChangeLinearEquiv`: the identification above.
* `RingTheory.TorIndependence.modelBifunctor` and `modelComplexRestrictIso`: the bifunctor
  `(X, W) ↦ (B₀ ⊗_A X) ⊗_{B₀} (B₀ ⊗_{R₀} W)` and, for complexes, the restriction to `R₀` of its
  total complex as the total complex of `(R₀ ⊗_R X^•) ⊗_{R₀} W^•`.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory
open scoped TensorProduct ChangeOfRings

universe u

namespace RingTheory.TorIndependence

/-- Base change of modules along an algebra, `X ↦ D ⊗_C X`, with the module structure over `D`
acting on the left factor. -/
def baseChangeFunctor (C D : Type u) [CommRing C] [CommRing D] [Algebra C D] :
    ModuleCat.{u} C ⥤ ModuleCat.{u} D where
  obj X := ModuleCat.of D (D ⊗[C] X)
  map f := ModuleCat.ofHom (f.hom.baseChange D)
  map_id X := by ext : 1; exact LinearMap.baseChange_id
  map_comp f g := by ext : 1; exact LinearMap.baseChange_comp f.hom g.hom

/-- Base change along an algebra is an additive functor. -/
instance (C D : Type u) [CommRing C] [CommRing D] [Algebra C D] :
    (baseChangeFunctor C D).Additive where
  map_add {_ _ f g} := by
    ext : 1
    exact LinearMap.baseChange_add f.hom g.hom

section Generic

variable (C D : Type u) [CommRing C] [CommRing D] [Algebra C D]

/-- Linear maps out of a base change agree as soon as they agree on pure tensors. -/
theorem baseChangeFunctor_hom_ext {X : ModuleCat.{u} C} {M : ModuleCat.{u} D}
    {φ ψ : (baseChangeFunctor C D).obj X ⟶ M}
    (h : ∀ (d : D) (x : X), φ.hom (d ⊗ₜ[C] x) = ψ.hom (d ⊗ₜ[C] x)) : φ = ψ := by
  ext t
  induction t using TensorProduct.induction_on with
  | zero => exact (map_zero φ.hom).trans (map_zero ψ.hom).symm
  | tmul d x => exact h d x
  | add t t' ht ht' =>
    exact (map_add φ.hom _ _).trans ((congrArg₂ (· + ·) ht ht').trans (map_add ψ.hom _ _).symm)

/-- The left factor of a base change, `D` with its two module structures over `C`. -/
def algebraRestrictLinearEquiv :
    D ≃ₗ[C] (ModuleCat.restrictScalars (algebraMap C D)).obj (ModuleCat.of D D) where
  toFun d := d
  invFun d := d
  map_add' _ _ := rfl
  map_smul' c d := by
    change c • d = algebraMap C D c * d
    exact Algebra.smul_def c d
  left_inv _ := rfl
  right_inv _ := rfl

/-- The underlying map of `baseChangeIsoExtendScalarsApp`. -/
def baseChangeToExtendScalars (X : ModuleCat.{u} C) :
    D ⊗[C] X → (ModuleCat.extendScalars (algebraMap C D)).obj X :=
  fun t => TensorProduct.congr (algebraRestrictLinearEquiv C D) (LinearEquiv.refl C X) t

/-- `baseChangeToExtendScalars` is additive. -/
theorem baseChangeToExtendScalars_add (X : ModuleCat.{u} C) (t t' : D ⊗[C] X) :
    baseChangeToExtendScalars C D X (t + t') =
      baseChangeToExtendScalars C D X t + baseChangeToExtendScalars C D X t' :=
  map_add (TensorProduct.congr (algebraRestrictLinearEquiv C D) (LinearEquiv.refl C X)) t t'

/-- `baseChangeToExtendScalars` commutes with the action of `D`. -/
theorem baseChangeToExtendScalars_smul (X : ModuleCat.{u} C) (d : D) (t : D ⊗[C] X) :
    baseChangeToExtendScalars C D X (d • t) = d • baseChangeToExtendScalars C D X t := by
  induction t using TensorProduct.induction_on with
  | zero =>
    rw [smul_zero]
    exact (map_zero (TensorProduct.congr (algebraRestrictLinearEquiv C D)
      (LinearEquiv.refl C X))).trans
        (smul_zero (A := (ModuleCat.extendScalars (algebraMap C D)).obj X) d).symm
  | tmul d' x =>
    rw [TensorProduct.smul_tmul', smul_eq_mul]
    exact (ModuleCat.ExtendScalars.smul_tmul (algebraMap C D) d d' x).symm
  | add t t' ht ht' =>
    rw [smul_add, baseChangeToExtendScalars_add, baseChangeToExtendScalars_add, ht, ht', smul_add]

/-- The linear equivalence underlying `baseChangeIsoExtendScalarsApp`. -/
def baseChangeExtendScalarsLinearEquiv (X : ModuleCat.{u} C) :
    (baseChangeFunctor C D).obj X ≃ₗ[D] (ModuleCat.extendScalars (algebraMap C D)).obj X where
  toFun := baseChangeToExtendScalars C D X
  invFun t := (TensorProduct.congr (algebraRestrictLinearEquiv C D) (LinearEquiv.refl C X)).symm t
  map_add' := map_add (TensorProduct.congr (algebraRestrictLinearEquiv C D) (LinearEquiv.refl C X))
  map_smul' := baseChangeToExtendScalars_smul C D X
  left_inv := (TensorProduct.congr (algebraRestrictLinearEquiv C D) (LinearEquiv.refl C X)).left_inv
  right_inv :=
    (TensorProduct.congr (algebraRestrictLinearEquiv C D) (LinearEquiv.refl C X)).right_inv

/-- Base change along an algebra is extension of scalars along its structure map. -/
def baseChangeIsoExtendScalarsApp (X : ModuleCat.{u} C) :
    (baseChangeFunctor C D).obj X ≅ (ModuleCat.extendScalars (algebraMap C D)).obj X :=
  (baseChangeExtendScalarsLinearEquiv C D X).toModuleIso

/-- `baseChangeIsoExtendScalarsApp` sends `d ⊗ x` to `d ⊗ x`. -/
theorem baseChangeIsoExtendScalarsApp_hom_tmul (X : ModuleCat.{u} C) (d : D) (x : X) :
    (baseChangeIsoExtendScalarsApp C D X).hom.hom (d ⊗ₜ[C] x) =
      (d ⊗ₜ[C, algebraMap C D] x : (ModuleCat.extendScalars (algebraMap C D)).obj X) := rfl

/-- Base change along an algebra is extension of scalars along its structure map, naturally. -/
def baseChangeIsoExtendScalars :
    baseChangeFunctor C D ≅ ModuleCat.extendScalars (algebraMap C D) :=
  NatIso.ofComponents (baseChangeIsoExtendScalarsApp C D) fun {X Y} f => by
    exact baseChangeFunctor_hom_ext C D fun d x => rfl

end Generic

variable {R A R₀ : Type u} [CommRing R] [CommRing A] [CommRing R₀] [Algebra R A] [Algebra R R₀]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

section Swap

variable (X : Type u) [AddCommGroup X] [Module A X] [Module R X] [IsScalarTower R A X]

/-- The additive equivalence `(A ⊗_R R₀) ⊗_A X ≃ R₀ ⊗_R X`, `(a ⊗ r) ⊗ x ↦ r ⊗ a x`. -/
def baseChangeSwapAddEquiv : (A ⊗[R] R₀) ⊗[A] X ≃+ R₀ ⊗[R] X :=
  (TensorProduct.comm A (A ⊗[R] R₀) X).toAddEquiv.trans
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange R A A X R₀).toAddEquiv.trans
      (TensorProduct.comm R X R₀).toAddEquiv)

/-- `baseChangeSwapAddEquiv` sends `(a ⊗ r) ⊗ x` to `r ⊗ (a • x)`. -/
theorem baseChangeSwapAddEquiv_tmul (a : A) (r : R₀) (x : X) :
    baseChangeSwapAddEquiv X ((a ⊗ₜ[R] r) ⊗ₜ[A] x) = r ⊗ₜ[R] (a • x) := rfl

/-- The `R₀`-linear equivalence `(A ⊗_R R₀) ⊗_A X ≃ R₀ ⊗_R X`. -/
def baseChangeSwap : (A ⊗[R] R₀) ⊗[A] X ≃ₗ[R₀] R₀ ⊗[R] X :=
  { baseChangeSwapAddEquiv X with
    map_smul' := fun r t => by
      change baseChangeSwapAddEquiv X (r • t) = r • baseChangeSwapAddEquiv X t
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul b x =>
        induction b using TensorProduct.induction_on with
        | zero => simp
        | tmul a r' =>
          have h : r • (a ⊗ₜ[R] r') = a ⊗ₜ[R] (r * r') := by
            rw [Algebra.smul_def, Algebra.TensorProduct.right_algebraMap_apply,
              Algebra.TensorProduct.tmul_mul_tmul, one_mul]
          rw [TensorProduct.smul_tmul', h, baseChangeSwapAddEquiv_tmul, baseChangeSwapAddEquiv_tmul,
            TensorProduct.smul_tmul', smul_eq_mul]
        | add b b' hb hb' =>
          rw [TensorProduct.add_tmul, smul_add, map_add, hb, hb', map_add, smul_add]
      | add t t' ht ht' => rw [smul_add, map_add, ht, ht', map_add, smul_add] }

/-- `baseChangeSwap` is natural in the `A`-module: for an `A`-linear map `φ : X → X'` it
intertwines `id ⊗ φ` on `(A ⊗_R R₀) ⊗_A X` with `id ⊗ φ` on `R₀ ⊗_R X`. -/
theorem baseChangeSwap_naturality {X' : Type u} [AddCommGroup X'] [Module A X'] [Module R X']
    [IsScalarTower R A X'] (φ : X →ₗ[A] X') (c : A ⊗[R] R₀) (x : X) :
    baseChangeSwap (R := R) (A := A) (R₀ := R₀) X' (c ⊗ₜ[A] φ x) =
      LinearMap.lTensor R₀ (φ.restrictScalars R) (baseChangeSwap X (c ⊗ₜ[A] x)) := by
  induction c using TensorProduct.induction_on with
  | zero => simp only [TensorProduct.zero_tmul, map_zero]
  | tmul a r =>
    show r ⊗ₜ[R] (a • φ x) = r ⊗ₜ[R] φ (a • x)
    rw [map_smul]
  | add c c' hc hc' => simp only [TensorProduct.add_tmul, map_add, hc, hc']

end Swap

section Pushout

local notation "B₀" => A ⊗[R] R₀

/-- An `A`-module, with its `R`-module structure by restriction of scalars along `R → A`, is a
scalar tower over `R` and `A`. -/
instance isScalarTower_restrictScalars_algebraMap (X : ModuleCat.{u} A) :
    IsScalarTower R A ((ModuleCat.restrictScalars (algebraMap R A)).obj X) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

variable (X : ModuleCat.{u} A) (W : ModuleCat.{u} R₀)

/-- `(B₀ ⊗_A X) ⊗_{B₀} (B₀ ⊗_{R₀} W) ≃ (R₀ ⊗_R X) ⊗_{R₀} W`, additively. -/
def tensorBaseChangeAddEquiv : (B₀ ⊗[A] X) ⊗[B₀] (B₀ ⊗[R₀] W) ≃+
    (R₀ ⊗[R] ((ModuleCat.restrictScalars (algebraMap R A)).obj X)) ⊗[R₀] W :=
  (TensorProduct.AlgebraTensorModule.cancelBaseChange R₀ B₀ B₀ (B₀ ⊗[A] X) W).toAddEquiv.trans
    (LinearEquiv.rTensor W
      (baseChangeSwap (R := R) (A := A) (R₀ := R₀)
        ((ModuleCat.restrictScalars (algebraMap R A)).obj X))).toAddEquiv

/-- The value of `tensorBaseChangeAddEquiv` on `((a ⊗ r) ⊗ x) ⊗ (b ⊗ w)`. -/
theorem tensorBaseChangeAddEquiv_tmul (a : A) (r : R₀) (x : X) (b : B₀) (w : W) :
    tensorBaseChangeAddEquiv X W (((a ⊗ₜ[R] r) ⊗ₜ[A] x) ⊗ₜ[B₀] (b ⊗ₜ[R₀] w)) =
      baseChangeSwap (R := R) (A := A) (R₀ := R₀)
        ((ModuleCat.restrictScalars (algebraMap R A)).obj X)
        (b • ((a ⊗ₜ[R] r) ⊗ₜ[A] x)) ⊗ₜ[R₀] w := rfl

/-- `tensorBaseChangeAddEquiv` is `R₀`-linear, `R₀` acting on the source through `B₀`. -/
theorem tensorBaseChangeAddEquiv_smul (r : R₀) (t : (B₀ ⊗[A] X) ⊗[B₀] (B₀ ⊗[R₀] W)) :
    tensorBaseChangeAddEquiv X W (algebraMap R₀ B₀ r • t) = r • tensorBaseChangeAddEquiv X W t := by
  show (LinearEquiv.rTensor W _) ((TensorProduct.AlgebraTensorModule.cancelBaseChange R₀ B₀ B₀
      (B₀ ⊗[A] X) W) (algebraMap R₀ B₀ r • t)) = r • (LinearEquiv.rTensor W _)
        ((TensorProduct.AlgebraTensorModule.cancelBaseChange R₀ B₀ B₀ (B₀ ⊗[A] X) W) t)
  rw [map_smul, algebraMap_smul, map_smul]

/-- **Base change along a pushout square.** For `B₀ = A ⊗_R R₀`, an `A`-module `X` and an
`R₀`-module `W`, `(B₀ ⊗_A X) ⊗_{B₀} (B₀ ⊗_{R₀} W) ≅ (R₀ ⊗_R X) ⊗_{R₀} W` over `R₀`. -/
def tensorBaseChangeLinearEquiv :
    (ModuleCat.restrictScalars (algebraMap R₀ B₀)).obj
        ((baseChangeFunctor A B₀).obj X ⊗ (baseChangeFunctor R₀ B₀).obj W) ≃ₗ[R₀]
      ((baseChangeFunctor R R₀).obj ((ModuleCat.restrictScalars (algebraMap R A)).obj X) ⊗ W :
        ModuleCat.{u} R₀) where
  toFun t := tensorBaseChangeAddEquiv X W t
  invFun t := (tensorBaseChangeAddEquiv X W).symm t
  map_add' := map_add (tensorBaseChangeAddEquiv X W)
  map_smul' := tensorBaseChangeAddEquiv_smul X W
  left_inv := (tensorBaseChangeAddEquiv X W).left_inv
  right_inv := (tensorBaseChangeAddEquiv X W).right_inv

/-- Maps out of `res (B₀ ⊗_A X ⊗_{B₀} B₀ ⊗_{R₀} W)` agree as soon as they agree on the
elements `((a ⊗ r) ⊗ x) ⊗ (b ⊗ w)`. -/
theorem tensorBaseChange_hom_ext {X : ModuleCat.{u} A} {W : ModuleCat.{u} R₀}
    {M : ModuleCat.{u} R₀}
    {φ ψ : (ModuleCat.restrictScalars (algebraMap R₀ B₀)).obj
        ((baseChangeFunctor A B₀).obj X ⊗ (baseChangeFunctor R₀ B₀).obj W) ⟶ M}
    (h : ∀ (a : A) (r : R₀) (x : X) (b : B₀) (w : W),
      φ.hom (((a ⊗ₜ[R] r) ⊗ₜ[A] x) ⊗ₜ[B₀] (b ⊗ₜ[R₀] w)) =
        ψ.hom (((a ⊗ₜ[R] r) ⊗ₜ[A] x) ⊗ₜ[B₀] (b ⊗ₜ[R₀] w))) : φ = ψ := by
  ext t
  have hz := (map_zero φ.hom).trans (map_zero ψ.hom).symm
  have ha : ∀ s s', φ.hom s = ψ.hom s → φ.hom s' = ψ.hom s' → φ.hom (s + s') = ψ.hom (s + s') :=
    fun s s' hs hs' => (map_add φ.hom _ _).trans
      ((congrArg₂ (· + ·) hs hs').trans (map_add ψ.hom _ _).symm)
  have hc : ∀ s s', s = s' → φ.hom s' = ψ.hom s' → φ.hom s = ψ.hom s := by
    intro s s' e h'
    rw [e]
    exact h'
  induction t using TensorProduct.induction_on with
  | zero => exact hz
  | add s s' hs hs' => exact ha s s' hs hs'
  | tmul m n =>
    induction m using TensorProduct.induction_on with
    | zero => exact hc _ _ (TensorProduct.zero_tmul _ n) hz
    | add m m' hm hm' => exact hc _ _ (TensorProduct.add_tmul m m' n) (ha _ _ hm hm')
    | tmul c x =>
      induction c using TensorProduct.induction_on with
      | zero =>
        exact hc _ _ ((congrArg (fun m : (baseChangeFunctor A B₀).obj X => m ⊗ₜ[B₀] n)
          (TensorProduct.zero_tmul _ x)).trans (TensorProduct.zero_tmul _ n)) hz
      | add c c' hc' hc'' =>
        exact hc _ _ ((congrArg (fun m : (baseChangeFunctor A B₀).obj X => m ⊗ₜ[B₀] n)
          (TensorProduct.add_tmul c c' x)).trans (TensorProduct.add_tmul _ _ n)) (ha _ _ hc' hc'')
      | tmul a r =>
        induction n using TensorProduct.induction_on with
        | zero => exact hc _ _ (TensorProduct.tmul_zero _ _) hz
        | add n n' hn hn' => exact hc _ _ (TensorProduct.tmul_add _ n n') (ha _ _ hn hn')
        | tmul b w => exact h a r x b w

/-- The bifunctor `(X, W) ↦ (B₀ ⊗_A X) ⊗_{B₀} (B₀ ⊗_{R₀} W)`. -/
def modelBifunctor : ModuleCat.{u} A ⥤ ModuleCat.{u} R₀ ⥤ ModuleCat.{u} B₀ :=
  baseChangeFunctor A B₀ ⋙ curriedTensor (ModuleCat.{u} B₀) ⋙
    (Functor.whiskeringLeft _ _ _).obj (baseChangeFunctor R₀ B₀)

/-- `modelBifunctor` preserves zero morphisms in its first variable. -/
instance : (modelBifunctor (R := R) (A := A) (R₀ := R₀)).PreservesZeroMorphisms where
  map_zero X₁ Y₁ := by
    ext W₁ : 2
    simp [modelBifunctor]
    rfl

/-- `modelBifunctor` preserves zero morphisms in its second variable. -/
instance (X₁ : ModuleCat.{u} A) :
    ((modelBifunctor (R := R) (A := A) (R₀ := R₀)).obj X₁).PreservesZeroMorphisms where
  map_zero W₁ W₂ := by
    simp [modelBifunctor]
    rfl

/-- The comparison of `modelBifunctor`, restricted to `R₀`, with `(X, W) ↦ (R₀ ⊗_R X) ⊗_{R₀} W`. -/
def modelBifunctorIso (X : ModuleCat.{u} A) (W : ModuleCat.{u} R₀) :
    (ModuleCat.restrictScalars (algebraMap R₀ B₀)).obj
        ((modelBifunctor.obj X).obj W) ≅
      ((curriedTensor (ModuleCat.{u} R₀)).obj
        ((ModuleCat.restrictScalars (algebraMap R A) ⋙ baseChangeFunctor R R₀).obj X)).obj
          ((𝟭 (ModuleCat.{u} R₀)).obj W) :=
  (tensorBaseChangeLinearEquiv X W).toModuleIso

/-- `modelBifunctorIso` is natural in the `A`-module. -/
theorem modelBifunctorIso_naturality_left {X X' : ModuleCat.{u} A} (f : X ⟶ X')
    (W : ModuleCat.{u} R₀) :
    (ModuleCat.restrictScalars (algebraMap R₀ B₀)).map ((modelBifunctor.map f).app W) ≫
        (modelBifunctorIso X' W).hom =
      (modelBifunctorIso X W).hom ≫ ((curriedTensor (ModuleCat.{u} R₀)).map
        ((ModuleCat.restrictScalars (algebraMap R A) ⋙ baseChangeFunctor R R₀).map f)).app
          ((𝟭 (ModuleCat.{u} R₀)).obj W) := by
  refine tensorBaseChange_hom_ext fun a r x b w => ?_
  show baseChangeSwap (R := R) (A := A) (R₀ := R₀)
      ((ModuleCat.restrictScalars (algebraMap R A)).obj X') (b • ((a ⊗ₜ[R] r) ⊗ₜ[A] f x)) ⊗ₜ[R₀] w =
    (LinearMap.lTensor R₀ ((ModuleCat.restrictScalars (algebraMap R A)).map f).hom
      (baseChangeSwap (R := R) (A := A) (R₀ := R₀)
        ((ModuleCat.restrictScalars (algebraMap R A)).obj X) (b • ((a ⊗ₜ[R] r) ⊗ₜ[A] x)))) ⊗ₜ[R₀] w
  rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul']
  congr 1
  generalize b • (a ⊗ₜ[R] r) = c
  induction c using TensorProduct.induction_on with
  | zero =>
    rw [TensorProduct.zero_tmul, TensorProduct.zero_tmul]
    refine (map_zero (baseChangeSwap (R := R) (A := A) (R₀ := R₀) _)).trans ?_
    exact ((congrArg (LinearMap.lTensor R₀ _)
      (map_zero (baseChangeSwap (R := R) (A := A) (R₀ := R₀) _))).trans (map_zero _)).symm
  | tmul a' r' =>
    exact congrArg (fun y : (ModuleCat.restrictScalars (algebraMap R A)).obj X' => r' ⊗ₜ[R] y)
      (map_smul f.hom a' x).symm
  | add c c' hc hc' =>
    rw [TensorProduct.add_tmul, TensorProduct.add_tmul]
    refine (map_add (baseChangeSwap (R := R) (A := A) (R₀ := R₀) _) _ _).trans ?_
    rw [hc, hc']
    exact ((congrArg (LinearMap.lTensor R₀ _)
      (map_add (baseChangeSwap (R := R) (A := A) (R₀ := R₀) _) _ _)).trans (map_add _ _ _)).symm

/-- `modelBifunctorIso` is natural in the `R₀`-module. -/
theorem modelBifunctorIso_naturality_right (X : ModuleCat.{u} A) {W W' : ModuleCat.{u} R₀}
    (g : W ⟶ W') :
    (ModuleCat.restrictScalars (algebraMap R₀ B₀)).map ((modelBifunctor.obj X).map g) ≫
        (modelBifunctorIso X W').hom =
      (modelBifunctorIso X W).hom ≫ ((curriedTensor (ModuleCat.{u} R₀)).obj
        ((ModuleCat.restrictScalars (algebraMap R A) ⋙ baseChangeFunctor R R₀).obj X)).map
          ((𝟭 (ModuleCat.{u} R₀)).map g) :=
  tensorBaseChange_hom_ext fun _ _ _ _ _ => rfl

variable (M : CochainComplex (ModuleCat.{u} A) ℤ) (F : CochainComplex (ModuleCat.{u} R₀) ℤ)

/-- For complexes `M` of `A`-modules and `F` of `R₀`-modules, the restriction to `R₀` of the
total complex of `(B₀ ⊗_A M) ⊗_{B₀} (B₀ ⊗_{R₀} F)` is isomorphic to the total complex of
`(R₀ ⊗_R M) ⊗_{R₀} F`. -/
def modelComplexRestrictIso :
    ((ModuleCat.restrictScalars (algebraMap R₀ B₀)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (HomologicalComplex.mapBifunctor M F (modelBifunctor (R := R)) (ComplexShape.up ℤ)) ≅
      HomologicalComplex.mapBifunctor
        ((ModuleCat.restrictScalars (algebraMap R A) ⋙ baseChangeFunctor R R₀).mapHomologicalComplex
          (ComplexShape.up ℤ) |>.obj M)
        ((𝟭 (ModuleCat.{u} R₀)).mapHomologicalComplex (ComplexShape.up ℤ) |>.obj F)
        (curriedTensor (ModuleCat.{u} R₀)) (ComplexShape.up ℤ) :=
  CategoryTheory.Functor.mapBifunctorTotalIso (modelBifunctor (R := R))
    (curriedTensor (ModuleCat.{u} R₀))
    (ModuleCat.restrictScalars (algebraMap R A) ⋙ baseChangeFunctor R R₀) (𝟭 _)
    (ModuleCat.restrictScalars (algebraMap R₀ B₀)) modelBifunctorIso
    (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
    modelBifunctorIso_naturality_left modelBifunctorIso_naturality_right M F

end Pushout

end RingTheory.TorIndependence
