module

public import StacksFrontier.Cotangent.BaseChangeQuasiIso

/-!
# The differentials of a tensor product of augmented algebras

Let `A` be a ring and `B` an `A`-algebra. For an `A`-algebra `P` augmented to `B`, the `B`-module
`B ⊗_P Ω[P⁄A]` is `CommAlgCat.overDifferentials`. If `Z` is an `A`-algebra over `B` and
`i : X ⟶ Z`, `j : Y ⟶ Z` are morphisms over `B` presenting `Z.left` as the tensor product
`X.left ⊗_A Y.left`, then the two induced maps make `B ⊗_Z Ω[Z⁄A]` the direct sum of
`B ⊗_X Ω[X⁄A]` and `B ⊗_Y Ω[Y⁄A]`.

## Main definitions

* `CommAlgCat.overDifferentialsDesc`: the universal property of `B ⊗_P Ω[P⁄A]`: a map out of it
  is an `A`-derivation of `P` with values in a `B`-module, the `P`-module structure being read
  through the augmentation.

## Main results

* `CommAlgCat.isIso_biprod_desc_overDifferentialsFunctor_map`: the direct sum decomposition of
  the differentials of a tensor product.

## Implementation notes

The inverse of the comparison is built from the two derivations `x ⊗ y ↦ ε(y) · (1 ⊗ d x)` and
`x ⊗ y ↦ ε(x) · (1 ⊗ d y)` of `X.left ⊗_A Y.left`, transported to `Z.left` along the given
presentation; the five identities expressing that the four maps form a biproduct are checked on
the pure differentials `1 ⊗ d z`, which generate.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace CommAlgCat

variable {A : Type u} [CommRing A] {B : CommAlgCat.{u} A}

/-! ### The universal property of `B ⊗_P Ω[P⁄A]` -/

section Desc

variable (X : Over B) {N : ModuleCat.{u} B} (δ : (X.left : Type u) →+ N)
  (hδA : ∀ a : A, δ (algebraMap A (X.left : Type u) a) = 0)
  (hδ : ∀ p q : (X.left : Type u),
    δ (p * q) = augmentationRingHom X p • δ q + augmentationRingHom X q • δ p)

/-- The derivation `P → N` underlying an additive map satisfying the Leibniz rule over the
augmentation and vanishing on the image of `A`; `N` is read as a `P`-module through the
augmentation. -/
def overDifferentialsDescDerivation :
    letI : Module A ((ModuleCat.restrictScalars (augmentationRingHom X)).obj N) :=
      Module.compHom _ (algebraMap A (X.left : Type u))
    Derivation A (X.left : Type u) ((ModuleCat.restrictScalars (augmentationRingHom X)).obj N) :=
  letI : Module A ((ModuleCat.restrictScalars (augmentationRingHom X)).obj N) :=
    Module.compHom _ (algebraMap A (X.left : Type u))
  { toFun := fun p => δ p
    map_add' := fun p q => δ.map_add p q
    map_smul' := fun a p => by
      change δ (a • p) = augmentationRingHom X (algebraMap A (X.left : Type u) a) • δ p
      rw [Algebra.smul_def, hδ, hδA, smul_zero, add_zero]
    map_one_eq_zero' := by
      change δ 1 = 0
      have h := hδ 1 1
      rw [mul_one, RingHom.map_one, one_smul] at h
      exact left_eq_add.mp h
    leibniz' := fun p q => by
      change δ (p * q) = augmentationRingHom X p • δ q + augmentationRingHom X q • δ p
      exact hδ p q }

/-- **A map out of `B ⊗_P Ω[P⁄A]` from a derivation.** An additive map `δ : P → N` to a
`B`-module which vanishes on the image of `A` and satisfies the Leibniz rule
`δ(pq) = ε(p) δ(q) + ε(q) δ(p)` induces the `B`-linear map `1 ⊗ d p ↦ δ p`. -/
def overDifferentialsDesc : overDifferentials X ⟶ N :=
  letI : Module A ((ModuleCat.restrictScalars (augmentationRingHom X)).obj N) :=
    Module.compHom _ (algebraMap A (X.left : Type u))
  haveI : IsScalarTower A (X.left : Type u)
      ((ModuleCat.restrictScalars (augmentationRingHom X)).obj N) :=
    IsScalarTower.of_compHom _ _ _
  ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars (augmentationRingHom X)
    (ModuleCat.ofHom (X := ModuleCat.of (X.left : Type u) (KaehlerDifferential A (X.left : Type u)))
      (Y := (ModuleCat.restrictScalars (augmentationRingHom X)).obj N)
      (overDifferentialsDescDerivation X δ hδA hδ).liftKaehlerDifferential)

/-- The map `overDifferentialsDesc X δ hδA hδ` sends `1 ⊗ d p` to `δ p`. -/
@[simp]
theorem overDifferentialsDesc_mk (p : (X.left : Type u)) :
    overDifferentialsDesc X δ hδA hδ (overDifferentialsMk X p) = δ p := by
  let : Module A ((ModuleCat.restrictScalars (augmentationRingHom X)).obj N) :=
    Module.compHom _ (algebraMap A (X.left : Type u))
  have : IsScalarTower A (X.left : Type u)
      ((ModuleCat.restrictScalars (augmentationRingHom X)).obj N) :=
    IsScalarTower.of_compHom _ _ _
  refine (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_tmul _ _ _ _).trans ?_
  rw [one_smul]
  exact (overDifferentialsDescDerivation X δ hδA hδ).liftKaehlerDifferential_comp_D p

end Desc

/-! ### Elementary identities for the pure differentials -/

/-- `1 ⊗ d(p + q) = 1 ⊗ d p + 1 ⊗ d q`. -/
theorem overDifferentialsMk_add (X : Over B) (p q : (X.left : Type u)) :
    overDifferentialsMk X (p + q) = overDifferentialsMk X p + overDifferentialsMk X q := by
  simp only [overDifferentialsMk, map_add]
  exact TensorProduct.tmul_add _ _ _

/-- The augmentation `augmentationRingHom X` is the structure map `X.hom` of `X` over `B`. -/
theorem augmentationRingHom_apply (X : Over B) (p : (X.left : Type u)) :
    augmentationRingHom X p = X.hom.hom p :=
  rfl

/-- `1 ⊗ d 0 = 0`. -/
theorem overDifferentialsMk_zero (X : Over B) : overDifferentialsMk X 0 = 0 := by
  simp only [overDifferentialsMk, map_zero]
  exact TensorProduct.tmul_zero _ _

/-- The differential of the image of an element of `A` vanishes: `1 ⊗ d a = 0`. -/
theorem overDifferentialsMk_algebraMap (X : Over B) (a : A) :
    overDifferentialsMk X (algebraMap A (X.left : Type u) a) = 0 := by
  simp only [overDifferentialsMk, Derivation.map_algebraMap]
  exact TensorProduct.tmul_zero _ _

/-- `1 ⊗ d 1 = 0`. -/
theorem overDifferentialsMk_one (X : Over B) : overDifferentialsMk X 1 = 0 := by
  simp only [overDifferentialsMk, Derivation.map_one_eq_zero]
  exact TensorProduct.tmul_zero _ _

/-- The Leibniz rule over the augmentation: `1 ⊗ d(pq) = ε(p) (1 ⊗ d q) + ε(q) (1 ⊗ d p)`. -/
theorem overDifferentialsMk_mul (X : Over B) (p q : (X.left : Type u)) :
    overDifferentialsMk X (p * q) =
      augmentationRingHom X p • overDifferentialsMk X q +
        augmentationRingHom X q • overDifferentialsMk X p := by
  simp only [overDifferentialsMk]
  rw [Derivation.leibniz]
  refine (TensorProduct.tmul_add _ _ _).trans ?_
  congr 1
  · exact (TensorProduct.tmul_smul _ _ _).trans (TensorProduct.smul_tmul' _ _ _).symm
  · exact (TensorProduct.tmul_smul _ _ _).trans (TensorProduct.smul_tmul' _ _ _).symm

/-- For `a : A`, `1 ⊗ d(a • p) = a • (1 ⊗ d p)`, with `A` acting on `B` through `algebraMap`. -/
theorem overDifferentialsMk_smul (X : Over B) (a : A) (p : (X.left : Type u)) :
    overDifferentialsMk X (a • p) = algebraMap A (B : Type u) a • overDifferentialsMk X p := by
  rw [Algebra.smul_def, overDifferentialsMk_mul, overDifferentialsMk_algebraMap, smul_zero,
    add_zero]
  congr 1
  exact X.hom.hom.commutes a

/-! ### The differentials of a tensor product -/

section Tensor

variable {X Y Z : Over B} (i : X ⟶ Z) (j : Y ⟶ Z)

/-- The map `X.left ⊗_A Y.left → Z.left` induced by two morphisms into `Z`. -/
abbrev overTensorLift : (X.left : Type u) ⊗[A] (Y.left : Type u) →ₐ[A] (Z.left : Type u) :=
  Algebra.TensorProduct.lift i.left.hom j.left.hom fun _ _ => Commute.all _ _

/-- The augmentation of `X.left ⊗_A Y.left`, `x ⊗ y ↦ ε(x) ε(y)`. -/
abbrev overTensorAugmentation :
    (X.left : Type u) ⊗[A] (Y.left : Type u) →ₐ[A] (B : Type u) :=
  Algebra.TensorProduct.lift X.hom.hom Y.hom.hom fun _ _ => Commute.all _ _

/-- The augmentation of `Z` composed with `overTensorLift i j` is `overTensorAugmentation`. -/
theorem augmentationRingHom_overTensorLift (w : (X.left : Type u) ⊗[A] (Y.left : Type u)) :
    augmentationRingHom Z (overTensorLift i j w) = overTensorAugmentation (X := X) (Y := Y) w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
      show Z.hom.hom (i.left.hom x * j.left.hom y) = X.hom.hom x * Y.hom.hom y
      rw [map_mul]
      exact congrArg₂ (· * ·) (ConcreteCategory.congr_hom (Over.w i) x)
        (ConcreteCategory.congr_hom (Over.w j) y)
  | add w w' hw hw' => simp only [map_add] at hw hw' ⊢; rw [hw, hw']

/-- The bilinear map `(x, y) ↦ ε(y) · (1 ⊗ d x)`. -/
def overTensorDerivFst : (X.left : Type u) ⊗[A] (Y.left : Type u) →+ overDifferentials X :=
  TensorProduct.liftAddHom
    { toFun := fun x =>
        { toFun := fun y => Y.hom.hom y • overDifferentialsMk X x
          map_zero' := by rw [map_zero, zero_smul]
          map_add' := fun y y' => by rw [map_add, add_smul] }
      map_zero' := by
        ext y
        change Y.hom.hom y • overDifferentialsMk X 0 = 0
        rw [overDifferentialsMk_zero, smul_zero]
      map_add' := fun x x' => by
        ext y
        change Y.hom.hom y • overDifferentialsMk X (x + x') =
          Y.hom.hom y • overDifferentialsMk X x + Y.hom.hom y • overDifferentialsMk X x'
        rw [overDifferentialsMk_add, smul_add] }
    fun a x y => by
      change Y.hom.hom y • overDifferentialsMk X (a • x) =
        Y.hom.hom (a • y) • overDifferentialsMk X x
      rw [overDifferentialsMk_smul, smul_smul, map_smul, Algebra.smul_def, mul_comm]

/-- The bilinear map `(x, y) ↦ ε(x) · (1 ⊗ d y)`. -/
def overTensorDerivSnd : (X.left : Type u) ⊗[A] (Y.left : Type u) →+ overDifferentials Y :=
  TensorProduct.liftAddHom
    { toFun := fun x =>
        { toFun := fun y => X.hom.hom x • overDifferentialsMk Y y
          map_zero' := by rw [overDifferentialsMk_zero, smul_zero]
          map_add' := fun y y' => by rw [overDifferentialsMk_add, smul_add] }
      map_zero' := by
        ext y
        change X.hom.hom 0 • overDifferentialsMk Y y = 0
        rw [map_zero, zero_smul]
      map_add' := fun x x' => by
        ext y
        change X.hom.hom (x + x') • overDifferentialsMk Y y =
          X.hom.hom x • overDifferentialsMk Y y + X.hom.hom x' • overDifferentialsMk Y y
        rw [map_add, add_smul] }
    fun a x y => by
      change X.hom.hom (a • x) • overDifferentialsMk Y y =
        X.hom.hom x • overDifferentialsMk Y (a • y)
      rw [overDifferentialsMk_smul, smul_smul, map_smul, Algebra.smul_def, mul_comm]

/-- `overTensorDerivFst` sends `x ⊗ y` to `ε(y) · (1 ⊗ d x)`. -/
@[simp]
theorem overTensorDerivFst_tmul (x : (X.left : Type u)) (y : (Y.left : Type u)) :
    overTensorDerivFst (X := X) (Y := Y) (x ⊗ₜ[A] y) = Y.hom.hom y • overDifferentialsMk X x :=
  rfl

/-- `overTensorDerivSnd` sends `x ⊗ y` to `ε(x) · (1 ⊗ d y)`. -/
@[simp]
theorem overTensorDerivSnd_tmul (x : (X.left : Type u)) (y : (Y.left : Type u)) :
    overTensorDerivSnd (X := X) (Y := Y) (x ⊗ₜ[A] y) = X.hom.hom x • overDifferentialsMk Y y :=
  rfl

/-- An additive map on `X.left ⊗_A Y.left` satisfies the Leibniz rule over
`overTensorAugmentation` as soon as it does on products of pure tensors. -/
private theorem leibniz_of_tmul_mul_tmul {M : Type*} [AddCommGroup M] [Module (B : Type u) M]
    (D : (X.left : Type u) ⊗[A] (Y.left : Type u) →+ M)
    (h : ∀ (x x' : (X.left : Type u)) (y y' : (Y.left : Type u)),
      D ((x ⊗ₜ[A] y) * (x' ⊗ₜ[A] y')) =
        overTensorAugmentation (x ⊗ₜ[A] y) • D (x' ⊗ₜ[A] y') +
          overTensorAugmentation (x' ⊗ₜ[A] y') • D (x ⊗ₜ[A] y))
    (w w' : (X.left : Type u) ⊗[A] (Y.left : Type u)) :
    D (w * w') = overTensorAugmentation w • D w' + overTensorAugmentation w' • D w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add w₁ w₂ h₁ h₂ => simp only [add_mul, map_add, h₁, h₂, add_smul, smul_add]; abel
  | tmul x y =>
    induction w' using TensorProduct.induction_on with
    | zero => simp
    | add w₁ w₂ h₁ h₂ => simp only [mul_add, map_add, h₁, h₂, add_smul, smul_add]; abel
    | tmul x' y' => exact h x x' y y'

/-- `overTensorDerivFst` satisfies the Leibniz rule over `overTensorAugmentation`. -/
theorem overTensorDerivFst_mul (w w' : (X.left : Type u) ⊗[A] (Y.left : Type u)) :
    overTensorDerivFst (w * w') =
      overTensorAugmentation w • overTensorDerivFst w' +
        overTensorAugmentation w' • overTensorDerivFst (X := X) (Y := Y) w :=
  leibniz_of_tmul_mul_tmul _ (fun x x' y y' => by
    rw [Algebra.TensorProduct.tmul_mul_tmul]
    simp only [overTensorDerivFst_tmul, overDifferentialsMk_mul, Algebra.TensorProduct.lift_tmul,
      map_mul, smul_add, smul_smul, augmentationRingHom_apply]
    congr 1 <;> congr 1 <;> ring) w w'

/-- `overTensorDerivSnd` satisfies the Leibniz rule over `overTensorAugmentation`. -/
theorem overTensorDerivSnd_mul (w w' : (X.left : Type u) ⊗[A] (Y.left : Type u)) :
    overTensorDerivSnd (w * w') =
      overTensorAugmentation w • overTensorDerivSnd w' +
        overTensorAugmentation w' • overTensorDerivSnd (X := X) (Y := Y) w :=
  leibniz_of_tmul_mul_tmul _ (fun x x' y y' => by
    rw [Algebra.TensorProduct.tmul_mul_tmul]
    simp only [overTensorDerivSnd_tmul, overDifferentialsMk_mul, Algebra.TensorProduct.lift_tmul,
      map_mul, smul_add, smul_smul, augmentationRingHom_apply]
    congr 1 <;> congr 1 <;> ring) w w'

/-- `overTensorDerivFst` vanishes on the image of `A`. -/
theorem overTensorDerivFst_algebraMap (a : A) :
    overTensorDerivFst (X := X) (Y := Y) (algebraMap A _ a) = 0 := by
  rw [Algebra.TensorProduct.algebraMap_apply, overTensorDerivFst_tmul,
    overDifferentialsMk_algebraMap, smul_zero]

/-- `overTensorDerivSnd` vanishes on the image of `A`. -/
theorem overTensorDerivSnd_algebraMap (a : A) :
    overTensorDerivSnd (X := X) (Y := Y) (algebraMap A _ a) = 0 := by
  rw [Algebra.TensorProduct.algebraMap_apply, overTensorDerivSnd_tmul,
    overDifferentialsMk_one, smul_zero]

section Presentation

variable (h : Function.Bijective (overTensorLift i j))

/-- The presentation `X.left ⊗_A Y.left ≃ Z.left`. -/
abbrev overTensorEquiv : ((X.left : Type u) ⊗[A] (Y.left : Type u)) ≃ₐ[A] (Z.left : Type u) :=
  AlgEquiv.ofBijective (overTensorLift i j) h

/-- The inverse of `overTensorEquiv i j h` sends `i x` to `x ⊗ 1`. -/
theorem overTensorEquiv_symm_left (x : (X.left : Type u)) :
    (overTensorEquiv i j h).symm (i.left.hom x) = x ⊗ₜ[A] 1 := by
  apply (overTensorEquiv i j h).injective
  rw [AlgEquiv.apply_symm_apply]
  show i.left.hom x = i.left.hom x * j.left.hom 1
  rw [map_one, mul_one]

/-- The inverse of `overTensorEquiv i j h` sends `j y` to `1 ⊗ y`. -/
theorem overTensorEquiv_symm_right (y : (Y.left : Type u)) :
    (overTensorEquiv i j h).symm (j.left.hom y) = 1 ⊗ₜ[A] y := by
  apply (overTensorEquiv i j h).injective
  rw [AlgEquiv.apply_symm_apply]
  show j.left.hom y = i.left.hom 1 * j.left.hom y
  rw [map_one, one_mul]

/-- The augmentation of `Z` is `overTensorAugmentation` transported along `overTensorEquiv`. -/
theorem augmentationRingHom_overTensorEquiv (z : (Z.left : Type u)) :
    augmentationRingHom Z z = overTensorAugmentation ((overTensorEquiv i j h).symm z) := by
  conv_lhs => rw [← (overTensorEquiv i j h).apply_symm_apply z]
  exact augmentationRingHom_overTensorLift i j _

/-- The projection `B ⊗_Z Ω[Z⁄A] ⟶ B ⊗_X Ω[X⁄A]`, `1 ⊗ d(x ⊗ y) ↦ ε(y) · (1 ⊗ d x)`. -/
def overTensorFst : overDifferentialsFunctor.obj Z ⟶ overDifferentialsFunctor.obj X :=
  overDifferentialsDesc Z
    (overTensorDerivFst.comp (overTensorEquiv i j h).symm.toRingEquiv.toAddEquiv.toAddMonoidHom)
    (fun a => by
      change overTensorDerivFst ((overTensorEquiv i j h).symm (algebraMap A _ a)) = 0
      rw [AlgEquiv.commutes, overTensorDerivFst_algebraMap])
    (fun p q => by
      change overTensorDerivFst ((overTensorEquiv i j h).symm (p * q)) =
        augmentationRingHom Z p • overTensorDerivFst ((overTensorEquiv i j h).symm q) +
          augmentationRingHom Z q • overTensorDerivFst ((overTensorEquiv i j h).symm p)
      rw [map_mul, overTensorDerivFst_mul, augmentationRingHom_overTensorEquiv i j h p,
        augmentationRingHom_overTensorEquiv i j h q])

/-- The projection `B ⊗_Z Ω[Z⁄A] ⟶ B ⊗_Y Ω[Y⁄A]`, `1 ⊗ d(x ⊗ y) ↦ ε(x) · (1 ⊗ d y)`. -/
def overTensorSnd : overDifferentialsFunctor.obj Z ⟶ overDifferentialsFunctor.obj Y :=
  overDifferentialsDesc Z
    (overTensorDerivSnd.comp (overTensorEquiv i j h).symm.toRingEquiv.toAddEquiv.toAddMonoidHom)
    (fun a => by
      change overTensorDerivSnd ((overTensorEquiv i j h).symm (algebraMap A _ a)) = 0
      rw [AlgEquiv.commutes, overTensorDerivSnd_algebraMap])
    (fun p q => by
      change overTensorDerivSnd ((overTensorEquiv i j h).symm (p * q)) =
        augmentationRingHom Z p • overTensorDerivSnd ((overTensorEquiv i j h).symm q) +
          augmentationRingHom Z q • overTensorDerivSnd ((overTensorEquiv i j h).symm p)
      rw [map_mul, overTensorDerivSnd_mul, augmentationRingHom_overTensorEquiv i j h p,
        augmentationRingHom_overTensorEquiv i j h q])

/-- `overTensorFst i j h` sends `1 ⊗ d z` to `overTensorDerivFst` of the preimage of `z`. -/
theorem overTensorFst_mk (z : (Z.left : Type u)) :
    overTensorFst i j h (overDifferentialsMk Z z) =
      overTensorDerivFst ((overTensorEquiv i j h).symm z) :=
  overDifferentialsDesc_mk _ _ _ _ z

/-- `overTensorSnd i j h` sends `1 ⊗ d z` to `overTensorDerivSnd` of the preimage of `z`. -/
theorem overTensorSnd_mk (z : (Z.left : Type u)) :
    overTensorSnd i j h (overDifferentialsMk Z z) =
      overTensorDerivSnd ((overTensorEquiv i j h).symm z) :=
  overDifferentialsDesc_mk _ _ _ _ z

include h in
/-- **The differentials of a tensor product are the direct sum of the differentials of the
factors.** If `i : X ⟶ Z` and `j : Y ⟶ Z` are morphisms of `A`-algebras over `B` such that
`x ⊗ y ↦ i(x) j(y)` is an isomorphism `X.left ⊗_A Y.left ≅ Z.left`, then the map
`B ⊗_X Ω[X⁄A] ⊕ B ⊗_Y Ω[Y⁄A] ⟶ B ⊗_Z Ω[Z⁄A]` induced by `i` and `j` is an isomorphism. -/
theorem isIso_biprod_desc_overDifferentialsFunctor_map :
    IsIso (biprod.desc (overDifferentialsFunctor.map i) (overDifferentialsFunctor.map j)) := by
  have h₁ : overDifferentialsFunctor.map i ≫ overTensorFst i j h = 𝟙 _ :=
    overDifferentials_hom_ext _ _ fun x => by
      show overTensorFst i j h (overDifferentialsFunctor.map i (overDifferentialsMk X x)) =
        overDifferentialsMk X x
      rw [overDifferentialsFunctor_map_mk, overTensorFst_mk,
        overTensorEquiv_symm_left, overTensorDerivFst_tmul, map_one, one_smul]
  have h₂ : overDifferentialsFunctor.map i ≫ overTensorSnd i j h = 0 :=
    overDifferentials_hom_ext _ _ fun x => by
      show overTensorSnd i j h (overDifferentialsFunctor.map i (overDifferentialsMk X x)) = 0
      rw [overDifferentialsFunctor_map_mk, overTensorSnd_mk,
        overTensorEquiv_symm_left, overTensorDerivSnd_tmul, overDifferentialsMk_one, smul_zero]
      rfl
  have h₃ : overDifferentialsFunctor.map j ≫ overTensorFst i j h = 0 :=
    overDifferentials_hom_ext _ _ fun y => by
      show overTensorFst i j h (overDifferentialsFunctor.map j (overDifferentialsMk Y y)) = 0
      rw [overDifferentialsFunctor_map_mk, overTensorFst_mk,
        overTensorEquiv_symm_right, overTensorDerivFst_tmul, overDifferentialsMk_one, smul_zero]
      rfl
  have h₄ : overDifferentialsFunctor.map j ≫ overTensorSnd i j h = 𝟙 _ :=
    overDifferentials_hom_ext _ _ fun y => by
      show overTensorSnd i j h (overDifferentialsFunctor.map j (overDifferentialsMk Y y)) =
        overDifferentialsMk Y y
      rw [overDifferentialsFunctor_map_mk, overTensorSnd_mk,
        overTensorEquiv_symm_right, overTensorDerivSnd_tmul, map_one, one_smul]
  have h₅ : overTensorFst i j h ≫ overDifferentialsFunctor.map i +
      overTensorSnd i j h ≫ overDifferentialsFunctor.map j = 𝟙 _ :=
    overDifferentials_hom_ext _ _ fun z => by
      obtain ⟨w, rfl⟩ := (overTensorEquiv i j h).surjective z
      let φi : overDifferentials X →ₗ[(B : Type u)] overDifferentials Z :=
        (overDifferentialsFunctor.map i).hom
      let φj : overDifferentials Y →ₗ[(B : Type u)] overDifferentials Z :=
        (overDifferentialsFunctor.map j).hom
      have hi : ∀ x, φi (overDifferentialsMk X x) = overDifferentialsMk Z (i.left.hom x) :=
        overDifferentialsFunctor_map_mk i
      have hj : ∀ y, φj (overDifferentialsMk Y y) = overDifferentialsMk Z (j.left.hom y) :=
        overDifferentialsFunctor_map_mk j
      show φi (overTensorFst i j h (overDifferentialsMk Z _)) +
        φj (overTensorSnd i j h (overDifferentialsMk Z _)) = overDifferentialsMk Z _
      rw [overTensorFst_mk, overTensorSnd_mk, AlgEquiv.symm_apply_apply]
      induction w using TensorProduct.induction_on with
      | zero => rw [map_zero, map_zero, map_zero, map_zero, map_zero, overDifferentialsMk_zero,
          add_zero]
      | add w w' hw hw' =>
          rw [map_add, map_add, map_add, map_add, map_add, overDifferentialsMk_add, ← hw, ← hw']
          abel
      | tmul x y =>
          rw [overTensorDerivFst_tmul, overTensorDerivSnd_tmul, map_smul, map_smul, hi, hj]
          show _ = overDifferentialsMk Z (i.left.hom x * j.left.hom y)
          rw [overDifferentialsMk_mul, augmentationRingHom_apply, augmentationRingHom_apply,
            ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, Over.w i, Over.w j,
            add_comm]
  refine ⟨biprod.lift (overTensorFst i j h) (overTensorSnd i j h), ?_, ?_⟩
  · apply biprod.hom_ext' <;> apply biprod.hom_ext <;>
      simp only [biprod.inl_desc_assoc, biprod.inr_desc_assoc, Category.assoc, biprod.lift_fst,
        biprod.lift_snd, Category.comp_id, biprod.inl_fst, biprod.inl_snd, biprod.inr_fst,
        biprod.inr_snd, h₁, h₂, h₃, h₄]
  · rw [biprod.lift_desc, h₅]

end Presentation

end Tensor

end CommAlgCat

end
