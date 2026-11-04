module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Coextension of scalars commutes with flat base change

Let `R` be a commutative ring, let `S` and `A` be commutative `R`-algebras and write
`B = S ⊗[R] A` for the tensor product algebra.  If `S` is flat over `R` and `A` is finitely
presented as an `R`-module, then for every `R`-module `E` the two natural `B`-modules

* `B ⊗[A] (A →ₗ[R] E)`, obtained by coextending `E` along `R → A` and then extending along
  `A → B`, and
* `B →ₗ[S] (S ⊗[R] E)`, obtained by extending `E` along `R → S` and then coextending along
  `S → B`

are isomorphic.

## Main definitions

* `ModuleCat.extendCoextendBaseChangeIso`: the isomorphism, in the form
  `(extendScalars h).obj ((coextendScalars (algebraMap R A)).obj E) ≅
   (coextendScalars (algebraMap S B)).obj ((extendScalars (algebraMap R S)).obj E)`
  where `h : A →+* B` is `Algebra.TensorProduct.includeRight`.

## Main statements

* `ModuleCat.extendCoextendBaseChangeIso_hom_apply`: the isomorphism sends the generator
  `(s ⊗ₜ a) ⊗ₜ φ` to the `S`-linear map taking `s' ⊗ₜ a'` to `(s' * s) ⊗ₜ φ (a' * a)`.

## Implementation notes

The underlying map is produced from the adjunction
`ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars`, which makes it `B`-linear by
construction; bijectivity is deduced from `Module.FinitePresentation.isBaseChange_map`, which is
where flatness of `S` and finite presentation of `A` are used.
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct

universe u

namespace ModuleCat

namespace CoextendBaseChange

/-- The underlying map of `ModuleCat.restrictScalars` is the identity: for a ring homomorphism
`f : R →+* A`, the `R`-module `(restrictScalars f).obj (of A A)` has `A` as its carrier. -/
def rcar {R A : Type u} [Ring R] [Ring A] (f : R →+* A) :
    ((restrictScalars f).obj (of A A)) ≃+ A where
  toFun b := b
  invFun b := b
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- The identity map of an `R`-algebra `A`, viewed as an `R`-linear equivalence onto the
restriction of scalars of `A` along `algebraMap R A`. -/
def algBridge (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] :
    A ≃ₗ[R] ((restrictScalars (algebraMap R A)).obj (of A A)) where
  toFun a := a
  map_add' _ _ := rfl
  map_smul' r a := Algebra.smul_def r a
  invFun a := a
  left_inv _ := rfl
  right_inv _ := rfl

variable {R S A : Type u} [CommRing R] [CommRing S] [CommRing A] [Algebra R S] [Algebra R A]

/-- The structure map `A →+* S ⊗[R] A` of the tensor product algebra. -/
abbrev incl (R S A : Type u) [CommRing R] [CommRing S] [CommRing A] [Algebra R S]
    [Algebra R A] : A →+* TensorProduct R S A :=
  (Algebra.TensorProduct.includeRight : A →ₐ[R] TensorProduct R S A).toRingHom

/-- `S`, with scalars restricted along `algebraMap R S`, is a scalar tower over `R` and `S`. -/
instance : IsScalarTower R S ((restrictScalars (algebraMap R S)).obj (of S S)) where
  smul_assoc r s x := by
    have h : ∀ y : S, (r • s) * y = algebraMap R S r * (s * y) := fun y => by
      rw [Algebra.smul_def, mul_assoc]
    exact h x

variable (E : ModuleCat.{u} R)

/-- The carrier of `(extendScalars (algebraMap R S)).obj E` is `S ⊗[R] E`. -/
noncomputable def extBridge : TensorProduct R S E ≃ₗ[S] ((extendScalars (algebraMap R S)).obj E) :=
  TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S S) (LinearEquiv.refl R E)

/-- The carrier of `(extendScalars h).obj ((coextendScalars (algebraMap R A)).obj E)` is
`(S ⊗[R] A) ⊗[A] (A →ₗ[R] E)`. -/
def zbridge :
    TensorProduct A ((restrictScalars (incl R S A)).obj
        (of (TensorProduct R S A) (TensorProduct R S A)))
      ((restrictScalars (algebraMap R A)).obj (of A A) →ₗ[R] E) ≃+
      ((extendScalars (incl R S A)).obj ((coextendScalars (algebraMap R A)).obj E)) where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- The `A`-linear map sending `φ : A →ₗ[R] E` to the base change `S ⊗[R] A →ₗ[S] S ⊗[R] E`,
written as a map into the coextension of `S ⊗[R] E` along `S → S ⊗[R] A`. -/
noncomputable def theta :
    ((restrictScalars (algebraMap R A)).obj (of A A) →ₗ[R] E) →+
      ((restrictScalars (algebraMap S (TensorProduct R S A))).obj
          (of (TensorProduct R S A) (TensorProduct R S A)) →ₗ[S]
        ((extendScalars (algebraMap R S)).obj E)) where
  toFun φ :=
    LinearEquiv.arrowCongr (algBridge S (TensorProduct R S A)) (extBridge E)
      (LinearMap.baseChange S
        ((LinearEquiv.arrowCongr (algBridge R A) (LinearEquiv.refl R E)).symm φ))
  map_zero' := by ext b; simp
  map_add' φ ψ := by ext b; simp

/-- The defining formula for `CoextendBaseChange.theta`. -/
lemma theta_tmul (φ : (restrictScalars (algebraMap R A)).obj (of A A) →ₗ[R] E) (s : S) (a : A) :
    theta E φ (algBridge S (TensorProduct R S A) (s ⊗ₜ[R] a)) =
      (s ⊗ₜ[R] φ a : (extendScalars (algebraMap R S)).obj E) := rfl

/-- The defining formula for `CoextendBaseChange.theta`, with the argument written as an
element of `S ⊗[R] A`. -/
lemma theta_tmul' (φ : (restrictScalars (algebraMap R A)).obj (of A A) →ₗ[R] E) (s : S) (a : A) :
    theta E φ ((s ⊗ₜ[R] a : TensorProduct R S A)) =
      (s ⊗ₜ[R] φ a : (extendScalars (algebraMap R S)).obj E) := rfl

/-- Unfolding of the coextension action, with arguments written as elements of `S ⊗[R] A`. -/
lemma coeSmul_apply' (ψ : (restrictScalars (algebraMap S (TensorProduct R S A))).obj
      (of (TensorProduct R S A) (TensorProduct R S A)) →ₗ[S]
        ((extendScalars (algebraMap R S)).obj E)) (b b' : TensorProduct R S A) :
    (b • ψ) (b' : TensorProduct R S A) = ψ ((b' * b : TensorProduct R S A)) := rfl

/-- Unfolding of the coextension action on the target of `CoextendBaseChange.theta`. -/
lemma coeSmul_apply (ψ : (restrictScalars (algebraMap S (TensorProduct R S A))).obj
      (of (TensorProduct R S A) (TensorProduct R S A)) →ₗ[S]
        ((extendScalars (algebraMap R S)).obj E)) (b b' : TensorProduct R S A) :
    (b • ψ) (algBridge S (TensorProduct R S A) b') =
      ψ (algBridge S (TensorProduct R S A) (b' * b)) := rfl

/-- Multiplication by `s ⊗ₜ 1` in `S ⊗[R] A` is the action of `s`. -/
lemma mul_tmul_one (s : S) (c : TensorProduct R S A) : c * (s ⊗ₜ[R] (1 : A)) = s • c := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | tmul s' a => simp [Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.smul_tmul', mul_comm]
  | add x y hx hy => simp [add_mul, hx, hy, smul_add]

/-- The scalars `s ⊗ₜ 1` act on the coextension as the scalars `s : S` do. -/
lemma smul_theta (ψ : (restrictScalars (algebraMap S (TensorProduct R S A))).obj
      (of (TensorProduct R S A) (TensorProduct R S A)) →ₗ[S]
        ((extendScalars (algebraMap R S)).obj E)) (s : S) :
    ((s ⊗ₜ[R] (1 : A) : TensorProduct R S A)) • ψ = s • ψ := by
  refine LinearMap.ext fun b => ?_
  obtain ⟨c, rfl⟩ := (algBridge S (TensorProduct R S A)).surjective b
  rw [coeSmul_apply, LinearMap.smul_apply, ← map_smul, ← map_smul, mul_tmul_one]

/-- `CoextendBaseChange.theta` is `A`-linear. -/
lemma theta_smul (φ : (restrictScalars (algebraMap R A)).obj (of A A) →ₗ[R] E) (a : A) :
    theta (S := S) E (a • φ) = ((1 : S) ⊗ₜ[R] a : TensorProduct R S A) • theta (S := S) E φ := by
  refine LinearMap.ext fun b => ?_
  obtain ⟨c, rfl⟩ := (algBridge S (TensorProduct R S A)).surjective b
  induction c using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul s a' =>
      rw [coeSmul_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, theta_tmul, theta_tmul,
        CoextendScalars.smul_apply']
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

/-- Unfolding of the coextension action of `A` on `A →ₗ[R] E`. -/
lemma coextSmul_apply (a : A) (φ : (restrictScalars (algebraMap R A)).obj (of A A) →ₗ[R] E)
    (x : (restrictScalars (algebraMap R A)).obj (of A A)) :
    (a • φ) x = φ (algBridge R A ((algBridge R A).symm x * a)) := rfl

/-- On `A →ₗ[R] E` the action of `r : R` agrees with the action of `algebraMap R A r`. -/
lemma coext_smul_eq (r : R) (φ : (restrictScalars (algebraMap R A)).obj (of A A) →ₗ[R] E) :
    r • φ = (algebraMap R A r) • φ := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨a, rfl⟩ := (algBridge R A).surjective x
  rw [LinearMap.smul_apply, coextSmul_apply, LinearEquiv.symm_apply_apply, ← map_smul,
    ← map_smul]
  congr 2
  rw [Algebra.smul_def, mul_comm]

/-- Unfolding of the `A`-action on `S ⊗[R] A` coming from `Algebra.TensorProduct.includeRight`. -/
lemma smul_rcar_symm (a : A) (b : TensorProduct R S A) :
    a • (rcar (incl R S A)).symm b = (rcar (incl R S A)).symm (((1 : S) ⊗ₜ[R] a) * b) := rfl

/-- A computation in `S ⊗[R] A`. -/
lemma one_tmul_mul (r : R) (s : S) :
    ((1 : S) ⊗ₜ[R] (algebraMap R A r)) * (s ⊗ₜ[R] (1 : A)) = (r • s) ⊗ₜ[R] (1 : A) := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one,
    Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul]

/-- `CoextendBaseChange.theta`, packaged as a morphism of `A`-modules. -/
noncomputable def thetaHom :
    (coextendScalars (algebraMap R A)).obj E ⟶
      (restrictScalars (incl R S A)).obj
        ((coextendScalars (algebraMap S (TensorProduct R S A))).obj
          ((extendScalars (algebraMap R S)).obj E)) :=
  ofHom (Y := (restrictScalars (incl R S A)).obj
      ((coextendScalars (algebraMap S (TensorProduct R S A))).obj
        ((extendScalars (algebraMap R S)).obj E)))
    { toFun := theta E
      map_add' := (theta E).map_add
      map_smul' := fun a φ => theta_smul E φ a }

/-- The forward morphism of the base-change isomorphism. -/
noncomputable def fwd :
    (extendScalars (incl R S A)).obj ((coextendScalars (algebraMap R A)).obj E) ⟶
      (coextendScalars (algebraMap S (TensorProduct R S A))).obj
        ((extendScalars (algebraMap R S)).obj E) :=
  ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars (incl R S A) (thetaHom E)

/-- The defining formula for `CoextendBaseChange.fwd`. -/
lemma fwd_tmul (b : TensorProduct R S A)
    (φ : (restrictScalars (algebraMap R A)).obj (of A A) →ₗ[R] E) :
    fwd E (zbridge E ((rcar (incl R S A)).symm b ⊗ₜ φ)) =
      ((b • theta E φ : (restrictScalars (algebraMap S (TensorProduct R S A))).obj
        (of (TensorProduct R S A) (TensorProduct R S A)) →ₗ[S]
          ((extendScalars (algebraMap R S)).obj E))) := rfl

/-- The additive map `S ⊗[R] (A →ₗ[R] E) → (S ⊗[R] A) ⊗[A] (A →ₗ[R] E)` sending `s ⊗ₜ φ` to
`(s ⊗ₜ 1) ⊗ₜ φ`. -/
noncomputable def alpha :
    TensorProduct R S ((restrictScalars (algebraMap R A)).obj (of A A) →ₗ[R] E) →+
      TensorProduct A ((restrictScalars (incl R S A)).obj
          (of (TensorProduct R S A) (TensorProduct R S A)))
        ((restrictScalars (algebraMap R A)).obj (of A A) →ₗ[R] E) :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk'
      (fun s => AddMonoidHom.mk'
        (fun φ => (rcar (incl R S A)).symm (s ⊗ₜ[R] (1 : A)) ⊗ₜ φ)
        (fun _ _ => TensorProduct.tmul_add _ _ _))
      (fun s₁ s₂ => AddMonoidHom.ext fun φ => by
        change (rcar (incl R S A)).symm ((s₁ + s₂) ⊗ₜ[R] (1 : A)) ⊗ₜ φ =
          (rcar (incl R S A)).symm (s₁ ⊗ₜ[R] (1 : A)) ⊗ₜ φ +
            (rcar (incl R S A)).symm (s₂ ⊗ₜ[R] (1 : A)) ⊗ₜ φ
        rw [TensorProduct.add_tmul, map_add, TensorProduct.add_tmul]))
    (fun r s φ => by
      change (rcar (incl R S A)).symm ((r • s) ⊗ₜ[R] (1 : A)) ⊗ₜ φ =
        (rcar (incl R S A)).symm (s ⊗ₜ[R] (1 : A)) ⊗ₜ (r • φ)
      rw [coext_smul_eq, ← TensorProduct.smul_tmul, smul_rcar_symm, one_tmul_mul])

/-- The defining formula for `CoextendBaseChange.alpha`. -/
lemma alpha_tmul (s : S) (φ : (restrictScalars (algebraMap R A)).obj (of A A) →ₗ[R] E) :
    alpha E (s ⊗ₜ[R] φ) = (rcar (incl R S A)).symm (s ⊗ₜ[R] (1 : A)) ⊗ₜ φ := rfl

/-- `CoextendBaseChange.alpha` is surjective. -/
lemma alpha_surjective : Function.Surjective (alpha (S := S) (A := A) E) := by
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul b φ =>
      obtain ⟨c, rfl⟩ := (rcar (incl R S A)).symm.surjective b
      induction c using TensorProduct.induction_on with
      | zero => exact ⟨0, by rw [map_zero, map_zero, TensorProduct.zero_tmul]⟩
      | tmul s a =>
          refine ⟨s ⊗ₜ[R] (a • φ), ?_⟩
          rw [alpha_tmul, ← TensorProduct.smul_tmul, smul_rcar_symm,
            Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
      | add c₁ c₂ h₁ h₂ =>
          obtain ⟨y₁, hy₁⟩ := h₁
          obtain ⟨y₂, hy₂⟩ := h₂
          refine ⟨y₁ + y₂, ?_⟩
          rw [map_add, hy₁, hy₂, map_add, TensorProduct.add_tmul]
  | add x y hx hy =>
      obtain ⟨y₁, hy₁⟩ := hx
      obtain ⟨y₂, hy₂⟩ := hy
      exact ⟨y₁ + y₂, by rw [map_add, hy₁, hy₂]⟩

/-- `CoextendBaseChange.alpha`, with values in the extension-of-scalars object. -/
noncomputable def alphaZ :
    TensorProduct R S ((restrictScalars (algebraMap R A)).obj (of A A) →ₗ[R] E) →+
      ((extendScalars (incl R S A)).obj ((coextendScalars (algebraMap R A)).obj E)) :=
  (zbridge E).toAddMonoidHom.comp (alpha E)

/-- The defining formula for `CoextendBaseChange.alphaZ`. -/
lemma alphaZ_tmul (s : S) (φ : (restrictScalars (algebraMap R A)).obj (of A A) →ₗ[R] E) :
    alphaZ E (s ⊗ₜ[R] φ) =
      zbridge E ((rcar (incl R S A)).symm (s ⊗ₜ[R] (1 : A)) ⊗ₜ φ) := rfl

/-- `CoextendBaseChange.alphaZ` is surjective. -/
lemma alphaZ_surjective : Function.Surjective (alphaZ (S := S) (A := A) E) :=
  (zbridge E).surjective.comp (alpha_surjective E)

variable [Module.Flat R S] [Module.FinitePresentation R A]

/-- The base-change equivalence `S ⊗[R] (A →ₗ[R] E) ≃ₗ[S] (S ⊗[R] A →ₗ[S] S ⊗[R] E)`, rewritten
in terms of the restriction-of-scalars carriers. -/
noncomputable def psi :
    TensorProduct R S ((restrictScalars (algebraMap R A)).obj (of A A) →ₗ[R] E) ≃ₗ[S]
      ((restrictScalars (algebraMap S (TensorProduct R S A))).obj
          (of (TensorProduct R S A) (TensorProduct R S A)) →ₗ[S]
        ((extendScalars (algebraMap R S)).obj E)) :=
  TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S S)
      (LinearEquiv.arrowCongr (algBridge R A) (LinearEquiv.refl R E)).symm ≪≫ₗ
    (Module.FinitePresentation.isBaseChange_map R A E S).equiv ≪≫ₗ
      LinearEquiv.arrowCongr (algBridge S (TensorProduct R S A)) (extBridge E)

/-- The defining formula for `CoextendBaseChange.psi`. -/
lemma psi_tmul (s : S) (φ : (restrictScalars (algebraMap R A)).obj (of A A) →ₗ[R] E) :
    psi E (s ⊗ₜ[R] φ) = s • theta E φ := by
  simp only [psi, LinearEquiv.trans_apply, TensorProduct.AlgebraTensorModule.congr_tmul,
    IsBaseChange.equiv_tmul, map_smul]
  rfl

/-- `CoextendBaseChange.fwd` composed with `CoextendBaseChange.alphaZ` is
`CoextendBaseChange.psi`. -/
lemma fwd_alphaZ
    (y : TensorProduct R S ((restrictScalars (algebraMap R A)).obj (of A A) →ₗ[R] E)) :
    fwd E (alphaZ E y) = psi E y := by
  induction y using TensorProduct.induction_on with
  | zero =>
      rw [map_zero, map_zero]
      exact (map_zero _).symm
  | tmul s φ => rw [alphaZ_tmul, fwd_tmul, psi_tmul, smul_theta]
  | add x y hx hy =>
      rw [map_add, map_add, hx, hy]
      exact (map_add _ _ _).symm

/-- `CoextendBaseChange.fwd` is bijective. -/
lemma fwd_bijective : Function.Bijective (fwd (S := S) (A := A) E) := by
  refine ⟨fun x₁ x₂ hx => ?_, fun w => ?_⟩
  · obtain ⟨y₁, rfl⟩ := alphaZ_surjective E x₁
    obtain ⟨y₂, rfl⟩ := alphaZ_surjective E x₂
    rw [fwd_alphaZ, fwd_alphaZ] at hx
    rw [(psi E).injective hx]
  · obtain ⟨y, hy⟩ := (psi E).surjective w
    exact ⟨alphaZ E y, by rw [fwd_alphaZ, hy]⟩

end CoextendBaseChange

/-- Coextension of scalars along `R → A` commutes with flat base change along `R → S`. -/
public noncomputable def extendCoextendBaseChangeIso
    {R S A : Type u} [CommRing R] [CommRing S] [CommRing A] [Algebra R S] [Algebra R A]
    [Module.Flat R S] [Module.FinitePresentation R A] (E : ModuleCat.{u} R) :
    (ModuleCat.extendScalars.{u, u, u}
          (Algebra.TensorProduct.includeRight : A →ₐ[R] TensorProduct R S A).toRingHom).obj
        ((ModuleCat.coextendScalars.{u, u, u} (algebraMap R A)).obj E) ≅
      (ModuleCat.coextendScalars.{u, u, u} (algebraMap S (TensorProduct R S A))).obj
        ((ModuleCat.extendScalars.{u, u, u} (algebraMap R S)).obj E) :=
  LinearEquiv.toModuleIso
    (LinearEquiv.ofBijective (CoextendBaseChange.fwd E).hom
      (CoextendBaseChange.fwd_bijective E))

/-- The isomorphism `ModuleCat.extendCoextendBaseChangeIso` sends the generator
`(s ⊗ₜ a) ⊗ₜ φ` to the `S`-linear map taking `s' ⊗ₜ a'` to `(s' * s) ⊗ₜ φ (a' * a)`. -/
public lemma extendCoextendBaseChangeIso_hom_apply
    {R S A : Type u} [CommRing R] [CommRing S] [CommRing A] [Algebra R S] [Algebra R A]
    [Module.Flat R S] [Module.FinitePresentation R A] (E : ModuleCat.{u} R)
    (φ : (ModuleCat.restrictScalars (algebraMap R A)).obj (ModuleCat.of A A) →ₗ[R] E)
    (s s' : S) (a a' : A) :
    (extendCoextendBaseChangeIso E).hom
        (((s ⊗ₜ[R] a : TensorProduct R S A) ⊗ₜ[A] φ :
          TensorProduct A ((ModuleCat.restrictScalars
                (Algebra.TensorProduct.includeRight :
                  A →ₐ[R] TensorProduct R S A).toRingHom).obj
              (ModuleCat.of (TensorProduct R S A) (TensorProduct R S A)))
            ((ModuleCat.restrictScalars (algebraMap R A)).obj (ModuleCat.of A A) →ₗ[R] E)))
        (s' ⊗ₜ[R] a' : TensorProduct R S A) =
      (((s' * s) ⊗ₜ[R] φ ((a' * a : A)) :
        (ModuleCat.extendScalars (algebraMap R S)).obj E)) := by
  have h2 : (((s ⊗ₜ[R] a : TensorProduct R S A) • CoextendBaseChange.theta E φ :
        (ModuleCat.restrictScalars (algebraMap S (TensorProduct R S A))).obj
          (ModuleCat.of (TensorProduct R S A) (TensorProduct R S A)) →ₗ[S]
            ((ModuleCat.extendScalars (algebraMap R S)).obj E)))
        (s' ⊗ₜ[R] a' : TensorProduct R S A) =
      (((s' * s) ⊗ₜ[R] φ ((a' * a : A)) :
        (ModuleCat.extendScalars (algebraMap R S)).obj E)) := by
    rw [CoextendBaseChange.coeSmul_apply', Algebra.TensorProduct.tmul_mul_tmul,
      CoextendBaseChange.theta_tmul']
  exact h2

end ModuleCat

end
