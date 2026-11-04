module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LeftGradedModule
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import Mathlib.CategoryTheory.GradedObject

/-!
# The relative tensor product of graded modules over a sheaf of graded algebras

Let `O` be a sheaf of commutative rings on a site, let `A` be a sheaf of graded `O`-algebras,
let `P` be a right graded `A`-module and let `N` be a left graded `A`-module. Degree `n` of the
relative tensor product `P ⊗_A N` is the cokernel of the balance map
`⨁_{r + s + t = n} P^r ⊗_O A^s ⊗_O N^t → ⨁_{p + q = n} P^p ⊗_O N^q` which sends a local section
`x ⊗ a ⊗ y` to `xa ⊗ y - x ⊗ ay`.

## Main definitions

* `PresheafOfModules.tensorMk₃` is a morphism out of a triple objectwise tensor product of
  presheaves of modules, built from a trilinear family of maps on sections, and
  `PresheafOfModules.tensorObj₃_hom_ext` is the matching extensionality principle.
* `SheafOfModules.RelativeTensor.tensorSum` and `SheafOfModules.RelativeTensor.relationSum` are
  the two direct sums of the presentation, and
  `SheafOfModules.RelativeTensor.balanceMap` is the balance map between them.
* `SheafOfModules.RelativeTensor.gradedTensorPre` is degree `n` of `P ⊗_A N` as a presheaf of
  modules, and `SheafOfModules.RelativeTensor.gradedTensor` is its associated sheaf.
* `SheafOfModules.RelativeTensor.gradedTensorMap` is the functoriality of `P ⊗_A -` in the left
  graded module, and `SheafOfModules.RelativeTensor.gradedTensorMapRight` the functoriality of
  `- ⊗_A N` in the right graded module.
* `SheafOfModules.RelativeTensor.gradedTensorFunctor` is the functor `- ⊗_A N` from right graded
  `A`-modules to graded `O`-modules.
* `SheafOfModules.RelativeTensor.tmul` is the local section `x ⊗ y` of `P ⊗_A N`, and
  `SheafOfModules.RelativeTensor.Balanced` is an `A`-balanced bilinear family of total degree
  `n`: the datum a morphism out of degree `n` of `P ⊗_A N` amounts to.

## Main results

* `SheafOfModules.RelativeTensor.balanceMap_tmul` computes the balance map on a local section
  `x ⊗ a ⊗ y`, and `SheafOfModules.RelativeTensor.balanceMap_naturality` is its compatibility
  with a homomorphism of left graded modules.
* `SheafOfModules.RelativeTensor.Balanced.desc` and
  `SheafOfModules.RelativeTensor.gradedTensor_hom_ext` are the universal property of
  `P ⊗_A N`: a balanced bilinear family of total degree `n` descends to a morphism out of
  degree `n`, uniquely, and `SheafOfModules.RelativeTensor.Balanced.desc_tmul` computes the
  descent on `x ⊗ y`.
* `SheafOfModules.RelativeTensor.gradedTensorMap_tmul` and `gradedTensorMapRight_tmul` compute
  the two functorialities on a local section `x ⊗ y`.

## Implementation notes

The presentation is formed in presheaves of modules and sheafified once, at the end. This is
the same object as the cokernel of the sheafified balance map, sheafification being a left
adjoint and so preserving cokernels and direct sums, and it means every morphism out of a tensor
product below is given by a trilinear or bilinear family on sections with no extension along a
sheafification unit.

The homogeneous pieces of the algebra and of the two modules live in one and the same universe.
This is forced by the construction rather than chosen: the summand `P^r ⊗_O A^s ⊗_O N^t` lives
in the maximum of the three universes while `P^p ⊗_O N^q` omits the algebra, and the balance map
goes between direct sums of the two. The universes of the site and of the sheaf of rings stay
independent.

The base is a sheaf of *commutative* rings, written `Osharp`, with the sheaf of rings underlying
it obtained by `CategoryTheory.Sheaf.toRingCat`; this is what the objectwise tensor product of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/SheafificationTensor.lean` needs, and it is the
structure sheaf of a ringed site in the sense of the source.

## References

* [Stacks Project, Tag 0FR2](https://stacks.math.columbia.edu/tag/0FR2)
* [Stacks Project, Tag 0FQZ](https://stacks.math.columbia.edu/tag/0FQZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

open scoped TensorProduct

universe v u w z t m

namespace ModuleCat

section Lift₃

variable {R : Type w} [CommRing R]
  {M : Type z} [AddCommGroup M] [Module R M]
  {N : Type z} [AddCommGroup N] [Module R N]
  {L : Type z} [AddCommGroup L] [Module R L]
  {Q : Type z} [AddCommGroup Q] [Module R Q]

/-- Two linear maps out of a tensor product which agree on pure tensors are equal. -/
theorem tensorProduct_linearMap_ext {g h : (N ⊗[R] L) →ₗ[R] Q}
    (H : ∀ y z, g (y ⊗ₜ[R] z) = h (y ⊗ₜ[R] z)) : g = h :=
  TensorProduct.ext (LinearMap.ext fun y ↦ LinearMap.ext fun z ↦ H y z)

variable (f : M → N → L → Q)
  (ha₁ : ∀ x x' y z, f (x + x') y z = f x y z + f x' y z)
  (hs₁ : ∀ (r : R) x y z, f (r • x) y z = r • f x y z)
  (ha₂ : ∀ x y y' z, f x (y + y') z = f x y z + f x y' z)
  (hs₂ : ∀ (r : R) x y z, f x (r • y) z = r • f x y z)
  (ha₃ : ∀ x y z z', f x y (z + z') = f x y z + f x y z')
  (hs₃ : ∀ (r : R) x y z, f x y (r • z) = r • f x y z)

/-- The linear map `N ⊗[R] L →ₗ[R] Q` obtained from a trilinear map by fixing its first
argument. -/
noncomputable def trilinearInner (x : M) : (N ⊗[R] L) →ₗ[R] Q :=
  TensorProduct.lift (LinearMap.mk₂ R (f x) (ha₂ x) (hs₂ · x) (ha₃ x) (hs₃ · x))

omit [AddCommGroup M] [Module R M] in
/-- `ModuleCat.trilinearInner f … x` sends a pure tensor `y ⊗ z` to `f x y z`. -/
@[simp]
theorem trilinearInner_tmul (x : M) (y : N) (z : L) :
    trilinearInner f ha₂ hs₂ ha₃ hs₃ x (y ⊗ₜ[R] z) = f x y z :=
  TensorProduct.lift.tmul _ _

/-- A trilinear map on sections lifts to a morphism out of a right-bracketed triple tensor
product. -/
noncomputable def tensorLift₃ :
    ModuleCat.of R (M ⊗[R] (N ⊗[R] L)) ⟶ ModuleCat.of R Q :=
  ModuleCat.ofHom (TensorProduct.lift (LinearMap.mk₂ R
    (fun x w ↦ trilinearInner f ha₂ hs₂ ha₃ hs₃ x w)
    (fun x x' w ↦ by
      refine DFunLike.congr_fun (tensorProduct_linearMap_ext (g := trilinearInner f ha₂ hs₂ ha₃
        hs₃ (x + x')) (h := trilinearInner f ha₂ hs₂ ha₃ hs₃ x +
          trilinearInner f ha₂ hs₂ ha₃ hs₃ x') ?_) w
      intro y z
      simp [ha₁])
    (fun r x w ↦ by
      refine DFunLike.congr_fun (tensorProduct_linearMap_ext
        (g := trilinearInner f ha₂ hs₂ ha₃ hs₃ (r • x))
        (h := r • trilinearInner f ha₂ hs₂ ha₃ hs₃ x) ?_) w
      intro y z
      simp [hs₁])
    (fun x w w' ↦ map_add _ _ _)
    (fun r x w ↦ map_smul _ _ _)))

/-- `ModuleCat.tensorLift₃ f …` sends a pure tensor `x ⊗ (y ⊗ z)` to `f x y z`. -/
@[simp]
theorem tensorLift₃_tmul (x : M) (y : N) (z : L) :
    tensorLift₃ f ha₁ hs₁ ha₂ hs₂ ha₃ hs₃ (x ⊗ₜ[R] (y ⊗ₜ[R] z)) = f x y z := by
  show trilinearInner f ha₂ hs₂ ha₃ hs₃ x (y ⊗ₜ[R] z) = _
  simp

/-- Two morphisms out of a right-bracketed triple tensor product which agree on pure tensors
are equal. -/
theorem tensor_ext₃ {T : ModuleCat.{z} R}
    {g h : ModuleCat.of R (M ⊗[R] (N ⊗[R] L)) ⟶ T}
    (H : ∀ (x : M) (y : N) (z : L), g (x ⊗ₜ[R] (y ⊗ₜ[R] z)) = h (x ⊗ₜ[R] (y ⊗ₜ[R] z))) :
    g = h := by
  refine ModuleCat.tensor_ext fun x w ↦ ?_
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul y z => exact H x y z
  | add w w' hw hw' =>
    rw [TensorProduct.tmul_add]
    rw [map_add (ConcreteCategory.hom g), map_add (ConcreteCategory.hom h), hw, hw']

end Lift₃

end ModuleCat

namespace PresheafOfModules

section TensorMk₃

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  {F : PresheafOfModules.{z} (O ⋙ forget₂ CommRingCat RingCat)}
  {G : PresheafOfModules.{z} (O ⋙ forget₂ CommRingCat RingCat)}
  {H : PresheafOfModules.{z} (O ⋙ forget₂ CommRingCat RingCat)}
  {Q : PresheafOfModules.{z} (O ⋙ forget₂ CommRingCat RingCat)}

/-- A morphism out of a right-bracketed triple objectwise tensor product of presheaves of
modules, built from a trilinear family of maps on sections compatible with restriction. -/
noncomputable def tensorMk₃
    (app : ∀ (X : Cᵒᵖ), F.obj X → G.obj X → H.obj X → Q.obj X)
    (add₁ : ∀ (X : Cᵒᵖ) (x x' : F.obj X) (y : G.obj X) (z : H.obj X),
      app X (x + x') y z = app X x y z + app X x' y z)
    (smul₁ : ∀ (X : Cᵒᵖ) (r : (O ⋙ forget₂ CommRingCat RingCat).obj X) (x : F.obj X)
      (y : G.obj X) (z : H.obj X), app X (r • x) y z = r • app X x y z)
    (add₂ : ∀ (X : Cᵒᵖ) (x : F.obj X) (y y' : G.obj X) (z : H.obj X),
      app X x (y + y') z = app X x y z + app X x y' z)
    (smul₂ : ∀ (X : Cᵒᵖ) (r : (O ⋙ forget₂ CommRingCat RingCat).obj X) (x : F.obj X)
      (y : G.obj X) (z : H.obj X), app X x (r • y) z = r • app X x y z)
    (add₃ : ∀ (X : Cᵒᵖ) (x : F.obj X) (y : G.obj X) (z z' : H.obj X),
      app X x y (z + z') = app X x y z + app X x y z')
    (smul₃ : ∀ (X : Cᵒᵖ) (r : (O ⋙ forget₂ CommRingCat RingCat).obj X) (x : F.obj X)
      (y : G.obj X) (z : H.obj X), app X x y (r • z) = r • app X x y z)
    (naturality : ∀ ⦃X Y : Cᵒᵖ⦄ (f : X ⟶ Y) (x : F.obj X) (y : G.obj X) (z : H.obj X),
      Q.restrictₛₗ f (app X x y z) =
        app Y (F.restrictₛₗ f x) (G.restrictₛₗ f y) (H.restrictₛₗ f z)) :
    tensorObj F (tensorObj G H) ⟶ Q where
  app X := ModuleCat.tensorLift₃ (app X) (add₁ X) (smul₁ X) (add₂ X) (smul₂ X) (add₃ X) (smul₃ X)
  naturality {X Y} f := by
    refine ModuleCat.tensor_ext₃ fun x y z ↦ ?_
    exact (naturality f x y z).symm

/-- `PresheafOfModules.tensorMk₃ app …` sends a pure tensor `x ⊗ (y ⊗ z)` of sections over `X`
to `app X x y z`. -/
@[simp]
theorem tensorMk₃_tmul
    (app : ∀ (X : Cᵒᵖ), F.obj X → G.obj X → H.obj X → Q.obj X) (add₁) (smul₁) (add₂) (smul₂)
    (add₃) (smul₃) (naturality) (X : Cᵒᵖ) (x : F.obj X) (y : G.obj X) (z : H.obj X) :
    Hom.app (tensorMk₃ app add₁ smul₁ add₂ smul₂ add₃ smul₃ naturality) X (x ⊗ₜ (y ⊗ₜ z)) =
      app X x y z :=
  ModuleCat.tensorLift₃_tmul (app X) (add₁ X) (smul₁ X) (add₂ X) (smul₂ X) (add₃ X) (smul₃ X)
    x y z

/-- Two morphisms out of a right-bracketed triple objectwise tensor product which agree on pure
tensors of sections are equal. -/
theorem tensorObj₃_hom_ext {φ ψ : tensorObj F (tensorObj G H) ⟶ Q}
    (h : ∀ (X : Cᵒᵖ) (x : F.obj X) (y : G.obj X) (z : H.obj X),
      Hom.app φ X (x ⊗ₜ (y ⊗ₜ z)) = Hom.app ψ X (x ⊗ₜ (y ⊗ₜ z))) : φ = ψ :=
  hom_ext fun X ↦ ModuleCat.tensor_ext₃ (h X)

end TensorMk₃

section TmulApp

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  {F : PresheafOfModules.{z} (O ⋙ forget₂ CommRingCat RingCat)}
  {G : PresheafOfModules.{z} (O ⋙ forget₂ CommRingCat RingCat)}
  {T : PresheafOfModules.{z} (O ⋙ forget₂ CommRingCat RingCat)}
  (φ : tensorObj F G ⟶ T)

/-- A morphism out of an objectwise tensor product is additive in the first factor of a pure
tensor of sections. -/
theorem app_tmul_add_left (X : Cᵒᵖ) (x x' : F.obj X) (y : G.obj X) :
    Hom.app φ X ((x + x') ⊗ₜ y) = Hom.app φ X (x ⊗ₜ y) + Hom.app φ X (x' ⊗ₜ y) := by
  have h : ((x + x') ⊗ₜ y : (tensorObj F G).obj X) = x ⊗ₜ y + x' ⊗ₜ y :=
    TensorProduct.add_tmul x x' y
  rw [h]
  exact map_add (ConcreteCategory.hom (Hom.app φ X)) _ _

/-- A morphism out of an objectwise tensor product is additive in the second factor of a pure
tensor of sections. -/
theorem app_tmul_add_right (X : Cᵒᵖ) (x : F.obj X) (y y' : G.obj X) :
    Hom.app φ X (x ⊗ₜ (y + y')) = Hom.app φ X (x ⊗ₜ y) + Hom.app φ X (x ⊗ₜ y') := by
  have h : (x ⊗ₜ (y + y') : (tensorObj F G).obj X) = x ⊗ₜ y + x ⊗ₜ y' :=
    TensorProduct.tmul_add x y y'
  rw [h]
  exact map_add (ConcreteCategory.hom (Hom.app φ X)) _ _

/-- A morphism out of an objectwise tensor product is linear in the first factor of a pure
tensor of sections. -/
theorem app_tmul_smul_left (X : Cᵒᵖ) (r : (O ⋙ forget₂ CommRingCat RingCat).obj X)
    (x : F.obj X) (y : G.obj X) :
    Hom.app φ X ((r • x) ⊗ₜ y) = r • Hom.app φ X (x ⊗ₜ y) := by
  have h : ((r • x) ⊗ₜ y : (tensorObj F G).obj X) = r • (x ⊗ₜ y) :=
    TensorProduct.smul_tmul' r x y
  rw [h]
  exact map_smul (ConcreteCategory.hom (Hom.app φ X)) r _

/-- A morphism out of an objectwise tensor product is linear in the second factor of a pure
tensor of sections. -/
theorem app_tmul_smul_right (X : Cᵒᵖ) (r : (O ⋙ forget₂ CommRingCat RingCat).obj X)
    (x : F.obj X) (y : G.obj X) :
    Hom.app φ X (x ⊗ₜ (r • y)) = r • Hom.app φ X (x ⊗ₜ y) := by
  have h : (x ⊗ₜ (r • y) : (tensorObj F G).obj X) = r • (x ⊗ₜ y) :=
    TensorProduct.tmul_smul r x y
  rw [h]
  exact map_smul (ConcreteCategory.hom (Hom.app φ X)) r _

/-- A morphism out of an objectwise tensor product vanishes on a pure tensor whose first factor
is zero. -/
theorem app_tmul_zero_left (X : Cᵒᵖ) (y : G.obj X) :
    Hom.app φ X ((0 : F.obj X) ⊗ₜ y) = 0 := by
  have h : ((0 : F.obj X) ⊗ₜ y : (tensorObj F G).obj X) = 0 := TensorProduct.zero_tmul _ y
  rw [h]
  exact map_zero (ConcreteCategory.hom (Hom.app φ X))

/-- A morphism out of an objectwise tensor product vanishes on a pure tensor whose second factor
is zero. -/
theorem app_tmul_zero_right (X : Cᵒᵖ) (x : F.obj X) :
    Hom.app φ X (x ⊗ₜ (0 : G.obj X)) = 0 := by
  have h : (x ⊗ₜ (0 : G.obj X) : (tensorObj F G).obj X) = 0 := TensorProduct.tmul_zero _ x
  rw [h]
  exact map_zero (ConcreteCategory.hom (Hom.app φ X))

/-- A morphism out of an objectwise tensor product commutes with an integer multiple in the
first factor of a pure tensor of sections. -/
theorem app_tmul_zsmul_left (X : Cᵒᵖ) (k : ℤ) (x : F.obj X) (y : G.obj X) :
    Hom.app φ X ((k • x) ⊗ₜ y) = k • Hom.app φ X (x ⊗ₜ y) :=
  map_zsmul (AddMonoidHom.mk' (fun u : F.obj X ↦ Hom.app φ X (u ⊗ₜ y))
    (fun u u' ↦ app_tmul_add_left φ X u u' y)) k x

/-- A morphism out of an objectwise tensor product commutes with an integer multiple in the
second factor of a pure tensor of sections. -/
theorem app_tmul_zsmul_right (X : Cᵒᵖ) (k : ℤ) (x : F.obj X) (y : G.obj X) :
    Hom.app φ X (x ⊗ₜ (k • y)) = k • Hom.app φ X (x ⊗ₜ y) :=
  map_zsmul (AddMonoidHom.mk' (fun w : G.obj X ↦ Hom.app φ X (x ⊗ₜ w))
    (fun w w' ↦ app_tmul_add_right φ X x w w')) k y

/-- The value of a morphism out of an objectwise tensor product on a pure tensor of sections
commutes with restriction. -/
theorem app_tmul_restrictₛₗ {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : F.obj X) (y : G.obj X) :
    T.restrictₛₗ f (Hom.app φ X (x ⊗ₜ y)) =
      Hom.app φ Y (F.restrictₛₗ f x ⊗ₜ G.restrictₛₗ f y) := by
  refine (restrictₛₗ_naturality_apply φ f (x ⊗ₜ y)).symm.trans ?_
  exact congrArg (fun w ↦ Hom.app φ Y w) (tensorObj_restrictₛₗ_tmul f x y)

end TmulApp

section TmulApp₃

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  {F : PresheafOfModules.{z} (O ⋙ forget₂ CommRingCat RingCat)}
  {G : PresheafOfModules.{z} (O ⋙ forget₂ CommRingCat RingCat)}
  {H : PresheafOfModules.{z} (O ⋙ forget₂ CommRingCat RingCat)}
  {T : PresheafOfModules.{z} (O ⋙ forget₂ CommRingCat RingCat)}
  (φ : tensorObj F (tensorObj G H) ⟶ T)

/-- A morphism out of a triple objectwise tensor product is additive in the first factor of a
pure tensor of sections. -/
theorem app_tmul₃_add_left (X : Cᵒᵖ) (x x' : F.obj X) (y : G.obj X) (z : H.obj X) :
    Hom.app φ X ((x + x') ⊗ₜ (y ⊗ₜ z)) =
      Hom.app φ X (x ⊗ₜ (y ⊗ₜ z)) + Hom.app φ X (x' ⊗ₜ (y ⊗ₜ z)) :=
  app_tmul_add_left φ X x x' (y ⊗ₜ z)

/-- A morphism out of a triple objectwise tensor product is linear in the first factor of a pure
tensor of sections. -/
theorem app_tmul₃_smul_left (X : Cᵒᵖ) (r : (O ⋙ forget₂ CommRingCat RingCat).obj X)
    (x : F.obj X) (y : G.obj X) (z : H.obj X) :
    Hom.app φ X ((r • x) ⊗ₜ (y ⊗ₜ z)) = r • Hom.app φ X (x ⊗ₜ (y ⊗ₜ z)) :=
  app_tmul_smul_left φ X r x (y ⊗ₜ z)

/-- A morphism out of a triple objectwise tensor product is additive in the middle factor of a
pure tensor of sections. -/
theorem app_tmul₃_add_mid (X : Cᵒᵖ) (x : F.obj X) (y y' : G.obj X) (z : H.obj X) :
    Hom.app φ X (x ⊗ₜ ((y + y') ⊗ₜ z)) =
      Hom.app φ X (x ⊗ₜ (y ⊗ₜ z)) + Hom.app φ X (x ⊗ₜ (y' ⊗ₜ z)) := by
  have e : ((y + y') ⊗ₜ z : (tensorObj G H).obj X) = y ⊗ₜ z + y' ⊗ₜ z :=
    TensorProduct.add_tmul y y' z
  rw [e]
  exact app_tmul_add_right φ X x (y ⊗ₜ z) (y' ⊗ₜ z)

/-- A morphism out of a triple objectwise tensor product is linear in the middle factor of a
pure tensor of sections. -/
theorem app_tmul₃_smul_mid (X : Cᵒᵖ) (r : (O ⋙ forget₂ CommRingCat RingCat).obj X)
    (x : F.obj X) (y : G.obj X) (z : H.obj X) :
    Hom.app φ X (x ⊗ₜ ((r • y) ⊗ₜ z)) = r • Hom.app φ X (x ⊗ₜ (y ⊗ₜ z)) := by
  have e : ((r • y) ⊗ₜ z : (tensorObj G H).obj X) = r • (y ⊗ₜ z) :=
    TensorProduct.smul_tmul' r y z
  rw [e]
  exact app_tmul_smul_right φ X r x (y ⊗ₜ z)

/-- A morphism out of a triple objectwise tensor product is additive in the last factor of a
pure tensor of sections. -/
theorem app_tmul₃_add_right (X : Cᵒᵖ) (x : F.obj X) (y : G.obj X) (z z' : H.obj X) :
    Hom.app φ X (x ⊗ₜ (y ⊗ₜ (z + z'))) =
      Hom.app φ X (x ⊗ₜ (y ⊗ₜ z)) + Hom.app φ X (x ⊗ₜ (y ⊗ₜ z')) := by
  have e : (y ⊗ₜ (z + z') : (tensorObj G H).obj X) = y ⊗ₜ z + y ⊗ₜ z' :=
    TensorProduct.tmul_add y z z'
  rw [e]
  exact app_tmul_add_right φ X x (y ⊗ₜ z) (y ⊗ₜ z')

/-- A morphism out of a triple objectwise tensor product is linear in the last factor of a pure
tensor of sections. -/
theorem app_tmul₃_smul_right (X : Cᵒᵖ) (r : (O ⋙ forget₂ CommRingCat RingCat).obj X)
    (x : F.obj X) (y : G.obj X) (z : H.obj X) :
    Hom.app φ X (x ⊗ₜ (y ⊗ₜ (r • z))) = r • Hom.app φ X (x ⊗ₜ (y ⊗ₜ z)) := by
  have e : (y ⊗ₜ (r • z) : (tensorObj G H).obj X) = r • (y ⊗ₜ z) :=
    TensorProduct.tmul_smul r y z
  rw [e]
  exact app_tmul_smul_right φ X r x (y ⊗ₜ z)

/-- The value of a morphism out of a triple objectwise tensor product on a pure tensor of
sections commutes with restriction. -/
theorem app_tmul₃_restrictₛₗ {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : F.obj X) (y : G.obj X)
    (z : H.obj X) :
    T.restrictₛₗ f (Hom.app φ X (x ⊗ₜ (y ⊗ₜ z))) =
      Hom.app φ Y (F.restrictₛₗ f x ⊗ₜ (G.restrictₛₗ f y ⊗ₜ H.restrictₛₗ f z)) := by
  refine (app_tmul_restrictₛₗ φ f x (y ⊗ₜ z)).trans ?_
  rw [tensorObj_restrictₛₗ_tmul]

end TmulApp₃

section SignedDiff

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  {F F' G G' H H' T : PresheafOfModules.{z} (O ⋙ forget₂ CommRingCat RingCat)}

/-- The signed differential `u ⊗ w ↦ ι₁ (dF u ⊗ w) + c • ι₂ (u ⊗ dG w)` on an objectwise tensor
product. -/
noncomputable def tensorSignedDiff (c : ℤ) (dF : F ⟶ F') (dG : G ⟶ G')
    (ι₁ : tensorObj F' G ⟶ T) (ι₂ : tensorObj F G' ⟶ T) : tensorObj F G ⟶ T :=
  tensorMk
    (fun X u w ↦ Hom.app ι₁ X (Hom.app dF X u ⊗ₜ w) +
      c • Hom.app ι₂ X (u ⊗ₜ Hom.app dG X w))
    (fun X u u' w ↦ by
      have h : Hom.app ι₁ X (Hom.app dF X (u + u') ⊗ₜ w) =
          Hom.app ι₁ X (Hom.app dF X u ⊗ₜ w) + Hom.app ι₁ X (Hom.app dF X u' ⊗ₜ w) :=
        (congrArg (fun v ↦ Hom.app ι₁ X (v ⊗ₜ w))
          (map_add (ConcreteCategory.hom (Hom.app dF X)) u u')).trans
          (app_tmul_add_left ι₁ X _ _ w)
      rw [h, app_tmul_add_left, smul_add]
      abel)
    (fun X r u w ↦ by
      have h : Hom.app ι₁ X (Hom.app dF X (r • u) ⊗ₜ w) =
          r • Hom.app ι₁ X (Hom.app dF X u ⊗ₜ w) :=
        (congrArg (fun v ↦ Hom.app ι₁ X (v ⊗ₜ w))
          (map_smul (ConcreteCategory.hom (Hom.app dF X)) r u)).trans
          (app_tmul_smul_left ι₁ X r _ w)
      rw [h, app_tmul_smul_left, smul_add, smul_comm])
    (fun X u w w' ↦ by
      have h : Hom.app ι₂ X (u ⊗ₜ Hom.app dG X (w + w')) =
          Hom.app ι₂ X (u ⊗ₜ Hom.app dG X w) + Hom.app ι₂ X (u ⊗ₜ Hom.app dG X w') :=
        (congrArg (fun v ↦ Hom.app ι₂ X (u ⊗ₜ v))
          (map_add (ConcreteCategory.hom (Hom.app dG X)) w w')).trans
          (app_tmul_add_right ι₂ X u _ _)
      rw [h, app_tmul_add_right, smul_add]
      abel)
    (fun X r u w ↦ by
      have h : Hom.app ι₂ X (u ⊗ₜ Hom.app dG X (r • w)) =
          r • Hom.app ι₂ X (u ⊗ₜ Hom.app dG X w) :=
        (congrArg (fun v ↦ Hom.app ι₂ X (u ⊗ₜ v))
          (map_smul (ConcreteCategory.hom (Hom.app dG X)) r w)).trans
          (app_tmul_smul_right ι₂ X r u _)
      rw [h, app_tmul_smul_right, smul_add, smul_comm])
    (fun X Y f u w ↦ by
      have h : T.restrictₛₗ f (Hom.app ι₁ X (Hom.app dF X u ⊗ₜ w) +
            c • Hom.app ι₂ X (u ⊗ₜ Hom.app dG X w)) =
          T.restrictₛₗ f (Hom.app ι₁ X (Hom.app dF X u ⊗ₜ w)) +
            c • T.restrictₛₗ f (Hom.app ι₂ X (u ⊗ₜ Hom.app dG X w)) := by
        rw [map_add (T.restrictₛₗ f),
          map_zsmul (T.restrictₛₗ f)]
      rw [h, app_tmul_restrictₛₗ, app_tmul_restrictₛₗ, restrictₛₗ_naturality_apply,
        restrictₛₗ_naturality_apply])

/-- The value of `PresheafOfModules.tensorSignedDiff` on a pure tensor `u ⊗ w`:
`ι₁ (dF u ⊗ w) + c • ι₂ (u ⊗ dG w)`. -/
@[simp]
theorem tensorSignedDiff_tmul (c : ℤ) (dF : F ⟶ F') (dG : G ⟶ G') (ι₁ : tensorObj F' G ⟶ T)
    (ι₂ : tensorObj F G' ⟶ T) (X : Cᵒᵖ) (u : F.obj X) (w : G.obj X) :
    Hom.app (tensorSignedDiff c dF dG ι₁ ι₂) X (u ⊗ₜ w) =
      Hom.app ι₁ X (Hom.app dF X u ⊗ₜ w) + c • Hom.app ι₂ X (u ⊗ₜ Hom.app dG X w) :=
  tensorMk_tmul _ _ _ _ _ _ X u w

/-- The signed differential
`x ⊗ y ⊗ z ↦ ι₁ (dF x ⊗ y ⊗ z) + c₂ • ι₂ (x ⊗ dG y ⊗ z) + c₃ • ι₃ (x ⊗ y ⊗ dH z)`
on a triple objectwise tensor product. -/
noncomputable def tensorSignedDiff₃ (c₂ c₃ : ℤ) (dF : F ⟶ F') (dG : G ⟶ G') (dH : H ⟶ H')
    (ι₁ : tensorObj F' (tensorObj G H) ⟶ T) (ι₂ : tensorObj F (tensorObj G' H) ⟶ T)
    (ι₃ : tensorObj F (tensorObj G H') ⟶ T) : tensorObj F (tensorObj G H) ⟶ T :=
  tensorMk₃
    (fun X x y z ↦ Hom.app ι₁ X (Hom.app dF X x ⊗ₜ (y ⊗ₜ z)) +
      (c₂ • Hom.app ι₂ X (x ⊗ₜ (Hom.app dG X y ⊗ₜ z)) +
        c₃ • Hom.app ι₃ X (x ⊗ₜ (y ⊗ₜ Hom.app dH X z))))
    (fun X x x' y z ↦ by
      have h : Hom.app ι₁ X (Hom.app dF X (x + x') ⊗ₜ (y ⊗ₜ z)) =
          Hom.app ι₁ X (Hom.app dF X x ⊗ₜ (y ⊗ₜ z)) +
            Hom.app ι₁ X (Hom.app dF X x' ⊗ₜ (y ⊗ₜ z)) :=
        (congrArg (fun v ↦ Hom.app ι₁ X (v ⊗ₜ (y ⊗ₜ z)))
          (map_add (ConcreteCategory.hom (Hom.app dF X)) x x')).trans
          (app_tmul₃_add_left ι₁ X _ _ y z)
      rw [h, app_tmul₃_add_left, app_tmul₃_add_left, smul_add, smul_add]
      abel)
    (fun X r x y z ↦ by
      have h : Hom.app ι₁ X (Hom.app dF X (r • x) ⊗ₜ (y ⊗ₜ z)) =
          r • Hom.app ι₁ X (Hom.app dF X x ⊗ₜ (y ⊗ₜ z)) :=
        (congrArg (fun v ↦ Hom.app ι₁ X (v ⊗ₜ (y ⊗ₜ z)))
          (map_smul (ConcreteCategory.hom (Hom.app dF X)) r x)).trans
          (app_tmul₃_smul_left ι₁ X r _ y z)
      rw [h, app_tmul₃_smul_left, app_tmul₃_smul_left, smul_add, smul_add, smul_comm c₂ r,
        smul_comm c₃ r])
    (fun X x y y' z ↦ by
      have h : Hom.app ι₂ X (x ⊗ₜ (Hom.app dG X (y + y') ⊗ₜ z)) =
          Hom.app ι₂ X (x ⊗ₜ (Hom.app dG X y ⊗ₜ z)) +
            Hom.app ι₂ X (x ⊗ₜ (Hom.app dG X y' ⊗ₜ z)) :=
        (congrArg (fun v ↦ Hom.app ι₂ X (x ⊗ₜ (v ⊗ₜ z)))
          (map_add (ConcreteCategory.hom (Hom.app dG X)) y y')).trans
          (app_tmul₃_add_mid ι₂ X x _ _ z)
      rw [h, app_tmul₃_add_mid, app_tmul₃_add_mid, smul_add, smul_add]
      abel)
    (fun X r x y z ↦ by
      have h : Hom.app ι₂ X (x ⊗ₜ (Hom.app dG X (r • y) ⊗ₜ z)) =
          r • Hom.app ι₂ X (x ⊗ₜ (Hom.app dG X y ⊗ₜ z)) :=
        (congrArg (fun v ↦ Hom.app ι₂ X (x ⊗ₜ (v ⊗ₜ z)))
          (map_smul (ConcreteCategory.hom (Hom.app dG X)) r y)).trans
          (app_tmul₃_smul_mid ι₂ X r x _ z)
      rw [h, app_tmul₃_smul_mid, app_tmul₃_smul_mid, smul_add, smul_add, smul_comm c₂ r,
        smul_comm c₃ r])
    (fun X x y z z' ↦ by
      have h : Hom.app ι₃ X (x ⊗ₜ (y ⊗ₜ Hom.app dH X (z + z'))) =
          Hom.app ι₃ X (x ⊗ₜ (y ⊗ₜ Hom.app dH X z)) +
            Hom.app ι₃ X (x ⊗ₜ (y ⊗ₜ Hom.app dH X z')) :=
        (congrArg (fun v ↦ Hom.app ι₃ X (x ⊗ₜ (y ⊗ₜ v)))
          (map_add (ConcreteCategory.hom (Hom.app dH X)) z z')).trans
          (app_tmul₃_add_right ι₃ X x y _ _)
      rw [h, app_tmul₃_add_right, app_tmul₃_add_right, smul_add, smul_add]
      abel)
    (fun X r x y z ↦ by
      have h : Hom.app ι₃ X (x ⊗ₜ (y ⊗ₜ Hom.app dH X (r • z))) =
          r • Hom.app ι₃ X (x ⊗ₜ (y ⊗ₜ Hom.app dH X z)) :=
        (congrArg (fun v ↦ Hom.app ι₃ X (x ⊗ₜ (y ⊗ₜ v)))
          (map_smul (ConcreteCategory.hom (Hom.app dH X)) r z)).trans
          (app_tmul₃_smul_right ι₃ X r x y _)
      rw [h, app_tmul₃_smul_right, app_tmul₃_smul_right, smul_add, smul_add, smul_comm c₂ r,
        smul_comm c₃ r])
    (fun X Y f x y z ↦ by
      have h : T.restrictₛₗ f (Hom.app ι₁ X (Hom.app dF X x ⊗ₜ (y ⊗ₜ z)) +
            (c₂ • Hom.app ι₂ X (x ⊗ₜ (Hom.app dG X y ⊗ₜ z)) +
              c₃ • Hom.app ι₃ X (x ⊗ₜ (y ⊗ₜ Hom.app dH X z)))) =
          T.restrictₛₗ f (Hom.app ι₁ X (Hom.app dF X x ⊗ₜ (y ⊗ₜ z))) +
            (c₂ • T.restrictₛₗ f (Hom.app ι₂ X (x ⊗ₜ (Hom.app dG X y ⊗ₜ z))) +
              c₃ • T.restrictₛₗ f (Hom.app ι₃ X (x ⊗ₜ (y ⊗ₜ Hom.app dH X z)))) := by
        rw [map_add (T.restrictₛₗ f),
          map_add (T.restrictₛₗ f),
          map_zsmul (T.restrictₛₗ f),
          map_zsmul (T.restrictₛₗ f)]
      rw [h, app_tmul₃_restrictₛₗ, app_tmul₃_restrictₛₗ, app_tmul₃_restrictₛₗ,
        restrictₛₗ_naturality_apply, restrictₛₗ_naturality_apply,
        restrictₛₗ_naturality_apply])

/-- The value of `PresheafOfModules.tensorSignedDiff₃` on a pure tensor `x ⊗ (y ⊗ z)`:
`ι₁ (dF x ⊗ y ⊗ z) + (c₂ • ι₂ (x ⊗ dG y ⊗ z) + c₃ • ι₃ (x ⊗ y ⊗ dH z))`. -/
@[simp]
theorem tensorSignedDiff₃_tmul (c₂ c₃ : ℤ) (dF : F ⟶ F') (dG : G ⟶ G') (dH : H ⟶ H')
    (ι₁ : tensorObj F' (tensorObj G H) ⟶ T) (ι₂ : tensorObj F (tensorObj G' H) ⟶ T)
    (ι₃ : tensorObj F (tensorObj G H') ⟶ T) (X : Cᵒᵖ) (x : F.obj X) (y : G.obj X)
    (z : H.obj X) :
    Hom.app (tensorSignedDiff₃ c₂ c₃ dF dG dH ι₁ ι₂ ι₃) X (x ⊗ₜ (y ⊗ₜ z)) =
      Hom.app ι₁ X (Hom.app dF X x ⊗ₜ (y ⊗ₜ z)) +
        (c₂ • Hom.app ι₂ X (x ⊗ₜ (Hom.app dG X y ⊗ₜ z)) +
          c₃ • Hom.app ι₃ X (x ⊗ₜ (y ⊗ₜ Hom.app dH X z))) :=
  tensorMk₃_tmul _ _ _ _ _ _ _ _ X x y z

end SignedDiff

section TensorHomFunctorial

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  {F F' F'' G G' G'' : PresheafOfModules.{z} (O ⋙ forget₂ CommRingCat RingCat)}

/-- The objectwise tensor product of two identity morphisms is the identity. -/
theorem tensorHom_id_id : tensorHom (𝟙 F) (𝟙 G) = 𝟙 (tensorObj F G) :=
  tensorObj_hom_ext fun X x y ↦ by rw [tensorHom_tmul]; rfl

/-- The objectwise tensor product of morphisms of presheaves of modules is compatible with
composition. -/
theorem tensorHom_comp_tensorHom (u : F ⟶ F') (u' : F' ⟶ F'') (v : G ⟶ G') (v' : G' ⟶ G'') :
    tensorHom u v ≫ tensorHom u' v' = tensorHom (u ≫ u') (v ≫ v') :=
  tensorObj_hom_ext fun X x y ↦
    ((comp_app_apply (tensorHom u v) (tensorHom u' v') X (x ⊗ₜ y)).trans
        ((congrArg (fun w ↦ Hom.app (tensorHom u' v') X w)
            (tensorHom_tmul u v X x y)).trans
          (tensorHom_tmul u' v' X (Hom.app u X x) (Hom.app v X y)))).trans
      (tensorHom_tmul (u ≫ u') (v ≫ v') X x y).symm

end TensorHomFunctorial

end PresheafOfModules

namespace SheafOfModules

open CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] {Osharp : Sheaf J CommRingCat.{t}}

/-- The index set `{(p, q) | p + q = n}` of the direct sum computing degree `n` of the relative
tensor product. -/
abbrev TensorIndex (n : ℤ) : Type := {p : ℤ × ℤ // p.1 + p.2 = n}

/-- The index set `{(r, s, t) | r + s + t = n}` of the direct sum of relations imposed in degree
`n` of the relative tensor product. -/
abbrev RelationIndex (n : ℤ) : Type := {i : ℤ × ℤ × ℤ // i.1 + i.2.1 + i.2.2 = n}

variable {A : GradedAlgebra.{t, m} (toRingCat J Osharp)}

/-- The right action of a graded module commutes with restriction. -/
theorem GradedModule.smul_restrictₛₗ (P : GradedModule.{t, m, m} A) (n i : ℤ) {U V : Cᵒᵖ}
    (f : U ⟶ V) (x : (P.piece n).val.obj U) (a : (A.piece i).val.obj U) :
    (P.piece (n + i)).val.restrictₛₗ f (P.smul n i U x a) =
      P.smul n i V ((P.piece n).val.restrictₛₗ f x) ((A.piece i).val.restrictₛₗ f a) :=
  P.smul_naturality n i f x a

/-- The left action of a left graded module commutes with restriction. -/
theorem LeftGradedModule.smul_restrictₛₗ (N : LeftGradedModule.{t, m, m} A) (i n : ℤ)
    {U V : Cᵒᵖ} (f : U ⟶ V) (a : (A.piece i).val.obj U) (y : (N.piece n).val.obj U) :
    (N.piece (i + n)).val.restrictₛₗ f (N.smul i n U a y) =
      N.smul i n V ((A.piece i).val.restrictₛₗ f a) ((N.piece n).val.restrictₛₗ f y) :=
  N.smul_naturality i n f a y

/-- The right action of a homogeneous piece of the algebra, as a morphism out of the objectwise
tensor product. -/
noncomputable def GradedModule.smulHom (P : GradedModule.{t, m, m} A) (n i : ℤ) :
    PresheafOfModules.tensorObj (P.piece n).val (A.piece i).val ⟶ (P.piece (n + i)).val :=
  PresheafOfModules.tensorMk (fun X x a ↦ P.smul n i X x a)
    (fun X x x' a ↦ by rw [map_add]; rfl)
    (fun X r x a ↦ P.smul_smul_left n i X r x a)
    (fun X x a a' ↦ map_add (P.smul n i X x) a a')
    (fun X r x a ↦ P.smul_smul_right n i X r x a)
    (fun _ _ f x a ↦ P.smul_naturality n i f x a)

/-- `SheafOfModules.GradedModule.smulHom` sends a pure tensor `x ⊗ a` to the right action
`P.smul n i X x a`. -/
@[simp]
theorem GradedModule.smulHom_tmul (P : GradedModule.{t, m, m} A) (n i : ℤ) (X : Cᵒᵖ)
    (x : (P.piece n).val.obj X) (a : (A.piece i).val.obj X) :
    PresheafOfModules.Hom.app (P.smulHom n i) X (x ⊗ₜ a) = P.smul n i X x a :=
  PresheafOfModules.tensorMk_tmul _ _ _ _ _ _ X x a

/-- The left action of a homogeneous piece of the algebra, as a morphism out of the objectwise
tensor product. -/
noncomputable def LeftGradedModule.smulHom (N : LeftGradedModule.{t, m, m} A) (i n : ℤ) :
    PresheafOfModules.tensorObj (A.piece i).val (N.piece n).val ⟶ (N.piece (i + n)).val :=
  PresheafOfModules.tensorMk (fun X a y ↦ N.smul i n X a y)
    (fun X a a' y ↦ by rw [map_add]; rfl)
    (fun X r a y ↦ N.smul_smul_left i n X r a y)
    (fun X a y y' ↦ map_add (N.smul i n X a) y y')
    (fun X r a y ↦ N.smul_smul_right i n X r a y)
    (fun _ _ f a y ↦ N.smul_naturality i n f a y)

/-- `SheafOfModules.LeftGradedModule.smulHom` sends a pure tensor `a ⊗ y` to the left action
`N.smul i n X a y`. -/
@[simp]
theorem LeftGradedModule.smulHom_tmul (N : LeftGradedModule.{t, m, m} A) (i n : ℤ) (X : Cᵒᵖ)
    (a : (A.piece i).val.obj X) (y : (N.piece n).val.obj X) :
    PresheafOfModules.Hom.app (N.smulHom i n) X (a ⊗ₜ y) = N.smul i n X a y :=
  PresheafOfModules.tensorMk_tmul _ _ _ _ _ _ X a y

namespace RelativeTensor

variable (P : GradedModule.{t, m, m} A) (N : LeftGradedModule.{t, m, m} A)

/-- The summand `P^p ⊗_O N^q` of the direct sum computing degree `n` of `P ⊗_A N`. -/
noncomputable abbrev tensorSummand {n : ℤ} (p : TensorIndex n) :
    PresheafOfModules.{m} (Osharp.obj ⋙ forget₂ CommRingCat RingCat) :=
  PresheafOfModules.tensorObj (P.piece p.1.1).val (N.piece p.1.2).val

/-- The summand `P^r ⊗_O A^s ⊗_O N^t` of the direct sum of relations in degree `n`. -/
noncomputable abbrev relationSummand {n : ℤ} (i : RelationIndex n) :
    PresheafOfModules.{m} (Osharp.obj ⋙ forget₂ CommRingCat RingCat) :=
  PresheafOfModules.tensorObj (P.piece i.1.1).val
    (PresheafOfModules.tensorObj (A.piece i.1.2.1).val (N.piece i.1.2.2).val)

/-- The direct sum `⨁_{p + q = n} P^p ⊗_O N^q`. -/
noncomputable abbrev tensorSum (n : ℤ) :
    PresheafOfModules.{m} (Osharp.obj ⋙ forget₂ CommRingCat RingCat) :=
  ∐ fun p : TensorIndex n => tensorSummand P N p

/-- The direct sum `⨁_{r + s + t = n} P^r ⊗_O A^s ⊗_O N^t`. -/
noncomputable abbrev relationSum (n : ℤ) :
    PresheafOfModules.{m} (Osharp.obj ⋙ forget₂ CommRingCat RingCat) :=
  ∐ fun i : RelationIndex n => relationSummand P N i

/-- The inclusion of the summand `P^p ⊗_O N^q` into the direct sum of degree `n`. -/
noncomputable abbrev tensorSumι {n : ℤ} (p : TensorIndex n) :
    tensorSummand P N p ⟶ tensorSum P N n :=
  Sigma.ι (fun p : TensorIndex n => tensorSummand P N p) p

/-- The inclusion of the summand `P^r ⊗_O A^s ⊗_O N^t` into the direct sum of relations of
degree `n`. -/
noncomputable abbrev relationSumι {n : ℤ} (i : RelationIndex n) :
    relationSummand P N i ⟶ relationSum P N n :=
  Sigma.ι (fun i : RelationIndex n => relationSummand P N i) i

/-- The index `(r + s, t)` of the summand containing `xa ⊗ y`. -/
abbrev leftIndex {n : ℤ} (i : RelationIndex n) : TensorIndex n :=
  ⟨(i.1.1 + i.1.2.1, i.1.2.2), i.2⟩

/-- The index `(r, s + t)` of the summand containing `x ⊗ ay`. -/
abbrev rightIndex {n : ℤ} (i : RelationIndex n) : TensorIndex n :=
  ⟨(i.1.1, i.1.2.1 + i.1.2.2), (add_assoc i.1.1 i.1.2.1 i.1.2.2).symm.trans i.2⟩

/-- The local section `xa ⊗ y` of the direct sum of degree `n`, for a relation index. -/
noncomputable abbrev leftTerm {n : ℤ} (i : RelationIndex n) (X : Cᵒᵖ)
    (x : (P.piece i.1.1).val.obj X) (a : (A.piece i.1.2.1).val.obj X)
    (y : (N.piece i.1.2.2).val.obj X) : (tensorSum P N n).obj X :=
  PresheafOfModules.Hom.app (tensorSumι P N (leftIndex i)) X
    (P.smul i.1.1 i.1.2.1 X x a ⊗ₜ y)

/-- The local section `x ⊗ ay` of the direct sum of degree `n`, for a relation index. -/
noncomputable abbrev rightTerm {n : ℤ} (i : RelationIndex n) (X : Cᵒᵖ)
    (x : (P.piece i.1.1).val.obj X) (a : (A.piece i.1.2.1).val.obj X)
    (y : (N.piece i.1.2.2).val.obj X) : (tensorSum P N n).obj X :=
  PresheafOfModules.Hom.app (tensorSumι P N (rightIndex i)) X
    (x ⊗ₜ N.smul i.1.2.1 i.1.2.2 X a y)

/-- The balance map on the summand of index `(r, s, t)`: it sends a local section `x ⊗ a ⊗ y`
to `xa ⊗ y - x ⊗ ay`. -/
noncomputable def balanceSummandMap {n : ℤ} (i : RelationIndex n) :
    relationSummand P N i ⟶ tensorSum P N n :=
  PresheafOfModules.tensorMk₃ (fun X x a y ↦ leftTerm P N i X x a y - rightTerm P N i X x a y)
    (fun X x x' a y ↦ by
      simp only [leftTerm, rightTerm, map_add, AddMonoidHom.add_apply,
        PresheafOfModules.app_tmul_add_left]
      abel)
    (fun X r x a y ↦ by
      simp only [leftTerm, rightTerm, P.smul_smul_left, PresheafOfModules.app_tmul_smul_left,
        smul_sub])
    (fun X x a a' y ↦ by
      simp only [leftTerm, rightTerm, map_add, PresheafOfModules.app_tmul_add_left,
        PresheafOfModules.app_tmul_add_right, AddMonoidHom.add_apply]
      abel)
    (fun X r x a y ↦ by
      simp only [leftTerm, rightTerm, P.smul_smul_right, N.smul_smul_left,
        PresheafOfModules.app_tmul_smul_left, PresheafOfModules.app_tmul_smul_right, smul_sub])
    (fun X x a y y' ↦ by
      simp only [leftTerm, rightTerm, map_add, PresheafOfModules.app_tmul_add_right]
      abel)
    (fun X r x a y ↦ by
      simp only [leftTerm, rightTerm, N.smul_smul_right, PresheafOfModules.app_tmul_smul_right,
        smul_sub])
    (fun X Y f x a y ↦ by
      simp only [leftTerm, rightTerm, map_sub, PresheafOfModules.app_tmul_restrictₛₗ]
      rw [GradedModule.smul_restrictₛₗ, LeftGradedModule.smul_restrictₛₗ])

/-- The balance map on the summand of index `i` sends `x ⊗ a ⊗ y` to `xa ⊗ y - x ⊗ ay`. -/
@[simp]
theorem balanceSummandMap_tmul {n : ℤ} (i : RelationIndex n) (X : Cᵒᵖ)
    (x : (P.piece i.1.1).val.obj X) (a : (A.piece i.1.2.1).val.obj X)
    (y : (N.piece i.1.2.2).val.obj X) :
    PresheafOfModules.Hom.app (balanceSummandMap P N i) X (x ⊗ₜ (a ⊗ₜ y)) =
      leftTerm P N i X x a y - rightTerm P N i X x a y :=
  PresheafOfModules.tensorMk₃_tmul _ _ _ _ _ _ _ _ X x a y

/-- A morphism out of the direct sum of degree `n` sends the balance map on a pure tensor
`x ⊗ a ⊗ y` to the difference of its values on `xa ⊗ y` and `x ⊗ ay`. -/
private theorem balanceSummandMap_comp_app_tmul {n : ℤ}
    {K : PresheafOfModules.{m} (Osharp.obj ⋙ forget₂ CommRingCat RingCat)}
    (i : RelationIndex n) (g : tensorSum P N n ⟶ K) (X : Cᵒᵖ)
    (x : (P.piece i.1.1).val.obj X) (a : (A.piece i.1.2.1).val.obj X)
    (y : (N.piece i.1.2.2).val.obj X) :
    PresheafOfModules.Hom.app (balanceSummandMap P N i ≫ g) X (x ⊗ₜ (a ⊗ₜ y)) =
      PresheafOfModules.Hom.app g X (leftTerm P N i X x a y) -
        PresheafOfModules.Hom.app g X (rightTerm P N i X x a y) := by
  refine (PresheafOfModules.comp_app_apply _ _ X _).trans
    ((congrArg (PresheafOfModules.Hom.app g X) (balanceSummandMap_tmul P N i X x a y)).trans ?_)
  exact map_sub (ConcreteCategory.hom (PresheafOfModules.Hom.app g X)) _ _

/-- The balance map `⨁_{r+s+t=n} P^r ⊗_O A^s ⊗_O N^t ⟶ ⨁_{p+q=n} P^p ⊗_O N^q` of degree `n`,
sending `x ⊗ a ⊗ y` to `xa ⊗ y - x ⊗ ay`. -/
@[stacks 0FR2 "the map of the presentation, sending `x ⊗ a ⊗ y` to `xa ⊗ y - x ⊗ ay`"]
noncomputable def balanceMap (n : ℤ) : relationSum P N n ⟶ tensorSum P N n :=
  Sigma.desc fun i ↦ balanceSummandMap P N i

/-- The balance map restricted to the summand of index `i` is
`SheafOfModules.RelativeTensor.balanceSummandMap`. -/
@[simp]
theorem relationSumι_balanceMap {n : ℤ} (i : RelationIndex n) :
    relationSumι P N i ≫ balanceMap P N n = balanceSummandMap P N i :=
  Sigma.ι_desc _ _

/-- Degree `n` of the relative tensor product `P ⊗_A N` as a presheaf of modules: the cokernel
of the balance map. -/
noncomputable abbrev gradedTensorPre (n : ℤ) :
    PresheafOfModules.{m} (Osharp.obj ⋙ forget₂ CommRingCat RingCat) :=
  cokernel (balanceMap P N n)

/-- The canonical surjection onto degree `n` of `P ⊗_A N`. -/
noncomputable abbrev gradedTensorπ (n : ℤ) : tensorSum P N n ⟶ gradedTensorPre P N n :=
  cokernel.π (balanceMap P N n)

section Sheafify

variable [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasWeakSheafify J AddCommGrpCat.{m}]

/-- Degree `n` of the relative tensor product `P ⊗_A N` of a right graded `A`-module with a left
graded `A`-module: the associated sheaf of the cokernel of the balance map. -/
@[stacks 0FR2 "degree `n` of the graded tensor product, as the cokernel of the balance map"]
noncomputable def gradedTensor (n : ℤ) : SheafOfModules.{m} (toRingCat J Osharp) :=
  (PresheafOfModules.sheafification (R := toRingCat J Osharp)
    (𝟙 (toRingCat J Osharp).obj)).obj (gradedTensorPre P N n)

end Sheafify

end RelativeTensor

namespace RelativeTensor

variable (P : GradedModule.{t, m, m} A) {N N' : LeftGradedModule.{t, m, m} A} (f : N ⟶ N')

/-- The map of direct sums `⨁ P^p ⊗_O N^q ⟶ ⨁ P^p ⊗_O N'^q` induced by a homomorphism of left
graded modules. -/
noncomputable def tensorSumMap (n : ℤ) : tensorSum P N n ⟶ tensorSum P N' n :=
  Limits.Sigma.map fun p : TensorIndex n ↦
    PresheafOfModules.tensorHom (𝟙 (P.piece p.1.1).val) (f.app p.1.2).val

/-- The map of direct sums of relations induced by a homomorphism of left graded modules. -/
noncomputable def relationSumMap (n : ℤ) : relationSum P N n ⟶ relationSum P N' n :=
  Limits.Sigma.map fun i : RelationIndex n ↦
    PresheafOfModules.tensorHom (𝟙 (P.piece i.1.1).val)
      (PresheafOfModules.tensorHom (𝟙 (A.piece i.1.2.1).val) (f.app i.1.2.2).val)

/-- `SheafOfModules.RelativeTensor.tensorSumMap` on the summand `P^p ⊗_O N^q` is
`𝟙 ⊗ f` followed by the inclusion of the summand `P^p ⊗_O N'^q`. -/
theorem tensorSumι_tensorSumMap {n : ℤ} (p : TensorIndex n) :
    tensorSumι P N p ≫ tensorSumMap P f n =
      PresheafOfModules.tensorHom (𝟙 (P.piece p.1.1).val) (f.app p.1.2).val ≫
        tensorSumι P N' p :=
  Limits.Sigma.ι_map _ p

/-- `SheafOfModules.RelativeTensor.relationSumMap` on the summand `P^r ⊗_O A^s ⊗_O N^t` is
`𝟙 ⊗ 𝟙 ⊗ f` followed by the inclusion of the summand `P^r ⊗_O A^s ⊗_O N'^t`. -/
theorem relationSumι_relationSumMap {n : ℤ} (i : RelationIndex n) :
    relationSumι P N i ≫ relationSumMap P f n =
      PresheafOfModules.tensorHom (𝟙 (P.piece i.1.1).val)
          (PresheafOfModules.tensorHom (𝟙 (A.piece i.1.2.1).val) (f.app i.1.2.2).val) ≫
        relationSumι P N' i :=
  Limits.Sigma.ι_map _ i

/-- `𝟙 ⊗ 𝟙 ⊗ f` sends a pure tensor `x ⊗ (a ⊗ y)` to `x ⊗ (a ⊗ f y)`. -/
theorem relationTensorHom_tmul {n : ℤ} (i : RelationIndex n) (X : Cᵒᵖ)
    (x : (P.piece i.1.1).val.obj X) (a : (A.piece i.1.2.1).val.obj X)
    (y : (N.piece i.1.2.2).val.obj X) :
    PresheafOfModules.Hom.app (PresheafOfModules.tensorHom (𝟙 (P.piece i.1.1).val)
          (PresheafOfModules.tensorHom (𝟙 (A.piece i.1.2.1).val) (f.app i.1.2.2).val)) X
        (x ⊗ₜ (a ⊗ₜ y)) =
      x ⊗ₜ (a ⊗ₜ PresheafOfModules.Hom.app (f.app i.1.2.2).val X y) := by
  refine (PresheafOfModules.tensorHom_tmul (𝟙 (P.piece i.1.1).val)
    (PresheafOfModules.tensorHom (𝟙 (A.piece i.1.2.1).val) (f.app i.1.2.2).val) X x
      (a ⊗ₜ y)).trans ?_
  exact congrArg (fun w' ↦ x ⊗ₜ w')
    (PresheafOfModules.tensorHom_tmul (𝟙 (A.piece i.1.2.1).val) (f.app i.1.2.2).val X a y)

/-- `SheafOfModules.RelativeTensor.tensorSumMap` sends the local section `u ⊗ w` of the summand
`P^p ⊗_O N^q` to the local section `u ⊗ f w` of the summand `P^p ⊗_O N'^q`. -/
theorem tensorSumMap_tensorSumι_apply {n : ℤ} (p : TensorIndex n) (X : Cᵒᵖ)
    (u : (P.piece p.1.1).val.obj X) (w : (N.piece p.1.2).val.obj X) :
    PresheafOfModules.Hom.app (tensorSumMap P f n) X
        (PresheafOfModules.Hom.app (tensorSumι P N p) X (u ⊗ₜ w)) =
      PresheafOfModules.Hom.app (tensorSumι P N' p) X
        (u ⊗ₜ PresheafOfModules.Hom.app (f.app p.1.2).val X w) := by
  refine (PresheafOfModules.hom_congr_apply' (tensorSumι_tensorSumMap P f p) X (u ⊗ₜ w)).trans ?_
  exact congrArg (fun w' ↦ PresheafOfModules.Hom.app (tensorSumι P N' p) X w')
    (PresheafOfModules.tensorHom_tmul (𝟙 (P.piece p.1.1).val) (f.app p.1.2).val X u w)

/-- The balance map is compatible with a homomorphism of left graded modules. -/
theorem balanceMap_naturality (n : ℤ) :
    balanceMap P N n ≫ tensorSumMap P f n = relationSumMap P f n ≫ balanceMap P N' n := by
  refine Sigma.hom_ext _ _ fun i ↦ ?_
  rw [← Category.assoc, relationSumι_balanceMap, ← Category.assoc, relationSumι_relationSumMap,
    Category.assoc, relationSumι_balanceMap]
  refine PresheafOfModules.tensorObj₃_hom_ext fun X x a y ↦ ?_
  rw [balanceSummandMap_comp_app_tmul]
  refine Eq.trans ?_ ((PresheafOfModules.comp_app_apply _ _ X _).trans
    ((congrArg (PresheafOfModules.Hom.app (balanceSummandMap P N' i) X)
      (relationTensorHom_tmul P f i X x a y)).trans (balanceSummandMap_tmul ..))).symm
  refine congrArg₂ (· - ·)
    (tensorSumMap_tensorSumι_apply P f (leftIndex i) X (P.smul i.1.1 i.1.2.1 X x a) y) ?_
  exact (tensorSumMap_tensorSumι_apply P f (rightIndex i) X x (N.smul i.1.2.1 i.1.2.2 X a y)).trans
    (congrArg (fun w ↦ PresheafOfModules.Hom.app (tensorSumι P N' (rightIndex i)) X (x ⊗ₜ w))
      (f.map_smul i.1.2.1 i.1.2.2 X a y))

/-- Degree `n` of the map `P ⊗_A N ⟶ P ⊗_A N'` induced by a homomorphism of left graded
modules, as a morphism of presheaves of modules. -/
noncomputable def gradedTensorMapPre (n : ℤ) : gradedTensorPre P N n ⟶ gradedTensorPre P N' n :=
  cokernel.desc (balanceMap P N n) (tensorSumMap P f n ≫ gradedTensorπ P N' n) (by
    rw [← Category.assoc, balanceMap_naturality, Category.assoc, cokernel.condition,
      comp_zero])

section Sheafify

variable [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasWeakSheafify J AddCommGrpCat.{m}]

/-- Degree `n` of the map `P ⊗_A N ⟶ P ⊗_A N'` induced by a homomorphism of left graded
modules. -/
noncomputable def gradedTensorMap (n : ℤ) : gradedTensor P N n ⟶ gradedTensor P N' n :=
  (PresheafOfModules.sheafification (R := toRingCat J Osharp)
    (𝟙 (toRingCat J Osharp).obj)).map (gradedTensorMapPre P f n)

end Sheafify

end RelativeTensor

namespace RelativeTensor

variable {P P' P'' : GradedModule.{t, m, m} A} (h : P ⟶ P')
  (N : LeftGradedModule.{t, m, m} A)

/-- The map of direct sums `⨁ P^p ⊗_O N^q ⟶ ⨁ P'^p ⊗_O N^q` induced by a homomorphism of right
graded modules. -/
noncomputable def tensorSumMapRight (n : ℤ) : tensorSum P N n ⟶ tensorSum P' N n :=
  Limits.Sigma.map fun p : TensorIndex n ↦
    PresheafOfModules.tensorHom (h.app p.1.1).val (𝟙 (N.piece p.1.2).val)

/-- The map of direct sums of relations induced by a homomorphism of right graded modules. -/
noncomputable def relationSumMapRight (n : ℤ) : relationSum P N n ⟶ relationSum P' N n :=
  Limits.Sigma.map fun i : RelationIndex n ↦
    PresheafOfModules.tensorHom (h.app i.1.1).val
      (𝟙 (PresheafOfModules.tensorObj (A.piece i.1.2.1).val (N.piece i.1.2.2).val))

/-- `SheafOfModules.RelativeTensor.tensorSumMapRight` on the summand `P^p ⊗_O N^q` is
`h ⊗ 𝟙` followed by the inclusion of the summand `P'^p ⊗_O N^q`. -/
theorem tensorSumι_tensorSumMapRight {n : ℤ} (p : TensorIndex n) :
    tensorSumι P N p ≫ tensorSumMapRight h N n =
      PresheafOfModules.tensorHom (h.app p.1.1).val (𝟙 (N.piece p.1.2).val) ≫
        tensorSumι P' N p :=
  Limits.Sigma.ι_map _ p

/-- `SheafOfModules.RelativeTensor.relationSumMapRight` on the summand `P^r ⊗_O A^s ⊗_O N^t` is
`h ⊗ 𝟙` followed by the inclusion of the summand `P'^r ⊗_O A^s ⊗_O N^t`. -/
theorem relationSumι_relationSumMapRight {n : ℤ} (i : RelationIndex n) :
    relationSumι P N i ≫ relationSumMapRight h N n =
      PresheafOfModules.tensorHom (h.app i.1.1).val
          (𝟙 (PresheafOfModules.tensorObj (A.piece i.1.2.1).val (N.piece i.1.2.2).val)) ≫
        relationSumι P' N i :=
  Limits.Sigma.ι_map _ i

/-- `h ⊗ 𝟙` sends a pure tensor `x ⊗ (a ⊗ y)` to `h x ⊗ (a ⊗ y)`. -/
theorem relationTensorHomRight_tmul {n : ℤ} (i : RelationIndex n) (X : Cᵒᵖ)
    (x : (P.piece i.1.1).val.obj X) (a : (A.piece i.1.2.1).val.obj X)
    (y : (N.piece i.1.2.2).val.obj X) :
    PresheafOfModules.Hom.app (PresheafOfModules.tensorHom (h.app i.1.1).val
          (𝟙 (PresheafOfModules.tensorObj (A.piece i.1.2.1).val (N.piece i.1.2.2).val))) X
        (x ⊗ₜ (a ⊗ₜ y)) =
      PresheafOfModules.Hom.app (h.app i.1.1).val X x ⊗ₜ (a ⊗ₜ y) :=
  PresheafOfModules.tensorHom_tmul (h.app i.1.1).val
    (𝟙 (PresheafOfModules.tensorObj (A.piece i.1.2.1).val (N.piece i.1.2.2).val)) X x (a ⊗ₜ y)

/-- `SheafOfModules.RelativeTensor.tensorSumMapRight` sends the local section `u ⊗ w` of the
summand `P^p ⊗_O N^q` to the local section `h u ⊗ w` of the summand `P'^p ⊗_O N^q`. -/
theorem tensorSumMapRight_tensorSumι_apply {n : ℤ} (p : TensorIndex n) (X : Cᵒᵖ)
    (u : (P.piece p.1.1).val.obj X) (w : (N.piece p.1.2).val.obj X) :
    PresheafOfModules.Hom.app (tensorSumMapRight h N n) X
        (PresheafOfModules.Hom.app (tensorSumι P N p) X (u ⊗ₜ w)) =
      PresheafOfModules.Hom.app (tensorSumι P' N p) X
        (PresheafOfModules.Hom.app (h.app p.1.1).val X u ⊗ₜ w) := by
  refine (PresheafOfModules.hom_congr_apply' (tensorSumι_tensorSumMapRight h N p) X
    (u ⊗ₜ w)).trans ?_
  exact congrArg (fun w' ↦ PresheafOfModules.Hom.app (tensorSumι P' N p) X w')
    (PresheafOfModules.tensorHom_tmul (h.app p.1.1).val (𝟙 (N.piece p.1.2).val) X u w)

/-- The balance map is compatible with a homomorphism of right graded modules. -/
theorem balanceMap_naturality_right (n : ℤ) :
    balanceMap P N n ≫ tensorSumMapRight h N n =
      relationSumMapRight h N n ≫ balanceMap P' N n := by
  refine Sigma.hom_ext _ _ fun i ↦ ?_
  rw [← Category.assoc, relationSumι_balanceMap, ← Category.assoc,
    relationSumι_relationSumMapRight, Category.assoc, relationSumι_balanceMap]
  refine PresheafOfModules.tensorObj₃_hom_ext fun X x a y ↦ ?_
  rw [balanceSummandMap_comp_app_tmul]
  refine Eq.trans ?_ ((PresheafOfModules.comp_app_apply _ _ X _).trans
    ((congrArg (PresheafOfModules.Hom.app (balanceSummandMap P' N i) X)
      (relationTensorHomRight_tmul h N i X x a y)).trans (balanceSummandMap_tmul ..))).symm
  refine congrArg₂ (· - ·) ?_ (tensorSumMapRight_tensorSumι_apply h N (rightIndex i) X x
    (N.smul i.1.2.1 i.1.2.2 X a y))
  exact (tensorSumMapRight_tensorSumι_apply h N (leftIndex i) X (P.smul i.1.1 i.1.2.1 X x a)
    y).trans (congrArg
      (fun v ↦ PresheafOfModules.Hom.app (tensorSumι P' N (leftIndex i)) X (v ⊗ₜ y))
      (h.map_smul i.1.1 i.1.2.1 X x a))

/-- Degree `n` of the map `P ⊗_A N ⟶ P' ⊗_A N` induced by a homomorphism of right graded
modules, as a morphism of presheaves of modules. -/
noncomputable def gradedTensorMapPreRight (n : ℤ) :
    gradedTensorPre P N n ⟶ gradedTensorPre P' N n :=
  cokernel.desc (balanceMap P N n) (tensorSumMapRight h N n ≫ gradedTensorπ P' N n) (by
    rw [← Category.assoc, balanceMap_naturality_right, Category.assoc, cokernel.condition,
      comp_zero])

/-- `SheafOfModules.RelativeTensor.gradedTensorMapPreRight` is induced on cokernels by
`SheafOfModules.RelativeTensor.tensorSumMapRight`. -/
@[simp]
theorem gradedTensorπ_gradedTensorMapPreRight (n : ℤ) :
    gradedTensorπ P N n ≫ gradedTensorMapPreRight h N n =
      tensorSumMapRight h N n ≫ gradedTensorπ P' N n :=
  cokernel.π_desc _ _ _

/-- `SheafOfModules.RelativeTensor.tensorSumMapRight` preserves identities. -/
theorem tensorSumMapRight_id (n : ℤ) :
    tensorSumMapRight (𝟙 P) N n = 𝟙 (tensorSum P N n) := by
  refine Sigma.hom_ext _ _ fun p ↦ ?_
  rw [Category.comp_id]
  refine PresheafOfModules.tensorObj_hom_ext fun X u w ↦ ?_
  refine (PresheafOfModules.comp_app_apply (tensorSumι P N p)
    (tensorSumMapRight (𝟙 P) N n) X (u ⊗ₜ w)).trans ?_
  exact tensorSumMapRight_tensorSumι_apply (𝟙 P) N p X u w

/-- `SheafOfModules.RelativeTensor.tensorSumMapRight` preserves composition. -/
theorem tensorSumMapRight_comp (h : P ⟶ P') (h' : P' ⟶ P'') (n : ℤ) :
    tensorSumMapRight (h ≫ h') N n =
      tensorSumMapRight h N n ≫ tensorSumMapRight h' N n := by
  refine Sigma.hom_ext _ _ fun p ↦ ?_
  refine PresheafOfModules.tensorObj_hom_ext fun X u w ↦ ?_
  refine ((PresheafOfModules.comp_app_apply (tensorSumι P N p)
    (tensorSumMapRight (h ≫ h') N n) X (u ⊗ₜ w)).trans
      (tensorSumMapRight_tensorSumι_apply (h ≫ h') N p X u w)).trans ?_
  refine Eq.trans ?_ ((PresheafOfModules.comp_app_apply (tensorSumι P N p)
    (tensorSumMapRight h N n ≫ tensorSumMapRight h' N n) X (u ⊗ₜ w)).trans
      ((PresheafOfModules.comp_app_apply (tensorSumMapRight h N n)
        (tensorSumMapRight h' N n) X _).trans
          ((congrArg (fun v ↦ PresheafOfModules.Hom.app (tensorSumMapRight h' N n) X v)
            (tensorSumMapRight_tensorSumι_apply h N p X u w)).trans
              (tensorSumMapRight_tensorSumι_apply h' N p X _ w)))).symm
  rfl

/-- `SheafOfModules.RelativeTensor.gradedTensorMapPreRight` preserves identities. -/
theorem gradedTensorMapPreRight_id (n : ℤ) :
    gradedTensorMapPreRight (𝟙 P) N n = 𝟙 (gradedTensorPre P N n) := by
  refine (cancel_epi (gradedTensorπ P N n)).mp ?_
  rw [gradedTensorπ_gradedTensorMapPreRight, tensorSumMapRight_id, Category.id_comp,
    Category.comp_id]

/-- `SheafOfModules.RelativeTensor.gradedTensorMapPreRight` preserves composition. -/
theorem gradedTensorMapPreRight_comp (h : P ⟶ P') (h' : P' ⟶ P'') (n : ℤ) :
    gradedTensorMapPreRight (h ≫ h') N n =
      gradedTensorMapPreRight h N n ≫ gradedTensorMapPreRight h' N n := by
  refine (cancel_epi (gradedTensorπ P N n)).mp ?_
  rw [← Category.assoc, gradedTensorπ_gradedTensorMapPreRight,
    gradedTensorπ_gradedTensorMapPreRight, Category.assoc,
    gradedTensorπ_gradedTensorMapPreRight, tensorSumMapRight_comp, Category.assoc]

section Sheafify

variable [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasWeakSheafify J AddCommGrpCat.{m}]

/-- Degree `n` of the map `P ⊗_A N ⟶ P' ⊗_A N` induced by a homomorphism of right graded
modules. -/
noncomputable def gradedTensorMapRight (n : ℤ) : gradedTensor P N n ⟶ gradedTensor P' N n :=
  (PresheafOfModules.sheafification (R := toRingCat J Osharp)
    (𝟙 (toRingCat J Osharp).obj)).map (gradedTensorMapPreRight h N n)

/-- `SheafOfModules.RelativeTensor.gradedTensorMapRight` preserves identities. -/
theorem gradedTensorMapRight_id (n : ℤ) :
    gradedTensorMapRight (𝟙 P) N n = 𝟙 (gradedTensor P N n) := by
  rw [gradedTensorMapRight, gradedTensorMapPreRight_id]
  exact (PresheafOfModules.sheafification (R := toRingCat J Osharp)
    (𝟙 (toRingCat J Osharp).obj)).map_id _

/-- `SheafOfModules.RelativeTensor.gradedTensorMapRight` preserves composition. -/
theorem gradedTensorMapRight_comp (h : P ⟶ P') (h' : P' ⟶ P'') (n : ℤ) :
    gradedTensorMapRight (h ≫ h') N n =
      gradedTensorMapRight h N n ≫ gradedTensorMapRight h' N n := by
  rw [gradedTensorMapRight, gradedTensorMapPreRight_comp]
  exact (PresheafOfModules.sheafification (R := toRingCat J Osharp)
    (𝟙 (toRingCat J Osharp).obj)).map_comp _ _

/-- The functor `- ⊗_A N` from right graded `A`-modules to graded `O`-modules, for a fixed left
graded `A`-module `N`. -/
@[stacks 0FR2 "the functor `- ⊗_A N` on right graded modules"]
noncomputable def gradedTensorFunctor :
    GradedModule.{t, m, m} A ⥤ GradedObject ℤ (SheafOfModules.{m} (toRingCat J Osharp)) where
  obj Q n := gradedTensor Q N n
  map k n := gradedTensorMapRight k N n
  map_id _ := funext fun n ↦ gradedTensorMapRight_id N n
  map_comp k k' := funext fun n ↦ gradedTensorMapRight_comp N k k' n

end Sheafify

end RelativeTensor

namespace RelativeTensor

variable [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasWeakSheafify J AddCommGrpCat.{m}]

/-- Condition (1) in the definition of a good differential graded module: the right graded
`A`-module `P` is flat, that is, the functor `N ↦ P ⊗_A N` is exact on the category of left
graded `A`-modules. -/
def IsGradedFlat (P : GradedModule.{t, m, m} A) : Prop :=
  ∀ (N₁ N₂ N₃ : LeftGradedModule.{t, m, m} A) (f : N₁ ⟶ N₂) (g : N₂ ⟶ N₃)
    (hfg : ∀ n : ℤ, f.app n ≫ g.app n = 0), LeftGradedModule.ShortExact f g hfg →
      ∀ n : ℤ, ∃ h : gradedTensorMap P f n ≫ gradedTensorMap P g n = 0,
        (ShortComplex.mk (gradedTensorMap P f n) (gradedTensorMap P g n) h).ShortExact

end RelativeTensor

/-! ### The universal property of the relative tensor product

Degree `n` of `P ⊗_A N` is the sheafification of the cokernel of the balance map, so a morphism
out of it is a family of bilinear maps `P^p × N^q → K` with `p + q = n` which identifies
`xa ⊗ y` with `x ⊗ ay`. That datum is `SheafOfModules.RelativeTensor.Balanced`, and
`SheafOfModules.RelativeTensor.Balanced.desc` together with
`SheafOfModules.RelativeTensor.gradedTensor_hom_ext` is the universal property. -/

namespace RelativeTensor

/-- An `A`-balanced bilinear family of total degree `n` out of a right graded `A`-module `P`
and a left graded `A`-module `N`, into a presheaf of modules `K`: bilinear maps
`P^p × N^q → K` for every `p + q = n` which give `xa ⊗ y` and `x ⊗ ay` the same value. -/
structure Balanced (P : GradedModule.{t, m, m} A) (N : LeftGradedModule.{t, m, m} A)
    (K : PresheafOfModules.{m} (Osharp.obj ⋙ forget₂ CommRingCat RingCat)) (n : ℤ) where
  /-- The bilinear map on the summand of index `(p, q)`. -/
  app (p : TensorIndex n) : Stacks.BilinearMap (P.piece p.1.1).val (N.piece p.1.2).val K
  /-- The family is `A`-balanced: `xa ⊗ y` and `x ⊗ ay` have the same value. -/
  balanced (i : RelationIndex n) (X : Cᵒᵖ) (x : (P.piece i.1.1).val.obj X)
      (a : (A.piece i.1.2.1).val.obj X) (y : (N.piece i.1.2.2).val.obj X) :
    (app (leftIndex i)).app X (P.smul i.1.1 i.1.2.1 X x a) y =
      (app (rightIndex i)).app X x (N.smul i.1.2.1 i.1.2.2 X a y)

namespace Balanced

variable {P : GradedModule.{t, m, m} A} {N : LeftGradedModule.{t, m, m} A}
  {K : PresheafOfModules.{m} (Osharp.obj ⋙ forget₂ CommRingCat RingCat)} {n : ℤ}

/-- The morphism out of `⨁_{p + q = n} P^p ⊗_O N^q` determined by a balanced bilinear
family. -/
noncomputable def tensorSumDesc (β : Balanced P N K n) : tensorSum P N n ⟶ K :=
  Sigma.desc fun p ↦ PresheafOfModules.ofBilinear (β.app p)

/-- The morphism `SheafOfModules.RelativeTensor.Balanced.tensorSumDesc` sends the local section
`x ⊗ y` of the summand `P^p ⊗_O N^q` to the value of the bilinear map of index `p` at
`(x, y)`. -/
theorem tensorSumDesc_tmul (β : Balanced P N K n) (p : TensorIndex n) (X : Cᵒᵖ)
    (x : (P.piece p.1.1).val.obj X) (y : (N.piece p.1.2).val.obj X) :
    PresheafOfModules.Hom.app β.tensorSumDesc X
        (PresheafOfModules.Hom.app (tensorSumι P N p) X (x ⊗ₜ y)) =
      (β.app p).app X x y :=
  (PresheafOfModules.comp_app_apply (tensorSumι P N p) β.tensorSumDesc X (x ⊗ₜ y)).symm.trans
    ((PresheafOfModules.hom_congr_apply'
      (Sigma.ι_desc (fun p ↦ PresheafOfModules.ofBilinear (β.app p)) p) X (x ⊗ₜ y)).trans
      (PresheafOfModules.ofBilinear_tmul (β.app p) X x y))

/-- A balanced bilinear family kills the relations of the presentation. -/
theorem balanceMap_comp_tensorSumDesc (β : Balanced P N K n) :
    balanceMap P N n ≫ β.tensorSumDesc = 0 := by
  refine Sigma.hom_ext _ _ fun i ↦ ?_
  rw [← Category.assoc, relationSumι_balanceMap, comp_zero]
  refine PresheafOfModules.tensorObj₃_hom_ext fun X x a y ↦ ?_
  refine (balanceSummandMap_comp_app_tmul P N i β.tensorSumDesc X x a y).trans ?_
  refine (congrArg₂ (· - ·) (β.tensorSumDesc_tmul (leftIndex i) X _ y)
    (β.tensorSumDesc_tmul (rightIndex i) X x _)).trans ?_
  exact (sub_eq_zero.mpr (β.balanced i X x a y)).trans rfl

/-- The morphism out of degree `n` of `P ⊗_A N` as a presheaf of modules determined by a
balanced bilinear family. -/
noncomputable def descPre (β : Balanced P N K n) : gradedTensorPre P N n ⟶ K :=
  cokernel.desc _ β.tensorSumDesc β.balanceMap_comp_tensorSumDesc

/-- `SheafOfModules.RelativeTensor.Balanced.descPre` is induced on the cokernel by
`SheafOfModules.RelativeTensor.Balanced.tensorSumDesc`. -/
theorem gradedTensorπ_descPre (β : Balanced P N K n) :
    gradedTensorπ P N n ≫ β.descPre = β.tensorSumDesc :=
  cokernel.π_desc _ _ _

/-- Postcomposition of a balanced bilinear family with a morphism out of its target. -/
noncomputable def postcomp
    {K' : PresheafOfModules.{m} (Osharp.obj ⋙ forget₂ CommRingCat RingCat)}
    (β : Balanced P N K n) (ψ : K ⟶ K') : Balanced P N K' n where
  app p := (β.app p).postcomp ψ
  balanced i X x a y :=
    congrArg (PresheafOfModules.Hom.app ψ X) (β.balanced i X x a y)

/-- The bilinear maps of `β.postcomp ψ` are those of `β` followed by `ψ`. -/
@[simp]
theorem postcomp_app
    {K' : PresheafOfModules.{m} (Osharp.obj ⋙ forget₂ CommRingCat RingCat)}
    (β : Balanced P N K n) (ψ : K ⟶ K') (p : TensorIndex n) (X : Cᵒᵖ)
    (x : (P.piece p.1.1).val.obj X) (y : (N.piece p.1.2).val.obj X) :
    ((β.postcomp ψ).app p).app X x y =
      PresheafOfModules.Hom.app ψ X ((β.app p).app X x y) := rfl

end Balanced

section Sheafify

variable [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasWeakSheafify J AddCommGrpCat.{m}]
  (P : GradedModule.{t, m, m} A) (N : LeftGradedModule.{t, m, m} A)

/-- The sheafification unit exhibiting degree `n` of `P ⊗_A N` as the associated sheaf of the
cokernel of the balance map. -/
noncomputable abbrev gradedTensorUnit (n : ℤ) :
    gradedTensorPre P N n ⟶ (gradedTensor P N n).val :=
  (PresheafOfModules.sheafificationAdjunction
    (𝟙 (toRingCat J Osharp).obj)).unit.app (gradedTensorPre P N n)

/-- The local section `x ⊗ y` of degree `n` of `P ⊗_A N`, for `x` of degree `p` and `y` of
degree `q` with `p + q = n`. -/
noncomputable def tmul (n : ℤ) (p : TensorIndex n) (X : Cᵒᵖ)
    (x : (P.piece p.1.1).val.obj X) (y : (N.piece p.1.2).val.obj X) :
    (gradedTensor P N n).val.obj X :=
  PresheafOfModules.Hom.app (gradedTensorUnit P N n) X
    (PresheafOfModules.Hom.app (gradedTensorπ P N n) X
      (PresheafOfModules.Hom.app (tensorSumι P N p) X (x ⊗ₜ y)))

/-- **The universal property of `P ⊗_A N`, descent.** A balanced bilinear family of total
degree `n` into a sheaf of modules `K` descends to a morphism `P ⊗_A N → K` in degree `n`. -/
noncomputable def Balanced.desc {K : SheafOfModules.{m} (toRingCat J Osharp)} {n : ℤ}
    (β : Balanced P N K.val n) : gradedTensor P N n ⟶ K :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 (toRingCat J Osharp).obj)).homEquiv
    (gradedTensorPre P N n) K).symm β.descPre

/-- **The universal property of `P ⊗_A N`, computation.** The descent
`SheafOfModules.RelativeTensor.Balanced.desc` of a balanced bilinear family sends the local
section `x ⊗ y` to the value of the family at `(x, y)`. -/
theorem Balanced.desc_tmul {K : SheafOfModules.{m} (toRingCat J Osharp)} {n : ℤ}
    (β : Balanced P N K.val n) (p : TensorIndex n) (X : Cᵒᵖ)
    (x : (P.piece p.1.1).val.obj X) (y : (N.piece p.1.2).val.obj X) :
    PresheafOfModules.Hom.app (β.desc P N).val X (tmul P N n p X x y) =
      (β.app p).app X x y := by
  refine (PresheafOfModules.hom_congr_apply
    (PresheafOfModules.sheafificationAdjunction_unit_comp_homEquiv_symm
      (𝟙 (toRingCat J Osharp).obj) (N := K) β.descPre) X
    (PresheafOfModules.Hom.app (gradedTensorπ P N n) X
      (PresheafOfModules.Hom.app (tensorSumι P N p) X (x ⊗ₜ y)))).trans ?_
  refine (PresheafOfModules.hom_congr_apply β.gradedTensorπ_descPre X
    (PresheafOfModules.Hom.app (tensorSumι P N p) X (x ⊗ₜ y))).trans ?_
  exact β.tensorSumDesc_tmul p X x y

/-- **The universal property of `P ⊗_A N`, uniqueness.** Two morphisms out of degree `n` of
`P ⊗_A N` which agree on all local sections `x ⊗ y` are equal. -/
theorem gradedTensor_hom_ext {K : SheafOfModules.{m} (toRingCat J Osharp)} {n : ℤ}
    {φ ψ : gradedTensor P N n ⟶ K}
    (h : ∀ (p : TensorIndex n) (X : Cᵒᵖ) (x : (P.piece p.1.1).val.obj X)
        (y : (N.piece p.1.2).val.obj X),
      PresheafOfModules.Hom.app φ.val X (tmul P N n p X x y) =
        PresheafOfModules.Hom.app ψ.val X (tmul P N n p X x y)) :
    φ = ψ := by
  refine PresheafOfModules.sheafification_hom_ext ((cancel_epi (gradedTensorπ P N n)).mp ?_)
  refine Sigma.hom_ext _ _ fun p ↦ ?_
  refine PresheafOfModules.tensorObj_hom_ext fun X x y ↦ ?_
  exact h p X x y

omit [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasWeakSheafify J AddCommGrpCat.{m}] in
/-- The balance map on each summand composes to zero with the projection onto degree `n` of
`P ⊗_A N`: the local sections `xa ⊗ y` and `x ⊗ ay` have the same image. -/
theorem balanceSummandMap_comp_gradedTensorπ {n : ℤ} (i : RelationIndex n) :
    balanceSummandMap P N i ≫ gradedTensorπ P N n = 0 := by
  rw [← relationSumι_balanceMap, Category.assoc, cokernel.condition, comp_zero]

/-- **The canonical balanced bilinear family into `P ⊗_A N`**, sending `(x, y)` to the local
section `x ⊗ y`. It is universal by `SheafOfModules.RelativeTensor.Balanced.desc_tmul` and
`SheafOfModules.RelativeTensor.gradedTensor_hom_ext`. -/
noncomputable def tmulBalanced (n : ℤ) : Balanced P N (gradedTensor P N n).val n where
  app p := PresheafOfModules.toBilinear
    (tensorSumι P N p ≫ gradedTensorπ P N n ≫ gradedTensorUnit P N n)
  balanced i X x a y := by
    have h : PresheafOfModules.Hom.app (balanceSummandMap P N i ≫
        gradedTensorπ P N n ≫ gradedTensorUnit P N n) X (x ⊗ₜ (a ⊗ₜ y)) = 0 := by
      rw [← Category.assoc, balanceSummandMap_comp_gradedTensorπ, zero_comp]
      rfl
    refine sub_eq_zero.mp (Eq.trans (Eq.trans (map_sub (ConcreteCategory.hom
        (PresheafOfModules.Hom.app
          (gradedTensorπ P N n ≫ gradedTensorUnit P N n) X)) _ _).symm
      (congrArg (PresheafOfModules.Hom.app (gradedTensorπ P N n ≫ gradedTensorUnit P N n) X)
        (balanceSummandMap_tmul P N i X x a y).symm)) h)

/-- The bilinear maps of `SheafOfModules.RelativeTensor.tmulBalanced` send `(x, y)` to the local
section `x ⊗ y`. -/
@[simp]
theorem tmulBalanced_app (n : ℤ) (p : TensorIndex n) (X : Cᵒᵖ)
    (x : (P.piece p.1.1).val.obj X) (y : (N.piece p.1.2).val.obj X) :
    ((tmulBalanced P N n).app p).app X x y = tmul P N n p X x y := rfl

end Sheafify

section Functoriality

variable [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasWeakSheafify J AddCommGrpCat.{m}]

/-- A morphism of degree `n` presheaf tensor products lying over a morphism `ψ` of the direct
sums acts on a local section `x ⊗ y` of the sheafification as `ψ` does on the summand. -/
private theorem sheafification_map_tmul {P P' : GradedModule.{t, m, m} A}
    {N N' : LeftGradedModule.{t, m, m} A} {n : ℤ}
    (φ : gradedTensorPre P N n ⟶ gradedTensorPre P' N' n) (ψ : tensorSum P N n ⟶ tensorSum P' N' n)
    (hψ : gradedTensorπ P N n ≫ φ = ψ ≫ gradedTensorπ P' N' n) (p : TensorIndex n) (X : Cᵒᵖ)
    (x : (P.piece p.1.1).val.obj X) (y : (N.piece p.1.2).val.obj X)
    (x' : (P'.piece p.1.1).val.obj X) (y' : (N'.piece p.1.2).val.obj X)
    (hxy : PresheafOfModules.Hom.app ψ X (PresheafOfModules.Hom.app (tensorSumι P N p) X (x ⊗ₜ y)) =
      PresheafOfModules.Hom.app (tensorSumι P' N' p) X (x' ⊗ₜ y')) :
    PresheafOfModules.Hom.app ((PresheafOfModules.sheafification (R := toRingCat J Osharp)
        (𝟙 (toRingCat J Osharp).obj)).map φ).val X (tmul P N n p X x y) =
      tmul P' N' n p X x' y' := by
  refine (PresheafOfModules.unit_naturality_apply (α := 𝟙 (toRingCat J Osharp).obj)
    (φ := φ) X _).trans ?_
  refine congrArg (PresheafOfModules.Hom.app (gradedTensorUnit P' N' n) X) ?_
  refine (PresheafOfModules.hom_congr_apply' hψ X _).trans ?_
  exact congrArg (PresheafOfModules.Hom.app (gradedTensorπ P' N' n) X) hxy

/-- `P ⊗_A -` on a local section `x ⊗ y`. -/
theorem gradedTensorMap_tmul (P : GradedModule.{t, m, m} A)
    {N N' : LeftGradedModule.{t, m, m} A} (f : N ⟶ N') (n : ℤ)
    (p : TensorIndex n) (X : Cᵒᵖ) (x : (P.piece p.1.1).val.obj X)
    (y : (N.piece p.1.2).val.obj X) :
    PresheafOfModules.Hom.app (gradedTensorMap P f n).val X (tmul P N n p X x y) =
      tmul P N' n p X x (PresheafOfModules.Hom.app (f.app p.1.2).val X y) :=
  sheafification_map_tmul (gradedTensorMapPre P f n) (tensorSumMap P f n)
    (cokernel.π_desc _ _ _) p X x y x _
    (tensorSumMap_tensorSumι_apply P f p X x y)

/-- `- ⊗_A N` on a local section `x ⊗ y`. -/
theorem gradedTensorMapRight_tmul {P P' : GradedModule.{t, m, m} A} (h : P ⟶ P')
    (N : LeftGradedModule.{t, m, m} A) (n : ℤ) (p : TensorIndex n) (X : Cᵒᵖ)
    (x : (P.piece p.1.1).val.obj X) (y : (N.piece p.1.2).val.obj X) :
    PresheafOfModules.Hom.app (gradedTensorMapRight h N n).val X (tmul P N n p X x y) =
      tmul P' N n p X (PresheafOfModules.Hom.app (h.app p.1.1).val X x) y :=
  sheafification_map_tmul (gradedTensorMapPreRight h N n) (tensorSumMapRight h N n)
    (gradedTensorπ_gradedTensorMapPreRight h N n) p X x y _ y
    (tensorSumMapRight_tensorSumι_apply h N p X x y)

end Functoriality

end RelativeTensor

end SheafOfModules
