module

public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Sites.Abelian
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleSignTwist
public import StacksFrontier.CategoryTheory.Sites.CharacterTwistEquivalence

/-!
# Tensoring with a fixed presheaf of abelian groups, as a functor

The objectwise tensor product over `ℤ` of presheaves of abelian groups,
`AddCommGrpCat.presheafTensor`, is functorial in each variable. This file fixes the right-hand
variable: the additivity of the functor `- ⊗_ℤ L` on presheaves of abelian groups, the two unit
isomorphisms, and — on a site — the sheafified version `F ↦ (F ⊗_ℤ L)^#`, together with the fact
that sheafification inverts the objectwise tensor product of two morphisms it inverts.

## Main definitions

* `AddCommGrpCat.presheafTensorRightMap` is `F ⊗_ℤ g` for a morphism `g : L ⟶ L'`, as a natural
  transformation of the functors `AddCommGrpCat.presheafTensorRight`.
* `AddCommGrpCat.sheafTensorRight` is the functor `F ↦ (F ⊗_ℤ L)^#` on abelian sheaves.

## Main results

* `AddCommGrpCat.presheafTensor_hom_ext`: two morphisms out of an objectwise tensor product agree
  as soon as they agree on the pure tensors.
* `AddCommGrpCat.W_presheafTensorMap`: the objectwise tensor product of two morphisms inverted by
  sheafification is inverted by sheafification. This is the two-variable form of
  `AddCommGrpCat.W_presheafTensorMap_id`.
* `AddCommGrpCat.presheafTensorConstLeftIso` and `AddCommGrpCat.presheafTensorConstRightIso`: the
  objectwise tensor product with the constant presheaf `ℤ` on either side changes nothing.

## Implementation notes

The monoidal structure on `AddCommGrpCat.{u + 1}` through which `AddCommGrpCat.presheafTensorMap`
is defined is the transported one of `AddCommGrpCat.monoidalCategory`; it is reinstalled here as a
collection of local instances, exactly as in
`StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleTensor`, because the one fact about it that is
needed — that the class of local isomorphisms is monoidal — is stated for it.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Enriched.FunctorCategory Opposite
open scoped TensorProduct CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed

attribute [local instance 2000] CategoryTheory.instHasWeakSheafifyOfHasSheafify

universe v u₁ u

namespace AddCommGrpCat

/-! ### Morphisms out of an objectwise tensor product -/

section Ext

variable {C : Type u₁} [Category.{v} C]

/-- The pure tensor `a ⊗ x` in the objectwise tensor product of two presheaves of abelian groups,
as a section of that presheaf over `V`. -/
def tensorGen {F G : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}} {V : Cᵒᵖ} (a : F.obj V) (x : G.obj V) :
    (presheafTensor F G).obj V :=
  a ⊗ₜ[ℤ] x

/-- The restriction of a pure tensor is the pure tensor of the restrictions. -/
@[simp]
lemma presheafTensor_map_tensorGen {F G : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}} {V V' : Cᵒᵖ}
    (f : V ⟶ V') (a : F.obj V) (x : G.obj V) :
    (presheafTensor F G).map f (tensorGen a x) = tensorGen (F.map f a) (G.map f x) := rfl

/-- The objectwise tensor product `f ⊗ g` sends `a ⊗ x` to `f a ⊗ g x`. -/
lemma presheafTensorMap_tensorGen {F₁ F₂ G₁ G₂ : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}} (f : F₁ ⟶ F₂)
    (g : G₁ ⟶ G₂) (V : Cᵒᵖ) (a : F₁.obj V) (x : G₁.obj V) :
    (presheafTensorMap f g).app V (tensorGen a x) = tensorGen (f.app V a) (g.app V x) :=
  presheafTensorMap_app_tmul f g V a x

/-- The objectwise tensor product `f ⊗ 𝟙` sends `a ⊗ x` to `f a ⊗ x`. -/
@[simp]
lemma presheafTensorMap_id_right_tensorGen {F₁ F₂ G : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}} (f : F₁ ⟶ F₂)
    (V : Cᵒᵖ) (a : F₁.obj V) (x : G.obj V) :
    (presheafTensorMap f (𝟙 G)).app V (tensorGen a x) = tensorGen (f.app V a) x := by
  rw [presheafTensorMap_tensorGen]
  rfl

/-- The objectwise tensor product `𝟙 ⊗ g` sends `a ⊗ x` to `a ⊗ g x`. -/
@[simp]
lemma presheafTensorMap_id_left_tensorGen {F G₁ G₂ : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}} (g : G₁ ⟶ G₂)
    (V : Cᵒᵖ) (a : F.obj V) (x : G₁.obj V) :
    (presheafTensorMap (𝟙 F) g).app V (tensorGen a x) = tensorGen a (g.app V x) := by
  rw [presheafTensorMap_tensorGen]
  rfl

/-- The pure tensor `0 ⊗ x` is zero. -/
lemma tensorGen_zero_left {F G : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}} {V : Cᵒᵖ} (x : G.obj V) :
    tensorGen (F := F) 0 x = 0 :=
  TensorProduct.zero_tmul _ _

/-- A pure tensor is additive in its left factor. -/
lemma tensorGen_add_left {F G : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}} {V : Cᵒᵖ} (a a' : F.obj V)
    (x : G.obj V) : tensorGen (G := G) (a + a') x = tensorGen a x + tensorGen a' x :=
  TensorProduct.add_tmul _ _ _

/-- A pure tensor commutes with subtraction in its left factor. -/
lemma tensorGen_sub_left {F G : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}} {V : Cᵒᵖ} (a a' : F.obj V)
    (x : G.obj V) : tensorGen (G := G) (a - a') x = tensorGen a x - tensorGen a' x :=
  TensorProduct.sub_tmul _ _ _

/-- `(n • a) ⊗ x = n • (a ⊗ x)` for an integer `n`. -/
lemma tensorGen_smul_left {F G : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}} {V : Cᵒᵖ} (n : ℤ) (a : F.obj V)
    (x : G.obj V) : tensorGen (G := G) (n • a) x = n • tensorGen a x :=
  TensorProduct.smul_tmul' _ _ _

/-- `a ⊗ (n • x) = n • (a ⊗ x)` for an integer `n`. -/
lemma tensorGen_smul_right {F G : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}} {V : Cᵒᵖ} (n : ℤ) (a : F.obj V)
    (x : G.obj V) : tensorGen (F := F) a (n • x) = n • tensorGen a x :=
  TensorProduct.tmul_smul _ _ _

/-- Scaling both factors of a pure tensor by the same integer scales the tensor by its square. -/
lemma tensorGen_smul_smul {F G : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}} {V : Cᵒᵖ} (n : ℤ) (a : F.obj V)
    (x : G.obj V) : tensorGen (n • a) (n • x) = (n * n) • tensorGen a x := by
  rw [tensorGen_smul_right, tensorGen_smul_left, smul_smul]

/-- **Induction on the sections of an objectwise tensor product of presheaves of abelian
groups.** A predicate holding for every pure tensor and stable under addition holds for every
section of the tensor product presheaf. -/
lemma presheafTensor_induction_on {F G : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}} {V : Cᵒᵖ}
    {motive : (presheafTensor F G).obj V → Prop} (z : (presheafTensor F G).obj V)
    (gen : ∀ (a : F.obj V) (x : G.obj V), motive (tensorGen a x))
    (add : ∀ z z' : (presheafTensor F G).obj V, motive z → motive z' → motive (z + z')) :
    motive z := by
  induction z using TensorProduct.inductionOn with
  | tmul a x => exact gen a x
  | add z z' hz hz' => exact add z z' hz hz'

/-- **Two morphisms out of an objectwise tensor product of presheaves of abelian groups agree as
soon as they agree on the pure tensors.** -/
lemma presheafTensor_hom_ext {F G H : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}}
    {a b : presheafTensor F G ⟶ H}
    (hab : ∀ (V : Cᵒᵖ) (x : F.obj V) (y : G.obj V),
      a.app V (tensorGen x y) = b.app V (tensorGen x y)) : a = b := by
  refine NatTrans.ext (funext fun V => AddCommGrpCat.hom_ext (AddMonoidHom.ext fun z => ?_))
  induction z using presheafTensor_induction_on with
  | gen x y => exact hab V x y
  | add z z' hz hz' =>
      exact (map_add _ z z').trans ((congrArg₂ (· + ·) hz hz').trans (map_add _ z z').symm)

/-- The objectwise tensor product of morphisms is additive in the left-hand morphism. -/
lemma presheafTensorMap_add_left {F₁ F₂ G₁ G₂ : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}}
    (f f' : F₁ ⟶ F₂) (g : G₁ ⟶ G₂) :
    presheafTensorMap (f + f') g = presheafTensorMap f g + presheafTensorMap f' g := by
  refine presheafTensor_hom_ext fun V x y => ?_
  rw [presheafTensorMap_tensorGen]
  change tensorGen (f.app V x + f'.app V x) (g.app V y) =
    (presheafTensorMap f g).app V (tensorGen x y) + (presheafTensorMap f' g).app V (tensorGen x y)
  rw [presheafTensorMap_tensorGen, presheafTensorMap_tensorGen]
  exact tensorGen_add_left _ _ _

/-- Tensoring on the left with a fixed section of the left-hand factor. -/
def tmulLeftHom {F L : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}} {V : Cᵒᵖ} (t : F.obj V) :
    L.obj V →+ (presheafTensor F L).obj V where
  toFun x := t ⊗ₜ[ℤ] x
  map_zero' := TensorProduct.tmul_zero _ _
  map_add' _ _ := TensorProduct.tmul_add _ _ _

/-- `AddCommGrpCat.tmulLeftHom t` sends `x` to `t ⊗ x`. -/
@[simp]
lemma tmulLeftHom_apply {F L : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}} {V : Cᵒᵖ} (t : F.obj V)
    (x : L.obj V) : tmulLeftHom (L := L) t x = tensorGen t x := rfl

end Ext

/-! ### The unit isomorphisms -/

section Unit

variable {C : Type u₁} [Category.{v} C]

/-- The constant presheaf with value a universe-lifted copy of the integers. -/
abbrev constInt (C : Type u₁) [Category.{v} C] : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ))

/-- Scalar multiplication of an abelian group by a universe-lifted integer, as a `ℤ`-bilinear
map with the integer on the left. -/
def intSmulLeft (A : Type (u + 1)) [AddCommGroup A] :
    ULift.{u + 1} ℤ →ₗ[ℤ] (A →ₗ[ℤ] A) :=
  (LinearMap.lsmul ℤ A).comp (ULift.moduleEquiv : ULift.{u + 1} ℤ ≃ₗ[ℤ] ℤ).toLinearMap

/-- `AddCommGrpCat.uliftIntSmul A a y` is `y • a`. -/
@[simp]
lemma uliftIntSmul_apply (A : Type (u + 1)) [AddCommGroup A] (a : A) (y : ULift.{u + 1} ℤ) :
    uliftIntSmul A a y = y.down • a := rfl

/-- `AddCommGrpCat.intSmulLeft A y a` is `y • a`. -/
@[simp]
lemma intSmulLeft_apply (A : Type (u + 1)) [AddCommGroup A] (y : ULift.{u + 1} ℤ) (a : A) :
    intSmulLeft A y a = y.down • a := rfl

/-- The objectwise tensor product over `ℤ` of a presheaf of abelian groups with the constant
presheaf `ℤ` on the right, at a single object. -/
def presheafTensorConstRightApp (F : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (V : Cᵒᵖ) :
    (presheafTensor F (constInt.{v, u₁, u} C)).obj V ≅ F.obj V where
  hom := AddCommGrpCat.ofHom (TensorProduct.lift (uliftIntSmul (F.obj V))).toAddMonoidHom
  inv := AddCommGrpCat.ofHom
    { toFun := fun x => x ⊗ₜ[ℤ] (ULift.up (1 : ℤ))
      map_zero' := TensorProduct.zero_tmul _ _
      map_add' := fun x y => TensorProduct.add_tmul _ _ _ }
  hom_inv_id := by
    ext z
    induction z using TensorProduct.inductionOn with
    | tmul x y =>
        have hy : y.down • (ULift.up (1 : ℤ) : ULift.{u + 1} ℤ) = y := by
          apply ULift.ext; simp
        change (y.down • x) ⊗ₜ[ℤ] (ULift.up (1 : ℤ)) = x ⊗ₜ[ℤ] y
        rw [TensorProduct.smul_tmul, hy]
    | add z z' hz hz' =>
        exact (map_add _ z z').trans ((congrArg₂ (· + ·) hz hz').trans (map_add _ z z').symm)
  inv_hom_id := by
    ext x
    change (1 : ℤ) • x = x
    rw [one_smul]

/-- The objectwise tensor product over `ℤ` of a presheaf of abelian groups with the constant
presheaf `ℤ` on the right is the presheaf itself. -/
def presheafTensorConstRightIso (F : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    presheafTensor F (constInt.{v, u₁, u} C) ≅ F :=
  NatIso.ofComponents (presheafTensorConstRightApp F) (by
    intro V V' f
    ext z
    induction z using TensorProduct.inductionOn with
    | tmul x y =>
        change y.down • F.map f x = F.map f (y.down • x)
        exact (map_zsmul (F.map f).hom _ _).symm
    | add z z' hz hz' =>
        exact (map_add _ z z').trans ((congrArg₂ (· + ·) hz hz').trans (map_add _ z z').symm))

/-- The objectwise tensor product over `ℤ` of the constant presheaf `ℤ` with a presheaf of
abelian groups, at a single object. -/
def presheafTensorConstLeftApp (F : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (V : Cᵒᵖ) :
    (presheafTensor (constInt.{v, u₁, u} C) F).obj V ≅ F.obj V where
  hom := AddCommGrpCat.ofHom (TensorProduct.lift (intSmulLeft (F.obj V))).toAddMonoidHom
  inv := AddCommGrpCat.ofHom
    { toFun := fun x => (ULift.up (1 : ℤ)) ⊗ₜ[ℤ] x
      map_zero' := TensorProduct.tmul_zero _ _
      map_add' := fun x y => TensorProduct.tmul_add _ _ _ }
  hom_inv_id := by
    ext z
    induction z using TensorProduct.inductionOn with
    | tmul y x =>
        have hy : y.down • (ULift.up (1 : ℤ) : ULift.{u + 1} ℤ) = y := by
          apply ULift.ext; simp
        change (ULift.up (1 : ℤ)) ⊗ₜ[ℤ] (y.down • x) = y ⊗ₜ[ℤ] x
        rw [← TensorProduct.smul_tmul, hy]
    | add z z' hz hz' =>
        exact (map_add _ z z').trans ((congrArg₂ (· + ·) hz hz').trans (map_add _ z z').symm)
  inv_hom_id := by
    ext x
    change (1 : ℤ) • x = x
    rw [one_smul]

/-- The objectwise tensor product over `ℤ` of the constant presheaf `ℤ` with a presheaf of
abelian groups is the presheaf itself. -/
def presheafTensorConstLeftIso (F : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    presheafTensor (constInt.{v, u₁, u} C) F ≅ F :=
  NatIso.ofComponents (presheafTensorConstLeftApp F) (by
    intro V V' f
    ext z
    induction z using TensorProduct.inductionOn with
    | tmul y x =>
        change y.down • F.map f x = F.map f (y.down • x)
        exact (map_zsmul (F.map f).hom _ _).symm
    | add z z' hz hz' =>
        exact (map_add _ z z').trans ((congrArg₂ (· + ·) hz hz').trans (map_add _ z z').symm))

end Unit

/-! ### Local isomorphisms and the objectwise tensor product -/

/-- The monoidal structure on `AddCommGrpCat.{u + 1}` transported along
`AddCommGrpCat.uliftIntEquivalence`. -/
local instance : MonoidalCategory AddCommGrpCat.{u + 1} := monoidalCategory.{u + 1}

/-- The inverse of `AddCommGrpCat.uliftIntEquivalence` is monoidal for the transported
structure. -/
local instance : (uliftIntEquivalence.{u + 1}).inverse.Monoidal := by
  change (Monoidal.equivalenceTransported (uliftIntEquivalence.{u + 1})).inverse.Monoidal
  infer_instance

/-- The functor of `AddCommGrpCat.uliftIntEquivalence` is monoidal for the transported
structure. -/
local instance : (uliftIntEquivalence.{u + 1}).functor.Monoidal := by
  change (Monoidal.equivalenceTransported (uliftIntEquivalence.{u + 1})).functor.Monoidal
  infer_instance

/-- The braiding on `AddCommGrpCat.{u + 1}` transported along
`AddCommGrpCat.uliftIntEquivalence`. -/
local instance : BraidedCategory AddCommGrpCat.{u + 1} := by
  change BraidedCategory (Monoidal.Transported (uliftIntEquivalence.{u + 1}))
  infer_instance

/-- The transported monoidal structure on `AddCommGrpCat.{u + 1}` is closed. -/
local instance : MonoidalClosed AddCommGrpCat.{u + 1} :=
  MonoidalClosed.ofEquiv (uliftIntEquivalence.{u + 1}).inverse
    (uliftIntEquivalence.{u + 1}).symm.toAdjunction

/-- **Sheafification inverts the objectwise tensor product of two morphisms it inverts.** This is
the two-variable form of `AddCommGrpCat.W_presheafTensorMap_id`. -/
theorem W_presheafTensorMap {C : Type u₁} [Category.{v} C] [UnivLE.{max u₁ v, u + 1}]
    (J : GrothendieckTopology C) {F₁ F₂ G₁ G₂ : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}}
    {f : F₁ ⟶ F₂} {g : G₁ ⟶ G₂} (hf : J.W f) (hg : J.W g) :
    J.W (presheafTensorMap f g) := by
  let : HasLimitsOfSize.{max u₁ v, max u₁ v} AddCommGrpCat.{u + 1} :=
    AddCommGrpCat.hasLimitsOfSize
  let : EnrichedOrdinaryCategory AddCommGrpCat.{u + 1} AddCommGrpCat.{u + 1} := inferInstance
  let : ∀ P₁ P₂ : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      HasFunctorEnrichedHom AddCommGrpCat.{u + 1} P₁ P₂ := by
    intro P₁ P₂ V
    infer_instance
  let : ∀ P₁ P₂ : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}, HasEnrichedHom AddCommGrpCat.{u + 1} P₁ P₂ := by
    intro P₁ P₂
    infer_instance
  apply MorphismProperty.RespectsIso.precomp
  apply MorphismProperty.RespectsIso.postcomp
  exact J.W.tensorHom_mem f g hf hg

/-! ### The sheafified tensor product with a fixed presheaf -/

section Sheaf

variable {C : Type u₁} [Category.{v} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J AddCommGrpCat.{u + 1}]

/-- The forgetful functor from abelian sheaves to abelian presheaves is additive. -/
instance sheafToPresheaf_additive [HasSheafify J AddCommGrpCat.{u + 1}] :
    (sheafToPresheaf J AddCommGrpCat.{u + 1}).Additive :=
  (sheafificationAdjunction J AddCommGrpCat.{u + 1}).right_adjoint_additive

/-- **A natural transformation of presheaf-valued functors whose components are inverted by
sheafification becomes a natural isomorphism after sheafification.** -/
def sheafifyNatIso
    {P Q : Sheaf J AddCommGrpCat.{u + 1} ⥤ (Cᵒᵖ ⥤ AddCommGrpCat.{u + 1})}
    (α : P ⟶ Q) (hα : ∀ X, J.W (α.app X)) :
    P ⋙ presheafToSheaf J AddCommGrpCat.{u + 1} ≅
      Q ⋙ presheafToSheaf J AddCommGrpCat.{u + 1} := by
  haveI : ∀ X, IsIso ((Functor.whiskerRight α
      (presheafToSheaf J AddCommGrpCat.{u + 1})).app X) := fun X => (J.W_iff _).mp (hα X)
  haveI := NatIso.isIso_of_isIso_app
    (Functor.whiskerRight α (presheafToSheaf J AddCommGrpCat.{u + 1}))
  exact asIso (Functor.whiskerRight α (presheafToSheaf J AddCommGrpCat.{u + 1}))

end Sheaf

/-! ### Tensoring with a fixed presheaf, as a functor

Here the morphisms of the base category lie in `Type (u + 1)`, as for
`AddCommGrpCat.presheafTensorRight`. -/

section Functor

variable {C : Type u₁} [Category.{u + 1} C]

/-- The functor `- ⊗_ℤ L` on presheaves of abelian groups is additive. -/
instance (L : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}) : (presheafTensorRight L).Additive where
  map_add := presheafTensorMap_add_left _ _ _

/-- **Tensoring with a morphism of presheaves of abelian groups on the right**, as a natural
transformation between the two tensoring functors. -/
def presheafTensorRightMap {L L' : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}} (g : L ⟶ L') :
    presheafTensorRight L ⟶ presheafTensorRight L' where
  app F := presheafTensorMap (𝟙 F) g
  naturality F F' f := by
    change presheafTensorMap f (𝟙 L) ≫ presheafTensorMap (𝟙 F') g =
      presheafTensorMap (𝟙 F) g ≫ presheafTensorMap f (𝟙 L')
    rw [presheafTensorMap_comp, presheafTensorMap_comp, Category.comp_id,
      Category.id_comp, Category.comp_id, Category.id_comp]

/-- The component of `AddCommGrpCat.presheafTensorRightMap g` at `F` is `𝟙 F ⊗ g`. -/
@[simp]
lemma presheafTensorRightMap_app {L L' : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}} (g : L ⟶ L')
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    (presheafTensorRightMap g).app F = presheafTensorMap (𝟙 F) g := rfl


/-- **Tensoring with the constant presheaf `ℤ` on the right is the identity functor.** -/
def presheafTensorRightConstIso :
    presheafTensorRight (constInt.{u + 1, u₁, u} C) ≅ 𝟭 (Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :=
  NatIso.ofComponents (fun F => presheafTensorConstRightIso F) (by
    intro F F' f
    refine presheafTensor_hom_ext fun V t x => ?_
    change (presheafTensorConstRightApp F' V).hom
        ((presheafTensorMap f (𝟙 (constInt.{u + 1, u₁, u} C))).app V (tensorGen t x)) =
      f.app V ((presheafTensorConstRightApp F V).hom (tensorGen t x))
    rw [presheafTensorMap_id_right_tensorGen]
    change x.down • f.app V t = f.app V (x.down • t)
    rw [map_zsmul])


variable (J : GrothendieckTopology C) [HasWeakSheafify J AddCommGrpCat.{u + 1}]

/-- **Tensoring over `ℤ` with a fixed presheaf of abelian groups on the right, on abelian
sheaves**: the sheafification of the objectwise tensor product. -/
def sheafTensorRight (L : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    Sheaf J AddCommGrpCat.{u + 1} ⥤ Sheaf J AddCommGrpCat.{u + 1} :=
  sheafToPresheaf J AddCommGrpCat.{u + 1} ⋙ presheafTensorRight L ⋙
    presheafToSheaf J AddCommGrpCat.{u + 1}

/-- The value of `AddCommGrpCat.sheafTensorRight J L` at `F` is the sheafification of
`F ⊗_ℤ L`. -/
lemma sheafTensorRight_obj (L : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (F : Sheaf J AddCommGrpCat.{u + 1}) :
    (sheafTensorRight J L).obj F =
      (presheafToSheaf J AddCommGrpCat.{u + 1}).obj (presheafTensor F.obj L) := rfl

/-- The functor `F ↦ (F ⊗_ℤ L)^#` on abelian sheaves is additive. -/
instance (L : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}) [HasSheafify J AddCommGrpCat.{u + 1}] :
    (sheafTensorRight J L).Additive :=
  inferInstanceAs (sheafToPresheaf J AddCommGrpCat.{u + 1} ⋙ presheafTensorRight L ⋙
    presheafToSheaf J AddCommGrpCat.{u + 1}).Additive

end Functor

end AddCommGrpCat

end
