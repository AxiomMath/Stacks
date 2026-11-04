module

public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.CategoryTheory.Monoidal.Braided.Transport
public import Mathlib.CategoryTheory.Monoidal.Closed.Transport
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleCoproduct

/-!
# Tensor products of abelian sheaves on the spaces-étale site

Let `X` be an algebraic space over a scheme `S`. The tensor product of two abelian sheaves on
the spaces-étale site of `X` is the sheafification of their objectwise tensor product over `ℤ`.
Stacks 0722 computes it on the extensions by zero of the constant sheaf `ℤ`: for two objects
`U₁` and `U₂` of the site, the tensor product of `j_{U₁!} ℤ` and `j_{U₂!} ℤ` is `j_{U₁₂!} ℤ`,
where `U₁₂ = U₁ ×_X U₂`.

The proof identifies `j_{U!} ℤ` with the sheafification of the free abelian presheaf on the
representable presheaf of `U`, for which the statement is the bijection between pairs of
morphisms into `U₁` and `U₂` and morphisms into `U₁₂`.

## Main definitions

* `AddCommGrpCat.presheafTensor` is the objectwise tensor product over `ℤ` of two presheaves of
  abelian groups, and `AddCommGrpCat.presheafTensorMap` is its functoriality.
* `AddCommGrpCat.monoidalCategory` is the monoidal structure on abelian groups given by the
  tensor product over `ℤ`, obtained by transport along the equivalence with modules over a
  copy of `ℤ` in the right universe.
* `AlgebraicGeometry.Space.SpacesEtale.abelianSheafTensor` is the tensor product of two abelian
  sheaves on the spaces-étale site of `X`.
* `AlgebraicGeometry.Space.SpacesEtale.extensionByZeroConstantGenerator` is the section of
  `j_{U!} ℤ` over `V` attached to a morphism `V ⟶ U`.

## Main results

* `AlgebraicGeometry.Space.SpacesEtale.presheafTensorMap_mem`: the objectwise tensor product of
  two morphisms inverted by sheafification is inverted by sheafification.
* `AlgebraicGeometry.Space.SpacesEtale.extensionByZeroConstantFreeRepresentableIso`:
  `j_{U!} ℤ` is the sheafification of the free abelian presheaf on the representable presheaf
  of `U`.
* `AlgebraicGeometry.Space.SpacesEtale.extensionByZeroConstantTensorIso` is Stacks 0722 for
  the tensor product, and
  `AlgebraicGeometry.Space.SpacesEtale.extensionByZeroConstantTensorIso_hom_generator` computes
  it on a pure tensor of generators.

## Implementation notes

Mathlib has no monoidal structure on `AddCommGrpCat` beyond the cartesian one, and the monoidal
structure on `ModuleCat R` needs `R` in the universe of the modules, so the tensor product of
abelian groups in `Type (u + 1)` is obtained by transporting the monoidal structure of modules
over `ULift.{u + 1} ℤ` along `AddCommGrpCat.uliftIntEquivalence`. That transported product is
only isomorphic to the tensor product over `ℤ`, not equal to it, and
`AddCommGrpCat.presheafTensorIso` is the comparison; it is what carries the one fact about the
monoidal structure that is used, namely that sheafification inverts the tensor product of two
morphisms it inverts.

The objectwise tensor product is defined directly rather than through the transported monoidal
structure, so that its sections are literally `TensorProduct ℤ`, which is what the computation
on generators needs.

The fibre product `U₁ ×_X U₂` enters as an arbitrary binary product of the site, presented by a
limiting `CategoryTheory.Limits.BinaryFan`, so no choice of fibre product is made.

## References

* [Stacks Project, Tag 0722](https://stacks.math.columbia.edu/tag/0722)
* [Stacks Project, Tag 03G0](https://stacks.math.columbia.edu/tag/03G0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Enriched.FunctorCategory
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed

universe v u

namespace AddCommGrpCat

/-! ### The objectwise tensor product of presheaves of abelian groups -/

/-- The objectwise tensor product over `ℤ` of two presheaves of abelian groups. -/
def presheafTensor {C : Type*} [Category C]
    (F G : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}) : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1} where
  obj V := AddCommGrpCat.of (TensorProduct ℤ (F.obj V) (G.obj V))
  map {V W} f := AddCommGrpCat.ofHom
    ((TensorProduct.map (F.map f).hom.toIntLinearMap
      (G.map f).hom.toIntLinearMap).toAddMonoidHom)
  map_id := by
    intro V
    ext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
    | tmul x y => simp
  map_comp := by
    intro V W Z f g
    ext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
    | tmul x y => simp [Functor.map_comp]

/-! ### The tensor product of abelian groups as a monoidal structure -/

/-- A copy of the integers in the universe of the abelian groups considered, used as the base
ring for the tensor product. -/
abbrev ULiftInt := ULift.{v} ℤ

/-- The ring homomorphism from the universe-lifted integers to the integers. -/
def uliftIntDown : ULiftInt.{v} →+* ℤ where
  toFun := ULift.down
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Abelian groups are the modules over a copy of the integers in their own universe. -/
@[sga "3 I 3.1.3" "special case"]
def uliftIntEquivalence : ModuleCat.{v} ULiftInt.{v} ≌ AddCommGrpCat.{v} :=
  (ModuleCat.restrictScalarsEquivalenceOfRingEquiv (ULift.ringEquiv.symm)).trans
    (forget₂ (ModuleCat.{v} ℤ) AddCommGrpCat.{v}).asEquivalence

/-- The monoidal structure on abelian groups given by the tensor product, transported from the
modules over a copy of the integers in the same universe. -/
@[instance_reducible] def monoidalCategory : MonoidalCategory AddCommGrpCat.{v} :=
  Monoidal.transport (uliftIntEquivalence.{v})

/-- An abelian group is a module over the universe-lifted integers. -/
local instance uliftIntModule (A : Type v) [AddCommGroup A] : Module ULiftInt.{v} A :=
  Module.compHom A uliftIntDown

/-- The scalar multiplication of the universe-lifted integers on a module over them. -/
local instance (priority := 1200) uliftIntSMul (A : Type v) [AddCommGroup A]
    [Module ULiftInt.{v} A] : SMul ULiftInt.{v} A :=
  (Module.toDistribMulAction (R := ULiftInt.{v}) (M := A)).toMulAction.toSemigroupAction.toSMul

/-- Scalar multiplication by a universe-lifted integer is the corresponding integer multiple. -/
lemma uliftInt_smul_eq_zsmul (A : Type v) [AddCommGroup A] [Module ULiftInt.{v} A]
    (r : ULiftInt.{v}) (a : A) : r • a = (uliftIntDown r : ℤ) • a := by
  have hr : r = ((uliftIntDown r : ℤ) : ULiftInt.{v}) := by cases r; rfl
  rw [hr]
  exact Int.cast_smul_eq_zsmul ULiftInt.{v} (uliftIntDown r) a

/-- The comparison map from the tensor product over `ℤ` to the tensor product over a
universe-lifted copy of `ℤ`. -/
def tensorProductToULiftInt (A B : Type v) [AddCommGroup A] [AddCommGroup B]
    [Module ULiftInt.{v} A] [Module ULiftInt.{v} B] :
    TensorProduct ℤ A B →+ TensorProduct ULiftInt.{v} A B := by
  let T := TensorProduct ULiftInt.{v} A B
  letI : Module ℤ T := AddCommGroup.toIntModule T
  letI : Module ULiftInt.{v} T := TensorProduct.instModule
  let q : A →ₗ[ℤ] (B →ₗ[ℤ] T) :=
    { toFun := fun a => (TensorProduct.mk ULiftInt.{v} A B a).restrictScalars ℤ
      map_add' := by intro a a'; ext b; simp
      map_smul' := by intro z a; ext b; simp }
  exact (TensorProduct.lift q).toAddMonoidHom

/-- An additive map of abelian groups is linear over a universe-lifted copy of `ℤ`. -/
def linearMapToULiftInt (A B : Type v) [AddCommGroup A] [AddCommGroup B]
    [Module ULiftInt.{v} A] [Module ULiftInt.{v} B] :
    (A →ₗ[ℤ] B) →ₗ[ULiftInt.{v}] (A →ₗ[ULiftInt.{v}] B) where
  toFun f :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := by
        intro r a
        calc
          f (r • a) = f ((uliftIntDown r : ℤ) • a) := by rw [uliftInt_smul_eq_zsmul]
          _ = (uliftIntDown r : ℤ) • f a := map_smul f _ _
          _ = r • f a := by rw [uliftInt_smul_eq_zsmul] }
  map_add' f g := by ext a; rfl
  map_smul' r f := by ext a; simp [uliftInt_smul_eq_zsmul]

/-- The comparison map from the tensor product over a universe-lifted copy of `ℤ` to the tensor
product over `ℤ`. -/
def tensorProductOfULiftInt (A B : Type v) [AddCommGroup A] [AddCommGroup B]
    [Module ULiftInt.{v} A] [Module ULiftInt.{v} B] :
    letI : Module ULiftInt.{v} (TensorProduct ULiftInt.{v} A B) := TensorProduct.instModule
    TensorProduct ULiftInt.{v} A B →+ TensorProduct ℤ A B := by
  letI : Module ℤ (TensorProduct ℤ A B) := AddCommGroup.toIntModule _
  letI : Module ULiftInt.{v} (TensorProduct ULiftInt.{v} A B) := TensorProduct.instModule
  letI : Module ULiftInt.{v} (TensorProduct ℤ A B) :=
    Module.compHom (TensorProduct ℤ A B) uliftIntDown
  let q₁ : A →ₗ[ℤ] (B →ₗ[ULiftInt.{v}] TensorProduct ℤ A B) :=
    ((linearMapToULiftInt B (TensorProduct ℤ A B)).restrictScalars ℤ).comp
      (TensorProduct.mk ℤ A B)
  let q₂ : A →ₗ[ULiftInt.{v}] (B →ₗ[ULiftInt.{v}] TensorProduct ℤ A B) :=
    linearMapToULiftInt A _ q₁
  exact (TensorProduct.lift q₂).toAddMonoidHom

/-- The comparison map to the tensor product over a universe-lifted copy of `ℤ` on a pure
tensor. -/
lemma tensorProductToULiftInt_tmul (A B : Type v) [AddCommGroup A] [AddCommGroup B]
    [Module ULiftInt.{v} A] [Module ULiftInt.{v} B] (a : A) (b : B) :
    tensorProductToULiftInt A B (a ⊗ₜ[ℤ] b) = a ⊗ₜ[ULiftInt.{v}] b := rfl

/-- The comparison map from the tensor product over a universe-lifted copy of `ℤ` on a pure
tensor. -/
lemma tensorProductOfULiftInt_tmul (A B : Type v) [AddCommGroup A] [AddCommGroup B]
    [Module ULiftInt.{v} A] [Module ULiftInt.{v} B] (a : A) (b : B) :
    tensorProductOfULiftInt A B (a ⊗ₜ[ULiftInt.{v}] b) = a ⊗ₜ[ℤ] b := rfl

/-- The tensor product over `ℤ` and the tensor product over a universe-lifted copy of `ℤ`
agree. -/
def tensorProductULiftIntEquiv (A B : Type v) [AddCommGroup A] [AddCommGroup B]
    [Module ULiftInt.{v} A] [Module ULiftInt.{v} B] :
    TensorProduct ℤ A B ≃+ TensorProduct ULiftInt.{v} A B where
  toFun := tensorProductToULiftInt A B
  invFun := tensorProductOfULiftInt A B
  left_inv x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [tensorProductToULiftInt_tmul, tensorProductOfULiftInt_tmul]
    | add x y hx hy => simp only [AddMonoidHom.map_add, hx, hy]
  right_inv x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [tensorProductToULiftInt_tmul, tensorProductOfULiftInt_tmul]
    | add x y hx hy => simp only [AddMonoidHom.map_add, hx, hy]
  map_add' x y := (tensorProductToULiftInt A B).map_add x y

/-- The objectwise tensor product over `ℤ` of two presheaves of abelian groups agrees with the
tensor product of the transported monoidal structure. -/
def presheafTensorIso {C : Type*} [Category C] (F G : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    (letI : MonoidalCategory AddCommGrpCat.{u + 1} := monoidalCategory.{u + 1};
      presheafTensor F G ≅ F ⊗ G) := by
  let e := uliftIntEquivalence.{u + 1}
  letI : MonoidalCategory AddCommGrpCat.{u + 1} := Monoidal.transport e
  letI : e.inverse.Monoidal := by
    change (Monoidal.equivalenceTransported e).inverse.Monoidal
    infer_instance
  letI : e.functor.Monoidal := by
    change (Monoidal.equivalenceTransported e).functor.Monoidal
    infer_instance
  let app : ∀ V : Cᵒᵖ, (presheafTensor F G).obj V ≅ (F ⊗ G).obj V := fun V => by
    let A' := e.inverse.obj (F.obj V)
    let B' := e.inverse.obj (G.obj V)
    let A₀ : Type (u + 1) := ↑A'
    let B₀ : Type (u + 1) := ↑B'
    letI : AddCommGroup A₀ := A'.isAddCommGroup
    letI : AddCommGroup B₀ := B'.isAddCommGroup
    letI : Module (ULiftInt.{u + 1}) A₀ := A'.isModule
    letI : Module (ULiftInt.{u + 1}) B₀ := B'.isModule
    let cA : AddCommGrpCat.of A₀ ≅ F.obj V := e.counitIso.app (F.obj V)
    let cB : AddCommGrpCat.of B₀ ≅ G.obj V := e.counitIso.app (G.obj V)
    let iA : (F.obj V) →ₗ[ℤ] A₀ := cA.inv.hom.toIntLinearMap
    let iB : (G.obj V) →ₗ[ℤ] B₀ := cB.inv.hom.toIntLinearMap
    let pA : A₀ →ₗ[ℤ] (F.obj V) := cA.hom.hom.toIntLinearMap
    let pB : B₀ →ₗ[ℤ] (G.obj V) := cB.hom.hom.toIntLinearMap
    let scalar := tensorProductULiftIntEquiv A₀ B₀
    let tensorR : Type (u + 1) := TensorProduct (ULiftInt.{u + 1}) A₀ B₀
    have htarget : AddCommGrpCat.of tensorR = e.functor.obj (A' ⊗ B') := rfl
    let forward : TensorProduct ℤ (F.obj V) (G.obj V) →+ tensorR :=
      scalar.toAddMonoidHom.comp (TensorProduct.map iA iB).toAddMonoidHom
    let backward : tensorR →+ TensorProduct ℤ (F.obj V) (G.obj V) :=
      (TensorProduct.map pA pB).toAddMonoidHom.comp scalar.symm.toAddMonoidHom
    let iso0 : AddCommGrpCat.of (TensorProduct ℤ (F.obj V) (G.obj V)) ≅
        AddCommGrpCat.of tensorR :=
      { hom := AddCommGrpCat.ofHom forward
        inv := AddCommGrpCat.ofHom backward
        hom_inv_id := by
          ext x
          induction x using TensorProduct.induction_on with
          | zero => exact map_zero (backward.comp forward)
          | tmul x y =>
              change TensorProduct.map pA pB
                (scalar.symm (scalar (TensorProduct.map iA iB (x ⊗ₜ[ℤ] y)))) = _
              rw [scalar.symm_apply_apply, TensorProduct.map_tmul, TensorProduct.map_tmul]
              simp [iA, iB, pA, pB]
          | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
        inv_hom_id := by
          ext x
          induction x using TensorProduct.induction_on with
          | zero => exact map_zero (forward.comp backward)
          | tmul x y =>
              change scalar (TensorProduct.map iA iB
                (TensorProduct.map pA pB (scalar.symm (x ⊗ₜ[ULiftInt.{u + 1}] y)))) = _
              rw [show scalar.symm (x ⊗ₜ[ULiftInt.{u + 1}] y) = x ⊗ₜ[ℤ] y from
                tensorProductOfULiftInt_tmul A₀ B₀ x y, TensorProduct.map_tmul]
              change scalar (iA (pA x) ⊗ₜ[ℤ] iB (pB y)) = x ⊗ₜ[ULiftInt.{u + 1}] y
              rw [show iA (pA x) = x by simp [iA, pA], show iB (pB y) = y by simp [iB, pB]]
              exact tensorProductToULiftInt_tmul A₀ B₀ x y
          | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy }
    change AddCommGrpCat.of (TensorProduct ℤ (F.obj V) (G.obj V)) ≅ e.functor.obj (A' ⊗ B')
    exact iso0 ≪≫ eqToIso htarget
  refine NatIso.ofComponents app ?_
  intro V W f
  ext x
  induction x using TensorProduct.induction_on with
  | zero =>
      exact ((AddCommGrpCat.Hom.hom
        ((presheafTensor F G).map f ≫ (app W).hom)).map_zero).trans
          ((AddCommGrpCat.Hom.hom ((app V).hom ≫ (F ⊗ G).map f)).map_zero).symm
  | add x y hx hy =>
      calc
        (AddCommGrpCat.Hom.hom ((presheafTensor F G).map f ≫ (app W).hom)) (x + y) =
            (AddCommGrpCat.Hom.hom ((presheafTensor F G).map f ≫ (app W).hom)) x +
              (AddCommGrpCat.Hom.hom ((presheafTensor F G).map f ≫ (app W).hom)) y :=
          map_add _ _ _
        _ = (AddCommGrpCat.Hom.hom ((app V).hom ≫ (F ⊗ G).map f)) x +
              (AddCommGrpCat.Hom.hom ((app V).hom ≫ (F ⊗ G).map f)) y :=
          congrArg₂ (· + ·) hx hy
        _ = (AddCommGrpCat.Hom.hom ((app V).hom ≫ (F ⊗ G).map f)) (x + y) :=
          (map_add _ _ _).symm
  | tmul x y =>
      let A'V := e.inverse.obj (F.obj V)
      let B'V := e.inverse.obj (G.obj V)
      let A'W := e.inverse.obj (F.obj W)
      let B'W := e.inverse.obj (G.obj W)
      let A₀V : Type (u + 1) := ↑A'V
      let B₀V : Type (u + 1) := ↑B'V
      let A₀W : Type (u + 1) := ↑A'W
      let B₀W : Type (u + 1) := ↑B'W
      let _ : AddCommGroup A₀V := A'V.isAddCommGroup
      let _ : AddCommGroup B₀V := B'V.isAddCommGroup
      let _ : AddCommGroup A₀W := A'W.isAddCommGroup
      let _ : AddCommGroup B₀W := B'W.isAddCommGroup
      let _ : Module (ULiftInt.{u + 1}) A₀V := A'V.isModule
      let _ : Module (ULiftInt.{u + 1}) B₀V := B'V.isModule
      let _ : Module (ULiftInt.{u + 1}) A₀W := A'W.isModule
      let _ : Module (ULiftInt.{u + 1}) B₀W := B'W.isModule
      let cAV : AddCommGrpCat.of A₀V ≅ F.obj V := e.counitIso.app (F.obj V)
      let cBV : AddCommGrpCat.of B₀V ≅ G.obj V := e.counitIso.app (G.obj V)
      let cAW : AddCommGrpCat.of A₀W ≅ F.obj W := e.counitIso.app (F.obj W)
      let cBW : AddCommGrpCat.of B₀W ≅ G.obj W := e.counitIso.app (G.obj W)
      let iAV : (F.obj V) →ₗ[ℤ] A₀V := cAV.inv.hom.toIntLinearMap
      let iBV : (G.obj V) →ₗ[ℤ] B₀V := cBV.inv.hom.toIntLinearMap
      let iAW : (F.obj W) →ₗ[ℤ] A₀W := cAW.inv.hom.toIntLinearMap
      let iBW : (G.obj W) →ₗ[ℤ] B₀W := cBW.inv.hom.toIntLinearMap
      have hiA : iAW (F.map f x) = (e.inverse.map (F.map f)).hom (iAV x) := by
        change (e.counitIso.inv.app (F.obj W)).hom (F.map f x) = _
        exact congrArg (fun k => k.hom x) (e.counitIso.inv.naturality (F.map f))
      have hiB : iBW (G.map f y) = (e.inverse.map (G.map f)).hom (iBV y) := by
        change (e.counitIso.inv.app (G.obj W)).hom (G.map f y) = _
        exact congrArg (fun k => k.hom y) (e.counitIso.inv.naturality (G.map f))
      dsimp only [app, presheafTensor]
      change tensorProductToULiftInt A₀W B₀W (iAW (F.map f x) ⊗ₜ[ℤ] iBW (G.map f y)) =
        TensorProduct.map (e.inverse.map (F.map f)).hom (e.inverse.map (G.map f)).hom
          (tensorProductToULiftInt A₀V B₀V (iAV x ⊗ₜ[ℤ] iBV y))
      rw [hiA, hiB, tensorProductToULiftInt_tmul, tensorProductToULiftInt_tmul,
        TensorProduct.map_tmul]

end AddCommGrpCat

/-- The tensor product monoidal structure on abelian groups. -/
local instance : MonoidalCategory AddCommGrpCat.{u + 1} :=
  AddCommGrpCat.monoidalCategory.{u + 1}

/-- The inverse of the equivalence between abelian groups and modules over the universe-lifted
integers is monoidal. -/
local instance : (AddCommGrpCat.uliftIntEquivalence.{u + 1}).inverse.Monoidal := by
  change (Monoidal.equivalenceTransported
    (AddCommGrpCat.uliftIntEquivalence.{u + 1})).inverse.Monoidal
  infer_instance

/-- The equivalence between modules over the universe-lifted integers and abelian groups is
monoidal. -/
local instance : (AddCommGrpCat.uliftIntEquivalence.{u + 1}).functor.Monoidal := by
  change (Monoidal.equivalenceTransported
    (AddCommGrpCat.uliftIntEquivalence.{u + 1})).functor.Monoidal
  infer_instance

/-- The tensor product of abelian groups is braided. -/
local instance : BraidedCategory AddCommGrpCat.{u + 1} := by
  change BraidedCategory (Monoidal.Transported (AddCommGrpCat.uliftIntEquivalence.{u + 1}))
  infer_instance

/-- The tensor product of abelian groups is closed. -/
local instance : MonoidalClosed AddCommGrpCat.{u + 1} :=
  MonoidalClosed.ofEquiv (AddCommGrpCat.uliftIntEquivalence.{u + 1}).inverse
    (AddCommGrpCat.uliftIntEquivalence.{u + 1}).symm.toAdjunction

namespace AddCommGrpCat

/-- The objectwise tensor product over `ℤ` of two morphisms of presheaves of abelian groups. -/
def presheafTensorMap {C : Type*} [Category C]
    {F₁ F₂ G₁ G₂ : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}} (f : F₁ ⟶ F₂) (g : G₁ ⟶ G₂) :
    presheafTensor F₁ G₁ ⟶ presheafTensor F₂ G₂ :=
  (presheafTensorIso F₁ G₁).hom ≫ (f ⊗ₘ g) ≫ (presheafTensorIso F₂ G₂).inv

/-- The objectwise tensor product of two morphisms acts on a pure tensor componentwise. -/
lemma presheafTensorMap_app_tmul {C : Type*} [Category C]
    {F₁ F₂ G₁ G₂ : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}} (f : F₁ ⟶ F₂) (g : G₁ ⟶ G₂) (V : Cᵒᵖ)
    (x : F₁.obj V) (y : G₁.obj V) :
    (presheafTensorMap f g).app V (x ⊗ₜ[ℤ] y) = f.app V x ⊗ₜ[ℤ] g.app V y := by
  apply (ConcreteCategory.bijective_of_isIso ((presheafTensorIso F₂ G₂).hom.app V)).1
  show ((presheafTensorIso F₂ G₂).hom.app V) (((presheafTensorIso F₂ G₂).inv.app V)
    ((f ⊗ₘ g).app V (((presheafTensorIso F₁ G₁).hom.app V) (x ⊗ₜ[ℤ] y)))) = _
  rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, Iso.inv_hom_id]
  simp only [NatTrans.id_app, CategoryTheory.id_apply]
  let _ := (uliftIntEquivalence.inverse.obj (F₁.obj V)).isModule
  let _ := (uliftIntEquivalence.inverse.obj (F₂.obj V)).isModule
  let _ := (uliftIntEquivalence.inverse.obj (G₁.obj V)).isModule
  let _ := (uliftIntEquivalence.inverse.obj (G₂.obj V)).isModule
  show TensorProduct.map (uliftIntEquivalence.inverse.map (f.app V)).hom
      (uliftIntEquivalence.inverse.map (g.app V)).hom
      (tensorProductToULiftInt (uliftIntEquivalence.inverse.obj (F₁.obj V))
        (uliftIntEquivalence.inverse.obj (G₁.obj V))
        (((uliftIntEquivalence.counitIso.inv.app (F₁.obj V)) x) ⊗ₜ[ℤ]
        ((uliftIntEquivalence.counitIso.inv.app (G₁.obj V)) y))) =
    tensorProductToULiftInt (uliftIntEquivalence.inverse.obj (F₂.obj V))
      (uliftIntEquivalence.inverse.obj (G₂.obj V))
      ((uliftIntEquivalence.counitIso.inv.app (F₂.obj V)) (f.app V x) ⊗ₜ[ℤ]
      (uliftIntEquivalence.counitIso.inv.app (G₂.obj V)) (g.app V y))
  have h : ∀ {A B : AddCommGrpCat.{u + 1}} (k : A ⟶ B) (z : A),
      (uliftIntEquivalence.counitIso.inv.app B).hom (k.hom z) =
        (uliftIntEquivalence.inverse.map k).hom ((uliftIntEquivalence.counitIso.inv.app A).hom z) :=
    fun k z => congrArg (fun m => m.hom z) (uliftIntEquivalence.counitIso.inv.naturality k)
  rw [h, h]
  rfl

/-! ### Free abelian groups on a product -/

/-- Two additive maps out of the tensor product of two free abelian groups agree as soon as
they agree on the pure tensors of generators. -/
lemma freeTensor_ext {α β : Type*} {M : Type*} [AddCommGroup M]
    (f g : TensorProduct ℤ (FreeAbelianGroup α) (FreeAbelianGroup β) →+ M)
    (h : ∀ (a : α) (b : β), f (FreeAbelianGroup.of a ⊗ₜ[ℤ] FreeAbelianGroup.of b) =
      g (FreeAbelianGroup.of a ⊗ₜ[ℤ] FreeAbelianGroup.of b))
    (x : TensorProduct ℤ (FreeAbelianGroup α) (FreeAbelianGroup β)) : f x = g x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul a b =>
      induction a using FreeAbelianGroup.induction_on with
      | zero => rw [TensorProduct.zero_tmul, map_zero, map_zero]
      | of a =>
          induction b using FreeAbelianGroup.induction_on with
          | zero => rw [TensorProduct.tmul_zero, map_zero, map_zero]
          | of b => exact h a b
          | neg b hb => rw [TensorProduct.tmul_neg, map_neg, map_neg, hb]
          | add b₁ b₂ hb₁ hb₂ => rw [TensorProduct.tmul_add, map_add, map_add, hb₁, hb₂]
      | neg a ha => rw [TensorProduct.neg_tmul, map_neg, map_neg, ha]
      | add a₁ a₂ ha₁ ha₂ => rw [TensorProduct.add_tmul, map_add, map_add, ha₁, ha₂]

/-- The forward comparison from the tensor product of two free abelian groups to the free
abelian group on the product of the index types. -/
def freeProdTensorForward (α β : Type*) :
    TensorProduct ℤ (FreeAbelianGroup α) (FreeAbelianGroup β) →+ FreeAbelianGroup (α × β) :=
  let f : FreeAbelianGroup α →ₗ[ℤ] (FreeAbelianGroup β →ₗ[ℤ] FreeAbelianGroup (α × β)) :=
    (FreeAbelianGroup.lift fun a =>
      (FreeAbelianGroup.lift fun b => FreeAbelianGroup.of (a, b)).toIntLinearMap).toIntLinearMap
  (TensorProduct.lift f).toAddMonoidHom

/-- The backward comparison from the free abelian group on a product of index types to the
tensor product of the two free abelian groups. -/
def freeProdTensorBackward (α β : Type*) :
    FreeAbelianGroup (α × β) →+ TensorProduct ℤ (FreeAbelianGroup α) (FreeAbelianGroup β) :=
  FreeAbelianGroup.lift fun ab => FreeAbelianGroup.of ab.1 ⊗ₜ[ℤ] FreeAbelianGroup.of ab.2

/-- The forward comparison sends the pure tensor of the generators at `a` and `b` to the
generator at `(a, b)`. -/
@[simp]
lemma freeProdTensorForward_of_tmul_of (α β : Type*) (a : α) (b : β) :
    freeProdTensorForward α β (FreeAbelianGroup.of a ⊗ₜ[ℤ] FreeAbelianGroup.of b) =
      FreeAbelianGroup.of (a, b) := by
  simp [freeProdTensorForward, TensorProduct.lift.tmul]

/-- The backward comparison sends the generator at `(a, b)` to the pure tensor of the
generators at `a` and `b`. -/
@[simp]
lemma freeProdTensorBackward_of (α β : Type*) (a : α) (b : β) :
    freeProdTensorBackward α β (FreeAbelianGroup.of (a, b)) =
      FreeAbelianGroup.of a ⊗ₜ[ℤ] FreeAbelianGroup.of b := by
  simp [freeProdTensorBackward]

/-- The tensor product of two free abelian groups is the free abelian group on the product of
the index types. -/
def freeProdTensorEquiv (α β : Type*) :
    TensorProduct ℤ (FreeAbelianGroup α) (FreeAbelianGroup β) ≃+ FreeAbelianGroup (α × β) where
  toFun := freeProdTensorForward α β
  invFun := freeProdTensorBackward α β
  left_inv x :=
    freeTensor_ext ((freeProdTensorBackward α β).comp (freeProdTensorForward α β))
      (AddMonoidHom.id _) (fun _ _ => by simp) x
  right_inv x := by
    induction x using FreeAbelianGroup.induction_on with
    | zero => simp
    | of ab =>
        obtain ⟨a, b⟩ := ab
        simp
    | neg x hx => rw [map_neg, map_neg, hx]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  map_add' x y := map_add (freeProdTensorForward α β) x y

end AddCommGrpCat

namespace AlgebraicGeometry.Space.SpacesEtale

open AddCommGrpCat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-! ### The tensor product of abelian sheaves -/

/-- The tensor product of two abelian sheaves on the spaces-étale site of `X`: the
sheafification of their objectwise tensor product over `ℤ`. -/
abbrev abelianSheafTensor (F G : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) :
    Sheaf (topology B S hS X) AddCommGrpCat.{u + 1} :=
  (presheafToSheaf (topology B S hS X) AddCommGrpCat.{u + 1}).obj
    (presheafTensor F.obj G.obj)

/-! ### Extension by zero of the constant sheaf and the free abelian presheaf -/

/-- The section of `j_{U!} ℤ` over `V` attached to a morphism `V ⟶ U` of the spaces-étale site
of `X`: the universal section at `U`, restricted along the morphism. -/
def extensionByZeroConstantGenerator (U V : SpacesEtale B S hS X) (φ : V ⟶ U) :
    (extensionByZeroConstant B S hS X U).obj.obj (Opposite.op V) :=
  ((extensionByZeroConstantHomEquiv B S hS X U _ (𝟙 _)) ≫
    (extensionByZeroConstant B S hS X U).obj.map φ.op) (ULift.up 1)

/-- Maps out of the sheafified free abelian presheaf on the representable presheaf of `U` are
sections over `U`. -/
def freeAbelianRepresentableHomEquiv (U : SpacesEtale B S hS X)
    (F : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) :
    ((freeAbelianRepresentableSheaf B S hS X).obj U ⟶ F) ≃ (F.obj.obj (Opposite.op U)) :=
  ((sheafificationAdjunction (topology B S hS X) AddCommGrpCat.{u + 1}).homEquiv
      (X := (yoneda.obj U ⋙ AddCommGrpCat.free)) (Y := F)).trans
    (((AddCommGrpCat.adj.whiskerRight (SpacesEtale B S hS X)ᵒᵖ).homEquiv
      (X := yoneda.obj U) (Y := F.obj)).trans
        (yonedaEquiv (X := U) (F := F.obj ⋙ forget AddCommGrpCat)))

/-- Homomorphisms out of the integers are elements. -/
def integerHomEquiv (A : AddCommGrpCat.{u + 1}) :
    (AddCommGrpCat.of (ULift.{u + 1} ℤ) ⟶ A) ≃ A where
  toFun f := f (ULift.up 1)
  invFun x := AddCommGrpCat.ofHom
    { toFun := fun z => z.down • x
      map_zero' := by simp
      map_add' := by intro z w; simp [add_zsmul] }
  left_inv f := by
    ext z
    obtain ⟨z⟩ := z
    have hz := map_zsmul f.hom z (ULift.up 1)
    have hz0 : z • (ULift.up 1 : ULift.{u + 1} ℤ) = ULift.up z := by
      apply ULift.ext
      simp
    rw [hz0] at hz
    simpa using hz.symm
  right_inv x := by simp

/-- Maps out of `j_{U!} ℤ` are sections over `U`. -/
def extensionByZeroConstantSectionEquiv (U : SpacesEtale B S hS X)
    (F : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) :
    (extensionByZeroConstant B S hS X U ⟶ F) ≃ F.obj.obj (Opposite.op U) :=
  (extensionByZeroConstantHomEquiv B S hS X U F).trans
    (integerHomEquiv (F.obj.obj (Opposite.op U)))

/-- The identification of maps out of the sheafified free abelian presheaf on `U` with sections
over `U` is natural in the sheaf. -/
lemma freeAbelianRepresentableHomEquiv_comp (U : SpacesEtale B S hS X)
    {F G : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}}
    (f : (freeAbelianRepresentableSheaf B S hS X).obj U ⟶ F) (g : F ⟶ G) :
    freeAbelianRepresentableHomEquiv B S hS X U G (f ≫ g) =
      (g.hom.app (Opposite.op U)) (freeAbelianRepresentableHomEquiv B S hS X U F f) := by
  dsimp only [freeAbelianRepresentableSheaf] at f
  change ((presheafToSheaf (topology B S hS X) AddCommGrpCat.{u + 1}).obj
    (yoneda.obj U ⋙ AddCommGrpCat.free) ⟶ F) at f
  show yonedaEquiv
      (((AddCommGrpCat.adj.whiskerRight (SpacesEtale B S hS X)ᵒᵖ).homEquiv
        (yoneda.obj U) G.obj)
        ((sheafificationAdjunction (topology B S hS X) AddCommGrpCat.{u + 1}).homEquiv
          ((yoneda.obj U ⋙ AddCommGrpCat.free)) G (f ≫ g))) =
    (g.hom.app (Opposite.op U)) (yonedaEquiv
      (((AddCommGrpCat.adj.whiskerRight (SpacesEtale B S hS X)ᵒᵖ).homEquiv
        (yoneda.obj U) F.obj)
        ((sheafificationAdjunction (topology B S hS X) AddCommGrpCat.{u + 1}).homEquiv
          ((yoneda.obj U ⋙ AddCommGrpCat.free)) F f)))
  rw [(sheafificationAdjunction (topology B S hS X)
    AddCommGrpCat.{u + 1}).homEquiv_naturality_right,
    (AddCommGrpCat.adj.whiskerRight (SpacesEtale B S hS X)ᵒᵖ).homEquiv_naturality_right]
  exact yonedaEquiv_comp _ _

/-- The identification of maps out of `j_{U!} ℤ` with sections over `U` is natural in the
sheaf. -/
lemma extensionByZeroConstantSectionEquiv_comp (U : SpacesEtale B S hS X)
    {F G : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}}
    (f : extensionByZeroConstant B S hS X U ⟶ F) (g : F ⟶ G) :
    extensionByZeroConstantSectionEquiv B S hS X U G (f ≫ g) =
      (g.hom.app (Opposite.op U)) (extensionByZeroConstantSectionEquiv B S hS X U F f) := by
  show (integerHomEquiv (G.obj.obj (Opposite.op U)))
      (extensionByZeroConstantHomEquiv B S hS X U G (f ≫ g)) = _
  rw [extensionByZeroConstantHomEquiv_comp]
  simp [extensionByZeroConstantSectionEquiv, integerHomEquiv]

/-- The universal section of the sheafified free abelian presheaf on `U` over `U`. -/
def freeAbelianRepresentableGenerator (U : SpacesEtale B S hS X) :
    ((freeAbelianRepresentableSheaf B S hS X).obj U).obj.obj (Opposite.op U) :=
  freeAbelianRepresentableHomEquiv B S hS X U
    ((freeAbelianRepresentableSheaf B S hS X).obj U) (𝟙 _)

/-- The universal section of `j_{U!} ℤ` over `U`. -/
def extensionByZeroConstantGeneratorAtId (U : SpacesEtale B S hS X) :
    (extensionByZeroConstant B S hS X U).obj.obj (Opposite.op U) :=
  extensionByZeroConstantSectionEquiv B S hS X U (extensionByZeroConstant B S hS X U) (𝟙 _)

/-- The map from `j_{U!} ℤ` to the sheafified free abelian presheaf on `U` taking the universal
section to the universal section. -/
def extensionByZeroConstantToFreeRepresentable (U : SpacesEtale B S hS X) :
    extensionByZeroConstant B S hS X U ⟶ (freeAbelianRepresentableSheaf B S hS X).obj U :=
  (extensionByZeroConstantSectionEquiv B S hS X U
    ((freeAbelianRepresentableSheaf B S hS X).obj U)).symm
      (freeAbelianRepresentableGenerator B S hS X U)

/-- The map from the sheafified free abelian presheaf on `U` to `j_{U!} ℤ` taking the universal
section to the universal section. -/
def freeRepresentableToExtensionByZeroConstant (U : SpacesEtale B S hS X) :
    (freeAbelianRepresentableSheaf B S hS X).obj U ⟶ extensionByZeroConstant B S hS X U :=
  (freeAbelianRepresentableHomEquiv B S hS X U
    (extensionByZeroConstant B S hS X U)).symm
      (extensionByZeroConstantGeneratorAtId B S hS X U)

/-- The map to `j_{U!} ℤ` sends the universal section over `U` to the universal section. -/
@[simp]
lemma freeRepresentableToExtensionByZeroConstant_generator (U : SpacesEtale B S hS X) :
    ((freeRepresentableToExtensionByZeroConstant B S hS X U).hom.app (Opposite.op U))
        (freeAbelianRepresentableGenerator B S hS X U) =
      extensionByZeroConstantGeneratorAtId B S hS X U := by
  calc
    _ = freeAbelianRepresentableHomEquiv B S hS X U (extensionByZeroConstant B S hS X U)
        (𝟙 _ ≫ freeRepresentableToExtensionByZeroConstant B S hS X U) :=
      (freeAbelianRepresentableHomEquiv_comp B S hS X U (𝟙 _) _).symm
    _ = extensionByZeroConstantGeneratorAtId B S hS X U := by
      simp [freeRepresentableToExtensionByZeroConstant]

/-- The section of `j_{U!} ℤ` attached to `φ : V ⟶ U` is the restriction of the universal
section along `φ`. -/
lemma extensionByZeroConstantGenerator_eq_map (U V : SpacesEtale B S hS X) (φ : V ⟶ U) :
    extensionByZeroConstantGenerator B S hS X U V φ =
      ((extensionByZeroConstant B S hS X U).obj.map φ.op)
        (extensionByZeroConstantGeneratorAtId B S hS X U) := rfl

/-- The map to `j_{U!} ℤ` sends the restriction of the universal section along `φ : V ⟶ U` to
the section attached to `φ`. -/
lemma freeRepresentableToExtensionByZeroConstant_generatorAt
    (U V : SpacesEtale B S hS X) (φ : V ⟶ U) :
    ((freeRepresentableToExtensionByZeroConstant B S hS X U).hom.app (Opposite.op V))
        ((((freeAbelianRepresentableSheaf B S hS X).obj U).obj.map φ.op)
          (freeAbelianRepresentableGenerator B S hS X U)) =
      extensionByZeroConstantGenerator B S hS X U V φ := by
  rw [extensionByZeroConstantGenerator_eq_map, NatTrans.naturality_apply,
    freeRepresentableToExtensionByZeroConstant_generator]

/-- The map out of `j_{U!} ℤ` sends the universal section over `U` to the universal section. -/
@[simp]
lemma extensionByZeroConstantToFreeRepresentable_generator (U : SpacesEtale B S hS X) :
    ((extensionByZeroConstantToFreeRepresentable B S hS X U).hom.app (Opposite.op U))
        (extensionByZeroConstantGeneratorAtId B S hS X U) =
      freeAbelianRepresentableGenerator B S hS X U := by
  calc
    _ = extensionByZeroConstantSectionEquiv B S hS X U
        ((freeAbelianRepresentableSheaf B S hS X).obj U)
        (𝟙 _ ≫ extensionByZeroConstantToFreeRepresentable B S hS X U) :=
      (extensionByZeroConstantSectionEquiv_comp B S hS X U (𝟙 _) _).symm
    _ = freeAbelianRepresentableGenerator B S hS X U := by
      simp [extensionByZeroConstantToFreeRepresentable]

/-- The map out of `j_{U!} ℤ` sends the section attached to `φ : V ⟶ U` to the restriction of
the universal section along `φ`. -/
lemma extensionByZeroConstantToFreeRepresentable_generatorAt
    (U V : SpacesEtale B S hS X) (φ : V ⟶ U) :
    ((extensionByZeroConstantToFreeRepresentable B S hS X U).hom.app (Opposite.op V))
        (extensionByZeroConstantGenerator B S hS X U V φ) =
      (((freeAbelianRepresentableSheaf B S hS X).obj U).obj.map φ.op)
        (freeAbelianRepresentableGenerator B S hS X U) := by
  rw [extensionByZeroConstantGenerator_eq_map, NatTrans.naturality_apply,
    extensionByZeroConstantToFreeRepresentable_generator]

/-- Extension by zero of the constant sheaf `ℤ` from the slice site at `U` is the sheafified
free abelian presheaf on the representable presheaf of `U`. -/
def extensionByZeroConstantFreeRepresentableIso (U : SpacesEtale B S hS X) :
    extensionByZeroConstant B S hS X U ≅ (freeAbelianRepresentableSheaf B S hS X).obj U where
  hom := extensionByZeroConstantToFreeRepresentable B S hS X U
  inv := freeRepresentableToExtensionByZeroConstant B S hS X U
  hom_inv_id := by
    apply (extensionByZeroConstantSectionEquiv B S hS X U _).injective
    rw [extensionByZeroConstantSectionEquiv_comp]
    simp only [extensionByZeroConstantToFreeRepresentable, Equiv.apply_symm_apply]
    rw [freeRepresentableToExtensionByZeroConstant_generator]
    rfl
  inv_hom_id := by
    apply (freeAbelianRepresentableHomEquiv B S hS X U _).injective
    rw [freeAbelianRepresentableHomEquiv_comp]
    simp only [freeRepresentableToExtensionByZeroConstant, Equiv.apply_symm_apply]
    rw [extensionByZeroConstantToFreeRepresentable_generator]
    rfl

/-- The canonical map from the free abelian presheaf on the representable presheaf of `U` to
the underlying presheaf of `j_{U!} ℤ`. -/
def freeRepresentableUnit (U : SpacesEtale B S hS X) :
    (yoneda.obj U ⋙ AddCommGrpCat.free) ⟶ (extensionByZeroConstant B S hS X U).obj :=
  toSheafify (topology B S hS X) _ ≫
    (extensionByZeroConstantFreeRepresentableIso B S hS X U).inv.hom

/-- The universal section of the sheafified free abelian presheaf on `U` is the image of the
generator at `𝟙 U` under the unit of sheafification. -/
lemma freeAbelianRepresentableGenerator_eq (U : SpacesEtale B S hS X) :
    freeAbelianRepresentableGenerator B S hS X U =
      (toSheafify (topology B S hS X) (yoneda.obj U ⋙ AddCommGrpCat.free)).app
        (Opposite.op U) (FreeAbelianGroup.of (𝟙 U)) := rfl

/-- The canonical map to `j_{U!} ℤ` sends the generator at `φ : V ⟶ U` to the section
attached to `φ`. -/
lemma freeRepresentableUnit_generator (U V : SpacesEtale B S hS X) (φ : V ⟶ U) :
    (freeRepresentableUnit B S hS X U).app (Opposite.op V) (FreeAbelianGroup.of φ) =
      extensionByZeroConstantGenerator B S hS X U V φ := by
  have hn := congrArg (fun k => k (FreeAbelianGroup.of (𝟙 U)))
    ((toSheafify (topology B S hS X) (yoneda.obj U ⋙ AddCommGrpCat.free)).naturality φ.op)
  show ((freeRepresentableToExtensionByZeroConstant B S hS X U).hom.app (Opposite.op V))
      ((toSheafify (topology B S hS X) (yoneda.obj U ⋙ AddCommGrpCat.free)).app
        (Opposite.op V) (FreeAbelianGroup.of φ)) = _
  rw [← freeRepresentableToExtensionByZeroConstant_generatorAt B S hS X U V φ,
    freeAbelianRepresentableGenerator_eq]
  congr 1

/-- The canonical map from the free abelian presheaf on the representable presheaf of `U` to
`j_{U!} ℤ` is inverted by sheafification. -/
lemma freeRepresentableUnit_mem (U : SpacesEtale B S hS X) :
    (topology B S hS X).W (freeRepresentableUnit B S hS X U) :=
  (topology B S hS X).W.comp_mem _ _ ((topology B S hS X).W_toSheafify _)
    (((topology B S hS X).W_sheafToPresheaf_map_iff_isIso
      (extensionByZeroConstantFreeRepresentableIso B S hS X U).inv).mpr inferInstance)

/-! ### The free abelian presheaf on a binary product -/

/-- A pair of morphisms into the two factors of a binary product is a morphism into the
product. -/
def binaryFanHomEquiv (U₁ U₂ U₁₂ : SpacesEtale B S hS X) (p₁ : U₁₂ ⟶ U₁) (p₂ : U₁₂ ⟶ U₂)
    (h : IsLimit (BinaryFan.mk p₁ p₂)) (V : SpacesEtale B S hS X) :
    (V ⟶ U₁) × (V ⟶ U₂) ≃ (V ⟶ U₁₂) where
  toFun q := h.lift (BinaryFan.mk q.1 q.2)
  invFun f := (f ≫ p₁, f ≫ p₂)
  left_inv q := Prod.ext (h.fac (BinaryFan.mk q.1 q.2) ⟨WalkingPair.left⟩)
    (h.fac (BinaryFan.mk q.1 q.2) ⟨WalkingPair.right⟩)
  right_inv f := by
    apply h.hom_ext
    intro j
    obtain ⟨j⟩ := j
    cases j with
    | left => simpa using h.fac (BinaryFan.mk (f ≫ p₁) (f ≫ p₂)) ⟨WalkingPair.left⟩
    | right => simpa using h.fac (BinaryFan.mk (f ≫ p₁) (f ≫ p₂)) ⟨WalkingPair.right⟩

/-- Precomposition commutes with pairing into a binary product. -/
lemma binaryFan_lift_comp {U₁ U₂ U₁₂ : SpacesEtale B S hS X} {p₁ : U₁₂ ⟶ U₁} {p₂ : U₁₂ ⟶ U₂}
    (h : IsLimit (BinaryFan.mk p₁ p₂)) {V W : SpacesEtale B S hS X} (g : W ⟶ V)
    (φ₁ : V ⟶ U₁) (φ₂ : V ⟶ U₂) :
    h.lift (BinaryFan.mk (g ≫ φ₁) (g ≫ φ₂)) = g ≫ h.lift (BinaryFan.mk φ₁ φ₂) := by
  refine h.hom_ext fun j => ?_
  obtain ⟨j⟩ := j
  cases j with
  | left =>
      rw [h.fac (BinaryFan.mk (g ≫ φ₁) (g ≫ φ₂)) ⟨WalkingPair.left⟩, Category.assoc]
      exact congrArg (g ≫ ·) (h.fac (BinaryFan.mk φ₁ φ₂) ⟨WalkingPair.left⟩).symm
  | right =>
      rw [h.fac (BinaryFan.mk (g ≫ φ₁) (g ≫ φ₂)) ⟨WalkingPair.right⟩, Category.assoc]
      exact congrArg (g ≫ ·) (h.fac (BinaryFan.mk φ₁ φ₂) ⟨WalkingPair.right⟩).symm

/-- The objectwise tensor product of the free abelian presheaves on two objects of the
spaces-étale site of `X` is the free abelian presheaf on their product. -/
def freeRepresentableTensorIso (U₁ U₂ U₁₂ : SpacesEtale B S hS X) (p₁ : U₁₂ ⟶ U₁)
    (p₂ : U₁₂ ⟶ U₂) (h : IsLimit (BinaryFan.mk p₁ p₂)) :
    presheafTensor ((yoneda.obj U₁ ⋙ AddCommGrpCat.free))
        ((yoneda.obj U₂ ⋙ AddCommGrpCat.free)) ≅
      (yoneda.obj U₁₂ ⋙ AddCommGrpCat.free) := by
  let comp : ∀ V : (SpacesEtale B S hS X)ᵒᵖ,
      TensorProduct ℤ (FreeAbelianGroup (V.unop ⟶ U₁)) (FreeAbelianGroup (V.unop ⟶ U₂)) ≃+
        FreeAbelianGroup (V.unop ⟶ U₁₂) := fun V =>
    (freeProdTensorEquiv (V.unop ⟶ U₁) (V.unop ⟶ U₂)).trans
      (FreeAbelianGroup.equivOfEquiv (binaryFanHomEquiv B S hS X U₁ U₂ U₁₂ p₁ p₂ h V.unop))
  refine NatIso.ofComponents (fun V => ?_) ?_
  · exact
      { hom := AddCommGrpCat.ofHom (comp V).toAddMonoidHom
        inv := AddCommGrpCat.ofHom (comp V).symm.toAddMonoidHom
        hom_inv_id := by ext x; exact (comp V).symm_apply_apply x
        inv_hom_id := by ext x; exact (comp V).apply_symm_apply x }
  · intro V W f
    ext z
    refine AddCommGrpCat.freeTensor_ext
      (AddCommGrpCat.Hom.hom ((presheafTensor ((yoneda.obj U₁ ⋙ AddCommGrpCat.free))
        ((yoneda.obj U₂ ⋙ AddCommGrpCat.free))).map f ≫
        AddCommGrpCat.ofHom (comp W).toAddMonoidHom))
      (AddCommGrpCat.Hom.hom (AddCommGrpCat.ofHom (comp V).toAddMonoidHom ≫
        ((yoneda.obj U₁₂ ⋙ AddCommGrpCat.free)).map f)) (fun φ₁ φ₂ => ?_) z
    change comp W (FreeAbelianGroup.of (f.unop ≫ φ₁) ⊗ₜ[ℤ]
      FreeAbelianGroup.of (f.unop ≫ φ₂)) =
      FreeAbelianGroup.map (fun φ : V.unop ⟶ U₁₂ => f.unop ≫ φ)
        (comp V (FreeAbelianGroup.of φ₁ ⊗ₜ[ℤ] FreeAbelianGroup.of φ₂))
    simp only [comp, AddEquiv.trans_apply, freeProdTensorEquiv,
      AddEquiv.coe_mk, Equiv.coe_fn_mk, freeProdTensorForward_of_tmul_of,
      FreeAbelianGroup.equivOfEquiv, FreeAbelianGroup.map_of_apply]
    exact congrArg FreeAbelianGroup.of (binaryFan_lift_comp B S hS X h f.unop φ₁ φ₂)

/-- The comparison of free abelian presheaves sends a pure tensor of generators to the
generator indexed by the pairing of the two morphisms. -/
lemma freeRepresentableTensorIso_hom_app_tmul (U₁ U₂ U₁₂ : SpacesEtale B S hS X)
    (p₁ : U₁₂ ⟶ U₁) (p₂ : U₁₂ ⟶ U₂) (h : IsLimit (BinaryFan.mk p₁ p₂))
    (V : SpacesEtale B S hS X) (φ₁ : V ⟶ U₁) (φ₂ : V ⟶ U₂) :
    (freeRepresentableTensorIso B S hS X U₁ U₂ U₁₂ p₁ p₂ h).hom.app (Opposite.op V)
        (FreeAbelianGroup.of φ₁ ⊗ₜ[ℤ] FreeAbelianGroup.of φ₂) =
      FreeAbelianGroup.of (h.lift (BinaryFan.mk φ₁ φ₂)) := by
  show FreeAbelianGroup.map (binaryFanHomEquiv B S hS X U₁ U₂ U₁₂ p₁ p₂ h V)
    (freeProdTensorForward _ _ (FreeAbelianGroup.of φ₁ ⊗ₜ[ℤ] FreeAbelianGroup.of φ₂)) = _
  rw [freeProdTensorForward_of_tmul_of, FreeAbelianGroup.map_of_apply]
  rfl

/-! ### The tensor product of extensions by zero of the constant sheaf -/

section Tensor

/-- Abelian groups are enriched over themselves. -/
local instance : EnrichedOrdinaryCategory AddCommGrpCat.{u + 1} AddCommGrpCat.{u + 1} :=
  inferInstance

/-- Presheaves of abelian groups on the spaces-étale site have functor enriched hom objects. -/
local instance : ∀ F G : (SpacesEtale B S hS X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
    HasFunctorEnrichedHom AddCommGrpCat.{u + 1} F G := by
  intro F G V
  infer_instance

/-- Presheaves of abelian groups on the spaces-étale site have enriched hom objects. -/
local instance : ∀ F G : (SpacesEtale B S hS X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
    HasEnrichedHom AddCommGrpCat.{u + 1} F G := by
  intro F G
  infer_instance

/-- The morphisms of presheaves of abelian groups inverted by sheafification are stable under
tensor products. -/
local instance : ((topology B S hS X).W (A := AddCommGrpCat.{u + 1})).IsMonoidal :=
  inferInstance

/-- The objectwise tensor product of two morphisms of presheaves of abelian groups which are
inverted by sheafification is inverted by sheafification. -/
lemma presheafTensorMap_mem
    {F₁ F₂ G₁ G₂ : (SpacesEtale B S hS X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}} (f : F₁ ⟶ F₂)
    (g : G₁ ⟶ G₂) (hf : (topology B S hS X).W f) (hg : (topology B S hS X).W g) :
    (topology B S hS X).W (presheafTensorMap f g) := by
  apply MorphismProperty.RespectsIso.precomp
  apply MorphismProperty.RespectsIso.postcomp
  exact (topology B S hS X).W.tensorHom_mem f g hf hg

/-- The tensor product of the extensions by zero of the constant sheaf `ℤ` from two objects of
the spaces-étale site of `X` is the extension by zero from their product. -/
@[stacks 0722 "product_tensor"]
def extensionByZeroConstantTensorIso (U₁ U₂ U₁₂ : SpacesEtale B S hS X) (p₁ : U₁₂ ⟶ U₁)
    (p₂ : U₁₂ ⟶ U₂) (h : IsLimit (BinaryFan.mk p₁ p₂)) :
    abelianSheafTensor B S hS X (extensionByZeroConstant B S hS X U₁)
        (extensionByZeroConstant B S hS X U₂) ≅
      extensionByZeroConstant B S hS X U₁₂ := by
  have hiso : IsIso ((presheafToSheaf (topology B S hS X) AddCommGrpCat.{u + 1}).map
      (presheafTensorMap (freeRepresentableUnit B S hS X U₁)
        (freeRepresentableUnit B S hS X U₂))) :=
    ((topology B S hS X).W_iff _).mp
      (presheafTensorMap_mem B S hS X _ _
        (freeRepresentableUnit_mem B S hS X U₁) (freeRepresentableUnit_mem B S hS X U₂))
  exact (asIso ((presheafToSheaf (topology B S hS X) AddCommGrpCat.{u + 1}).map
      (presheafTensorMap (freeRepresentableUnit B S hS X U₁)
        (freeRepresentableUnit B S hS X U₂)))).symm ≪≫
    (presheafToSheaf (topology B S hS X) AddCommGrpCat.{u + 1}).mapIso
      (freeRepresentableTensorIso B S hS X U₁ U₂ U₁₂ p₁ p₂ h) ≪≫
    (extensionByZeroConstantFreeRepresentableIso B S hS X U₁₂).symm

/-- The sheafified tensor product of the canonical maps, followed by the tensor-product
isomorphism, is the sheafified comparison of free abelian presheaves followed by the
identification with `j_{U₁₂!} ℤ`. -/
lemma presheafToSheaf_map_presheafTensorMap_comp_tensorIso_hom
    (U₁ U₂ U₁₂ : SpacesEtale B S hS X) (p₁ : U₁₂ ⟶ U₁) (p₂ : U₁₂ ⟶ U₂)
    (h : IsLimit (BinaryFan.mk p₁ p₂)) :
    (presheafToSheaf (topology B S hS X) AddCommGrpCat.{u + 1}).map
        (presheafTensorMap (freeRepresentableUnit B S hS X U₁)
          (freeRepresentableUnit B S hS X U₂)) ≫
      (extensionByZeroConstantTensorIso B S hS X U₁ U₂ U₁₂ p₁ p₂ h).hom =
    (presheafToSheaf (topology B S hS X) AddCommGrpCat.{u + 1}).map
        (freeRepresentableTensorIso B S hS X U₁ U₂ U₁₂ p₁ p₂ h).hom ≫
      (extensionByZeroConstantFreeRepresentableIso B S hS X U₁₂).inv := by
  have hiso := ((topology B S hS X).W_iff _).mp
    (presheafTensorMap_mem B S hS X _ _
      (freeRepresentableUnit_mem B S hS X U₁) (freeRepresentableUnit_mem B S hS X U₂))
  have key : (extensionByZeroConstantTensorIso B S hS X U₁ U₂ U₁₂ p₁ p₂ h).hom =
      inv ((presheafToSheaf (topology B S hS X) AddCommGrpCat.{u + 1}).map
          (presheafTensorMap (freeRepresentableUnit B S hS X U₁)
            (freeRepresentableUnit B S hS X U₂))) ≫
        ((presheafToSheaf (topology B S hS X) AddCommGrpCat.{u + 1}).map
            (freeRepresentableTensorIso B S hS X U₁ U₂ U₁₂ p₁ p₂ h).hom ≫
          (extensionByZeroConstantFreeRepresentableIso B S hS X U₁₂).inv) := rfl
  rw [key, IsIso.hom_inv_id_assoc]

/-- The comparison of the free abelian presheaves, followed by the unit of sheafification and
the tensor-product isomorphism, is the unit of sheafification at the product. -/
lemma presheafTensorMap_comp_toSheafify_comp_tensorIso (U₁ U₂ U₁₂ : SpacesEtale B S hS X)
    (p₁ : U₁₂ ⟶ U₁) (p₂ : U₁₂ ⟶ U₂) (h : IsLimit (BinaryFan.mk p₁ p₂)) :
    presheafTensorMap (freeRepresentableUnit B S hS X U₁)
          (freeRepresentableUnit B S hS X U₂) ≫
        toSheafify (topology B S hS X)
          (presheafTensor (extensionByZeroConstant B S hS X U₁).obj
            (extensionByZeroConstant B S hS X U₂).obj) ≫
        (extensionByZeroConstantTensorIso B S hS X U₁ U₂ U₁₂ p₁ p₂ h).hom.hom =
      (freeRepresentableTensorIso B S hS X U₁ U₂ U₁₂ p₁ p₂ h).hom ≫
        freeRepresentableUnit B S hS X U₁₂ := by
  have hpre : sheafifyMap (topology B S hS X)
        (presheafTensorMap (freeRepresentableUnit B S hS X U₁)
          (freeRepresentableUnit B S hS X U₂)) ≫
        (extensionByZeroConstantTensorIso B S hS X U₁ U₂ U₁₂ p₁ p₂ h).hom.hom =
      sheafifyMap (topology B S hS X)
        (freeRepresentableTensorIso B S hS X U₁ U₂ U₁₂ p₁ p₂ h).hom ≫
        (extensionByZeroConstantFreeRepresentableIso B S hS X U₁₂).inv.hom :=
    congrArg (fun m => (sheafToPresheaf (topology B S hS X) AddCommGrpCat.{u + 1}).map m)
      (presheafToSheaf_map_presheafTensorMap_comp_tensorIso_hom B S hS X U₁ U₂ U₁₂ p₁ p₂ h)
  rw [toSheafify_naturality_assoc, hpre]
  exact (toSheafify_naturality_assoc (topology B S hS X)
    (freeRepresentableTensorIso B S hS X U₁ U₂ U₁₂ p₁ p₂ h).hom
    (extensionByZeroConstantFreeRepresentableIso B S hS X U₁₂).inv.hom).symm

/-- The tensor-product isomorphism sends the pure tensor of the generators indexed by `φ₁` and
`φ₂` to the generator indexed by their pairing into the product. -/
@[stacks 0722 "product_tensor on generators"]
theorem extensionByZeroConstantTensorIso_hom_generator (U₁ U₂ U₁₂ : SpacesEtale B S hS X)
    (p₁ : U₁₂ ⟶ U₁) (p₂ : U₁₂ ⟶ U₂) (h : IsLimit (BinaryFan.mk p₁ p₂))
    (V : SpacesEtale B S hS X) (φ₁ : V ⟶ U₁) (φ₂ : V ⟶ U₂) :
    ((extensionByZeroConstantTensorIso B S hS X U₁ U₂ U₁₂ p₁ p₂ h).hom.hom.app
        (Opposite.op V))
      (((toSheafify (topology B S hS X)
        (presheafTensor (extensionByZeroConstant B S hS X U₁).obj
          (extensionByZeroConstant B S hS X U₂).obj)).app (Opposite.op V))
        (TensorProduct.tmul ℤ (extensionByZeroConstantGenerator B S hS X U₁ V φ₁)
          (extensionByZeroConstantGenerator B S hS X U₂ V φ₂))) =
      extensionByZeroConstantGenerator B S hS X U₁₂ V (h.lift (BinaryFan.mk φ₁ φ₂)) := by
  have ht := presheafTensorMap_app_tmul (freeRepresentableUnit B S hS X U₁)
    (freeRepresentableUnit B S hS X U₂) (Opposite.op V) (FreeAbelianGroup.of φ₁)
    (FreeAbelianGroup.of φ₂)
  rw [freeRepresentableUnit_generator, freeRepresentableUnit_generator] at ht
  rw [← ht]
  refine Eq.trans ?_ (freeRepresentableUnit_generator B S hS X U₁₂ V
    (h.lift (BinaryFan.mk φ₁ φ₂)))
  rw [← freeRepresentableTensorIso_hom_app_tmul B S hS X U₁ U₂ U₁₂ p₁ p₂ h V φ₁ φ₂]
  exact congrArg
    (fun k => k.app (Opposite.op V) (FreeAbelianGroup.of φ₁ ⊗ₜ[ℤ] FreeAbelianGroup.of φ₂))
    (presheafTensorMap_comp_toSheafify_comp_tensorIso B S hS X U₁ U₂ U₁₂ p₁ p₂ h)

end Tensor

end AlgebraicGeometry.Space.SpacesEtale

end
