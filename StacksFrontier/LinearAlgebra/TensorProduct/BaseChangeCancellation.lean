module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Cancelling both base changes to a tensor product of algebras

Let `A` and `B` be commutative algebras over a commutative ring `R`, let `M` be an `A`-module and
`N` a `B`-module, and write `T = A ⊗_R B`. Base changing `M` and `N` to `T` and tensoring the
results over `T` recovers the tensor product of `M` and `N` over `R`:
`(T ⊗_A M) ⊗_T (T ⊗_B N) ≅ M ⊗_R N`.

## Main definitions

* `Stacks.TensorProductPushout.cancelBaseChange`: the `R`-linear equivalence
  `(T ⊗_A M) ⊗_T (T ⊗_B N) ≃ M ⊗_R N`.
* `Stacks.TensorProductPushout.extendScalarsObjIso`: the base change of a module along
  `algebraMap R S`, as `ModuleCat.extendScalars` computes it, is the tensor product `S ⊗_R M`
  formed with the `Algebra` instance.
* `Stacks.TensorProductPushout.extendScalarsCancelIso`: the cancellation again, phrased with
  `ModuleCat.extendScalars` and `ModuleCat.restrictScalars` for the base changes and for the
  two restrictions to `R`.

## Main results

* `Stacks.TensorProductPushout.cancelBaseChange_one_tmul`,
  `Stacks.TensorProductPushout.cancelBaseChange_symm_tmul` and
  `Stacks.TensorProductPushout.cancelBaseChange_tmul_tmul` evaluate the equivalence and its
  inverse on pure tensors: `(1 ⊗ m) ⊗ (1 ⊗ n) ↦ m ⊗ n`, and more generally
  `((a ⊗ b) ⊗ m) ⊗ ((a' ⊗ b') ⊗ n) ↦ (a a' • m) ⊗ (b b' • n)`.

## Implementation notes

The equivalence is `R`-linear and no more: its middle steps are `B`-linear and the final
commutation of `N ⊗_R M` into `M ⊗_R N` is only `R`-linear.

Two Mathlib instances are deliberately not global, because they would make the action of `S` on
`S ⊗_R S` ambiguous, and are introduced here as local instances: the `B`-algebra structure
`Algebra.TensorProduct.rightAlgebra` on `A ⊗_R B`, and the `IsScalarTower R B (A ⊗_R B)` and
`SMulCommClass` instances it carries with it come from the same section of Mathlib.

`ModuleCat.extendScalars` and `ModuleCat.restrictScalars` give a module over the source ring of a
ring map through `Module.compHom`, not through an `Algebra` instance, and the two structures are
equal but not definitionally equal. `Stacks.TensorProductPushout.extendScalarsObjIso'` is the
device that crosses between them for `extendScalars`: for a ring map `f` whose induced algebra
structure is *the* algebra structure, substituting that equation makes `Module.compHom _ f` and
`Algebra.toModule` definitionally equal, so the comparison is the identity and its value on pure
tensors is `rfl`.

For `restrictScalars` no such substitution is used. `AddEquiv.toLinearEquiv` builds the `R`-linear
equivalence out of the underlying additive equivalence, whose type mentions no `Module R`
structure, together with the compatibility `f r • x = r • x`; so the two structures are compared
once, inside a proof, instead of being transported, and the resulting equivalence reduces on a
pure tensor without the kernel having an `Eq.mpr` to unfold.
-/

@[expose] public noncomputable section

open TensorProduct

namespace Stacks.TensorProductPushout

universe u v w x y

section LinearEquivVersion

variable (R : Type u) (A : Type v) (B : Type w) (M : Type x) (N : Type y)
  [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
  [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
  [AddCommGroup N] [Module R N] [Module B N] [IsScalarTower R B N]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- For commutative `R`-algebras `A` and `B`, an `A`-module `M` and a `B`-module `N`, the tensor
product over `T = A ⊗_R B` of the base changes of `M` and of `N` to `T` is the tensor product of
`M` and `N` over `R`. -/
def cancelBaseChange :
    ((A ⊗[R] B) ⊗[A] M) ⊗[A ⊗[R] B] ((A ⊗[R] B) ⊗[B] N) ≃ₗ[R] M ⊗[R] N :=
  (AlgebraTensorModule.cancelBaseChange B (A ⊗[R] B) (A ⊗[R] B)
      ((A ⊗[R] B) ⊗[A] M) N).restrictScalars R ≪≫ₗ
    (TensorProduct.congr (Algebra.IsPushout.cancelBaseChange R B A (A ⊗[R] B) M)
        (LinearEquiv.refl B N) ≪≫ₗ
      TensorProduct.comm B (B ⊗[R] M) N ≪≫ₗ
      AlgebraTensorModule.cancelBaseChange R B B N M).restrictScalars R ≪≫ₗ
    TensorProduct.comm R N M

variable {M N}

/-- `cancelBaseChange` sends `(1 ⊗ m) ⊗ (1 ⊗ n)` to `m ⊗ n`. -/
@[simp]
theorem cancelBaseChange_one_tmul (m : M) (n : N) :
    cancelBaseChange R A B M N (((1 : A ⊗[R] B) ⊗ₜ m) ⊗ₜ ((1 : A ⊗[R] B) ⊗ₜ n)) = m ⊗ₜ n := by
  simp [cancelBaseChange]

/-- The inverse of `cancelBaseChange` sends `m ⊗ n` to `(1 ⊗ m) ⊗ (1 ⊗ n)`. -/
@[simp]
theorem cancelBaseChange_symm_tmul (m : M) (n : N) :
    (cancelBaseChange R A B M N).symm (m ⊗ₜ n) =
      ((1 : A ⊗[R] B) ⊗ₜ m) ⊗ₜ ((1 : A ⊗[R] B) ⊗ₜ n) := by
  simp [cancelBaseChange]

/-- `cancelBaseChange` sends `((a ⊗ b) ⊗ m) ⊗ ((a' ⊗ b') ⊗ n)` to `(a a' • m) ⊗ (b b' • n)`. -/
theorem cancelBaseChange_tmul_tmul (a a' : A) (b b' : B) (m : M) (n : N) :
    cancelBaseChange R A B M N (((a ⊗ₜ b) ⊗ₜ m) ⊗ₜ ((a' ⊗ₜ b') ⊗ₜ n)) =
      ((a * a') • m) ⊗ₜ ((b * b') • n) := by
  have htmul : ∀ (a : A) (b : B), (a ⊗ₜ[R] b : A ⊗[R] B) = a • (1 ⊗ₜ[R] b) := fun a b => by
    rw [Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply,
      Algebra.TensorProduct.tmul_mul_tmul]
    simp
  have hsmul : ∀ b : B, b • (1 : A ⊗[R] B) = 1 ⊗ₜ[R] b := fun b => by
    rw [Algebra.smul_def, Algebra.TensorProduct.right_algebraMap_apply, mul_one]
  rw [show ((a' ⊗ₜ[R] b') ⊗ₜ[B] n : (A ⊗[R] B) ⊗[B] N)
        = (a' ⊗ₜ[R] b' : A ⊗[R] B) • ((1 : A ⊗[R] B) ⊗ₜ[B] n) by
      rw [TensorProduct.smul_tmul' (R := B), smul_eq_mul, mul_one],
    ← TensorProduct.smul_tmul,
    show ((a' ⊗ₜ[R] b' : A ⊗[R] B) • ((a ⊗ₜ[R] b) ⊗ₜ[A] m) : (A ⊗[R] B) ⊗[A] M)
        = (b * b') • ((1 : A ⊗[R] B) ⊗ₜ[A] ((a * a') • m)) by
      rw [TensorProduct.smul_tmul' (R := A), smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul,
        TensorProduct.smul_tmul' (R := A), hsmul, htmul, TensorProduct.smul_tmul, mul_comm a' a,
        mul_comm b' b],
    TensorProduct.smul_tmul, TensorProduct.smul_tmul' (R := B), TensorProduct.smul_tmul,
    cancelBaseChange_one_tmul]

end LinearEquivVersion

/-! ### The cancellation for `ModuleCat.extendScalars` -/

section ModuleCatVersion

open CategoryTheory

/-- Extension of scalars along a ring map `f : R ⟶ S` whose induced algebra structure is the
given one sends a module `M` to the base change `S ⊗_R M`. -/
def extendScalarsObjIso' {R S : Type u} [CommRing R] [CommRing S] [i : Algebra R S]
    (f : R →+* S) (h : f.toAlgebra = i) (M : ModuleCat.{u} R) :
    (ModuleCat.extendScalars f).obj M ≅ ModuleCat.of S (S ⊗[R] M) := by
  subst h
  exact Iso.refl _

open scoped ChangeOfRings in
/-- `Stacks.TensorProductPushout.extendScalarsObjIso'` is the identity on pure tensors. -/
theorem extendScalarsObjIso'_hom_tmul {R S : Type u} [CommRing R] [CommRing S] [i : Algebra R S]
    (f : R →+* S) (h : f.toAlgebra = i) (M : ModuleCat.{u} R) (s : S) (m : M) :
    (extendScalarsObjIso' f h M).hom (s ⊗ₜ[R, f] m) = s ⊗ₜ[R] m := by
  subst h
  rfl

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- Extension of scalars along `algebraMap R S` sends a module `M` to the base change
`S ⊗_R M`. -/
def extendScalarsObjIso (M : ModuleCat.{u} R) :
    (ModuleCat.extendScalars (algebraMap R S)).obj M ≅ ModuleCat.of S (S ⊗[R] M) :=
  extendScalarsObjIso' (algebraMap R S) toAlgebra_algebraMap M

open scoped ChangeOfRings in
/-- `extendScalarsObjIso` is the identity on pure tensors. -/
@[simp]
theorem extendScalarsObjIso_hom_tmul (M : ModuleCat.{u} R) (s : S) (m : M) :
    (extendScalarsObjIso M).hom (s ⊗ₜ[R, algebraMap R S] m) = s ⊗ₜ[R] m :=
  extendScalarsObjIso'_hom_tmul _ _ M s m

open scoped ChangeOfRings in
/-- The inverse of `extendScalarsObjIso` is the identity on pure tensors. -/
@[simp]
theorem extendScalarsObjIso_inv_tmul (M : ModuleCat.{u} R) (s : S) (m : M) :
    (extendScalarsObjIso M).inv (s ⊗ₜ[R] m) = s ⊗ₜ[R, algebraMap R S] m := by
  apply (ConcreteCategory.bijective_of_isIso (extendScalarsObjIso M).hom).injective
  rw [← ModuleCat.comp_apply, (extendScalarsObjIso M).inv_hom_id]
  exact (extendScalarsObjIso_hom_tmul M s m).symm

variable (R) (A B : Type u) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
  (M : ModuleCat.{u} A) (N : ModuleCat.{u} B)

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- **Cancelling both base changes to `A ⊗_R B`.** The tensor product over `A ⊗_R B` of the base
changes of an `A`-module `M` and a `B`-module `N` is, as a module over `R`, the tensor product of
`M` and `N` over `R`. -/
def extendScalarsCancelIso :
    (ModuleCat.restrictScalars (algebraMap R (A ⊗[R] B))).obj
        (MonoidalCategory.tensorObj
          ((ModuleCat.extendScalars (algebraMap A (A ⊗[R] B))).obj M)
          ((ModuleCat.extendScalars
            (Algebra.TensorProduct.includeRight.toRingHom : B →+* A ⊗[R] B)).obj N)) ≅
      MonoidalCategory.tensorObj
        ((ModuleCat.restrictScalars (algebraMap R A)).obj M)
        ((ModuleCat.restrictScalars (algebraMap R B)).obj N) :=
  (ModuleCat.restrictScalars (algebraMap R (A ⊗[R] B))).mapIso
      (MonoidalCategory.tensorIso (extendScalarsObjIso M) (extendScalarsObjIso N)) ≪≫ by
  let : Module R (M : Type u) := Module.compHom _ (algebraMap R A)
  let : IsScalarTower R A (M : Type u) := IsScalarTower.of_compHom R A _
  let : Module R (N : Type u) := Module.compHom _ (algebraMap R B)
  let : IsScalarTower R B (N : Type u) := IsScalarTower.of_compHom R B _
  exact LinearEquiv.toModuleIso <| @AddEquiv.toLinearEquiv R
    (((A ⊗[R] B) ⊗[A] (M : Type u)) ⊗[A ⊗[R] B] ((A ⊗[R] B) ⊗[B] (N : Type u)))
    ((M : Type u) ⊗[R] (N : Type u)) _ _ _
    (Module.compHom _ (algebraMap R (A ⊗[R] B))) _
    (cancelBaseChange R A B (M : Type u) (N : Type u)).toAddEquiv
    (fun r x => (congrArg ⇑(cancelBaseChange R A B (M : Type u) (N : Type u))
        (algebraMap_smul (A ⊗[R] B) r x)).trans
      ((cancelBaseChange R A B (M : Type u) (N : Type u)).map_smul r x))

end ModuleCatVersion

end Stacks.TensorProductPushout

end
