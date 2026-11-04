module

public import StacksFrontier.LinearAlgebra.TensorProduct.BaseChangeCancellation

/-!
# Pure tensors under the cancellation of a double base change

For commutative `R`-algebras `A` and `B`, an `A`-module `M` and a `B`-module `N`, the tensor
product over `A ⊗_R B` of the base changes of `M` and of `N` is, as a module over `R`, the tensor
product `M ⊗_R N`. This file evaluates that identification, and its inverse, on pure tensors:
`(1 ⊗ m) ⊗ (1 ⊗ n) ↦ m ⊗ n`.

## Main results

* `Stacks.TensorProductPushout.extendScalarsObjIso_tensor_hom_one_tmul`: the comparison between
  `CategoryTheory.ModuleCat.extendScalars` and the base change formed from an algebra structure,
  tensored in both variables, carries a pure tensor of pure tensors to the corresponding pure
  tensor of pure tensors.
* `Stacks.TensorProductPushout.extendScalarsCancelIso_hom_one_tmul` and
  `Stacks.TensorProductPushout.extendScalarsCancelIso_inv_tmul`: the cancellation and its inverse
  match `(1 ⊗ m) ⊗ (1 ⊗ n)` with `m ⊗ n`.
* `Stacks.TensorProductPushout.linearEquiv_transport_apply`: a linear equivalence transported
  along an equality of the module structures on its source has the same underlying function.

## Implementation notes

The two module structures over `R` on `((A ⊗_R B) ⊗_A M) ⊗_{A ⊗_R B} ((A ⊗_R B) ⊗_B N)` — the one
`CategoryTheory.ModuleCat.restrictScalars` supplies through `Module.compHom`, and the one the
tensor products carry — are equal but not definitionally equal. They are compared inside a proof
by `Stacks.TensorProductPushout.extendScalarsCancelIso`, so the value of that isomorphism on a
pure tensor is a composite of the values of its two factors, and the pure-tensor rules above are
immediate from the rule for `Stacks.TensorProductPushout.cancelBaseChange`.

`linearEquiv_transport_apply` substitutes such an equality of module structures instead, which is
only possible with both structures quantified over. It is not needed for the rules above.
-/

@[expose] public noncomputable section

open CategoryTheory TensorProduct

namespace Stacks.TensorProductPushout

universe u

/-- A linear equivalence transported along an equality of the module structures on its source has
the same underlying function. -/
theorem linearEquiv_transport_apply {R : Type u} [CommRing R] {T W : Type u} [AddCommGroup T]
    [AddCommGroup W] [Module R W] {i₁ i₂ : Module R T} (h : i₁ = i₂)
    (e : @LinearEquiv R R _ _ (RingHom.id R) (RingHom.id R) _ _ T W _ _ i₂ _) (x : T) :
    (Eq.mpr (congrArg
        (fun j => @LinearEquiv R R _ _ (RingHom.id R) (RingHom.id R) _ _ T W _ _ j _) h) e) x
      = e x := by
  subst h
  rfl

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
  (M : ModuleCat.{u} A) (N : ModuleCat.{u} B)

attribute [local instance] Algebra.TensorProduct.rightAlgebra

open scoped ChangeOfRings in
/-- The comparison between `CategoryTheory.ModuleCat.extendScalars` and the base change formed
from an algebra structure, tensored in both variables, carries `(1 ⊗ m) ⊗ (1 ⊗ n)` to
`(1 ⊗ m) ⊗ (1 ⊗ n)`. This is the first factor of
`Stacks.TensorProductPushout.extendScalarsCancelIso` on pure tensors. -/
theorem extendScalarsObjIso_tensor_hom_one_tmul (m : M) (n : N) :
    ((ModuleCat.restrictScalars (algebraMap R (A ⊗[R] B))).mapIso
        (MonoidalCategory.tensorIso (extendScalarsObjIso (S := A ⊗[R] B) M)
          (extendScalarsObjIso (S := A ⊗[R] B) N))).hom
      (((1 : A ⊗[R] B) ⊗ₜ[A, algebraMap A (A ⊗[R] B)] m) ⊗ₜ[A ⊗[R] B]
        ((1 : A ⊗[R] B) ⊗ₜ[B, (algebraMap B (A ⊗[R] B))] n))
      = ((1 : A ⊗[R] B) ⊗ₜ[A] m) ⊗ₜ[A ⊗[R] B] ((1 : A ⊗[R] B) ⊗ₜ[B] n) :=
  congrArg₂ (fun (x : (A ⊗[R] B) ⊗[A] (M : Type u)) (y : (A ⊗[R] B) ⊗[B] (N : Type u)) =>
      x ⊗ₜ[A ⊗[R] B] y)
    (extendScalarsObjIso_hom_tmul (S := A ⊗[R] B) M 1 m)
    (extendScalarsObjIso_hom_tmul (S := A ⊗[R] B) N 1 n)

open scoped ChangeOfRings in
/-- **The cancellation of a double base change on pure tensors.** The isomorphism
`((A ⊗_R B) ⊗_A M) ⊗_{A ⊗_R B} ((A ⊗_R B) ⊗_B N) ≅ M ⊗_R N` of modules over `R` carries
`(1 ⊗ m) ⊗ (1 ⊗ n)` to `m ⊗ n`. -/
theorem extendScalarsCancelIso_hom_one_tmul (m : M) (n : N) :
    (extendScalarsCancelIso R A B M N).hom
        (((1 : A ⊗[R] B) ⊗ₜ[A, algebraMap A (A ⊗[R] B)] m) ⊗ₜ[A ⊗[R] B]
          ((1 : A ⊗[R] B) ⊗ₜ[B, algebraMap B (A ⊗[R] B)] n))
      = (m ⊗ₜ[R] n :
          ↑(MonoidalCategory.tensorObj ((ModuleCat.restrictScalars (algebraMap R A)).obj M)
            ((ModuleCat.restrictScalars (algebraMap R B)).obj N))) := by
  let : Module R (M : Type u) := Module.compHom _ (algebraMap R A)
  let : IsScalarTower R A (M : Type u) := IsScalarTower.of_compHom R A _
  let : Module R (N : Type u) := Module.compHom _ (algebraMap R B)
  let : IsScalarTower R B (N : Type u) := IsScalarTower.of_compHom R B _
  exact (congrArg ⇑(cancelBaseChange R A B (M : Type u) (N : Type u))
      (extendScalarsObjIso_tensor_hom_one_tmul R A B M N m n)).trans
    (cancelBaseChange_one_tmul R A B m n)

open scoped ChangeOfRings in
/-- The inverse of the cancellation of a double base change carries a pure tensor `m ⊗ n` of
`M ⊗_R N` to `(1 ⊗ m) ⊗ (1 ⊗ n)`. -/
theorem extendScalarsCancelIso_inv_tmul (m : M) (n : N) :
    (extendScalarsCancelIso R A B M N).inv
        (m ⊗ₜ[R] n :
          ↑(MonoidalCategory.tensorObj ((ModuleCat.restrictScalars (algebraMap R A)).obj M)
            ((ModuleCat.restrictScalars (algebraMap R B)).obj N)))
      = (((1 : A ⊗[R] B) ⊗ₜ[A, algebraMap A (A ⊗[R] B)] m) ⊗ₜ[A ⊗[R] B]
            ((1 : A ⊗[R] B) ⊗ₜ[B, algebraMap B (A ⊗[R] B)] n) :
          ↑((ModuleCat.restrictScalars (algebraMap R (A ⊗[R] B))).obj
            (MonoidalCategory.tensorObj
              ((ModuleCat.extendScalars (algebraMap A (A ⊗[R] B))).obj M)
              ((ModuleCat.extendScalars (algebraMap B (A ⊗[R] B))).obj N)))) :=
  (ConcreteCategory.bijective_of_isIso (extendScalarsCancelIso R A B M N).hom).injective
    ((Iso.inv_hom_id_apply (extendScalarsCancelIso R A B M N) _).trans
      (extendScalarsCancelIso_hom_one_tmul R A B M N m n).symm)

end Stacks.TensorProductPushout

end
