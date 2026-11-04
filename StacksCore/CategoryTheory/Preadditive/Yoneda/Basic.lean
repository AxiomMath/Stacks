module

public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

/-!
# The preadditive coyoneda functor of the opposite category

`PreadditiveCoyoneda.objOpOp` identifies the covariant preadditive hom-functor of `Cᵒᵖ` at `op X`
with the contravariant preadditive hom-functor of `C` at `X`, via `Quiver.Hom.unop` on each
hom-group. This is the preadditive analogue of `Coyoneda.objOpOp`.
-/

@[expose] public section

open Opposite

namespace CategoryTheory.PreadditiveCoyoneda

variable {C : Type*} [Category* C] [Preadditive C]

/-- Taking the `unop` of morphisms is an additive natural isomorphism: the covariant preadditive
hom-functor of `Cᵒᵖ` at `op X` agrees with the contravariant preadditive hom-functor of `C` at
`X`. This is the preadditive analogue of `Coyoneda.objOpOp`. -/
@[simps! hom_app inv_app]
def objOpOp (X : C) : preadditiveCoyoneda.obj (op (op X)) ≅ preadditiveYoneda.obj X :=
  NatIso.ofComponents
    (fun Y ↦ AddEquiv.toAddCommGrpIso
      { toFun := fun φ ↦ φ.unop
        invFun := fun φ ↦ φ.op
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun φ ψ ↦ unop_add _ φ ψ })
    (fun u ↦ by ext φ; rfl)

end CategoryTheory.PreadditiveCoyoneda
