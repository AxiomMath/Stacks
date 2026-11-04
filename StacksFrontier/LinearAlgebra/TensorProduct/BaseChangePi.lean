module

public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# A tensor product with a finite product of modules over base-changed rings

Let `R` be a commutative ring, `G` an `R`-module and `(A i)` a finite family of commutative
`R`-algebras. For each `i` let `F i` be an `A i`-module and let `L i` be an `A i`-module
identified with the base change `A i ⊗_R G` by an `A i`-linear equivalence `e i`. Then

`G ⊗_R (∏ᵢ F i) ≅ ∏ᵢ L i ⊗_{A i} F i`,

the isomorphism sending `g ⊗ (sᵢ)ᵢ` to `(e i (1 ⊗ g) ⊗ sᵢ)ᵢ`.

A tensor product distributes over a finite product, and on each factor the base change cancels
against the tensor product over the base-changed ring: `(A ⊗_R G) ⊗_A F = G ⊗_R F`
(`AlgebraicGeometry.Space.tensorBaseChangeCancel`, written out here through
`TensorProduct.AlgebraTensorModule.cancelBaseChange` so as not to import the geometry).

This is the identity the stalkwise proof of the projection formula for a finite morphism comes
down to (Stacks 0DK4): `R` and `G` are the stalks of the sheaf of rings and of the module on the
target at a geometric point, the index set is the set of lifts of that point, `A i` and `F i`
are the stalks of the sheaf of rings and of the module on the source at the lifts, and `L i` is
the stalk of the pullback of `G` at a lift.

## Main definitions

* `TensorProduct.tensorPiBaseChangeEquiv`: the `R`-linear equivalence
  `G ⊗_R (∏ᵢ F i) ≃ ∏ᵢ L i ⊗_{A i} F i`.

## Main results

* `TensorProduct.tensorPiBaseChangeEquiv_tmul`: the equivalence on pure tensors.
-/

@[expose] public noncomputable section

open TensorProduct

universe u v w t s

namespace TensorProduct

section Pi

variable (R : Type u) [CommRing R] {ι : Type v} [Fintype ι] [DecidableEq ι]
    (G : Type w) [AddCommGroup G] [Module R G]
    (A : ι → Type t) [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    (L : ι → Type s) [∀ i, AddCommGroup (L i)] [∀ i, Module (A i) (L i)]
    [∀ i, Module R (L i)] [∀ i, IsScalarTower R (A i) (L i)]
    (F : ι → Type s) [∀ i, AddCommGroup (F i)] [∀ i, Module (A i) (F i)]
    [∀ i, Module R (F i)] [∀ i, IsScalarTower R (A i) (F i)]
    (e : ∀ i, (A i ⊗[R] G) ≃ₗ[A i] L i)

/-- **A tensor product with a finite product of modules over base-changed rings.** If each
`L i` is the base change `A i ⊗_R G` by `e i`, then `G ⊗_R (∏ᵢ F i)` is `∏ᵢ L i ⊗_{A i} F i`,
by `g ⊗ (sᵢ)ᵢ ↦ (e i (1 ⊗ g) ⊗ sᵢ)ᵢ`. -/
def tensorPiBaseChangeEquiv : (G ⊗[R] ∀ i, F i) ≃ₗ[R] ∀ i, L i ⊗[A i] F i :=
  (TensorProduct.piRight R R G F).trans
    (LinearEquiv.piCongrRight fun i =>
      ((TensorProduct.comm R (F i) G).symm.trans
        (((AlgebraTensorModule.cancelBaseChange R (A i) (A i) (F i) G).symm.restrictScalars R).trans
          ((TensorProduct.comm (A i) (A i ⊗[R] G) (F i)).symm.restrictScalars R))).trans
        ((TensorProduct.AlgebraTensorModule.congr (e i)
          (LinearEquiv.refl (A i) (F i))).restrictScalars R))

/-- `tensorPiBaseChangeEquiv` on a pure tensor: the `i`th component of the image of `g ⊗ f` is
`e i (1 ⊗ g) ⊗ f i`. -/
@[simp]
theorem tensorPiBaseChangeEquiv_tmul (g : G) (f : ∀ i, F i) (i : ι) :
    tensorPiBaseChangeEquiv R G A L F e (g ⊗ₜ f) i = e i ((1 : A i) ⊗ₜ g) ⊗ₜ f i := by
  simp [tensorPiBaseChangeEquiv, TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul]

end Pi

end TensorProduct

end
