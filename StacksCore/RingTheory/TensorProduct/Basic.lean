module

public import Mathlib.RingTheory.TensorProduct.Basic
import StacksCore.Tactic.StacksAttribute

/-! # The base change / restriction of scalars Hom-set formula

Stacks tag 05DQ, second half: the adjunction between base change and restriction of scalars,
written out on Hom-sets as `Hom_R(M, N_R) = Hom_S(M ⊗_R S, N)`.

`LinearMap.liftBaseChangeEquiv` gives more than the tag's equality — it is an `S`-linear
equivalence `(M →ₗ[R] N) ≃ₗ[S] (S ⊗[R] M →ₗ[S] N)`, so the bijection is natural in the
structure the tag leaves implicit. As in the categorical half, Mathlib's base change is
`S ⊗_R M` where the tag writes `M ⊗_R S`.

The functor-level statement, that these are adjoint, is `ModuleCat.extendRestrictScalarsAdj`,
tagged in `StacksCore.Algebra.Category.ModuleCat.ChangeOfRings`.
-/

@[expose] public section

add_to_stacks 05DQ "`Hom_R(M, N_R) = Hom_S(S ⊗_R M, N)`, as an `S`-linear equivalence. The tag
  writes the tensor product in the other order." LinearMap.liftBaseChangeEquiv
