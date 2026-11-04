module

public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.RingTheory.TensorProduct.Maps

@[expose] public section

universe u v w x

/-!
# Finiteness of a tensor product over a subring

For an `R`-algebra `A`, a finite `A`-module `M` and a finite `R`-module `N`, the tensor
product `M ⊗[R] N` is finite over `A`. This is `Module.Finite.tensorProduct` read through
the base-change cancellation `M ⊗[A] (A ⊗[R] N) ≃ M ⊗[R] N`.
-/

open scoped TensorProduct

namespace Module.Finite

/-- A tensor product `M ⊗[R] N` of a finite `A`-module with a finite `R`-module is finite
over `A`, for `A` an `R`-algebra acting on `M` compatibly with `R`. -/
public theorem tensorProduct_right (R : Type u) [CommRing R] (A : Type v) [CommRing A]
    [Algebra R A] (M : Type w) [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
    [Module.Finite A M] (N : Type x) [AddCommGroup N] [Module R N] [Module.Finite R N] :
    Module.Finite A (M ⊗[R] N) :=
  Module.Finite.equiv (TensorProduct.AlgebraTensorModule.cancelBaseChange R A A M N)

end Module.Finite
