module

public import Mathlib.Algebra.Module.RingHom
public import Mathlib.Algebra.Ring.Opposite

/-!
# The right action of a commutative semiring on one of its modules

A module `M` over a commutative semiring `R` is also a module over `Rᵐᵒᵖ`, with `op r` acting
as `r` does, and the two actions agree, `IsCentralScalar R M`. These are the data that
Mathlib's trivial square-zero extension `TrivSqZeroExt R M` needs to be a commutative ring.

Mathlib deliberately gives no instance `Module Rᵐᵒᵖ M` for a general module: on `M = R` it
would compete with `Semiring.toOppositeModule`, the action by right multiplication. So the
action is a named definition here, `Module.oppositeOfCommSemiring`, to be installed as a
local instance at specific carriers.

## Main definitions

* `Module.oppositeOfCommSemiring` — the action of `Rᵐᵒᵖ` on `M` through `MulOpposite.unop`.
* `Module.isCentralScalar_oppositeOfCommSemiring` — that action agrees with the action of `R`.

## Implementation notes

Use this shared term for local instances of this action. Different presentations through
ring homomorphisms can agree at default transparency while failing to agree at the
transparency used by instance search and `rw`/`simp`. Sharing this named construction
keeps lemmas about `TrivSqZeroExt R M` compatible across those instances.
-/

@[expose] public section

namespace Module

variable (R M : Type*) [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- The right action of a commutative semiring on one of its modules: `op r • m = r • m`. Not
a global instance: on `M = R` it would compete with `Semiring.toOppositeModule`. -/
@[instance_reducible] def oppositeOfCommSemiring : Module Rᵐᵒᵖ M :=
  Module.compHom M
    { toFun := MulOpposite.unop
      map_one' := rfl
      map_mul' := fun x y => mul_comm y.unop x.unop
      map_zero' := rfl
      map_add' := fun _ _ => rfl }

attribute [local instance] oppositeOfCommSemiring in
/-- Over a commutative semiring the actions of `R` and of `Rᵐᵒᵖ` on a module agree. -/
theorem isCentralScalar_oppositeOfCommSemiring : IsCentralScalar R M :=
  ⟨fun _ _ => rfl⟩

end Module

end
