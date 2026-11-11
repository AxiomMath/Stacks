module

public import Mathlib.CategoryTheory.DifferentialObject
public import StacksFrontier.CategoryTheory.DifferentialObject

/-!
# Stacks differential objects as Mathlib differential objects for the trivial shift

Stacks defines a differential object as a pair `(A, d)` with `d : A ⟶ A` and `d ≫ d = 0`
(`StacksDifferentialObject`). Mathlib's `CategoryTheory.DifferentialObject S C` instead takes
`d : A ⟶ A⟦1⟧` for a shift on `C`. For the trivial shift, where every shift functor is the
identity, the two notions agree.

## Main definitions

* `CategoryTheory.trivialShift C A`: the shift on `C` by `A` with every shift functor the identity.
* `StacksDifferentialObject.equivDifferentialObjectTrivialShift`: the equivalence between
  `StacksDifferentialObject C` and `DifferentialObject S C` for the trivial shift.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory

/-- The trivial shift on `C` by an additive monoid `A`: every shift functor is the identity and
every structure isomorphism is the identity. -/
@[implicit_reducible]
def trivialShift (C : Type*) [Category C] (A : Type*) [AddMonoid A] : HasShift C A :=
  hasShiftMk C A
    { F := fun _ ↦ 𝟭 C
      zero := Iso.refl _
      add := fun _ _ ↦ Iso.refl _ }

end CategoryTheory

namespace StacksDifferentialObject

variable (S : Type*) [AddMonoidWithOne S] (C : Type*) [Category C] [Limits.HasZeroMorphisms C]

/-- Stacks differential objects `(A, d)`, `d : A ⟶ A`, `d ≫ d = 0`, are the same as Mathlib's
differential objects for the trivial shift on `C`. -/
def equivDifferentialObjectTrivialShift :
    letI := trivialShift C S
    StacksDifferentialObject C ≌ DifferentialObject S C :=
  letI := trivialShift C S
  { functor :=
      { obj := fun M ↦ { obj := M.X, d := M.d, d_squared := M.d_sq }
        map := fun φ ↦ { f := φ.f, comm := φ.comm.symm } }
    inverse :=
      { obj := fun M ↦ { X := M.obj, d := M.d, d_sq := M.d_squared }
        map := fun φ ↦ { f := φ.f, comm := φ.comm.symm } }
    unitIso := Iso.refl _
    counitIso := Iso.refl _ }

end StacksDifferentialObject
