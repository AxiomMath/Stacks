module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex

/-!
# Cochains between complexes of `B`-modules as a scalar tower over a base ring

Let `B` be an algebra over a commutative ring `A`. The scoped instances of `ModuleCat.Algebra`
make `ModuleCat B` an `A`-linear category, so for cochain complexes `P`, `F` of `B`-modules the
`B`-module `Cochain P F n` of degree-`n` cochains also carries an `A`-module structure, obtained
by restricting scalars degreewise. This file records that the two actions form a scalar tower,
which is what lets a cochain be moved between the two base rings inside a base-change argument.

The statement needs `ModuleCat.Algebra` to be open as a scope, so it is not an instance: use
`attribute [local instance] CochainComplex.HomComplex.Cochain.isScalarTower` where it is needed.

## Main results

* `CochainComplex.HomComplex.Cochain.isScalarTower`: `IsScalarTower A B (Cochain P F n)`.
-/

@[expose] public section

open CategoryTheory

open scoped ModuleCat.Algebra

namespace CochainComplex.HomComplex

/-- Cochains between two complexes of `B`-modules form a scalar tower over a base ring `A` of
`B`: the `A`-action is the `B`-action restricted along `algebraMap A B`. -/
public theorem Cochain.isScalarTower
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (P F : CochainComplex (ModuleCat B) ℤ) (n : ℤ) :
    IsScalarTower A B (CochainComplex.HomComplex.Cochain P F n) where
  smul_assoc a b z := Cochain.ext _ _ fun p q hpq ↦
    ModuleCat.hom_ext (LinearMap.ext fun x ↦ smul_assoc a b ((z.v p q hpq).hom x))

end CochainComplex.HomComplex

end
