module

public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.Algebra.Module.Defs

/-!
# The `(-1)^n` action on a module

`Int.negOnePow n` acts on a module over a commutative ring `R` as `(-1 : R) ^ n.natAbs`.

## Main results

* `negOnePow_smul_eq`: the action of `(Int.negOnePow n : ℤ)` on a module agrees with that of
  `(-1 : R) ^ n.natAbs`.
* `units_negOnePow_smul_eq`: the same identity for the action of the unit `Int.negOnePow n : ℤˣ`.
-/

@[expose] public section

universe u

/-- The `Int.negOnePow n` action on a module agrees with multiplication by
`(-1 : R) ^ n.natAbs`. -/
public theorem negOnePow_smul_eq {R : Type u} [CommRing R] {M : Type*} [AddCommGroup M]
    [Module R M] (n : ℤ) (x : M) : ((n.negOnePow : ℤ)) • x = ((-1 : R) ^ n.natAbs) • x := by
  rw [← Int.cast_smul_eq_zsmul (R := R), Int.coe_negOnePow]

/-- The action of the unit `Int.negOnePow n : ℤˣ` on a module agrees with multiplication by
`(-1 : R) ^ n.natAbs`. -/
public theorem units_negOnePow_smul_eq {R : Type u} [CommRing R] {M : Type*} [AddCommGroup M]
    [Module R M] (n : ℤ) (x : M) : n.negOnePow • x = ((-1 : R) ^ n.natAbs) • x := by
  show ((n.negOnePow : ℤ)) • x = _
  exact negOnePow_smul_eq n x

end
