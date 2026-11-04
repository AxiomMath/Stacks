module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.PrincipalDivisor

/-!
# The Weil divisor class group

Let `X` be a locally Noetherian integral scheme. The principal Weil divisors — the divisors
`div(f)` of invertible rational functions — form a subgroup of the group `Div(X)` of Weil
divisors, and the *Weil divisor class group* `Cl(X)` is the quotient.

## Main definitions

* `AlgebraicGeometry.principalWeilDivisors` — the subgroup of principal Weil divisors.
* `AlgebraicGeometry.weilDivisorClassGroup` — `Cl(X)`.

## Main results

* `AlgebraicGeometry.mem_principalWeilDivisors_iff` — a Weil divisor is principal exactly when
  it is the divisor of an invertible rational function.
* `AlgebraicGeometry.mk_eq_zero_iff` — a Weil divisor has zero class exactly when it is
  principal.

## References

* [Stacks Project, Tag 0BE4](https://stacks.math.columbia.edu/tag/0BE4)
-/

@[expose] public noncomputable section

universe u

namespace AlgebraicGeometry

variable (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]

/-- The subgroup of principal Weil divisors: those of the form `div(f)` for an invertible
rational function `f`. -/
def principalWeilDivisors : AddSubgroup (WeilDivisor X) where
  carrier := Set.range (principalDivisor X)
  zero_mem' := ⟨1, principalDivisor_one X⟩
  add_mem' := by
    rintro _ _ ⟨f, rfl⟩ ⟨g, rfl⟩
    exact ⟨f * g, principalDivisor_mul X f g⟩
  neg_mem' := by
    rintro _ ⟨f, rfl⟩
    exact ⟨f⁻¹, principalDivisor_inv X f⟩

/-- A Weil divisor is principal exactly when it is the divisor of an invertible rational
function. -/
@[simp]
theorem mem_principalWeilDivisors_iff (D : WeilDivisor X) :
    D ∈ principalWeilDivisors X ↔
      ∃ f : (Stacks.Chow.rationalFunctions X)ˣ, principalDivisor X f = D :=
  Iff.rfl

/-- The Weil divisor class group `Cl(X)` of a locally Noetherian integral
scheme: the group of Weil divisors modulo the subgroup of principal Weil divisors. -/
@[stacks 0BE4]
abbrev weilDivisorClassGroup : Type u :=
  WeilDivisor X ⧸ principalWeilDivisors X

/-- A Weil divisor has zero class in `Cl(X)` exactly when it is the divisor of an invertible
rational function. -/
@[simp]
theorem mk_eq_zero_iff (D : WeilDivisor X) :
    (D : weilDivisorClassGroup X) = 0 ↔
      ∃ f : (Stacks.Chow.rationalFunctions X)ˣ, principalDivisor X f = D := by
  simpa only [mem_principalWeilDivisors_iff] using
    QuotientAddGroup.eq_zero_iff (N := principalWeilDivisors X) D

end AlgebraicGeometry

end
