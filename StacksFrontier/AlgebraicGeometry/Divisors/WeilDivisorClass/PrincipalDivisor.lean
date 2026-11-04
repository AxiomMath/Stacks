module

public import StacksFrontier.AlgebraicGeometry.Chow.RationalFunctions.FunctionField
public import StacksFrontier.AlgebraicGeometry.Chow.Vocabulary.PrincipalCycle
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.GenericPoint

/-!
# The principal Weil divisor of a rational function

Let `X` be a locally Noetherian integral scheme and let `f` be an invertible rational function
on `X`. The principal Weil divisor of `f` is `div(f) = ∑_Z ord_Z(f) [Z]`, the sum over prime
divisors `Z` of the order of vanishing of `f` at the generic point of `Z`. The collection of
prime divisors contributing to it is locally finite, so `div(f)` is a Weil divisor, and `div` is
additive in `f`.

Rational functions are taken in the sense of `Stacks.Chow.rationalFunctions`, the ring `R(X)`
of rational maps from `X` to the affine line, and are identified with the function field
`𝒪_{X, η}` by the canonical ring isomorphism `Stacks.Chow.rationalFunctionsEquivFunctionField`.

## Main definitions

* `AlgebraicGeometry.principalDivisor`: `div(f) ∈ Div(X)`.

## Main results

* `AlgebraicGeometry.ord_mem_weilDivisor`: the orders of vanishing of a function field element
  are the coefficients of a Weil divisor.
* `AlgebraicGeometry.principalDivisor_apply`: the coefficient of `div(f)` at a prime divisor
  is the order of vanishing of `f` at its generic point.
* `AlgebraicGeometry.principalDivisor_mul`: `div(fg) = div(f) + div(g)`, together with
  `AlgebraicGeometry.principalDivisor_one` and `AlgebraicGeometry.principalDivisor_inv`.

## References

* [Stacks Project, Tag 0BE3](https://stacks.math.columbia.edu/tag/0BE3)
* [Stacks Project, Tag 02RL](https://stacks.math.columbia.edu/tag/02RL)
* [Stacks Project, Tag 02RP](https://stacks.math.columbia.edu/tag/02RP)
-/

@[expose] public noncomputable section

open TopologicalSpace

universe u

namespace AlgebraicGeometry

variable (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]

/-- The prime divisors along which an element of the function field has nonzero order form a
locally finite collection, so its orders of vanishing are the coefficients of a Weil divisor. -/
theorem ord_mem_weilDivisor (g : X.functionField) :
    (fun Z : PrimeDivisor X => X.ord g Z.genericPoint) ∈ WeilDivisor X := by
  refine mem_weilDivisor_of_forall_exists_open fun x => ?_
  obtain ⟨V, hV, hfin⟩ := Stacks.Chow.locallyFiniteSupport_ord X g x
  refine ⟨interior V, isOpen_interior, mem_interior_iff_mem_nhds.mpr hV, ?_⟩
  refine Set.Finite.of_finite_image (f := PrimeDivisor.genericPoint)
    (hfin.subset ?_) PrimeDivisor.genericPoint_injective.injOn
  rintro - ⟨Z, ⟨hZV, hZne⟩, rfl⟩
  exact ⟨interior_subset hZV, hZne⟩

/-- The principal Weil divisor `div(f) = ∑_Z ord_Z(f) [Z]` of an invertible rational function
`f`: the sum over the prime divisors `Z` of `X` of the order of vanishing of `f`, read in the
function field, at the generic point of `Z`. -/
def principalDivisor (f : (Stacks.Chow.rationalFunctions X)ˣ) : WeilDivisor X :=
  ⟨fun Z => X.ord ((Stacks.Chow.rationalFunctionsEquivFunctionField X).val f) Z.genericPoint,
    ord_mem_weilDivisor X _⟩

/-- The coefficient of a principal divisor at a prime divisor is the order of vanishing of the
rational function at its generic point. -/
@[simp]
theorem principalDivisor_apply (f : (Stacks.Chow.rationalFunctions X)ˣ) (Z : PrimeDivisor X) :
    (principalDivisor X f).val Z =
      X.ord ((Stacks.Chow.rationalFunctionsEquivFunctionField X).val f) Z.genericPoint :=
  rfl

omit [IsLocallyNoetherian X] in
/-- An invertible rational function is nonzero in the function field. -/
private theorem equivFunctionField_unit_ne_zero (f : (Stacks.Chow.rationalFunctions X)ˣ) :
    (Stacks.Chow.rationalFunctionsEquivFunctionField X).val f ≠ 0 :=
  (f.isUnit.map (Stacks.Chow.rationalFunctionsEquivFunctionField X).val.toRingHom).ne_zero

/-- The principal divisor of a product of invertible rational functions is the
sum of their principal divisors. -/
theorem principalDivisor_mul (f g : (Stacks.Chow.rationalFunctions X)ˣ) :
    principalDivisor X (f * g) = principalDivisor X f + principalDivisor X g := by
  refine Subtype.ext (funext fun Z => ?_)
  simp only [principalDivisor_apply, AddSubgroup.coe_add, Pi.add_apply, Units.val_mul, map_mul]
  exact X.ord_mul (equivFunctionField_unit_ne_zero X f) (equivFunctionField_unit_ne_zero X g)

/-- The principal divisor of the constant function `1` is zero. -/
@[simp]
theorem principalDivisor_one : principalDivisor X 1 = 0 := by
  simpa using principalDivisor_mul X 1 1

/-- The principal divisor of the inverse of an invertible rational function is the negative of
its principal divisor. -/
@[simp]
theorem principalDivisor_inv (f : (Stacks.Chow.rationalFunctions X)ˣ) :
    principalDivisor X f⁻¹ = -principalDivisor X f := by
  rw [eq_neg_iff_add_eq_zero, add_comm, ← principalDivisor_mul, mul_inv_cancel,
    principalDivisor_one]

end AlgebraicGeometry

end
