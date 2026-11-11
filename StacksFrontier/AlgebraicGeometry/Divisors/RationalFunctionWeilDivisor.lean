module

public import StacksFrontier.AlgebraicGeometry.Divisors.CartierWeilDivisor
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.PrincipalDivisor

/-!
# The Weil divisor of a rational function

Let `X` be a Noetherian integral scheme. For a prime divisor `Z` of `X` with generic point `ξ`
the local ring `𝒪_{X, Z} = 𝒪_{X, ξ}` is a subring of the function field `K(X)`. The *Weil divisor
of a nonzero rational function* `f ∈ K(X)^*` is the formal sum `Σ v_Z(f) [Z]` over the prime
divisors of `X`, where

* `v_Z(f) = 0` when `f ∈ 𝒪_{X, Z}^*`,
* `v_Z(f) = length (𝒪_{X, Z} / (f))` when `f ∈ 𝒪_{X, Z}`, and
* `v_Z(f) = length (𝒪_{X, Z} / (a)) - length (𝒪_{X, Z} / (b))` when `f = a / b` with
  `a, b ∈ 𝒪_{X, Z}`.

The three clauses are read off one integer: the order of vanishing of `f` at `ξ`, which is
Mathlib's `AlgebraicGeometry.Scheme.ord`. The family of orders is finitely supported, so the sum
is a Weil divisor.

## Main definitions

* `AlgebraicGeometry.rationalFunctionWeilDivisor`: the Weil divisor `Σ v_Z(f) [Z]` of a nonzero
  rational function.

## Main results

* `AlgebraicGeometry.PrimeDivisor.algebraMap_stalk_functionField_injective`: the local ring
  `𝒪_{X, Z}` is a subring of the function field.
* `AlgebraicGeometry.rationalFunctionWeilDivisor_apply_of_eq_algebraMap_unit`,
  `AlgebraicGeometry.rationalFunctionWeilDivisor_apply_of_eq_algebraMap` and
  `AlgebraicGeometry.rationalFunctionWeilDivisor_apply_of_eq_div`: the three clauses defining
  `v_Z(f)`.
* `AlgebraicGeometry.principalDivisor_eq_rationalFunctionWeilDivisor`: the construction agrees
  with the principal Weil divisor `AlgebraicGeometry.principalDivisor` of Tag 0BE3, read through
  the identification of rational functions with the function field.

## Implementation notes

The length of `𝒪_{X, Z} / (a)` is Mathlib's `Module.length`, valued in `ℕ∞`. For a nonzero `a`
in the one-dimensional Noetherian local domain `𝒪_{X, Z}` it is finite, and the integer
coefficient is its `ENat.toNat`, the convention shared with the Weil divisors of effective
Cartier divisors and of Cartier divisors in this library. The bridge from the order of vanishing
to the length is `AlgebraicGeometry.ord_algebraMap_stalk`, which is Tag 02MD at a point; the
additivity of lengths that makes the third clause independent of the fraction chosen (Tag 02F5,
remark (2)) enters through the multiplicativity `AlgebraicGeometry.Scheme.ord_mul`.

## References

* [Stacks Project, Tag 02AR](https://stacks.math.columbia.edu/tag/02AR)
* [Stacks Project, Tag 02MD](https://stacks.math.columbia.edu/tag/02MD)
* [Stacks Project, Tag 0BE3](https://stacks.math.columbia.edu/tag/0BE3)
-/

@[expose] public noncomputable section

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- **Stacks 02AR part (2), the local ring as a subring.** On an integral scheme the local ring
`𝒪_{X, Z}` at the generic point of a prime divisor `Z` embeds into the function field `K(X)`. -/
@[stacks 02AR "prime_divisor"]
theorem PrimeDivisor.algebraMap_stalk_functionField_injective [IsIntegral X]
    (Z : PrimeDivisor X) :
    Function.Injective
      (algebraMap (X.presheaf.stalk Z.genericPoint) X.functionField) :=
  IsFractionRing.injective _ _

variable (X) in
/-- **Stacks 02AR part (3).** The Weil divisor `Σ v_Z(f) [Z]` of a nonzero rational function `f`
on a Noetherian integral scheme: the coefficient at a prime divisor `Z` is the order of vanishing
of `f` at the generic point of `Z`. -/
@[stacks 02AR "rational_function_weil_divisor"]
def rationalFunctionWeilDivisor [IsNoetherian X] [IsIntegral X] (f : X.functionFieldˣ) :
    WeilDivisor X :=
  ⟨fun Z => X.ord (f : X.functionField) Z.genericPoint, ord_mem_weilDivisor X _⟩

/-- **Stacks 02AR part (3).** The coefficient of the Weil divisor of a rational function at a
prime divisor `Z` is the order `v_Z(f)`. -/
@[stacks 02AR "rational_function_weil_divisor"]
theorem rationalFunctionWeilDivisor_apply [IsNoetherian X] [IsIntegral X]
    (f : X.functionFieldˣ) (Z : PrimeDivisor X) :
    (rationalFunctionWeilDivisor X f).1 Z = X.ord (f : X.functionField) Z.genericPoint :=
  rfl

/-- **Stacks 02AR part (3), clause (b).** If the rational function `f` lies in the local ring
`𝒪_{X, Z}`, its coefficient at `Z` is the length of `𝒪_{X, Z} / (f)`. -/
@[stacks 02AR "rational_function_weil_divisor"]
theorem rationalFunctionWeilDivisor_apply_of_eq_algebraMap [IsNoetherian X] [IsIntegral X]
    (f : X.functionFieldˣ) (Z : PrimeDivisor X) (a : X.presheaf.stalk Z.genericPoint)
    (hf : (f : X.functionField) = algebraMap _ X.functionField a) :
    (rationalFunctionWeilDivisor X f).1 Z =
      ((Module.length (X.presheaf.stalk Z.genericPoint)
        ((X.presheaf.stalk Z.genericPoint) ⧸ Ideal.span {a})).toNat : ℤ) := by
  have ha : a ≠ 0 := by
    rintro rfl
    exact f.ne_zero (by rw [hf, map_zero])
  rw [rationalFunctionWeilDivisor_apply, hf]
  exact ord_algebraMap_stalk Z.genericPoint Z.coheight_genericPoint_eq_one a ha

/-- **Stacks 02AR part (3), clause (a).** If the rational function `f` is a unit of the local
ring `𝒪_{X, Z}`, its coefficient at `Z` is zero. -/
@[stacks 02AR "rational_function_weil_divisor"]
theorem rationalFunctionWeilDivisor_apply_of_eq_algebraMap_unit [IsNoetherian X] [IsIntegral X]
    (f : X.functionFieldˣ) (Z : PrimeDivisor X) (u : (X.presheaf.stalk Z.genericPoint)ˣ)
    (hf : (f : X.functionField) =
      algebraMap _ X.functionField (u : X.presheaf.stalk Z.genericPoint)) :
    (rationalFunctionWeilDivisor X f).1 Z = 0 := by
  rw [rationalFunctionWeilDivisor_apply_of_eq_algebraMap f Z _ hf,
    Ideal.span_singleton_eq_top.mpr u.isUnit]
  have : Subsingleton ((X.presheaf.stalk Z.genericPoint) ⧸ (⊤ : Ideal _)) :=
    Ideal.Quotient.subsingleton_iff.mpr rfl
  simp [Module.length_eq_zero]

/-- **Stacks 02AR part (3), clause (c).** If the rational function is a fraction `f = a / b` of
two elements of the local ring `𝒪_{X, Z}`, its coefficient at `Z` is the difference of the
lengths of `𝒪_{X, Z} / (a)` and `𝒪_{X, Z} / (b)`. -/
@[stacks 02AR "rational_function_weil_divisor"]
theorem rationalFunctionWeilDivisor_apply_of_eq_div [IsNoetherian X] [IsIntegral X]
    (f : X.functionFieldˣ) (Z : PrimeDivisor X) (a b : X.presheaf.stalk Z.genericPoint)
    (hf : (f : X.functionField) =
      algebraMap _ X.functionField a / algebraMap _ X.functionField b) :
    (rationalFunctionWeilDivisor X f).1 Z =
      ((Module.length (X.presheaf.stalk Z.genericPoint)
        ((X.presheaf.stalk Z.genericPoint) ⧸ Ideal.span {a})).toNat : ℤ) -
      ((Module.length (X.presheaf.stalk Z.genericPoint)
        ((X.presheaf.stalk Z.genericPoint) ⧸ Ideal.span {b})).toNat : ℤ) := by
  have hb : algebraMap _ X.functionField b ≠ 0 := by
    intro h
    exact f.ne_zero (by rw [hf, h, div_zero])
  have hb' : b ≠ 0 := by
    rintro rfl
    exact hb (map_zero _)
  have ha : a ≠ 0 := by
    rintro rfl
    exact f.ne_zero (by rw [hf, map_zero, zero_div])
  have hmul : (f : X.functionField) * algebraMap _ X.functionField b =
      algebraMap _ X.functionField a := by
    rw [hf, div_mul_cancel₀ _ hb]
  have hord := congrArg (fun g => X.ord g Z.genericPoint) hmul
  rw [Scheme.ord_mul f.ne_zero hb,
    ord_algebraMap_stalk Z.genericPoint Z.coheight_genericPoint_eq_one a ha,
    ord_algebraMap_stalk Z.genericPoint Z.coheight_genericPoint_eq_one b hb'] at hord
  rw [rationalFunctionWeilDivisor_apply]
  omega

/-- The Weil divisor of a rational function is the principal Weil divisor of Tag 0BE3, once the
invertible rational maps to the affine line are identified with the units of the function
field. -/
theorem principalDivisor_eq_rationalFunctionWeilDivisor [IsNoetherian X] [IsIntegral X]
    (f : (Stacks.Chow.rationalFunctions X)ˣ) :
    principalDivisor X f = rationalFunctionWeilDivisor X
      (Units.map (Stacks.Chow.rationalFunctionsEquivFunctionField X).val.toMonoidHom f) :=
  rfl

end AlgebraicGeometry

end
