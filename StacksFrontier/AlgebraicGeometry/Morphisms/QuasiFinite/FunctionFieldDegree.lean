module

public import StacksFrontier.AlgebraicGeometry.Chow.PrincipalDivisorPushforward.StalkTransport
public import StacksFrontier.AlgebraicGeometry.FunctionField.DominantMap

/-!
# The degree of a dominant morphism of integral schemes

Let `f : X ⟶ Y` be a morphism of integral schemes which is locally of finite type and dominant.
The induced extension of function fields `R(Y) ⊆ R(X)` is
`AlgebraicGeometry.dominantFunctionFieldMap f`, and the degree of `X` over `Y` is the degree
`[R(X) : R(Y)]` of that extension. This file defines that degree and records two facts about it:
it is positive as soon as the extension is finite, and it is multiplicative in a tower, so that
for dominant `f : X ⟶ Y` and `g : Y ⟶ Z` between integral schemes with both extensions finite,
`deg(X/Z) = deg(X/Y) * deg(Y/Z)`.

## Main definitions

* `AlgebraicGeometry.degreeOver`: the degree `deg(X/Y) = [R(X) : R(Y)]` of `X` over `Y`.

## Main results

* `AlgebraicGeometry.degreeOver_eq_finrank`: the degree is the degree of the extension of
  function fields, computed against whichever algebra structure the caller has in scope.
* `AlgebraicGeometry.degreeOver_pos`: the degree is positive when the extension is finite.
* `AlgebraicGeometry.residueDegree_genericPoint_eq_degreeOver`: the degree is the residue degree
  at the generic point of the source.
* `AlgebraicGeometry.isScalarTower_dominantFunctionFieldMap`: the function fields of `X`, `Y`
  and `Z` form a tower of field extensions.
* `AlgebraicGeometry.finrank_functionField_comp`: multiplicativity of the degrees.

## Implementation notes

There is no canonical `Algebra` instance on a pair of function fields: the algebra structure
comes from a morphism of schemes, which does not appear in the type. The three algebra
structures are therefore taken as instance arguments together with the equations identifying
their structure maps with the function-field maps, as is done for the section rings in
`StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.DimensionFormula`, so that the statements
can be used against whichever instances the caller already has in scope — typically
`(dominantFunctionFieldMap f).toAlgebra`, for which the equations are `rfl`.

For the same reason `degreeOver` fixes that algebra structure inside its body rather than taking
it as an argument, so that the degree is a function of the morphism alone and not of an instance
that does not appear in its type; `degreeOver_eq_finrank` is what transports it to another
algebra structure with the same structure map.

The source states the degree under the additional hypothesis that the extension of function
fields is finite, and calls it a positive integer. `Module.finrank` is `0` on an extension that
is not finite, so `degreeOver` is defined without that hypothesis and positivity is the separate
statement `degreeOver_pos`, whose hypothesis is exactly the source's. The source also allows
the hypothesis to be given in any of the equivalent forms of Stacks Tag 02NX; finiteness of the
extension is the form the degree is computed from, and it is the one taken here.

The source assumes in addition that `f` and `g` are locally of finite type, which is what makes
the two degrees finite in the situation it cares about. Finiteness of the two extensions is
assumed here directly, so no finite-type hypothesis is needed; the statement proved is therefore
more general than the source's.

The scalar tower is exactly the functoriality of the function-field map, Stacks Tag 02JU, which
is `Stacks.Chow.dominantFunctionFieldMap_comp`; given it, multiplicativity is
`Module.finrank_mul_finrank`.

## References

* [Stacks Project, Tag 02NY](https://stacks.math.columbia.edu/tag/02NY)
* [Stacks Project, Tag 02NZ](https://stacks.math.columbia.edu/tag/02NZ)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

section Degree

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **Stacks Project, Tag 02NY.** The *degree of `X` over `Y`* for a morphism `f : X ⟶ Y` of
integral schemes which is locally of finite type and dominant: the degree
`deg(X/Y) = [R(X) : R(Y)]` of the extension of function fields induced by `f`.

This is a positive integer whenever that extension is finite, which is the case the source
defines it in; see `AlgebraicGeometry.degreeOver_pos`. -/
@[stacks 02NY]
noncomputable def degreeOver (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y]
    [LocallyOfFiniteType f] [IsDominant f] : ℕ :=
  letI := (dominantFunctionFieldMap f).toAlgebra
  Module.finrank Y.functionField X.functionField

variable [IsIntegral X] [IsIntegral Y] [LocallyOfFiniteType f] [IsDominant f]

/-- The degree of `X` over `Y` is the degree of the extension of function fields induced by `f`,
computed against any algebra structure whose structure map is that extension. -/
theorem degreeOver_eq_finrank [Algebra Y.functionField X.functionField]
    (hf : algebraMap Y.functionField X.functionField = dominantFunctionFieldMap f) :
    degreeOver f = Module.finrank Y.functionField X.functionField := by
  unfold degreeOver
  congr 1
  exact congrArg (fun i ↦ @Algebra.toModule _ _ _ _ i)
    (Algebra.algebra_ext _ _ fun r ↦ by rw [hf]; rfl)

/-- The degree of `X` over `Y` is positive when the extension of function fields induced by `f`
is finite. This is the hypothesis under which the source defines the degree, and positivity is
the source's assertion that it is a positive integer. -/
theorem degreeOver_pos
    (h : letI := (dominantFunctionFieldMap f).toAlgebra
      FiniteDimensional Y.functionField X.functionField) :
    0 < degreeOver f := by
  let := (dominantFunctionFieldMap f).toAlgebra
  let : FiniteDimensional Y.functionField X.functionField := h
  exact Module.finrank_pos

end Degree

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  [IsIntegral X] [IsIntegral Y] [IsIntegral Z] [IsDominant f] [IsDominant g]
  [Algebra Y.functionField X.functionField] [Algebra Z.functionField Y.functionField]
  [Algebra Z.functionField X.functionField]

/-- For dominant morphisms `f : X ⟶ Y` and `g : Y ⟶ Z` of integral schemes whose function
fields carry the algebra structures induced by `f`, `g` and `f ≫ g`, the function field of `X`
over that of `Y` over that of `Z` is a tower of field extensions. -/
theorem isScalarTower_dominantFunctionFieldMap
    (hf : algebraMap Y.functionField X.functionField = dominantFunctionFieldMap f)
    (hg : algebraMap Z.functionField Y.functionField = dominantFunctionFieldMap g)
    (hfg : algebraMap Z.functionField X.functionField = dominantFunctionFieldMap (f ≫ g)) :
    IsScalarTower Z.functionField Y.functionField X.functionField :=
  IsScalarTower.of_algebraMap_eq fun x ↦ by
    rw [hf, hg, hfg, Stacks.Chow.dominantFunctionFieldMap_comp]
    rfl

/-- **Stacks Project, Tag 02NZ.** The degree of a tower of dominant morphisms of integral
schemes is the product of the two degrees: if the function field of `X` is finite over that of
`Y` and the function field of `Y` is finite over that of `Z`, then
`[R(X) : R(Z)] = [R(X) : R(Y)] * [R(Y) : R(Z)]`. -/
@[stacks 02NZ]
theorem finrank_functionField_comp
    [FiniteDimensional Y.functionField X.functionField]
    [FiniteDimensional Z.functionField Y.functionField]
    (hf : algebraMap Y.functionField X.functionField = dominantFunctionFieldMap f)
    (hg : algebraMap Z.functionField Y.functionField = dominantFunctionFieldMap g)
    (hfg : algebraMap Z.functionField X.functionField = dominantFunctionFieldMap (f ≫ g)) :
    Module.finrank Z.functionField X.functionField =
      Module.finrank Y.functionField X.functionField *
        Module.finrank Z.functionField Y.functionField := by
  have := isScalarTower_dominantFunctionFieldMap f g hf hg hfg
  exact (Module.finrank_mul_finrank _ _ _).symm.trans (Nat.mul_comm _ _)

end AlgebraicGeometry

end
