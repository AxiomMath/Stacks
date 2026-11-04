module

public import StacksFrontier.AlgebraicGeometry.Spaces.GenericRationalFunctions

/-!
# The function field of an integral algebraic space

Let `X` be an integral algebraic space over a scheme `S`. Its ring `R(X)` of rational
functions, in the sense of Tag 0EMP, is a field: Tag 0END identifies it with the residue
field at the generic point of `X`. That field is the *function field*, or the *field of
rational functions*, of `X`, also written `k(X)`.

## Main definitions

* `AlgebraicGeometry.Space.functionField` is Tag 0ENE: the field structure carried by the
  ring of rational functions of an integral algebraic space over `S`.

## Main results

* `AlgebraicGeometry.Space.functionField_toCommRing`: the function field has the canonical
  commutative ring of rational functions as its underlying ring, so that putting it in scope
  leaves the ring structure on `R(X)` unchanged.
* `AlgebraicGeometry.Space.functionField_mul_inv_cancel`: a nonzero rational function is
  invertible for that field structure.

## Implementation notes

The function field is produced as a `Field` structure on the existing type
`AlgebraicGeometry.Space.rationalFunctions` rather than as a type of its own: the Stacks
definition names the ring `R(X)` as a field and introduces no new object, and a separate
type would force every consumer of Tag 0END to transport along an isomorphism. For the same
reason this mirrors the scheme case, where the field structure on the rational functions of
an integral scheme is likewise put on the ring itself.

It cannot be an instance: integrality of an algebraic space,
`AlgebraicGeometry.Space.IsIntegralSpace`, is a conjunction of propositions rather than a
class, so the field structure depends on hypotheses that instance resolution cannot find. A
consumer brings it into scope with `letI := functionField B S hS hX hInt`.

## References

* [Stacks Project, Tag 0ENE](https://stacks.math.columbia.edu/tag/0ENE)
* [Stacks Project, Tag 0END](https://stacks.math.columbia.edu/tag/0END)
* [Stacks Project, Tag 0EMP](https://stacks.math.columbia.edu/tag/0EMP)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 0ENE.** The function field, or field of rational functions, of an integral
algebraic space `X` over `S`: the ring `R(X)` of rational functions of Tag 0EMP, which
Tag 0END shows to be a field by identifying it with the residue field at the generic
point. -/
@[stacks 0ENE "the function field R(X) = k(X) of an integral algebraic space", instance_reducible]
noncomputable def functionField (hX : IsAlgebraicSpace B S hS X)
    (hInt : IsIntegralSpace B S hS X) : Field (rationalFunctions B S hS hX) :=
  (isField_rationalFunctions B S hS hX hInt).toField

/-- The function field of an integral algebraic space has the canonical commutative ring of
rational functions as its underlying ring: it adds inverses and nothing else. -/
theorem functionField_toCommRing (hX : IsAlgebraicSpace B S hS X)
    (hInt : IsIntegralSpace B S hS X) :
    (functionField B S hS hX hInt).toCommRing =
      (inferInstance : CommRing (rationalFunctions B S hS hX)) :=
  rfl

/-- A nonzero rational function on an integral algebraic space is invertible in the function
field. -/
theorem functionField_mul_inv_cancel (hX : IsAlgebraicSpace B S hS X)
    (hInt : IsIntegralSpace B S hS X) {f : rationalFunctions B S hS hX} (hf : f ≠ 0) :
    letI := functionField B S hS hX hInt
    f * f⁻¹ = 1 :=
  let _ := functionField B S hS hX hInt
  mul_inv_cancel₀ hf

end AlgebraicGeometry.Space

end
