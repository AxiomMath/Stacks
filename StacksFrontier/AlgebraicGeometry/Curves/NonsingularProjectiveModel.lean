module

public import StacksFrontier.AlgebraicGeometry.Properties.Regular
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Projective
public import StacksCore.Tactic.StacksAttribute

/-!
# Nonsingular projective models of curves

A *nonsingular projective model* of a curve `X` over a field `k` is a regular projective curve
`Y` over `k` together with an isomorphism of function fields over `k`. Since the function field
of a curve is a finitely generated extension of `k` of transcendence degree one, such a model
records the birational class of `X` by a regular projective representative.

## Main definitions

* `AlgebraicGeometry.functionFieldAlgebra` is the `k`-algebra structure on the function field of
  a curve over `k` induced by its structure morphism.
* `AlgebraicGeometry.NonsingularProjectiveModel` is a nonsingular projective model of a curve
  over a field.

## Main results

* `AlgebraicGeometry.NonsingularProjectiveModel.functionFieldEquiv_bijective`: the comparison of
  function fields furnished by a model is bijective.
* `AlgebraicGeometry.NonsingularProjectiveModel.functionFieldEquiv_algebraMap`: it fixes the
  base field.

## Implementation notes

The structure morphisms to the spectrum of the base field are explicit arguments, as for
`AlgebraicGeometry.IsVariety` and `AlgebraicGeometry.IsCurve`. The function field is Mathlib's
`AlgebraicGeometry.Scheme.functionField`, the stalk at the generic point, and the `k`-algebra
structure on it is obtained from the global sections of the structure morphism followed by the
germ map out of the top open; it is `instance_reducible` so that scalar towers over it are
discharged by unfolding. The comparison of function fields is an algebra equivalence rather than
a bare ring equivalence, which is what makes it fix the embedded copy of `k`.

## References

* [Stacks Project, Tag 0BY2](https://stacks.math.columbia.edu/tag/0BY2)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The `k`-algebra structure on the function field of a curve over `k` induced by its structure
morphism. -/
@[instance_reducible]
noncomputable def functionFieldAlgebra (k : Type u) [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [IsCurve k sX] : Algebra k X.functionField := by
  letI : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  exact ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appTop ≫
    X.germToFunctionField ⊤).hom.toAlgebra

/-- A nonsingular projective model of a curve `X` over a field `k` is a regular projective curve
over `k` together with a `k`-algebra isomorphism from the function field of `X` to its own function
field. -/
@[stacks 0BY2]
structure NonsingularProjectiveModel (k : Type u) [Field k]
    (X : Scheme.{u}) (sX : X ⟶ Spec (.of k)) [IsCurve k sX] where
  /-- The scheme underlying the model. -/
  Y : Scheme.{u}
  /-- The structure morphism of the model to the spectrum of the base field. -/
  structureMap : Y ⟶ Spec (.of k)
  /-- The model is a curve over the base field. -/
  isCurve : IsCurve k structureMap
  /-- The model is a projective variety over the base field. -/
  isProjectiveVariety : IsProjectiveVariety k structureMap
  /-- The model is regular, that is, nonsingular. -/
  isRegular : IsRegular Y
  /-- The `k`-algebra isomorphism comparing the function field of `X` with that of the model. -/
  functionFieldEquiv :
    letI : IsCurve k structureMap := isCurve
    letI : Algebra k X.functionField := functionFieldAlgebra k sX
    letI : Algebra k Y.functionField := functionFieldAlgebra k structureMap
    X.functionField ≃ₐ[k] Y.functionField

/-- The comparison of function fields furnished by a nonsingular projective model is bijective. -/
theorem NonsingularProjectiveModel.functionFieldEquiv_bijective
    {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    [IsCurve k sX] (M : NonsingularProjectiveModel k X sX) :
    Function.Bijective M.functionFieldEquiv := by
  let _ := M.isCurve
  let _ := functionFieldAlgebra k sX
  let _ := functionFieldAlgebra k M.structureMap
  exact M.functionFieldEquiv.bijective

/-- The comparison of function fields furnished by a nonsingular projective model fixes the base
field. -/
@[simp]
theorem NonsingularProjectiveModel.functionFieldEquiv_algebraMap
    {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    [IsCurve k sX] (M : NonsingularProjectiveModel k X sX) (a : k) :
    letI : IsCurve k M.structureMap := M.isCurve
    letI : Algebra k X.functionField := functionFieldAlgebra k sX
    letI : Algebra k M.Y.functionField := functionFieldAlgebra k M.structureMap
    M.functionFieldEquiv (algebraMap k X.functionField a) =
      algebraMap k M.Y.functionField a := by
  let _ := M.isCurve
  let _ := functionFieldAlgebra k sX
  let _ := functionFieldAlgebra k M.structureMap
  exact M.functionFieldEquiv.commutes a

end AlgebraicGeometry

end
