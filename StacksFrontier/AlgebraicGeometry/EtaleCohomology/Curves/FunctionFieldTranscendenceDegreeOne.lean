module

public import StacksFrontier.AlgebraicGeometry.Curves.NonsingularProjectiveModel
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.BrauerGroupFunctionField

/-!
# The transcendence degree of the function field of a curve

Let `k` be a field and `X` a curve over `k`. Then the function field `k(X)` has transcendence
degree one over `k`.

## Main results

* `AlgebraicGeometry.trdeg_functionField_eq_one`: the statement above, for an unbundled structure
  morphism `f : X ⟶ Spec k` and the `k`-algebra structure
  `AlgebraicGeometry.functionFieldAlgebra`.

## Implementation notes

The dimension formula of Tag 0A21 delivers the transcendence degree at the *residue field of the
generic point*, which is
`AlgebraicGeometry.trdeg_residueField_genericPoint_eq_one`. On an integral scheme that field is
the function field, by `AlgebraicGeometry.genericResidueEquiv`, and the identification is a
`k`-algebra map because evaluation at a point is the germ followed by the residue; so the
transcendence degree carries across it by `AlgEquiv.trdeg_eq`.

`AlgebraicGeometry.isCurve_iff_trdeg_functionField_eq_one` is the same fact for the bundled
`AlgebraicGeometry.Variety`, stated against that category's global algebra instance
`AlgebraicGeometry.varietyFunctionFieldAlgebra`. What is proved here is the form for an
unbundled structure morphism, which is the form the étale-cohomology files use; it is a separate
file rather than an addition to
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.BrauerGroupFunctionField` because
`AlgebraicGeometry.functionFieldAlgebra` lives in the curves tree, and widening the import
surface of that file pushes an unrelated `isDefEq` in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GaloisCohomologyFunctionField` past its
heartbeat limit.

## References

* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21): the dimension formula
  this reads off the function field.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **The function field of a curve has transcendence degree one over the base field.** This is
`AlgebraicGeometry.trdeg_residueField_genericPoint_eq_one` carried across
`AlgebraicGeometry.genericResidueEquiv`, which on an integral scheme identifies the function
field with the residue field at the generic point and is a `k`-algebra map because evaluation at
a point is the germ followed by the residue.

The `k`-algebra structure is `AlgebraicGeometry.functionFieldAlgebra`, the one induced by the
structure morphism. -/
theorem trdeg_functionField_eq_one (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsCurve k f] :
    letI := functionFieldAlgebra k f
    Algebra.trdeg k X.functionField = 1 := by
  let : Algebra k (X.residueField (genericPoint X)) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
      X.Γevaluation (genericPoint X)).hom.toAlgebra
  let := functionFieldAlgebra k f
  exact (AlgEquiv.trdeg_eq (AlgEquiv.ofRingEquiv (f := genericResidueEquiv X)
    (fun a => rfl))).trans (trdeg_residueField_genericPoint_eq_one k f)

end AlgebraicGeometry

end
