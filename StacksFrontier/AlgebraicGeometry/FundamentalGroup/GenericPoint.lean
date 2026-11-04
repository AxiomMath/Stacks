module

public import Mathlib.AlgebraicGeometry.FunctionField
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCategory.FieldFundamentalGroup
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.MorphismMap

/-!
# The fundamental group of an irreducible scheme and its function field

For an irreducible scheme the inclusion of the generic point induces a continuous homomorphism
from the absolute Galois group of the function field to the étale fundamental group, based at the
geometric point that an algebraically closed extension of the function field provides.

## Main definitions

* `AlgebraicGeometry.galoisToFundamentalGroup`: the canonical continuous homomorphism from the
  Galois group of a separable closure of the function field to the étale fundamental group of the
  scheme.

## Implementation notes

The generic point is `genericPoint X`, its residue field is the function field, and the inclusion
of the generic point is `AlgebraicGeometry.Scheme.fromSpecResidueField`. The homomorphism is the
composite of the canonical identification of the absolute Galois group of a field with the
fundamental group of its spectrum and the homomorphism induced by that inclusion.

## References

* [Stacks Project, Tag 0BQH](https://stacks.math.columbia.edu/tag/0BQH)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The canonical continuous homomorphism from the absolute Galois group of the function field of
an irreducible scheme to its étale fundamental group, based at a geometric generic point. -/
@[stacks 0BQH, sga "7 XIX 1.4" "partial"]
def galoisToFundamentalGroup
    (X : Scheme.{u}) [IrreducibleSpace X]
    (L Ω : Type u) [Field L] [Field Ω]
    [Algebra (X.residueField (genericPoint X)) L]
    [IsSepClosure (X.residueField (genericPoint X)) L]
    [Algebra L Ω] [Algebra (X.residueField (genericPoint X)) Ω]
    [IsScalarTower (X.residueField (genericPoint X)) L Ω]
    [IsAlgClosed Ω]
    [Algebra.IsAlgebraic (X.residueField (genericPoint X)) Ω] :
    Gal(L / X.residueField (genericPoint X)) →ₜ*
      EtaleFundamentalGroup X
        ((algebraicClosureGeometricPoint
          (X.residueField (genericPoint X)) Ω).map
          (X.fromSpecResidueField (genericPoint X))) :=
  (etaleFundamentalGroupMap
    (X.fromSpecResidueField (genericPoint X))
    (algebraicClosureGeometricPoint
      (X.residueField (genericPoint X)) Ω)).comp
    (ContinuousMonoidHom.toContinuousMonoidHom
      (galoisEquivEtaleFundamentalGroup
        (X.residueField (genericPoint X)) L Ω))

end AlgebraicGeometry

end
