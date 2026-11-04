module

public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedCategoryDevissage
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorHomAdjunction
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorTriangulated

/-!
# Derived restriction of scalars along a homomorphism of differential graded algebras is exact

Let `φ : (A, d) → (B, d)` be a homomorphism of differential graded algebras over a commutative
ring. Derived restriction of scalars `(-)_A : D(B, d) ⥤ D(A, d)` of Tag 0BYX is the right
adjoint of derived extension of scalars `- ⊗_A^𝐋 B`, which commutes with the translation and
carries distinguished triangles to distinguished triangles. This file equips restriction of
scalars with the two corresponding structures, which the right adjoint of a triangulated functor
always carries.

## Main results

* `DifferentialGradedModule.derivedRestriction_commShift`: derived restriction of scalars
  commutes with the translation, by the unique structure compatible with the adjunction.
* `DifferentialGradedModule.derivedRestriction_isTriangulated`: derived restriction of scalars
  is exact.

Both are instances, so `(derivedRestriction φ).mapTriangle` becomes available, as do the
constructions which turn a left adjoint of `derivedRestriction φ` into a triangulated functor.

## Implementation notes

The commutation with the translation is `CategoryTheory.Adjunction.rightAdjointCommShift` at the
adjunction of Tag 0BYX, and it is the structure which makes that adjunction compatible with the
translation; the exactness is then
`CategoryTheory.Adjunction.isTriangulated_rightAdjoint`. The instance has to be seated with that
specific witness, because the compatibility of the adjunction with the translation is a
statement *about* it.

## References

* [Stacks Project, Tag 0BYX](https://stacks.math.columbia.edu/tag/0BYX)
* [Stacks Project, Tag 09LS](https://stacks.math.columbia.edu/tag/09LS)
-/

@[expose] public noncomputable section

open CategoryTheory

/- This file is stated against the admissible-sequence pretriangulated structure of Tag 09KH,
which is not an instance; it is activated here explicitly. -/
attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory'

universe u

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {A B : DifferentialGradedAlgebra R}

/-- Derived restriction of scalars commutes with the translation: it is the right adjoint of
derived extension of scalars, which does, and a right adjoint carries a unique commutation
compatible with the adjunction. -/
@[instance_reducible]
instance derivedRestriction_commShift (φ : A.Hom B) : (derivedRestriction φ).CommShift ℤ :=
  (DifferentialGraded.Bimodule.derivedTensorFunctor_adj_derivedRestriction
    φ).rightAdjointCommShift ℤ

/-- The adjunction between derived extension and derived restriction of scalars is compatible
with the translation. -/
instance derivedTensorFunctor_adj_derivedRestriction_commShift (φ : A.Hom B) :
    (DifferentialGraded.Bimodule.derivedTensorFunctor_adj_derivedRestriction φ).CommShift ℤ :=
  (DifferentialGraded.Bimodule.derivedTensorFunctor_adj_derivedRestriction
    φ).commShift_of_leftAdjoint ℤ

/-- Derived restriction of scalars is exact: it is the right adjoint, compatibly with the
translation, of the exact functor `- ⊗_A^𝐋 B`. -/
instance derivedRestriction_isTriangulated (φ : A.Hom B) :
    (derivedRestriction φ).IsTriangulated :=
  (DifferentialGraded.Bimodule.derivedTensorFunctor_adj_derivedRestriction
    φ).isTriangulated_rightAdjoint

end DifferentialGradedModule

end
