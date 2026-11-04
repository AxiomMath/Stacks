module

public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective

/-! # The K-injective complexes form a triangulated subcategory

Let `A` be an abelian category and `K(A)` the homotopy category of `ℤ`-indexed cochain complexes
in `A`. A cochain complex is K-injective exactly when its image in `K(A)` is right orthogonal to
the acyclic complexes, and in a pretriangulated category the right orthogonal of a triangulated
subcategory is again a triangulated subcategory. So the K-injective objects of `K(A)` form a
triangulated subcategory, which this file names; in particular the mapping cone of a morphism
between K-injective complexes is again K-injective.

The mapping cone statement is the form in which the closure property is used: a criterion for a
right derived functor on the unbounded derived category to be triangulated has to produce, for
every morphism of `D(A)`, a distinguished triangle of `K(A)` all three of whose vertices compute
the derived functor, and the third vertex of such a triangle on a morphism of complexes is a
mapping cone. The analogous property fails for the complexes with injective terms, since an
unbounded complex of injectives need not be K-injective.

## Main definitions

* `HomotopyCategory.subcategoryKInjective`: the K-injective objects of `K(A)`, as an object
  property, carrying `ObjectProperty.IsTriangulated` and
  `ObjectProperty.IsClosedUnderIsomorphisms`.

## Main results

* `CochainComplex.isKInjective_mappingCone`: the mapping cone of a morphism between K-injective
  cochain complexes is K-injective.

## Implementation notes

Both results are formal consequences of what is already available. `CochainComplex`'s
`isKInjective_iff_rightOrthogonal` identifies K-injectivity with right orthogonality to
`HomotopyCategory.subcategoryAcyclic`, whose `ObjectProperty.IsTriangulated` instance is
Mathlib's, as is the instance making a right orthogonal triangulated; so the subcategory needs no
proof beyond `dsimp`, and `isKInjective_mappingCone` is `ObjectProperty`'s
`ext_of_isTriangulatedClosed₃` at `HomotopyCategory.mappingCone_triangleh_distinguished`. What is
added here is the name, and the mapping-cone form, neither of which existed.

`CochainComplex.isKInjective_two_out_of_three_of_distTriang` in
`StacksFrontier.Algebra.Homology.DerivedCategory.KInjective` is the same closure property stated for
a general distinguished triangle of `K(A)`, and carries the tag of [Stacks, Tag 090X]. This file
is deliberately independent of it: it imports nothing outside Mathlib, so that both declarations
are available to the general derived-category modules without pulling in the whole of that file.

## References

* [Stacks Project, Tag 070H](https://stacks.math.columbia.edu/tag/070H)
* [Stacks Project, Tag 090X](https://stacks.math.columbia.edu/tag/090X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe v u

namespace HomotopyCategory

variable (A : Type u) [Category.{v} A] [Abelian A]

/-- The K-injective objects of the homotopy category `K(A)` of `ℤ`-indexed cochain complexes in
an abelian category `A`, as an object property. By
`CochainComplex.isKInjective_iff_rightOrthogonal` these are exactly the objects right orthogonal
to the acyclic complexes. -/
def subcategoryKInjective : ObjectProperty (HomotopyCategory A (ComplexShape.up ℤ)) :=
  (subcategoryAcyclic A).rightOrthogonal

/-- The K-injective objects form a triangulated subcategory of `K(A)`: the acyclic complexes form
a triangulated subcategory, and the right orthogonal of one is again one. -/
instance subcategoryKInjective_isTriangulated :
    (subcategoryKInjective A).IsTriangulated := by
  dsimp only [subcategoryKInjective]
  infer_instance

/-- The K-injective objects of `K(A)` are stable under isomorphism in `K(A)`, that is, under
homotopy equivalence of cochain complexes. -/
instance subcategoryKInjective_isClosedUnderIsomorphisms :
    (subcategoryKInjective A).IsClosedUnderIsomorphisms := by
  dsimp only [subcategoryKInjective]
  infer_instance

variable {A}

/-- A cochain complex is K-injective exactly when its image in `K(A)` lies in the triangulated
subcategory `HomotopyCategory.subcategoryKInjective`. -/
lemma quotient_obj_mem_subcategoryKInjective_iff (K : CochainComplex A ℤ) :
    subcategoryKInjective A ((quotient _ _).obj K) ↔ K.IsKInjective :=
  (CochainComplex.isKInjective_iff_rightOrthogonal K).symm

/-- An object of `K(A)` lies in `HomotopyCategory.subcategoryKInjective` exactly when the cochain
complex representing it is K-injective. -/
lemma mem_subcategoryKInjective_iff (X : HomotopyCategory A (ComplexShape.up ℤ)) :
    subcategoryKInjective A X ↔ CochainComplex.IsKInjective X.as :=
  quotient_obj_mem_subcategoryKInjective_iff X.as

end HomotopyCategory

namespace CochainComplex

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The mapping cone of a morphism between K-injective cochain complexes is K-injective: the
mapping cone is the third vertex of a distinguished triangle of `K(A)` whose first two vertices
are the given complexes, and the K-injective objects form a triangulated subcategory of `K(A)`. -/
theorem isKInjective_mappingCone {K L : CochainComplex A ℤ} (φ : K ⟶ L)
    [K.IsKInjective] [L.IsKInjective] :
    (mappingCone φ).IsKInjective := by
  rw [← HomotopyCategory.quotient_obj_mem_subcategoryKInjective_iff]
  exact ObjectProperty.ext_of_isTriangulatedClosed₃ _ _
    (HomotopyCategory.mappingCone_triangleh_distinguished φ)
    ((HomotopyCategory.quotient_obj_mem_subcategoryKInjective_iff K).2 inferInstance)
    ((HomotopyCategory.quotient_obj_mem_subcategoryKInjective_iff L).2 inferInstance)

end CochainComplex

end
