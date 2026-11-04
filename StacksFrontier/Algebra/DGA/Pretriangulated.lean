module

public import StacksFrontier.Algebra.DGA.ConeShift

/-!
# The homotopy category of differential graded modules is pretriangulated

The class of triangles isomorphic to a cone triangle satisfies the five axioms of a
pretriangulated category.  Four of them are
`DifferentialGradedModule.isomorphic_mem_distinguishedConeTriangles`,
`DifferentialGradedModule.contractible_mem_distinguishedConeTriangles`,
`DifferentialGradedModule.exists_mem_distinguishedConeTriangles` and
`DifferentialGradedModule.complete_distinguishedConeTriangles_morphism`, and one implication of
the fifth is `DifferentialGradedModule.rotate_mem_distinguishedConeTriangles`; this file supplies
the converse, from the closure of the class under the shift of triangles, and assembles the five
into the `CategoryTheory.Pretriangulated` instance.

## Main definitions

* `DifferentialGradedModule.coneTriangleDGShiftIso` identifies the shift of the cone triangle of
  `f` in the category of triangles of differential graded modules with the cone triangle of the
  shift of `f`, and `DifferentialGradedModule.shiftConeTriangleIso` is its image in the homotopy
  category.

## Main results

* `DifferentialGradedModule.shift_mem_distinguishedConeTriangles`: the shift of a triangle
  isomorphic to a cone triangle is one.
* `DifferentialGradedModule.invRotate_mem_distinguishedConeTriangles` and
  `DifferentialGradedModule.rotate_distinguishedConeTriangles_iff`: the class is closed under
  the inverse rotation, so a triangle lies in it exactly when its rotation does.
* `DifferentialGradedModule.instPretriangulatedHomotopyCategory`.

## Implementation notes

The shift of a triangle multiplies all three morphisms by the sign of the shift and inserts the
exchange of the two shifts into the third one; the comparison with the cone triangle of the
shifted morphism therefore carries that sign on the middle object and the comparison of the
cones, which multiplies the coordinate of the source by the same sign, on the third.  Both signs
are forced, and both are recorded in `DifferentialGradedModule.shiftedConeTriangleIso`.

The closure under the inverse rotation is deduced rather than computed: the inverse rotation of
a triangle is isomorphic to its double rotation shifted by `-1`, by
`CategoryTheory.Pretriangulated.invRotateIsoRotateRotateShiftFunctorNegOne`, and the class is
closed under rotation and under the shift.  The rotation axiom in its biconditional form then
follows from the unit of the auto-equivalence of the category of triangles given by rotation.

## References

* [Stacks Project, Tag 09KA](https://stacks.math.columbia.edu/tag/09KA)
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated

namespace DifferentialGradedModule

universe u v w

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra.{u, v} R}
variable {K L : DifferentialGradedModule.{u, v, w} A}

/-- The shift by `n` of the cone triangle of `f : K ⟶ L`, in the category of triangles of
differential graded modules, is the cone triangle of the shift of `f` by `n`. -/
noncomputable def coneTriangleDGShiftIso (f : K ⟶ L) (n : ℤ) :
    (Triangle.shiftFunctor (DifferentialGradedModule.{u, v, w} A) n).obj (coneTriangleDG f) ≅
      coneTriangleDG
        ((CategoryTheory.shiftFunctor (DifferentialGradedModule.{u, v, w} A) n).map f) :=
  eqToIso (Triangle.shiftFunctor_obj _ n (coneTriangleDG f)) ≪≫ shiftedConeTriangleIso f n

/-- The shift by `n` of the cone triangle of `f : K ⟶ L`, in the category of triangles of the
homotopy category, is the cone triangle of the shift of `f` by `n`: the quotient functor commutes
with the shift, so it carries the comparison of differential graded modules to a comparison in
the homotopy category. -/
noncomputable def shiftConeTriangleIso (f : K ⟶ L) (n : ℤ) :
    (Triangle.shiftFunctor (HomotopyCategory.{u, v, w} A) n).obj (coneTriangle f) ≅
      coneTriangle ((CategoryTheory.shiftFunctor (DifferentialGradedModule.{u, v, w} A) n).map f) :=
  ((toHomotopyCategory.{u, v, w} A).mapTriangle.commShiftIso n).symm.app (coneTriangleDG f) ≪≫
    (toHomotopyCategory.{u, v, w} A).mapTriangle.mapIso (coneTriangleDGShiftIso f n)

/-- The shift of a triangle isomorphic to a cone triangle is isomorphic to a cone triangle: it
is isomorphic to the cone triangle of the shift of the morphism. -/
theorem shift_mem_distinguishedConeTriangles (T : Triangle (HomotopyCategory.{u, v, w} A))
    (hT : T ∈ distinguishedConeTriangles.{u, v, w} (A := A)) (n : ℤ) :
    (Triangle.shiftFunctor (HomotopyCategory.{u, v, w} A) n).obj T ∈
      distinguishedConeTriangles.{u, v, w} (A := A) := by
  obtain ⟨K, L, f, ⟨e⟩⟩ := hT
  exact ⟨_, _, (CategoryTheory.shiftFunctor (DifferentialGradedModule.{u, v, w} A) n).map f,
    ⟨(Triangle.shiftFunctor (HomotopyCategory.{u, v, w} A) n).mapIso e ≪≫
      shiftConeTriangleIso f n⟩⟩

/-- The inverse rotation of a triangle isomorphic to a cone triangle is isomorphic to a cone
triangle: it is isomorphic to the double rotation shifted by `-1`. -/
theorem invRotate_mem_distinguishedConeTriangles (T : Triangle (HomotopyCategory.{u, v, w} A))
    (hT : T ∈ distinguishedConeTriangles.{u, v, w} (A := A)) :
    T.invRotate ∈ distinguishedConeTriangles.{u, v, w} (A := A) :=
  isomorphic_mem_distinguishedConeTriangles _
    (shift_mem_distinguishedConeTriangles _
      (rotate_mem_distinguishedConeTriangles _
        (rotate_mem_distinguishedConeTriangles _ hT)) (-1)) _
    ((invRotateIsoRotateRotateShiftFunctorNegOne (HomotopyCategory.{u, v, w} A)).app T)

/-- A triangle of the homotopy category is isomorphic to a cone triangle exactly when its
rotation is. -/
theorem rotate_distinguishedConeTriangles_iff (T : Triangle (HomotopyCategory.{u, v, w} A)) :
    T ∈ distinguishedConeTriangles.{u, v, w} (A := A) ↔
      T.rotate ∈ distinguishedConeTriangles.{u, v, w} (A := A) :=
  ⟨rotate_mem_distinguishedConeTriangles T, fun hT =>
    isomorphic_mem_distinguishedConeTriangles _
      (invRotate_mem_distinguishedConeTriangles T.rotate hT) _
      ((triangleRotation (HomotopyCategory.{u, v, w} A)).unitIso.app T)⟩

/-- The homotopy category of right differential graded `A`-modules is pretriangulated, with the
triangles isomorphic to a cone triangle as its distinguished triangles. -/
noncomputable instance instPretriangulatedHomotopyCategory :
    Pretriangulated (HomotopyCategory.{u, v, w} A) where
  distinguishedTriangles := distinguishedConeTriangles.{u, v, w} (A := A)
  isomorphic_distinguished := isomorphic_mem_distinguishedConeTriangles
  contractible_distinguished := contractible_mem_distinguishedConeTriangles
  distinguished_cocone_triangle := exists_mem_distinguishedConeTriangles
  rotate_distinguished_triangle := rotate_distinguishedConeTriangles_iff
  complete_distinguished_triangle_morphism := complete_distinguishedConeTriangles_morphism

end DifferentialGradedModule

end
