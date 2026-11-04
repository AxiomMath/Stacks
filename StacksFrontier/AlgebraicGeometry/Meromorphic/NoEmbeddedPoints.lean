module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Embedded
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.MinimalSupport
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.WeaklyAssociated
public import StacksFrontier.AlgebraicGeometry.Properties.Noetherian

/-!
# A locally Noetherian scheme without embedded points

On a locally Noetherian scheme the associated and the weakly associated points coincide, and a
generic point of an irreducible component is always associated. So if the scheme has no embedded
points, both sets of points are exactly the generic points of the irreducible components.

## Main results

* `AlgebraicGeometry.schemeAssociatedPoints_eq_genericPoints_of_hasNoEmbeddedPoints` and
  `AlgebraicGeometry.schemeWeaklyAssociatedPoints_eq_genericPoints_of_hasNoEmbeddedPoints`: on a
  locally Noetherian scheme without embedded points the associated points, the weakly
  associated points and the generic points of the irreducible components all agree.

## References

* [Stacks Project, Tag 0EMH](https://stacks.math.columbia.edu/tag/0EMH)
* [Stacks Project, Tag 05AH](https://stacks.math.columbia.edu/tag/05AH)
* [Stacks Project, Tag 05AR](https://stacks.math.columbia.edu/tag/05AR)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- On a locally Noetherian scheme without embedded points the associated points are exactly the
generic points of the irreducible components. -/
theorem schemeAssociatedPoints_eq_genericPoints_of_hasNoEmbeddedPoints (X : Scheme.{u})
    [IsLocallyNoetherian X] (hX : HasNoEmbeddedPoints X) :
    Stacks.Divisors.schemeAssociatedPoints X = genericPoints X := by
  refine subset_antisymm (fun x hx => ?_) fun x hx =>
    mem_schemeAssociatedPoints_of_isGenericPoint_irreducibleComponent X hx rfl
  let C : irreducibleComponents X :=
    ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
  let η : genericPoints X := genericPoints.ofComponent C
  have hηx : η.1 ⤳ x := specializes_iff_mem_closure.mpr <|
    (genericPoints.isGenericPoint_ofComponent C).symm ▸ mem_irreducibleComponent
  exact (of_not_not fun hne => hX x ⟨hx, η.1,
    mem_schemeAssociatedPoints_of_isGenericPoint_irreducibleComponent
      X C.property (genericPoints.isGenericPoint_ofComponent C), hηx, hne⟩ : η.1 = x) ▸ η.property

/-- On a locally Noetherian scheme without embedded points the weakly associated points are
exactly the generic points of the irreducible components. -/
theorem schemeWeaklyAssociatedPoints_eq_genericPoints_of_hasNoEmbeddedPoints (X : Scheme.{u})
    [IsLocallyNoetherian X] (hX : HasNoEmbeddedPoints X) :
    Stacks.Divisors.schemeWeaklyAssociatedPoints X = genericPoints X :=
  (associatedPoints_eq_weaklyAssociatedPoints X (SheafOfModules.unit X.ringCatSheaf)).symm.trans
    (schemeAssociatedPoints_eq_genericPoints_of_hasNoEmbeddedPoints X hX)

end AlgebraicGeometry
