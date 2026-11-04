module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.Basic

/-!
# Birationality of a surjective morphism of irreducible schemes

An irreducible scheme has exactly one generic point, so for a surjective morphism between
irreducible schemes the bijection on generic points demanded by birationality is automatic: the
generic point of the source is carried to the generic point of the target, because its closure is
everything and a surjection carries a dense subset to a dense subset. What remains of birationality
is then a single condition, that the morphism be an isomorphism on the local ring at the generic
point.

## Main results

* `AlgebraicGeometry.genericPoint_eq_of_surjective`: a surjective morphism of irreducible schemes
  carries the generic point to the generic point.
* `AlgebraicGeometry.isBirational_of_isIso_stalkMap_genericPoint`: a surjective morphism of
  irreducible schemes which is an isomorphism on the local ring at the generic point is birational.

## References

* [Stacks Project, Tag 01RO](https://stacks.math.columbia.edu/tag/01RO)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A surjective morphism of irreducible schemes carries the generic point of its source to the
generic point of its target. -/
theorem genericPoint_eq_of_surjective {X Y : Scheme.{u}} [IrreducibleSpace X]
    [IrreducibleSpace Y] (f : X ⟶ Y) [Surjective f] :
    f (genericPoint X) = genericPoint Y := by
  refine IsGenericPoint.eq ?_ (genericPoint_spec Y)
  simpa only [Set.image_univ, f.surjective.range_eq, closure_univ] using
    (genericPoint_spec X).image f.continuous

/-- A surjective morphism of irreducible schemes inducing an isomorphism on the local ring at the
generic point is birational. -/
theorem isBirational_of_isIso_stalkMap_genericPoint {X Y : Scheme.{u}} [IrreducibleSpace X]
    [IrreducibleSpace Y] (f : X ⟶ Y) [Surjective f]
    [IsIso (f.stalkMap (genericPoint X))] : IsBirational f := by
  simp only [isBirational_iff, genericPoints_eq_singleton, Set.bijOn_singleton,
    Set.mem_singleton_iff, forall_eq]
  exact ⟨genericPoint_eq_of_surjective f, inferInstance⟩

end AlgebraicGeometry

end
