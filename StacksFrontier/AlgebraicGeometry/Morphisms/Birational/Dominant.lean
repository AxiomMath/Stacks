module

public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Properties
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.Basic

/-!
# Birational morphisms are dominant

A birational morphism of schemes hits every generic point of an irreducible component of its
target, by the bijection on generic points in the definition of birationality. Those points are
dense, because the underlying space of a scheme is sober, so such a morphism has dense range and
is therefore dominant.

## Main results

* `AlgebraicGeometry.isDominant_of_genericPoints_subset_range`: a morphism of schemes whose
  image contains the generic point of every irreducible component of the target is dominant.
* `AlgebraicGeometry.IsBirational.isDominant`: a birational morphism of schemes is dominant.

## Implementation notes

Only the surjectivity half of the bijection on generic points is used; the condition on local
rings and the finiteness of the sets of irreducible components play no role. Accordingly the
statement here carries neither finiteness hypothesis, and is stronger than the source, which
imposes both because they are the hypotheses under which birationality is defined.

The density of the generic points is `TopologicalSpace.genericPoints.closure`, and the
implication from it to dominance is
[Stacks Project, Tag 01RK](https://stacks.math.columbia.edu/tag/01RK), which the source's proof
invokes; it is stated here as `AlgebraicGeometry.isDominant_of_genericPoints_subset_range`.

## References

* [Stacks Project, Tag 01RK](https://stacks.math.columbia.edu/tag/01RK)
* [Stacks Project, Tag 01RP](https://stacks.math.columbia.edu/tag/01RP)
-/

@[expose] public section

open TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A morphism of schemes whose image contains the generic point of every irreducible component
of the target is dominant. -/
@[stacks 01RK]
theorem isDominant_of_genericPoints_subset_range {X S : Scheme.{u}} (f : X ⟶ S)
    (h : genericPoints S ⊆ Set.range f) : IsDominant f :=
  ⟨(dense_iff_closure_eq.mpr (genericPoints.closure (α := S))).mono h⟩

/-- A birational morphism of schemes is dominant. -/
@[stacks 01RP, ega "I 2.2.9" "more general"]
theorem IsBirational.isDominant {X Y : Scheme.{u}} {f : X ⟶ Y} (hf : IsBirational f) :
    IsDominant f :=
  isDominant_of_genericPoints_subset_range f hf.bijOn.surjOn.subset_range

end AlgebraicGeometry
