module

public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedFamiliesFiberedForget
public import StacksFrontier.AlgebraicGeometry.Quot.StackOfSpacesStack
public import StacksFrontier.AlgebraicGeometry.Stacks.Localization.InheritedTopology
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Subcanonical
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverBased
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverCompare
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.Basic
public import StacksFrontier.CategoryTheory.Sites.Localization.StacksAndLocalization
public import StacksFrontier.CategoryTheory.Sites.Stack.StackBridge
public import StacksFrontier.CategoryTheory.Sites.Stack.Transport

/-!
# The two assertions of Stacks 0D40, and how the first follows from the second

Stacks 0D40 asserts that the category `Polarized` of polarized families of Stacks 0D1M is a
stack in groupoids over the category `Spaces'_{fp, flat, proper}` of Stacks 0D1E, endowed with
the topology inherited from the big fppf site (Stacks 06NV), and that it is a stack in groupoids
over the big fppf site itself.

This file records the formal part of the argument, which is the same for both assertions:

* `Spaces'_{fp, flat, proper}` over the terminal scheme, read over the big fppf site itself
  through `AlgebraicGeometry.polarizedFamiliesProperFlatProjection`, is a stack in groupoids:
  Stacks 0D1G over the slice at the terminal scheme, and Construction A of Stacks 04WV, which is
  Stacks 09WX for the slice projection (the representable presheaf of the terminal scheme is a
  sheaf because the big fppf site is subcanonical).
* if `Polarized` is a stack over the big fppf site, then so is the replacement category
  `AlgebraicGeometry.PolarizedSpaces` of Stacks 06N7 to which Stacks 0D3Z refers (Stacks 042W, the
  two being equivalent over the site), and then `PolarizedSpaces` is a stack in groupoids over
  `Spaces'_{fp, flat, proper}` with the inherited topology by Stacks 06NX: a 1-morphism of stacks
  in groupoids which makes its source fibred in groupoids over its target makes it a stack in
  groupoids over the target, and `AlgebraicGeometry.polarizedSpacesForget` is such a 1-morphism by
  Stacks 0D3Z.

The source proves the first assertion directly and deduces the second by Stacks 09WX. Both
assertions are equivalent given Stacks 0D1G and 0D3Z (09WX in one direction, 06NX in the other),
and the second is the one whose verification needs no bookkeeping of the replacement category, so
the argument is organised around it.

## Main results

* `AlgebraicGeometry.polarizedFamiliesProperFlatProjection_isStack` and
  `AlgebraicGeometry.polarizedFamiliesProperFlatProjection_isStackInGroupoids`: Stacks 0D1G read
  over the big fppf site itself.
* `AlgebraicGeometry.polarizedSpacesProjection_isStack_of_isStack`: the transport of the stack
  condition from `Polarized` to the replacement category.
* `AlgebraicGeometry.polarizedSpacesForget_isStackInGroupoids_of_isStack`: the first assertion of
  Stacks 0D40 from the second.

## References

* [Stacks Project, Tag 0D40](https://stacks.math.columbia.edu/tag/0D40)
* [Stacks Project, Tag 06NX](https://stacks.math.columbia.edu/tag/06NX)
* [Stacks Project, Tag 04WV](https://stacks.math.columbia.edu/tag/04WV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u})

/-! ### `Spaces'_{fp, flat, proper}` over the big fppf site itself -/

/-- Stacks 0D1G read over the big fppf site itself: the finitely presented, flat and proper
families of algebraic spaces over the terminal scheme, projected to their base scheme, form a
stack over the big fppf site.

Stacks 0D1G gives the stack over the slice at the terminal scheme, and composing with the slice
projection is Construction A of Stacks 04WV, whose only input is that the representable presheaf
of the terminal scheme is a sheaf; it is, the big fppf site being subcanonical. -/
theorem polarizedFamiliesProperFlatProjection_isStack :
    (polarizedFamiliesProperFlatProjection B).IsStack B.topology :=
  Functor.isStack_comp_forget _
    ((isSheaf_iff_isSheaf_of_type B.topology _).2
      (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _))
    (cartesianProperFlatProjection_isStack B integerBase B.contains_integerBase).2

/-- Stacks 0D1G read over the big fppf site itself, as a stack in groupoids in the sense of
Stacks 02ZI. -/
theorem polarizedFamiliesProperFlatProjection_isStackInGroupoids :
    (polarizedFamiliesProperFlatProjection B).IsStackInGroupoids.{w} B.topology :=
  (polarizedFamiliesProperFlatProjection_isStack B).isStackInGroupoids
    (polarizedFamiliesProperFlatProjection_isFiberedInGroupoids B)

/-! ### From the stack over the site to the stack over `Spaces'_{fp, flat, proper}` -/

/-- The equivalence over the big fppf site between `Polarized` and its replacement category
`AlgebraicGeometry.PolarizedSpaces`, as an equivalence of categories over the site. -/
def polarizedSpacesBasedEquivalence :
    BasedCategory.Equivalence (BasedCategory.ofFunctor (polarizedProjection B))
      (BasedCategory.ofFunctor (polarizedSpacesProjection B)) :=
  StacksRepresentableCFG.EquivalenceOver.toBasedEquivalence
    (StacksRepresentableCFG.EquivalenceOver.ofFunctorIsEquivalenceOver
      (toPolarizedSpaces_comp_polarizedSpacesProjection B) (polarizedSpaces_isEquivalenceOver B))

/-- If `Polarized` is a stack over the big fppf site, so is its replacement category
`AlgebraicGeometry.PolarizedSpaces` (Stacks 042W). -/
theorem polarizedSpacesProjection_isStack_of_isStack
    (h : (polarizedProjection B).IsStack B.topology) :
    (polarizedSpacesProjection B).IsStack B.topology :=
  (BasedCategory.isStack_iff_of_equivalence (polarizedSpacesBasedEquivalence B) B.topology).1 h

/-- **The first assertion of Stacks 0D40 from the second.** If `Polarized` is a stack over the
big fppf site, then the replacement category `AlgebraicGeometry.PolarizedSpaces` is a stack in
groupoids over `Spaces'_{fp, flat, proper}` endowed with the topology inherited from the big
fppf site (Stacks 06NV).

This is Stacks 06NX for the forgetful 1-morphism `AlgebraicGeometry.polarizedSpacesForget`: its
source and target are stacks in groupoids over the site (the hypothesis, transported to the
replacement category, and Stacks 0D1G), and it makes its source fibred in groupoids over its
target (Stacks 0D3Z). -/
theorem polarizedSpacesForget_isStackInGroupoids_of_isStack
    (h : (polarizedProjection B).IsStack B.topology) :
    (polarizedSpacesForget B).IsStackInGroupoids.{w}
      ((polarizedFamiliesProperFlatProjection B).inheritedTopology B.topology) := by
  have := (polarizedFamiliesProperFlatProjection_isFiberedInGroupoids B).isFibered
  exact Functor.isStackInGroupoids_of_isFiberedInGroupoids B.topology _
    (polarizedSpacesProjection B) (polarizedFamiliesProperFlatProjection B)
    (polarizedSpacesForget B)
    ((polarizedSpacesProjection_isStack_of_isStack B h).isStackInGroupoids
      (polarizedSpacesProjection_isFiberedInGroupoids B))
    (polarizedFamiliesProperFlatProjection_isStackInGroupoids B)
    (polarizedSpacesForget_comp_polarizedFamiliesProperFlatProjection B)
    (polarizedSpacesForget_isFiberedInGroupoids B)
    (Functor.isInheritedTopology_inheritedTopology _ _)

end AlgebraicGeometry

end
