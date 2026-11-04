module

public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.TriangulatedSubcategory

/-!
# Direct summands of perfect objects on a ringed space

Tag 08CS says that if `K ⊞ L` is a perfect object of `D(O_X)` then so are `K` and `L`. The
perfect objects are already known to form a *triangulated* subcategory (Tag 08CR, Tag 0FDG);
08CS is the statement that this subcategory is *thick*, which no formal triangulated argument
supplies. This file contains what the triangulated structure alone does give: once one summand
of a perfect biproduct is known to be perfect, so is the other.

Tag 08CS itself is `Stacks.Cohomology.TorAmplitude.isPerfect_of_biprod`: the characterisation of
Tag 08CQ turns perfectness of `K ⊞ L` into pseudo-coherence plus locally finite Tor dimension,
both of which pass to a summand (Tags 08CE and 08CK), and Tag 08CQ turns the pair back into
perfectness. Its retract form is `Stacks.Cohomology.PerfectDirectSummands.isPerfect_of_retract`.

## Main results

* `Stacks.Cohomology.PerfectDirectSummands.isPerfect_left_of_biprod_of_right` and
  `Stacks.Cohomology.PerfectDirectSummands.isPerfect_right_of_biprod_of_left`: once one summand is
  known to be perfect, the other is. These are the two-out-of-three property of Tag 08CR applied
  to the split triangle `K ⟶ K ⊞ L ⟶ L ⟶ K[1]`.

## Implementation notes

The statements hold for any model of `D(O_X)`. The space, ring and module universes coincide, as
they must for Tag 08CR.

## References

* [Stacks Project, Tag 08CS](https://stacks.math.columbia.edu/tag/08CS)
* [Stacks Project, Tag 08CR](https://stacks.math.columbia.edu/tag/08CR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open StrictlyPerfect

namespace Stacks.Cohomology.PerfectDirectSummands

universe u d

variable {X : RingedSpace.{u, u}}

/-- **If a biproduct is perfect and its second summand is, then so is its first.** The split
triangle `K ⟶ K ⊞ L ⟶ L ⟶ K[1]` is distinguished, so this is the two-out-of-three property
of Tag 08CR for the first vertex. -/
theorem isPerfect_left_of_biprod_of_right [HasDerivedCategory.{d} (OXMod.{u} X)]
    (K L : DerivedCategory (OXMod.{u} X))
    (h : Stacks.Cohomology.PerfectComplexes.IsPerfect (K ⊞ L)) (hL :
      Stacks.Cohomology.PerfectComplexes.IsPerfect L) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect K :=
  Stacks.Cohomology.PerfectComplexTriangles.isPerfect_obj₁_of_distinguished (binaryBiproductTriangle
    K L)
    (binaryBiproductTriangle_distinguished K L) h hL

/-- **If a biproduct is perfect and its first summand is, then so is its second.** -/
theorem isPerfect_right_of_biprod_of_left [HasDerivedCategory.{d} (OXMod.{u} X)]
    (K L : DerivedCategory (OXMod.{u} X))
    (h : Stacks.Cohomology.PerfectComplexes.IsPerfect (K ⊞ L)) (hK :
      Stacks.Cohomology.PerfectComplexes.IsPerfect K) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect L :=
  Stacks.Cohomology.PerfectComplexTriangles.isPerfect_obj₃_of_distinguished (binaryBiproductTriangle
    K L)
    (binaryBiproductTriangle_distinguished K L) hK h

end Stacks.Cohomology.PerfectDirectSummands

end
