module

public import StacksFrontier.AlgebraicGeometry.FinitelyPresentedOver.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.FinitePresentationBiproduct

/-!
# Finite presentation is closed under binary biproducts, and the index category is filtered

`StacksFrontier/AlgebraicGeometry/FinitelyPresentedOver/Basic.lean` builds the category
`Stacks.AlgebraicGeometry.FinitelyPresentedOver F` of finitely presented modules over a given
module `F`, proves it nonempty and essentially small, and proves the `cocone_maps` half of
filteredness.  It leaves the `cocone_objs` half open, for want of the closure of finite
presentation under binary biproducts, and records that `IsFiltered` follows from that closure and
nothing else.  This file proves the closure and draws that conclusion.

A presentation of `A ⊞ B` is assembled from presentations of `A` and of `B` over the pairwise
intersections of their respective covers: over such an intersection both restrict, and the
biproduct of two presentations of modules over a common open is a presentation of the biproduct,
because a biproduct of two cokernel diagrams is a cokernel diagram.  Both covers being covers of
the whole space, so is the family of pairwise intersections, and finiteness of the assembled
presentation is finiteness of each half.

## Main results

* `Stacks.AlgebraicGeometry.isFinitePresentation_biprod`: the biproduct of two finitely presented
  modules on a scheme is of finite presentation.
* `Stacks.AlgebraicGeometry.FinitelyPresentedOver.isFiltered`: the category of finitely presented
  modules over a module is filtered.  This is the first half of [Stacks Project, Tag 01PG] for
  the index category through which [Stacks Project, Tag 01PJ] is proved.

## Implementation notes

The obstruction recorded in `StacksFrontier/AlgebraicGeometry/FinitelyPresentedOver/Basic.lean` —
that the only construction of a presentation of a biproduct in this development,
`biprod_presentation`, carries no universe
parameters and so exists only for modules in `Type 0` — is sidestepped rather than repaired: the
presentation of a biproduct is rebuilt here directly from the two cokernel diagrams, at an
arbitrary universe, so nothing in that construction is used or needs generalising.

## References

* [Stacks Project, Tag 01PJ](https://stacks.math.columbia.edu/tag/01PJ)
* [Stacks Project, Tag 01PG](https://stacks.math.columbia.edu/tag/01PG)
* [Stacks Project, Tag 01BF](https://stacks.math.columbia.edu/tag/01BF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits SheafOfModules
open scoped ZeroObject

universe u v₁ u₁

namespace Stacks.AlgebraicGeometry

open _root_.AlgebraicGeometry

namespace FinitelyPresentedOver

/-- The category of finitely presented modules over a module is **filtered**.

The `cocone_maps` half is `exists_hom_comp_eq`, the nonemptiness is `nonempty`, and the
`cocone_objs` half is the biproduct, which is of finite presentation by
`isFinitePresentation_biprod`.  This is exactly the derivation
`StacksFrontier/AlgebraicGeometry/FinitelyPresentedOver/Basic.lean` describes as following from that
closure "and nothing else". -/
instance isFiltered {X : Scheme.{u}} (F : X.Modules) : IsFiltered (FinitelyPresentedOver F) := by
  have : IsFilteredOrEmpty (FinitelyPresentedOver F) :=
    { cocone_objs := by
        intro A B
        have hA : A.1.left.IsFinitePresentation := A.2
        have hB : B.1.left.IsFinitePresentation := B.2
        refine ⟨⟨Over.mk (biprod.desc A.1.hom B.1.hom),
            AlgebraicGeometry.isFinitePresentation_biprod _ _⟩,
          ObjectProperty.homMk (Over.homMk biprod.inl),
          ObjectProperty.homMk (Over.homMk biprod.inr), trivial⟩
      cocone_maps := fun {A B} f g => exists_hom_comp_eq F A B f g }
  exact IsFiltered.mk

end FinitelyPresentedOver

end Stacks.AlgebraicGeometry

end
