module

public import StacksFrontier.RingTheory.Dualizing.LocalCohomology.RightAdjoint

/-!
# Local cohomology with support in a closed subset of the spectrum

Let `I` be a finitely generated ideal of a commutative ring `A`, and let `Z = V(I)` be the
corresponding closed subset of `Spec(A)`. Local cohomology with support in `Z` is the functor
`RΓ_Z` from `D(A)` to the full subcategory of `D(A)` whose objects have `I`-power-torsion
cohomology modules; it is the right adjoint to the inclusion of that subcategory.

## Main definitions

* `Dualizing.localCohomologyFunctor` — the functor `RΓ_Z`.

## Implementation notes

The ideal indexes the functor because it determines the closed subset `Z = V(I)`;
functoriality in the derived object is part of the bundled functor. The underlying
construction and the adjunction are `Dualizing.localCohomologyRightAdjoint`, and this module
only names the right adjoint it produces.

## References

* [Stacks Project, Tag 0A6Q](https://stacks.math.columbia.edu/tag/0A6Q)
-/

@[expose] public noncomputable section

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Dualizing

/-- **Stacks 0A6Q.** Local cohomology with support in `V(I)`, valued in the full subcategory of
derived objects with `I`-power-torsion cohomology. -/
@[stacks 0A6Q "the functor"]
noncomputable def localCohomologyFunctor
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) :
    DerivedCategory (ModuleCat.{v} A) ⥤
      PowerTorsionDerivedCategory A I hI :=
  (localCohomologyRightAdjoint A I hI).1

end Dualizing
