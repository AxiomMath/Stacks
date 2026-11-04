module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.BaseChangeComparisonSections
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.BaseChangeTranspose

/-!
# The derived base change map as a component of the mate square

The derived base change map `Lg^*Rπ_*M ⟶ Rπ'_*Lg₀^*M` of [Stacks, Tag 08HY] for a commutative
square of ringed spaces, `Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap`, is by
definition the component at `M` of the mate square
`Stacks.Cohomology.DerivedBaseChange.Mate.derivedBaseChangeSquare` of the two derived adjunctions.

## Main results

* `Stacks.Cohomology.SectionsPullback.derivedBaseChangeMap_eq_mate`: the derived base change map
  at `M` is the component at `M` of the mate square.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces Stacks.Cohomology.DerivedSectionsLeray
open Stacks.Cohomology.DerivedBaseChange Stacks.DerivedPullback.Composition

universe u

namespace Stacks.Cohomology.SectionsPullback

attribute [local instance 10000] HasDerivedCategory.standard

variable {X' X Z W : RingedSpace.{u, u}} (g₀ : X' ⟶ X) (π' : X' ⟶ Z) (π : X ⟶ W) (g : Z ⟶ W)
  (sq : g₀ ≫ π = π' ≫ g)

/-- The derived base change map of [Stacks, Tag 08HY] is, by definition, the component at `M` of
the mate square `Stacks.Cohomology.DerivedBaseChange.Mate.derivedBaseChangeSquare`. -/
theorem derivedBaseChangeMap_eq_mate
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    derivedBaseChangeMap g₀ π' π g sq M =
      (Mate.derivedBaseChangeSquare (derivedAdjunction π) (derivedAdjunction π')
        (derivedPullbackCompIsoLeft g₀ π' π g sq) (derivedPullbackCompIsoCanonical g₀ π)).app M :=
  (show derivedBaseChangeMap g₀ π' π g sq M =
      Mate.derivedBaseChangeMap (derivedAdjunction π) (derivedAdjunction π')
        (derivedPullbackCompIsoLeft g₀ π' π g sq) (derivedPullbackCompIsoCanonical g₀ π) M
    from rfl).trans rfl

end Stacks.Cohomology.SectionsPullback

end
