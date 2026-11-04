module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Morphisms from reduced schemes into closed subschemes

Let `f : X ⟶ Z` be a closed immersion and let `g : Y ⟶ Z` be a morphism from a reduced scheme
whose image lies in the image of `f`. Then `g` factors through `f`. Indeed the kernel of `g` is
the ideal sheaf of functions vanishing on the image of `g`, because `Y` is reduced, and it
contains the ideal sheaf of `f`, whose support is the image of `f`.

## Main results

* `AlgebraicGeometry.IsClosedImmersion.ker_le_ker_of_range_subset`: the kernel of the closed
  immersion is contained in the kernel of the morphism from the reduced scheme.
* `AlgebraicGeometry.IsClosedImmersion.liftOfReduced`: the factorization, with
  `AlgebraicGeometry.IsClosedImmersion.liftOfReduced_fac`.

## References

* [Stacks Project, Tag 0356](https://stacks.math.columbia.edu/tag/0356)
-/

@[expose] public section

noncomputable section

open CategoryTheory

namespace AlgebraicGeometry

universe u

namespace IsClosedImmersion

variable {X Y Z : Scheme.{u}} (f : X ⟶ Z) [IsClosedImmersion f] (g : Y ⟶ Z) [IsReduced Y]

/-- For `Y` reduced and the image of `g` inside the image of the closed immersion `f`, the ideal
sheaf of `f` is contained in the kernel of `g`. -/
theorem ker_le_ker_of_range_subset (h : Set.range g ⊆ Set.range f) : f.ker ≤ g.ker := by
  rw [← Scheme.IdealSheafData.map_bot g, ← Scheme.nilradical_eq_bot (X := Y),
    ← Scheme.IdealSheafData.vanishingIdeal_top, Scheme.IdealSheafData.map_vanishingIdeal,
    ← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal]
  rw [← SetLike.coe_subset_coe, Scheme.Hom.support_ker]
  simpa using closure_mono h

/-- For `Y` reduced and the image of `g` inside the image of the closed immersion `f`, the
morphism `Y ⟶ X` through which `g` factors. -/
@[ega "I 5.2.2", sga "3 VIB 7.1" "partial"]
def liftOfReduced (h : Set.range g ⊆ Set.range f) : Y ⟶ X :=
  IsClosedImmersion.lift f g (ker_le_ker_of_range_subset f g h)

/-- The composite of `liftOfReduced f g h` with the closed immersion `f` is `g`. -/
@[reassoc (attr := simp)]
theorem liftOfReduced_fac (h : Set.range g ⊆ Set.range f) : liftOfReduced f g h ≫ f = g :=
  IsClosedImmersion.lift_fac _ _ _

end IsClosedImmersion

end AlgebraicGeometry
