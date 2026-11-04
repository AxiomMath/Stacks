module

public import Mathlib.CategoryTheory.Limits.Connected
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.BinaryProductInstance
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.ChangeBaseConnectedLimits
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.BigComparison

/-!
# `Cris(X/S) ⥤ Cris(X'/S')` commutes with fibre products and equalizers

The functor `smallChangeBase` of [Stacks, Tag 07KL] is cut out of the change of divided power
base `changeBase` of [Stacks, Tag 07IC] by restricting to the objects whose structure map to the
scheme is an open immersion: it is `ObjectProperty.lift` of `ι ⋙ changeBase` through the full
subcategory `Cris(X'/S') ⊆ CRIS(X'/S')`.  So it commutes with a limit as soon as `changeBase`
does and the inclusion of the small site into the big one does, the latter being
[Stacks, Tag 07IJ] — `Crystalline.GlobalCrystallineSituation.CrystallineThickening.ι` is fully
faithful, hence reflects limits, and the limits of `Cris(X/S)` are computed in `CRIS(X/S)`.

`Crystalline.GlobalCrystallineSituation.changeBase_preservesLimitsOfShape` supplies the first
half for every connected shape.  The two shapes wanted here are `WalkingCospan` and
`WalkingParallelPair`, both connected, so **change of divided power base preserves the fibre
products and the equalizers of the crystalline site**.

Equalizers are not obtained from products here, and that matters: the existing proof that
`CRIS(X/S)` *has* equalizers goes through products of pairs
(`...hasNonemptyFiniteLimits_thickening`, by way of
`CategoryTheory.Limits.hasEqualizers_of_hasPullbacks_and_binary_products`), and products of pairs
are a shape the argument used here cannot reach — `WalkingPair` is not connected, and a product
in `CRIS(X/S)` has for ambient divided power scheme an envelope of `T₁ ×_S T₂`, built over the
base that `f` moves.  Existence and preservation are separate questions, and only the first one
needs products.

## Main results

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation`.

* `smallChangeBase_preservesLimitsOfShape` — `Cris(X/S) ⥤ Cris(X'/S')` commutes with limits of
  any connected finite shape of which `CRIS(X/S)` has limits.
* `smallChangeBase_preservesPullbacks` and `smallChangeBase_preservesEqualizers` — the two shapes
  of [Stacks, Tag 07I9] at which that is wanted, as instances.

## Implementation notes

The reduction is `CategoryTheory.Limits.preservesLimitsOfShape_of_reflects_of_preserves` applied
to `smallChangeBase ⋙ ι`, which is *definitionally* `ι ⋙ changeBase`
(`CategoryTheory.ObjectProperty.liftCompιIso` is the identity isomorphism), so no transport along
a comparison isomorphism is involved.

No `@[stacks]` attribute is placed.  [Stacks, Tag 07KL] states the functor and its full
faithfulness, both already carried by
`Crystalline.GlobalCrystallineSituation.smallChangeBase` and `...smallChangeBaseFullyFaithful`;
exactness properties of it are not part of the tag.

## References

* [Stacks Project, Tag 07KL](https://stacks.math.columbia.edu/tag/07KL)
* [Stacks Project, Tag 07IC](https://stacks.math.columbia.edu/tag/07IC)
* [Stacks Project, Tag 07IJ](https://stacks.math.columbia.edu/tag/07IJ)
* [Stacks Project, Tag 07I9](https://stacks.math.columbia.edu/tag/07I9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation

variable (S S' : GlobalCrystallineSituation.{u}) (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
  (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber)
  [IsOpenImmersion g]

/-- **`Cris(X/S) ⥤ Cris(X'/S')` commutes with limits of any connected finite shape that
`CRIS(X/S)` has limits of.**  Composed with the inclusion of the small site into the big one it
is `ι ⋙ changeBase`, which commutes with such limits by [Stacks, Tag 07IJ] and
`Crystalline.GlobalCrystallineSituation.changeBase_preservesLimitsOfShape`; and the inclusion
`Cris(X'/S') ⥤ CRIS(X'/S')` is fully faithful, so it reflects them. -/
theorem smallChangeBase_preservesLimitsOfShape (J : Type) [SmallCategory J] [FinCategory J]
    [IsConnected J] [HasLimitsOfShape J (Thickening S)] :
    PreservesLimitsOfShape J (smallChangeBase S S' f g h) := by
  have : PreservesLimitsOfShape J (CrystallineThickening.ι S) := inferInstance
  have : PreservesLimitsOfShape J (changeBase S S' f g h) :=
    changeBase_preservesLimitsOfShape J
  have : PreservesLimitsOfShape J
      (smallChangeBase S S' f g h ⋙ CrystallineThickening.ι S') :=
    inferInstanceAs (PreservesLimitsOfShape J
      (CrystallineThickening.ι S ⋙ changeBase S S' f g h))
  exact preservesLimitsOfShape_of_reflects_of_preserves (smallChangeBase S S' f g h)
    (CrystallineThickening.ι S')

/-- **Change of divided power base preserves the fibre products of the crystalline site**,
`WalkingCospan` being connected. -/
instance smallChangeBase_preservesPullbacks :
    PreservesLimitsOfShape WalkingCospan (smallChangeBase S S' f g h) :=
  smallChangeBase_preservesLimitsOfShape S S' f g h WalkingCospan

/-- **Change of divided power base preserves the equalizers of the crystalline site**,
`WalkingParallelPair` being connected.  The equalizers are not built from products of pairs here;
only their *existence* in `CRIS(X/S)` is, and that is the hypothesis
`HasLimitsOfShape WalkingParallelPair (Thickening S)` discharged by
`CategoryTheory.Limits.hasEqualizers_of_hasPullbacks_and_binary_products`. -/
instance smallChangeBase_preservesEqualizers :
    PreservesLimitsOfShape WalkingParallelPair (smallChangeBase S S' f g h) :=
  haveI : HasEqualizers (Thickening S) := hasEqualizers_of_hasPullbacks_and_binary_products
  smallChangeBase_preservesLimitsOfShape S S' f g h WalkingParallelPair

end Crystalline.GlobalCrystallineSituation

end

end
