module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.AdjunctionUnconditional
import StacksCore.Tactic.StacksAttribute

/-!
# The ordinary and the derived pullback–pushforward counit of a morphism of ringed spaces

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces and let `K` be a complex of
`𝒪_X`-modules.  The comparison `Lf^* ⟶ f^*` of the derived pullback with degreewise pullback,
the comparison `f_* ⟶ Rf_*` of degreewise pushforward with the derived pushforward, the counit
of the derived adjunction `Lf^* ⊣ Rf_*` and the ordinary counit `f^* f_* ⟶ id` form a square

```
Lf^* f_* K ⟶ f^* f_* K
    ↓              ↓
Lf^* Rf_* K ⟶      K
```

in `D(𝒪_X)`, and this square commutes.  That is
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction_counit_fac`, where it is
proved for an arbitrary morphism of ringed spaces and read as the compatibility of the derived
counit with the ordinary one; its upper edge is the comparison `Lf^* ⟶ f^*` at `f_* K`, its left
edge is `Lf^*` applied to the comparison `f_* ⟶ Rf_*`, its lower edge is the derived counit and
its right edge is the ordinary counit.  Nothing is restated here.

The statement is taken at an object of the unbounded homotopy category rather than at a cochain
complex, which is the form the comparison maps of the two derived functors take and is more
general: a complex gives such an object through `HomotopyCategory.quotient`.

## References

* [Stacks Project, Tag 0FP1](https://stacks.math.columbia.edu/tag/0FP1)
-/

@[expose] public section

add_to_stacks 0FP1 "the square of the ordinary and the derived counit commutes"
  Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction_counit_fac

end
