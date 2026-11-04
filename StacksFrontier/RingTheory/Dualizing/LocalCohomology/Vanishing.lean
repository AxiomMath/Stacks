module

public import StacksFrontier.RingTheory.Dualizing.DerivingTorsion.Vanishing
public import StacksCore.Tactic.StacksAttribute

/-!
# Vanishing of local cohomology on modules where the support ideal is inverted

Let `I` be a finitely generated ideal of a commutative ring `A`. The local cohomology of an
object of `D(A)` with support in `V(I)` vanishes as soon as some element of `I` acts invertibly
on that object — in particular for a complex of modules over a localization `A_f` with `f ∈ I`.

## Main results

* `Dualizing.localCohomology_isZero_of_isIso_smul` carries this vanishing; it is stated and
  proved in `StacksFrontier.RingTheory.Dualizing.DerivingTorsion.Vanishing`.

## Implementation notes

The hypothesis `IsIso (f • 𝟙 K)` is the derived-category form of "`f` acts invertibly", and
includes the case of a complex of `A_f`-modules. Local cohomology takes values in the full
subcategory of objects whose cohomology modules are `I`-power torsion.

## References

* [Stacks Project, Tag 0A6S](https://stacks.math.columbia.edu/tag/0A6S)
-/

@[expose] public section

add_to_stacks 0A6S Dualizing.localCohomology_isZero_of_isIso_smul
