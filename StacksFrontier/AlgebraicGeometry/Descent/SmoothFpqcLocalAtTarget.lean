module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcLocalAtTarget

/-!
# Smoothness of morphisms of schemes is fpqc local on the base (Stacks 02VL)

Smoothness of a morphism of schemes can be checked after any fpqc covering of the target.

## Main definitions

No new definitions are introduced.

## Main results

* `Stacks.Descent.smooth_isLocalAtTarget_fpqc`: **Stacks 02VL**.

## Implementation notes

This is the criterion `Stacks.Descent.isLocalAtTarget_fpqcPrecoverage` (Tag 02KP) at
`P = AlgebraicGeometry.Smooth`. Of its three hypotheses, stability under base change and
descent along surjective flat quasi-compact morphisms are Mathlib instances for smoothness;
Zariski locality on the target is supplied here from the affine-local description of smoothness
by a ring-map property, which is not registered as an instance.

Stability under *flat* base change has to be derived by name from
`Stacks.Descent.isStableUnderFlatBaseChange_of_isStableUnderBaseChange`: the morphism arguments
of `AlgebraicGeometry.Smooth` are implicit rather than strict implicit, so instance search cannot
apply that instance on its own. See its docstring.

The statement is an instance, since what needs it — fpqc locality for morphisms of algebraic
spaces, Tag 0429 — reaches it through the instance arguments of Tag 03MJ.

## References

* [Stacks Project, Tag 02VL](https://stacks.math.columbia.edu/tag/02VL)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Descent

/-- **Stacks 02VL.** Smoothness of morphisms of schemes is local on the base for the fpqc
topology. -/
@[stacks 02VL, sga "3 VIB 2.1.2" "partial", sga "3 VIIA 8.3.1" "Final descent step"]
instance smooth_isLocalAtTarget_fpqc :
    MorphismProperty.IsLocalAtTarget (@Smooth : MorphismProperty Scheme.{u})
      Scheme.fpqcPrecoverage :=
  have : IsZariskiLocalAtTarget (@Smooth : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Smooth)
  have := isStableUnderFlatBaseChange_of_isStableUnderBaseChange
    (@Smooth : MorphismProperty Scheme.{u})
  isLocalAtTarget_fpqcPrecoverage _

end Stacks.Descent

end
