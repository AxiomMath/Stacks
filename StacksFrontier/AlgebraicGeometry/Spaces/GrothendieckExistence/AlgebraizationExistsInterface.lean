module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.AlgebraizationExists
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.Statements

/-!
# The interface statement of the existence half of Stacks 08BB

`AlgebraicGeometry.Space.CompletionAlgebraizationExists` is the statement of the existence half
of Stacks 08BB that the other Grothendieck existence modules build against.  It is discharged
here by `AlgebraicGeometry.Space.exists_algebraization`.

## Main results

* `AlgebraicGeometry.Space.completionAlgebraizationExists` — the interface statement holds for
  every algebraic space.

## References

* [Stacks Project, Tag 08BB](https://stacks.math.columbia.edu/tag/08BB)
-/

@[expose] public noncomputable section

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The interface statement `AlgebraicGeometry.Space.CompletionAlgebraizationExists` of the
existence half of Stacks 08BB holds for every algebraic space. -/
theorem completionAlgebraizationExists (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS) : CompletionAlgebraizationExists hZ X :=
  fun hN 𝓘 hI _ _ _ α hα => exists_algebraization B S hS X.1 X.2 𝓘 hI hZ hN α hα

end AlgebraicGeometry.Space

end
