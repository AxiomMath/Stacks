/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.FormalScheme.TwistedDoubleIdealsOfDefinition
public import StacksFrontier.AlgebraicGeometry.FormalScheme.TwistedDoubleObstruction

/-!
# The "if" direction of Stacks 0AIW is false for sectionwise ideals of definition

Remark 0AIW of the Stacks project states that for a quasi-compact formal scheme `𝔛`, the functor
of points `h_𝔛` is a colimit of schemes along thickenings, as in Lemma 0AIU, if and only if `𝔛`
has a fundamental system of ideals of definition. With the source's definition of an ideal of
definition, sectionwise (an ideal sheaf whose ideals of sections over the affine formal opens are
ideals of definition), the "if" direction is false.

The counterexample is the twisted double `AlgebraicGeometry.TwistedDouble.𝔛`: two copies of
`Spf R⟦X⟧`, over a local ring `R` with infinitely many points `q n` with `D(y n) = {q n}`, glued
along `W = ⨆ D(y n)` by the substitutions `X ↦ X - ε n` with `ε n` nilpotent of order `n + 1`
(`AlgebraicGeometry.TwistedDouble.D`).

* Every point of `𝔛` has a smallest open neighbourhood, so ideal sheaves can be prescribed on the
  smallest neighbourhoods. This gives a fundamental system of ideals of definition
  (`AlgebraicGeometry.TwistedDouble.exists_isFundamentalSystemOfIdealsOfDefinitionOn`).
* `h_𝔛` is not a colimit (`AlgebraicGeometry.TwistedDouble.not_isFppfColimitOfThickenings`). By
  `AlgebraicGeometry.FormalScheme.isFppfColimitOfThickenings_iff`, a colimit would give a
  fundamental system of ideals of definition cut out by their sections over the affine formal
  opens. Let `J` be such an ideal sheaf whose sections over the copy `U true` are killed by the
  point at `(X)` of that copy. The sections of `J` over the copy `U false` form an open ideal, so
  they contain the section `X ^ M` of that copy for some `M`. Over the point `η n`, this section
  is `(X - ε n) ^ M` in the chart of the copy `true`. For `n ≥ M` the point at `(X)` of the copy
  `true` does not kill it, since `ε n ^ M ≠ 0`. This contradicts the cut-out condition at
  `U true`.

## Main results

* `AlgebraicGeometry.FormalScheme.not_forall_isFppfColimitOfThickenings_of_exists`: the "if"
  direction of Stacks 0AIW, as printed, is false.

## References

* [Stacks Project, Tag 0AIW](https://stacks.math.columbia.edu/tag/0AIW)
* [Stacks Project, Tag 0AIU](https://stacks.math.columbia.edu/tag/0AIU)
-/

@[expose] public section

namespace AlgebraicGeometry

open LocallyTopologicallyRingedSpace

/-- **Stacks 0AIW, the "if" direction as printed, is false.** There is a quasi-compact formal
scheme `𝔛` à la EGA (the twisted double `AlgebraicGeometry.TwistedDouble.𝔛`) which has a
fundamental system of ideals of definition, in the source's sectionwise sense, but whose functor
of points `h_𝔛` is not a colimit of schemes along thickenings in fppf sheaves, as in Stacks 0AIU.

The corrected form is `AlgebraicGeometry.FormalScheme.isFppfColimitOfThickenings_iff`, where the
ideals of definition are cut out by their sections over the affine formal opens. -/
@[stacks 0AIW "the if direction as printed (sectionwise ideals of definition) is false: a \
quasi-compact formal scheme with a fundamental system of ideals of definition whose functor of \
points h_𝔛 is not a colimit of schemes as in Lemma 0AIU (colimit in fppf sheaves); corrected \
form: FormalScheme.isFppfColimitOfThickenings_iff"]
theorem FormalScheme.not_forall_isFppfColimitOfThickenings_of_exists :
    ¬ ∀ (X : FormalScheme.{0}) [CompactSpace X.obj],
      (∃ 𝒮 : Set (IdealSheaf X.obj),
        IsFundamentalSystemOfIdealsOfDefinitionOn 𝒮 (IsAffineFormalOpen X.obj)) →
        X.toMcQuillanFormalScheme.IsFppfColimitOfThickenings :=
  fun h => TwistedDouble.not_isFppfColimitOfThickenings
    (h TwistedDouble.𝔛 TwistedDouble.exists_isFundamentalSystemOfIdealsOfDefinitionOn)

/-- **Stacks 0AIV, the "if" direction as printed, is false.** There is a formal scheme `𝔛` in the
sense of McQuillan (the twisted double `AlgebraicGeometry.TwistedDouble.𝔛`, a formal scheme à la
EGA) which has a fundamental system of weak ideals of definition, in the source's sectionwise
sense, but whose functor of points `h_𝔛` is not a colimit of schemes along thickenings in fppf
sheaves, as in Stacks 0AIU. On a formal scheme à la EGA the weak affine formal opens are the
affine formal opens, and a fundamental system of ideals of definition is one of weak ideals of
definition, so the fundamental system of
`AlgebraicGeometry.TwistedDouble.exists_isFundamentalSystemOfIdealsOfDefinitionOn` serves.

The corrected form is
`McQuillanFormalScheme.isFppfColimitOfThickenings_iff_exists_isFundamentalSystem`,
where the weak ideals of definition are cut out by their sections over the affine formal opens. -/
@[stacks 0AIV "the statement as printed is false: the if direction, for sectionwise weak ideals \
of definition, fails for the twisted double, a formal scheme with a fundamental system of \
(weak) ideals of definition whose functor of points h_𝔛 is not a colimit of schemes as in \
Lemma 0AIU (colimit in fppf sheaves); the corrected form is \
McQuillanFormalScheme.isFppfColimitOfThickenings_iff_exists_isFundamentalSystem"]
theorem McQuillanFormalScheme.not_forall_isFppfColimitOfThickenings_of_exists :
    ¬ ∀ 𝔛 : McQuillanFormalScheme.{0},
      (∃ 𝒮 : Set (IdealSheaf 𝔛.obj),
        IsFundamentalSystemOfWeakIdealsOfDefinitionOn 𝒮 (IsWeakAffineFormalOpen 𝔛.obj)) →
        𝔛.IsFppfColimitOfThickenings := by
  intro h
  obtain ⟨𝒮, h𝒮⟩ := TwistedDouble.exists_isFundamentalSystemOfIdealsOfDefinitionOn
  refine TwistedDouble.not_isFppfColimitOfThickenings (h TwistedDouble.𝔛.toMcQuillanFormalScheme
    ⟨𝒮, ?_⟩)
  change IsFundamentalSystemOfWeakIdealsOfDefinitionOn 𝒮
    (IsWeakAffineFormalOpen TwistedDouble.𝔛.obj)
  rw [TwistedDouble.𝔛.property.isWeakAffineFormalOpen_eq]
  exact
    isFundamentalSystemOfWeakIdealsOfDefinitionOn_of_isFundamentalSystemOfIdealsOfDefinitionOn h𝒮

end AlgebraicGeometry

end
