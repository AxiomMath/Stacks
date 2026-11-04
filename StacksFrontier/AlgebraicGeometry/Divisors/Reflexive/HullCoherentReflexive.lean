module

public import StacksFrontier.AlgebraicGeometry.Divisors.ReflexiveEquivalence.StalkDescent
public import StacksFrontier.AlgebraicGeometry.ReflexiveHull.DualStalk

/-!
# The reflexive hull of a coherent module is coherent and reflexive

On an integral locally Noetherian scheme the reflexive hull `F^∨∨` of a coherent module is
again coherent, and it is reflexive.  Coherence holds on any locally Noetherian scheme and is
the dual of a coherent module being coherent, applied twice; reflexivity is the statement that
a dual is reflexive, applied to `F^∨`.

## Main results

* `AlgebraicGeometry.isReflexive_reflexiveHull`: the reflexive hull of a coherent module on an
  integral locally Noetherian scheme is reflexive.

## Implementation notes

The reflexivity of a dual is
`Stacks.AlgebraicGeometry.ReflexiveModules.isReflexive_dualSheaf_of_isFinitePresentation`, whose
finite-presentation hypotheses are discharged from coherence of the iterated duals, which is
`Stacks.AlgebraicGeometry.ReflexiveEquivalence.isCoherent_dualSheaf`.  Coherence of the hull is
already in the library as
`Stacks.AlgebraicGeometry.ReflexiveEquivalence.isCoherent_doubleDual`, so it is not restated
here.

## References

* [Stacks Project, Tag 0EBH](https://stacks.math.columbia.edu/tag/0EBH)
-/

@[expose] public section

open CategoryTheory
open Stacks.AlgebraicGeometry.ReflexiveEquivalence
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace AlgebraicGeometry

/-- The reflexive hull `F^∨∨` of a coherent module on an integral locally Noetherian scheme is
reflexive: it is the dual of the coherent module `F^∨`, and duals of coherent modules are
reflexive. -/
@[stacks 0EBH "hull"]
theorem isReflexive_reflexiveHull (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (F : X.Modules) [_root_.SheafOfModules.IsCoherent F] : IsReflexive (reflexiveHull F) := by
  have h1 : _root_.SheafOfModules.IsCoherent (dualSheaf F) := isCoherent_dualSheaf F
  have h2 : _root_.SheafOfModules.IsCoherent (dualSheaf (dualSheaf F)) :=
    isCoherent_dualSheaf (dualSheaf F)
  have h3 : _root_.SheafOfModules.IsCoherent (dualSheaf (dualSheaf (dualSheaf F))) :=
    isCoherent_dualSheaf (dualSheaf (dualSheaf F))
  have : (dualSheaf F).IsFiniteType := _root_.SheafOfModules.IsCoherent.isFiniteType
  have : (dualSheaf F).IsFinitePresentation := _root_.isFinitePresentation_of_isCoherent _
  have : (dualSheaf (dualSheaf F)).IsFinitePresentation :=
    _root_.isFinitePresentation_of_isCoherent _
  have : (dualSheaf (dualSheaf (dualSheaf F))).IsFinitePresentation :=
    _root_.isFinitePresentation_of_isCoherent _
  exact isReflexive_dualSheaf_of_isFinitePresentation X (dualSheaf F)

end AlgebraicGeometry

end
