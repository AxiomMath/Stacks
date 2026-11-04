module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitVectorBundleGroupoid
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.GeneratorAlmostBlowUpStackSufficiency
public import StacksFrontier.CategoryTheory.Sites.Descent.CoGrothendieckIsStack

/-!
# The structure functor of Stacks Tag 0EXE is a stack exactly when its pseudofunctor is

`StacksFrontier/AlgebraicGeometry/Descent/FrobeniusColimitVectorBundleGroupoid.lean` builds the
pseudofunctor in groupoids `AlgebraicGeometry.frobeniusVectorBundleGroupoidPseudofunctor` of
finite locally free `colim_F 𝒪_U`-modules and the structure functor
`AlgebraicGeometry.frobeniusVectorBundleGroupoidFibration` it presents, and
`StacksFrontier/AlgebraicGeometry/Descent/FrobeniusColimitVectorBundleGroupoidStack.lean` and
`StacksFrontier/AlgebraicGeometry/Descent/FrobeniusColimitVectorBundleGroupoidFullSubcategory.lean` carry descent statements *about
the pseudofunctor* down from the pseudofunctor of all Frobenius-colimit modules.  The conditions
of Stacks Tag 0EX9, however, and its conclusion, are statements about the *structure functor*.
This file crosses between the two, by
`CategoryTheory.Pseudofunctor.CoGrothendieck.isStack_forget_iff`.

## Main results

* `AlgebraicGeometry.isStack_frobeniusVectorBundleGroupoidFibration_iff`: **the structure functor
  of Stacks Tag 0EXE is a stack for a topology exactly when its pseudofunctor in groupoids is.**
* `AlgebraicGeometry.isStackInGroupoids_frobeniusVectorBundleGroupoidFibration`: **it is a stack
  in groupoids as soon as its pseudofunctor in groupoids is a stack**, the fibred-in-groupoids
  condition being `AlgebraicGeometry.frobeniusVectorBundleGroupoidFibration_isFiberedInGroupoids`.
* `AlgebraicGeometry.isZariskiStackInGroupoids_frobeniusVectorBundleGroupoidFibration`: the same
  read at the Zariski topology, which is condition (1) of Stacks Tag 0EX9.
* `isStackInGroupoids_frobeniusVectorBundleGroupoidFibration_of_generatorSquares`: **the four
  conditions of Stacks Tag 0EX9 give h-descent in groupoids for finite locally free
  Frobenius-colimit modules**, which is the main clause of Stacks Tag 0EXE.  This is
  `AlgebraicGeometry.BigHOver.isStackInGroupoids_of_generatorSquares` at the structure functor;
  the four conditions are not proved here.

## Implementation notes

The crossing is not formal bookkeeping.  `CategoryTheory.Functor.IsStack` of the structure functor
is compared by `CategoryTheory.Functor.isStack_pullbackPseudofunctor_iff` with the *pullback*
pseudofunctor of Stacks 02XO, whose transition functor is a chosen cartesian pullback, and that
pseudofunctor is not the one the fibres were built from; the identification of the two is
`CategoryTheory.Pseudofunctor.CoGrothendieck.pullbackCmpStrongTrans`.

## References

* [Stacks Project, Tag 0EXE](https://stacks.math.columbia.edu/tag/0EXE)
* [Stacks Project, Tag 0EX9](https://stacks.math.columbia.edu/tag/0EX9)
* [Stacks Project, Tag 02ZI](https://stacks.math.columbia.edu/tag/02ZI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Pseudofunctor Opposite
open Stacks.Frobenius

namespace AlgebraicGeometry

universe u

variable (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (p : ℕ) [Fact p.Prime]
  (hpS : IsInCharacteristic S p)

include hpS

/-- **The structure functor of Stacks Tag 0EXE is a stack in the sense of Stacks 026F for a
topology exactly when its pseudofunctor in groupoids is a stack for that topology.** -/
theorem isStack_frobeniusVectorBundleGroupoidFibration_iff
    (J : GrothendieckTopology (BigHOver B S hS)) :
    (frobeniusVectorBundleGroupoidFibration B S hS p hpS).IsStack J ↔
      (frobeniusVectorBundleGroupoidPseudofunctor B S hS p hpS).IsStack J :=
  CoGrothendieck.isStack_forget_iff.{u, u + 1, u, u + 1}
    (frobeniusVectorBundleGroupoidPseudofunctor B S hS p hpS) J

/-- **The structure functor of Stacks Tag 0EXE is a stack in groupoids for a topology as soon as
its pseudofunctor in groupoids is a stack for that topology.**

Condition (1) of Stacks 02ZI is
`AlgebraicGeometry.frobeniusVectorBundleGroupoidFibration_isFiberedInGroupoids` and the other two
come from `AlgebraicGeometry.isStack_frobeniusVectorBundleGroupoidFibration_iff` through
`CategoryTheory.Functor.IsStack.isStackInGroupoids`. -/
theorem isStackInGroupoids_frobeniusVectorBundleGroupoidFibration
    {J : GrothendieckTopology (BigHOver B S hS)}
    (hF : (frobeniusVectorBundleGroupoidPseudofunctor B S hS p hpS).IsStack J) :
    (frobeniusVectorBundleGroupoidFibration B S hS p hpS).IsStackInGroupoids.{u + 1} J :=
  CoGrothendieck.isStackInGroupoids_forget.{u + 1, u, u + 1, u, u + 1}
    (frobeniusVectorBundleGroupoidPseudofunctor B S hS p hpS) hF
    (frobeniusVectorBundleGroupoidFibration_isFiberedInGroupoids B S hS p hpS)

/-- **Condition (1) of Stacks Tag 0EX9 for the structure functor of Stacks Tag 0EXE holds as soon
as its pseudofunctor in groupoids is a stack for the Zariski topology on `(Sch/S)_h`.**  This is
`AlgebraicGeometry.isStackInGroupoids_frobeniusVectorBundleGroupoidFibration` at
`AlgebraicGeometry.BigHOver.zariskiTopology`, which is the topology that condition names. -/
theorem isZariskiStackInGroupoids_frobeniusVectorBundleGroupoidFibration
    (hF : (frobeniusVectorBundleGroupoidPseudofunctor B S hS p hpS).IsStack
      (BigHOver.zariskiTopology B S hS)) :
    BigHOver.IsZariskiStackInGroupoids B S hS
      (frobeniusVectorBundleGroupoidFibration B S hS p hpS) :=
  isStackInGroupoids_frobeniusVectorBundleGroupoidFibration B S hS p hpS hF

/-- **The four conditions of Stacks Tag 0EX9 give h-descent in groupoids for finite locally free
Frobenius-colimit modules**, which is the main clause of Stacks Tag 0EXE.

This is `AlgebraicGeometry.BigHOver.isStackInGroupoids_of_generatorSquares` read at
`AlgebraicGeometry.frobeniusVectorBundleGroupoidFibration`, whose fibred-category instance the
Grothendieck construction supplies.  None of the four conditions is proved here: they are
Zariski-stackness of the structure functor, effective descent along a flat proper
finitely-presented surjection onto an affine object, and the two almost-blow-up conditions of
Examples 0EVG and 0EVH. -/
theorem isStackInGroupoids_frobeniusVectorBundleGroupoidFibration_of_generatorSquares
    (h1 : BigHOver.IsZariskiStackInGroupoids B S hS
      (frobeniusVectorBundleGroupoidFibration B S hS p hpS))
    (h2 : BigHOver.IsAffineFlatProperFinitePresentationDescent B S hS
      (frobeniusVectorBundleGroupoidFibration B S hS p hpS))
    (h3 : BigHOver.IsOneGeneratorAlmostBlowUpStack B S hS
      (frobeniusVectorBundleGroupoidFibration B S hS p hpS))
    (h4 : BigHOver.IsTwoGeneratorAlmostBlowUpStack B S hS
      (frobeniusVectorBundleGroupoidFibration B S hS p hpS)) :
    (frobeniusVectorBundleGroupoidFibration B S hS p hpS).IsStackInGroupoids.{u + 1}
      (BigHOver.topology B S hS) :=
  BigHOver.isStackInGroupoids_of_generatorSquares h1 h2 h3 h4

end AlgebraicGeometry

end
