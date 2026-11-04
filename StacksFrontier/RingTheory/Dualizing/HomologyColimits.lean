module

public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.Limits
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import StacksFrontier.Homology.HomologyColimit

/-!
# Homology commutes with exact colimits

In an abelian category in which colimits of shape `J` are exact, the homology of short complexes
and the homology of homological complexes both commute with colimits of shape `J`.

## Main results

* `StacksDraft.HomologyColimits.preservesColimitsOfShape_homologyFunctor`: homology of
  homological complexes commutes with colimits of shape `J` when those colimits are exact.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace StacksDraft.HomologyColimits

section

variable {A : Type*} [Category A] [Abelian A]

/-- Homology of homological complexes commutes with colimits of shape `J` when colimits of shape
`J` are exact. -/
lemma preservesColimitsOfShape_homologyFunctor {J : Type*} [Category J]
    [HasColimitsOfShape J A] [HasExactColimitsOfShape J A]
    {ι : Type*} (c : ComplexShape ι) (i : ι) :
    PreservesColimitsOfShape J (HomologicalComplex.homologyFunctor A c i) :=
  have := Stacks.HomologyColimit.preservesColimitsOfShape_shortComplexFunctor (A := A) (J := J) c i
  have :=
    Stacks.HomologyColimit.preservesColimitsOfShape_shortComplex_homologyFunctor (A := A) (J := J)
  preservesColimitsOfShape_of_natIso (HomologicalComplex.homologyFunctorIso A c i).symm

end

end StacksDraft.HomologyColimits

end
