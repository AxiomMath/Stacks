module

public import StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.GeneratedInDegreeOne
public import StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.Basic
public import StacksFrontier.AlgebraicGeometry.TwistMapsInvertible.Basic

/-!
# Consumers of degree-one generation for `Sym(E)`

`Stacks.SymGraded.adjoin_grading_one_eq_top` is the hypothesis that the relative-Proj twist
theory of Tag 01O4 carries as an argument and as a `Fact`. **This file discharges it at the
symmetric algebra**, so that the invertibility of the twists on the projective bundle
`P(E) = Proj_X(Sym(E))` of a quasi-coherent module is unconditional except for the twist datum
itself.

## Main results

* `Stacks.SymGraded.fact_isGeneratedInDegreeOne_schemeSheafGradedAlgebra`:
  `Stacks.SymGraded.isGeneratedInDegreeOne_schemeSheafGradedAlgebra` as a `Fact`,
  which is the form
  `Stacks.AlgebraicGeometry.TwistMapsInvertible.relativeProjTwists_isInvertible` consumes, so
  that instance now fires for `Sym(E)`.
* `Stacks.SymGraded.twistData_isInvertible_schemeSheafGradedAlgebra` and
  `twistData_stacksIsInvertible_schemeSheafGradedAlgebra`: **every integral twist on
  `P(E) = Proj_X(Sym(E))` is invertible**, for either of the repository's two classes realising
  Tag 01CS, given a twist datum of `Sym(E)`.

## Implementation notes

The twist datum remains an argument of the declarations below, but it is not an obstacle:
`Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra` builds Tag 01NR's datum for
every quasi-coherent graded algebra, reading nothing beyond the algebra itself, and
`StacksFrontier.AlgebraicGeometry.SymGenDegreeOne.ProjectiveBundleTwists` uses it to remove this
argument as well. What this file removes is the *other* hypothesis
of Tag 01O4's invertibility statement.

## References

* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01OB](https://stacks.math.columbia.edu/tag/01OB)

## Not done here

**No tag is attached.** Tag 01O4's `twists_invertible` label is already registered at
`Stacks.AlgebraicGeometry.TwistMapsInvertible.relativeProjTwists_isInvertible`, and the
declarations here are instantiations of it rather than new assertions of the tag; Tag 01OB needs
the relative twist `𝒪_{P(E)}(n)` and functoriality of the bundle in `E`, neither of which is
here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwists
open Stacks.AlgebraicGeometry.ProjRepresentsF1
open Stacks.AlgebraicGeometry.TwistMapsInvertible

namespace Stacks.SymGraded

universe u

variable {X : Scheme.{u}} (E : X.Modules) (hqc : IsQuasicoherentPieces E)

/-- The generation hypothesis as a `Fact`, so that
`Stacks.AlgebraicGeometry.TwistMapsInvertible.relativeProjTwists_isInvertible` applies to the
symmetric algebra by instance search. -/
instance fact_isGeneratedInDegreeOne_schemeSheafGradedAlgebra [E.IsQuasicoherent] :
    Fact (∀ U : X.Opens, IsAffineOpen U →
      Algebra.adjoin ((schemeSheafGradedAlgebra E hqc).grading U 0)
        (((schemeSheafGradedAlgebra E hqc).grading U 1 :
          Set ((schemeSheafGradedAlgebra E hqc).sectionRing U))) = ⊤) :=
  ⟨isGeneratedInDegreeOne_schemeSheafGradedAlgebra E hqc⟩

/-- **Every integral twist on the projective bundle `P(E) = Proj_X(Sym(E))` is invertible**, for
any twist datum of `Sym(E)`. This is Tag 01O4's invertibility statement at the symmetric
algebra: the generation hypothesis it carries is discharged by
`Stacks.SymGraded.adjoin_grading_one_eq_top`. -/
theorem twistData_isInvertible_schemeSheafGradedAlgebra [E.IsQuasicoherent]
    (D : TwistData (schemeSheafGradedAlgebra E hqc)) (n : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsInvertible
      (relativeProj (schemeSheafGradedAlgebra E hqc)).scheme.presheaf
      (relativeProj (schemeSheafGradedAlgebra E hqc)).scheme.ringCatSheaf.2
      (D.algebra.piece n) :=
  twistData_isInvertible D (isGeneratedInDegreeOne_schemeSheafGradedAlgebra E hqc) n

/-- The same conclusion for the repository's second class realising Tag 01CS. -/
theorem twistData_stacksIsInvertible_schemeSheafGradedAlgebra [E.IsQuasicoherent]
    (D : TwistData (schemeSheafGradedAlgebra E hqc)) (n : ℤ) :
    Stacks.SheafOfModules.IsInvertible
      (relativeProj (schemeSheafGradedAlgebra E hqc)).scheme.presheaf
      (relativeProj (schemeSheafGradedAlgebra E hqc)).scheme.ringCatSheaf.2
      (D.algebra.piece n) :=
  twistData_stacksIsInvertible D (isGeneratedInDegreeOne_schemeSheafGradedAlgebra E hqc) n

end Stacks.SymGraded

end
