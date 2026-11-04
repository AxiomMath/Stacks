module

public import StacksFrontier.AlgebraicGeometry.SymGenDegreeOne.Consumers
public import StacksFrontier.AlgebraicGeometry.GluedTwistAlgebra.Assemble

/-!
# The twists on a projective bundle are invertible, on no hypothesis at all

`Stacks.SymGraded.twistData_isInvertible_schemeSheafGradedAlgebra` discharges the degree-one
generation hypothesis of Tag 01O4's `twists_invertible` assertion at the symmetric algebra, and
leaves the twist datum of Tag 01NR as its one remaining argument. That argument is not an
obstacle: `Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra` builds a twist
datum for every quasi-coherent graded algebra, reading nothing beyond the algebra itself. This
file composes the two.

The conclusion is the field `twist_isInvertible` of `Stacks.Divisors.BundleSplittingDatum`, at
the bundle `𝐏(ℰ)` and the twist `𝒪_{𝐏(ℰ)}(1)` that datum is about, with no hypothesis beyond
quasi-coherence of `ℰ` and of the homogeneous pieces of `Sym(ℰ)`.

## Main definitions

* `Stacks.SymGraded.projectiveBundleTwistData`: the canonical twist datum of `Sym(ℰ)`.

## Main results

* `Stacks.SymGraded.isInvertible_projectiveBundleTwist`: **every integral twist on the
  projective bundle is invertible**, with no twist datum supplied by the caller.
* `Stacks.SymGraded.stacksIsInvertible_projectiveBundleTwist`: the same for the repository's
  second class realising Tag 01CS.

## Implementation notes

**Which twist datum.** Tag 01NR's uniqueness assertion says any two twist data of an algebra are
related by a unique compatible isomorphism, so invertibility at one of them gives it at all; the
canonical choice is recorded here only so that the statements take no datum as an argument.
`Stacks.AlgebraicGeometry.TwistExistence.isUniqueTwistData` is that uniqueness.

**The generation hypothesis is not an argument anywhere in this file.** It is discharged at
`Sym(ℰ)` by `Stacks.SymGraded.isGeneratedInDegreeOne_schemeSheafGradedAlgebra`, which is the
notion `Stacks.AlgebraicGeometry.ProjRepresentsF1.IsGeneratedInDegreeOne` — the same one the
field `Stacks.AlgebraicGeometry.ProjRepresentsF1.F1Bundle.generated` carries, so a bundle of Tag
01O4 for `Sym(ℰ)` would supply nothing here that is not already proved.

## References

* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01OB](https://stacks.math.columbia.edu/tag/01OB)
* [Stacks Project, Tag 0AYP](https://stacks.math.columbia.edu/tag/0AYP)

## Not done here

**No tag is attached.** Tag 01O4's `twists_invertible` label is live at
`Stacks.AlgebraicGeometry.TwistMapsInvertible.relativeProjTwists_isInvertible` and Tag 01NR's at
`Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra`; the declarations here are
instantiations of those at the symmetric algebra, not new assertions of either tag. Tag 01OB
additionally needs functoriality of the bundle in `ℰ`, which is not here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwists

namespace Stacks.SymGraded

universe u

variable {X : Scheme.{u}} (E : X.Modules) (hqc : IsQuasicoherentPieces E)

/-- **The canonical twist datum of `Sym(ℰ)`**, Tag 01NR's datum for the graded algebra of the
projective bundle. It reads nothing beyond the algebra. -/
public def projectiveBundleTwistData : TwistData (schemeSheafGradedAlgebra E hqc) :=
  Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra
    (schemeSheafGradedAlgebra E hqc)

/-- **Every integral twist on the projective bundle `𝐏(ℰ) = Proj_X(Sym(ℰ))` is invertible.**
Both hypotheses of Tag 01O4's invertibility assertion are discharged: degree-one generation by
`Stacks.SymGraded.isGeneratedInDegreeOne_schemeSheafGradedAlgebra`, and the twist datum by
`Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra`. -/
public theorem isInvertible_projectiveBundleTwist [E.IsQuasicoherent] (n : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsInvertible
      (relativeProj (schemeSheafGradedAlgebra E hqc)).scheme.presheaf
      (relativeProj (schemeSheafGradedAlgebra E hqc)).scheme.ringCatSheaf.2
      ((projectiveBundleTwistData E hqc).algebra.piece n) :=
  twistData_isInvertible_schemeSheafGradedAlgebra E hqc (projectiveBundleTwistData E hqc) n

/-- The same conclusion for the repository's second class realising Tag 01CS, the one Tags 0B8K
and 0B8L are stated for. -/
public theorem stacksIsInvertible_projectiveBundleTwist [E.IsQuasicoherent] (n : ℤ) :
    Stacks.SheafOfModules.IsInvertible
      (relativeProj (schemeSheafGradedAlgebra E hqc)).scheme.presheaf
      (relativeProj (schemeSheafGradedAlgebra E hqc)).scheme.ringCatSheaf.2
      ((projectiveBundleTwistData E hqc).algebra.piece n) :=
  twistData_stacksIsInvertible_schemeSheafGradedAlgebra E hqc
    (projectiveBundleTwistData E hqc) n

end Stacks.SymGraded

end
