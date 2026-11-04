module

public import StacksFrontier.AlgebraicGeometry.ProjF1Normalisation.TautologicalSurjection
public import StacksFrontier.AlgebraicGeometry.TwistMapsInvertible.Basic

/-!
# A bundle of Tag 01O4 carries the invertibility of the twists with it

`Stacks.AlgebraicGeometry.ProjRepresentsF1.F1Bundle` states Tag 01O4's hypothesis in its field
`generated`, and `Stacks.AlgebraicGeometry.TwistMapsInvertible.twistData_isInvertible` is the
tag's `twists_invertible` assertion, whose own hypothesis is that same generation in degree one.
So a bundle discharges it: on the relative `Proj` of an algebra admitting a bundle, every
integral twist is invertible, with no hypothesis beyond the bundle.

Together with `Stacks.AlgebraicGeometry.ProjF1Normalisation.exists_epi_to_twistPieceOne_twistData`
this is the pair of conclusions `Stacks.Divisors.BundleSplittingDatum` asks of its fields `quot`
and `twist_isInvertible`: the tautological surjection onto `𝒪(1)` and the invertibility of its
target. `exists_epi_isInvertible_twistPieceOne` states them as one term.

## Main results

* `Stacks.AlgebraicGeometry.ProjF1Normalisation.twistData_isInvertible_of_f1Bundle`: **the
  twists on a relative `Proj` admitting a bundle are invertible**, unconditionally.
* `Stacks.AlgebraicGeometry.ProjF1Normalisation.twistData_stacksIsInvertible_of_f1Bundle`: the
  same for the repository's other class realising Tag 01CS.
* `Stacks.AlgebraicGeometry.ProjF1Normalisation.exists_epi_isInvertible_twistPieceOne`: the
  tautological surjection onto the degree-one twist together with the invertibility of that
  twist.

## Implementation notes

**The generation hypothesis is read off the bundle by `rfl`.**
`Stacks.AlgebraicGeometry.ProjRepresentsF1.IsGeneratedInDegreeOne` is the adjoin form over every
affine open of the base, which is literally the binder `twistData_isInvertible` takes, so the
field `generated` is passed with no transport. This is the reason that notion, rather than the
additive-subgroup `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.`
`IsGeneratedInDegreeOneAt` or the other substrate's
`SheafOfModules.GradedAlgebra.IsGeneratedInDegreeOne`, is the one the structure carries.

**Nothing here needs the canonicality of the universal pair except the surjection.** The
invertibility statements read only `generated`; the twist datum enters as an ordinary argument
and may be any one, in particular the unconditional
`Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra`. Canonicality is what
identifies the pair's invertible sheaf with `𝒪(1)`, and so is needed only to place the
surjection's target on the datum's own degree-one piece.

## References

* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Tag 0AYP](https://stacks.math.columbia.edu/tag/0AYP)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwists
open Stacks.AlgebraicGeometry.ProjRepresentsF1

namespace Stacks.AlgebraicGeometry.ProjF1Normalisation

universe u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

variable {S : Scheme.{u}} (A : SheafGradedAlgebra.{u} S) (TA : TensorAlgebras.{u})
  {ι : TensorAlgebraPullbackIsos.{u} TA}

/-- **The twists of a relative `Proj` admitting a bundle of Tag 01O4 are invertible.** The
bundle's field `generated` is exactly the hypothesis of the tag's `twists_invertible` assertion,
so no hypothesis beyond the bundle is needed.

The twist datum is an ordinary argument and may be any one; none of its properties are read. -/
public theorem twistData_isInvertible_of_f1Bundle (B : F1Bundle A TA ι) (D : TwistData A)
    (n : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsInvertible (relativeProj A).scheme.presheaf
      (relativeProj A).scheme.ringCatSheaf.2 (D.algebra.piece n) :=
  Stacks.AlgebraicGeometry.TwistMapsInvertible.twistData_isInvertible D B.generated n

/-- The same conclusion for the repository's other class realising Tag 01CS, the one Tags 0B8K
and 0B8L are stated for. -/
public theorem twistData_stacksIsInvertible_of_f1Bundle (B : F1Bundle A TA ι) (D : TwistData A)
    (n : ℤ) :
    Stacks.SheafOfModules.IsInvertible (relativeProj A).scheme.presheaf
      (relativeProj A).scheme.ringCatSheaf.2 (D.algebra.piece n) :=
  Stacks.AlgebraicGeometry.TwistMapsInvertible.twistData_stacksIsInvertible D B.generated n

/-- **The tautological surjection onto the degree-one twist, together with the invertibility of
that twist.** These are the two conclusions `Stacks.Divisors.BundleSplittingDatum` asks of its
fields `quot` and `twist_isInvertible`, for the relative `Proj` of an algebra carrying a bundle
whose universal pair is canonical for the twist datum. -/
public theorem exists_epi_isInvertible_twistPieceOne (B : F1Bundle A TA ι) (D : TwistData A)
    (hB : IsCanonicalTwistPair A TA D B.universal) :
    (∃ q : (Scheme.Modules.pullback (relativeProj A).toBase).obj (A.piece 1) ⟶
        D.algebra.piece 1, Epi q) ∧
      AlgebraicGeometry.SheafOfModules.IsInvertible (relativeProj A).scheme.presheaf
        (relativeProj A).scheme.ringCatSheaf.2 (D.algebra.piece 1) :=
  ⟨exists_epi_to_twistPieceOne_twistData A TA B D hB,
    twistData_isInvertible_of_f1Bundle A TA B D 1⟩

end Stacks.AlgebraicGeometry.ProjF1Normalisation

end
