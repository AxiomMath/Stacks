module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RepresentedHomotopyPullbackCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativeDescentHomDescentAssembly
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativelyPerfectRepresentedChartProof

/-!
# Hom descent and the colimit of relatively perfect objects (Stacks 0DKV, 0DKW)

The hom-descent output of Stacks 0DKV, clauses (4) and (5) of Stacks 0DKW, and Stacks 0DKW
itself, obtained by applying the `AlgebraicGeometry.Space.RelativeDescentSituation` results
`homDescentOfPseudoCoherent_of_homotopyPullbackCoherence`,
`relativelyPerfectFullyFaithful_of_homotopyPullbackCoherence` and
`relativelyPerfectColimit_of_homotopyPullbackCoherence` to
`AlgebraicGeometry.Space.representedHomotopyPullbackCoherence`.

## References

* [Stacks Project, Tag 0DKV](https://stacks.math.columbia.edu/tag/0DKV)
* [Stacks Project, Tag 0DKW](https://stacks.math.columbia.edu/tag/0DKW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

namespace RelativeDescentSituation

attribute [local instance] isDirected_laterIndex

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]

variable (I) in
/-- The hom-descent output of Stacks 0DKV, for index types in universe `u`. -/
theorem homDescentOfPseudoCoherent_proved : HomDescentOfPseudoCoherent B S hS hZ I :=
  homDescentOfPseudoCoherent_of_homotopyPullbackCoherence I
    (representedHomotopyPullbackCoherence B S hS)

/-- Clauses (4) and (5) of Stacks 0DKW: full faithfulness. -/
theorem relativelyPerfectFullyFaithful_proved (D : RelativeDescentSituation B S hS hZ I) :
    D.RelativelyPerfectFullyFaithful :=
  D.relativelyPerfectFullyFaithful_of_homotopyPullbackCoherence
    (representedHomotopyPullbackCoherence B S hS)

/-- In Situation 0DKU (indexed by a directed preorder `I` in `Type u`), whose
limit is a limit of schemes on affine charts (the standing meaning of `Y = lim Yᵢ`,
`AlgebraicGeometry.Space.RelativeDescentSituation.IsSchemeLimit`), the category of `Y`-perfect
objects of `D(𝒪_X)` is the colimit of the categories of `Yᵢ`-perfect objects of `D(𝒪_{Xᵢ})`, in the
five clauses of `AlgebraicGeometry.Space.RelativeDescentSituation.RelativelyPerfectColimit`. -/
@[stacks 0DKW]
theorem relativelyPerfectColimit_proved (D : RelativeDescentSituation B S hS hZ I) :
    D.RelativelyPerfectColimit :=
  D.relativelyPerfectColimit_of_homotopyPullbackCoherence
    (representedHomotopyPullbackCoherence B S hS)

end RelativeDescentSituation

end AlgebraicGeometry.Space

end
