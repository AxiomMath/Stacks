module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ChartDegreeOpenEquiv

/-!
# [Stacks, Tag 01NY] and [Stacks, Tag 01NZ] over a general base, unconditionally

Let `S` be a scheme and `𝒜` a quasi-coherent graded `𝒪_S`-algebra (Situation 01NN). This file
records the two tags in full generality, under Situation 01NN alone: an arbitrary relative
homogeneous spectrum of `𝒜` — in particular `Proj_S(𝒜)` of [Stacks, Tag 01NQ] — represents the
functor `F` of the display 01NX, and over a quasi-compact test scheme the morphisms into
`Proj_S(𝒜)` are exactly the graded-twist quotients.

Residue (i) of the source's proof of [Stacks, Tag 01NY] — the descent of [Stacks, Tag 01NU]
along the charts of the base, packaged as
`...RelativeProjQcohSheaf.ProjDegreeRepresentation` — is **constructed**, as
`...RelativeProjQcohSheaf.ProjDegreeRepresentation.ofCharts` of
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ChartDegreeOpenEquiv`, so the two tags
follow from:
`...RelativeProjQcohSheaf.F.representableByRelativeProj` of
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.DegreeOpenCover` and
`...RelativeProjQcohSheaf.relativeProjRepresentableByFunctor` of
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.GluedRepresentsFunctor`.

## Main results

* `...RelativeProjQcohSheaf.F.representableByRelativeProjOfCharts`: **[Stacks, Tag 01NY] over a
  general base**, for an arbitrary relative homogeneous spectrum.
* `...RelativeProjQcohSheaf.relativeProjRepresentableByFunctorUnconditional`: **[Stacks, Tag
  01NZ]**, the relative homogeneous spectrum of [Stacks, Tag 01NQ] represents `F`.
* `...RelativeProjQcohSheaf.canonicalTwistQuotientEquivUnconditional`: the universal graded-twist
  quotient on a quasi-compact test scheme.

## References

* [Stacks Project, Tag 01NY](https://stacks.math.columbia.edu/tag/01NY)
* [Stacks Project, Tag 01NZ](https://stacks.math.columbia.edu/tag/01NZ)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Tag 01NU](https://stacks.math.columbia.edu/tag/01NU)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry Stacks.RingedSpace
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S)

/-- **[Stacks, Tag 01NY] over a general base, unconditionally.** Let `S` be a scheme and `𝒜` a
quasi-coherent graded `𝒪_S`-algebra (Situation 01NN), and let `X` be a relative homogeneous
spectrum of `𝒜` — in particular `Proj_S(𝒜)` of [Stacks, Tag 01NQ]. Then `X` represents the
functor `F` of the display 01NX.

Residue (iii) is `...RelativeProj.RelativeProjData.isOpenCover_degreeOpen` and residue (i) is
`...RelativeProjQcohSheaf.ProjDegreeRepresentation.ofCharts`; nothing is assumed beyond
Situation 01NN. -/
-- Beyond what this declaration proves, recorded here rather than in the attribute:
--   NOT proved here: nothing is said about the morphism to S being the structure morphism of the
--   representation, nor about Tag 01NR's psi being the universal one
--   How it is proved, recorded here rather than in the attribute: this is
--   DegreeOpenCover.F.representableByRelativeProj fed
--   ChartDegreeOpenEquiv.ProjDegreeRepresentation.ofCharts, i.e. residue (iii) of the source proof
--   (RelativeProjData.isOpenCover_degreeOpen and RelativeProjData.degreeOpen_toNat_le_of_dvd, both
--   over an arbitrary base) together with residue (i) over a GENERAL base, the descent of Tag 01NU
--   along the charts. The forward map of that descent is ChartGlue.Fd.existsUnique_hom_degreeOpen,
--   it is a bijection by ChartDegreeOpenEquiv.Fd.homDegreeOpen_injective and
--   Fd.homDegreeOpen_surjective, and its compatibility with the transitions is
--   Fd.degreeOpenEquiv'_scale. The two inputs that complete it are
--   ChartBaseClause.Fd.chartHom_comp_toBase for the base clause of the converse of the chart
--   agreement, and ChartClassScale.Fd.chartClassInv_scale. This supersedes
--   AffineScaleRepresentation.F.representableByRelativeProjOfAffine, which restricted S to be
--   affine.
def F.representableByRelativeProjOfCharts (P : RelativeProjData A) :
    (F.limFunctor (situationAlgebra A)).RepresentableBy P.scheme :=
  F.representableByRelativeProj (ProjDegreeRepresentation.ofCharts A P)

/-- Under Situation 01NN alone, the functor `F` of the display 01NX is representable. -/
theorem F.isRepresentable_relativeProjOfCharts (P : RelativeProjData A) :
    (F.limFunctor (situationAlgebra A)).IsRepresentable :=
  (F.representableByRelativeProjOfCharts A P).isRepresentable

/-- **[Stacks, Tag 01NY].** In Situation 01NN — a scheme `S` and a quasi-coherent graded
`𝒪_S`-algebra `𝒜` — the functor `F` of the display 01NX is representable by a scheme.

This is the tag's sentence itself, with no datum quantified over beyond `S` and `𝒜`: the
representing scheme is `Proj_S(𝒜)` of [Stacks, Tag 01NQ], and the representation is
`F.representableByRelativeProjOfCharts` at that scheme. The functor is `F.limFunctor`, the
display on *every* test scheme — the union over `d ≥ 1` of the `F_d` on a quasi-compact one and
the inverse limit of those over the quasi-compact opens in general — so the statement is about
the source's `F` and not about one `F_d`.

The sibling `F.representableByRelativeProjOfCharts` is the sharper form, naming the representing
scheme and allowing it to be an arbitrary relative homogeneous spectrum of `𝒜`; this is the bare
existential the tag states. Nothing is assumed beyond Situation 01NN, which `𝒜` carries. -/
@[stacks 01NY "the tag's sentence in one statement, with no datum beyond the scheme and the \
graded algebra: the functor F of the display 01NX is representable by a scheme, the representing \
scheme being the constructed relative homogeneous spectrum Proj_S(A)"]
theorem F.isRepresentable_limFunctor :
    (F.limFunctor (situationAlgebra A)).IsRepresentable :=
  F.isRepresentable_relativeProjOfCharts A (relativeProj A)

/-- **[Stacks, Tag 01NZ] over a general base, unconditionally.** For a scheme `S` and a
quasi-coherent graded `𝒪_S`-algebra `𝒜` (Situation 01NN) the relative homogeneous spectrum
`Proj_S(𝒜)` of [Stacks, Tag 01NQ] represents the functor `F` of the display 01NX.

This is `...RelativeProjQcohSheaf.relativeProjRepresentableByFunctor` with its hypothesis
`hrep` — which is exactly [Stacks, Tag 01NY] — discharged by
`F.representableByRelativeProjOfCharts`. -/
-- Beyond what this declaration proves, recorded here rather than in the attribute:
--   NOT proved here, and not a consequence: that the universal quadruple's psi is the psi of Tag
--   01NR or
--   that its L is O(d) that comparison is discussed in RelativeProjQcohSheaf.Theta and this
--   repository
--   does not have it
--   How it is proved, recorded here rather than in the attribute: it is
--   GluedRepresentsFunctor.relativeProjRepresentableByFunctor, whose input hrep is exactly Tag 01NY
--   and is supplied by F.representableByRelativeProjOfCharts of this file. It supersedes
--   AffineScaleRepresentation.relativeProjRepresentableByFunctorOfAffine, which restricted S to be
--   affine.
def relativeProjRepresentableByFunctorUnconditional :
    (F.limFunctor (situationAlgebra A)).RepresentableBy (relativeProj A).scheme :=
  relativeProjRepresentableByFunctor A (relativeProj A)
    (F.representableByRelativeProjOfCharts A (relativeProj A))

/-- **The universal graded-twist quotient, unconditionally.** For a quasi-compact test scheme
`W` the morphisms `W ⟶ Proj_S(𝒜)` correspond bijectively to the points of `F(W)`, that is, to
the graded-twist quotients over `W` of positive degree modulo the identifications of Section
01NS and [Stacks, Tag 01NW].

This is `...RelativeProjQcohSheaf.canonicalTwistQuotientEquiv` with its hypothesis `hrep`
discharged. -/
-- Beyond what this declaration proves, recorded here rather than in the attribute:
--   NOT proved here: that the universal quadruple's psi is the psi of Tag 01NR, or that its L is
--   O(d)
def canonicalTwistQuotientEquivUnconditional (W : Scheme.{u}) (hW : CompactSpace W) :
    (W ⟶ (relativeProj A).scheme) ≃ F (situationAlgebra A) W :=
  canonicalTwistQuotientEquiv A (relativeProj A)
    (F.representableByRelativeProjOfCharts A (relativeProj A)) W hW

/-! ### The two assertions of Tag 01NZ in one statement -/

/-- **[Stacks, Tag 01NZ].** In Situation 01NN, let `P` be any scheme over `S` carrying
projective-spectrum charts on the affine opens of `S` — for instance the scheme representing the
functor `F`, which is such a datum by the source's *"over each affine open of `S` we can identify
`X` with the homogeneous spectrum of the sections of `𝒜` over that open"*. Then

1. the relative homogeneous spectrum `π : Proj_S(𝒜) → S` of [Stacks, Tag 01NQ] represents `F`,
   and
2. there is exactly one isomorphism `Proj_S(𝒜) ≅ P` compatible with the charts, and it is an
   isomorphism over `S`.

Together these say that `Proj_S(𝒜)` and the scheme representing `F` are canonically isomorphic
as schemes over `S`, which is the source's statement: the first assertion identifies `Proj_S(𝒜)`
as a representing object and the second produces the canonical comparison with any other
chart-carrying scheme over `S`, uniquely.

The first assertion is a representation, hence data rather than a proposition, so the two are
packaged by `PProd` rather than `And`. The chart datum `P` is the only binder beyond Situation
01NN, and it is data the statement needs in order to speak of the second scheme at all; it is not
a hypothesis of the source, since `relativeProj A` is itself a `RelativeProjData A` and so is
every projective bundle of `...SheafSymmetricAlgebra`.

The two assertions are `relativeProjRepresentableByFunctorUnconditional` of this file and
`...RelativeProjQcohSheaf.existsUnique_isoOver` of
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.GluedRepresents`. -/
@[stacks 01NZ "for a scheme S and a quasi-coherent graded O_S-algebra A (Situation 01NN) and any \
scheme over S carrying projective-spectrum charts on the affine opens of S, the constructed \
relative homogeneous spectrum Proj_S(A) represents the functor F.limFunctor of the display 01NX, \
and there is exactly one isomorphism from Proj_S(A) to that scheme compatible with the charts, \
which is an isomorphism over S"]
def representableBy_and_existsUnique_isoOver (P : RelativeProjData A) :
    PProd ((F.limFunctor (situationAlgebra A)).RepresentableBy (relativeProj A).scheme)
      (∃! e : (relativeProj A).scheme ≅ P.scheme,
        (∀ U : S.affineOpens, (relativeProj A).chart U.1 U.2 ≫ e.hom = P.chart U.1 U.2) ∧
          e.hom ≫ P.toBase = (relativeProj A).toBase) :=
  ⟨relativeProjRepresentableByFunctorUnconditional A, existsUnique_isoOver A P⟩

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
