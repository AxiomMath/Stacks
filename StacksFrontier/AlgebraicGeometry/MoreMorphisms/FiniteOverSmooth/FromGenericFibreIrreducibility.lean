module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.ConnectedAfterShrinking
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.FromRegularSlice

/-!
# The Stacks 057K chain on the single hypothesis of Tag 0559

Tags `055P` and `055R` are the only inputs of the chain
`055P`, `055R` → `057I` → `055W` → `057J` → `057K` that are not available in the library, Tag
`0570` having been discharged in
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.FromRegularSlice`. Both follow from
the
conclusion of Tag `0559`: Tag `055P` outright, and Tag `055R` together with stability of the
locus `X⁰` under generalization, which is the content of the proof of Tag `055Q` and is carried
here as `AlgebraicGeometry.LocusStableUnderGeneralization`.

This module feeds those two into the chain, so that each of Tags `057I`, `055W`, `057J` and
`057K` is stated on the single hypothesis
`AlgebraicGeometry.GeometricallyIrreducibleAfterShrinking`, the conclusion of Tag `0559`,
together with that one residual stability hypothesis.

## Main results

Everything here lives in the `AlgebraicGeometry` namespace.

* `LocusStableUnderGeneralization`: stability of the locus `X⁰` under generalization, the one
  input of Tag `055R` that Tag `0559` does not supply.
* `statement055P_of_geometricallyIrreducibleAfterShrinking` and
  `statement055R_of_geometricallyIrreducibleAfterShrinking`: Tags `055P` and `055R` in the shape
  the 057K chain consumes them.
* `statement057I_of_geometricallyIrreducibleAfterShrinking`,
  `statement055W_of_geometricallyIrreducibleAfterShrinking`,
  `statement057J_of_geometricallyIrreducibleAfterShrinking` and
  `statement057K_of_geometricallyIrreducibleAfterShrinking`: Tags `057I`, `055W`, `057J` and
  `057K`, each on no hypothesis beyond the conclusion of Tag `0559` and the stability of `X⁰`
  under generalization.

## Implementation notes

Nothing here is tagged: every statement carries hypotheses that the corresponding Stacks
statement does not have. Once Tag `0559` is proved, each of the four results above becomes the
corresponding Stacks statement by a single application, modulo
`LocusStableUnderGeneralization`.

The Stacks proof of stability of `X⁰` under generalization is the substance of Tag `055Q`: a
reduction to a Noetherian base by a limit argument, a reduction to a discrete valuation ring
base through Tag `054F` and the Noetherian neighbourhood criterion for constructible sets, and
then Tag `055J` on the resulting connected family. None of that is done here.

## References

* [Stacks Project, Tag 0559](https://stacks.math.columbia.edu/tag/0559)
* [Stacks Project, Tag 055P](https://stacks.math.columbia.edu/tag/055P)
* [Stacks Project, Tag 055Q](https://stacks.math.columbia.edu/tag/055Q)
* [Stacks Project, Tag 055R](https://stacks.math.columbia.edu/tag/055R)
* [Stacks Project, Tag 057I](https://stacks.math.columbia.edu/tag/057I)
* [Stacks Project, Tag 055W](https://stacks.math.columbia.edu/tag/055W)
* [Stacks Project, Tag 057J](https://stacks.math.columbia.edu/tag/057J)
* [Stacks Project, Tag 057K](https://stacks.math.columbia.edu/tag/057K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology

universe u

namespace AlgebraicGeometry

/-- Stability of the locus `X⁰` of **Stacks Project, Situation 055L** under generalization, for
a flat morphism of finite presentation with geometrically reduced fibres: if a point lies in the
union of the fibrewise connected components meeting the section, then so does every point
specializing to it. This is the one input of Tag `055R` that the conclusion of Tag `0559` does
not supply; in the Stacks Project it is proved along the way to Tag `055Q`. -/
abbrev LocusStableUnderGeneralization : Prop :=
  ∀ (D : ConnectedAlongSection.{u}), FinitePresentation D.f →
    ∀ [Flat D.f] [GeometricallyReduced D.f] (x : D.X), x ∈ D.locus →
      ∀ x' : D.X, x' ⤳ x → x' ∈ D.locus

/-- **Stacks Project, Tag 055P**, granted Tag 0559, in the shape `AlgebraicGeometry.Statement055P`
in which the Stacks 057K chain consumes it. -/
theorem statement055P_of_geometricallyIrreducibleAfterShrinking
    (H : GeometricallyIrreducibleAfterShrinking.{u}) : Statement055P.{u} := by
  intro D _ _ _
  exact ConnectedAlongSection.isLocallyConstructible_locus_of_geometricallyIrreducible H D

/-- **Stacks Project, Tag 055R**, granted Tag 0559 and stability of the locus under
generalization, in the shape `AlgebraicGeometry.Statement055R` in which the Stacks 057K chain
consumes it. -/
theorem statement055R_of_geometricallyIrreducibleAfterShrinking
    (H : GeometricallyIrreducibleAfterShrinking.{u})
    (hgen : LocusStableUnderGeneralization.{u}) : Statement055R.{u} := by
  intro D hfp _ _
  let : LocallyOfFinitePresentation D.f := hfp.locallyOfFinitePresentation
  let : QuasiCompact D.f := hfp.quasiCompact
  let : QuasiSeparated D.f := hfp.quasiSeparated
  exact ConnectedAlongSection.isOpen_locus_of_geometricallyIrreducible H D (hgen D hfp)

/-- **Stacks Project, Tag 057I**, granted Tag 0559 and stability of the locus under
generalization. -/
theorem statement057I_of_geometricallyIrreducibleAfterShrinking
    (H : GeometricallyIrreducibleAfterShrinking.{u})
    (hgen : LocusStableUnderGeneralization.{u}) : Statement057I.{u} :=
  ConnectedComponentSection.statement057I (statement055P_of_geometricallyIrreducibleAfterShrinking
    H)
    (statement055R_of_geometricallyIrreducibleAfterShrinking H hgen)

/-- **Stacks Project, Tag 055W**, granted Tag 0559 and stability of the locus under
generalization. -/
theorem statement055W_of_geometricallyIrreducibleAfterShrinking
    (H : GeometricallyIrreducibleAfterShrinking.{u})
    (hgen : LocusStableUnderGeneralization.{u}) : Statement055W.{u} :=
  statement055W_of_statement057I
    (statement057I_of_geometricallyIrreducibleAfterShrinking H hgen)

/-- **Stacks Project, Tag 057J**, granted Tag 0559 and stability of the locus under
generalization. -/
theorem statement057J_of_geometricallyIrreducibleAfterShrinking
    (H : GeometricallyIrreducibleAfterShrinking.{u})
    (hgen : LocusStableUnderGeneralization.{u}) : Statement057J.{u} :=
  statement057J_of_statement055W
    (statement055W_of_geometricallyIrreducibleAfterShrinking H hgen)

/-- **Stacks Project, Tag 057K**, granted Tag 0559 and stability of the locus under
generalization. This is the top of the chain: no other input is missing. -/
theorem statement057K_of_geometricallyIrreducibleAfterShrinking
    (H : GeometricallyIrreducibleAfterShrinking.{u})
    (hgen : LocusStableUnderGeneralization.{u}) : Statement057K.{u} :=
  statement057K_of_statement055W
    (statement055W_of_geometricallyIrreducibleAfterShrinking H hgen)

end AlgebraicGeometry

end
