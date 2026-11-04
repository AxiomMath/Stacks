module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.GeometricallyConnectedFibres
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ConnectedComponentSection.ClopenLocusConsequences

/-!
# Reducing the Tag 055G hypothesis of the Tag 055N chain to Tag 0559

Tags 055N, 055P, 055Q and 055R are available in the library granted
`AlgebraicGeometry.GeometricallyConnectedAfterShrinking`, the conclusion of Stacks Tag 055G.
Tag 055G itself is available granted
`AlgebraicGeometry.GeometricallyIrreducibleAfterShrinking`, the conclusion of Stacks Tag 0559.
This module composes the two, so that the single outstanding input of the whole chain is
Tag 0559.

## Main results

* `AlgebraicGeometry.geometricallyConnectedAfterShrinking_of_geometricallyIrreducible`:
  the conclusion of Tag 0559 implies the conclusion of Tag 055G.
* `AlgebraicGeometry.ConnectedAlongSection.clopenLocusAfterShrinking_of_geometricallyIrreducible`
  and the three results after it restate Tags 055N, 055P, 055Q and 055R with Tag 0559 as the
  hypothesis in place of Tag 055G.

## Implementation notes

No tag is attached to anything here: every statement carries a hypothesis that the
corresponding Stacks statement does not have. Discharging
`GeometricallyIrreducibleAfterShrinking` — that is, proving Tag 0559 — turns
`geometricallyConnectedAfterShrinking_of_geometricallyIrreducible` into Tag 055G and the first
two results below into Tags 055N and 055P; Tags 055Q and 055R additionally need stability of
the locus under generalization, which is the hypothesis `hgen`.

## References

* [Stacks Project, Tag 0559](https://stacks.math.columbia.edu/tag/0559)
* [Stacks Project, Tag 055G](https://stacks.math.columbia.edu/tag/055G)
* [Stacks Project, Tag 055N](https://stacks.math.columbia.edu/tag/055N)
* [Stacks Project, Tag 055P](https://stacks.math.columbia.edu/tag/055P)
* [Stacks Project, Tag 055Q](https://stacks.math.columbia.edu/tag/055Q)
* [Stacks Project, Tag 055R](https://stacks.math.columbia.edu/tag/055R)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Topology

universe u

namespace AlgebraicGeometry

/-- The conclusion of Stacks Tag 0559 implies the conclusion of Stacks Tag 055G: this is
Tag 055G, whose only input missing from the library is Tag 0559. -/
theorem geometricallyConnectedAfterShrinking_of_geometricallyIrreducible
    (H : GeometricallyIrreducibleAfterShrinking.{u}) :
    GeometricallyConnectedAfterShrinking.{u} := by
  intro X Y f hY hft hqc η hη hGC
  have := hY
  have := hft
  have := hqc
  have := hGC
  exact exists_open_geometricallyConnected_restrict H f η hη

namespace ConnectedAlongSection

/-- **Stacks Project, Tag 055N**, granted Tag 0559: for a finite type morphism with a section,
the locus `X⁰` is open and closed in the inverse image of a nonempty open subset of the closure
of any point of the target. -/
theorem clopenLocusAfterShrinking_of_geometricallyIrreducible
    (H : GeometricallyIrreducibleAfterShrinking.{u}) : ClopenLocusAfterShrinking.{u} :=
  clopenLocusAfterShrinking_of_geometricallyConnected
    (geometricallyConnectedAfterShrinking_of_geometricallyIrreducible H)

/-- **Stacks Project, Tag 055P**, granted Tag 0559: for a morphism of finite presentation with
a section, the locus `X⁰` is locally constructible in the source. -/
theorem isLocallyConstructible_locus_of_geometricallyIrreducible
    (H : GeometricallyIrreducibleAfterShrinking.{u}) (D : ConnectedAlongSection.{u})
    [LocallyOfFinitePresentation D.f] [QuasiCompact D.f] [QuasiSeparated D.f] :
    IsLocallyConstructible D.locus :=
  isLocallyConstructible_locus_of_geometricallyConnected
    (geometricallyConnectedAfterShrinking_of_geometricallyIrreducible H) D

/-- **Stacks Project, Tag 055Q**, granted Tag 0559 and stability of the locus under
generalization: the locus `X⁰` is a neighbourhood of the selected connected component of the
fibre over `y`. -/
theorem locus_mem_nhdsSet_fiberComponent_of_geometricallyIrreducible
    (H : GeometricallyIrreducibleAfterShrinking.{u}) (D : ConnectedAlongSection.{u})
    [LocallyOfFinitePresentation D.f] [QuasiCompact D.f] [QuasiSeparated D.f] (y : D.Y)
    (hgen : ∀ x ∈ D.locus, ∀ x' : D.X, x' ⤳ x → x' ∈ D.locus) :
    D.locus ∈ 𝓝ˢ (D.f.fiberι y '' D.fiberComponent y) :=
  locus_mem_nhdsSet_fiberComponent_of_specializes'
    (geometricallyConnectedAfterShrinking_of_geometricallyIrreducible H) D y hgen

/-- **Stacks Project, Tag 055R**, granted Tag 0559 and stability of the locus under
generalization: the locus `X⁰` is open in the source. -/
theorem isOpen_locus_of_geometricallyIrreducible
    (H : GeometricallyIrreducibleAfterShrinking.{u}) (D : ConnectedAlongSection.{u})
    [LocallyOfFinitePresentation D.f] [QuasiCompact D.f] [QuasiSeparated D.f]
    (hgen : ∀ x ∈ D.locus, ∀ x' : D.X, x' ⤳ x → x' ∈ D.locus) :
    IsOpen D.locus :=
  isOpen_locus_of_specializes
    (geometricallyConnectedAfterShrinking_of_geometricallyIrreducible H) D hgen

end ConnectedAlongSection

end AlgebraicGeometry

end
