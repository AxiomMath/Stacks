module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ChainInputs.ConnectedAlongSectionNeighbourhood
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ConnectedComponentSection.LocallyConstructibleLocus
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ConnectedComponentSection.Clopen

/-!
# The consequences of Tag 055N for Tags 055P, 055Q and 055R

The library already contains Stacks Tag 055P conditional on the conclusion of Tag 055N
(`AlgebraicGeometry.ConnectedAlongSection.isLocallyConstructible_locus_of_clopenLocus`) and
Stacks Tag 055Q conditional on Tag 055P together with stability of `X⁰` under generalization
(`AlgebraicGeometry.ConnectedAlongSection.locus_mem_nhdsSet_fiberComponent_of_specializes`).

Feeding in Tag 055N as proved in
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.ConnectedComponentSection.Clopen` collapses
the first of those
hypotheses, so that the whole chain `055N → 055P → 055Q → 055R` rests on the conclusion of
Tag 055G alone, plus — for 055Q and 055R — the stability of `X⁰` under generalization.

## Main results

* `AlgebraicGeometry.ConnectedAlongSection.clopenLocusAfterShrinking_of_geometricallyConnected`
  discharges the hypothesis of Tag 055P.
* `AlgebraicGeometry.ConnectedAlongSection.isLocallyConstructible_locus_of_geometricallyConnected`
  is Tag 055P granted the conclusion of Tag 055G.
* `AlgebraicGeometry.ConnectedAlongSection.locus_mem_nhdsSet_fiberComponent_of_specializes'`
  is Tag 055Q granted the conclusion of Tag 055G and stability under generalization.
* `AlgebraicGeometry.ConnectedAlongSection.isOpen_locus_of_specializes` is Tag 055R granted
  the same two inputs.

## References

* [Stacks Project, Tag 055P](https://stacks.math.columbia.edu/tag/055P)
* [Stacks Project, Tag 055Q](https://stacks.math.columbia.edu/tag/055Q)
* [Stacks Project, Tag 055R](https://stacks.math.columbia.edu/tag/055R)
-/

@[expose] public section

open CategoryTheory Topology

universe u

namespace AlgebraicGeometry

namespace ConnectedAlongSection

/-- Granted the conclusion of Tag 055G, the hypothesis `ClopenLocusAfterShrinking` of Tag 055P
holds: this is exactly Tag 055N. -/
theorem clopenLocusAfterShrinking_of_geometricallyConnected
    (H : GeometricallyConnectedAfterShrinking.{u}) : ClopenLocusAfterShrinking.{u} :=
  fun D hfin hqc y =>
    @exists_open_isClopen_locus_of_geometricallyConnected H D hfin hqc y

/-- **Stacks Project, Tag 055P**, granted the conclusion of Tag 055G. For a morphism of finite
presentation with a specified section, the union of the connected components of the fibres
containing the section is locally constructible in the source. -/
theorem isLocallyConstructible_locus_of_geometricallyConnected
    (H : GeometricallyConnectedAfterShrinking.{u}) (D : ConnectedAlongSection.{u})
    [LocallyOfFinitePresentation D.f] [QuasiCompact D.f] [QuasiSeparated D.f] :
    IsLocallyConstructible D.locus :=
  isLocallyConstructible_locus_of_clopenLocus
    (clopenLocusAfterShrinking_of_geometricallyConnected H) D

/-- **Stacks Project, Tag 055Q**, granted the conclusion of Tag 055G and stability of `X⁰`
under generalization. The locus `X⁰` is a neighbourhood of the selected connected component of
the fibre over `y`. -/
theorem locus_mem_nhdsSet_fiberComponent_of_specializes'
    (H : GeometricallyConnectedAfterShrinking.{u}) (D : ConnectedAlongSection.{u})
    [LocallyOfFinitePresentation D.f] [QuasiCompact D.f] [QuasiSeparated D.f] (y : D.Y)
    (hgen : ∀ x ∈ D.locus, ∀ x' : D.X, x' ⤳ x → x' ∈ D.locus) :
    D.locus ∈ 𝓝ˢ (D.f.fiberι y '' D.fiberComponent y) :=
  locus_mem_nhdsSet_fiberComponent_of_specializes D y
    (isLocallyConstructible_locus_of_geometricallyConnected H D) hgen

/-- **Stacks Project, Tag 055R**, granted the conclusion of Tag 055G and stability of `X⁰`
under generalization. The locus `X⁰` is open in the source. -/
theorem isOpen_locus_of_specializes
    (H : GeometricallyConnectedAfterShrinking.{u}) (D : ConnectedAlongSection.{u})
    [LocallyOfFinitePresentation D.f] [QuasiCompact D.f] [QuasiSeparated D.f]
    (hgen : ∀ x ∈ D.locus, ∀ x' : D.X, x' ⤳ x → x' ∈ D.locus) :
    IsOpen D.locus := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨y, z, hz, rfl⟩ := (D.mem_locus x).1 hx
  exact mem_nhdsSet_iff_forall.mp
    (locus_mem_nhdsSet_fiberComponent_of_specializes' H D y hgen) _ ⟨z, hz, rfl⟩

end ConnectedAlongSection

end AlgebraicGeometry

end
