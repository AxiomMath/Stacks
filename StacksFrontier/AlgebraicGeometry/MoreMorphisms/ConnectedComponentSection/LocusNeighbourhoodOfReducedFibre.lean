module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.ConnectedAfterShrinking
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ConnectedComponentSection.Generalization

/-!
# The locus `X⁰` is a neighbourhood of a geometrically reduced fibre's selected component

Let `f : X ⟶ Y` be flat and of finite presentation with a specified section `s`, as in
Situation 055L, and let `y` be a point of `Y` whose fibre `X_y` is geometrically reduced. Then
the locus `X⁰` is a neighbourhood of the connected component `X⁰_y` of `X_y` meeting the
section.

The hypothesis of geometric reducedness is on the single fibre `X_y`, as in Stacks Tag 055Q,
and not on all the fibres of `f`, as in Stacks Tag 055R.

## Main results

* `AlgebraicGeometry.ConnectedAlongSection.locus_mem_nhdsSet_fiberComponent_of_specializes_fiber`:
  the neighbourhood statement from local constructibility of `X⁰` and stability of `X⁰` under
  generalization at the points of the fibre over `y`.
* `AlgebraicGeometry.ConnectedAlongSection.locus_mem_nhdsSet_fiberComponent_of_fiber`: the
  neighbourhood statement from flatness, finite presentation and geometric reducedness of the
  fibre over `y`, granted the conclusion of Stacks Tag 0559.

## Implementation notes

Being a neighbourhood of `X⁰_y` is tested one point at a time, and every point tested lies in
the fibre over `y`. Stability of `X⁰` under generalization is therefore needed only at the
points of that one fibre, which is what makes a hypothesis on the fibre over `y` alone suffice:
the generalization step `AlgebraicGeometry.ConnectedAlongSection.mem_locus_of_specializes_of_fiber`
asks for geometric reducedness of the fibre through the point it is applied to, and that point
lies over `y`.

## References

* [Stacks Project, Tag 0559](https://stacks.math.columbia.edu/tag/0559)
* [Stacks Project, Tag 055L](https://stacks.math.columbia.edu/tag/055L)
* [Stacks Project, Tag 055P](https://stacks.math.columbia.edu/tag/055P)
* [Stacks Project, Tag 055Q](https://stacks.math.columbia.edu/tag/055Q)
* [Stacks Project, Tag 05LW](https://stacks.math.columbia.edu/tag/05LW)
-/

@[expose] public section

open CategoryTheory Topology

universe u

namespace AlgebraicGeometry

namespace ConnectedAlongSection

/-- If the locus `X⁰` of a sectioned morphism is locally constructible and contains every
generalization of each of its points lying over `y`, then it is a neighbourhood of the selected
connected component of the fibre over `y`.

Only the points of the fibre over `y` are subjected to the stability hypothesis; a point of
`X⁰` lying over another point of the target is never tested. -/
theorem locus_mem_nhdsSet_fiberComponent_of_specializes_fiber (D : ConnectedAlongSection.{u})
    (y : D.Y) (hc : IsLocallyConstructible D.locus)
    (hgen : ∀ x ∈ D.locus, D.f x = y → ∀ x' : D.X, x' ⤳ x → x' ∈ D.locus) :
    D.locus ∈ 𝓝ˢ (D.f.fiberι y '' D.fiberComponent y) := by
  rw [mem_nhdsSet_iff_forall]
  rintro x ⟨z, hz, rfl⟩
  exact mem_nhds_of_isLocallyConstructible_of_specializes_subset hc
    fun _ hx' => hgen _ ((D.mem_locus _).mpr ⟨y, z, hz, rfl⟩)
      ((D.f.range_fiberι y).le ⟨z, rfl⟩) _ hx'

/-- **Stacks Project, Tag 055Q**, granted the conclusion of Tag 0559. For a flat sectioned
morphism of finite presentation and a point `y` of the target whose fibre is geometrically
reduced, the locus `X⁰` is a neighbourhood of the connected component of the fibre over `y`
meeting the section. -/
theorem locus_mem_nhdsSet_fiberComponent_of_fiber
    (H : GeometricallyIrreducibleAfterShrinking.{u}) (D : ConnectedAlongSection.{u})
    (hfp : FinitePresentation D.f) [Flat D.f] (y : D.Y)
    (hgr : GeometricallyReduced (D.f.fiberToSpecResidueField y)) :
    D.locus ∈ 𝓝ˢ (D.f.fiberι y '' D.fiberComponent y) := by
  have : LocallyOfFinitePresentation D.f := hfp.1
  have : QuasiCompact D.f := hfp.2.1
  have : QuasiSeparated D.f := hfp.2.2
  refine locus_mem_nhdsSet_fiberComponent_of_specializes_fiber D y
    (isLocallyConstructible_locus_of_geometricallyIrreducible H D) ?_
  intro x hx hfx x' hspec
  have hgrx : GeometricallyReduced (D.f.fiberToSpecResidueField (D.f x)) := by
    rw [hfx]
    exact hgr
  exact mem_locus_of_specializes_of_fiber D hfp hgrx hx hspec

end ConnectedAlongSection

end AlgebraicGeometry

end
