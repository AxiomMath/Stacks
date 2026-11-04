module

public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.BaseChange
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.Pushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAffinePushforwardQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedChartPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedChartHenselization

/-!
# Weakly associated points of a finite direct image of represented algebraic spaces

Let `g : T' ⟶ T` be a morphism of the big fppf category over `S` whose underlying morphism of
schemes is finite, and let `F` be a quasi-coherent `𝒪`-module on the algebraic space `T'`
represents. The weakly associated points of the direct image of `F` along the morphism of
represented algebraic spaces `g` induces are the images of the weakly associated points of `F`.

This is the scheme-level statement, Stacks 05EZ, carried to represented algebraic spaces. On a
represented space weak association in the sense of Stacks 0CTX is Zariski weak association of
the restriction along the identity chart, by Stacks 0CTW; and the chart restriction of the
direct image is the scheme-level direct image of the chart restriction.

## Main results

* `AlgebraicGeometry.Space.isWeaklyAssociatedPoint_iff_restrictToChartScheme_idEtaleChart`:
  on a represented algebraic space, weak association of a quasi-coherent module is Zariski
  weak association of its restriction to the chart scheme of the identity chart.
* `AlgebraicGeometry.Space.weaklyAssociatedPoints_modulePushforward_representedSpaceMap_eq_image`:
  the statement above.

## Implementation notes

No `@[stacks]` attribute is placed: Stacks 05EZ is registered on the scheme-level
`AlgebraicGeometry.weaklyAssociatedPoints_pushforward_eq_image_of_isFinite`, and Stacks 0CU9 on
the statement for arbitrary algebraic spaces in
`StacksFrontier/AlgebraicGeometry/Divisors/MorphismWeaklyAssociated/SpaceFiniteDirectImage.lean`,
of which this is the represented case.

The three inputs are the unconditional form of Stacks 0CTW on a represented space,
`AlgebraicGeometry.Space.isWeaklyAssociatedPoint_restrictToChart_idEtaleChart_iff`, whose only
hypothesis is quasi-coherence of the module on the site; quasi-coherence of the direct image,
`AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePushforward_representedSpaceMap`, which is
Stacks 02KG (1) read on the small étale site; and the comparison of the chart restriction of
the direct image with the scheme-level direct image of the chart restriction,
`AlgebraicGeometry.Space.restrictToChartSchemePushforwardIdEtaleChartIso'`.

## References

* [Stacks Project, Tag 05EZ](https://stacks.math.columbia.edu/tag/05EZ)
* [Stacks Project, Tag 0CTW](https://stacks.math.columbia.edu/tag/0CTW)
* [Stacks Project, Tag 0CTX](https://stacks.math.columbia.edu/tag/0CTX)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Weak association on a represented algebraic space is Zariski weak association on the
chart scheme of the identity chart.** This is
`AlgebraicGeometry.Space.isWeaklyAssociatedPoint_restrictToChart_idEtaleChart_iff`, Stacks 0CTW
on a represented space, read through
`AlgebraicGeometry.Space.restrictToChartIsoRestrictToChartScheme` for the second of the two
readings of a chart restriction and with the point transported by the bijection of
Stacks 03BX. -/
theorem isWeaklyAssociatedPoint_iff_restrictToChartScheme_idEtaleChart (T : BigFppfOver B S hS)
    (G : Modules.{u, u} B S hS (yoneda.obj T)
      (_root_.AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T))
    (hG : G.IsQuasicoherentOnSite) (t : points B S hS (yoneda.obj T)) :
    IsWeaklyAssociatedPoint B S hS
        ⟨yoneda.obj T, _root_.AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T⟩ G t ↔
      Stacks.Divisors.IsWeaklyAssociatedPoint
        (restrictToChartScheme B S hS (yoneda.obj T)
          (_root_.AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T) G
          (idEtaleChart B S hS T)) (pointsEquivScheme B S hS T t) := by
  have hreadings := _root_.AlgebraicGeometry.isWeaklyAssociatedPoint_iff_of_iso
    (restrictToChartIsoRestrictToChartScheme B S hS
      (_root_.AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T) G (idEtaleChart B S hS T))
    (pointsEquivScheme B S hS T t)
  have hchart := isWeaklyAssociatedPoint_restrictToChart_idEtaleChart_iff B S hS T G
    (pointsEquivScheme B S hS T t)
  rw [Equiv.symm_apply_apply] at hchart
  exact hchart.symm.trans hreadings

/-- **Stacks 05EZ for represented algebraic spaces.** Let `g : T' ⟶ T` be a morphism of the big
fppf category over `S` whose underlying morphism of schemes is finite and let `F` be a
quasi-coherent `𝒪`-module on the algebraic space represented by `T'`. The weakly associated
points of the direct image of `F` along the morphism of represented algebraic spaces induced by
`g` are the images of the weakly associated points of `F`. -/
theorem weaklyAssociatedPoints_modulePushforward_representedSpaceMap_eq_image
    {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
    (hg : _root_.AlgebraicGeometry.IsFinite ((BigFppfOver.toScheme B S hS).map g))
    (F : Modules.{u, u} B S hS (yoneda.obj T')
      (_root_.AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T'))
    (hF : F.IsQuasicoherentOnSite) :
    weaklyAssociatedPoints B S hS
        ⟨yoneda.obj T, _root_.AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T⟩
        ((modulePushforward B S hS (representedSpaceMap B S hS g)).obj F) =
      pointsMap B S hS (yoneda.obj T') (yoneda.map g) ''
        weaklyAssociatedPoints B S hS
          ⟨yoneda.obj T', _root_.AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T'⟩ F := by
  have hgfin : _root_.AlgebraicGeometry.IsFinite
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) g.left) := hg
  have hPqc : ((modulePushforward B S hS (representedSpaceMap B S hS g)).obj
      F).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePushforward_representedSpaceMap B S hS g F hF
  have hGT' : (restrictToChartScheme B S hS (yoneda.obj T')
      (_root_.AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T') F
      (idEtaleChart B S hS T')).IsQuasicoherent :=
    (isQuasicoherent_restrictToChart_iff B S hS
      (_root_.AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T') F
      (idEtaleChart B S hS T')).1
      (isQuasicoherent_restrictToChart B S hS
        ⟨yoneda.obj T', _root_.AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T'⟩ F hF
        (idEtaleChart B S hS T'))
  have h05 := @_root_.AlgebraicGeometry.weaklyAssociatedPoints_pushforward_eq_image_of_isFinite
    _ _ (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) g.left) hgfin
    (restrictToChartScheme B S hS (yoneda.obj T')
      (_root_.AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T') F (idEtaleChart B S hS T'))
    hGT'
  have hiso := _root_.AlgebraicGeometry.isWeaklyAssociatedPoint_iff_of_iso
    (restrictToChartSchemePushforwardIdEtaleChartIso' B S hS g F)
  have hkey : ∀ t, t ∈ weaklyAssociatedPoints B S hS
        ⟨yoneda.obj T, _root_.AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T⟩
        ((modulePushforward B S hS (representedSpaceMap B S hS g)).obj F) ↔
      pointsEquivScheme B S hS T t ∈ Stacks.Divisors.weaklyAssociatedPoints
        ((Scheme.Modules.pushforward (_root_.AlgebraicGeometry.SmallEtale.schemeHom
            (associatedBigEtaleSite B) g.left)).obj
          (restrictToChartScheme B S hS (yoneda.obj T')
            (_root_.AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T') F
            (idEtaleChart B S hS T'))) := fun t =>
    (isWeaklyAssociatedPoint_iff_restrictToChartScheme_idEtaleChart B S hS T _ hPqc t).trans
      (hiso (pointsEquivScheme B S hS T t))
  have hmap : ∀ t', pointsEquivScheme B S hS T
      (pointsMap B S hS (yoneda.obj T') (yoneda.map g) t') =
      ((BigFppfOver.toScheme B S hS).map g).base (pointsEquivScheme B S hS T' t') := fun t' => by
    have h := pointsEquivScheme_symm_map B S hS g (pointsEquivScheme B S hS T' t')
    rw [Equiv.symm_apply_apply] at h
    rw [← h, Equiv.apply_symm_apply]
  ext t
  constructor
  · intro ht
    obtain ⟨s', hs', hst⟩ := (h05 ▸ (hkey t).1 ht :)
    refine ⟨(pointsEquivScheme B S hS T').symm s', ?_,
      (pointsEquivScheme B S hS T).injective (by rw [hmap, Equiv.apply_symm_apply]; exact hst)⟩
    refine (isWeaklyAssociatedPoint_iff_restrictToChartScheme_idEtaleChart B S hS T' F hF
      ((pointsEquivScheme B S hS T').symm s')).2 ?_
    rwa [Equiv.apply_symm_apply]
  · rintro ⟨t', ht', rfl⟩
    refine (hkey _).2 ?_
    rw [h05, hmap]
    exact ⟨pointsEquivScheme B S hS T' t',
      (isWeaklyAssociatedPoint_iff_restrictToChartScheme_idEtaleChart B S hS T' F hF t').1 ht',
      rfl⟩

end AlgebraicGeometry.Space

end
