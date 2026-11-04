module

public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.SpaceRepresentedFinitePushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAffinePushforwardQuasicoherent

/-!
# Weakly associated points of an affine direct image of represented algebraic spaces

Let `g : T' ⟶ T` be a morphism of the big fppf category over `S` whose underlying morphism of
schemes is affine, and let `F` be a quasi-coherent `𝒪`-module on the algebraic space `T'`
represents. Every weakly associated point of the direct image of `F` along the morphism of
represented algebraic spaces `g` induces is the image of a weakly associated point of `F`, and
the two sets are equal when the scheme of `T'` is locally Noetherian.

These are Stacks 05EX and Stacks 05EY for represented algebraic spaces.

## Main results

All in the namespace `AlgebraicGeometry.Space`:

* `weaklyAssociatedPoints_modulePushforward_representedSpaceMap_subset_image_of_isAffineHom`:
  every weakly associated point of the direct image is the image of a weakly associated point of
  `F`.
* `weaklyAssociatedPoints_modulePushforward_representedSpaceMap_eq_image_of_isAffineHom`: the
  weakly associated points of the direct image are the images of those of `F`, for a locally
  Noetherian source scheme.

## References

* [Stacks Project, Tag 05EX](https://stacks.math.columbia.edu/tag/05EX)
* [Stacks Project, Tag 05EY](https://stacks.math.columbia.edu/tag/05EY)
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

/-- **Stacks 05EX for represented algebraic spaces.** Let `g : T' ⟶ T` be a morphism of the big
fppf category over `S` whose underlying morphism of schemes is affine and let `F` be a
quasi-coherent `𝒪`-module on the algebraic space represented by `T'`. Every weakly associated
point of the direct image of `F` along the morphism of represented algebraic spaces induced by
`g` is the image of a weakly associated point of `F`. -/
theorem weaklyAssociatedPoints_modulePushforward_representedSpaceMap_subset_image_of_isAffineHom
    {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
    (hg : _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map g))
    (F : Modules.{u, u} B S hS (yoneda.obj T')
      (_root_.AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T'))
    (hF : F.IsQuasicoherentOnSite) :
    weaklyAssociatedPoints B S hS
        ⟨yoneda.obj T, _root_.AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T⟩
        ((modulePushforward B S hS (representedSpaceMap B S hS g)).obj F) ⊆
      pointsMap B S hS (yoneda.obj T') (yoneda.map g) ''
        weaklyAssociatedPoints B S hS
          ⟨yoneda.obj T', _root_.AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T'⟩ F := by
  have hgaff : _root_.AlgebraicGeometry.IsAffineHom
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) g.left) := hg
  have := hF
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
  have h05 := @_root_.AlgebraicGeometry.weaklyAssociatedPoints_pushforward_subset_image
    _ _ (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) g.left) hgaff
    (restrictToChartScheme B S hS (yoneda.obj T')
      (_root_.AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T') F (idEtaleChart B S hS T'))
    hGT'
  have hiso := _root_.AlgebraicGeometry.isWeaklyAssociatedPoint_iff_of_moduleIso
    (restrictToChartSchemePushforwardIdEtaleChartIso' B S hS g F)
  intro t ht
  have h2 : pointsEquivScheme B S hS T t ∈
      Stacks.Divisors.weaklyAssociatedPoints
        ((Scheme.Modules.pushforward (_root_.AlgebraicGeometry.SmallEtale.schemeHom
            (associatedBigEtaleSite B) g.left)).obj
          (restrictToChartScheme B S hS (yoneda.obj T')
            (_root_.AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T') F
            (idEtaleChart B S hS T'))) :=
    (hiso (pointsEquivScheme B S hS T t)).1
      ((isWeaklyAssociatedPoint_iff_restrictToChartScheme_idEtaleChart B S hS T _ hPqc t).1 ht)
  obtain ⟨s', hs', hst⟩ := h05 h2
  have hst' : ((BigFppfOver.toScheme B S hS).map g).base s' =
      pointsEquivScheme B S hS T t := hst
  refine ⟨(pointsEquivScheme B S hS T').symm s', ?_, ?_⟩
  · refine (isWeaklyAssociatedPoint_iff_restrictToChartScheme_idEtaleChart B S hS T' F hF
      ((pointsEquivScheme B S hS T').symm s')).2 ?_
    rwa [Equiv.apply_symm_apply]
  · rw [← pointsEquivScheme_symm_map B S hS g s', hst', Equiv.symm_apply_apply]

/-- **Stacks 05EY for represented algebraic spaces.** Let `g : T' ⟶ T` be a morphism of the big
fppf category over `S` whose underlying morphism of schemes is affine and has locally Noetherian
source, and let `F` be a quasi-coherent `𝒪`-module on the algebraic space represented by `T'`.
The weakly associated points of the direct image of `F` along the morphism of represented
algebraic spaces induced by `g` are the images of the weakly associated points of `F`. -/
theorem weaklyAssociatedPoints_modulePushforward_representedSpaceMap_eq_image_of_isAffineHom
    {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
    (hg : _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map g))
    (hT' : _root_.AlgebraicGeometry.IsLocallyNoetherian
      ((BigFppfOver.toScheme B S hS).obj T'))
    (F : Modules.{u, u} B S hS (yoneda.obj T')
      (_root_.AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T'))
    (hF : F.IsQuasicoherentOnSite) :
    weaklyAssociatedPoints B S hS
        ⟨yoneda.obj T, _root_.AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T⟩
        ((modulePushforward B S hS (representedSpaceMap B S hS g)).obj F) =
      pointsMap B S hS (yoneda.obj T') (yoneda.map g) ''
        weaklyAssociatedPoints B S hS
          ⟨yoneda.obj T', _root_.AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T'⟩ F := by
  have hgaff : _root_.AlgebraicGeometry.IsAffineHom
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) g.left) := hg
  have := hF
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
  have h05 := @_root_.AlgebraicGeometry.weaklyAssociatedPoints_pushforward_eq_image_of_isAffineHom
    _ _ (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) g.left) hgaff
    hT'
    (restrictToChartScheme B S hS (yoneda.obj T')
      (_root_.AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T') F (idEtaleChart B S hS T'))
    hGT'
  have hiso := _root_.AlgebraicGeometry.isWeaklyAssociatedPoint_iff_of_moduleIso
    (restrictToChartSchemePushforwardIdEtaleChartIso' B S hS g F)
  refine Set.Subset.antisymm
    (weaklyAssociatedPoints_modulePushforward_representedSpaceMap_subset_image_of_isAffineHom
      B S hS g hg F hF) ?_
  rintro t ⟨t', ht', rfl⟩
  refine (isWeaklyAssociatedPoint_iff_restrictToChartScheme_idEtaleChart B S hS T _ hPqc
    (pointsMap B S hS (yoneda.obj T') (yoneda.map g) t')).2 ?_
  refine (hiso (pointsEquivScheme B S hS T
    (pointsMap B S hS (yoneda.obj T') (yoneda.map g) t'))).2 ?_
  show pointsEquivScheme B S hS T (pointsMap B S hS (yoneda.obj T') (yoneda.map g) t') ∈
    Stacks.Divisors.weaklyAssociatedPoints
      ((Scheme.Modules.pushforward (_root_.AlgebraicGeometry.SmallEtale.schemeHom
          (associatedBigEtaleSite B) g.left)).obj
        (restrictToChartScheme B S hS (yoneda.obj T')
          (_root_.AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T') F
          (idEtaleChart B S hS T')))
  have hmap : pointsEquivScheme B S hS T
      (pointsMap B S hS (yoneda.obj T') (yoneda.map g) t') =
      ((BigFppfOver.toScheme B S hS).map g).base (pointsEquivScheme B S hS T' t') := by
    have h := pointsEquivScheme_symm_map B S hS g (pointsEquivScheme B S hS T' t')
    rw [Equiv.symm_apply_apply] at h
    rw [← h, Equiv.apply_symm_apply]
  rw [h05, hmap]
  exact ⟨pointsEquivScheme B S hS T' t',
    (isWeaklyAssociatedPoint_iff_restrictToChartScheme_idEtaleChart B S hS T' F hF t').1 ht',
    rfl⟩

end AlgebraicGeometry.Space

end
