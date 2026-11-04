module

public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.BaseChange
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.FlatSurjectivePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedChartHenselization

/-!
# Weakly associated points of a represented algebraic space under a flat surjective pullback

Let `ρ : U' ⟶ U` be a morphism of the big fppf category over `S` whose underlying morphism of
schemes is flat and surjective, and let `N` be a quasi-coherent `𝒪`-module on the algebraic
space represented by `U`. Every weakly associated point of `N` is the image of a weakly
associated point of the inverse image of `N` on the algebraic space represented by `U'`.

On a represented algebraic space weak association in the sense of Stacks 0CTX is Zariski weak
association of the restriction along the identity chart, by Stacks 0CTW, and for a
quasi-coherent module that restriction commutes with base change along `ρ`. So the statement is
the schemes statement on the underlying morphism of schemes, which is
`AlgebraicGeometry.exists_isWeaklyAssociatedPoint_pullback_of_flat_of_surjective`.

## Main results

* `AlgebraicGeometry.Space.exists_isWeaklyAssociatedPoint_modulePullback_representedSpaceMap`:
  the existence of that preimage.

## Implementation notes

The two readings of the restriction to the chart scheme — `restrictToChart` on the small étale
site and `restrictToChartScheme` on the Zariski site of the chart's scheme — are matched by
`AlgebraicGeometry.Space.restrictToChartIsoRestrictToChartScheme`, since Stacks 0CTW is stated
for the first and the base-change comparison
`AlgebraicGeometry.Space.nonempty_restrictToChartScheme_baseChange_of_isQuasicoherent` for the
second.

No finiteness hypothesis on `ρ` is used, and no hypothesis beyond quasi-coherence of `N`: the
schemes statement needs none, and the unconditional form of Stacks 0CTW on a represented space
trades the finite generation of the maximal ideal of the local ring for quasi-coherence.

## References

* [Stacks Project, Tag 0CTW](https://stacks.math.columbia.edu/tag/0CTW)
* [Stacks Project, Tag 0CTX](https://stacks.math.columbia.edu/tag/0CTX)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 05F0](https://stacks.math.columbia.edu/tag/05F0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A weakly associated point of a quasi-coherent module on a represented algebraic space has
a weakly associated preimage under a flat surjective morphism of the site.** For
`ρ : U' ⟶ U` whose underlying morphism of schemes is flat and surjective and `N` a
quasi-coherent `𝒪`-module on the space represented by `U`, every point weakly associated to `N`
is the image of a point weakly associated to the inverse image of `N` on the space represented
by `U'`. -/
theorem exists_isWeaklyAssociatedPoint_modulePullback_representedSpaceMap
    {U' U : BigFppfOver B S hS} (ρ : U' ⟶ U)
    (hflat : _root_.AlgebraicGeometry.Flat ((BigFppfOver.toScheme B S hS).map ρ))
    (hsurj : _root_.AlgebraicGeometry.Surjective ((BigFppfOver.toScheme B S hS).map ρ))
    (N : Modules.{u, u} B S hS (yoneda.obj U)
      (_root_.AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))
    (hN : N.IsQuasicoherentOnSite)
    {u : points B S hS (yoneda.obj U)}
    (hu : IsWeaklyAssociatedPoint B S hS
      ⟨yoneda.obj U, _root_.AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U⟩ N u) :
    ∃ u' : points B S hS (yoneda.obj U'),
      pointsMap B S hS (yoneda.obj U') (yoneda.map ρ) u' = u ∧
        IsWeaklyAssociatedPoint B S hS
          ⟨yoneda.obj U', _root_.AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U'⟩
          ((modulePullback B S hS (representedSpaceMap B S hS ρ)).obj N) u' := by
  have := hflat
  have := hsurj
  have := hN
  have hN' : ((modulePullback B S hS (representedSpaceMap B S hS ρ)).obj N).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
      (representedSpaceMap B S hS ρ) N hN
  set t := pointsEquivScheme B S hS U u with ht
  have hut : (pointsEquivScheme B S hS U).symm t = u := by rw [ht, Equiv.symm_apply_apply]
  have key : ∀ (V : BigFppfOver B S hS)
      (M : Modules.{u, u} B S hS (yoneda.obj V)
        (_root_.AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V))
      [M.IsQuasicoherentOnSite] t,
      IsWeaklyAssociatedPoint B S hS
        ⟨yoneda.obj V, _root_.AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V⟩ M
        ((pointsEquivScheme B S hS V).symm t) ↔
      Stacks.Divisors.IsWeaklyAssociatedPoint
        (restrictToChartScheme B S hS (yoneda.obj V)
          (_root_.AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V) M
          (idEtaleChart B S hS V)) t := fun V M _ t =>
    (isWeaklyAssociatedPoint_restrictToChart_idEtaleChart_iff B S hS V M t).symm.trans
      (_root_.AlgebraicGeometry.isWeaklyAssociatedPoint_iff_of_iso
        (restrictToChartIsoRestrictToChartScheme B S hS
          (_root_.AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V) M
          (idEtaleChart B S hS V)) t)
  have h2 := (key U N t).1 (hut ▸ hu)
  obtain ⟨t', ht', h3⟩ :=
    _root_.AlgebraicGeometry.exists_isWeaklyAssociatedPoint_pullback_of_flat_of_surjective
      ((BigFppfOver.toScheme B S hS).map ρ) _ h2
  obtain ⟨e⟩ := nonempty_restrictToChartScheme_baseChange_of_isQuasicoherent ρ N hN
  have h4 := (_root_.AlgebraicGeometry.isWeaklyAssociatedPoint_iff_of_iso e t').2 h3
  refine ⟨(pointsEquivScheme B S hS U').symm t', ?_, (key U' _ t').2 h4⟩
  rw [← pointsEquivScheme_symm_map B S hS ρ t', ht', hut]

end AlgebraicGeometry.Space

end
