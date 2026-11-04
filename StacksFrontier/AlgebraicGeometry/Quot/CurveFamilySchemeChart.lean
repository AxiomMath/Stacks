module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilies
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyRelativeDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionChart
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFppfDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowTwistWitness
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FinitePresentationLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.FibrewiseFiber
public import StacksFrontier.AlgebraicGeometry.ProperFibreDimensionNeighbourhood.Basic

/-!
# A family of curves whose base change has a scheme as total space

Let `f : X ⟶ S` be a family of curves (Stacks 0D4Z) and let `φ : U ⟶ S` be a morphism of the big
fppf site such that the base change `X ×_S U` is represented by a scheme `Z`, that is, there is a
cartesian square of algebraic spaces

```
h_Z --p--> X
 |q        |f
h_U --φ--> h_S
```

with `q` a morphism of the site. Such squares are what the étale-local reduction of the moduli
of curves to schemes produces (Stacks 0E6F), and the proof of Stacks 0E88 applies Stacks 0E7L to
the morphism of schemes `Z ⟶ U` underlying `q`. This file records the hypotheses of that
application which come from the family itself.

## Main results

* `AlgebraicGeometry.CurveFamily.flat_toScheme_map_of_isPullback`,
  `AlgebraicGeometry.CurveFamily.locallyOfFinitePresentation_toScheme_map_of_isPullback` and
  `AlgebraicGeometry.CurveFamily.isProper_toScheme_map_of_isPullback_schemeSpaceMap`: the
  morphism of schemes `Z ⟶ U` is flat, locally of finite presentation and proper. Each property
  of `f` is stable under base change of algebraic spaces (Stacks 03MO, 03XR, 04WP) and, for a
  morphism of the site, is the corresponding property of the underlying morphism of schemes.
* `AlgebraicGeometry.CurveFamily.topologicalKrullDim_fiber_toScheme_map_le_of_isPullback`: when
  `φ` is étale, every fibre of `Z ⟶ U` has dimension at most one.
* `AlgebraicGeometry.topologicalKrullDim_fiber_fiberHom_le`: a bound on the dimension of the
  fibre of `f ≫ q` over `s` bounds the dimension of every fibre of the induced morphism
  `(f ≫ q)_s ⟶ q_s` of fibres, which is the form of the fibre-dimension hypothesis of
  Stacks 0E7L.

## Implementation notes

The relative-dimension field of `AlgebraicGeometry.CurveFamily` is the every-étale-chart
condition of Stacks 04NC on the fibre dimension of Stacks 04NL. When `φ` is étale, so is the
base change `p`, and the square above is itself a pair of étale charts of `f`; Stacks 04NC then
reads the fibre dimension of `f` at the image of a point of `Z` off the fibre of `Z ⟶ U`
through that point (`AlgebraicGeometry.Space.holdsOnEveryEtaleChartAtPoint_iff_chartMap`). For
an arbitrary `φ` the fibre-dimension bound would need the invariance of fibre dimension under
base change for algebraic spaces (Stacks 02FY transported along an étale atlas), which is not
needed here, so the bound is stated for étale `φ` only.

## References

* [Stacks Project, Tag 0D4Z](https://stacks.math.columbia.edu/tag/0D4Z)
* [Stacks Project, Tag 0E6F](https://stacks.math.columbia.edu/tag/0E6F)
* [Stacks Project, Tag 0E7L](https://stacks.math.columbia.edu/tag/0E7L)
* [Stacks Project, Tag 0E88](https://stacks.math.columbia.edu/tag/0E88)
* [Stacks Project, Tag 04NC](https://stacks.math.columbia.edu/tag/04NC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

/-- A bound on the dimension of the fibre of `f ≫ q` bounds the dimension of every fibre of the
induced morphism of fibres `(f ≫ q)_s ⟶ q_s`. -/
theorem topologicalKrullDim_fiber_fiberHom_le {A C U : Scheme.{u}} (f : A ⟶ C) (q : C ⟶ U)
    (s : U) {n : WithBot ℕ∞} (h : topologicalKrullDim ((f ≫ q).fiber s) ≤ n)
    (y : q.fiber s) : topologicalKrullDim ((Stacks.Flatness.fiberHom f q s).fiber y) ≤ n :=
  (Topology.IsInducing.topologicalKrullDim_le
    ((Stacks.Flatness.fiberHom f q s).fiberι y).isEmbedding.isInducing).trans h

namespace CurveFamily

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase} (X : CurveFamily B hZ)
  {U Z : BigFppfOver B integerBase hZ} {φ : U ⟶ X.base} {p : schemeSpace Z ⟶ X.total}
  {q : Z ⟶ U}

/-- If the base change of a family of curves along a morphism of the site is a scheme `Z` over
`U`, then `Z ⟶ U` is flat: flatness of algebraic spaces is stable under base change, and for a
morphism of the site it is flatness of the underlying morphism of schemes. -/
theorem flat_toScheme_map_of_isPullback
    (sq : IsPullback p (schemeSpaceMap q) X.toBase (schemeSpaceMap φ)) :
    Flat ((BigFppfOver.toScheme B integerBase hZ).map q) := by
  have h : Space.IsFlat B integerBase hZ (schemeSpaceMap q).hom :=
    (Space.isFlat_isStableUnderBaseChange B integerBase hZ).of_isPullback sq X.flat
  exact (Space.holdsOnEveryEtaleChart_yoneda_map_iff B integerBase hZ
    Flat.isEtaleLocalOnSourceAndTarget q).1 h

/-- If the base change of a family of curves along a morphism of the site is a scheme `Z` over
`U`, then `Z ⟶ U` is locally of finite presentation (Stacks 03XR). -/
theorem locallyOfFinitePresentation_toScheme_map_of_isPullback
    (sq : IsPullback p (schemeSpaceMap q) X.toBase (schemeSpaceMap φ)) :
    LocallyOfFinitePresentation ((BigFppfOver.toScheme B integerBase hZ).map q) := by
  have h : Space.IsLocallyOfFinitePresentation B integerBase hZ (schemeSpaceMap q).hom :=
    (Space.isLocallyOfFinitePresentation_isStableUnderBaseChange B integerBase hZ).of_isPullback
      sq X.finitePresentation.1
  exact (Space.holdsOnEveryEtaleChart_yoneda_map_iff B integerBase hZ
    LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget q).1 h

/-- If the base change of a family of curves along a morphism of the site is a scheme `Z` over
`U`, then `Z ⟶ U` is proper (Stacks 04WP). -/
theorem isProper_toScheme_map_of_isPullback_schemeSpaceMap
    (sq : IsPullback p (schemeSpaceMap q) X.toBase (schemeSpaceMap φ)) :
    IsProper ((BigFppfOver.toScheme B integerBase hZ).map q) := by
  have h : Space.IsProper B integerBase hZ (schemeSpaceMap q).hom :=
    (Space.isProper_isStableUnderBaseChange B integerBase hZ).of_isPullback sq X.proper
  exact Space.isProper_toScheme_map_of_isProper_yoneda_map B integerBase hZ q h

/-- If the base change of a family of curves along an étale morphism of the site is a scheme
`Z` over `U`, then at every point of `Z` the fibre of `Z ⟶ U` through it has dimension at most
one there. The square is a pair of étale charts of the family, so the relative-dimension field
of the family, read on it (Stacks 04NC), is the fibre dimension of `Z ⟶ U` at the point. -/
theorem topologicalKrullDimAt_fiber_toScheme_map_le_of_isPullback
    (sq : IsPullback p (schemeSpaceMap q) X.toBase (schemeSpaceMap φ))
    (hφ : Etale ((BigFppfOver.toScheme B integerBase hZ).map φ))
    (z : (BigFppfOver.toScheme B integerBase hZ).obj Z) :
    topologicalKrullDimAt (((BigFppfOver.toScheme B integerBase hZ).map q).fiber
        (((BigFppfOver.toScheme B integerBase hZ).map q) z))
      (((BigFppfOver.toScheme B integerBase hZ).map q).asFiber z) ≤
      ((1 : ℕ) : WithBot ℕ∞) := by
  let r := Space.schemePointRepresentative B integerBase hZ Z z
  let w : Space.points B integerBase hZ (yoneda.obj Z) := r.class B integerBase hZ (yoneda.obj Z)
  have hw : Space.pointsToScheme B integerBase hZ Z w = z :=
    Space.schemePointRepresentative_point B integerBase hZ Z z
  obtain ⟨e, he, hchart⟩ :=
    X.relativeDimensionLE (Space.pointsMap B integerBase hZ (yoneda.obj Z) p.hom w)
  have hb := (Space.presheaf_yoneda_map_etale_iff B integerBase hZ φ).2 hφ
  have hpet : Space.IsEtale B integerBase hZ p.hom :=
    Space.isEtale_of_isPullback B integerBase hZ _ _ _ _ sq.flip
      ((Space.isEtale_iff_presheaf_of_yoneda B integerBase hZ (yoneda.map φ)).2 hb)
  have ha := (Space.isEtale_iff_presheaf_of_yoneda B integerBase hZ p.hom).1 hpet
  have hcomm : p.hom ≫ X.toBase.hom = yoneda.map q ≫ yoneda.map φ :=
    congrArg (fun k => k.hom) sq.w
  have hq := (Space.holdsOnEveryEtaleChartAtPoint_iff_chartMap B integerBase hZ _
    (fiberDimensionAt_isEtaleLocalOnSourceAndTarget (e : ℕ∞)) X.total.2 (schemeSpace X.base).2
    X.toBase.hom _ p.hom (yoneda.map φ) q ha hb hcomm w r rfl rfl).1 hchart
  have hg := (Space.holdsOnEveryEtaleChartAtPoint_yoneda_map_iff B integerBase hZ _
    (fiberDimensionAt_isEtaleLocalOnSourceAndTarget (e : ℕ∞)) q w).1 hq
  rw [hw, hasFiberDimensionAt_ofSchemeHom_iff] at hg
  rw [hg]
  exact_mod_cast he

/-- If the base change of a family of curves along an étale morphism of the site is a scheme
`Z` over `U`, then every fibre of `Z ⟶ U` has dimension at most one. -/
theorem topologicalKrullDim_fiber_toScheme_map_le_of_isPullback
    (sq : IsPullback p (schemeSpaceMap q) X.toBase (schemeSpaceMap φ))
    (hφ : Etale ((BigFppfOver.toScheme B integerBase hZ).map φ))
    (u : (BigFppfOver.toScheme B integerBase hZ).obj U) :
    topologicalKrullDim (((BigFppfOver.toScheme B integerBase hZ).map q).fiber u) ≤
      ((1 : ℕ) : WithBot ℕ∞) :=
  Stacks.AlgebraicGeometry.ProperFibreDimension.topologicalKrullDim_fiber_le_of_forall _ u 1
    fun z _ => X.topologicalKrullDimAt_fiber_toScheme_map_le_of_isPullback sq hφ z

end CurveFamily

end AlgebraicGeometry

end
