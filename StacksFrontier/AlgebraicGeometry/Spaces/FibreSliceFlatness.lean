module

public import StacksFrontier.AlgebraicGeometry.Spaces.FibreChartNeighborhoodChartMap
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreChartRegularityDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleLocusOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicPullbackWeaklyAssociated

/-!
# The flatness half of Stacks 06LW for a fibre over a field factoring through a chart

Let `g : X ⟶ Y` be a flat, locally finitely presented morphism of algebraic spaces over a scheme
`S` in a big fppf site, let `f₁, …, f_r ∈ Γ(X, 𝒪_X)`, let `q : V ⟶ Y` be a surjective étale
scheme chart of the target and let `Spec k' ⟶ Y` be a point of the target which **factors through
`V`**.  Let `F = X ×_Y Spec k'` be the fibre and let `z` be a geometric point of `F` at which the
`f_i` have regular images in the étale local ring `𝒪_{F, z̄}`.

This file concludes, with no further hypothesis, that after replacing `X` by an open subspace
containing the image of `z` the closed subspace `V(f₁, …, f_r)` is flat over `Y` — that is, the
flatness half of Stacks 06LW for such a fibre.  What separates this from Stacks 06LW itself is
only the factorisation: the source first enlarges the field `k` of the given point of the fibre
until the enlarged field spectrum maps to `Y` through the chart, and that enlargement is not
performed here.

## Main results

* `exists_isOpenSubspace_isFlat_vanishingSubfunctor_of_isRegular_fiber_factorThroughChart`:
  the flatness half of Stacks 06LW for a fibre whose point factors through a chart.

## Implementation notes

The three ingredients are the chart construction
`AlgebraicGeometry.Space.exists_smallEtaleNeighborhood_fiberBaseChange_chartMap`, which produces
the chart `U` of `X` over `V`, the small étale neighbourhood of `z` whose scheme is the base change
`U_v ×_{κ(v)} Spec k'` of the scheme-theoretic fibre, and the morphism of the site between the two
charts; the descent of the fibre hypothesis to the local ring of `U_v`,
`AlgebraicGeometry.Space.isRegular_chartFiber_of_isRegular_etaleLocalRing`; and the slicing and
descent step
`AlgebraicGeometry.Space.exists_isOpenSubspace_isFlat_vanishingSubfunctor_of_isRegular_chartFiber`.

The hypothesis is taken in the form the source's conclusion is used in — quantified over the
small étale neighbourhoods of the image of `z` in `X` — which is the same condition for one
neighbourhood as for all, the image of a germ of a global function under the comparison
homomorphism of Stacks 04NG not depending on the neighbourhood.  It is the form in which
Stacks 06MD states it, `Stacks.AlgebraicGeometry.FibreIsRegularSequenceAt`.

The conclusion names the image of `z` in the point space of `X` rather than the point of the
chart that the slicing step returns; the two agree because a chart diagram carries the point of
`X` determined by a chart point to the point determined by its image
(`AlgebraicGeometry.Space.chartSchemeToPoints_map_chartDiagram`) and because the chart point of a
small étale neighbourhood lies over the image of the geometric point
(`AlgebraicGeometry.Space.chartPoint_isChartPoint`).

## References

* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 04NG](https://stacks.math.columbia.edu/tag/04NG)
* [Stacks Project, Tag 05VU](https://stacks.math.columbia.edu/tag/05VU)
* [Stacks Project, Tag 06LI](https://stacks.math.columbia.edu/tag/06LI)
* [Stacks Project, Lemma 06LW](https://stacks.math.columbia.edu/tag/06LW)
* [Stacks Project, Tag 06NF](https://stacks.math.columbia.edu/tag/06NF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The flatness half of Stacks 06LW for a fibre over a field factoring through a chart.**
Let `g : X ⟶ Y` be a flat, locally finitely presented morphism of algebraic spaces over `S`, let
`f₁, …, f_r ∈ Γ(X, 𝒪_X)`, let `q : V ⟶ Y` be a surjective étale scheme chart of the target and
let `ρ : Spec k' ⟶ V` exhibit a field-valued point of `Y` as factoring through that chart.  Let
`ξ : F ⟶ X` and `π : F ⟶ Spec k'` present `F` as the fibre `X ×_Y Spec k'` and let `z` be a
geometric point of `F` at which the images of the `f_i` in the étale local ring `𝒪_{F, z̄}` form a
regular sequence.

Then there is an open subspace `W ⊆ X` containing the image of `z` such that
`V(f₁, …, f_r) ∩ W ⟶ Y` is flat. -/
theorem exists_isOpenSubspace_isFlat_vanishingSubfunctor_of_isRegular_fiber_factorThroughChart
    (X Y F : AlgebraicSpaces B S hS) (g : X.1 ⟶ Y.1)
    (hgflat : IsFlat B S hS g) (hglfp : IsLocallyOfFinitePresentation B S hS g)
    {r : ℕ} (fs : Fin r → (SheafOfModules.unit (structureRingSheaf B S hS X)).sections)
    (V : BigFppfOver B S hS) (q : yoneda.obj V ⟶ Y.1)
    (hqS : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) q)
    (hqE : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) q)
    {k' : Type u} [Field k'] (hk' : B.Contains (Spec (.of k'))) (b' : Spec (.of k') ⟶ S)
    (ρ : (Over.mk (⟨b'⟩ : B.obj hk' ⟶ B.obj hS) : BigFppfOver B S hS) ⟶ V)
    (ξ : F ⟶ X) {π : F.1 ⟶ yoneda.obj (Over.mk (⟨b'⟩ : B.obj hk' ⟶ B.obj hS))}
    (sq : IsPullback ξ.hom π g (yoneda.map ρ ≫ q))
    (z : GeometricPoint B S hS F.1)
    (hreg : ∀ Nx : SmallEtaleNeighborhood (geometricPointMap ξ.hom z),
      RingTheory.Sequence.IsRegular (etaleLocalRing B S hS F.1 z)
        (List.ofFn fun i : Fin r => etaleLocalRingMap F.2 ξ.hom z
          (etaleLocalRingGerm B S hS X.1 (geometricPointMap ξ.hom z) (op Nx)
            ((fs i).eval (op Nx.chart))))) :
    ∃ (W : Subfunctor X.1) (_ : IsOpenSubspace B S hS W),
      pointsMap B S hS F.1 ξ.hom z.image ∈
          Set.range (pointsMap B S hS W.toFunctor W.ι) ∧
        IsFlat B S hS (((vanishingSubfunctor B S hS X fs).preimage W.ι).ι ≫ W.ι ≫ g) := by
  obtain ⟨U, gUV, aX, N, gNU, v, φ, haXS, haXE, hcomm, hsqN, -, e, he⟩ :=
    exists_smallEtaleNeighborhood_fiberBaseChange_chartMap B S hS X.2 Y.2 F.2 g V q hqS hqE hk' b'
      ρ sq z
  have hregA := isRegular_chartFiber_of_isRegular_etaleLocalRing B S hS ξ N
    (⟨CostructuredArrow.mk aX, haXE⟩ : SmallEtale B S hS X.1) gNU hsqN gUV φ e he fs
    (hreg (targetNeighborhood B S hS N
      (⟨CostructuredArrow.mk aX, haXE⟩ : SmallEtale B S hS X.1) gNU hsqN))
  obtain ⟨W, hWopen, hmem, hflat⟩ :=
    exists_isOpenSubspace_isFlat_vanishingSubfunctor_of_isRegular_chartFiber B S hS X Y g
      hgflat hglfp fs (⟨CostructuredArrow.mk aX, haXE⟩ : SmallEtale B S hS X.1) V q
      ((isEtale_iff_presheaf_of_yoneda B S hS q).2 hqE) gUV hcomm.symm
      ((BigFppfOver.toScheme B S hS).map gNU (chartPoint B S hS F.1 N)) hregA
  refine ⟨W, hWopen, ?_, hflat⟩
  rw [← show chartSchemeToPoints B S hS X.1
      (⟨CostructuredArrow.mk aX, haXE⟩ : SmallEtale B S hS X.1)
      ((BigFppfOver.toScheme B S hS).map gNU (chartPoint B S hS F.1 N)) =
      pointsMap B S hS F.1 ξ.hom z.image from ?_]
  · exact hmem
  refine Eq.trans (chartSchemeToPoints_map_chartDiagram B S hS
    ({ U := N.chart, V := ⟨CostructuredArrow.mk aX, haXE⟩, g := gNU, comm := hsqN } :
      ChartDiagram B S hS F.1 X.1 ξ.hom) (chartPoint B S hS F.1 N)) ?_
  refine congrArg (pointsMap B S hS F.1 ξ.hom) ?_
  rw [chartSchemeToPoints_eq_pointsMap_pointsEquivScheme_symm]
  exact (chartPoint_iff_pointOfEtaleChart_eq B S hS N.chart (chartPoint B S hS F.1 N)
    z.image).1 (chartPoint_isChartPoint B S hS z N)

end AlgebraicGeometry.Space

end
