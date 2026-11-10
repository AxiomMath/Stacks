module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ClosedSubspaceCycleChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FirstChernClassCap

/-!
# The right-hand side of Stacks 0EQL, read on an étale chart

Let `X/B` be a good algebraic space in Situation 0EDT, let `s` be a global section of an
`𝒪_X`-module `ℒ` and let `V` be a surjective étale scheme chart of `X`.  The right-hand side of
Stacks 0EQL is the weighted sum `∑ n_i [Z(s_i)]_k` of
`AlgebraicGeometry.Space.componentZeroCycleSumCoeff`, over the irreducible components
`X_i ⊆ X` of δ-dimension `k + 1`.  This file reads both of its factors as coefficients of cycles
of Stacks 02QU on `V`, for the base situation `AlgebraicGeometry.Space.chartChowSituation`, which
is the form in which the scheme case Stacks 0EPI — `Stacks.Chow.zeroCycle_eq_sum_components` —
states them.  It is the counterpart on the right-hand side of
`AlgebraicGeometry.Space.cycleCoeffOfClosedSubspace_eq_cycleAssociatedToClosedSubscheme_chart`,
which is the dictionary for the left.

## The two factors

The multiplicity `n_i` is the coefficient of `X_i` in `[X]_{k+1} = [𝒪_X]_{k+1}`, a length of
`𝒪_X` at a geometric point.  On the chart it becomes the coefficient of `[V]_{k+1}` — the cycle
of `V` as a closed subscheme of *itself* — at a chart point over the generic point of `X_i`: the
scheme-side multiplicity of a component is the length of the local ring of the subscheme over
itself (`Stacks.Chow.componentMultiplicity_eq_length_stalk`), which for the identity is
`𝒪_{V, v}`, and that is the geometric length by Stacks 0EE1 on the chart
(`AlgebraicGeometry.Space.geometricLength_structureSheafModule_eq_length_chartStalk`).  The index
conditions agree through Stacks 0EE4 at the structure sheaf: away from the generic points of the
chart the geometric length is `⊤`, so its `ENat.toNat` is zero exactly where the `dite` of
Stacks 02QU takes its else-branch.

The cycle `[Z(s_i)]_k`, pushed forward along `X_i → X`, is a cycle of a closed subspace of a
closed subspace, so the comparison is one level deeper than the dictionary for the left-hand
side: the chain is `Z(s|_{X_i}) ⊆ X_i ⊆ X`, and the chart of `Z(s|_{X_i})` is the double base
change `(V ×_X X_i) ×_{X_i} Z(s|_{X_i})`, a closed subscheme of `V` through the composite of the
two projections.  The general statement for such a chain is
`cycleClosedPushforward_cycleCoeffOfClosedSubspace_eq_cycleAssociatedToClosedSubscheme_chart`,
which takes the closed immersion of the chart into `V` as a parameter together with the two
conditions it has to satisfy — compatibility with the maps to `|X|`, and the lifting of a chart
point lying over the subspace.  Taking it as a parameter is deliberate: the closed subscheme of
`V` that Stacks 0EPI actually works with is cut out by an ideal sheaf, not presented as a fibre
product, and it can be substituted for the double base change without touching the proof.

## Hypotheses

Beyond Situation 0EDT and the chart, the hypotheses are of three kinds, and none of them stands
in for a missing result.

* `D.IsGood (Z(s|_{X_i}).ι ≫ X_i.ι ≫ sX)`, that the zero scheme of `s|_{X_i}` is itself good over
  the base.  This is the hypothesis the chapter carries wherever it treats a closed subspace as a
  space in its own right, exactly as `D.IsGood (Y.ι ≫ sX)` is carried in
  `StacksFrontier.AlgebraicGeometry.Spaces.Chow.ClosedSubspaceCycleChartComparison`; it is used for
  the decency and the local Noetherianity of the zero scheme.
* That the chosen geometric representatives lie over the points they are assigned to.  The
  functions `γ` and `γW` are parameters of
  `AlgebraicGeometry.Space.componentZeroCycleSumCoeff`, not hypotheses of the source.
* A chart point over the generic point of each component, `wpt`.  The cycle of Stacks 02QU
  records a multiplicity at a point of the chart, and the chart being surjective such a point
  exists; which one is a choice.

## What this does not do

It does not reindex the sum.  Stacks 0EPI sums over the irreducible components of the *scheme*
`V` of δ-dimension `k + 1`, whereas the sum here is over the components of `|X|`; the map from
the former to the latter is surjective but not injective, two components of an étale chart being
able to lie over one component of the space.  Grouping them is
`StacksFrontier.AlgebraicGeometry.Spaces.BranchesOverComponents`.  Nor does it identify the chart of
a zero scheme with the closed subscheme of `V` that Stacks 0EPI cuts out by an ideal sheaf: that
is the compatibility of the zero scheme of Stacks 0845 with base change, the derivation named as
missing in the docstring of `AlgebraicGeometry.Space.ComponentVanishingLocusOver`.

## Main definitions

* `AlgebraicGeometry.Space.componentVanishingLocusChart`: the étale chart
  `(V ×_X W) ×_W Z(s|_W)` of the zero scheme of `s|_W` on an integral closed subspace `W ⊆ X`.
* `AlgebraicGeometry.Space.componentVanishingLocusChartImmersion`: its closed immersion into the
  chart `V` of `X`.

## Main results

* `AlgebraicGeometry.Space.fundamentalCycleCoeff_eq_cycleAssociatedToClosedSubscheme_id_chart`:
  the multiplicity `n_i`, read on the chart.
* `cycleClosedPushforward_cycleCoeffOfClosedSubspace_eq_cycleAssociatedToClosedSubscheme_chart`:
  the cycle of a closed subspace of a closed subspace `Y ⊆ W ⊆ X`, pushed forward to `X` and read
  on a chart of `X`.
* `AlgebraicGeometry.Space.componentZeroCycleCoeff_eq_cycleAssociatedToClosedSubscheme_chart`:
  the cycle `[Z(s|_{X_i})]_k`, pushed forward to `X` and read on the chart.
* `componentZeroCycleSumCoeff_eq_finsum_cycleAssociatedToClosedSubscheme_chart`:
  the weighted sum `∑ n_i [Z(s_i)]_k`, read on the chart.

## References

* [Stacks Project, Tag 02QU](https://stacks.math.columbia.edu/tag/02QU)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 0845](https://stacks.math.columbia.edu/tag/0845)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EE1](https://stacks.math.columbia.edu/tag/0EE1)
* [Stacks Project, Tag 0EE4](https://stacks.math.columbia.edu/tag/0EE4)
* [Stacks Project, Tag 0EE9](https://stacks.math.columbia.edu/tag/0EE9)
* [Stacks Project, Tag 0EEB](https://stacks.math.columbia.edu/tag/0EEB)
* [Stacks Project, Tag 0EPI](https://stacks.math.columbia.edu/tag/0EPI)
* [Stacks Project, Tag 0EQL](https://stacks.math.columbia.edu/tag/0EQL)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- The coefficient of `[Z]_k` at the image of a generic point `t` of `Z` of relative dimension `k`
is the length of the stalk of `Z` at `t` over itself. -/
private theorem cycleAssociatedToClosedSubscheme_apply_eq_toNat_length
    (C : Stacks.Chow.ChowSituation.{u}) {Y Z : _root_.AlgebraicGeometry.Scheme.{u}} (p : Y ⟶ C.S)
    [_root_.AlgebraicGeometry.LocallyOfFiniteType p] (i : Z ⟶ Y)
    [_root_.AlgebraicGeometry.IsClosedImmersion i] (k : ℤ) {y : Y} (t : Z)
    (ht : i t = y) (hgen : t ∈ genericPoints Z)
    (hdim : Stacks.Chow.relativeDimension C.dimensionFunction p y = k) :
    (Stacks.Chow.cycleAssociatedToClosedSubscheme C p i k).1 y =
      ((Module.length (Z.presheaf.stalk t) (Z.presheaf.stalk t)).toNat : ℤ) := by
  subst ht
  exact (Stacks.Chow.cycleAssociatedToClosedSubscheme_apply C p i k ⟨t, hgen⟩ hdim).trans
    (Stacks.Chow.componentMultiplicity_eq_length_stalk i ⟨t, hgen⟩)

/-- **The coefficient of the fundamental cycle `[X]_n` is a coefficient of `[V]_n` on a chart.**
Let `X/B` be a good algebraic space, let `V` be a surjective étale scheme chart of `X`, let
`Z ⊆ X` be an integral closed subspace and let `v` be a point of the chart over the generic point
of `Z`.  Then the coefficient of `Z` in `[X]_n = [𝒪_X]_n` is the coefficient of `v` in the cycle
of Stacks 02QU of `V` as a closed subscheme of itself, for the base situation on the chart.

This is the multiplicity `n_i` of Stacks 0EQL read on the chart.  The value agrees because the
scheme-side multiplicity of a component is a length of the local ring of the subscheme over
itself (`Stacks.Chow.componentMultiplicity_eq_length_stalk`), here `𝒪_{V, v}`, and that is the
length of `𝒪_X` at a geometric point by Stacks 0EE1 on the chart
(`AlgebraicGeometry.Space.geometricLength_structureSheafModule_eq_length_chartStalk`).  The index
conditions agree by Stacks 0EE4 at the structure sheaf: if `v` is not a generic point of the
chart the geometric length is `⊤`, whose `ENat.toNat` is zero, while the `dite` of Stacks 02QU
has no generic point to choose. -/
theorem fundamentalCycleCoeff_eq_cycleAssociatedToClosedSubscheme_id_chart
    (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (V : SmallEtale D.site D.base D.base_mem X)
    (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme D.site D.base D.base_mem))) V.obj.hom)
    (n : ℤ)
    (γ : Space.points D.site D.base D.base_mem X →
      GeometricPoint D.site D.base D.base_mem X)
    (hγ : ∀ x, (γ x).image = x)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) (v : chartScheme V)
    (hv : chartSchemeToPoints D.site D.base D.base_mem X V v =
      Z.ambientGenericPoint D.site D.base D.base_mem) :
    haveI _hft := locallyOfFiniteType_id_chartChowSituation D sX hX V hs
    fundamentalCycleCoeff D sX hX n γ Z =
      (Stacks.Chow.cycleAssociatedToClosedSubscheme (chartChowSituation D sX hX V hs)
        (𝟙 (chartScheme V)) (𝟙 (chartScheme V)) n).1 v := by
  classical
  have hft := locallyOfFiniteType_id_chartChowSituation D sX hX V hs
  have hrel : Stacks.Chow.relativeDimension
      (chartChowSituation D sX hX V hs).dimensionFunction
      (𝟙 (chartScheme V)) v = deltaDimension D sX Z :=
    (deltaDimension_eq_relativeDimension_id_chartChowSituation D sX hX V hs Z v hv).symm
  have hXLN : HasEtaleLocalProperty D.site D.base D.base_mem X
      (fun T : Scheme.{u} => IsLocallyNoetherian T) :=
    hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX
  have hvbar : chartSchemeToPoints D.site D.base D.base_mem X V v =
      (γ (Z.ambientGenericPoint D.site D.base D.base_mem)).image :=
    hv.trans (hγ _).symm
  by_cases hk : deltaDimension D sX Z = n
  · by_cases hgen : v ∈ genericPoints (chartScheme V)
    · rw [fundamentalCycleCoeff, cycleCoeffOfModule, ite_eq_left hk,
        geometricLength_structureSheafModule_eq_length_chartStalk D.site D.base D.base_mem
          ⟨X, hX.1⟩ (γ (Z.ambientGenericPoint D.site D.base D.base_mem)) V v hvbar]
      exact (cycleAssociatedToClosedSubscheme_apply_eq_toNat_length _ _ (𝟙 (chartScheme V)) n v
        rfl hgen (hrel.trans hk)).symm
    · rw [fundamentalCycleCoeff, cycleCoeffOfModule, ite_eq_left hk,
        Stacks.Chow.cycleAssociatedToClosedSubscheme_apply_eq_zero
          (chartChowSituation D sX hX V hs) (𝟙 (chartScheme V)) (𝟙 (chartScheme V)) n v
          (by rintro ⟨ξ, hξ, -⟩; exact hgen (hξ ▸ ξ.2))]
      norm_cast
      exact toNat_geometricLength_structureSheafModule_eq_zero_of_notMem_genericPoints
        D.site D.base D.base_mem ⟨X, hX.1⟩ hXLN
        (γ (Z.ambientGenericPoint D.site D.base D.base_mem)) V v hvbar hgen
  · rw [fundamentalCycleCoeff, cycleCoeffOfModule, ite_eq_right hk,
      Stacks.Chow.cycleAssociatedToClosedSubscheme_apply_eq_zero
        (chartChowSituation D sX hX V hs) (𝟙 (chartScheme V)) (𝟙 (chartScheme V)) n v]
    rintro ⟨ξ, -, hdim⟩
    exact hk (hrel.symm.trans hdim)

/-- **The cycle of a closed subspace of a closed subspace, read on a chart of the ambient
space.**  Let `Y ⊆ W ⊆ X` be closed subspaces of a good algebraic space `X/B`, with `W` and `Y`
good over the base, let `V` be a surjective étale scheme chart of `X`, and let `j` be a closed
immersion of the scheme of an étale chart `T` of `Y` into the chart scheme `V` which is
compatible with the maps to `|X|` (`hjpt`) and through which a point of `V` lying over `|Y|`
lifts (`hjlift`).  Then at a point `v` of the chart over the generic point of an integral closed
subspace `Z ⊆ X`, the coefficient of `Z` in the pushforward to `X` of the `k`-cycle `[Y]_k` of
Stacks 0EE9 is the coefficient of `v` in the cycle `[T]_k` of Stacks 02QU, for the base situation
on the chart.

The proof is the three-step match of
`AlgebraicGeometry.Space.cycleCoeffOfClosedSubspace_eq_cycleAssociatedToClosedSubscheme_chart`,
of which this is the generalization to a chain of two closed subspaces: the δ-dimension
conditions agree by
`AlgebraicGeometry.Space.deltaDimension_eq_relativeDimension_id_chartChowSituation` and
`AlgebraicGeometry.Space.deltaDimension_closedSubspaceComponentImage`, the values agree by
Stacks 0EE1 on the chart `T`, and the index conditions agree because `j` is injective and, where
no lift of `v` is a generic point, the length of `𝒪_Y` there is infinite — Stacks 0EE4 at the
structure sheaf.

`j` and `T` are parameters rather than the base change `(V ×_X W) ×_W Y` because the closed
subscheme of a chart that a scheme-side statement works with is in general presented by an ideal
sheaf; for the base change itself see
`AlgebraicGeometry.Space.componentZeroCycleCoeff_eq_cycleAssociatedToClosedSubscheme_chart`. -/
theorem cycleClosedPushforward_cycleCoeffOfClosedSubspace_eq_cycleAssociatedToClosedSubscheme_chart
    (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (W : Subfunctor X) (hW : IsClosedSubspace D.site D.base D.base_mem W)
    (hWgood : D.IsGood (W.ι ≫ sX))
    (Y : Subfunctor W.toFunctor) (hY : IsClosedSubspace D.site D.base D.base_mem Y)
    (hYgood : D.IsGood (Y.ι ≫ W.ι ≫ sX))
    (V : SmallEtale D.site D.base D.base_mem X)
    (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme D.site D.base D.base_mem))) V.obj.hom)
    (T : SmallEtale D.site D.base D.base_mem Y.toFunctor)
    (j : chartScheme T ⟶ chartScheme V)
    [_root_.AlgebraicGeometry.IsClosedImmersion j]
    (hjpt : ∀ t : chartScheme T,
      chartSchemeToPoints D.site D.base D.base_mem X V (j t) =
        pointsMap D.site D.base D.base_mem W.toFunctor W.ι
          (pointsMap D.site D.base D.base_mem Y.toFunctor Y.ι
            (chartSchemeToPoints D.site D.base D.base_mem Y.toFunctor T t)))
    (hjlift : ∀ u : chartScheme V,
      (∃ y, pointsMap D.site D.base D.base_mem W.toFunctor W.ι
          (pointsMap D.site D.base D.base_mem Y.toFunctor Y.ι y) =
        chartSchemeToPoints D.site D.base D.base_mem X V u) → ∃ t, j t = u)
    (k : ℤ)
    (γ : Space.points D.site D.base D.base_mem Y.toFunctor →
      GeometricPoint D.site D.base D.base_mem Y.toFunctor)
    (hγ : ∀ y, (γ y).image = y)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) (v : chartScheme V)
    (hv : chartSchemeToPoints D.site D.base D.base_mem X V v =
      Z.ambientGenericPoint D.site D.base D.base_mem) :
    haveI _hft := locallyOfFiniteType_id_chartChowSituation D sX hX V hs
    cycleClosedPushforward D hX.1 hW.1 (D.isDecentSpace_of_isGood sX hX) hW.2
        (cycleCoeffOfClosedSubspace D (W.ι ≫ sX) hWgood Y hY k γ) Z =
      (Stacks.Chow.cycleAssociatedToClosedSubscheme (chartChowSituation D sX hX V hs)
        (𝟙 (chartScheme V)) j k).1 v := by
  classical
  have hft := locallyOfFiniteType_id_chartChowSituation D sX hX V hs
  have hXdec : IsDecentSpace D.site D.base D.base_mem X := D.isDecentSpace_of_isGood sX hX
  have hWdec : IsDecentSpace D.site D.base D.base_mem W.toFunctor :=
    D.isDecentSpace_of_isGood (W.ι ≫ sX) hWgood
  have hYdec : IsDecentSpace D.site D.base D.base_mem Y.toFunctor :=
    D.isDecentSpace_of_isGood (Y.ι ≫ W.ι ≫ sX) hYgood
  have hYLN : HasEtaleLocalProperty D.site D.base D.base_mem Y.toFunctor
      (fun P : Scheme.{u} => IsLocallyNoetherian P) :=
    hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D (Y.ι ≫ W.ι ≫ sX) hYgood
  have hinjW := (isClosedEmbedding_pointsMap_of_isClosedImmersion D.site D.base D.base_mem
    hX.1 hW.2).injective
  have hinjY := (isClosedEmbedding_pointsMap_of_isClosedImmersion D.site D.base D.base_mem
    hW.1 hY.2).injective
  have hinjj : Function.Injective j := j.isClosedEmbedding.injective
  have hrel : Stacks.Chow.relativeDimension
      (chartChowSituation D sX hX V hs).dimensionFunction
      (𝟙 (chartScheme V)) v = deltaDimension D sX Z :=
    (deltaDimension_eq_relativeDimension_id_chartChowSituation D sX hX V hs Z v hv).symm
  by_cases hZW : ∃ Z' : IntegralClosedSubspace D.site D.base D.base_mem W.toFunctor,
      closedSubspaceComponentImage D sX hX W hW Z' = Z
  · obtain ⟨Z', rfl⟩ := hZW
    have hZagp : pointsMap D.site D.base D.base_mem W.toFunctor W.ι
        (Z'.ambientGenericPoint D.site D.base D.base_mem) =
        (closedSubspaceComponentImage D sX hX W hW Z').ambientGenericPoint
          D.site D.base D.base_mem :=
      (IntegralClosedSubspace.ambientGenericPoint_pushforward D.site D.base D.base_mem
        hX.1 hW.1 hXdec hW.2 Z').symm
    have hrel' : Stacks.Chow.relativeDimension
        (chartChowSituation D sX hX V hs).dimensionFunction
        (𝟙 (chartScheme V)) v = deltaDimension D (W.ι ≫ sX) Z' :=
      hrel.trans (deltaDimension_closedSubspaceComponentImage D sX hX W hW Z')
    rw [cycleClosedPushforward_apply_pushforward]
    by_cases hk : deltaDimension D (W.ι ≫ sX) Z' = k
    · by_cases hsub : subspacePointSet D.site D.base D.base_mem W.toFunctor Z'.subspace ⊆
          subspacePointSet D.site D.base D.base_mem W.toFunctor Y
      · obtain ⟨U, hU⟩ := IntegralClosedSubspace.exists_pushforward_eq D.site D.base D.base_mem
          hW.1 hY.1 hWdec hYdec hY.2 Z' hsub
        have hU' : closedSubspaceComponentImage D (W.ι ≫ sX) hWgood Y hY U = Z' := hU
        have hUagp : pointsMap D.site D.base D.base_mem Y.toFunctor Y.ι
            (U.ambientGenericPoint D.site D.base D.base_mem) =
            Z'.ambientGenericPoint D.site D.base D.base_mem := by
          rw [← hU]
          exact (IntegralClosedSubspace.ambientGenericPoint_pushforward D.site D.base D.base_mem
            hW.1 hY.1 hWdec hY.2 U).symm
        have hspace : cycleCoeffOfClosedSubspace D (W.ι ≫ sX) hWgood Y hY k γ Z' =
            closedSubspaceMultiplicity D Y hY U := by
          rw [← hU']
          exact cycleCoeffOfClosedSubspace_eq_closedSubspaceMultiplicity D (W.ι ≫ sX) hWgood
            Y hY k γ U (hγ _) (hU' ▸ hk)
        obtain ⟨t, ht⟩ := hjlift v
          ⟨U.ambientGenericPoint D.site D.base D.base_mem, by rw [hUagp, hZagp, hv]⟩
        have hTagp : chartSchemeToPoints D.site D.base D.base_mem Y.toFunctor T t =
            U.ambientGenericPoint D.site D.base D.base_mem := by
          refine hinjY (hinjW ?_)
          rw [← hjpt t, ht, hv, ← hZagp, hUagp]
        by_cases hgen : t ∈ genericPoints (chartScheme T)
        · rw [hspace, cycleAssociatedToClosedSubscheme_apply_eq_toNat_length _ _ j k t ht hgen
            (hrel'.trans hk), closedSubspaceMultiplicity,
            geometricLength_structureSheafModule_eq_length_chartStalk D.site D.base D.base_mem
              ⟨Y.toFunctor, hY.1⟩ (canonicalGeometricPoint D.site D.base D.base_mem Y.toFunctor
                (U.ambientGenericPoint D.site D.base D.base_mem)) T t
              (hTagp.trans (canonicalGeometricPoint_image D.site D.base D.base_mem
                Y.toFunctor (U.ambientGenericPoint D.site D.base D.base_mem)).symm)]
        · rw [hspace, Stacks.Chow.cycleAssociatedToClosedSubscheme_apply_eq_zero
            (chartChowSituation D sX hX V hs) (𝟙 (chartScheme V)) j k v
            (by rintro ⟨ξ, hξ, -⟩; exact hgen (hinjj (hξ.trans ht.symm) ▸ ξ.2)),
            closedSubspaceMultiplicity]
          norm_cast
          exact toNat_geometricLength_structureSheafModule_eq_zero_of_notMem_genericPoints
            D.site D.base D.base_mem ⟨Y.toFunctor, hY.1⟩ hYLN _ T t
            (hTagp.trans (canonicalGeometricPoint_image D.site D.base D.base_mem Y.toFunctor
              (U.ambientGenericPoint D.site D.base D.base_mem)).symm) hgen
      · rw [cycleCoeffOfClosedSubspace_eq_zero D (W.ι ≫ sX) hWgood Y hY k γ Z'
            (fun U hU => hsub (by
              rw [← hU, IntegralClosedSubspace.subspacePointSet_pushforward]
              exact Set.image_subset_range _ _)),
          Stacks.Chow.cycleAssociatedToClosedSubscheme_apply_eq_zero
            (chartChowSituation D sX hX V hs) (𝟙 (chartScheme V)) j k v]
        rintro ⟨ξ, hξ, -⟩
        refine hsub (IntegralClosedSubspace.subspacePointSet_subset_of_ambientGenericPoint_mem D
          hW.1 Z' (isClosed_subspacePointSet_of_isClosedSubspace D hW.1 Y hY) ?_)
        refine ⟨chartSchemeToPoints D.site D.base D.base_mem Y.toFunctor T ξ.1, hinjW ?_⟩
        rw [← hjpt ξ.1, hξ, hv, ← hZagp]
    · rw [cycleCoeffOfClosedSubspace, ite_eq_right hk,
        Stacks.Chow.cycleAssociatedToClosedSubscheme_apply_eq_zero
          (chartChowSituation D sX hX V hs) (𝟙 (chartScheme V)) j k v]
      rintro ⟨ξ, -, hdim⟩
      exact hk (hrel'.symm.trans hdim)
  · rw [cycleClosedPushforward_apply_of_forall_ne D hX.1 hW.1 hXdec hW.2 _ Z
      fun Z' hZ' => hZW ⟨Z', hZ'⟩,
      Stacks.Chow.cycleAssociatedToClosedSubscheme_apply_eq_zero
        (chartChowSituation D sX hX V hs) (𝟙 (chartScheme V)) j k v]
    rintro ⟨ξ, hξ, -⟩
    refine hZW (IntegralClosedSubspace.exists_pushforward_eq D.site D.base D.base_mem
      hX.1 hW.1 hXdec hWdec hW.2 Z
      (IntegralClosedSubspace.subspacePointSet_subset_of_ambientGenericPoint_mem D hX.1 Z
        (isClosed_subspacePointSet_of_isClosedSubspace D hX.1 W hW) ?_))
    refine ⟨pointsMap D.site D.base D.base_mem Y.toFunctor Y.ι
      (chartSchemeToPoints D.site D.base D.base_mem Y.toFunctor T ξ.1), ?_⟩
    rw [← hjpt ξ.1, hξ, hv]

section ZeroCycleOfSection

variable (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (L : Modules.{u, u} D.site D.base D.base_mem X hX.1) (s : L.sections) (k : ℤ)

/-- The étale chart `(V ×_X W) ×_W Z(s|_W)` of the zero scheme of `s|_W` on an integral closed
subspace `W ⊆ X`, obtained by base changing an étale chart `V` of `X` twice. -/
abbrev componentVanishingLocusChart (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (V : SmallEtale D.site D.base D.base_mem X) :
    SmallEtale D.site D.base D.base_mem
      (componentVanishingLocus D sX hX L s W).1.toFunctor :=
  closedSubspaceBaseChangeChart D.site D.base D.base_mem W.isClosedSubspace.1
    (componentVanishingLocus D sX hX L s W).1 (componentVanishingLocus D sX hX L s W).2
    (closedSubspaceBaseChangeChart D.site D.base D.base_mem hX.1 W.subspace
      W.isClosedSubspace V)

/-- The morphism of schemes `(V ×_X W) ×_W Z(s|_W) ⟶ V` cutting the chart of `Z(s|_W)` out of
the chart `V` of `X`: the composite of the two base-change projections. -/
abbrev componentVanishingLocusChartImmersion
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (V : SmallEtale D.site D.base D.base_mem X) :
    chartScheme (componentVanishingLocusChart D sX hX L s W V) ⟶ chartScheme V :=
  closedSubspaceBaseChangeChartProj D.site D.base D.base_mem W.isClosedSubspace.1
      (componentVanishingLocus D sX hX L s W).1 (componentVanishingLocus D sX hX L s W).2
      (closedSubspaceBaseChangeChart D.site D.base D.base_mem hX.1 W.subspace
        W.isClosedSubspace V) ≫
    closedSubspaceBaseChangeChartProj D.site D.base D.base_mem hX.1 W.subspace
      W.isClosedSubspace V

/-- **The chart of `Z(s|_W)` is a closed subscheme of the chart of `X`**: both base-change
projections are closed immersions of schemes, and so is their composite. -/
theorem isClosedImmersion_componentVanishingLocusChartImmersion
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (V : SmallEtale D.site D.base D.base_mem X) :
    _root_.AlgebraicGeometry.IsClosedImmersion
      (componentVanishingLocusChartImmersion D sX hX L s W V) := by
  have := isClosedImmersion_closedSubspaceBaseChangeChartProj D.site D.base D.base_mem
    hX.1 W.subspace W.isClosedSubspace V
  have := isClosedImmersion_closedSubspaceBaseChangeChartProj D.site D.base D.base_mem
    W.isClosedSubspace.1 (componentVanishingLocus D sX hX L s W).1
    (componentVanishingLocus D sX hX L s W).2
    (closedSubspaceBaseChangeChart D.site D.base D.base_mem hX.1 W.subspace
      W.isClosedSubspace V)
  infer_instance

/-- The two base-change projections are compatible with the maps to `|X|`: a point of the chart
of `Z(s|_W)` determines a point of `|Z(s|_W)|` whose image in `|X|`, taken through `W`, is the
point determined by its image in the chart of `X`. -/
theorem chartSchemeToPoints_componentVanishingLocusChartImmersion
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (V : SmallEtale D.site D.base D.base_mem X)
    (t : chartScheme (componentVanishingLocusChart D sX hX L s W V)) :
    chartSchemeToPoints D.site D.base D.base_mem X V
        (componentVanishingLocusChartImmersion D sX hX L s W V t) =
      pointsMap D.site D.base D.base_mem W.subspace.toFunctor W.subspace.ι
        (pointsMap D.site D.base D.base_mem
          (componentVanishingLocus D sX hX L s W).1.toFunctor
          (componentVanishingLocus D sX hX L s W).1.ι
          (chartSchemeToPoints D.site D.base D.base_mem
            (componentVanishingLocus D sX hX L s W).1.toFunctor
            (componentVanishingLocusChart D sX hX L s W V) t)) := by
  rw [show componentVanishingLocusChartImmersion D sX hX L s W V t =
      closedSubspaceBaseChangeChartProj D.site D.base D.base_mem hX.1 W.subspace
        W.isClosedSubspace V
        (closedSubspaceBaseChangeChartProj D.site D.base D.base_mem W.isClosedSubspace.1
          (componentVanishingLocus D sX hX L s W).1
          (componentVanishingLocus D sX hX L s W).2 _ t) from rfl,
    chartSchemeToPoints_closedSubspaceBaseChangeChartProj D.site D.base D.base_mem
      hX.1 W.subspace W.isClosedSubspace V,
    chartSchemeToPoints_closedSubspaceBaseChangeChartProj D.site D.base D.base_mem
      W.isClosedSubspace.1 (componentVanishingLocus D sX hX L s W).1
      (componentVanishingLocus D sX hX L s W).2 _ t]

/-- **A point of the chart of `X` over a point of `Z(s|_W)` lifts to the chart of `Z(s|_W)`**:
Stacks 03H4 applied to each of the two base changes in turn. -/
theorem exists_componentVanishingLocusChartImmersion_eq
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (V : SmallEtale D.site D.base D.base_mem X) (u : chartScheme V)
    (hu : ∃ y, pointsMap D.site D.base D.base_mem W.subspace.toFunctor W.subspace.ι
        (pointsMap D.site D.base D.base_mem
          (componentVanishingLocus D sX hX L s W).1.toFunctor
          (componentVanishingLocus D sX hX L s W).1.ι y) =
      chartSchemeToPoints D.site D.base D.base_mem X V u) :
    ∃ t, componentVanishingLocusChartImmersion D sX hX L s W V t = u := by
  obtain ⟨y, hy⟩ := hu
  have hinjW := (isClosedEmbedding_pointsMap_of_isClosedImmersion D.site D.base D.base_mem
    hX.1 W.isClosedSubspace.2).injective
  obtain ⟨w, hw⟩ := exists_closedSubspaceBaseChangeChartProj_eq D.site D.base D.base_mem
    hX.1 W.subspace W.isClosedSubspace V u (hy ▸ ⟨_, rfl⟩)
  obtain ⟨t, ht⟩ := exists_closedSubspaceBaseChangeChartProj_eq D.site D.base D.base_mem
    W.isClosedSubspace.1 (componentVanishingLocus D sX hX L s W).1
    (componentVanishingLocus D sX hX L s W).2 _ w ⟨y, hinjW (by
      rw [← chartSchemeToPoints_closedSubspaceBaseChangeChartProj D.site D.base D.base_mem
        hX.1 W.subspace W.isClosedSubspace V w, hw, ← hy])⟩
  refine ⟨t, ?_⟩
  rw [show componentVanishingLocusChartImmersion D sX hX L s W V t =
      closedSubspaceBaseChangeChartProj D.site D.base D.base_mem hX.1 W.subspace
        W.isClosedSubspace V
        (closedSubspaceBaseChangeChartProj D.site D.base D.base_mem W.isClosedSubspace.1
          (componentVanishingLocus D sX hX L s W).1
          (componentVanishingLocus D sX hX L s W).2 _ t) from rfl, ht, hw]

/-- **The coefficient of `[Z(s|_W)]_k` pushed forward to `X` is a coefficient of the cycle of a
closed subscheme of a chart.**  Let `W ⊆ X` be an integral closed subspace of a good algebraic
space `X/B`, let `s` be a global section of an `𝒪_X`-module `ℒ`, let `V` be a surjective étale
scheme chart of `X`, let `Z ⊆ X` be an integral closed subspace and let `v` be a point of the
chart over the generic point of `Z`.  Then the coefficient of `Z` in the pushforward along
`W → X` of the `k`-cycle `[Z(s|_W)]_k` of Stacks 0EE9 is the coefficient of `v` in the cycle of
Stacks 02QU of the chart of `Z(s|_W)`, read as a closed subscheme of `V` through
`AlgebraicGeometry.Space.componentVanishingLocusChartImmersion`, for the base situation on the
chart.

This is
`cycleClosedPushforward_cycleCoeffOfClosedSubspace_eq_cycleAssociatedToClosedSubscheme_chart`
at the chain `Z(s|_W) ⊆ W ⊆ X` and the double chart base change, whose two point hypotheses are
`AlgebraicGeometry.Space.chartSchemeToPoints_componentVanishingLocusChartImmersion` and
`AlgebraicGeometry.Space.exists_componentVanishingLocusChartImmersion_eq`. -/
theorem componentZeroCycleCoeff_eq_cycleAssociatedToClosedSubscheme_chart
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hVLgood : D.IsGood ((componentVanishingLocus D sX hX L s W).1.ι ≫ W.subspace.ι ≫ sX))
    (V : SmallEtale D.site D.base D.base_mem X)
    (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme D.site D.base D.base_mem))) V.obj.hom)
    (γ : Space.points D.site D.base D.base_mem
        (componentVanishingLocus D sX hX L s W).1.toFunctor →
      GeometricPoint D.site D.base D.base_mem
        (componentVanishingLocus D sX hX L s W).1.toFunctor)
    (hγ : ∀ y, (γ y).image = y)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) (v : chartScheme V)
    (hv : chartSchemeToPoints D.site D.base D.base_mem X V v =
      Z.ambientGenericPoint D.site D.base D.base_mem) :
    haveI _hft := locallyOfFiniteType_id_chartChowSituation D sX hX V hs
    haveI _hci := isClosedImmersion_componentVanishingLocusChartImmersion D sX hX L s W V
    componentZeroCycleCoeff D sX hX L s k W γ Z =
      (Stacks.Chow.cycleAssociatedToClosedSubscheme (chartChowSituation D sX hX V hs)
        (𝟙 (chartScheme V))
        (componentVanishingLocusChartImmersion D sX hX L s W V) k).1 v := by
  have hci := isClosedImmersion_componentVanishingLocusChartImmersion D sX hX L s W V
  exact cycleClosedPushforward_cycleCoeffOfClosedSubspace_eq_cycleAssociatedToClosedSubscheme_chart
    D sX hX W.subspace W.isClosedSubspace (isGood_integralClosedSubspace D sX hX W)
    (componentVanishingLocus D sX hX L s W).1 (componentVanishingLocus D sX hX L s W).2
    hVLgood V hs _ _
    (chartSchemeToPoints_componentVanishingLocusChartImmersion D sX hX L s W V)
    (exists_componentVanishingLocusChartImmersion_eq D sX hX L s W V) k γ hγ Z v hv

/-- **The chart dictionary for the right-hand side of Stacks 0EQL.**  The weighted sum
`∑ n_i [Z(s_i)]_k` of `AlgebraicGeometry.Space.componentZeroCycleSumCoeff`, evaluated at an
integral closed subspace `Z ⊆ X`, is the sum over the same index set — the irreducible
components `X_i ⊆ X` of δ-dimension `k + 1` — of the product of two coefficients of cycles of
Stacks 02QU on a surjective étale scheme chart `V` of `X`, for the base situation
`AlgebraicGeometry.Space.chartChowSituation`:

* the multiplicity `n_i`, read as the coefficient of `[V]_{k+1}` — the cycle of `V` as a closed
  subscheme of itself — at a chart point `wpt i` over the generic point of `X_i`;
* the coefficient at `v` of the cycle `[Z(s_i) ×_X V]_k` of the chart of `Z(s|_{X_i})`, read as
  a closed subscheme of `V`.

The chart points `wpt i` over the generic points of the components are a parameter, as is the
point `v` over the generic point of `Z`: the cycle of Stacks 02QU records a multiplicity at a
point of the chart, and which point of the chart over a given point of `|X|` is taken is a
choice.  Such points exist, by
`AlgebraicGeometry.Space.surjective_chartSchemeToPoints` at the surjectivity `hs` of the chart;
they are left as parameters because the comparison with Stacks 0EPI wants them to be the generic
points of the components of the *scheme* `V`.

This is the dictionary the comparison with the scheme-side Stacks 0EPI,
`Stacks.Chow.zeroCycle_eq_sum_components`, needs on the right-hand side; what it does **not**
do is reindex the sum.  Stacks 0EPI sums over the irreducible components of the *scheme* `V` of
δ-dimension `k + 1`, and the map from those to the components of `|X|` is surjective but not
injective — two components of a chart may lie over one component of the space, which is the
branch grouping of `StacksFrontier.AlgebraicGeometry.Spaces.BranchesOverComponents`. -/
theorem componentZeroCycleSumCoeff_eq_finsum_cycleAssociatedToClosedSubscheme_chart
    (γ : Space.points D.site D.base D.base_mem X →
      GeometricPoint D.site D.base D.base_mem X)
    (hγ : ∀ x, (γ x).image = x)
    (γW : ComponentGeometricRepresentatives D sX hX L s k)
    (hγW : ∀ (W : ComponentsOfDeltaDimension D sX hX (k + 1)) y, (γW W y).image = y)
    (hVLgood : ∀ W : ComponentsOfDeltaDimension D sX hX (k + 1),
      D.IsGood ((componentVanishingLocus D sX hX L s W.1).1.ι ≫ W.1.subspace.ι ≫ sX))
    (V : SmallEtale D.site D.base D.base_mem X)
    (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme D.site D.base D.base_mem))) V.obj.hom)
    (wpt : ComponentsOfDeltaDimension D sX hX (k + 1) → chartScheme V)
    (hwpt : ∀ W, chartSchemeToPoints D.site D.base D.base_mem X V (wpt W) =
      W.1.ambientGenericPoint D.site D.base D.base_mem)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) (v : chartScheme V)
    (hv : chartSchemeToPoints D.site D.base D.base_mem X V v =
      Z.ambientGenericPoint D.site D.base D.base_mem) :
    haveI _hft := locallyOfFiniteType_id_chartChowSituation D sX hX V hs
    haveI _hci : ∀ W : ComponentsOfDeltaDimension D sX hX (k + 1),
        _root_.AlgebraicGeometry.IsClosedImmersion
          (componentVanishingLocusChartImmersion D sX hX L s W.1 V) :=
      fun W => isClosedImmersion_componentVanishingLocusChartImmersion D sX hX L s W.1 V
    componentZeroCycleSumCoeff D sX hX L s k γ γW Z =
      ∑ᶠ W : ComponentsOfDeltaDimension D sX hX (k + 1),
        (Stacks.Chow.cycleAssociatedToClosedSubscheme (chartChowSituation D sX hX V hs)
            (𝟙 (chartScheme V)) (𝟙 (chartScheme V)) (k + 1)).1 (wpt W) *
          (Stacks.Chow.cycleAssociatedToClosedSubscheme (chartChowSituation D sX hX V hs)
            (𝟙 (chartScheme V))
            (componentVanishingLocusChartImmersion D sX hX L s W.1 V) k).1 v := by
  have hft := locallyOfFiniteType_id_chartChowSituation D sX hX V hs
  have hci : ∀ W : ComponentsOfDeltaDimension D sX hX (k + 1),
      _root_.AlgebraicGeometry.IsClosedImmersion
        (componentVanishingLocusChartImmersion D sX hX L s W.1 V) :=
    fun W => isClosedImmersion_componentVanishingLocusChartImmersion D sX hX L s W.1 V
  rw [componentZeroCycleSumCoeff]
  refine finsum_congr fun W => ?_
  rw [fundamentalCycleCoeff_eq_cycleAssociatedToClosedSubscheme_id_chart D sX hX V hs (k + 1)
      γ hγ W.1 (wpt W) (hwpt W),
    componentZeroCycleCoeff_eq_cycleAssociatedToClosedSubscheme_chart D sX hX L s k W.1
      (hVLgood W) V hs (γW W) (hγW W) Z v hv]

end ZeroCycleOfSection

end AlgebraicGeometry.Space

end
