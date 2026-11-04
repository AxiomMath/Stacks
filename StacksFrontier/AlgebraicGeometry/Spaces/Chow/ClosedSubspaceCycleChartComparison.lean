module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ClosedSubspaceChartMultiplicity
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ChartChowSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.StructureSheafGenericPointLength
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackAssociatedCycle
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.IntegralClosedSubspaceMaps
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalenceDefs

/-!
# The cycle of a closed subspace agrees with the cycle of its chart base change

Let `Y ⊆ X` be a closed subspace of a good algebraic space `X/B` in Situation 0EDT, and let `V`
be a surjective étale scheme chart of `X`.  The base change `V ×_X Y` is a closed subscheme of
the scheme `V` (`AlgebraicGeometry.Space.isClosedImmersion_closedSubspaceBaseChangeChartProj`),
so the scheme theory of chapter 42 attaches to it the cycle `[V ×_X Y]_k` of Stacks 02QU on the
base situation `AlgebraicGeometry.Space.chartChowSituation` of the chart.  This file identifies
its coefficients with those of the algebraic-space cycle `[Y]_k` of Stacks 0EE9.

## The two conventions and why they agree

The coefficient of `[Y]_k` at an integral closed subspace `Z ⊆ X` is a supremum over the
integral closed subspaces `W ⊆ Y` with image `Z`, a set with at most one element; the coefficient
of `[V ×_X Y]_k` at a point `v` of the chart is a `dite` over the generic points `ξ` of `V ×_X Y`
with `ξ ↦ v`.  Three steps match them, at a chart point `v` over the generic point of `Z`:

* the δ-dimension conditions agree, by
  `AlgebraicGeometry.Space.deltaDimension_eq_relativeDimension_id_chartChowSituation`;
* the values agree, by
  `AlgebraicGeometry.Space.closedSubspaceMultiplicity_eq_componentMultiplicity` and
  `AlgebraicGeometry.Space.cycleCoeffOfClosedSubspace_eq_closedSubspaceMultiplicity`;
* the index conditions agree.

The last was the open point, and the apparent obstruction was an asymmetry.  A `W` with image
`Z` exists as soon as `|Z| ⊆ |Y|`, whereas a *generic* point `ξ` of `V ×_X Y` over `v` exists
only when `W` is a component of `Y`; in the remaining case the space-side coefficient vanishes
only through the `⊤ ↦ 0` convention of `ENat.toNat`, the length of `𝒪_Y` at a point which is not
a component being infinite.  What removes the asymmetry rather than accommodating it is
`AlgebraicGeometry.Space.mem_genericPoints_iff_of_chartSchemeToPoints_eq`: being a generic point
of a chart of `Y` is a property of the image in `|Y|`, so *some* lift of `v` to `V ×_X Y` is a
generic point exactly when a *chosen* lift is.  A chosen lift always exists
(`AlgebraicGeometry.Space.exists_closedSubspaceBaseChangeChartProj_eq`, Stacks 03H4), and
whether it is generic decides both coefficients at once: if it is, both are the multiplicity of
Stacks 02QU; if it is not, the scheme side has no `ξ` to choose and the space side has an
infinite length, so both are zero.

## Hypotheses

Beyond Situation 0EDT and the chart, the only hypothesis is `D.IsGood (Y.ι ≫ sX)`, that `Y` is
itself good over the base.  **It is a hypothesis of the source's situation, not a stand-in for a
missing result**: the chapter carries it wherever it works with a closed subspace as a space in
its own right (for instance at
`AlgebraicGeometry.Space.gysinIntersectionSubspace`).  It is used twice, for the decency of `Y`
needed to recognise an integral closed subspace of `X` inside `|Y|` as the image of one of `Y`
(`AlgebraicGeometry.Space.IntegralClosedSubspace.exists_pushforward_eq`), and for the local
Noetherianity of `Y` that Stacks 0EE4 asks for
(`AlgebraicGeometry.Space.hasEtaleLocalProperty_isLocallyNoetherian_of_isGood`).

The function `γ` choosing geometric representatives is a parameter of
`AlgebraicGeometry.Space.cycleCoeffOfClosedSubspace`, not a hypothesis of the source; it is
required here only to lie over the point it is taken at, which
`AlgebraicGeometry.Space.canonicalGeometricPoint` satisfies.

## Main results

* `AlgebraicGeometry.Space.cycleCoeffOfClosedSubspace_eq_cycleAssociatedToClosedSubscheme_chart`

## References

* [Stacks Project, Tag 02QU](https://stacks.math.columbia.edu/tag/02QU)
* [Stacks Project, Tag 0EE9](https://stacks.math.columbia.edu/tag/0EE9)
* [Stacks Project, Tag 0EE4](https://stacks.math.columbia.edu/tag/0EE4)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- **The identity is a legitimate structure morphism for the base situation on a chart.**  The
identity of a chart scheme is locally of finite type, being an isomorphism, so it can be fed to
the cycle constructions of chapter 42 as the structure morphism of the chart over the base scheme
of `AlgebraicGeometry.Space.chartChowSituation`, which is the chart scheme itself.

The codomain is written as that base scheme rather than as `chartScheme V`.  The two are equal by
definition, but the instance argument of a cycle construction records the codomain, so an instance
stated at the other spelling is not found by instance search, which unfolds only reducible
definitions. -/
theorem locallyOfFiniteType_id_chartChowSituation (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (V : SmallEtale D.site D.base D.base_mem X)
    (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme D.site D.base D.base_mem))) V.obj.hom) :
    @LocallyOfFiniteType (chartScheme V) (chartChowSituation D sX hX V hs).S
      (𝟙 (chartScheme V)) :=
  inferInstanceAs (LocallyOfFiniteType (𝟙 (chartScheme V)))

/-- **The coefficient of `[Y]_k` is the coefficient of `[V ×_X Y]_k` on a chart.**  Let `Y ⊆ X`
be a closed subspace of a good algebraic space `X/B`, itself good over the base, let `V` be a
surjective étale scheme chart of `X`, let `Z ⊆ X` be an integral closed subspace and let `v` be
a point of the chart over the generic point of `Z`.  Then the coefficient of `Z` in the cycle
`[Y]_k` of Stacks 0EE9 is the coefficient of `v` in the cycle `[V ×_X Y]_k` of Stacks 02QU for
the base situation on the chart.

The proof is the three-step match described in the module documentation.  The index conditions
agree because a chosen lift `y` of `v` to `V ×_X Y` exists (Stacks 03H4) and, by
`AlgebraicGeometry.Space.mem_genericPoints_iff_of_chartSchemeToPoints_eq`, is a generic point
exactly when some generic point of `V ×_X Y` lies over `v`. -/
theorem cycleCoeffOfClosedSubspace_eq_cycleAssociatedToClosedSubscheme_chart
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (Y : Subfunctor X)
    (hY : IsClosedSubspace D.site D.base D.base_mem Y)
    (hYgood : D.IsGood (Y.ι ≫ sX))
    (V : SmallEtale D.site D.base D.base_mem X)
    (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme D.site D.base D.base_mem))) V.obj.hom)
    (k : ℤ)
    (γ : points D.site D.base D.base_mem Y.toFunctor →
      GeometricPoint D.site D.base D.base_mem Y.toFunctor)
    (hγ : ∀ y, (γ y).image = y)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) (v : chartScheme V)
    (hv : chartSchemeToPoints D.site D.base D.base_mem X V v =
      Z.ambientGenericPoint D.site D.base D.base_mem) :
    haveI hft := locallyOfFiniteType_id_chartChowSituation D sX hX V hs
    haveI hci := isClosedImmersion_closedSubspaceBaseChangeChartProj D.site D.base D.base_mem
      hX.1 Y hY V
    cycleCoeffOfClosedSubspace D sX hX Y hY k γ Z =
      (Stacks.Chow.cycleAssociatedToClosedSubscheme (chartChowSituation D sX hX V hs)
        (𝟙 (chartScheme V))
        (closedSubspaceBaseChangeChartProj D.site D.base D.base_mem hX.1 Y hY V) k).1 v := by
  classical
  have hft := locallyOfFiniteType_id_chartChowSituation D sX hX V hs
  have hci := isClosedImmersion_closedSubspaceBaseChangeChartProj D.site D.base D.base_mem
    hX.1 Y hY V
  have hYdec : IsDecentSpace D.site D.base D.base_mem Y.toFunctor :=
    D.isDecentSpace_of_isGood (Y.ι ≫ sX) hYgood
  have hYLN : HasEtaleLocalProperty D.site D.base D.base_mem Y.toFunctor
      (fun T : Scheme.{u} => IsLocallyNoetherian T) :=
    hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D (Y.ι ≫ sX) hYgood
  have hrel : Stacks.Chow.relativeDimension
      (chartChowSituation D sX hX V hs).dimensionFunction
      (𝟙 (chartScheme V)) v = deltaDimension D sX Z :=
    (deltaDimension_eq_relativeDimension_id_chartChowSituation D sX hX V hs Z v hv).symm
  -- points of the chart of `Y` are determined by their images in `|X|`
  have hemb := isClosedEmbedding_pointsMap_of_isClosedImmersion D.site D.base D.base_mem
    hX.1 hY.2
  have hcomm := chartSchemeToPoints_closedSubspaceBaseChangeChartProj D.site D.base D.base_mem
    hX.1 Y hY V
  -- A generic point of `V ×_X Y` over `v` lies over the generic point of the integral closed
  -- subspace `W ⊆ Y` with image `Z`, whenever that exists.
  by_cases hk : deltaDimension D sX Z = k
  · by_cases hsub : subspacePointSet D.site D.base D.base_mem X Z.subspace ⊆
        subspacePointSet D.site D.base D.base_mem X Y
    · -- `|Z| ⊆ |Y|`, so `Z` is the image of an integral closed subspace `W ⊆ Y`.
      obtain ⟨W, hW⟩ := IntegralClosedSubspace.exists_pushforward_eq D.site D.base D.base_mem
        hX.1 hY.1 (D.isDecentSpace_of_isGood sX hX) hYdec hY.2 Z hsub
      have hW' : closedSubspaceComponentImage D sX hX Y hY W = Z := hW
      have hagp : pointsMap D.site D.base D.base_mem Y.toFunctor Y.ι
          (W.ambientGenericPoint D.site D.base D.base_mem) =
          Z.ambientGenericPoint D.site D.base D.base_mem := by
        rw [← hW]
        exact (IntegralClosedSubspace.ambientGenericPoint_pushforward D.site D.base D.base_mem
          hX.1 hY.1 (D.isDecentSpace_of_isGood sX hX) hY.2 W).symm
      -- the space-side coefficient is the multiplicity `m_{W, Y}`
      have hspace : cycleCoeffOfClosedSubspace D sX hX Y hY k γ Z =
          closedSubspaceMultiplicity D Y hY W := by
        rw [← hW']
        exact cycleCoeffOfClosedSubspace_eq_closedSubspaceMultiplicity D sX hX Y hY k γ W
          (hγ _) (hW' ▸ hk)
      -- a chosen lift of `v` to the chart `V ×_X Y` of `Y`
      have hvY : chartSchemeToPoints D.site D.base D.base_mem X V v ∈
          subspacePointSet D.site D.base D.base_mem X Y := by
        rw [hv, ← hagp]; exact ⟨_, rfl⟩
      obtain ⟨y, hy⟩ := exists_closedSubspaceBaseChangeChartProj_eq D.site D.base D.base_mem
        hX.1 Y hY V v hvY
      have hyagp : chartSchemeToPoints D.site D.base D.base_mem Y.toFunctor
          (closedSubspaceBaseChangeChart D.site D.base D.base_mem hX.1 Y hY V) y =
          W.ambientGenericPoint D.site D.base D.base_mem :=
        hemb.injective (by rw [← hcomm, hy, hv, hagp])
      by_cases hgen : y ∈ genericPoints
          (chartScheme (closedSubspaceBaseChangeChart D.site D.base D.base_mem hX.1 Y hY V))
      · -- both coefficients are the multiplicity of Stacks 02QU at `⟨y, hgen⟩`
        rw [hspace, closedSubspaceMultiplicity_eq_componentMultiplicity D hX.1 Y hY V W
          ⟨y, hgen⟩ hyagp, ← hy]
        exact (Stacks.Chow.cycleAssociatedToClosedSubscheme_apply
          (chartChowSituation D sX hX V hs) (𝟙 (chartScheme V)) _ k
          ⟨y, hgen⟩ (by rw [hy]; exact hrel.trans hk)).symm
      · -- no lift of `v` is a generic point, so both coefficients vanish
        have hnone : ¬ ∃ ξ : genericPoints
            (chartScheme (closedSubspaceBaseChangeChart D.site D.base D.base_mem hX.1 Y hY V)),
            closedSubspaceBaseChangeChartProj D.site D.base D.base_mem hX.1 Y hY V ξ.1 = v ∧
              Stacks.Chow.relativeDimension (chartChowSituation D sX hX V hs).dimensionFunction
                (𝟙 (chartScheme V)) v = k := by
          rintro ⟨ξ, hξ, -⟩
          refine hgen ((mem_genericPoints_iff_of_chartSchemeToPoints_eq D.site D.base D.base_mem
            ⟨Y.toFunctor, hY.1⟩ hYLN _ _ ξ.1 y ?_).mp ξ.2)
          exact hemb.injective (by rw [← hcomm, ← hcomm, hξ, hy])
        rw [Stacks.Chow.cycleAssociatedToClosedSubscheme_apply_eq_zero
          (chartChowSituation D sX hX V hs) (𝟙 (chartScheme V)) _ k v hnone,
          hspace, closedSubspaceMultiplicity]
        norm_cast
        exact toNat_geometricLength_structureSheafModule_eq_zero_of_notMem_genericPoints
          D.site D.base D.base_mem ⟨Y.toFunctor, hY.1⟩ hYLN _ _ y
          (hyagp.trans (canonicalGeometricPoint_image D.site D.base D.base_mem Y.toFunctor
            (W.ambientGenericPoint D.site D.base D.base_mem)).symm) hgen
    · -- `|Z| ⊄ |Y|`: there is no `W` and no generic point of `V ×_X Y` over `v`
      have hZW : ∀ W : IntegralClosedSubspace D.site D.base D.base_mem Y.toFunctor,
          closedSubspaceComponentImage D sX hX Y hY W ≠ Z := by
        intro W hWZ
        refine hsub ?_
        rw [← hWZ, IntegralClosedSubspace.subspacePointSet_pushforward]
        exact Set.image_subset_range _ _
      rw [cycleCoeffOfClosedSubspace_eq_zero D sX hX Y hY k γ Z hZW,
        Stacks.Chow.cycleAssociatedToClosedSubscheme_apply_eq_zero
          (chartChowSituation D sX hX V hs) (𝟙 (chartScheme V)) _ k v]
      rintro ⟨ξ, hξ, -⟩
      refine hsub (IntegralClosedSubspace.subspacePointSet_subset_of_ambientGenericPoint_mem D
        hX.1 Z (isClosed_subspacePointSet_of_isClosedSubspace D hX.1 Y hY) ?_)
      rw [← hv, ← hξ,
        chartSchemeToPoints_closedSubspaceBaseChangeChartProj D.site D.base D.base_mem
          hX.1 Y hY V ξ.1]
      exact ⟨_, rfl⟩
  · -- the δ-dimension condition fails on both sides
    rw [cycleCoeffOfClosedSubspace, ite_eq_right hk,
      Stacks.Chow.cycleAssociatedToClosedSubscheme_apply_eq_zero
        (chartChowSituation D sX hX V hs) (𝟙 (chartScheme V)) _ k v]
    rintro ⟨ξ, -, hdim⟩
    exact hk (hrel.symm.trans hdim)

end AlgebraicGeometry.Space

end
