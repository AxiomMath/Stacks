module

public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypePointsLocallyClosedChart
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypePointsLocallyClosed

/-!
# Finite type points of an algebraic stack are dense in closed subsets (Stacks 06G2)

For an algebraic stack `𝒳` and a locally closed subset `T ⊆ |𝒳|` of its point space, if `T` is
nonempty then `T ∩ 𝒳_{ft-pts}` is nonempty; and in particular, for every closed subset
`T ⊆ |𝒳|`, the intersection `T ∩ 𝒳_{ft-pts}` is dense in `T`.

## Main results

* `AlgebraicGeometry.Stack.exists_isFiniteTypePoint_mem_of_isLocallyClosed`: a nonempty locally
  closed set of points contains a finite type point.
* `AlgebraicGeometry.Stack.closure_inter_finiteTypePoints`: for a closed subset `T` of the point
  space, `closure (T ∩ 𝒳_{ft-pts}) = T`.
* `AlgebraicGeometry.Stack.nonempty_inter_and_closure_inter_finiteTypePoints`: both assertions of
  **Stacks 06G2** in a single statement.

## Implementation notes

The point space of `𝒳` carries the topology of **Stacks 04Y8**,
`AlgebraicGeometry.Stack.pointTopology`, which is installed locally with `letI`.

The density clause is stated as the ambient equality `closure (T ∩ 𝒳_{ft-pts}) = T`. For closed
`T` it is equivalent to `T ⊆ closure (T ∩ 𝒳_{ft-pts})`, that is, to the density of
`T ∩ 𝒳_{ft-pts}` in the subspace `T`, the remaining inclusion being `closure_minimal`. It is the
spelling of the scheme-level **Stacks 02J4** and the algebraic-space-level **Stacks 06EK**.

## References

* [Stacks Project, Tag 01XF](https://stacks.math.columbia.edu/tag/01XF)
* [Stacks Project, Tag 026O](https://stacks.math.columbia.edu/tag/026O)
* [Stacks Project, Tag 02J4](https://stacks.math.columbia.edu/tag/02J4)
* [Stacks Project, Tag 04XL](https://stacks.math.columbia.edu/tag/04XL)
* [Stacks Project, Tag 04Y8](https://stacks.math.columbia.edu/tag/04Y8)
* [Stacks Project, Tag 06EK](https://stacks.math.columbia.edu/tag/06EK)
* [Stacks Project, Tag 06FK](https://stacks.math.columbia.edu/tag/06FK)
* [Stacks Project, Tag 06FV](https://stacks.math.columbia.edu/tag/06FV)
* [Stacks Project, Tag 06FX](https://stacks.math.columbia.edu/tag/06FX)
* [Stacks Project, Tag 06FY](https://stacks.math.columbia.edu/tag/06FY)
* [Stacks Project, Tag 06G0](https://stacks.math.columbia.edu/tag/06G0)
* [Stacks Project, Tag 06G2](https://stacks.math.columbia.edu/tag/06G2)
* [Stacks Project, Tag 075V](https://stacks.math.columbia.edu/tag/075V)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### A nonempty locally closed set of points contains a finite type point -/

/-- A nonempty locally closed subset `T` of the point space of an algebraic stack `𝒳` contains
a finite type point of `𝒳`. -/
theorem exists_isFiniteTypePoint_mem_of_isLocallyClosed (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    letI := pointTopology B S hS 𝒳.val
    ∀ T : Set (points B S hS 𝒳.val.val 𝒳.val.property), IsLocallyClosed T → T.Nonempty →
      ∃ x ∈ T, IsFiniteTypePoint.{u, w} B S hS 𝒳 x := by
  classical
  let _ := pointTopology B S hS 𝒳.val
  intro T hT hTne
  obtain ⟨U, a, hasm, hasurj⟩ := exists_smooth_surjective_schemeStack.{u, w} B S hS 𝒳
  obtain ⟨t, htT⟩ := hTne
  obtain ⟨z₀, hz₀⟩ := hasurj t
  let _ := pointTopology B S hS (schemeFibredCategory B S hS U)
  let _ : ∀ i : ((BigFppfOver.toScheme B S hS).obj U).affineOpens,
      TopologicalSpace (points B S hS (schemeFibredCategory B S hS (affChart U i)).val
        (schemeFibredCategory B S hS (affChart U i)).property) :=
    fun i => pointTopology B S hS (schemeFibredCategory B S hS (affChart U i))
  have hcont : @Continuous _ _ (pointTopology B S hS (schemeFibredCategory B S hS U))
      (pointTopology B S hS 𝒳.val)
      (pointsMap B S hS (schemeFibredCategory B S hS U).val
        (schemeFibredCategory B S hS U).property 𝒳.val.property a.hom.hom) :=
    continuous_pointsMap B S hS (schemeFibredCategory B S hS U) 𝒳.val a.hom.hom
  obtain ⟨W, C, hW, hC, hWC⟩ :=
    (hT.preimage hcont).preimage (pointsHomeomorphScheme B S hS U).symm.continuous
  have haz₀ : pointsMap B S hS (schemeFibredCategory B S hS U).val
      (schemeFibredCategory B S hS U).property 𝒳.val.property a.hom.hom z₀ = t := hz₀
  have hz₀mem : pointsHomeomorphScheme B S hS U z₀ ∈ W ∩ C := by
    rw [← hWC]
    change pointsMap B S hS (schemeFibredCategory B S hS U).val
      (schemeFibredCategory B S hS U).property 𝒳.val.property a.hom.hom
      ((pointsHomeomorphScheme B S hS U).symm
        (pointsHomeomorphScheme B S hS U z₀)) ∈ T
    rw [Homeomorph.symm_apply_apply, haz₀]
    exact htT
  obtain ⟨-, ⟨V₀, hV₀, rfl⟩, hmem, hVW⟩ :=
    ((BigFppfOver.toScheme B S hS).obj U).isBasis_affineOpens.exists_subset_of_mem_open
      hz₀mem.1 hW
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (affChart U ⟨V₀, hV₀⟩)) :=
    isAffine_affChart U ⟨V₀, hV₀⟩
  obtain ⟨v, hvC, hvclosed⟩ :=
    Stacks.SerreAffinenessCriterion.exists_isClosed_singleton_mem
      (X := (BigFppfOver.toScheme B S hS).obj (affChart U ⟨V₀, hV₀⟩))
      (hC.preimage ((BigFppfOver.toScheme B S hS).map (affChartHom U ⟨V₀, hV₀⟩)).continuous)
      ⟨⟨pointsHomeomorphScheme B S hS U z₀, hmem⟩, hz₀mem.2⟩
  obtain ⟨y, hy⟩ := (pointsHomeomorphScheme B S hS (affChart U ⟨V₀, hV₀⟩)).surjective v
  have hcomp : pointsMap B S hS (schemeFibredCategory B S hS (affChart U ⟨V₀, hV₀⟩)).val
        (schemeFibredCategory B S hS (affChart U ⟨V₀, hV₀⟩)).property 𝒳.val.property
        (schemeStackMap.{u, w} B S hS (affChartHom U ⟨V₀, hV₀⟩) ≫ a).hom.hom y =
      pointsMap B S hS (schemeFibredCategory B S hS U).val
        (schemeFibredCategory B S hS U).property 𝒳.val.property a.hom.hom
        (pointsMap B S hS (schemeFibredCategory B S hS (affChart U ⟨V₀, hV₀⟩)).val
          (schemeFibredCategory B S hS (affChart U ⟨V₀, hV₀⟩)).property
          (schemeFibredCategory B S hS U).property
          (schemeStackMap.{u, w} B S hS (affChartHom U ⟨V₀, hV₀⟩)).hom.hom y) :=
    congrFun (AlgebraicStacks.pointsMap_comp B S hS
      (schemeStackMap.{u, w} B S hS (affChartHom U ⟨V₀, hV₀⟩)) a) y
  have hchart : pointsMap B S hS (schemeFibredCategory B S hS (affChart U ⟨V₀, hV₀⟩)).val
        (schemeFibredCategory B S hS (affChart U ⟨V₀, hV₀⟩)).property
        (schemeFibredCategory B S hS U).property
        (schemeStackMap.{u, w} B S hS (affChartHom U ⟨V₀, hV₀⟩)).hom.hom y =
      (pointsHomeomorphScheme B S hS U).symm
        ((BigFppfOver.toScheme B S hS).map (affChartHom U ⟨V₀, hV₀⟩) v) := by
    refine (pointsHomeomorphScheme B S hS U).injective ?_
    rw [Homeomorph.apply_symm_apply, ← hy]
    exact pointsHomeomorphScheme_naturality B S hS (affChartHom U ⟨V₀, hV₀⟩) y
  refine ⟨pointsMap B S hS (schemeFibredCategory B S hS (affChart U ⟨V₀, hV₀⟩)).val
      (schemeFibredCategory B S hS (affChart U ⟨V₀, hV₀⟩)).property 𝒳.val.property
      (schemeStackMap.{u, w} B S hS (affChartHom U ⟨V₀, hV₀⟩) ≫ a).hom.hom y, ?_, ?_⟩
  · have hmemWC : (BigFppfOver.toScheme B S hS).map (affChartHom U ⟨V₀, hV₀⟩) v ∈ W ∩ C := by
      refine ⟨hVW ?_, hvC⟩
      rw [affChartHom_toScheme]
      exact (Scheme.Opens.range_ι V₀) ▸ Set.mem_range_self v
    rw [← hWC] at hmemWC
    rw [hcomp, hchart]
    exact hmemWC
  · refine isFiniteTypePoint_of_exists_isClosed_smoothChart.{u, w} B S hS 𝒳 _
      ⟨affChart U ⟨V₀, hV₀⟩, schemeStackMap.{u, w} B S hS (affChartHom U ⟨V₀, hV₀⟩) ≫ a, y, ?_,
        ?_, rfl⟩
    · exact AlgebraicStacks.isSmooth_comp B S hS _ _
        (isSmooth_schemeStackMap.{u, w} B S hS (affChartHom U ⟨V₀, hV₀⟩)
          (smooth_affChartHom U ⟨V₀, hV₀⟩)) hasm
    · rw [hy]
      exact hvclosed

/-! ### Stacks 06G2 -/

/-- For a closed subset `T` of the point space of an algebraic stack `𝒳`, the closure of the set
of finite type points lying in `T` is `T` itself; that is, `T ∩ 𝒳_{ft-pts}` is dense in `T`. -/
@[stacks 06G2 "closed subsets, in the spelling of the scheme-level Stacks 02J4 and the \
algebraic-space-level Stacks 06EK: for a closed subset of the point space, the closure of its \
intersection with the set of finite type points is the subset itself"]
theorem closure_inter_finiteTypePoints (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    letI := pointTopology B S hS 𝒳.val
    ∀ T : Set (points B S hS 𝒳.val.val 𝒳.val.property), IsClosed T →
      closure (T ∩ finiteTypePoints B S hS 𝒳) = T := by
  let _ := pointTopology B S hS 𝒳.val
  intro T hT
  exact subset_antisymm (closure_minimal Set.inter_subset_left hT)
    (subset_closure_inter_finiteTypePoints_of_isClosed.{u, w} B S hS 𝒳 T hT)

/-- Let `𝒳` be an algebraic stack over `S`. Then

* for any locally closed subset `T ⊆ |𝒳|` of its point space, `T ≠ ∅ → T ∩ 𝒳_{ft-pts} ≠ ∅`; and
* in particular, for any closed subset `T ⊆ |𝒳|` the closure of `T ∩ 𝒳_{ft-pts}` is `T`, that
  is, `T ∩ 𝒳_{ft-pts}` is dense in `T`. -/
@[stacks 06G2 "both assertions: for a locally closed subset T of the point space of an algebraic \
stack, T nonempty implies that T meets the set of finite type points; and in particular, for a \
closed subset T, the intersection of T with the set of finite type points is dense in T"]
theorem nonempty_inter_and_closure_inter_finiteTypePoints
    (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    letI := pointTopology B S hS 𝒳.val
    (∀ T : Set (points B S hS 𝒳.val.val 𝒳.val.property), IsLocallyClosed T → T.Nonempty →
        (T ∩ finiteTypePoints B S hS 𝒳).Nonempty) ∧
      ∀ T : Set (points B S hS 𝒳.val.val 𝒳.val.property), IsClosed T →
        closure (T ∩ finiteTypePoints B S hS 𝒳) = T :=
  ⟨exists_mem_finiteTypePoints_of_isLocallyClosed.{u, w} B S hS 𝒳,
    closure_inter_finiteTypePoints.{u, w} B S hS 𝒳⟩

end AlgebraicGeometry.Stack

end
