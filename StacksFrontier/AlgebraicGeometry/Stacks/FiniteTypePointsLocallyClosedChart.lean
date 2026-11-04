module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypePointsLocallyClosed

/-!
# Finite type points meet every nonempty locally closed subset (Stacks 06G2)

**Stacks 06G2** says that for an algebraic stack `𝒳` and a nonempty locally closed subset
`T ⊆ |𝒳|` of its point space (**Stacks 04XL**), `T` contains a finite type point, and that
consequently for a *closed* subset `T` the finite type points lying in `T` are dense in `T`.

## Main results

* `AlgebraicGeometry.Stack.exists_mem_finiteTypePoints_of_isLocallyClosed`: **Stacks 06G2**, first
  clause.
* `AlgebraicGeometry.Stack.subset_closure_inter_finiteTypePoints_of_isClosed`: **Stacks 06G2**,
  second clause.
* `AlgebraicGeometry.Stack.eq_univ_of_isOpen_of_finiteTypePoints_subset`: an open subset of the
  point space containing every finite type point is everything.

## References

* [Stacks Project, Tag 026O](https://stacks.math.columbia.edu/tag/026O)
* [Stacks Project, Tag 04XL](https://stacks.math.columbia.edu/tag/04XL)
* [Stacks Project, Tag 06FK](https://stacks.math.columbia.edu/tag/06FK)
* [Stacks Project, Tag 06FX](https://stacks.math.columbia.edu/tag/06FX)
* [Stacks Project, Tag 06G2](https://stacks.math.columbia.edu/tag/06G2)
* [Stacks Project, Tag 06N3](https://stacks.math.columbia.edu/tag/06N3)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A nonempty locally closed subset of the point space of an algebraic stack contains a finite
type point. -/
@[stacks 06G2 "the first clause: a nonempty locally closed subset of the point space meets the \
set of finite type points"]
theorem exists_mem_finiteTypePoints_of_isLocallyClosed (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    letI := pointTopology B S hS 𝒳.val
    ∀ T : Set (points B S hS 𝒳.val.val 𝒳.val.property), IsLocallyClosed T → T.Nonempty →
      (T ∩ finiteTypePoints B S hS 𝒳).Nonempty := by
  classical
  let := pointTopology B S hS 𝒳.val
  intro T hT hTne
  obtain ⟨U, a, hasm, hasurj⟩ := exists_smooth_surjective_schemeStack.{u, w} B S hS 𝒳
  let := pointTopology B S hS (schemeFibredCategory B S hS U)
  set p := pointsMap B S hS (schemeFibredCategory B S hS U).val
    (schemeFibredCategory B S hS U).property 𝒳.val.property a.hom.hom with hpdef
  have hpcont : Continuous p :=
    continuous_pointsMap B S hS (schemeFibredCategory B S hS U) 𝒳.val a.hom.hom
  set h := pointsHomeomorphScheme B S hS U with hhdef
  set T' : Set ((BigFppfOver.toScheme B S hS).obj U) := h.symm ⁻¹' (p ⁻¹' T) with hT'def
  have hT' : IsLocallyClosed T' :=
    (hT.preimage hpcont).preimage h.symm.continuous
  obtain ⟨x₀, hx₀⟩ := hTne
  obtain ⟨z₀, hz₀⟩ := hasurj x₀
  have hz₀T' : h z₀ ∈ T' := by
    change p (h.symm (h z₀)) ∈ T
    rw [Homeomorph.symm_apply_apply]
    convert hx₀
  obtain ⟨O, Z, hO, hZ, hOZ⟩ := hT'
  have hz₀O : h z₀ ∈ O := (hOZ ▸ hz₀T').1
  obtain ⟨-, ⟨V₀, hV₀, rfl⟩, hz₀V₀, hV₀O⟩ :=
    ((BigFppfOver.toScheme B S hS).obj U).isBasis_affineOpens.exists_subset_of_mem_open
      hz₀O hO
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (affChart U ⟨V₀, hV₀⟩)) :=
    isAffine_affChart U ⟨V₀, hV₀⟩
  set ι := (BigFppfOver.toScheme B S hS).map (affChartHom U ⟨V₀, hV₀⟩) with hιdef
  obtain ⟨v, hvZ, hvclosed⟩ :=
    Stacks.SerreAffinenessCriterion.exists_isClosed_singleton_mem
      (X := (BigFppfOver.toScheme B S hS).obj (affChart U ⟨V₀, hV₀⟩))
      (hZ.preimage ι.continuous) (⟨⟨h z₀, hz₀V₀⟩, (hOZ ▸ hz₀T').2⟩ : (ι ⁻¹' Z).Nonempty)
  let := pointTopology B S hS (schemeFibredCategory B S hS (affChart U ⟨V₀, hV₀⟩))
  obtain ⟨y, hy⟩ := (pointsHomeomorphScheme B S hS (affChart U ⟨V₀, hV₀⟩)).surjective v
  set c := schemeStackMap.{u, w} B S hS (affChartHom U ⟨V₀, hV₀⟩) with hcdef
  set w₀ := pointsMap B S hS (schemeFibredCategory B S hS (affChart U ⟨V₀, hV₀⟩)).val
    (schemeFibredCategory B S hS (affChart U ⟨V₀, hV₀⟩)).property
    (schemeFibredCategory B S hS U).property c.hom.hom y with hw₀def
  have hw₀ : h w₀ = ι v := by
    refine (pointsHomeomorphScheme_naturality B S hS (affChartHom U ⟨V₀, hV₀⟩) y).trans ?_
    rw [hy]
  have hιv : ι v ∈ O := hV₀O v.2
  refine ⟨pointsMap B S hS (schemeFibredCategory B S hS (affChart U ⟨V₀, hV₀⟩)).val
      (schemeFibredCategory B S hS (affChart U ⟨V₀, hV₀⟩)).property 𝒳.val.property
      (c ≫ a).hom.hom y,
    ?_, ?_⟩
  · have hcomp : p w₀ = _ :=
      pointsMap_comp (h𝒴 := (schemeFibredCategory B S hS U).property)
        (h𝒵 := 𝒳.val.property) (F := c.hom.hom) (G := a.hom.hom) (z := y)
    refine hcomp ▸ ?_
    have hmem : h w₀ ∈ T' := by
      rw [hOZ, hw₀]
      exact ⟨hιv, hvZ⟩
    simpa [hT'def] using hmem
  · refine isFiniteTypePoint_of_exists_isClosed_smoothChart.{u, w} B S hS 𝒳 _
      ⟨affChart U ⟨V₀, hV₀⟩, c ≫ a, y, ?_, ?_, rfl⟩
    · exact AlgebraicStacks.isSmooth_comp B S hS _ _
        (isSmooth_schemeStackMap.{u, w} B S hS (affChartHom U ⟨V₀, hV₀⟩)
          (smooth_affChartHom U ⟨V₀, hV₀⟩)) hasm
    · rw [hy]
      exact hvclosed

/-- For a closed subset `T` of the point space of an algebraic stack, the finite type points
lying in `T` are dense in `T`. -/
@[stacks 06G2 "the second clause: for a closed subset of the point space, its intersection with \
the set of finite type points is dense in it"]
theorem subset_closure_inter_finiteTypePoints_of_isClosed (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    letI := pointTopology B S hS 𝒳.val
    ∀ T : Set (points B S hS 𝒳.val.val 𝒳.val.property), IsClosed T →
      T ⊆ closure (T ∩ finiteTypePoints B S hS 𝒳) := by
  let := pointTopology B S hS 𝒳.val
  intro T hT x hx
  rw [mem_closure_iff]
  intro V hV hxV
  obtain ⟨t, ⟨htT, htV⟩, htft⟩ :=
    exists_mem_finiteTypePoints_of_isLocallyClosed.{u, w} B S hS 𝒳 (T ∩ V)
      (hT.isLocallyClosed.inter hV.isLocallyClosed) ⟨x, hx, hxV⟩
  exact ⟨t, htV, htT, htft⟩

/-- An open subset of the point space of an algebraic stack containing every finite type point
is the whole point space. -/
theorem eq_univ_of_isOpen_of_finiteTypePoints_subset (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    letI := pointTopology B S hS 𝒳.val
    ∀ W : Set (points B S hS 𝒳.val.val 𝒳.val.property), IsOpen W →
      finiteTypePoints B S hS 𝒳 ⊆ W → W = Set.univ := by
  let := pointTopology B S hS 𝒳.val
  intro W hW hft
  by_contra hne
  obtain ⟨x, hx⟩ := (Set.ne_univ_iff_exists_notMem W).1 hne
  obtain ⟨t, htW, htft⟩ :=
    exists_mem_finiteTypePoints_of_isLocallyClosed.{u, w} B S hS 𝒳 Wᶜ
      hW.isClosed_compl.isLocallyClosed ⟨x, hx⟩
  exact htW (hft htft)

end AlgebraicGeometry.Stack

end
