module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.IrreducibleComponents
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeNormalization
public import StacksFrontier.AlgebraicGeometry.Stacks.ComponentMultiplicity
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStackComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothPresentationQuasiCompact

/-!
# Normalization of an algebraic stack: the finiteness condition (Stacks 0GMI)

An algebraic stack over `S` can be normalized as soon as its smooth scheme charts have finitely
many irreducible components over every quasi-compact open. This file proves the four
characterisations of that condition given by Tag 0GMI: one smooth surjective scheme chart
suffices, every smooth scheme chart has the property, every algebraic space smooth over the stack
satisfies the equivalent conditions of Tag 0BB1, and the space of points of every quasi-compact
algebraic stack smooth over it has finitely many irreducible components.

## Main definitions

No new definitions are introduced: conditions (1) and (2) are the two scheme criteria
`AlgebraicGeometry.Stack.HasPropertyOnSomeSchemeAtlas` and
`AlgebraicGeometry.Stack.HasPropertyOnEverySchemeChart` of Tag 04YF at the scheme property of
Tag 0BAL, and condition (3) is stated through
`AlgebraicGeometry.Space.HasLocallyFiniteIrreducibleComponents`, which is condition (2) of
Tag 0BB1.

## Main results

* `AlgebraicGeometry.finiteIrreducibleComponents_isLocal_smooth`: the scheme property is local in
  the smooth topology.
* `AlgebraicGeometry.Stack.exists_smooth_atlas_iff_forall_smooth_chart`,
  `AlgebraicGeometry.Stack.forall_smooth_chart_iff_forall_space` and
  `AlgebraicGeometry.Stack.forall_smooth_chart_iff_finite_irreducibleComponents` are the three
  comparisons of Tag 0GMI, linking its four conditions in a chain through condition (2).

## Implementation notes

Conditions (1), (2) and (3) are instances of Tag 04YF, which compares the scheme criteria with
each other and with the algebraic-space criteria for any property of schemes local in the smooth
topology; Tag 0BAL supplies that locality, through
`AlgebraicGeometry.Scheme.smoothPrecoverage_le_fppfPrecoverage`. The algebraic-space criterion of
Tag 04YF asks the étale-local property of Tag 03E6 of the chart, and
`AlgebraicGeometry.Space.HasLocallyFiniteIrreducibleComponents` is its every-chart form, so the
two are identified by condition (2) of Tag 03E8.

The comparison with condition (4) is the source's argument. For the forward direction a
quasi-compact algebraic stack has a smooth surjective presentation by an affine scheme
(Tag 04YC), that presentation composed with the smooth 1-morphism to `𝒳` is smooth (Tag 075V), so
condition (2) makes the affine scheme have finitely many irreducible components, and Tag 0GM2
carries the finiteness along the surjective continuous map on points. For the converse a
quasi-compact open `V` of a smooth scheme chart `U` is itself an object of the site, its algebraic
stack is quasi-compact because the point space of the algebraic stack of a scheme *is* that scheme
(`AlgebraicGeometry.Stack.pointsHomeomorphScheme`), and it is smooth over `𝒳` because the open
immersion `V ⟶ U` is étale.

## References

* [Stacks Project, Tag 03E6](https://stacks.math.columbia.edu/tag/03E6)
* [Stacks Project, Tag 03E8](https://stacks.math.columbia.edu/tag/03E8)
* [Stacks Project, Tag 04YC](https://stacks.math.columbia.edu/tag/04YC)
* [Stacks Project, Tag 04YF](https://stacks.math.columbia.edu/tag/04YF)
* [Stacks Project, Tag 075V](https://stacks.math.columbia.edu/tag/075V)
* [Stacks Project, Tag 0BAL](https://stacks.math.columbia.edu/tag/0BAL)
* [Stacks Project, Tag 0BB1](https://stacks.math.columbia.edu/tag/0BB1)
* [Stacks Project, Tag 0GM2](https://stacks.math.columbia.edu/tag/0GM2)
* [Stacks Project, Tag 0GMI](https://stacks.math.columbia.edu/tag/0GMI)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

universe u w

/-- Finiteness of the irreducible components of the quasi-compact opens of a scheme is local in
the smooth topology: it is local in the fppf topology by Tag 0BAL, and every smooth covering
family is an fppf covering family. -/
@[sga "7 VIII 5.2" "partial"]
instance finiteIrreducibleComponents_isLocal_smooth :
    ObjectProperty.IsLocal
      (fun X : Scheme.{u} =>
        ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite)
      (Scheme.precoverage (@Smooth : MorphismProperty Scheme.{u})) :=
  ObjectProperty.IsLocal.of_le Scheme.smoothPrecoverage_le_fppfPrecoverage

namespace Stack

/-- Finiteness of the irreducible components transfers along a homeomorphism `X ≃ₜ Y`. -/
private theorem finite_irreducibleComponents_of_homeomorph {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) (h : (irreducibleComponents X).Finite) :
    (irreducibleComponents Y).Finite :=
  (ncard_irreducibleComponents_le_of_surjective e e.continuous e.surjective h).1

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The étale-local property of Tag 03E6 at finiteness of irreducible components over
quasi-compact opens is the every-chart condition
`AlgebraicGeometry.Space.HasLocallyFiniteIrreducibleComponents`, which is condition (2) of
Tag 0BB1. -/
private theorem hasEtaleLocalProperty_iff_hasLocallyFiniteIrreducibleComponents
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F) :
    Space.HasEtaleLocalProperty B S hS F
        (fun X : Scheme.{u} =>
          ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite) ↔
      Space.HasLocallyFiniteIrreducibleComponents B S hS F := by
  rw [Space.exists_atlas_iff_forall_etale B S hS F _ hF]
  exact forall_congr' fun U => forall_congr' fun g =>
    imp_congr (Space.isEtale_iff_presheaf_of_yoneda B S hS g).symm Iff.rfl

/-- **Stacks 0GMI, conditions (1) and (2).** One smooth surjective scheme chart whose
quasi-compact opens have finitely many irreducible components suffices: then every smooth scheme
chart of the algebraic stack has that property. -/
@[stacks 0GMI "conditions (1) and (2)"]
theorem exists_smooth_atlas_iff_forall_smooth_chart (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    HasPropertyOnSomeSchemeAtlas B S hS
        (fun X : Scheme.{u} =>
          ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite) 𝒳 ↔
      HasPropertyOnEverySchemeChart B S hS
        (fun X : Scheme.{u} =>
          ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite) 𝒳 :=
  exists_scheme_atlas_iff_forall_scheme B S hS _ 𝒳

/-- **Stacks 0GMI, conditions (2) and (3).** Every smooth scheme chart of the algebraic stack has
finitely many irreducible components over each of its quasi-compact opens exactly when every
algebraic space smooth over it satisfies the equivalent conditions of Tag 0BB1. -/
@[stacks 0GMI "conditions (2) and (3)"]
theorem forall_smooth_chart_iff_forall_space (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    HasPropertyOnEverySchemeChart B S hS
        (fun X : Scheme.{u} =>
          ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite) 𝒳 ↔
      ∀ (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
        (f : algebraicSpaceStack.{u, w} B S hS F hF ⟶ 𝒳),
        AlgebraicStacks.IsSmooth B S hS f →
          Space.HasLocallyFiniteIrreducibleComponents B S hS F := by
  rw [← exists_scheme_atlas_iff_forall_scheme B S hS _ 𝒳,
    exists_scheme_atlas_iff_exists_space_atlas B S hS _ 𝒳,
    exists_space_atlas_iff_forall_space B S hS _ 𝒳]
  exact forall_congr' fun F => forall_congr' fun hF => forall_congr' fun f =>
    imp_congr Iff.rfl
      (hasEtaleLocalProperty_iff_hasLocallyFiniteIrreducibleComponents B S hS hF)

/-- **Stacks 0GMI, conditions (2) and (4).** Every smooth scheme chart of the algebraic stack has
finitely many irreducible components over each of its quasi-compact opens exactly when the space
of points of Tag 04XL of every quasi-compact algebraic stack smooth over it has finitely many
irreducible components. -/
@[stacks 0GMI "conditions (2) and (4)"]
theorem forall_smooth_chart_iff_finite_irreducibleComponents
    (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    HasPropertyOnEverySchemeChart B S hS
        (fun X : Scheme.{u} =>
          ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite) 𝒳 ↔
      ∀ (𝒴 : AlgebraicStacks.{u, w} B S hS) (f : 𝒴 ⟶ 𝒳),
        IsQuasiCompactStack.{u, w} B S hS 𝒴.val 𝒴.property →
          AlgebraicStacks.IsSmooth B S hS f →
            (@irreducibleComponents (AlgebraicStacks.points B S hS 𝒴)
              (pointTopology B S hS 𝒴.val)).Finite := by
  refine ⟨fun h 𝒴 f hqc hf => ?_, fun h U f hf V hV => ?_⟩
  · let _ := pointTopology B S hS 𝒴.val
    obtain ⟨U, hU, g, hgSurj, hgRel⟩ :=
      (isQuasiCompactStack_iff_hasAffineSmoothPresentation B S hS 𝒴).1 hqc
    let _ : IsAffine ((BigFppfOver.toScheme B S hS).obj U) := hU
    have hgSmooth : AlgebraicStacks.IsSmooth B S hS g :=
      hasPropertyOnSomeSmoothDiagram_of_hasRelativeProperty.{u, w, u} B S hS
        (fun _ _ k => Space.IsSmooth B S hS k) 𝒴.property _ hgRel.1 hgRel.2
    have hP := h U (g ≫ f) (AlgebraicStacks.isSmooth_comp B S hS g f hgSmooth hf)
    have hfin : (irreducibleComponents ((BigFppfOver.toScheme B S hS).obj U)).Finite :=
      finite_irreducibleComponents_of_homeomorph
        (Homeomorph.Set.univ ((BigFppfOver.toScheme B S hS).obj U))
        (hP ⊤ (by simpa using (isCompact_univ :
          IsCompact (Set.univ : Set ((BigFppfOver.toScheme B S hS).obj U)))))
    exact (ncard_irreducibleComponents_le_of_surjective
      (AlgebraicStacks.chartPointMap B S hS U 𝒴 g)
      (AlgebraicStacks.continuous_chartPointMap B S hS U 𝒴 g)
      (AlgebraicStacks.surjective_chartPointMap B S hS U 𝒴 g hgSurj) hfin).1
  · have hsize : V.toScheme.size < B.cutoff :=
      (Scheme.size_coe_opens_le _ V).trans_lt U.left.property
    let i : B.obj hsize ⟶ U.left := B.inclusion.preimage V.ι
    let W : BigFppfOver B S hS := Over.mk (i ≫ U.hom)
    let j : W ⟶ U := Over.homMk i
    let _ := pointTopology B S hS (schemeStack.{u, w} B S hS W).val
    have hj : (BigFppfOver.toScheme B S hS).map j = V.ι := B.inclusion.map_preimage _
    have hWcompact : CompactSpace ((BigFppfOver.toScheme B S hS).obj W) := by
      change CompactSpace V.toScheme
      exact isCompact_iff_compactSpace.mp (by simpa using hV)
    have hjEtale : (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map j) :=
      (Space.presheaf_yoneda_map_etale_iff B S hS j).2
        (by rw [hj]; exact AlgebraicGeometry.Etale.instOfIsOpenImmersion V.ι)
    obtain ⟨c, hcSmooth, -⟩ := exists_schemeStack_hom_of_etaleChart.{u, w} B S hS
      (isAlgebraicSpace_yoneda B S hS U) (yoneda.map j) hjEtale
    obtain ⟨e, heSmooth, -⟩ := exists_smooth_surjective_algebraicSpaceStack_hom.{u, w} B S hS U
    have hWqc : IsQuasiCompactStack.{u, w} B S hS (schemeStack.{u, w} B S hS W).val
        (schemeStack.{u, w} B S hS W).property :=
      (pointsHomeomorphScheme B S hS W).symm.compactSpace
    have hfin := h (schemeStack.{u, w} B S hS W) (c ≫ e ≫ f) hWqc
      (AlgebraicStacks.isSmooth_comp B S hS c (e ≫ f) hcSmooth
        (AlgebraicStacks.isSmooth_comp B S hS e f heSmooth hf))
    change (irreducibleComponents V.toScheme).Finite
    exact finite_irreducibleComponents_of_homeomorph (pointsHomeomorphScheme B S hS W) hfin

end Stack

end AlgebraicGeometry

end
