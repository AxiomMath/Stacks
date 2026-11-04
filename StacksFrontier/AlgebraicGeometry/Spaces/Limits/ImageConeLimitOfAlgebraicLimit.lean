module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ChartLimitAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage

/-!
# Stacks 0CP9 with no bound on the index type

In Situation 0CP6, for a diagram as in Stacks 0CP8, the canonical cone from `X` to the inverse
system of the scheme-theoretic images `X_{i'}` of `X ⟶ B_{i'} ×_{B_i} W` is a limit cone:
`X = lim_{i' ≥ i} X_{i'}`, with no bound on the size of the index type.

## Main results

* `AlgebraicGeometry.Space.GoodDiagram.imageInter_le_range_induced_of_algebraicLimit`: the
  inclusion that remained of Stacks 0CP9.
* `AlgebraicGeometry.Space.GoodDiagram.isLimit_imageCone_of_algebraicLimit`: **Stacks 0CP9**.

## Implementation notes

The limit of the system of affine charts used in the proof is taken in the site by
`AlgebraicGeometry.Space.AffineChartSystem.exists_chartLimit_appTop_of_isAlgebraicSpace`, a
closed subscheme of the limit of the affine schemes, which is all the argument needs; it plays
the part of the limit bridge of
`AlgebraicGeometry.Space.GoodDiagram.imageInter_le_range_induced_of_chart`, which needs the
index type small for the site. The forms carrying the bound `#I < B.cutoff.ord.cof` are
`AlgebraicGeometry.Space.GoodDiagram.imageInter_le_range_induced` and
`AlgebraicGeometry.Space.GoodDiagram.isLimit_imageCone`.

## References

* [Stacks Project, Tag 0CP6](https://stacks.math.columbia.edu/tag/0CP6)
* [Stacks Project, Tag 0CP8](https://stacks.math.columbia.edu/tag/0CP8)
* [Stacks Project, Tag 0CP9](https://stacks.math.columbia.edu/tag/0CP9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

section Helpers

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The projections of the chosen limiting cone of a Noetherian limit system are affine
morphisms, the limit being an algebraic space (Stacks 07SF, part (1)); no bound on the index
type is needed. -/
lemma isAffineHom_limitCone_π_of_algebraicLimit {hZ : B.Contains (⊤_ Scheme.{u})}
    {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (D : NoetherianLimitSystem B S hS hZ I) (k : Iᵒᵖ) :
    IsAffineHom B S hS (D.limitCone.π.app k) :=
  isAffineHom_π_of_isAlgebraicSpace B S hS D.system (fun f => D.transition_affine f) D.isLimit
    D.limit_isAlgebraicSpace k (D.system_isAlgebraicSpace k.unop)

end Helpers

namespace GoodDiagram

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [Nonempty I]
    [IsDirectedOrder I] {D : NoetherianLimitSystem B S hS hZ I}
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ D.limitCone.pt}
    (G : GoodDiagram B S hS hZ D f) {U₀ : BigAffineFppf B S hS}
    (a : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ G.model)

/-! ### The chart of the limit space along a chart limit -/

/-- The chart `B ×_{B_i} U₀ ⟶ B ×_{B_i} W` of the base change of the model to the limit
space. -/
noncomputable def chartLimitChart (L : AffineChartSystem.ChartLimit (modelChartSystem G a)) :
    yoneda.obj L.cone.pt ⟶ pullback (D.limitCone.π.app (op G.index)) G.modelMap :=
  pullback.lift (D.chartLimitToLimit G.index (a ≫ G.modelMap) L) (L.toBase ≫ a)
    ((D.isPullback_chartLimitToLimit G.index (a ≫ G.modelMap) L).w.trans
      (Category.assoc _ _ _).symm)

/-- The chart of the limit space, followed by the projection to the limit space. -/
lemma chartLimitChart_fst (L : AffineChartSystem.ChartLimit (modelChartSystem G a)) :
    chartLimitChart G a L ≫ pullback.fst (D.limitCone.π.app (op G.index)) G.modelMap =
      D.chartLimitToLimit G.index (a ≫ G.modelMap) L :=
  pullback.lift_fst _ _ _

/-- The chart of the limit space, followed by the projection to the model. -/
lemma chartLimitChart_snd (L : AffineChartSystem.ChartLimit (modelChartSystem G a)) :
    chartLimitChart G a L ≫ pullback.snd (D.limitCone.π.app (op G.index)) G.modelMap =
      L.toBase ≫ a :=
  pullback.lift_snd _ _ _

/-- The chart of the base change of the model to the limit space is the base change of the
chosen chart of the model. -/
lemma isPullback_chartLimitChart (L : AffineChartSystem.ChartLimit (modelChartSystem G a)) :
    IsPullback (chartLimitChart G a L) L.toBase
      (pullback.snd (D.limitCone.π.app (op G.index)) G.modelMap) a := by
  refine IsPullback.of_right ?_ (chartLimitChart_snd G a L)
    (IsPullback.of_hasPullback (D.limitCone.π.app (op G.index)) G.modelMap)
  rw [chartLimitChart_fst]
  exact D.isPullback_chartLimitToLimit G.index (a ≫ G.modelMap) L

/-- The chart of the limit space projects to the chart of each later stage. -/
lemma chartLimitChart_comp_modelπ (L : AffineChartSystem.ChartLimit (modelChartSystem G a))
    (j : Over (op G.index)) :
    chartLimitChart G a L ≫ modelπ G j =
      yoneda.map (L.cone.π.app j) ≫ stageChart G a j := by
  have hct : D.chartLimitToLimit G.index (a ≫ G.modelMap) L = L.toLimit ≫ D.limitIso.hom := rfl
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, modelπ_fst, ← Category.assoc, chartLimitChart_fst, Category.assoc,
      stageChart_fst, hct, Category.assoc, D.limitIso_hom_comp_π, L.toLimit_comp_limitπ j]
  · rw [Category.assoc, modelπ_snd, chartLimitChart_snd, Category.assoc, stageChart_snd,
      ← Category.assoc, L.baseMap_comp j]

/-- The chart of the limit space is the limit of the charts of the stages: it is the base
change of the chart of any one stage along the projection of the base-changed models. -/
lemma isPullback_chartLimitChart_stage
    (L : AffineChartSystem.ChartLimit (modelChartSystem G a)) (j : Over (op G.index)) :
    IsPullback (chartLimitChart G a L) (yoneda.map (L.cone.π.app j)) (modelπ G j)
      (stageChart G a j) := by
  refine IsPullback.of_bot ?_ (chartLimitChart_comp_modelπ G a L j) (isPullback_stageChart G a j)
  rw [L.baseMap_comp j, modelπ_snd]
  exact isPullback_chartLimitChart G a L

/-- A base-change stable property of the chosen chart of the model passes to the chart of the
base change of the model to the limit space. -/
lemma presheaf_chartLimitChart {P : MorphismProperty Scheme.{u}}
    (L : AffineChartSystem.ChartLimit (modelChartSystem G a))
    (ha : (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).presheaf a) :
    (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).presheaf
      (chartLimitChart G a L) := by
  have : (MorphismProperty.inverseImage P
      (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  exact MorphismProperty.of_isPullback (isPullback_chartLimitChart G a L).flip ha

/-- **The chart-local form of Stacks 082Z, part (3), for a good diagram.** On the chart
`B_{i'} ×_{B_i} U₀` of a later stage, the scheme-theoretic image `X_{i'}` cuts out exactly the
scheme-theoretic image of the chart `X ×_{B ×_{B_i} W} (B ×_{B_i} U₀)` of `X`, which is an
object of the site because `X ⟶ B ×_{B_i} W` is a closed immersion. -/
lemma schemeTheoreticImage_chartLimitChart_eq_preimage_stageImage
    (hX : IsAlgebraicSpace B S hS X)
    (hetale : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hqc : ∀ j : Over (op G.index), IsQuasiCompact B S hS (stageMap G j))
    (L : AffineChartSystem.ChartLimit (modelChartSystem G a)) (j : Over (op G.index)) :
    schemeTheoreticImageSubfunctor B S hS
        (yoneda.map (G.isClosedImmersion.rep.snd (chartLimitChart G a L) ≫
          L.cone.π.app j)) =
      (stageImage G j).preimage (stageChart G a j) := by
  have hpb : IsPullback (G.isClosedImmersion.rep.fst (chartLimitChart G a L))
      (yoneda.map (G.isClosedImmersion.rep.snd (chartLimitChart G a L) ≫ L.cone.π.app j))
      (stageMap G j) (stageChart G a j) := by
    have h := (G.isClosedImmersion.rep.isPullback (chartLimitChart G a L)).paste_vert
      (isPullback_chartLimitChart_stage G a L j)
    rwa [← Functor.map_comp, induced_comp_modelπ] at h
  have hrange : Subfunctor.range
      (yoneda.map (G.isClosedImmersion.rep.snd (chartLimitChart G a L) ≫ L.cone.π.app j)) =
      Subfunctor.range (pullback.snd (stageMap G j) (stageChart G a j)) := by
    rw [← hpb.isoPullback_hom_snd, Subfunctor.range_comp, Subfunctor.range_eq_top,
      Subfunctor.image_top]
  rw [schemeTheoreticImageSubfunctor_congr_range' B S hS _ _
      (isAlgebraicSpace_yoneda B S hS _) hrange,
    schemeTheoreticImageSubfunctor_pullback_snd_of_isEtale_of_isQuasiCompact' B S hS
      (stageMap G j) (stageChart G a j) hX (isAlgebraicSpace_stageTarget G j)
      (isAlgebraicSpace_yoneda B S hS _) (hqc j)
      (isEtale_of_presheaf_etale' B S hS _ (presheaf_stageChart G a j hetale))]

/-! ### The remaining inclusion of Stacks 0CP9, on one chart -/

/-- The base change of the model to the limit space is an algebraic space. -/
private lemma isAlgebraicSpace_pullback_limitCone_modelMap :
    IsAlgebraicSpace B S hS (pullback (D.limitCone.π.app (op G.index)) G.modelMap) :=
  isAlgebraicSpace_pullback B S hS _ _ D.limit_isAlgebraicSpace G.model_isAlgebraicSpace
    (D.system_isAlgebraicSpace G.index)

/-- **The inclusion `imageInter G ≤ Subfunctor.range G.induced` of Stacks 0CP9, proved from a
single affine étale surjective chart of the model.**

A point of `B ×_{B_i} W` lying in every `X_{i'}` is tested after the surjective étale base
change by the chart `B ×_{B_i} U₀`, where membership in the closed subspace `X` is the
inclusion of the ideal sheaf of `X ×_{B ×_{B_i} W} (B ×_{B_i} U₀)` into the kernel of the
point. The chart is affine and is the limit of the affine charts `B_{i'} ×_{B_i} U₀`, so every
regular function on it is pulled back from one of those; there the ideal of `X` is, by Stacks
082Z, the ideal of functions vanishing on the chart of `X`, which the point kills because it
lies in `X_{i'}`. -/
theorem imageInter_le_range_induced_of_chartLimit
    (hX : IsAlgebraicSpace B S hS X)
    (hsurj : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hetale : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hqc : ∀ j : Over (op G.index), IsQuasiCompact B S hS (stageMap G j))
    (L : AffineChartSystem.ChartLimit (modelChartSystem G a))
    (hLaff : IsAffine ((BigFppfOver.toScheme B S hS).obj L.cone.pt))
    (hLΓ : ∀ s : Γ((BigFppfOver.toScheme B S hS).obj L.cone.pt, ⊤),
      ∃ (j : Over (op G.index)) (y : Γ((modelChartSystem G a).schemeDiagram.obj j, ⊤)),
        ((BigFppfOver.toScheme B S hS).map (L.cone.π.app j)).appTop y = s) :
    imageInter G ≤ Subfunctor.range G.induced := by
  classical
  have hMalg := isAlgebraicSpace_pullback_limitCone_modelMap G
  have hmono : Mono G.induced := mono_of_isClosedImmersion B S hS _ G.isClosedImmersion
  have hRalg : IsAlgebraicSpace B S hS (Subfunctor.range G.induced).toFunctor :=
    isAlgebraicSpace_of_iso B S hS (asIso (Subfunctor.toRange G.induced)) hX
  have hclE : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (chartLimitChart G a L) :=
    presheaf_chartLimitChart G a L hetale
  intro T x hx
  set t : yoneda.obj T.unop ⟶ pullback (D.limitCone.π.app (op G.index)) G.modelMap :=
    yonedaEquiv.symm x with ht
  have hw : yoneda.map (hclE.rep.fst' t) ≫ chartLimitChart G a L =
      yoneda.map (hclE.rep.snd t) ≫ t := by
    rw [hclE.rep.map_fst' t]
    exact (hclE.rep.isPullback t).w
  have hval : (pullback (D.limitCone.π.app (op G.index)) G.modelMap).map
      (hclE.rep.snd t).op x =
      (chartLimitChart G a L).app (op (hclE.rep.pullback t)) (hclE.rep.fst' t) := by
    rw [← yonedaEquiv_yoneda_map_comp B S hS (chartLimitChart G a L) (hclE.rep.fst' t), hw,
      ← yonedaEquiv_naturality, ht, Equiv.apply_symm_apply]
  refine mem_obj_of_surjective_etale B S hS hMalg.isSheaf (Subfunctor.range G.induced)
    hRalg.isSheaf (hclE.rep.snd t) ((presheaf_chartLimitChart G a L hsurj).property_snd t)
    (hclE.property_snd t) x ?_
  rw [hval]
  have hker : ((BigFppfOver.toScheme B S hS).map
      (G.isClosedImmersion.rep.snd (chartLimitChart G a L))).ker ≤
      ((BigFppfOver.toScheme B S hS).map (hclE.rep.fst' t)).ker := by
    refine ker_le_of_stagewise_ker_le'
      (fun j => (modelChartSystem G a).schemeDiagram.obj j)
      (fun j => (modelChartSystem G a).isAffine_obj j)
      (fun j => (BigFppfOver.toScheme B S hS).map (L.cone.π.app j)) _ _
      hLΓ ?_
    intro j
    rw [← Functor.map_comp, ← Functor.map_comp]
    refine ker_le_of_mem_schemeTheoreticImageSubfunctor B S hS _ _ ?_
    rw [schemeTheoreticImage_chartLimitChart_eq_preimage_stageImage G a hX hetale hqc L j]
    have h1 : (pullback (D.system.map j.hom) G.modelMap).map (hclE.rep.snd t).op
        ((modelπ G j).app T x) ∈ (stageImage G j).obj (op (hclE.rep.pullback t)) :=
      (stageImage G j).map (hclE.rep.snd t).op (imageInter_le G j T hx)
    rw [← (modelπ G j).naturality_apply, hval] at h1
    have h2 : (stageChart G a j).app (op (hclE.rep.pullback t))
        (hclE.rep.fst' t ≫ L.cone.π.app j) =
        (modelπ G j).app (op (hclE.rep.pullback t))
          ((chartLimitChart G a L).app (op (hclE.rep.pullback t)) (hclE.rep.fst' t)) :=
      (congrArg
        (fun k : yoneda.obj L.cone.pt ⟶ pullback (D.system.map j.hom) G.modelMap =>
          k.app (op (hclE.rep.pullback t)) (hclE.rep.fst' t))
        (chartLimitChart_comp_modelπ G a L j)).symm
    show (stageChart G a j).app (op (hclE.rep.pullback t))
        (hclE.rep.fst' t ≫ L.cone.π.app j) ∈ (stageImage G j).obj (op (hclE.rep.pullback t))
    rwa [h2]
  obtain ⟨ψ, hψ⟩ := exists_comp_eq_of_ker_le B S hS
    (G.isClosedImmersion.rep.snd (chartLimitChart G a L)) (hclE.rep.fst' t)
    (G.isClosedImmersion.property (chartLimitChart G a L) _ _
      (G.isClosedImmersion.rep.isPullback (chartLimitChart G a L))) hker
  refine ⟨yonedaEquiv (yoneda.map ψ ≫
    G.isClosedImmersion.rep.fst (chartLimitChart G a L)), ?_⟩
  rw [← yonedaEquiv_comp, Category.assoc,
    (G.isClosedImmersion.rep.isPullback (chartLimitChart G a L)).w, ← Category.assoc,
    ← Functor.map_comp, hψ]
  exact yonedaEquiv_yoneda_map_comp B S hS _ _

/-! ### Stacks 0CP9 -/

/-- **The stage maps of a good diagram are quasi-compact.** The morphism `X ⟶ B ×_{B_i} W` is
a closed immersion, and `B ×_{B_i} W ⟶ B_{i'} ×_{B_i} W` is a base change of the affine
projection `B ⟶ B_{i'}`. -/
lemma isQuasiCompact_stageMap_of_algebraicLimit (j : Over (op G.index)) :
    IsQuasiCompact B S hS (stageMap G j) := by
  have hMalg := isAlgebraicSpace_pullback_limitCone_modelMap G
  have hmaff : IsAffineHom B S hS (modelπ G j) :=
    isAffineHom_of_isPullback' B S hS (isPullback_modelπ G j)
      (isAffineHom_limitCone_π_of_algebraicLimit B S hS D j.left)
  have hmqc : IsQuasiCompact B S hS (modelπ G j) :=
    isQuasiCompact_of_isAffineHom' B S hS _ hMalg (isAlgebraicSpace_stageTarget G j) hmaff
  rw [← induced_comp_modelπ G j]
  exact isQuasiCompact_comp B S hS hMalg (isAlgebraicSpace_stageTarget G j) _ _
    (isQuasiCompact_of_isClosedImmersion' B S hS G.isClosedImmersion) hmqc

/-- **The inclusion that remained of Stacks 0CP9.** Every point of `B ×_{B_i} W` which lies in
the scheme-theoretic image `X_{i'}` at every stage `i' ≥ i` already lies in `X`.

The model `W` is quasi-compact over the Noetherian stage `B_i`, hence quasi-compact, so it has
a single affine étale surjective chart `U₀ ⟶ W`; the statement is then
`AlgebraicGeometry.Space.GoodDiagram.imageInter_le_range_induced_of_chartLimit` for that chart. The
system of charts of the stages has a limit in the site because the limit `B` is an algebraic
space: it is a closed subscheme of the limit of the affine charts, so it is affine and every
regular function on it is pulled back from a chart. No bound on the index type is needed. -/
theorem imageInter_le_range_induced_of_algebraicLimit (hX : IsAlgebraicSpace B S hS X) :
    imageInter G ≤ Subfunctor.range G.induced := by
  obtain ⟨A, a, hAaff, hasurj, haetale⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS G.model
      G.model_isAlgebraicSpace).mp
      (isQuasiCompactSpace_source_of_isQuasiCompact B S hS
        (D.system_isAlgebraicSpace G.index) (D.noetherian G.index).1 G.isFiniteType.2)
  have hlim : IsAlgebraicSpace B S hS (limit D.system) :=
    isAlgebraicSpace_of_iso B S hS D.limitIso.symm D.limit_isAlgebraicSpace
  obtain ⟨L, hLaff, hLΓ⟩ :=
    (modelChartSystem G (U₀ := ⟨A, hAaff⟩) a).exists_chartLimit_appTop_of_isAlgebraicSpace
      B S hS hlim (D.system_isAlgebraicSpace G.index)
  have hae := etale_presheaf_of_isEtale' B S hS A a haetale
  exact imageInter_le_range_induced_of_chartLimit G (U₀ := ⟨A, hAaff⟩) a hX hasurj hae
    (isQuasiCompact_stageMap_of_algebraicLimit G) L hLaff hLΓ

/-- **Stacks 0CP9.** In Situation 0CP6, for a diagram as in Stacks 0CP8, the canonical cone
from `X` to the inverse system of the scheme-theoretic images `X_{i'}` of
`X ⟶ B_{i'} ×_{B_i} W` is a limit cone: `X = lim_{i' ≥ i} X_{i'}`.

By `AlgebraicGeometry.Space.GoodDiagram.nonempty_isLimit_imageCone_iff` this is the single
inclusion `AlgebraicGeometry.Space.GoodDiagram.imageInter_le_range_induced_of_algebraicLimit` of
subfunctors of `B ×_{B_i} W`. -/
noncomputable def isLimit_imageCone_of_algebraicLimit (hX : IsAlgebraicSpace B S hS X) :
    IsLimit (imageCone G) :=
  isLimit_imageCone_of_imageInter_le G (imageInter_le_range_induced_of_algebraicLimit G hX)

end GoodDiagram

end AlgebraicGeometry.Space

end
