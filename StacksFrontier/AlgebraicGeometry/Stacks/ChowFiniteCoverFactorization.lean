module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FppfApplication.FiniteDomination
public import StacksFrontier.AlgebraicGeometry.FiniteFactorization.ExtendFiniteSurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSplitQuasiFiniteReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.RelationSize
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemePointsAffineHom
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFppfDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartRespectsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IsomorphismLocusOnBase
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitenessComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianPointsAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionAtPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentingMapFunctorial
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismComp
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismEvery
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismMonotone
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismRepresented
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasBridges
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStackComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveProperties
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningFlatDeformation
public import StacksFrontier.AlgebraicGeometry.Spaces.Finite
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcOpenSubspaceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralSchemeCoverEtaleRefinement
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralUniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationInQcqsIntegral
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceQuasiCompactOperations
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransform
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitePresentationBaseChangeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductUniversalProperty
import all StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteSeparatedRepresentable

/-!
# Finite covers along which a flat surjection splits Zariski locally

Let `Y` be a quasi-compact and quasi-separated algebraic space, `V ⊆ Y` a quasi-compact open
and `f : 𝒳 ⟶ V` a surjective, flat 1-morphism of algebraic stacks which is locally of finite
presentation. [Stacks, Tag 0CQ6] produces a finite surjective morphism `g : Y' ⟶ Y` such that
`g⁻¹(V) ⟶ V` factors Zariski locally through `f`. This file carries out the scheme-theoretic
core of the source proof.

## Main results

* `AlgebraicGeometry.Space.exists_finite_surjective_openCover_factorization_of_flat_surjective`:
  the case of a scheme `Y₀` of the big fppf site with a quasi-compact open `V₀ ⟶ Y₀` and a flat
  surjection `U ⟶ V₀` locally of finite presentation. It is the first paragraph of the source
  proof: [Stacks, Tag 0CP0] dominates the fppf covering `{U ⟶ V₀}` by a finite surjection
  `V' ⟶ V₀` which factors through `U` on the members of an open covering of `V'`, and
  [Stacks, Tag 0CNY] extends `V' ⟶ V₀` to a finite surjection `Y' ⟶ Y₀`. The size bound of the
  big fppf site keeps `Y'` and the members of the covering inside the site.

## References

* [Stacks Project, Tag 0CQ6](https://stacks.math.columbia.edu/tag/0CQ6)
* [Stacks Project, Tag 0CP0](https://stacks.math.columbia.edu/tag/0CP0)
* [Stacks Project, Tag 0CNY](https://stacks.math.columbia.edu/tag/0CNY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The scheme-theoretic core of [Stacks, Tag 0CQ6].** Let `Y₀` be a quasi-compact and
quasi-separated scheme of the big fppf site of `S`, let `k : V₀ ⟶ Y₀` be an open immersion with
quasi-compact source and let `h : U ⟶ V₀` be flat, surjective and locally of finite
presentation. Then there are a finite surjective `g : Y' ⟶ Y₀` and open immersions
`ι j : W j ⟶ Y'` whose images cover `g⁻¹(k(V₀))`, each factoring through `h` over `V₀`. -/
theorem exists_finite_surjective_openCover_factorization_of_flat_surjective
    {Y₀ V₀ U : BigFppfOver B S hS}
    (hY₀c : CompactSpace ((BigFppfOver.toScheme B S hS).obj Y₀))
    (hY₀s : QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj Y₀))
    (k : V₀ ⟶ Y₀)
    (hk : _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map k))
    (hV₀c : CompactSpace ((BigFppfOver.toScheme B S hS).obj V₀))
    (h : U ⟶ V₀) (hfl : Flat ((BigFppfOver.toScheme B S hS).map h))
    (hlfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map h))
    (hsurj : Surjective ((BigFppfOver.toScheme B S hS).map h)) :
    ∃ (Y' : BigFppfOver B S hS) (g : Y' ⟶ Y₀),
      _root_.AlgebraicGeometry.IsFinite ((BigFppfOver.toScheme B S hS).map g) ∧
      Surjective ((BigFppfOver.toScheme B S hS).map g) ∧
      ∃ (J : Type u) (W : J → BigFppfOver B S hS) (ι : ∀ j, W j ⟶ Y') (t : ∀ j, W j ⟶ U),
        (∀ j, _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (ι j))) ∧
        (∀ j, ι j ≫ g = t j ≫ h ≫ k) ∧
        ∀ y : (BigFppfOver.toScheme B S hS).obj Y',
          (BigFppfOver.toScheme B S hS).map g y ∈
              Set.range ((BigFppfOver.toScheme B S hS).map k) →
            ∃ j, y ∈ Set.range ((BigFppfOver.toScheme B S hS).map (ι j)) := by
  classical
  set F := BigFppfOver.toScheme B S hS
  have w : ∀ {T T' : BigFppfOver B S hS} (a : T ⟶ T'),
      F.map a ≫ B.inclusion.map T'.hom = B.inclusion.map T.hom := fun a =>
    (B.inclusion.map_comp _ _).symm.trans (congrArg _ (Over.w a))
  have := hY₀c
  have := hY₀s
  have := hk
  have := hV₀c
  have := hfl
  have := hlfp
  have := hsurj
  have : QuasiSeparatedSpace (F.obj V₀) := quasiSeparatedSpace_of_quasiSeparated (F.map k)
  -- the fppf covering `{U ⟶ V₀}` and [Stacks, Tag 0CP0]
  have hcov : Presieve.ofArrows (fun _ : PUnit.{u + 1} => F.obj U) (fun _ => F.map h) ∈
      Scheme.fppfPrecoverage (F.obj V₀) := by
    rw [Scheme.fppfPrecoverage, Scheme.ofArrows_mem_precoverage_iff]
    exact ⟨fun x => ⟨PUnit.unit, hsurj.surj x⟩, fun _ => ⟨hfl, hlfp⟩⟩
  obtain ⟨S', g', hg'fin, hg'surj, -, J, Uc, hUc, hfac⟩ :=
    exists_finite_surjective_openCover_factorization_of_mem_fppfPrecoverage _ _ hcov
  choose _ t ht using hfac
  -- the open `U₀ = k(V₀)` and [Stacks, Tag 0CNY]
  set U₀ := (F.map k).opensRange with hU₀def
  have hU₀ : IsCompact (U₀ : Set (F.obj Y₀)) := by
    rw [hU₀def, Scheme.Hom.coe_opensRange]
    exact isCompact_range (F.map k).continuous
  let e₀ := (F.map k).isoOpensRange
  have := hg'fin
  have := hg'surj
  let f₀ : S' ⟶ U₀.toScheme := g' ≫ e₀.hom
  obtain ⟨Ybar, gbar, hgfin, hgsurj, e, he⟩ :=
    Stacks.FiniteFactorization.exists_finite_surjective_extension U₀ hU₀ f₀
  have := hgfin
  have := hgsurj
  have hYbar : B.Contains Ybar :=
    contains_of_locallyOfFiniteType_of_quasiCompact B S hS (Y₀ := Y₀) gbar
  let Y' : BigFppfOver B S hS := BigFppfOver.mk B S hS hYbar (gbar ≫ B.inclusion.map Y₀.hom)
  let g : Y' ⟶ Y₀ := BigFppfOver.homOfCompEq B S hS (T := Y') gbar rfl
  have hFg : F.map g = gbar := BigFppfOver.toScheme_map_homOfCompEq B S hS _ _
  -- the members of the covering, inside `Ybar`
  let ιs : ∀ c, (Uc c).toScheme ⟶ Ybar := fun c => (Uc c).ι ≫ e.inv ≫ pullback.fst gbar U₀.ι
  have hW : ∀ c, B.Contains (Uc c).toScheme := fun c =>
    BigFppfSite.contains_of_mono B (ιs c) hYbar
  let W : J → BigFppfOver B S hS := fun c =>
    BigFppfOver.mk B S hS (hW c) (ιs c ≫ gbar ≫ B.inclusion.map Y₀.hom)
  let ι : ∀ c, W c ⟶ Y' := fun c => BigFppfOver.homOfCompEq B S hS (T := W c) (W := Y') (ιs c) rfl
  have hFι : ∀ c, F.map (ι c) = ιs c := fun c => BigFppfOver.toScheme_map_homOfCompEq B S hS _ _
  have hesnd : e.inv ≫ pullback.snd gbar U₀.ι = f₀ := by rw [← he, Iso.inv_hom_id_assoc]
  have key : ∀ c, ιs c ≫ gbar = t c ≫ F.map h ≫ F.map k := fun c => by
    calc ιs c ≫ gbar = (Uc c).ι ≫ e.inv ≫ pullback.snd gbar U₀.ι ≫ U₀.ι := by
          simp only [ιs, Category.assoc, pullback.condition]
      _ = (Uc c).ι ≫ g' ≫ F.map k := by
          rw [reassoc_of% hesnd]
          simp only [f₀, e₀, Category.assoc]
          exact congrArg (fun m => (Uc c).ι ≫ g' ≫ m) (Scheme.Hom.isoOpensRange_hom_ι (F.map k))
      _ = t c ≫ F.map h ≫ F.map k := by rw [reassoc_of% (ht c)]
  let t' : ∀ c, W c ⟶ U := fun c => BigFppfOver.homOfCompEq B S hS (T := W c) (W := U) (t c) (by
    show t c ≫ B.inclusion.map U.hom = ιs c ≫ gbar ≫ B.inclusion.map Y₀.hom
    rw [← w h, ← w k, reassoc_of% (key c)])
  have hFt : ∀ c, F.map (t' c) = t c := fun c => BigFppfOver.toScheme_map_homOfCompEq B S hS _ _
  refine ⟨Y', g, hFg ▸ hgfin, hFg ▸ hgsurj, J, W, ι, t', fun c => ?_, fun c => ?_, fun y hy => ?_⟩
  · rw [hFι c]
    show _root_.AlgebraicGeometry.IsOpenImmersion ((Uc c).ι ≫ e.inv ≫ pullback.fst gbar U₀.ι)
    infer_instance
  · apply F.map_injective
    rw [F.map_comp, F.map_comp, F.map_comp, hFι, hFg, hFt]
    exact key c
  · rw [hFg] at hy
    obtain ⟨p, rfl⟩ : y ∈ Set.range (pullback.fst gbar U₀.ι) := by
      rw [Scheme.Pullback.range_fst, Scheme.Opens.range_ι]
      show gbar y ∈ (U₀ : Set (F.obj Y₀))
      rwa [hU₀def, Scheme.Hom.coe_opensRange]
    have hs : e.hom p ∈ (⨆ c, Uc c) := by rw [hUc]; trivial
    obtain ⟨c, hc⟩ := TopologicalSpace.Opens.mem_iSup.mp hs
    refine ⟨c, ⟨⟨e.hom p, hc⟩, ?_⟩⟩
    rw [hFι c]
    show (pullback.fst gbar U₀.ι) (e.inv (e.hom p)) = _
    rw [show e.inv (e.hom p) = p from Scheme.inv_hom_apply e.symm p]

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A 1-morphism between the algebraic stacks of two algebraic spaces is 2-isomorphic to the
1-morphism of the morphism of representing presheaves it induces** (Stacks 04SW), stated for a
named morphism `g` equal to that induced morphism. -/
theorem nonempty_iso_algebraicSpaceStackMap_of_representingMap_eq
    {T G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hT : IsAlgebraicSpace B S hS T) (hG : IsAlgebraicSpace B S hS G)
    (a : algebraicSpaceStack.{u, w} B S hS T hT ⟶ algebraicSpaceStack.{u, w} B S hS G hG)
    (g : T ⟶ G)
    (h : representingMap B S hS (fibredCategory B S hS T) (fibredCategory B S hS G) T G
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _) a.hom = g) :
    Nonempty (a ≅ algebraicSpaceStackMap.{u, w} B S hS hT hG g) := by
  obtain ⟨e⟩ := nonempty_twoIso_associatedMap_representingMap B S hS T G a.hom
  subst h
  exact ⟨(Bicategory.InducedBicategory.isoMk e).symm⟩

/-- **An open subspace of the algebraic space of a scheme of the site is the algebraic space of an
open subscheme.** The inclusion of an open subspace is representable by open immersions, and its
base change along the identity is represented by an open immersion `k : V₀ ⟶ Y₀` of the site. -/
theorem exists_iso_yoneda_of_isOpenSubspace {Y₀ : BigFppfOver B S hS}
    (V : Subfunctor (yoneda.obj Y₀)) (hV : Space.IsOpenSubspace B S hS V) :
    ∃ (V₀ : BigFppfOver B S hS) (k : V₀ ⟶ Y₀) (i : yoneda.obj V₀ ≅ V.toFunctor),
      _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map k) ∧
        i.hom ≫ V.ι = yoneda.map k := by
  obtain ⟨V₀, k, i₀, hpb⟩ := hV.2.1 (𝟙 (yoneda.obj Y₀))
  have : IsIso i₀ := hpb.isIso_fst_of_isIso
  refine ⟨V₀, k, asIso i₀, hV.2.2 _ i₀ k hpb, ?_⟩
  show i₀ ≫ V.ι = _
  simpa only [Category.comp_id, Category.id_comp] using hpb.w

/-- **A flat surjection of algebraic stacks onto an algebraic space, locally of finite
presentation, is reached from a scheme by a flat surjection locally of finite presentation.**
For `f : 𝒳 ⟶ G` there are a scheme `U` of the site, a 1-morphism `c : h_U ⟶ 𝒳` (a smooth
surjective chart) and a flat surjective morphism `φ : h_U ⟶ G` of algebraic spaces, locally of
finite presentation, such that every `t ≫ c` followed by `f` is 2-isomorphic to `t ≫ φ`. -/
theorem exists_flat_surjective_chart_of_isFlat
    {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hG : IsAlgebraicSpace B S hS G)
    {𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS G hG)
    (hfs : IsSurjective B S hS f) (hff : AlgebraicStacks.IsFlat B S hS f)
    (hfl : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS f) :
    ∃ (U : BigFppfOver B S hS)
      (c : algebraicSpaceStack.{u, w} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) ⟶ 𝒳)
      (φ : yoneda.obj U ⟶ G),
      Space.IsFlat B S hS φ ∧ Space.IsLocallyOfFinitePresentation B S hS φ ∧
        Space.IsSurjective B S hS φ ∧
        ∀ (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hT : IsAlgebraicSpace B S hS T)
          (t : T ⟶ yoneda.obj U),
          Nonempty ((algebraicSpaceStackMap.{u, w} B S hS hT (isAlgebraicSpace_yoneda B S hS U) t ≫
            c) ≫ f ≅ algebraicSpaceStackMap.{u, w} B S hS hT hG (t ≫ φ)) := by
  obtain ⟨U, a, hasm, hasu⟩ := exists_smooth_surjective_schemeStack.{u, w} B S hS 𝒳
  obtain ⟨e, hesm, hesu⟩ := exists_smooth_surjective_algebraicSpaceStack_hom.{u, w} B S hS U
  have hU : IsAlgebraicSpace B S hS (yoneda.obj U) := isAlgebraicSpace_yoneda B S hS U
  let c := e ≫ a
  have hcsm : AlgebraicStacks.IsSmooth B S hS c :=
    AlgebraicStacks.isSmooth_comp B S hS e a hesm hasm
  have hcsu : IsSurjective B S hS c := isSurjective_comp B S hS e a hesu hasu
  let cf := c ≫ f
  let φ : yoneda.obj U ⟶ G :=
    representingMap B S hS (fibredCategory B S hS (yoneda.obj U)) (fibredCategory B S hS G) _ _
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _) cf.hom
  refine ⟨U, c, φ, ?_, ?_, ?_, fun T hT t => ?_⟩
  · exact (hasPropertyOnSomeSmoothDiagram_iff_represented.{u, w} B S hS _
      (Space.isSmoothLocalOnSourceAndTarget_flat B S hS)
      (algebraicSpaceStack.{u, w} B S hS (yoneda.obj U) hU).property
      (algebraicSpaceStack.{u, w} B S hS G hG).property _ _ hU hG
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _) cf.hom).mp
      ((AlgebraicStacks.isFlat_iff_hasPropertyOnSomeSmoothDiagram B S hS cf).mp
        (AlgebraicStacks.isFlat_comp B S hS c f
          (AlgebraicStacks.isFlat_of_isSmooth B S hS c hcsm) hff))
  · exact (hasPropertyOnSomeSmoothDiagram_iff_represented.{u, w} B S hS _
      (Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS)
      (algebraicSpaceStack.{u, w} B S hS (yoneda.obj U) hU).property
      (algebraicSpaceStack.{u, w} B S hS G hG).property _ _ hU hG
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _) cf.hom).mp
      (hasPropertyOnSomeSmoothDiagram_of_hasPropertyOnEverySmoothDiagram.{u, w} B S hS _
        (algebraicSpaceStack.{u, w} B S hS (yoneda.obj U) hU).property
        (algebraicSpaceStack.{u, w} B S hS G hG).property cf.hom
        (AlgebraicStacks.isLocallyOfFinitePresentation_comp B S hS c f
          (AlgebraicStacks.isLocallyOfFinitePresentation_of_isSmooth B S hS c hcsm) hfl))
  · exact isSurjective_representingMap_of_isSurjective.{u, w} B S hS
      (𝒳 := algebraicSpaceStack.{u, w} B S hS (yoneda.obj U) hU)
      (𝒴 := algebraicSpaceStack.{u, w} B S hS G hG) (yoneda.obj U) G
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _) cf (isSurjective_comp B S hS c f hcsu hfs)
  · refine ⟨Bicategory.associator _ c f ≪≫ ?_⟩
    refine (nonempty_iso_algebraicSpaceStackMap_of_representingMap_eq.{u, w} B S hS hT hG _
      _ ?_).some
    have e1 := representingMap_comp B S hS (𝒜 := fibredCategory B S hS T)
      (ℬ := fibredCategory B S hS (yoneda.obj U)) (𝒞 := fibredCategory B S hS G) T (yoneda.obj U) G
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _) (associatedMap B S hS t).1 cf.hom
    rwa [representingMap_associatedMap B S hS T (yoneda.obj U) t] at e1

/-- If `φ` holds on every étale chart and `h_m = φ ≫ i⁻¹`, then `P` holds for the morphism of
schemes underlying `m`. -/
private theorem map_of_holdsOnEveryEtaleChart_of_yoneda_map_comp_eq
    {P : MorphismProperty Scheme.{u}} (hP : IsEtaleLocalOnSourceAndTarget P)
    {U V₀ : BigFppfOver B S hS} {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (i : yoneda.obj V₀ ≅ G)
    (φ : yoneda.obj U ⟶ G) (m : U ⟶ V₀) (hm : yoneda.map m = φ ≫ i.inv)
    (h : Space.HoldsOnEveryEtaleChart B S hS P φ) : P ((BigFppfOver.toScheme B S hS).map m) := by
  refine (Space.holdsOnEveryEtaleChart_yoneda_map_iff B S hS hP m).mp ?_
  rw [hm]
  have := Space.holdsOnEveryEtaleChart_respectsIso_presheaf B S hS P
  exact MorphismProperty.RespectsIso.postcomp
    (fun ⦃_ _ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u⦄ n => Space.HoldsOnEveryEtaleChart B S hS P n)
    i.inv φ h

/-- **A flat surjection of algebraic spaces from a scheme onto the algebraic space of a scheme,
locally of finite presentation, is a flat surjection of schemes locally of finite presentation.**
If `φ : h_U ⟶ G` is such and `i : h_{V₀} ≅ G`, then `φ` is `h_m ≫ i` for a morphism `m : U ⟶ V₀`
of the site whose underlying morphism of schemes is flat, surjective and locally of finite
presentation. -/
theorem exists_flat_surjective_scheme_hom_of_iso_yoneda {U V₀ : BigFppfOver B S hS}
    {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (i : yoneda.obj V₀ ≅ G) (φ : yoneda.obj U ⟶ G)
    (hfl : Space.IsFlat B S hS φ) (hlfp : Space.IsLocallyOfFinitePresentation B S hS φ)
    (hsu : Space.IsSurjective B S hS φ) :
    ∃ m : U ⟶ V₀, yoneda.map m ≫ i.hom = φ ∧
      Flat ((BigFppfOver.toScheme B S hS).map m) ∧
      LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map m) ∧
      Surjective ((BigFppfOver.toScheme B S hS).map m) := by
  obtain ⟨m, hm⟩ := (yoneda (C := BigFppfOver B S hS)).map_surjective (φ ≫ i.inv)
  refine ⟨m, by rw [hm]; simp, ?_, ?_, ?_⟩
  · exact map_of_holdsOnEveryEtaleChart_of_yoneda_map_comp_eq B S hS
      Flat.isEtaleLocalOnSourceAndTarget i φ m hm hfl
  · exact map_of_holdsOnEveryEtaleChart_of_yoneda_map_comp_eq B S hS
      LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget i φ m hm hlfp
  · refine (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS (@Surjective.{u}) m).mp ?_
    refine (Space.surjective_yonedaMap_iff_surjective_pointsMap B S hS m).mpr ?_
    rw [hm]
    exact Space.isSurjective_comp B S hS hsu (Space.isSurjective_of_isIso B S hS i.inv)

/-- **[Stacks, Tag 0CQ6] when the ambient space is a scheme.** Let `Y₀` be a quasi-compact and
quasi-separated scheme of the big fppf site of `S`, let `V` be a quasi-compact open subspace of
the algebraic space `h_{Y₀}` it represents, and let `f : 𝒳 ⟶ V` be a surjective and flat
1-morphism of algebraic stacks which is locally of finite presentation. Then there is a finite
surjective morphism `g : Y' ⟶ h_{Y₀}` of algebraic spaces such that `g⁻¹(V) ⟶ V` factors
Zariski locally through `f`: there are open immersions `ι j : W j ⟶ Y'` contained in `g⁻¹(V)`
(they factor through `V` over `g`, by `q j`) whose images cover `g⁻¹(V)`, and 1-morphisms
`x j : W j ⟶ 𝒳` with `x j ≫ f` 2-isomorphic to `q j`.

This is the first paragraph of the source proof:
`AlgebraicGeometry.Space.exists_finite_surjective_openCover_factorization_of_flat_surjective`
applied to the morphism of schemes underlying a smooth surjective chart of `𝒳` followed by `f`. -/
theorem exists_finite_surjective_zariskiLocal_factorization_of_yoneda
    {Y₀ : BigFppfOver B S hS}
    (hY₀c : CompactSpace ((BigFppfOver.toScheme B S hS).obj Y₀))
    (hY₀s : QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj Y₀))
    (V : Subfunctor (yoneda.obj Y₀)) (hV : Space.IsOpenSubspace B S hS V)
    (hVqc : Space.IsQuasiCompactSpace B S hS V.toFunctor)
    {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS V.toFunctor hV.1)
    (hfs : IsSurjective B S hS f) (hff : AlgebraicStacks.IsFlat B S hS f)
    (hfl : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS f) :
    ∃ (Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS Y')
      (g : Y' ⟶ yoneda.obj Y₀),
      Space.IsFinite B S hS g ∧ Space.IsSurjective B S hS g ∧
      ∃ (J : Type u) (W : J → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
        (hW : ∀ j, IsAlgebraicSpace B S hS (W j)) (ι : ∀ j, W j ⟶ Y')
        (q : ∀ j, W j ⟶ V.toFunctor)
        (x : ∀ j, algebraicSpaceStack.{u, w} B S hS (W j) (hW j) ⟶ 𝒳),
        (∀ j, Space.IsOpenImmersion B S hS (ι j)) ∧ (∀ j, ι j ≫ g = q j ≫ V.ι) ∧
        (∀ y : Space.points B S hS Y',
          Space.pointsMap B S hS Y' g y ∈ Set.range (Space.pointsMap B S hS V.toFunctor V.ι) →
            ∃ j, y ∈ Set.range (Space.pointsMap B S hS (W j) (ι j))) ∧
        ∀ j, Nonempty (x j ≫ f ≅ algebraicSpaceStackMap.{u, w} B S hS (hW j) hV.1 (q j)) := by
  obtain ⟨V₀, k, i, hk, hik⟩ := exists_iso_yoneda_of_isOpenSubspace B S hS V hV
  have hV₀c : CompactSpace ((BigFppfOver.toScheme B S hS).obj V₀) :=
    Space.compactSpace_of_isQuasiCompactSpace_yoneda_obj B S hS
      (Space.isQuasiCompactSpace_of_iso B S hS i.symm hVqc)
  obtain ⟨U, c, φ, hφfl, hφlfp, hφsu, hc⟩ :=
    exists_flat_surjective_chart_of_isFlat.{u, w} B S hS hV.1 f hfs hff hfl
  obtain ⟨m, hm, hmfl, hmlfp, hmsu⟩ :=
    exists_flat_surjective_scheme_hom_of_iso_yoneda B S hS i φ hφfl hφlfp hφsu
  obtain ⟨Y'₀, g₀, hg₀fin, hg₀su, J, W, ι, t, hι, hιt, hcov⟩ :=
    Space.exists_finite_surjective_openCover_factorization_of_flat_surjective B S hS hY₀c hY₀s
      k hk hV₀c m hmfl hmlfp hmsu
  have hW : ∀ j, IsAlgebraicSpace B S hS (yoneda.obj (W j)) := fun j =>
    isAlgebraicSpace_yoneda B S hS (W j)
  refine ⟨yoneda.obj Y'₀, isAlgebraicSpace_yoneda B S hS Y'₀, yoneda.map g₀,
    Space.isFinite_yoneda_map B S hS g₀ hg₀fin, Space.isSurjective_yoneda_map B S hS g₀ hg₀su,
    J, fun j => yoneda.obj (W j), hW, fun j => yoneda.map (ι j),
    fun j => yoneda.map (t j) ≫ φ,
    fun j => algebraicSpaceStackMap.{u, w} B S hS (hW j) (isAlgebraicSpace_yoneda B S hS U)
      (yoneda.map (t j)) ≫ c,
    fun j => ?_, fun j => ?_, fun y hy => ?_, fun j => hc _ (hW j) (yoneda.map (t j))⟩
  · exact (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
      (@_root_.AlgebraicGeometry.IsOpenImmersion.{u}) (ι j)).mpr (hι j)
  · rw [← Functor.map_comp, hιt j, Functor.map_comp, Functor.map_comp, ← hik, ← hm]
    simp only [Category.assoc]
  · obtain ⟨v, hv⟩ := hy
    have hpt : (BigFppfOver.toScheme B S hS).map g₀ (Space.pointsToScheme B S hS Y'₀ y) ∈
        Set.range ((BigFppfOver.toScheme B S hS).map k) := by
      refine ⟨Space.pointsToScheme B S hS V₀ (Space.pointsMap B S hS _ i.inv v), ?_⟩
      rw [← Space.pointsToScheme_pointsMap, ← Space.pointsToScheme_pointsMap, ←
        Space.pointsMap_comp_apply, ← hik, Iso.inv_hom_id_assoc, hv]
    obtain ⟨j, z, hz⟩ := hcov _ hpt
    obtain ⟨z', rfl⟩ := Space.surjective_pointsToScheme B S hS (W j) z
    refine ⟨j, z', Space.injective_pointsToScheme B S hS Y'₀ ?_⟩
    rw [Space.pointsToScheme_pointsMap, hz]

/-- **[Stacks, Tag 0CQ6], reduced to the existence of finite surjective scheme covers.** Let `Y`
be a quasi-compact and quasi-separated algebraic space over `S`, let `V ⊆ Y` be a quasi-compact
open subspace and let `f : 𝒳 ⟶ V` be a surjective and flat 1-morphism of algebraic stacks which
is locally of finite presentation. Then there is a finite surjective morphism `g : Y' ⟶ Y` of
algebraic spaces such that `g⁻¹(V) ⟶ V` factors Zariski locally through `f`: open immersions
`ι j : W j ⟶ Y'` contained in `g⁻¹(V)` (they factor through `V` over `g`, by `q j`) cover
`g⁻¹(V)`, and there are 1-morphisms `x j : W j ⟶ 𝒳` with `x j ≫ f` 2-isomorphic to `q j`.

**Unregistered: it waits on [Stacks, Proposition 09YC].** The hypothesis `h09YC` is the
finite-surjective part of 09YC (1) only, without the finite presentation of the cover: every
quasi-compact and quasi-separated algebraic space receives a finite surjective morphism from a
scheme of the site. 09YC (1) implies it. With `h09YC` discharged this statement is
[Stacks, Tag 0CQ6].

The proof is the source's second paragraph: base change along a finite surjective `h_{Y₁} ⟶ Y`
from a scheme reduces to
`AlgebraicGeometry.Stack.exists_finite_surjective_zariskiLocal_factorization_of_yoneda`. -/
theorem exists_finite_surjective_zariskiLocal_factorization_of_finiteSchemeCover
    (h09YC : ∀ (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u), IsAlgebraicSpace B S hS Z →
      Space.IsQuasiCompactSpace B S hS Z →
      Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Z →
        ∃ (Z' : BigFppfOver B S hS) (c : yoneda.obj Z' ⟶ Z),
          Space.IsSurjective B S hS c ∧ Space.IsFinite B S hS c)
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (hYqc : Space.IsQuasiCompactSpace B S hS Y)
    (hYqs : Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y)
    (V : Subfunctor Y) (hV : Space.IsOpenSubspace B S hS V)
    (hVqc : Space.IsQuasiCompactSpace B S hS V.toFunctor)
    {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS V.toFunctor hV.1)
    (hfs : IsSurjective B S hS f) (hff : AlgebraicStacks.IsFlat B S hS f)
    (hfl : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS f) :
    ∃ (Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS Y') (g : Y' ⟶ Y),
      Space.IsFinite B S hS g ∧ Space.IsSurjective B S hS g ∧
      ∃ (J : Type u) (W : J → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
        (hW : ∀ j, IsAlgebraicSpace B S hS (W j)) (ι : ∀ j, W j ⟶ Y')
        (q : ∀ j, W j ⟶ V.toFunctor)
        (x : ∀ j, algebraicSpaceStack.{u, w} B S hS (W j) (hW j) ⟶ 𝒳),
        (∀ j, Space.IsOpenImmersion B S hS (ι j)) ∧ (∀ j, ι j ≫ g = q j ≫ V.ι) ∧
        (∀ y : Space.points B S hS Y',
          Space.pointsMap B S hS Y' g y ∈ Set.range (Space.pointsMap B S hS V.toFunctor V.ι) →
            ∃ j, y ∈ Set.range (Space.pointsMap B S hS (W j) (ι j))) ∧
        ∀ j, Nonempty (x j ≫ f ≅ algebraicSpaceStackMap.{u, w} B S hS (hW j) hV.1 (q j)) := by
  -- a finite surjective scheme cover `π : h_{Y₁} ⟶ Y`
  obtain ⟨Y₁, π, hπs, hπf⟩ := h09YC Y hY hYqc hYqs
  have hY₁ : IsAlgebraicSpace B S hS (yoneda.obj Y₁) := isAlgebraicSpace_yoneda B S hS Y₁
  obtain ⟨hY₁c, hY₁s⟩ := Space.compactSpace_and_quasiSeparatedSpace_of_isIntegralHom B S hS
    B.contains_terminal Y₁ π hY hYqc hYqs (Space.IsFinite.isIntegralHom B S hS hπf)
  -- the open `V₁ = π⁻¹(V)` and the base change of `f` to it
  have hV₁ : Space.IsOpenSubspace B S hS (V.preimage π) :=
    Space.isOpenSubspace_preimage B S hS π V hY hY₁ hV
  have hV₁qc : Space.IsQuasiCompactSpace B S hS (V.preimage π).toFunctor :=
    Space.isQuasiCompactSpace_preimage_of_isQuasiCompact B S hS hY hY₁ π
      (Space.isQuasiCompact_of_isIntegralHom π hY₁ hY (Space.IsFinite.isIntegralHom B S hS hπf))
      hV hVqc
  let r : (V.preimage π).toFunctor ⟶ V.toFunctor := V.fromPreimage π
  let b := algebraicSpaceStackMap.{u, w} B S hS hV₁.1 hV.1 r
  let P := AlgebraicStacks.twoFibreProductSquare B S hS b f
  have hP : Bicategory.IsTwoFibreProduct P :=
    AlgebraicStacks.isTwoFibreProduct_twoFibreProductSquare B S hS b f
  obtain ⟨Y', hY', g₁, hg₁f, hg₁s, J, W, hW, ι, q, x, hι, hιq, hcov, hx⟩ :=
    exists_finite_surjective_zariskiLocal_factorization_of_yoneda.{u, w} B S hS hY₁c hY₁s
      (V.preimage π) hV₁ hV₁qc P.fst (isSurjective_fst_of_isTwoFibreProduct B S hS P hP hfs)
      (AlgebraicStacks.isFlat_baseChange B S hS f b P hP hff)
      (AlgebraicStacks.isLocallyOfFinitePresentation_baseChange B S hS f b P hP hfl)
  refine ⟨Y', hY', g₁ ≫ π, Space.isFinite_comp B S hS hg₁f hπf, Space.isSurjective_comp B S hS
    hg₁s hπs, J, W, hW, ι, fun j => q j ≫ r, fun j => x j ≫ P.snd, hι, fun j => ?_,
    fun y hy => ?_, fun j => ?_⟩
  · rw [← Category.assoc, hιq j, Category.assoc, Category.assoc, Subfunctor.fromPreimage_ι]
  · refine hcov y ?_
    rwa [Space.range_pointsMap_preimage_ι B S hS π V, Set.mem_preimage,
      ← Space.pointsMap_comp_apply]
  · obtain ⟨e⟩ := hx j
    have hcomp : algebraicSpaceStackMap.{u, w} B S hS (hW j) hV.1 (q j ≫ r) =
        algebraicSpaceStackMap.{u, w} B S hS (hW j) hV₁.1 (q j) ≫ b := by
      simp only [algebraicSpaceStackMap, b, associatedMap_comp]
      rfl
    exact ⟨Bicategory.associator _ _ _ ≪≫ Bicategory.whiskerLeftIso (x j) P.iso.symm ≪≫
      (Bicategory.associator _ _ _).symm ≪≫ Bicategory.whiskerRightIso e b ≪≫
      eqToIso hcomp.symm⟩

end AlgebraicGeometry.Stack

end
