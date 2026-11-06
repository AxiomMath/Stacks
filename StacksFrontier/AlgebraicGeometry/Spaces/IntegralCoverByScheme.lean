module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.IntegralRefinement
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.UniversallyBoundedBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.DenseSchematicLocusEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleOpenOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionPointEmbedding
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Etale
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedDiagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiMainTheoremGeneral

/-!
# A quasi-compact and quasi-separated algebraic space is integrally dominated by a scheme

Stacks 09YB, part (1): a quasi-compact and quasi-separated algebraic space `X` over a scheme
`S` receives a surjective integral morphism from a scheme. The source's proof is an induction
on a bound `d` for the degrees of the geometric fibres of a surjective étale morphism `U ⟶ X`
from a quasi-compact separated scheme. This module builds that induction step by step.

## Main results

* `AlgebraicGeometry.Space.NormalizationInData.denseRange_pointsMap_toNorm`: the image of `X`
  in the normalization of `Y` in `X` is dense, for a relatively representable, quasi-compact
  and separated morphism `X ⟶ Y`.
* `AlgebraicGeometry.Space.isOpenImmersion_graph_of_isEtale`: the graph of an open immersion
  `j : U ⟶ Y` over `Y ⟶ X` is an open immersion when `U ⟶ X` is étale; with Stacks 03KO it is
  then open and closed when `Y ⟶ X` is separated.
* `AlgebraicGeometry.Space.isRepresentable_of_forall_mem_isRepresentable_isOpenSubspace`: an
  algebraic space every point of which lies in an open subspace that is a scheme is a scheme.

## References

* [Stacks Project, Tag 09YB](https://stacks.math.columbia.edu/tag/09YB)
* [Stacks Project, Tag 0ABS](https://stacks.math.columbia.edu/tag/0ABS)
* [Stacks Project, Tag 0G2D](https://stacks.math.columbia.edu/tag/0G2D)
* [Stacks Project, Tag 07S8](https://stacks.math.columbia.edu/tag/07S8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.MoreMorphisms

open _root_.AlgebraicGeometry

/-- **The degree drop of Stacks 09Z0 on any presentation of the fibre product.**
`Stacks.MoreMorphisms.boundsFiberDegrees_openImmersionGraphCompl` for a cartesian square
`P = U ×_X T` given by an arbitrary `IsPullback`: the complement of the graph of `j` inside `P`
has fibre degrees over `T` bounded by `n` when those of `j ≫ ν` are bounded by `n + 1`. -/
public theorem boundsFiberDegrees_compl_range_lift_of_isPullback {U X T P : Scheme.{u}}
    (j : U ⟶ T) (ν : T ⟶ X) [IsOpenImmersion j] [IsIntegralHom ν] [Etale (j ≫ ν)]
    [IsSeparated (j ≫ ν)] [QuasiCompact (j ≫ ν)] [CompactSpace T] (n : ℕ)
    (hb : BoundsFiberDegrees (j ≫ ν) ((n + 1 : ℕ) : ℤ)) (hdense : DenseRange j.base)
    {pr₁ : P ⟶ U} {pr₂ : P ⟶ T} (sq : IsPullback pr₁ pr₂ (j ≫ ν) ν) (O : P.Opens)
    (hO : (O : Set P) = (Set.range (sq.lift (𝟙 U) j (by simp)).base)ᶜ) :
    BoundsFiberDegrees (O.ι ≫ pr₂) (n : ℤ) := by
  set G := openImmersionGraphCompl j ν
  set e := sq.isoPullback
  have hlift : sq.lift (𝟙 U) j (by simp) ≫ e.hom = openImmersionGraph j ν := by
    apply pullback.hom_ext <;> simp [e]
  have hOG : O = e.hom ⁻¹ᵁ G := by
    ext x
    rw [hO]
    show _ ↔ e.hom.base x ∈ (G : Set _)
    rw [coe_openImmersionGraphCompl]
    simp only [Set.mem_compl_iff, Set.mem_range, ← hlift, Scheme.Hom.comp_apply,
      (ConcreteCategory.bijective_of_isIso e.hom.base).1.eq_iff]
  subst hOG
  have hb' : BoundsFiberDegrees (G.ι ≫ pullback.snd (j ≫ ν) ν) (n : ℤ) :=
    boundsFiberDegrees_openImmersionGraphCompl j ν n hb hdense
  have hsq : IsPullback (e.hom ∣_ G) ((e.hom ⁻¹ᵁ G).ι ≫ pr₂)
      (G.ι ≫ pullback.snd (j ≫ ν) ν) (𝟙 T) := by
    refine IsPullback.of_horiz_isIso ⟨?_⟩
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
    simp [e]
  exact boundsFiberDegrees_of_isPullback hsq hb'

end Stacks.MoreMorphisms

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance (priority := high) hasPullback_presheaf_integralCoverByScheme
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

namespace NormalizationInData

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y} (N : NormalizationInData B S hS f)

/-- **The source is dense in the normalization.** For a relatively representable,
quasi-compact and separated morphism `f : X ⟶ Y` of algebraic spaces, the image of the points
of `X` in the points of the normalization of `Y` in `X` is dense.

Over a surjective étale scheme chart of `Y` the morphism `X ⟶ Y'` is the canonical morphism to
the relative normalization of the chart of `f`, which is dominant; the chart of `Y'` is open
and surjective on points, so density descends. -/
theorem denseRange_pointsMap_toNorm (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hrep : yoneda.relativelyRepresentable f)
    (hqc : IsQuasiCompact B S hS f) (hsep : IsSeparated B S hS f) :
    DenseRange (pointsMap B S hS X N.toNorm) := by
  obtain ⟨W, w, hwsurj, hwet⟩ := hY.exists_atlas
  have hsq : IsPullback (hrep.fst w) (yoneda.map (hrep.snd w)) f w := hrep.isPullback w
  have := NormalizationGluing.quasiCompact_hrep_snd_of_isQuasiCompact B S hS hrep hqc w
  have := NormalizationGluing.quasiSeparated_hrep_snd B S hS hrep hX hY hsep w
  obtain ⟨W', q, b, r, e, hbq, hrb, hre, -⟩ :=
    N.chart W (hrep.pullback w) w (hrep.snd w) (hrep.fst w) hwet hsq
  have hbcE := MorphismProperty.relative_isStableUnderBaseChange
    (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) (F := yoneda)
  have hbcS := MorphismProperty.relative_isStableUnderBaseChange
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) (F := yoneda)
  have hbS := hbcS.of_isPullback hbq.flip hwsurj
  have hbE := hbcE.of_isPullback hbq.flip hwet
  have hbpts : Function.Surjective (pointsMap B S hS (yoneda.obj W') b) :=
    (surjective_iff_surjective_pointsMap B S hS _ N.isAlgebraicSpace _ b).1 hbS
  have hbopen : IsOpenMap (pointsMap B S hS (yoneda.obj W') b) :=
    isOpenMap_pointsMap_of_isEtale B S hS b (isAlgebraicSpace_yoneda B S hS W')
      N.isAlgebraicSpace ((isEtale_iff_presheaf_of_yoneda B S hS b).2 hbE)
  have hrdense : DenseRange (pointsMap B S hS _ (yoneda.map r)) := by
    have hT : (BigFppfOver.toScheme B S hS).map r =
        ((BigFppfOver.toScheme B S hS).map (hrep.snd w)).toNormalization ≫ e.inv := by
      rw [← hre, Category.assoc, e.hom_inv_id, Category.comp_id]
    have hdom : DenseRange ((BigFppfOver.toScheme B S hS).map r) := by
      rw [hT]
      exact (IsDominant.denseRange (f := _ ≫ e.inv))
    rw [pointsMap_yoneda_eq_conj]
    exact (schemePointsHomeomorph B S hS W').symm.surjective.denseRange.comp
      (hdom.comp (schemePointsHomeomorph B S hS _).surjective.denseRange
        (map_continuous _)) (map_continuous _)
  rw [DenseRange, dense_iff_inter_open]
  intro O hO hOne
  obtain ⟨y, hy⟩ := hOne
  obtain ⟨y', rfl⟩ := hbpts y
  have hpre : IsOpen (pointsMap B S hS (yoneda.obj W') b ⁻¹' O) :=
    hO.preimage (continuous_pointsMap B S hS b)
  obtain ⟨_, hzO, ⟨x, rfl⟩⟩ := dense_iff_inter_open.1 hrdense _ hpre ⟨y', hy⟩
  refine ⟨_, hzO, pointsMap B S hS _ (hrep.fst w) x, ?_⟩
  rw [← Function.comp_apply (f := pointsMap B S hS X N.toNorm), ← pointsMap_comp,
    ← Function.comp_apply (f := pointsMap B S hS _ b), ← pointsMap_comp, hrb]

end NormalizationInData

/-- **The graph of an open immersion over an étale composite is an open immersion.** For an open
immersion `j : U ⟶ Y` and `ν : Y ⟶ X` with `j ≫ ν` étale, the graph `U ⟶ U ×_X Y` of `j` is the
relative diagonal of `j ≫ ν`, an open immersion because `j ≫ ν` is unramified, followed by the
base change `U ×_X U ⟶ U ×_X Y` of `j`. -/
theorem isOpenImmersion_graph_of_isEtale {U Y X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hU : IsAlgebraicSpace B S hS U) (hX : IsAlgebraicSpace B S hS X) (j : U ⟶ Y) (ν : Y ⟶ X)
    (hj : IsOpenImmersion B S hS j) (het : IsEtale B S hS (j ≫ ν)) :
    IsOpenImmersion B S hS (graph B S hS j ν) := by
  let m : pullback (j ≫ ν) (j ≫ ν) ⟶ pullback (j ≫ ν) ν :=
    pullback.map _ _ _ _ (𝟙 _) j (𝟙 _) (by simp) (by simp)
  have hm : IsPullback (pullback.snd (j ≫ ν) (j ≫ ν)) m j (pullback.snd (j ≫ ν) ν) := by
    refine (IsPullback.of_right (h₁₂ := pullback.fst (j ≫ ν) ν) (v₁₃ := j ≫ ν) (h₂₂ := ν)
      ?_ (by simp [m]) (IsPullback.of_hasPullback (j ≫ ν) ν)).flip
    rw [show m ≫ pullback.fst (j ≫ ν) ν = pullback.fst (j ≫ ν) (j ≫ ν) by simp [m]]
    exact IsPullback.of_hasPullback (j ≫ ν) (j ≫ ν)
  have hmoi : IsOpenImmersion B S hS m :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hm hj
  have hgraph : graph B S hS j ν = pullback.diagonal (j ≫ ν) ≫ m := by
    apply pullback.hom_ext <;> simp [graph_comp_fst, graph_comp_snd, m]
  rw [hgraph]
  exact isOpenImmersion_comp B S hS _ _
    (isOpenImmersion_diagonal_of_isUnramified B S hS hU hX _ (isUnramified_of_isEtale B S hS het))
    hmoi

/-- **An algebraic space covered by open subschemes is a scheme.** If every point of an
algebraic space `X` lies in an open subspace of `X` which is representable, then `X` is
representable: the schematic locus of Stacks 03JH then contains every point, so it is all of
`X`. -/
theorem isRepresentable_of_forall_mem_isRepresentable_isOpenSubspace
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (h : ∀ x : points B S hS X, ∃ G : Subfunctor X, IsOpenSubspace B S hS G ∧
      G.toFunctor.IsRepresentable ∧ x ∈ Set.range (pointsMap B S hS G.toFunctor G.ι)) :
    X.IsRepresentable := by
  obtain ⟨hLo, hLr⟩ :=
    isOpenSubspace_and_isRepresentable_schematicLocus_of_isAlgebraicSpace B S hS hX
  have hL : schematicLocus B S hS X = ⊤ := by
    refine eq_of_range_pointsMap_ι_eq B S hS hLo (isOpenSubspace_top hX) ?_
    rw [(pointsMap_surjective_of_isIso B S hS (⊤ : Subfunctor X).ι).range_eq]
    refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨G, hGo, hGr, hx⟩ := h x
    exact range_pointsMap_ι_le_schematicLocus B S hS G hGo hGr hx
  have : IsIso (schematicLocus B S hS X).ι := (Subfunctor.eq_top_iff_isIso _).1 hL
  exact isRepresentable_of_natIso _ (asIso (schematicLocus B S hS X).ι)

/-- **A section base changes to a pullback square.** If `s` is a section of `π : P ⟶ U` and
`P' = P ×_U U'`, the induced section `s'` of `P' ⟶ U'` exhibits `U'` as the fibre product of
`s` and `P' ⟶ P`. -/
theorem isPullback_section_of_isPullback {𝒞 : Type*} [Category 𝒞] {U P U' P' : 𝒞}
    {π : P ⟶ U} {s : U ⟶ P} (hs : s ≫ π = 𝟙 U) {f : U' ⟶ U} {π' : P' ⟶ U'} {f' : P' ⟶ P}
    (h : IsPullback π' f' f π) {s' : U' ⟶ P'} (hs' : s' ≫ π' = 𝟙 U')
    (hss' : s' ≫ f' = f ≫ s) : IsPullback s' f f' s :=
  IsPullback.of_right (by
      rw [hs, hs']
      exact IsPullback.of_horiz_isIso ⟨by simp⟩) hss' h

/-- **The graph of `j` on the represented fibre product.** For an open immersion
`j : h_U ⟶ Y` and a relatively representable separated `ν : Y ⟶ X` with `j ≫ ν` étale, the
morphism `U ⟶ U ×_X Y` of the site lifting `(𝟙, j)` is an open and closed immersion of
schemes. -/
theorem isOpenImmersion_isClosedImmersion_toScheme_map_lift
    {U : BigFppfOver B S hS} {Y X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (j : yoneda.obj U ⟶ Y) (ν : Y ⟶ X)
    (hν : yoneda.relativelyRepresentable ν) (hj : IsOpenImmersion B S hS j)
    (het : IsEtale B S hS (j ≫ ν)) (hsep : IsSeparated B S hS ν) :
    _root_.AlgebraicGeometry.IsOpenImmersion
        ((BigFppfOver.toScheme B S hS).map (hν.lift (g := j ≫ ν) j (𝟙 U) (by simp))) ∧
      _root_.AlgebraicGeometry.IsClosedImmersion
        ((BigFppfOver.toScheme B S hS).map (hν.lift (g := j ≫ ν) j (𝟙 U) (by simp))) := by
  set γ := hν.lift (g := j ≫ ν) j (𝟙 U) (by simp)
  have hsq := (hν.isPullback (j ≫ ν)).flip
  have hγ : yoneda.map γ ≫ hsq.isoPullback.hom = graph B S hS j ν := by
    apply pullback.hom_ext
    · rw [Category.assoc, hsq.isoPullback_hom_fst, graph_comp_fst, ← Functor.map_comp,
        Functor.relativelyRepresentable.lift_snd, CategoryTheory.Functor.map_id]
    · rw [Category.assoc, hsq.isoPullback_hom_snd, graph_comp_snd,
        Functor.relativelyRepresentable.lift_fst]
  have hγ' : yoneda.map γ = graph B S hS j ν ≫ hsq.isoPullback.inv := by
    rw [← hγ, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have h1 : IsOpenImmersion B S hS (yoneda.map γ) := by
    rw [hγ']
    exact isOpenImmersion_comp B S hS _ _
      (isOpenImmersion_graph_of_isEtale (isAlgebraicSpace_yoneda B S hS U) hX j ν hj het)
      (isOpenImmersion_of_isIso B S hS _)
  have h2 : IsClosedImmersion B S hS (yoneda.map γ) := by
    rw [hγ']
    exact isClosedImmersion_comp B S hS _ _
      (isClosedImmersion_graph_of_isSeparated B S hS j ν hsep)
      (isClosedImmersion_of_isIso B S hS _)
  have hid : IsPullback (𝟙 (yoneda.obj U)) (yoneda.map γ) (yoneda.map γ)
      (𝟙 (yoneda.obj (hν.pullback (j ≫ ν)))) := IsPullback.of_horiz_isIso ⟨by simp⟩
  exact ⟨h1.property _ _ _ hid, h2.2 _ _ _ hid⟩

attribute [local instance] CategoryTheory.Limits.comp_preservesLimitsOfShape in
/-- The functor to schemes preserves fibre products. -/
local instance preservesPullbacks_toScheme' :
    PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
  comp_preservesLimitsOfShape _ _

/-- **An open subscheme cut out by a preimage is a fibre product.** If `O₁ ⟶ X₁` is the open
subscheme of `X₁` given by the preimage of an open subscheme `O₂ ⟶ X₂` under `f : X₁ ⟶ X₂`, with
the universal property of `AlgebraicGeometry.exists_restrict_bigFppfOver`, the square is
cartesian in the site. -/
theorem isPullback_of_range_subset_of_isOpenImmersion {X₁ X₂ O₁ O₂ : BigFppfOver B S hS}
    (f : X₁ ⟶ X₂) (i₁ : O₁ ⟶ X₁) (i₂ : O₂ ⟶ X₂) (g : O₁ ⟶ O₂)
    (hi₁ : _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map i₁))
    (hi₂ : _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map i₂))
    (hfac : ∀ {T : BigFppfOver B S hS} (t : T ⟶ X₁),
      Set.range ((BigFppfOver.toScheme B S hS).map t) ⊆
        Set.range ((BigFppfOver.toScheme B S hS).map i₁) → ∃ h : T ⟶ O₁, h ≫ i₁ = t)
    (hrange : ((BigFppfOver.toScheme B S hS).map f).base ⁻¹'
        Set.range ((BigFppfOver.toScheme B S hS).map i₂) ⊆
      Set.range ((BigFppfOver.toScheme B S hS).map i₁))
    (hw : g ≫ i₂ = i₁ ≫ f) : IsPullback g i₁ i₂ f := by
  have : Mono i₁ := (BigFppfOver.toScheme B S hS).mono_of_mono_map inferInstance
  have : Mono i₂ := (BigFppfOver.toScheme B S hS).mono_of_mono_map inferInstance
  have hlift : ∀ s : PullbackCone i₂ f, ∃ h : s.pt ⟶ O₁, h ≫ i₁ = s.snd := fun s => by
    refine hfac s.snd ?_
    rintro _ ⟨x, rfl⟩
    refine hrange ⟨(BigFppfOver.toScheme B S hS |>.map s.fst).base x, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, s.condition, Functor.map_comp,
      Scheme.Hom.comp_apply]
  refine IsPullback.of_isLimit' ⟨hw⟩ (PullbackCone.IsLimit.mk _
    (fun s => (hlift s).choose) (fun s => ?_) (fun s => (hlift s).choose_spec)
    (fun s m _ hm => by rw [← cancel_mono i₁, hm, (hlift s).choose_spec]))
  rw [← cancel_mono i₂, Category.assoc, hw, ← Category.assoc, (hlift s).choose_spec,
    s.condition]

/-- **The complement of the graph, over an étale chart.** Let `j : h_U ⟶ Y` and
`ν : Y ⟶ X` be given with `ν` relatively representable, let `CU ⟶ C` represent the base change of
`j ≫ ν` along a chart `c : h_C ⟶ X`, and let `D ⟶ C` represent that of `ν`, so that
`r : CU ⟶ D` is the chart of `j`. Let `W₀` be the open complement of the graph of `j` inside the
represented fibre product `P₀ = U ×_X Y`. If the chart of `j` is a dense open immersion, the
chart of `ν` is integral and `n + 1` bounds the fibre degrees of `CU ⟶ C`, then the base change
of `W₀ ⟶ Y` along `D ⟶ Y` is represented by a scheme whose fibre degrees over `D` are bounded by
`n`.

The represented fibre product `Pc = CU ×_C D` is `P₀ ×_Y D` and `P₀ ×_U CU` by pasting, the graph
of the chart of `j` is the base change of the graph of `j`, so the complement of the former is the
preimage of `W₀`; and `Stacks.MoreMorphisms.boundsFiberDegrees_compl_range_lift_of_isPullback`
bounds its fibre degrees. -/
theorem exists_isPullback_boundsFiberDegrees_of_graphCompl
    {U C CU D W₀ : BigFppfOver B S hS} {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (j : yoneda.obj U ⟶ Y) (ν : Y ⟶ X) (hν : yoneda.relativelyRepresentable ν)
    {c : yoneda.obj C ⟶ X} {a : yoneda.obj CU ⟶ yoneda.obj U} {π : CU ⟶ C}
    (hsq : IsPullback a (yoneda.map π) (j ≫ ν) c)
    {q : D ⟶ C} {b : yoneda.obj D ⟶ Y} {r : CU ⟶ D}
    (hbq : IsPullback b (yoneda.map q) ν c) (hrb : yoneda.map r ≫ b = a ≫ j) (hrq : r ≫ q = π)
    [_root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map r)]
    [_root_.AlgebraicGeometry.IsIntegralHom ((BigFppfOver.toScheme B S hS).map q)]
    [Etale ((BigFppfOver.toScheme B S hS).map π)]
    [_root_.AlgebraicGeometry.IsSeparated ((BigFppfOver.toScheme B S hS).map π)]
    [QuasiCompact ((BigFppfOver.toScheme B S hS).map π)]
    [CompactSpace ((BigFppfOver.toScheme B S hS).obj D)]
    (hdense : DenseRange ((BigFppfOver.toScheme B S hS).map r).base) (n : ℕ)
    (hb : BoundsFiberDegrees ((BigFppfOver.toScheme B S hS).map π) ((n + 1 : ℕ) : ℤ))
    (w₀ : W₀ ⟶ hν.pullback (j ≫ ν))
    (hw₀ : _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map w₀))
    (hW₀ : Set.range ((BigFppfOver.toScheme B S hS).map w₀) =
      (Set.range ((BigFppfOver.toScheme B S hS).map
        (hν.lift (g := j ≫ ν) j (𝟙 U) (by simp))))ᶜ)
    (hW₀fac : ∀ {T : BigFppfOver B S hS} (t : T ⟶ hν.pullback (j ≫ ν)),
      Set.range ((BigFppfOver.toScheme B S hS).map t) ⊆
        Set.range ((BigFppfOver.toScheme B S hS).map w₀) → ∃ h : T ⟶ W₀, h ≫ w₀ = t) :
    ∃ (G : BigFppfOver B S hS) (g : G ⟶ W₀) (dG : G ⟶ D),
      IsPullback (yoneda.map g) (yoneda.map dG) (yoneda.map w₀ ≫ hν.fst (j ≫ ν)) b ∧
        BoundsFiberDegrees ((BigFppfOver.toScheme B S hS).map dG) (n : ℤ) := by
  let 𝒯 := BigFppfOver.toScheme B S hS
  set γ := hν.lift (g := j ≫ ν) j (𝟙 U) (by simp)
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : CU ⟶ U, yoneda.map a₀ = a :=
    ⟨yoneda.preimage a, yoneda.map_preimage a⟩
  have hPc := IsPullback.of_hasPullback (r ≫ q) q
  set pr₁ := Limits.pullback.fst (r ≫ q) q
  set pr₂ := Limits.pullback.snd (r ≫ q) q
  have hc : pr₁ ≫ π = pr₂ ≫ q := by rw [← hrq]; exact hPc.w
  have hmw : (yoneda.map pr₂ ≫ b) ≫ ν = yoneda.map (pr₁ ≫ a₀) ≫ (j ≫ ν) := by
    rw [Category.assoc, hbq.w, Functor.map_comp, Category.assoc, ha₀, hsq.w,
      ← Category.assoc, ← Category.assoc, ← Functor.map_comp, ← Functor.map_comp, hc]
  set m := hν.lift (g := j ≫ ν) (yoneda.map pr₂ ≫ b) (pr₁ ≫ a₀) hmw
  have hPc' : IsPullback pr₂ pr₁ q π := by rw [← hrq]; exact hPc.flip
  -- `Pc = P₀ ×_U CU`
  have hA' : IsPullback (yoneda.map m) (yoneda.map pr₁) (yoneda.map (hν.snd (j ≫ ν))) a := by
    refine IsPullback.of_right (h₁₂ := hν.fst (j ≫ ν)) (h₂₂ := j ≫ ν) (v₁₃ := ν) ?_ ?_
      (hν.isPullback (j ≫ ν))
    · rw [hν.lift_fst, hsq.w]
      exact (hPc'.map yoneda).paste_horiz hbq
    · rw [← Functor.map_comp, hν.lift_snd, Functor.map_comp, ha₀]
  -- `Pc = P₀ ×_Y D`
  have hA : IsPullback (yoneda.map m) (yoneda.map pr₂) (hν.fst (j ≫ ν)) b := by
    refine (IsPullback.of_right (h₁₂ := yoneda.map q) (h₂₂ := ν) (v₁₃ := c) ?_ ?_
      hbq.flip).flip
    · have : yoneda.map pr₂ ≫ yoneda.map q = yoneda.map pr₁ ≫ yoneda.map π := by
        rw [← Functor.map_comp, ← Functor.map_comp, hc]
      rw [this, hν.w]
      exact hA'.flip.paste_horiz hsq.flip
    · exact (hν.lift_fst _ _ _).symm
  -- the graph of the chart of `j` is the base change of the graph of `j`
  set γc : CU ⟶ Limits.pullback (r ≫ q) q :=
    Limits.pullback.lift (𝟙 CU) r (by rw [Category.id_comp])
  have hB : IsPullback (yoneda.map γc) a (yoneda.map m) (yoneda.map γ) := by
    refine isPullback_section_of_isPullback (π := yoneda.map (hν.snd (j ≫ ν)))
      (by rw [← Functor.map_comp, hν.lift_snd, CategoryTheory.Functor.map_id]) hA'.flip
      (by rw [← Functor.map_comp, Limits.pullback.lift_fst, CategoryTheory.Functor.map_id]) ?_
    rw [← ha₀, ← Functor.map_comp, ← Functor.map_comp]
    congr 1
    apply hν.hom_ext
    · rw [Functor.map_comp, Category.assoc, hν.lift_fst, Functor.map_comp, Category.assoc,
        hν.lift_fst, ← Category.assoc, ← Functor.map_comp, Limits.pullback.lift_snd, hrb, ha₀]
    · rw [Category.assoc, hν.lift_snd, Category.assoc, hν.lift_snd, ← Category.assoc,
        Limits.pullback.lift_fst, Category.id_comp, Category.comp_id]
  have hB' : IsPullback (yoneda.map γc) (yoneda.map a₀) (yoneda.map m) (yoneda.map γ) := by
    rw [ha₀]; exact hB
  have hBs := (IsPullback.of_map_of_faithful yoneda hB').map 𝒯
  have hrangeB : Set.range (𝒯.map γc) = (𝒯.map m).base ⁻¹' Set.range (𝒯.map γ) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨(𝒯.map a₀).base y, by rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
        hBs.w]⟩
    · intro hx
      obtain ⟨z, rfl⟩ : x ∈ Set.range (Limits.pullback.fst (𝒯.map m) (𝒯.map γ)).base := by
        rw [Scheme.Pullback.range_fst]; exact hx
      exact ⟨hBs.isoPullback.inv.base z, by
        rw [← Scheme.Hom.comp_apply, hBs.isoPullback_inv_fst]⟩
  -- the degree drop on the chart
  have hsqS : IsPullback (𝒯.map pr₁) (𝒯.map pr₂) (𝒯.map r ≫ 𝒯.map q) (𝒯.map q) := by
    rw [← Functor.map_comp]; exact hPc.map 𝒯
  have hrqS : 𝒯.map r ≫ 𝒯.map q = 𝒯.map π := by rw [← Functor.map_comp, hrq]
  have : Etale (𝒯.map r ≫ 𝒯.map q) := by rw [hrqS]; infer_instance
  have : _root_.AlgebraicGeometry.IsSeparated (𝒯.map r ≫ 𝒯.map q) := by
    rw [hrqS]; infer_instance
  have : QuasiCompact (𝒯.map r ≫ 𝒯.map q) := by rw [hrqS]; infer_instance
  have hlift : hsqS.lift (𝟙 _) (𝒯.map r) (by simp) = 𝒯.map γc := by
    apply hsqS.hom_ext
    · rw [hsqS.lift_fst, ← Functor.map_comp, Limits.pullback.lift_fst,
        CategoryTheory.Functor.map_id]
    · rw [hsqS.lift_snd, ← Functor.map_comp, Limits.pullback.lift_snd]
  have hOeq : (Set.range (𝒯.map γc))ᶜ = (𝒯.map m).base ⁻¹' Set.range (𝒯.map w₀) := by
    rw [hrangeB, hW₀, Set.preimage_compl]
  let O : (𝒯.obj (Limits.pullback (r ≫ q) q)).Opens :=
    ⟨(Set.range (𝒯.map γc))ᶜ, by
      rw [hOeq]; exact (𝒯.map w₀).isOpenEmbedding.isOpen_range.preimage (𝒯.map m).continuous⟩
  have hbd := Stacks.MoreMorphisms.boundsFiberDegrees_compl_range_lift_of_isPullback
    (𝒯.map r) (𝒯.map q) n (by rwa [hrqS]) hdense hsqS O (by rw [hlift]; rfl)
  obtain ⟨G, iG, hiG, hrG, hfacG⟩ := exists_restrict_bigFppfOver _ O
  obtain ⟨g, hg⟩ := hW₀fac (iG ≫ m) (by
    rintro _ ⟨x, rfl⟩
    rw [Functor.map_comp, Scheme.Hom.comp_apply, ← Set.mem_preimage, ← hOeq]
    exact hrG.le ⟨x, rfl⟩)
  have hP := isPullback_of_range_subset_of_isOpenImmersion m iG w₀ g hiG hw₀
    (fun t ht => hfacG t (by rw [← hrG]; exact ht))
    (by rw [hrG]; exact hOeq.symm.subset) hg
  refine ⟨G, g, iG ≫ pr₂, ?_, ?_⟩
  · rw [Functor.map_comp]
    exact (hP.map yoneda).paste_vert hA
  · let eO := IsOpenImmersion.isoOfRangeEq (𝒯.map iG) O.ι (by rw [hrG, O.range_ι])
    have hsq' : IsPullback eO.hom (𝒯.map (iG ≫ pr₂)) (O.ι ≫ 𝒯.map pr₂) (𝟙 _) := by
      refine IsPullback.of_horiz_isIso ⟨?_⟩
      rw [← Category.assoc, IsOpenImmersion.isoOfRangeEq_hom_fac, Functor.map_comp,
        Category.comp_id]
    exact boundsFiberDegrees_of_isPullback hsq' hbd

end AlgebraicGeometry.Space

end
