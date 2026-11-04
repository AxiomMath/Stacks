module

public import StacksFrontier.AlgebraicGeometry.Spaces.LimitSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescentUnbounded
import all StacksFrontier.AlgebraicGeometry.Spaces.ApproximationSteps
import all StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphismProperties

/-!
# Stacks 08K0, flatness of a module, with no bound on the index

`AlgebraicGeometry.Space.MorphismDescentSystem.exists_isFlatOver_mapAt` is Stacks 08K0 (flatness
of a module) for the situation `AlgebraicGeometry.Space.MorphismDescentSystem` of Stacks 084W.
That situation bounds the cardinality of the index by the cofinality of the site's cutoff
(`AlgebraicGeometry.Space.MorphismDescentSystem.indexSize`), and the source has no such bound.
This file states the lemma for any cofiltered inverse system with affine transition morphisms.
In place of the bound it assumes the chapter's convention 07SD (tag 07SD, Section 70.2): the
limits of the base changes of the stages to the affine objects of the site lie in the site. This
is the hypothesis `hconv` of
`AlgebraicGeometry.Space.exists_model_of_finitePresentation_of_chartLimitsInSite`, and it states
`AlgebraicGeometry.Space.SiteContainsBaseChangeLimits` unfolded.
It is the source's standing convention read for the system, not an extra assumption.

## Implementation notes

The proof is that of `AlgebraicGeometry.Space.MorphismDescentSystem.exists_isFlatOver_mapAt`.
There the bound is used once, to form the limit of the affine charts of the stages in the site;
here that limit comes from the convention. The comparison between flatness of the module and
flatness on one square of affine étale charts only involves the distinguished stage. It is reused
from the base file through the situation of Stacks 084W over the one-point index whose only stage
is the distinguished one.

This lives in its own module, not beside the bounded lemma, because it needs Stacks 07SF under
the convention (`AlgebraicGeometry.Space.isAlgebraicSpace_limit_of_chartLimitsInSite`). Importing
that into the base module would enlarge its import closure by many modules.

## References

* [Stacks Project, Tag 07SD](https://stacks.math.columbia.edu/tag/07SD)
* [Stacks Project, Tag 084W](https://stacks.math.columbia.edu/tag/084W)
* [Stacks Project, Tag 08K0](https://stacks.math.columbia.edu/tag/08K0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

section ModuleFlatness

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})}

/-- The situation of Stacks 084W over the one-point index whose only stage is `B₀`, for a morphism
`f : X ⟶ Y` of spaces over `B₀`. It only serves to choose a square of affine étale charts at the
distinguished stage, and to compare flatness of a module with flatness on that square. -/
private abbrev pointMorphismDescentSystem {B₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hB₀ : IsAlgebraicSpace B S hS B₀) (hB₀qc : IsQuasiCompactSpace B S hS B₀)
    (hB₀qs : IsAbsolutelyQuasiSeparated B S hS hZ B₀) {X Y : Over B₀} (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X.left) (hY : IsAlgebraicSpace B S hS Y.left)
    (hXqc : IsQuasiCompactSpace B S hS X.left) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.left)
    (hYqc : IsQuasiCompactSpace B S hS Y.left)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.left) :
    MorphismDescentSystem B S hS hZ PUnit.{u + 1} where
  base := (Functor.const _).obj B₀
  indexSize := (Cardinal.le_one_iff_subsingleton.mpr inferInstance).trans_lt
    (Cardinal.one_lt_aleph0.trans B.aleph0_lt_cutoff_cof)
  base_isAlgebraicSpace _ := hB₀
  transition_affine _ := isAffineHom_of_isIso _
  limit_isAlgebraicSpace := by
    let c : Cone ((Functor.const PUnit.{u + 1}ᵒᵖ).obj B₀) :=
      { pt := B₀, π := { app := fun _ => 𝟙 B₀ } }
    have hc : IsLimit c :=
      { lift := fun s => s.π.app (op PUnit.unit)
        fac := fun s j => by
          obtain ⟨⟨⟩⟩ := j
          simp [c]
        uniq := fun s m hm => by simpa [c] using hm (op PUnit.unit) }
    exact hB₀.of_iso ((limit.isLimit _).conePointUniqueUpToIso hc).symm
  initial := PUnit.unit
  source₀ := X.left
  target₀ := Y.left
  sourceToBase := X.hom
  targetToBase := Y.hom
  map₀ := f.left
  map₀_over := Over.w f
  source₀_isAlgebraicSpace := hX
  target₀_isAlgebraicSpace := hY
  base₀_quasiCompact := hB₀qc
  base₀_quasiSeparated := hB₀qs
  source₀_quasiCompact := hXqc
  source₀_quasiSeparated := hXqs
  target₀_quasiCompact := hYqc
  target₀_quasiSeparated := hYqs

/-- **Stacks 08K0, flatness of a module, with no bound on the index.** Let `(B_i)` be a
cofiltered inverse system of algebraic spaces over `S` with affine transition morphisms, let `i`
be a stage with `B_i` quasi-compact and quasi-separated, and let `f : X ⟶ Y` be a morphism of
quasi-compact, quasi-separated algebraic spaces over `B_i`. Let `F₀` be a quasi-coherent
`𝒪_X`-module of finite presentation. Suppose the pullback of `F₀` to `lim B_j ×_{B_i} X` is flat
over `lim B_j ×_{B_i} Y`, and `f` is locally of finite presentation. Then for some stage `j ⟶ i`
the pullback of `F₀` to `B_j ×_{B_i} X` is flat over `B_j ×_{B_i} Y`.

This strengthens `AlgebraicGeometry.Space.MorphismDescentSystem.exists_isFlatOver_mapAt`. The
bound `MorphismDescentSystem.indexSize` on the index is replaced by `hconv`. `hconv` is the
chapter's convention 07SD: the limits of the base changes of the stages to the affine objects of
the site lie in the site. It is not an assumption beyond the source. It is equivalent to
`AlgebraicGeometry.Space.SiteContainsBaseChangeLimits`, which it states unfolded, and the index
bound implies it (`AlgebraicGeometry.Space.chartLimitsInSite_of_lt_cof`). -/
@[stacks 08K0 "flatness of a module, with no bound on the index: the 07SD convention in place \
  of the index bound of MorphismDescentSystem, which exists_isFlatOver_mapAt carries"]
theorem exists_isFlatOver_baseChange_of_chartLimitsInSite
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hconv : ∀ (i : I) (Z : BigAffineFppf B S hS)
      (g : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj Z) ⟶ D.obj i)
      (W : Over i ⥤ BigAffineFppf B S hS),
      (W ⋙ (BigAffineFppf.inclusion B S hS ⋙ yoneda) ≅
        (Over.post (X := i) D ⋙ Over.pullback g) ⋙
          Over.forget (yoneda.obj ((BigAffineFppf.inclusion B S hS).obj Z))) →
      ∀ c : Cone (((W ⋙ BigAffineFppf.inclusion B S hS) ⋙
          BigFppfOver.forget B S hS) ⋙ B.inclusion),
        IsLimit c → B.Contains c.pt)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (i : I) (hB₀qc : IsQuasiCompactSpace B S hS (D.obj i))
    (hB₀qs : IsAbsolutelyQuasiSeparated B S hS hZ (D.obj i))
    {X Y : Over (D.obj i)} (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X.left) (hY : IsAlgebraicSpace B S hS Y.left)
    (hXqc : IsQuasiCompactSpace B S hS X.left) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.left)
    (hYqc : IsQuasiCompactSpace B S hS Y.left) (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.left)
    (F₀ : Modules.{u, u} B S hS X.left hX)
    [F₀.IsQuasicoherentOnSite] [F₀.IsFinitePresentationOnSite]
    (flat : IsFlatOver B S hS
      (isAlgebraicSpace_pullback B S hS (limit.π D i) X.hom
        (isAlgebraicSpace_limit_of_chartLimitsInSite B S hS D hconv hD hAffine i hB₀qc) hX (hD i))
      (pullback.map (limit.π D i) X.hom (limit.π D i) Y.hom (𝟙 _) f.left (𝟙 _) (by simp)
        (by simp))
      ((modulePullback B S hS (ObjectProperty.homMk (pullback.snd (limit.π D i) X.hom) :
          (⟨pullback (limit.π D i) X.hom,
            isAlgebraicSpace_pullback B S hS (limit.π D i) X.hom
              (isAlgebraicSpace_limit_of_chartLimitsInSite B S hS D hconv hD hAffine i hB₀qc) hX
              (hD i)⟩ : AlgebraicSpaces B S hS) ⟶ ⟨X.left, hX⟩)).obj F₀))
    (fp : IsLocallyOfFinitePresentation B S hS f.left) :
    ∃ (j : I) (e : j ⟶ i), IsFlatOver B S hS
      (isAlgebraicSpace_pullback B S hS (D.map e) X.hom (hD j) hX (hD i))
      (pullback.map (D.map e) X.hom (D.map e) Y.hom (𝟙 _) f.left (𝟙 _) (by simp) (by simp))
      ((modulePullback B S hS (ObjectProperty.homMk (pullback.snd (D.map e) X.hom) :
          (⟨pullback (D.map e) X.hom,
            isAlgebraicSpace_pullback B S hS (D.map e) X.hom (hD j) hX (hD i)⟩ :
              AlgebraicSpaces B S hS) ⟶ ⟨X.left, hX⟩)).obj F₀) := by
  let D' := pointMorphismDescentSystem (hD i) hB₀qc hB₀qs f hX hY hXqc hXqs hYqc hYqs
  obtain ⟨C⟩ := nonempty_chartSquare D'
  let H := BigFppfOver.toScheme B S hS
  -- the system of affine charts of the stages over `i`, and its limit in the site
  let Sys := affineChartSystem B S hS i D C.targetObj C.baseChart hAffine
  have hL := hconv i C.targetObj C.baseChart Sys.diagram Sys.iso
  let L : Sys.LimitBridge := AffineChartSystem.limitBridgeOfHasLimit Sys
    (hasLimit_of_isAffine_of_sizeBelow Sys.siteDiagram Sys.isAffine_obj hL)
    (preservesLimit_toScheme_of_sizeBelow Sys.siteDiagram Sys.isAffine_obj hL)
  let stageChart : ∀ j : Over i, Sys.siteDiagram.obj j ⟶
      (BigAffineFppf.inclusion B S hS).obj C.targetObj := fun j => yoneda.preimage (Sys.baseMap j)
  let limitChart : L.cone.pt ⟶ (BigAffineFppf.inclusion B S hS).obj C.targetObj :=
    yoneda.preimage L.toBase
  have isPullback_stageChart : ∀ j : Over i, IsPullback (Sys.stageMap j)
      (yoneda.map (stageChart j)) (D.map j.hom) C.baseChart := fun j => by
    simp only [stageChart, Functor.map_preimage]
    exact Sys.isPullback j
  have isPullback_limitChart : IsPullback L.toLimit (yoneda.map limitChart) (limit.π D i)
      C.baseChart := by
    simp only [limitChart, Functor.map_preimage]
    exact L.isPullback
  have siteDiagram_map_comp_stageChart : ∀ {j k : Over i} (g : j ⟶ k),
      Sys.siteDiagram.map g ≫ stageChart k = stageChart j := by
    intro j k g
    have hnat : yoneda.map (Sys.siteDiagram.map g) ≫ Sys.iso.hom.app k =
        Sys.iso.hom.app j ≫ (stageBaseChangeDiagram B S hS i D C.targetObj C.baseChart).map g :=
      Sys.iso.hom.naturality g
    have hw : (stageBaseChangeDiagram B S hS i D C.targetObj C.baseChart).map g ≫
        stageBaseChangeSnd B S hS i D C.targetObj C.baseChart k =
        stageBaseChangeSnd B S hS i D C.targetObj C.baseChart j :=
      Over.w ((Over.post (X := i) D ⋙ Over.pullback C.baseChart).map g)
    apply yoneda.map_injective
    simp only [stageChart, Functor.map_comp, Functor.map_preimage, AffineChartSystem.baseMap]
    rw [← Category.assoc, hnat, Category.assoc, hw]
  have cone_π_comp_stageChart : ∀ j : Over i, L.cone.π.app j ≫ stageChart j = limitChart := by
    intro j
    apply yoneda.map_injective
    simp only [stageChart, limitChart, Functor.map_comp, Functor.map_preimage]
    exact L.baseMap_comp j
  -- the module on the chart of the source
  let M : (H.obj ((BigAffineFppf.inclusion B S hS).obj C.sourceObj)).Modules :=
    restrictToChart B S hS D'.source₀_isAlgebraicSpace F₀ C.sourceSmallEtale
  have : M.IsQuasicoherent :=
    isQuasicoherent_restrictToChart B S hS ⟨D'.source₀, D'.source₀_isAlgebraicSpace⟩ F₀
      inferInstance C.sourceSmallEtale
  have : M.IsFinitePresentation :=
    isFinitePresentation_restrictToChart B S hS ⟨D'.source₀, D'.source₀_isAlgebraicSpace⟩ F₀
      inferInstance inferInstance C.sourceSmallEtale
  have hchartFp : LocallyOfFinitePresentation (H.map C.chartMap) :=
    fp _ _ C.sourceChart C.targetChart C.chartMap C.sourceChart_etale
      C.targetChart_etale C.comm
  let diagram := Sys.schemeDiagram
  let cone : Cone diagram := H.mapCone L.cone
  let j₀ : Over i := Over.mk (𝟙 i)
  let st₀ := H.map (stageChart j₀)
  let g := pullback.snd (H.map C.chartMap) st₀
  let N := (Scheme.Modules.pullback (pullback.fst (H.map C.chartMap) st₀)).obj M
  have key : ∀ {W : BigFppfOver B S hS} (s : H.obj W ⟶ diagram.obj j₀)
      (q : W ⟶ (BigAffineFppf.inclusion B S hS).obj C.targetObj), s ≫ st₀ = H.map q →
      (_root_.AlgebraicGeometry.IsFlatOver (pullback.snd g s).toLRSHom.toShHom
          ((Scheme.Modules.pullback (pullback.fst g s)).obj N) ↔
        _root_.AlgebraicGeometry.IsFlatOver (H.map (pullback.snd C.chartMap q)).toLRSHom.toShHom
          ((Scheme.Modules.pullback (H.map (pullback.fst C.chartMap q))).obj M)) := by
    intro W s q hs
    have h₁ := (IsPullback.of_hasPullback g s).paste_horiz
      (IsPullback.of_hasPullback (H.map C.chartMap) st₀)
    rw [hs] at h₁
    exact (_root_.AlgebraicGeometry.isFlatOver_iff_of_iso _
      ((schemeModulePullbackCompIso (pullback.fst g s) (pullback.fst (H.map C.chartMap) st₀)).app
        M)).trans (isFlatOver_modulePullback_iff_of_isPullback h₁
          ((IsPullback.of_hasPullback C.chartMap q).map H) M)
  have hqL : cone.π.app j₀ ≫ st₀ = H.map limitChart := by
    show H.map (L.cone.π.app j₀) ≫ _ = _
    rw [← Functor.map_comp, cone_π_comp_stageChart j₀]
  have hXlim := isAlgebraicSpace_pullback B S hS (limit.π D i) X.hom
    (isAlgebraicSpace_limit_of_chartLimitsInSite B S hS D hconv hD hAffine i hB₀qc) hX (hD i)
  have hYlim := isAlgebraicSpace_pullback B S hS (limit.π D i) Y.hom
    (isAlgebraicSpace_limit_of_chartLimitsInSite B S hS D hconv hD hAffine i hB₀qc) hY (hD i)
  have hlimit := (key (cone.π.app j₀) limitChart hqL).mpr
    ((isFlatOver_modulePullback_baseChange_iff C F₀ (limit D) (limit.π D i)
      L.cone.pt L.toLimit limitChart isPullback_limitChart
      (pullback.map (limit.π D i) X.hom (limit.π D i) Y.hom (𝟙 _) f.left (𝟙 _) (by simp)
        (by simp)) ((pullback.lift_fst _ _ _).trans (Category.comp_id _))
      (pullback.lift_snd _ _ _) hXlim
      hYlim).mp flat)
  have : ∀ {j k : Over i} (e : j ⟶ k), _root_.AlgebraicGeometry.IsAffineHom (diagram.map e) :=
    fun e ↦ Sys.isAffineHom_map e
  have : ∀ j, CompactSpace (diagram.obj j) :=
    fun j ↦ have := Sys.isAffine_obj j; Scheme.compactSpace_of_isAffine _
  have : ∀ j, QuasiSeparatedSpace (diagram.obj j) :=
    fun j ↦ have := Sys.isAffine_obj j; inferInstance
  have : IsAffine (H.obj ((BigAffineFppf.inclusion B S hS).obj C.sourceObj)) :=
    C.sourceObj.property
  have : IsAffine (H.obj ((BigAffineFppf.inclusion B S hS).obj C.targetObj)) :=
    C.targetObj.property
  have : IsAffine (H.obj (Sys.siteDiagram.obj j₀)) := Sys.isAffine_obj j₀
  have : _root_.AlgebraicGeometry.IsAffineHom st₀ := isAffineHom_of_isAffine _
  have : _root_.AlgebraicGeometry.IsAffineHom (pullback.fst (H.map C.chartMap) st₀) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _).flip ‹_›
  have : IsAffine (pullback (H.map C.chartMap) st₀) :=
    isAffine_of_isAffineHom (pullback.fst (H.map C.chartMap) st₀)
  have : CompactSpace ↥(pullback (H.map C.chartMap) st₀) := Scheme.compactSpace_of_isAffine _
  have : LocallyOfFinitePresentation g :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback (H.map C.chartMap) st₀) hchartFp
  have : N.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback _ M
  have : SheafOfModules.IsFinitePresentation (R := structureSheafRing
      (H.obj ((BigAffineFppf.inclusion B S hS).obj C.sourceObj)).toRingedSpace) M := ‹_›
  have : N.IsFinitePresentation :=
    Stacks.SheafOfModules.modulePullback_isFinitePresentation
      (pullback.fst (H.map C.chartMap) st₀).toLRSHom.toShHom M
  obtain ⟨j, e, hj⟩ := exists_isFlatOver_modulePullback_pullback_snd diagram cone
    L.schemeIsLimit j₀ g N hlimit
  have hqj : diagram.map e ≫ st₀ = H.map (stageChart j) := by
    show H.map (Sys.siteDiagram.map e) ≫ _ = _
    rw [← Functor.map_comp, siteDiagram_map_comp_stageChart e]
  exact ⟨j.left, j.hom,
    (isFlatOver_modulePullback_baseChange_iff C F₀ _ _ _ (Sys.stageMap j) (stageChart j)
      (isPullback_stageChart j)
      (pullback.map (D.map j.hom) X.hom (D.map j.hom) Y.hom (𝟙 _) f.left (𝟙 _) (by simp)
        (by simp)) ((pullback.lift_fst _ _ _).trans (Category.comp_id _))
      (pullback.lift_snd _ _ _)
      (isAlgebraicSpace_pullback B S hS (D.map j.hom) X.hom (hD j.left) hX (hD i))
      (isAlgebraicSpace_pullback B S hS (D.map j.hom) Y.hom (hD j.left) hY (hD i))).mpr
      ((key (diagram.map e) (stageChart j) hqj).mp hj)⟩

end ModuleFlatness

end AlgebraicGeometry.Space

end
