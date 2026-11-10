module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.CutoffBoundedSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphismProperties

/-!
# Étaleness descends to a stage of a system bounded by the cutoff

Stacks 07SL says: in the situation of Stacks 084W, if the base change `f : X ⟶ Y` of a morphism
`f₀ : X₀ ⟶ Y₀` of finite presentation over the stage `B₀` to the limit `B = lim Bᵢ` is étale,
then so is its base change `fᵢ : Xᵢ ⟶ Yᵢ` to some stage. The library proves it as
`AlgebraicGeometry.Space.MorphismDescentSystem.exists_isEtale_mapAt` for a morphism descent
system, whose index set is asked to be smaller than the cofinality of the site's cutoff. This
file proves it for an inverse system bounded by the cutoff
(`AlgebraicGeometry.Space.IsCutoffBoundedSystem`), with no condition on the cofinality.

The proof is the library's. A square of affine étale charts `U₀ ⟶ V₀` of `f₀` is chosen, the
chart `V₀ ⟶ Y₀ ⟶ B₀` of the stage is base changed to a system of affine charts of the stages,
and étaleness of every base change of `f₀` is read on the base change of `U₀ ⟶ V₀` to the chart
of that base change. The limit of the system of charts is taken with
`AlgebraicGeometry.Space.AffineChartSystem.limitBridgeOfBaseChangeSizeBounded` in place of
`AlgebraicGeometry.Space.AffineChartSystem.limitBridge`; that is the only point where the bound
by the cofinality entered. The descent along the limit of affine schemes is Stacks 07RP,
`AlgebraicGeometry.exists_etale_pullback_of_isLimit`.

The system is unbundled, and the base changes of `f₀` are written as `pullback.map`, as in the
hypothesis `h08K1` of
`exists_isLimit_isProper_isFinitePresentation_arrow_of_cutoffBoundedApproximations` (in the
namespace `AlgebraicGeometry.Space`).

## Main results

* `AlgebraicGeometry.Space.exists_isEtale_pullbackMap_of_isCutoffBoundedSystem`: Stacks 07SL for
  an inverse system bounded by the cutoff.

Nothing here is registered: Stacks 07SL is registered on the base in its bounded form.

## References

* [Stacks Project, Tag 07SL](https://stacks.math.columbia.edu/tag/07SL)
* [Stacks Project, Tag 084W](https://stacks.math.columbia.edu/tag/084W)
* [Stacks Project, Tag 07RP](https://stacks.math.columbia.edu/tag/07RP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (hZ : B.Contains (⊤_ Scheme.{u}))

attribute [local instance] MorphismProperty.relative_isStableUnderBaseChange

/-- Pullbacks in the big fppf category over `S` (instance search times out without this
shortcut). -/
local instance hasPullbacks_bigFppfOver_etaleStageOfCutoffBoundedSystem :
    HasPullbacks (BigFppfOver B S hS) :=
  hasPullbacks_bigFppfOver B S hS

local instance (priority := high) hasPullback_bigFppfOver_etaleStageOfCutoffBoundedSystem
    {X Y Z : BigFppfOver B S hS} (f : X ⟶ Z) (g : Y ⟶ Z) : HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- A morphism `f₀ : X₀ ⟶ Y₀` of algebraic spaces over `S`, locally of finite presentation, with
`X₀` and `Y₀` quasi-compact and `Y₀` quasi-separated, has a square of affine étale charts: an
étale `b : U ⟶ Y₀` and an étale surjective `a : V ⟶ X₀` from affine objects, with a
morphism `r : V ⟶ U` locally of finite presentation lying over `f₀`. -/
private theorem exists_affine_etale_chart_square {X₀ Y₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f₀ : X₀ ⟶ Y₀) (hX₀ : IsAlgebraicSpace B S hS X₀) (hY₀ : IsAlgebraicSpace B S hS Y₀)
    (hX₀qc : IsQuasiCompactSpace B S hS X₀) (hY₀qc : IsQuasiCompactSpace B S hS Y₀)
    (hY₀qs : IsAbsolutelyQuasiSeparated B S hS hZ Y₀)
    (fp : IsLocallyOfFinitePresentation B S hS f₀) :
    ∃ (U V : BigFppfOver B S hS) (b : yoneda.obj U ⟶ Y₀) (a : yoneda.obj V ⟶ X₀) (r : V ⟶ U),
      IsAffine ((BigFppfOver.toScheme B S hS).obj U) ∧
      IsAffine ((BigFppfOver.toScheme B S hS).obj V) ∧
      (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} :
        MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf b ∧
      (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} :
        MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf a ∧
      (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u} :
        MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf a ∧
      yoneda.map r ≫ b = a ≫ f₀ ∧
      LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map r) := by
  have hEtMul := isMultiplicative_presheaf_etale B S hS
  have hSuMul := isMultiplicative_presheaf_surjective B S hS
  /- A square of affine étale charts of `f₀`: `b : V₀ ⟶ Y₀` étale surjective, `cover` an étale
  surjective chart of `X₀ ×_{Y₀} V₀`, `a : U₀ ⟶ X₀` and `r : U₀ ⟶ V₀` the composites. -/
  obtain ⟨U, b, hU, hbS, hbE⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS Y₀ hY₀).mp hY₀qc
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj U) := hU
  have hfibSpace : IsAlgebraicSpace B S hS (pullback f₀ b) :=
    isAlgebraicSpace_pullback B S hS f₀ b hX₀ (isAlgebraicSpace_yoneda B S hS U) hY₀
  have hfib : IsQuasiCompactSpace B S hS (pullback f₀ b) :=
    isQuasiCompactSpace_pullback B S hS hZ f₀ b hX₀ hY₀ hX₀qc
      (isQuasiCompactSpace_yoneda_obj B S hS inferInstance) hY₀qs
  obtain ⟨V, cover, hV, hcS, hcE⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS _ hfibSpace).mp hfib
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj V) := hV
  have hbE' := (isEtale_iff_presheaf_of_yoneda B S hS b).mp hbE
  have hcE' := (isEtale_iff_presheaf_of_yoneda B S hS cover).mp hcE
  let r : V ⟶ U := yoneda.preimage (cover ≫ pullback.snd f₀ b)
  let a : yoneda.obj V ⟶ X₀ := cover ≫ pullback.fst f₀ b
  have haE : (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} :
      MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf a :=
    MorphismProperty.comp_mem _ _ _ hcE'
      (MorphismProperty.of_isPullback (IsPullback.of_hasPullback f₀ b).flip hbE')
  have haS : (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u} :
      MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf a :=
    MorphismProperty.comp_mem _ _ _ hcS
      (MorphismProperty.of_isPullback (IsPullback.of_hasPullback f₀ b).flip hbS)
  have hcomm : yoneda.map r ≫ b = a ≫ f₀ := by
    simp only [r, a, Functor.map_preimage, Category.assoc, pullback.condition]
  exact ⟨U, V, b, a, r, hU, hV, hbE', haE, haS, hcomm, fp _ _ a b r haE hbE' hcomm⟩

/-- Given a square of étale charts `a`, `b`, `r` of `f₀ : X₀ ⟶ Y₀` over `B₀`, étaleness of the
base change of `f₀` along `t : B' ⟶ B₀` is étaleness of the base change of `r` to a chart
`q : W ⟶ U` of `B' ×_{B₀} U`. -/
private theorem isEtale_pullbackMap_iff_etale_pullback_snd
    {X₀ Y₀ B₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (x : X₀ ⟶ B₀) (y : Y₀ ⟶ B₀) (f₀ : X₀ ⟶ Y₀)
    (hf₀ : f₀ ≫ y = x) (hX₀ : IsAlgebraicSpace B S hS X₀) (hY₀ : IsAlgebraicSpace B S hS Y₀)
    (hB₀ : IsAlgebraicSpace B S hS B₀) {U V : BigFppfOver B S hS} (b : yoneda.obj U ⟶ Y₀)
    (a : yoneda.obj V ⟶ X₀) (r : V ⟶ U)
    (haE : (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} :
      MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf a)
    (haS : (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u} :
      MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf a)
    (hbE : (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} :
      MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf b)
    (hcomm : yoneda.map r ≫ b = a ≫ f₀) (B' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hB' : IsAlgebraicSpace B S hS B') (t : B' ⟶ B₀) {W : BigFppfOver B S hS}
    (p : yoneda.obj W ⟶ B') (q : W ⟶ U) (hp : IsPullback p (yoneda.map q) t (b ≫ y)) :
    IsEtale B S hS (pullback.map t x t y (𝟙 _) f₀ (𝟙 _) (by simp) (by simp [hf₀])) ↔
      AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map (pullback.snd r q)) := by
  set f' := pullback.map t x t y (𝟙 _) f₀ (𝟙 _) (by simp) (by simp [hf₀])
  have hf₁ : f' ≫ pullback.fst t y = pullback.fst t x := by simp [f']
  have hf₂ : f' ≫ pullback.snd t y = pullback.snd t x ≫ f₀ := by simp [f']
  have hX' : IsAlgebraicSpace B S hS (pullback t x) :=
    isAlgebraicSpace_pullback B S hS t x hB' hX₀ hB₀
  have hY' : IsAlgebraicSpace B S hS (pullback t y) :=
    isAlgebraicSpace_pullback B S hS t y hB' hY₀ hB₀
  -- the base change of the chart square
  have hσ := (IsPullback.of_hasPullback r q).map yoneda
  have hbase : yoneda.map r ≫ b ≫ y = a ≫ x := by
    rw [← Category.assoc, hcomm, Category.assoc, hf₀]
  have hp' : IsPullback (yoneda.map (pullback.snd r q) ≫ p) (yoneda.map (pullback.fst r q))
      t (a ≫ x) := by
    simpa only [hbase] using (hσ.paste_vert hp.flip).flip
  let a' : yoneda.obj (pullback r q) ⟶ pullback t x :=
    pullback.lift (yoneda.map (pullback.snd r q) ≫ p) (yoneda.map (pullback.fst r q) ≫ a) hp'.w
  let b' : yoneda.obj W ⟶ pullback t y := pullback.lift p (yoneda.map q ≫ b) hp.w
  have sa : IsPullback (yoneda.map (pullback.fst r q)) a' a (pullback.snd t x) := by
    refine IsPullback.of_bot (t := (IsPullback.of_hasPullback t x).flip) ?_
      (pullback.lift_snd _ _ _).symm
    simpa only [a', pullback.lift_fst] using hp'.flip
  have sb : IsPullback (yoneda.map q) b' b (pullback.snd t y) := by
    refine IsPullback.of_bot (t := (IsPullback.of_hasPullback t y).flip) ?_
      (pullback.lift_snd _ _ _).symm
    simpa only [b', pullback.lift_fst] using hp.flip
  have comm : yoneda.map (pullback.snd r q) ≫ b' = a' ≫ f' := by
    refine pullback.hom_ext ?_ ?_
    · simp only [a', b', Category.assoc, hf₁, pullback.lift_fst]
    · simp only [a', b', Category.assoc, hf₂, pullback.lift_snd, pullback.lift_snd_assoc]
      rw [← Category.assoc, ← Functor.map_comp, ← pullback.condition, Functor.map_comp,
        Category.assoc, hcomm]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact (isEtale_iff_holdsOnEveryEtaleChart B S hS hX' hY' f').mp h _ _ a' b'
      (pullback.snd r q) (MorphismProperty.of_isPullback sa haE)
      (MorphismProperty.of_isPullback sb hbE) comm
  · exact (isEtale_iff_exists_etale_chart_square B S hS hX' hY' f').mpr
      ⟨_, _, a', b', pullback.snd r q, comm.symm, MorphismProperty.of_isPullback sa haS,
        MorphismProperty.of_isPullback sa haE, MorphismProperty.of_isPullback sb hbE, h⟩

namespace AffineChartSystem

variable {B S hS} {I : Type u} [Category.{u} I] {i₀ : I}
  {D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U₀ : BigAffineFppf B S hS}
  {f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀}

/-- The morphisms of the site underlying the projections of a chart system to `U₀` are
compatible with its transition morphisms. -/
private theorem siteDiagram_map_comp_preimage_baseMap (C : AffineChartSystem B S hS i₀ D U₀ f₀)
    {j k : Over i₀} (g : j ⟶ k) :
    C.siteDiagram.map g ≫ yoneda.preimage (C.baseMap k) = yoneda.preimage (C.baseMap j) := by
  have hnat : yoneda.map (C.siteDiagram.map g) ≫ C.iso.hom.app k =
      C.iso.hom.app j ≫ (stageBaseChangeDiagram B S hS i₀ D U₀ f₀).map g :=
    C.iso.hom.naturality g
  apply yoneda.map_injective
  rw [yoneda.map_comp, Functor.map_preimage, Functor.map_preimage]
  simp only [AffineChartSystem.baseMap]
  rw [← Category.assoc, hnat, Category.assoc, stageBaseChangeDiagram_map_comp_snd]

/-- The morphism of the site underlying the projection of the limit of a chart system to `U₀`
factors through every chart. -/
private theorem LimitBridge.π_app_comp_preimage_baseMap {C : AffineChartSystem B S hS i₀ D U₀ f₀}
    (L : C.LimitBridge) (j : Over i₀) :
    L.cone.π.app j ≫ yoneda.preimage (C.baseMap j) = yoneda.preimage L.toBase := by
  apply yoneda.map_injective
  rw [yoneda.map_comp, Functor.map_preimage, Functor.map_preimage]
  exact L.baseMap_comp j

/-- **Stacks 07RP on a chart system.** If `r : V ⟶ U₀` is locally of finite presentation and its
base change to the limit of a chart system is étale, then so is its base change to some chart. -/
private theorem LimitBridge.exists_etale_map_pullback_snd [IsCofiltered (Over i₀)]
    {C : AffineChartSystem B S hS i₀ D U₀ f₀} (L : C.LimitBridge) {V : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    (r : V ⟶ (BigAffineFppf.inclusion B S hS).obj U₀)
    (hr : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map r))
    (h : AlgebraicGeometry.Etale
      ((BigFppfOver.toScheme B S hS).map (pullback.snd r (yoneda.preimage L.toBase)))) :
    ∃ j : Over i₀, AlgebraicGeometry.Etale
      ((BigFppfOver.toScheme B S hS).map (pullback.snd r (yoneda.preimage (C.baseMap j)))) := by
  let j₀ : Over i₀ := Over.mk (𝟙 i₀)
  let T := BigFppfOver.toScheme B S hS
  let fbase := pullback.snd (T.map r) (T.map (yoneda.preimage (C.baseMap j₀)))
  let X₁ : Over (C.schemeDiagram.obj j₀) := Over.mk fbase
  let Y₁ : Over (C.schemeDiagram.obj j₀) := Over.mk (𝟙 (C.schemeDiagram.obj j₀))
  let φ₁ : X₁ ⟶ Y₁ := Over.homMk fbase (Category.comp_id _)
  have : ∀ {j k : Over i₀} (g : j ⟶ k),
      _root_.AlgebraicGeometry.IsAffineHom (C.schemeDiagram.map g) :=
    fun g => C.isAffineHom_map g
  have := C.isAffine_obj j₀
  have hj₀aff : IsAffine (T.obj (C.siteDiagram.obj j₀)) := C.isAffine_obj j₀
  have hUaff : IsAffine (T.obj ((BigAffineFppf.inclusion B S hS).obj U₀)) := U₀.property
  have hfstAff : _root_.AlgebraicGeometry.IsAffineHom
      (pullback.fst (T.map r) (T.map (yoneda.preimage (C.baseMap j₀)))) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _).flip
      (isAffineHom_of_isAffine (T.map (yoneda.preimage (C.baseMap j₀))))
  have : IsAffine X₁.left :=
    isAffine_of_isAffineHom (pullback.fst (T.map r) (T.map (yoneda.preimage (C.baseMap j₀))))
  have hY₁aff : IsAffine Y₁.left := C.isAffine_obj j₀
  have : LocallyOfFinitePresentation φ₁.left :=
    MorphismProperty.of_isPullback
      (IsPullback.of_hasPullback (T.map r) (T.map (yoneda.preimage (C.baseMap j₀)))) hr
  have : MorphismProperty.RespectsIso
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  let cL := T.mapCone L.cone
  have hqL : cL.π.app j₀ ≫ T.map (yoneda.preimage (C.baseMap j₀)) =
      T.map (yoneda.preimage L.toBase) := by
    change T.map (L.cone.π.app j₀) ≫ _ = _
    rw [← Functor.map_comp, L.π_app_comp_preimage_baseMap j₀]
  have : AlgebraicGeometry.Etale ((Over.pullback (cL.π.app j₀)).map φ₁).left := by
    refine (prop_overPullback_map_left_iff_pullback_snd _ fbase (cL.π.app j₀)).mpr ?_
    exact (prop_iteratedPullback_snd_iff T _ r (yoneda.preimage (C.baseMap j₀))
      (yoneda.preimage L.toBase) (cL.π.app j₀) hqL).mpr h
  obtain ⟨jj, hjj⟩ := exists_etale_pullback_of_isLimit C.schemeDiagram cL L.schemeIsLimit j₀
    X₁ Y₁ φ₁
  have hqj : C.schemeDiagram.map jj.hom ≫ T.map (yoneda.preimage (C.baseMap j₀)) =
      T.map (yoneda.preimage (C.baseMap jj.left)) := by
    change T.map (C.siteDiagram.map jj.hom) ≫ _ = _
    rw [← Functor.map_comp, C.siteDiagram_map_comp_preimage_baseMap jj.hom]
  refine ⟨jj.left, (prop_iteratedPullback_snd_iff T _ r (yoneda.preimage (C.baseMap j₀))
    (yoneda.preimage (C.baseMap jj.left)) (C.schemeDiagram.map jj.hom) hqj).mp ?_⟩
  exact (prop_overPullback_map_left_iff_pullback_snd _ fbase (C.schemeDiagram.map jj.hom)).mp hjj

end AffineChartSystem

/-- **Stacks 07SL, for an inverse system bounded by the cutoff.** Let `D` be a directed inverse
system of algebraic spaces over `S` with affine transition morphisms, bounded by the cutoff
(`AlgebraicGeometry.Space.IsCutoffBoundedSystem`), let `i₀` be a stage, and let `f₀ : X₀ ⟶ Y₀`
be a morphism of algebraic spaces over `D i₀`, locally of finite presentation, with `X₀` and `Y₀`
quasi-compact and `Y₀` quasi-separated. If the base change of `f₀` to `lim D` is étale, then so is
its base change to some stage `D i` with `i₀ ≤ i`.

This is `AlgebraicGeometry.Space.MorphismDescentSystem.exists_isEtale_mapAt` with the bound by
the cofinality of the cutoff on the index set traded for
`AlgebraicGeometry.Space.IsCutoffBoundedSystem`; the limit of the affine charts of the stages is
`AlgebraicGeometry.Space.AffineChartSystem.limitBridgeOfBaseChangeSizeBounded`. -/
theorem exists_isEtale_pullbackMap_of_isCutoffBoundedSystem {I : Type u} [Preorder I]
    [IsDirected I (· ≤ ·)] (D : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hD : IsCutoffBoundedSystem B S hS D)
    (hDalg : ∀ i : I, IsAlgebraicSpace B S hS (D.obj (op i)))
    (hDaff : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom B S hS (D.map a))
    (i₀ : I) {X₀ Y₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (x : X₀ ⟶ D.obj (op i₀))
    (y : Y₀ ⟶ D.obj (op i₀)) (f₀ : X₀ ⟶ Y₀) (hf₀ : f₀ ≫ y = x)
    (hX₀ : IsAlgebraicSpace B S hS X₀) (hY₀ : IsAlgebraicSpace B S hS Y₀)
    (hX₀qc : IsQuasiCompactSpace B S hS X₀) (hY₀qc : IsQuasiCompactSpace B S hS Y₀)
    (hY₀qs : IsAbsolutelyQuasiSeparated B S hS hZ Y₀)
    (fp : IsLocallyOfFinitePresentation B S hS f₀)
    (etale : IsEtale B S hS (pullback.map (limit.π D (op i₀)) x (limit.π D (op i₀)) y (𝟙 _) f₀
      (𝟙 _) (by simp) (by simp [hf₀]))) :
    ∃ (i : I) (hi : i₀ ≤ i), IsEtale B S hS (pullback.map (D.map (homOfLE hi).op) x
      (D.map (homOfLE hi).op) y (𝟙 _) f₀ (𝟙 _) (by simp) (by simp [hf₀])) := by
  classical
  obtain ⟨hSize, ⟨ν, hν, hHomSize⟩, hB⟩ := hD
  have _ : Nonempty I := ⟨i₀⟩
  have _ : IsCofiltered Iᵒᵖ := inferInstance
  have hlim : IsAlgebraicSpace B S hS (limit D) :=
    isAlgebraicSpace_limit_of_baseChangeSizeBounded B S hS D hSize hν hHomSize
      (fun i => hDalg i.unop) hDaff hB
  obtain ⟨U, V, b, a, r, hU, hV, hbE, haE, haS, hcomm, hrfp⟩ :=
    exists_affine_etale_chart_square B S hS hZ f₀ hX₀ hY₀ hX₀qc hY₀qc hY₀qs fp
  /- The system of affine charts of the stages over `i₀` cut out by `b ≫ y`, and its limit. -/
  let C := affineChartSystem B S hS (op i₀) D ⟨U, hU⟩ (b ≫ y) hDaff
  let L := C.limitBridgeOfBaseChangeSizeBounded hSize hν hHomSize hB
  have hpL : IsPullback L.toLimit (yoneda.map (yoneda.preimage L.toBase)) (limit.π D (op i₀))
      (b ≫ y) := by
    rw [Functor.map_preimage]
    exact L.isPullback
  /- The descent along the limit of affine schemes, Stacks 07RP. -/
  have key := isEtale_pullbackMap_iff_etale_pullback_snd B S hS x y f₀ hf₀ hX₀ hY₀ (hDalg i₀) b a
    r haE haS hbE hcomm
  obtain ⟨j, hj⟩ := L.exists_etale_map_pullback_snd r hrfp ((key _ hlim _ L.toLimit _ hpL).mp etale)
  /- Back to the stage `j`. -/
  have hmap : D.map (homOfLE (leOfHom j.hom.unop)).op = D.map j.hom :=
    congrArg D.map (Subsingleton.elim _ _)
  have hp : IsPullback (C.stageMap j) (yoneda.map (yoneda.preimage (C.baseMap j)))
      (D.map (homOfLE (leOfHom j.hom.unop)).op) (b ≫ y) := by
    rw [hmap, Functor.map_preimage]
    exact C.isPullback j
  exact ⟨j.left.unop, leOfHom j.hom.unop, (key _ (hDalg _) _ _ _ hp).mpr hj⟩

end AlgebraicGeometry.Space

end
