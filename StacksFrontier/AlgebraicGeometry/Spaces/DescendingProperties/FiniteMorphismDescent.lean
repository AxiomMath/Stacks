module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Finite
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHomTfaeComplete
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.AffineMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.ClosedImmersionMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.ProperMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.Separated
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SeparatedMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineProper
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteMorphismSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralFiniteEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IntegralFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteSeparatedRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionQuasiFinite

/-!
# Descending finiteness along a limit of algebraic spaces

Work in the situation of Stacks 084W, formalized as
`AlgebraicGeometry.Space.MorphismDescentSituation`: a directed inverse system of algebraic spaces
`B = lim B_i` with affine transition morphisms, a morphism `f₀ : X₀ ⟶ Y₀` of quasi-compact
quasi-separated algebraic spaces over `B₀`, and its base changes `f_i : X_i ⟶ Y_i` and
`f : X ⟶ Y` to `B_i` and to `B`. **Stacks 084Z is proved here**
(`exists_isFinite_mapAt_of_siteContainsBaseChangeLimits`): if `f` is finite and `f₀` is locally
of finite type, then `f_i` is finite for some `i ≥ 0`. As everywhere in the chapter, this is
under the standing convention of its Section 70.2 (tag 07SD) that every ring considered has its
spectrum in the big fppf site, which for the system of bases is
`AlgebraicGeometry.Space.SiteContainsBaseChangeLimits`.

## Main results

All names below are in the namespace `AlgebraicGeometry.Space.MorphismDescentSituation`.

* `exists_isLocallyQuasiFinite_mapAt`: local quasi-finiteness descends from the limit to a stage,
  through the relative-dimension bound of Stacks 0D4K.
* `exists_isSeparated_isLocallyQuasiFinite_mapAt`: if `f` is finite then some stage is separated
  and locally quasi-finite at once.
* `relativelyRepresentable_mapAt_of_isSeparated_of_isLocallyQuasiFinite`: such a stage is
  representable by schemes.
* `TargetChart.isFinite_mapAt_of_isFinite_pullback_stageChart`: the étale-descent step,
  Stacks 03ZQ for finite morphisms.
* `TargetChart.exists_isFinite_mapAt_of_isSeparated_of_relativelyRepresentable`: the scheme-level
  step, Stacks 01ZO on the affine charts, from a stage that is separated and representable by
  schemes; `TargetChart.exists_isFinite_mapAt_of_isAffineHom` is its case of an affine stage.
* `exists_isFinite_mapAt_of_siteContainsBaseChangeLimits`: **Stacks 084Z.**
* `exists_isFinite_mapAt`: the same for a system small for the site, which implies the
  convention.

## Implementation notes

*The route taken.* It is the source's. A finite morphism is affine (Stacks 04NZ), so Stacks
084Y, whose proof is where Stacks 07SQ makes some `V_k ×_{Y_k} X_k` affine, makes some `f_k`
affine. Then `f_k` is separated and representable by schemes, so `W_k = V_k ×_{Y_k} X_k` is a
quasi-compact quasi-separated scheme over the affine `V_k`, the charts of the later stages are a
cofiltered system of affine schemes with limit `V`, and `W_k ×_{V_k} V = V ×_Y X` is finite over
`V`. Stacks 01ZO then makes `W_l ⟶ V_l` finite at some later stage `l`, and Stacks 03ZQ descends
that through the surjective étale chart of `Y_l`.

*Quasi-separatedness of the chart of the source.* Stacks 01ZO asks for it, and here it comes
from separatedness: `W_k ⟶ V_k` is a base change of the separated `f_k`, so it is a separated —
hence quasi-separated — morphism of schemes with affine target.

*The affine chart apparatus is not rebuilt.* The chart `V₀ ⟶ Y₀` of the target, the induced
charts `V_i ⟶ Y_i` and `V ⟶ Y`, the cofiltered system of affine schemes they form and its
limit are `AlgebraicGeometry.Space.MorphismDescentSituation.TargetChart` and its fields, built for
Stacks 0850 in
`StacksFrontier/AlgebraicGeometry/Spaces/DescendingProperties/ClosedImmersionMorphismDescent.lean`.

*The convention.* It is consumed twice: by Stacks 084Y, and by Stacks 07SF for the system of
charts `V_i`, whose limit `V` is formed in the site because the colimit of the rings of the
`V_i` has its spectrum there. It cannot be dropped: for a system of spectra of fields `K_i`
whose union `K` is larger than the size cutoff of the site, the limit of the system in
presheaves on the site is empty, so every base change to the limit is finite while no stage
need be (take `f₀` the structure morphism of the projective line).

*Separatedness and local quasi-finiteness.* The first results of the file descend these two
properties of a finite `f` to a stage for a system small for the site, which is the other
standard way to make `V_k ×_{Y_k} X_k` a scheme (Stacks 0418).

## References

* [Stacks Project, Tag 084Z](https://stacks.math.columbia.edu/tag/084Z)
* [Stacks Project, Tag 084W](https://stacks.math.columbia.edu/tag/084W)
* [Stacks Project, Tag 07SD](https://stacks.math.columbia.edu/tag/07SD)
* [Stacks Project, Tag 084Y](https://stacks.math.columbia.edu/tag/084Y)
* [Stacks Project, Tag 04NZ](https://stacks.math.columbia.edu/tag/04NZ)
* [Stacks Project, Tag 0851](https://stacks.math.columbia.edu/tag/0851)
* [Stacks Project, Tag 0D4K](https://stacks.math.columbia.edu/tag/0D4K)
* [Stacks Project, Tag 0418](https://stacks.math.columbia.edu/tag/0418)
* [Stacks Project, Tag 01ZO](https://stacks.math.columbia.edu/tag/01ZO)
* [Stacks Project, Tag 03ZQ](https://stacks.math.columbia.edu/tag/03ZQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] MorphismProperty.relative_isStableUnderBaseChange

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]

namespace MorphismDescentSituation

variable (D : MorphismDescentSituation B S hS hZ I)

/-! ### Separatedness and local quasi-finiteness at a stage -/

/-- **Local quasi-finiteness descends to a stage.** A morphism locally of finite type is
locally quasi-finite exactly when its relative dimension vanishes at every point of its source
(Stacks 04NV), so this is Stacks 0D4K for `d = 0`. -/
theorem exists_isLocallyQuasiFinite_mapAt (hb : IsSiteSmall B S hS D.base)
    (hf : IsLocallyQuasiFinite B S hS D.mapLimit)
    (hf₀ : IsLocallyOfFiniteType B S hS D.map₀) :
    ∃ (i : I) (hi : D.initial ≤ i), IsLocallyQuasiFinite B S hS (D.mapAt i hi) := by
  have hdim : HasRelativeDimensionLE 0 B S hS D.mapLimit := fun x =>
    ⟨0, le_rfl, by
      simpa using (isLocallyQuasiFinite_iff_forall_hasRelativeDimensionAt_zero B S hS
        D.mapLimit (D.isLocallyOfFiniteType_mapLimit hf₀)).1 hf x⟩
  obtain ⟨i, hi, hdimi⟩ := D.exists_hasRelativeDimensionLE_mapAt hb 0 hdim hf₀
  refine ⟨i, hi, (isLocallyQuasiFinite_iff_forall_hasRelativeDimensionAt_zero B S hS
    (D.mapAt i hi) (D.isLocallyOfFiniteType_mapAt hf₀ i hi)).2 fun x => ?_⟩
  obtain ⟨e, he, h⟩ := hdimi x
  rw [Nat.le_zero.mp he] at h
  simpa using h

/-- **A stage at which `f_i` is both separated and locally quasi-finite.** A finite morphism is
separated and locally quasi-finite, and each of those descends to a stage — the first by
Stacks 0851, the second by Stacks 0D4K with `d = 0`. Both then hold at any later stage, being
stable under the base change exhibiting `f_k` over `f_i`. -/
theorem exists_isSeparated_isLocallyQuasiFinite_mapAt (hb : IsSiteSmall B S hS D.base)
    (hf : IsFinite B S hS D.mapLimit)
    (hf₀ : IsLocallyOfFiniteType B S hS D.map₀) :
    ∃ (i : I) (hi : D.initial ≤ i),
      IsSeparated B S hS (D.mapAt i hi) ∧ IsLocallyQuasiFinite B S hS (D.mapAt i hi) := by
  obtain ⟨i₁, hi₁, hsep₁⟩ := D.exists_isSeparated_mapAt_of_isSeparated_mapLimit hb
    (isSeparated_of_isFinite B S hS D.mapLimit D.sourceLimit_isAlgebraicSpace
      D.targetLimit_isAlgebraicSpace hf)
  obtain ⟨i₂, hi₂, hlqf₂⟩ := D.exists_isLocallyQuasiFinite_mapAt hb
    (isQuasiFinite_of_isFinite B S hS D.mapLimit D.sourceLimit_isAlgebraicSpace
      D.targetLimit_isAlgebraicSpace hf).1 hf₀
  obtain ⟨k, hk₁, hk₂⟩ := directed_of (· ≤ ·) i₁ i₂
  obtain ⟨α, β, hpb⟩ := D.exists_isPullback_mapAt_of_le hi₂ hk₂
  exact ⟨k, hi₁.trans hk₁, D.isSeparated_mapAt_of_le hi₁ hk₁ hsep₁,
    IsLocallyQuasiFinite.of_isPullback B S hS hpb.flip (D.sourceAt_isAlgebraicSpace i₂ hi₂)
      (D.targetAt_isAlgebraicSpace i₂ hi₂) hlqf₂⟩

/-- **A separated locally quasi-finite base change of `f₀` is representable by schemes.** This
is Stacks 0418. -/
theorem relativelyRepresentable_mapAt_of_isSeparated_of_isLocallyQuasiFinite {i : I}
    (hi : D.initial ≤ i) (hsep : IsSeparated B S hS (D.mapAt i hi))
    (hlqf : IsLocallyQuasiFinite B S hS (D.mapAt i hi)) :
    yoneda.relativelyRepresentable (D.mapAt i hi) :=
  relativelyRepresentable_of_isLocallyQuasiFinite_isSeparated B S hS (D.mapAt i hi)
    (D.sourceAt_isAlgebraicSpace i hi) (D.targetAt_isAlgebraicSpace i hi) hlqf hsep

namespace TargetChart

variable {D} (T : TargetChart D)

/-- **The étale-descent step of Stacks 084Z.** If the base change of `f_i` along the chart of
the target at a stage is finite, then `f_i` is finite. This is Stacks 03ZQ for finite
morphisms, conditions (3) implies (2). -/
theorem isFinite_mapAt_of_isFinite_pullback_stageChart (j : Over (op D.initial))
    (hV : IsFinite B S hS
      (pullback.snd (D.mapAt j.left.unop (leOfHom j.hom.unop)) (T.stageChart j))) :
    IsFinite B S hS (D.mapAt j.left.unop (leOfHom j.hom.unop)) :=
  (isFinite_iff_etaleLocal B S hS (D.mapAt j.left.unop (leOfHom j.hom.unop))
      (D.sourceAt_isAlgebraicSpace j.left.unop (leOfHom j.hom.unop))
      (D.targetAt_isAlgebraicSpace j.left.unop (leOfHom j.hom.unop))).2
    ⟨T.system.siteDiagram.obj j, T.stageChart j, T.stageChart_surjective j,
      T.stageChart_etale j, hV⟩

include T in
/-- **The descent step at one stage.** If the base change of `f₀` to the stage indexed by `k`
is separated and representable by schemes, and the base change of `f₀` to the limit is finite,
then the base change of `f₀` to some stage is finite.

The base change of `f_k` along the affine chart `V_k` of the target is a morphism of schemes
`W_k ⟶ V_k`, locally of finite type, from a quasi-compact quasi-separated scheme to an affine
one, and `W_k ×_{V_k} V = V ×_Y X` is finite over `V`. Stacks 01ZO makes `W_l ⟶ V_l` finite at
a later stage `l`, and the finiteness then descends through the surjective étale chart of
`Y_l`. -/
theorem exists_isFinite_mapAt_of_isSeparated_of_relativelyRepresentable
    (hf : IsFinite B S hS D.mapLimit)
    (hf₀ : IsLocallyOfFiniteType B S hS D.map₀) (k : Over (op D.initial))
    (hsep : IsSeparated B S hS (D.mapAt k.left.unop (leOfHom k.hom.unop)))
    (hrep : yoneda.relativelyRepresentable (D.mapAt k.left.unop (leOfHom k.hom.unop))) :
    ∃ (i : I) (hi : D.initial ≤ i), IsFinite B S hS (D.mapAt i hi) := by
  classical
  have : HasPullbacks (BigFppfOver B S hS) := inferInstance
  have : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    comp_preservesLimitsOfShape _ _
  have _hri : MorphismProperty.RespectsIso
      (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  -- `W_k`, the base change of `f_k` along the chart of the target at the stage `k`
  have hsq : IsPullback (hrep.fst (T.stageChart k)) (yoneda.map (hrep.snd (T.stageChart k)))
      (D.mapAt k.left.unop (leOfHom k.hom.unop)) (T.stageChart k) :=
    hrep.isPullback (T.stageChart k)
  have hetaleW : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (hrep.fst (T.stageChart k)) :=
    MorphismProperty.of_isPullback hsq.flip (T.stageChart_etale k)
  have hlftW : LocallyOfFiniteType
      ((BigFppfOver.toScheme B S hS).map (hrep.snd (T.stageChart k))) :=
    D.isLocallyOfFiniteType_mapAt hf₀ k.left.unop (leOfHom k.hom.unop) _ _
      (hrep.fst (T.stageChart k)) (T.stageChart k) _ hetaleW (T.stageChart_etale k) hsq.w.symm
  -- `W_k` is quasi-compact, and quasi-separated because `W_k ⟶ V_k` is separated
  have hqcW : IsQuasiCompactSpace B S hS (yoneda.obj (hrep.pullback (T.stageChart k))) :=
    isQuasiCompactSpace_of_iso B S hS hsq.isoPullback.symm
      (isQuasiCompactSpace_pullback B S hS hZ _ (T.stageChart k)
        (D.sourceAt_isAlgebraicSpace _ _) (D.targetAt_isAlgebraicSpace _ _)
        (D.isQuasiCompactSpace_sourceAt _ _)
        (isQuasiCompactSpace_yoneda_of_isAffine B S hS _ (T.system.isAffine_obj k))
        (D.isAbsolutelyQuasiSeparated_targetAt _ _))
  have hVkaff : IsAffine ((BigFppfOver.toScheme B S hS).obj (T.system.siteDiagram.obj k)) :=
    T.system.isAffine_obj k
  have hVkaff' : IsAffine (T.system.schemeDiagram.obj k) := T.system.isAffine_obj k
  have hsepW : _root_.AlgebraicGeometry.IsSeparated
      ((BigFppfOver.toScheme B S hS).map (hrep.snd (T.stageChart k))) :=
    ((isSeparated_iff_presheaf B S hS (D.mapAt k.left.unop (leOfHom k.hom.unop))
      (D.sourceAt_isAlgebraicSpace _ _) (D.targetAt_isAlgebraicSpace _ _) hrep).1
        hsep).property (T.stageChart k) (hrep.fst (T.stageChart k)) _ hsq
  -- base changes of `W_k ⟶ V_k` along a map `V' ⟶ V_k` are base changes of `f_i` along `V' ⟶ Y_i`
  have hbc : ∀ {Z} (t : Z ⟶ T.system.siteDiagram.obj k) {Y' X'} (c : yoneda.obj Z ⟶ Y')
      (p : Y' ⟶ _) (f' : X' ⟶ Y') (hcomm : yoneda.map t ≫ T.stageChart k = c ≫ p)
      (hpb : ∃ α, IsPullback α f' (D.mapAt k.left.unop (leOfHom k.hom.unop)) p),
      ∃ φ, IsPullback φ (yoneda.map (pullback.snd (hrep.snd (T.stageChart k)) t)) f' c := by
    intro Z t Y' X' c p f' hcomm ⟨α, hα⟩
    have houter := ((IsPullback.of_hasPullback (hrep.snd (T.stageChart k)) t).map
      yoneda).paste_horiz hsq
    rw [hcomm] at houter
    exact ⟨_, IsPullback.of_right' houter hα⟩
  -- finiteness of `W_k ×_{V_k} V' ⟶ V'` in the site or in `Scheme`
  have hiff := fun {Z} (t : Z ⟶ T.system.siteDiagram.obj k) =>
    prop_snd_iff_of_isPullback (@_root_.AlgebraicGeometry.IsFinite.{u})
      ((IsPullback.of_hasPullback (hrep.snd (T.stageChart k)) t).map
        (BigFppfOver.toScheme B S hS))
      (IsPullback.of_hasPullback ((BigFppfOver.toScheme B S hS).map (hrep.snd (T.stageChart k)))
        ((BigFppfOver.toScheme B S hS).map t))
  -- at the limit `W_k ×_{V_k} V = V ×_Y X` is finite over the affine scheme `V`
  have hlimFin : _root_.AlgebraicGeometry.IsFinite
      (pullback.snd ((BigFppfOver.toScheme B S hS).map (hrep.snd (T.stageChart k)))
        ((BigFppfOver.toScheme B S hS).map (T.bridge.cone.π.app k))) :=
    (hiff _).mp <| ((isFinite_iff_representable B S hS D.mapLimit D.sourceLimit_isAlgebraicSpace
      D.targetLimit_isAlgebraicSpace).1 hf).2.property T.limitChart _ _
        (hbc _ T.limitChart _ _ (T.yoneda_map_bridge_π_comp_stageChart k)
          (D.exists_isPullback_mapLimit_targetLimitProj k.left.unop
            (leOfHom k.hom.unop))).choose_spec
  -- Stacks 01ZO for the cofiltered system of affine charts of the stages
  have : Nonempty I := ⟨D.initial⟩
  have : IsDirectedOrder I := inferInstance
  have : IsFiltered I := inferInstance
  have : IsCofiltered Iᵒᵖ := inferInstance
  have : IsCofiltered (Over (op D.initial)) := inferInstance
  have hEhom : ∀ {a b : Over (op D.initial)} (g : a ⟶ b),
      _root_.AlgebraicGeometry.IsAffineHom (T.system.schemeDiagram.map g) :=
    fun g ↦ T.system.isAffineHom_map g
  have : IsAffine (Over.mk (𝟙 (T.system.schemeDiagram.obj k))).left := hVkaff'
  have : CompactSpace
      (Over.mk ((BigFppfOver.toScheme B S hS).map (hrep.snd (T.stageChart k))) :
        Over (T.system.schemeDiagram.obj k)).left :=
    compactSpace_of_isQuasiCompactSpace_yoneda_obj B S hS hqcW
  have : QuasiSeparatedSpace
      (Over.mk ((BigFppfOver.toScheme B S hS).map (hrep.snd (T.stageChart k))) :
        Over (T.system.schemeDiagram.obj k)).left :=
    quasiSeparatedSpace_of_quasiSeparated
      ((BigFppfOver.toScheme B S hS).map (hrep.snd (T.stageChart k)))
  have : LocallyOfFiniteType (Over.homMk
      ((BigFppfOver.toScheme B S hS).map (hrep.snd (T.stageChart k))) (Category.comp_id _) :
      (Over.mk ((BigFppfOver.toScheme B S hS).map (hrep.snd (T.stageChart k))) :
        Over (T.system.schemeDiagram.obj k)) ⟶ Over.mk (𝟙 _)).left := hlftW
  have : _root_.AlgebraicGeometry.IsFinite ((Over.pullback
      (((BigFppfOver.toScheme B S hS).mapCone T.bridge.cone).π.app k)).map
      (Over.homMk ((BigFppfOver.toScheme B S hS).map (hrep.snd (T.stageChart k)))
        (Category.comp_id _) :
        (Over.mk ((BigFppfOver.toScheme B S hS).map (hrep.snd (T.stageChart k))) :
          Over (T.system.schemeDiagram.obj k)) ⟶ Over.mk (𝟙 _))).left :=
    (prop_overPullback_map_left_iff_pullback_snd
      (@_root_.AlgebraicGeometry.IsFinite.{u}) _ _).mpr hlimFin
  obtain ⟨l, g, hres⟩ := _root_.AlgebraicGeometry.exists_isFinite_baseChange_of_isLimit
    T.system.schemeDiagram _ T.bridge.schemeIsLimit k
    (Over.mk ((BigFppfOver.toScheme B S hS).map (hrep.snd (T.stageChart k))))
    (Over.mk (𝟙 (T.system.schemeDiagram.obj k)))
    (Over.homMk ((BigFppfOver.toScheme B S hS).map (hrep.snd (T.stageChart k)))
      (Category.comp_id _))
  -- transport the finiteness of schemes back to the algebraic spaces
  have hstage : _root_.AlgebraicGeometry.IsFinite (pullback.snd
      ((BigFppfOver.toScheme B S hS).map (hrep.snd (T.stageChart k)))
      (T.system.schemeDiagram.map g)) :=
    (prop_overPullback_map_left_iff_pullback_snd
      (@_root_.AlgebraicGeometry.IsFinite.{u}) _ _).mp hres
  have hpre : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map
        (pullback.snd (hrep.snd (T.stageChart k)) (T.system.siteDiagram.map g))) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ _).2 ((hiff _).mpr hstage)
  obtain ⟨_, hchart⟩ := hbc _ _ _ _ (T.yoneda_map_siteDiagram_map_comp_stageChart g)
    (D.exists_isPullback_mapAt_targetAtProj (leOfHom k.hom.unop) (leOfHom g.left.unop))
  have hchart := (prop_snd_iff_of_isPullback _ hchart (IsPullback.of_hasPullback _ _)).mp hpre
  refine ⟨l.left.unop, leOfHom l.hom.unop,
    T.isFinite_mapAt_of_isFinite_pullback_stageChart l ?_⟩
  exact (isFinite_iff_representable B S hS _
    (isAlgebraicSpace_pullback B S hS (D.mapAt l.left.unop (leOfHom l.hom.unop))
      (T.stageChart l) (D.sourceAt_isAlgebraicSpace _ _)
      (isAlgebraicSpace_yoneda B S hS _) (D.targetAt_isAlgebraicSpace _ _))
    (isAlgebraicSpace_yoneda B S hS _)).2 ⟨hchart.rep, hchart⟩

include T in
/-- **The descent step at a separated, locally quasi-finite stage.** Such a stage is
representable by schemes (Stacks 0418), so
`exists_isFinite_mapAt_of_isSeparated_of_relativelyRepresentable` applies. -/
theorem exists_isFinite_mapAt_of_isSeparated_of_isLocallyQuasiFinite
    (hf : IsFinite B S hS D.mapLimit)
    (hf₀ : IsLocallyOfFiniteType B S hS D.map₀) (k : Over (op D.initial))
    (hsep : IsSeparated B S hS (D.mapAt k.left.unop (leOfHom k.hom.unop)))
    (hlqf : IsLocallyQuasiFinite B S hS (D.mapAt k.left.unop (leOfHom k.hom.unop))) :
    ∃ (i : I) (hi : D.initial ≤ i), IsFinite B S hS (D.mapAt i hi) :=
  T.exists_isFinite_mapAt_of_isSeparated_of_relativelyRepresentable hf hf₀ k hsep
    (D.relativelyRepresentable_mapAt_of_isSeparated_of_isLocallyQuasiFinite
      (leOfHom k.hom.unop) hsep hlqf)

include T in
/-- **The descent step at an affine stage.** An affine base change of `f₀` is separated and
representable by schemes, so
`exists_isFinite_mapAt_of_isSeparated_of_relativelyRepresentable` applies. -/
theorem exists_isFinite_mapAt_of_isAffineHom
    (hf : IsFinite B S hS D.mapLimit)
    (hf₀ : IsLocallyOfFiniteType B S hS D.map₀) (k : Over (op D.initial))
    (haff : IsAffineHom B S hS (D.mapAt k.left.unop (leOfHom k.hom.unop))) :
    ∃ (i : I) (hi : D.initial ≤ i), IsFinite B S hS (D.mapAt i hi) :=
  T.exists_isFinite_mapAt_of_isSeparated_of_relativelyRepresentable hf hf₀ k
    (isSeparated_of_isAffineHom B S hS _ (D.sourceAt_isAlgebraicSpace _ _)
      (D.targetAt_isAlgebraicSpace _ _) haff)
    (presheaf_isAffineHom_of_isAffineHom_of_isAlgebraicSpace B S hS
      (D.sourceAt_isAlgebraicSpace _ _) (D.targetAt_isAlgebraicSpace _ _) haff).1

end TargetChart

/-- **Stacks 084Z.** Notation and assumptions as in Situation 70.6.1 (tag 084W), carried by
`AlgebraicGeometry.Space.MorphismDescentSituation`, in the chapter's setting of Section 70.2
(tag 07SD): if the base change `f` of `f₀` to the limit `B` is finite and `f₀` is locally of
finite type, then the base change `f_i` of `f₀` to some stage `B_i` is finite.

The hypothesis `hconv` is the chapter's standing convention that every ring considered has its
spectrum in the big fppf site, read for the system of bases; the situation itself asks nothing
of the index. Without the convention Stacks 07SQ, used below, is false:
`AlgebraicGeometry.Space.DescentSituation.not_forall_exists_isAffineSpace_system_obj`.

The proof is the source's. A finite morphism is affine (Stacks 04NZ), so by Stacks 084Y
(`exists_isAffineHom_mapAt_of_isAffineHom_mapLimit_of_siteContainsBaseChangeLimits`, which is
where Stacks 07SQ enters) some `f_k` is affine, so that `V_k ×_{Y_k} X_k` is affine over the
affine chart `V_k` of the target. Stacks 01ZO, applied to the system of affine charts of the
later stages, makes `V_l ×_{Y_l} X_l ⟶ V_l` finite at some stage `l`, and Stacks 03ZQ descends
this through the surjective étale chart `V_l ⟶ Y_l` to `f_l`. -/
theorem exists_isFinite_mapAt_of_siteContainsBaseChangeLimits
    (hconv : SiteContainsBaseChangeLimits B S hS D.base)
    (hf : IsFinite B S hS D.mapLimit)
    (hf₀ : IsLocallyOfFiniteType B S hS D.map₀) :
    ∃ (i : I) (hi : D.initial ≤ i), IsFinite B S hS (D.mapAt i hi) := by
  obtain ⟨T⟩ := D.nonempty_targetChart_of_siteContainsBaseChangeLimits hconv
  obtain ⟨k, hk, haff⟩ :=
    D.exists_isAffineHom_mapAt_of_isAffineHom_mapLimit_of_siteContainsBaseChangeLimits hconv
      ((isFinite_iff_isAffineHom_and_isProper B S hS D.sourceLimit_isAlgebraicSpace
        D.targetLimit_isAlgebraicSpace D.mapLimit).1 hf).1
  exact T.exists_isFinite_mapAt_of_isAffineHom hf hf₀ (Over.mk (homOfLE hk).op) haff

/-- **Stacks 084Z, for a system small for the site.** Smallness of the system for the site
implies the chapter's convention; see `exists_isFinite_mapAt_of_siteContainsBaseChangeLimits`. -/
theorem exists_isFinite_mapAt (hb : IsSiteSmall B S hS D.base)
    (hf : IsFinite B S hS D.mapLimit)
    (hf₀ : IsLocallyOfFiniteType B S hS D.map₀) :
    ∃ (i : I) (hi : D.initial ≤ i), IsFinite B S hS (D.mapAt i hi) :=
  have := D.isCofiltered_op
  D.exists_isFinite_mapAt_of_siteContainsBaseChangeLimits
    (IsSiteSmall.siteContainsBaseChangeLimits B S hS D.base hb) hf hf₀

end MorphismDescentSituation

end AlgebraicGeometry.Space

end
