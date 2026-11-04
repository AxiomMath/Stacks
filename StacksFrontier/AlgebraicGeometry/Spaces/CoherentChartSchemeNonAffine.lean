module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartIdealSheafDataComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentChartSchemeRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModelCoveringSet

/-!
# Coherence of the chart restriction on a chart which is Noetherian but not affine

Let `X` be an algebraic space over a scheme `S` in a big fppf site `B` and let `M` be a coherent
`𝒪_X`-module.  On an étale scheme chart `V` of `X` the file
`StacksFrontier/AlgebraicGeometry/Spaces/CoherentChartSchemeRestriction.lean` proves that the chart
restriction `AlgebraicGeometry.Space.chartSchemeModule` is coherent **over a Noetherian affine
chart**.  That is not enough for the Stacks 07UM argument: there the scheme-level Stacks 01YB is
applied on the kernel pair `W ⨯ W` of a single surjective affine Noetherian chart `W`, and
`W ⨯ W` is only a *Noetherian scheme*, never an affine chart.

This file removes affineness.  The point is that nothing in the finiteness of the sections of the
chart restriction over a Zariski open `W` of the chart's scheme uses affineness of the chart
itself: the chain of four pushforwards identifies those sections with the sections of `M` over
the étale chart `AlgebraicGeometry.Space.openChartOfComparison … W`, and that chart's scheme is
`W` itself, so it is affine as soon as `W` is an *affine open*.  Running the argument over the
affine opens of the chart's scheme, which cover it, gives finite type with no hypothesis at all;
coherence then needs only local Noetherianity of the chart's scheme, through Stacks 01XZ
(2) ⇒ (1).

## Main results

* `AlgebraicGeometry.Space.moduleFinite_sections_chartSchemeModule`: over an **affine open** of
  the chart's scheme the sections of the chart restriction form a finite module.  This is the
  Zariski-local form of
  `AlgebraicGeometry.Space.moduleFinite_sectionsTop_chartSchemeModule`.
* `AlgebraicGeometry.Space.isFiniteType_chartSchemeModule_of_isCoherent`: the chart restriction
  of a coherent module is of finite type **on every** étale scheme chart.
* `AlgebraicGeometry.Space.isCoherent_chartSchemeModule_of_isLocallyNoetherian`: **the chart
  restriction of a coherent module is coherent on every chart whose scheme is locally
  Noetherian.**
* `AlgebraicGeometry.Space.isNoetherianAffineChart_of_isAffineChart`: on a Noetherian algebraic
  space every affine étale chart is a Noetherian affine chart.
* `AlgebraicGeometry.Space.isNoetherian_chartScheme_of_isNoetherianAffineChart`: the scheme of a
  Noetherian affine chart is a Noetherian scheme.
* `AlgebraicGeometry.Space.isNoetherian_chartScheme_prod`: the scheme of the product of two
  charts with quasi-compact schemes over a quasi-separated, locally Noetherian algebraic space is
  a Noetherian scheme.
* `AlgebraicGeometry.Space`
  `.exists_surjective_isNoetherianAffineChart_isNoetherian_prod_isCoherent_chartSchemeModule`:
  **on a Noetherian algebraic space there is a surjective Noetherian affine chart `W` such that
  the chart restriction is coherent both on `W` and on the kernel pair `W ⨯ W`, whose scheme is
  Noetherian.**  This is the shape in which the Stacks 07UM argument instantiates the
  scheme-level Stacks 01YB.

## Implementation notes

**The chart cut out by an open is the open.**  `AlgebraicGeometry.Space.openChartOfComparison` is
the chart which a Zariski open becomes under the two comparison equivalences, and
`AlgebraicGeometry.Space.openChart_eq_chartLocalization_opensObj` says it *equals*
`AlgebraicGeometry.Space.openChart`, whose scheme is the open subscheme on the nose.  Affineness
of the chart's scheme is therefore `IsAffineOpen` of the open, definitionally; that equation is
used only here, inside the scheme-level predicate, and is never rewritten at module level, where
it would move the codomain of the scalar map.

**Why finite type carries no hypothesis.**
`AlgebraicGeometry.Space.isFiniteType_chartSchemeModule` asks for an affine chart only because it
covers the chart's scheme by the single open `⊤`.  The affine opens of any scheme cover it
(`AlgebraicGeometry.iSup_affineOpens_eq_top`), and condition (4) of Stacks 01XZ at each of them is
the same finiteness statement, so the covering argument goes through unchanged.  The result below
therefore *subsumes* both `moduleFinite_sectionsTop_chartSchemeModule` (at `W = ⊤`, which is
affine when the chart is) and `isFiniteType_chartSchemeModule`.

**The sections lemma is a copy, not a reuse.**  Its proof is the chain of four applications of
`Stacks.SheafOfModules.moduleFinite_sections_pushforward` of
`moduleFinite_sectionsTop_chartSchemeModule` with the open `⊤` replaced by `W` throughout; only
the first step, the affineness of the chart cut out by the open, differs.  The heartbeat budget
is per-declaration, so the two are kept as separate declarations rather than one being derived
from a shared general form.

**Local Noetherianity at a chart.**  `AlgebraicGeometry.Space.IsNoetherian` records local
Noetherianity as the some-chart condition `AlgebraicGeometry.Space.HasEtaleLocalProperty`;
Stacks 03E8, `AlgebraicGeometry.Space.exists_atlas_iff_forall_etale`, turns it into the
every-chart condition, which is the only place algebraicity of `X` is used.  Its locality input
is `AlgebraicGeometry.isLocallyNoetherian_isLocal_etale` and is an instance, so it is not a
hypothesis.  Quasi-compactness of the product of two charts is
`AlgebraicGeometry.Space.SmallEtale.compactSpace_prod`, Stacks 073B on charts, which needs
quasi-separatedness of `X` and nothing else.

No declaration here carries a `stacks` tag: coherence of the chart restriction is an input to
Stacks 07UM, not a clause of it, and the clauses of Stacks 01XZ, 03E8 and 073B used are already
covered in the tree.

## References

* [Stacks Project, Tag 07UM](https://stacks.math.columbia.edu/tag/07UM)
* [Stacks Project, Tag 01YB](https://stacks.math.columbia.edu/tag/01YB)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 03E8](https://stacks.math.columbia.edu/tag/03E8)
* [Stacks Project, Tag 073B](https://stacks.math.columbia.edu/tag/073B)
* [Stacks Project, Tag 03EA](https://stacks.math.columbia.edu/tag/03EA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.FiniteDirectImageCoherent

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)
    (M : SheafOfModules.{u} (structureRingSheaf B S hS X))

/-! ### The sections over an affine open of the chart scheme -/

/-- **The sections of the chart restriction over an affine open of the chart's scheme are
finite.**  For a coherent `𝒪_X`-module, any étale chart and any *affine open* `W` of the chart's
scheme, the sections over `W` of the `AlgebraicGeometry.Scheme.Modules` which `M` becomes on the
chart's scheme form a finite module over the functions on `W`.

This is `AlgebraicGeometry.Space.moduleFinite_sectionsTop_chartSchemeModule` with the open `⊤` of
an affine chart replaced by an affine open of an arbitrary chart: the chain of four pushforwards
— the slice at the chart, the comparison of Stacks 04M0, the comparison of the representable case
of Stacks 03ED, and the inclusion of the small Zariski site — identifies the sections with those
of `M` over the étale chart `AlgebraicGeometry.Space.openChartOfComparison … W`, whose scheme is
affine by `AlgebraicGeometry.Space.isAffine_chartScheme_openChartOfComparison`. -/
theorem moduleFinite_sections_chartSchemeModule
    (hM : IsCoherent B S hS X.1 X.2 M) (V : SmallEtale B S hS X.1)
    {W : (chartScheme V).Opens} (hW : IsAffineOpen W) :
    Module.Finite ((chartScheme V).ringCatSheaf.obj.obj (op W))
      ((chartSchemeModule B S hS X M hM.toIsQuasicoherentOnSite V).val.obj (op W)) := by
  have h0 := moduleFinite_sections_of_isCoherent B S hS X.1 X.2 M hM
    (isAffine_chartScheme_openChartOfComparison B S hS X V hW)
  set O := _root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
    (chartScheme V) (chartFppfObject B S hS X V).left.property W
  set P := (representedSmallEtaleEquivalence B S hS (chartFppfObject B S hS X V)).inverse.obj O
  have h1 := Stacks.SheafOfModules.moduleFinite_sections_pushforward
    (𝟙 ((structureRingSheaf B S hS X).over V)) M
    ((SmallEtale.chartLocalizationEquivalence B S hS X.1 V).functor.obj P)
    (fun x => ⟨x, rfl⟩) h0
  have h2 := @Stacks.SheafOfModules.moduleFinite_sections_pushforward
    (SmallEtale B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj V))) inferInstance
    (Over V) inferInstance
    (SmallEtale.topology B S hS (chartSpace B S hS X V).1)
    ((SmallEtale.topology B S hS X.1).over V)
    (SmallEtale.chartLocalizationEquivalence B S hS X.1 V).functor
    (chartStructureRingSheaf B S hS X V) ((structureRingSheaf B S hS X).over V)
    (isContinuous_chartLocalization_chartSpace B S hS X V)
    (𝟙 (chartStructureRingSheaf B S hS X V)) (M.over V)
    P (fun x => ⟨x, rfl⟩) h1
  have h3 := Stacks.SheafOfModules.moduleFinite_sections_pushforward
    (Stacks.SheafOfModules.reindexBackSharp
      (J' := SmallEtale.topology B S hS (yoneda.obj (chartFppfObject B S hS X V)))
      (representedSmallEtaleEquivalence B S hS (chartFppfObject B S hS X V))
      (representedSchemeStructureSheaf B S hS (chartFppfObject B S hS X V)))
    (chartSmallEtaleRestriction B S hS X M V) O
    (Stacks.SheafOfModules.surjective_reindexBackSharp_app _ _ _) h2
  have h4 := Stacks.SheafOfModules.moduleFinite_sections_pushforward
    (_root_.AlgebraicGeometry.SmallEtale.structureMap (associatedBigEtaleSite B) (chartScheme V)
      (chartFppfObject B S hS X V).left.property)
    (chartSchemeEtaleModule B S hS X M hM.toIsQuasicoherentOnSite V) W
    (_root_.AlgebraicGeometry.SmallEtale.surjective_structureMap_hom_app _ _ _ _) h3
  exact Stacks.SheafOfModules.moduleFinite_sections_of_iso
    (chartSchemeModuleIsoRestrictModule B S hS X M hM.toIsQuasicoherentOnSite V) W h4

/-! ### Finite type on an arbitrary chart -/

/-- **The chart restriction of a coherent module is of finite type on every étale scheme
chart.**  The affine opens of the chart's scheme cover it, and over each of them the sections of
the chart restriction form a finite module, so condition (4) of Stacks 01XZ holds there.

This is `AlgebraicGeometry.Space.isFiniteType_chartSchemeModule` with its affineness hypothesis
removed: that hypothesis only served to make `⊤` an affine open. -/
theorem isFiniteType_chartSchemeModule_of_isCoherent
    (hM : IsCoherent B S hS X.1 X.2 M) (V : SmallEtale B S hS X.1) :
    SheafOfModules.IsFiniteType (chartSchemeModule B S hS X M hM.toIsQuasicoherentOnSite V) :=
  have _hq : SheafOfModules.IsQuasicoherent
      (chartSchemeModule B S hS X M hM.toIsQuasicoherentOnSite V) :=
    isQuasicoherent_chartSchemeModule B S hS X M hM.toIsQuasicoherentOnSite V
  Stacks.AlgebraicGeometry.CoherentTFAE.isFiniteType_of_cover_isFiniteTildeOn _
    (fun W : (chartScheme V).affineOpens => (W : (chartScheme V).Opens))
    (TopologicalSpace.IsOpenCover.mk
      (_root_.AlgebraicGeometry.iSup_affineOpens_eq_top (chartScheme V)))
    (fun W => W.2)
    (fun W => isFiniteTildeOn_of_moduleFinite_sections _ W
      (moduleFinite_sections_chartSchemeModule B S hS X M hM V W.2))

/-! ### Coherence on a chart whose scheme is locally Noetherian -/

/-- **Stacks 07UM reduced to a scheme chart, with no affineness: the chart restriction of a
coherent module on an algebraic space is coherent over any chart whose scheme is locally
Noetherian.**

The chart restriction is quasi-coherent by
`AlgebraicGeometry.Space.isQuasicoherent_chartSchemeModule` and of finite type by
`AlgebraicGeometry.Space.isFiniteType_chartSchemeModule_of_isCoherent`, so Stacks 01XZ (2) ⇒ (1)
applies.  This is the form the Stacks 07UM argument needs on the kernel pair of a chart, which is
a Noetherian scheme but not an affine chart. -/
theorem isCoherent_chartSchemeModule_of_isLocallyNoetherian
    (hM : IsCoherent B S hS X.1 X.2 M) (V : SmallEtale B S hS X.1)
    (hV : IsLocallyNoetherian (chartScheme V)) :
    SheafOfModules.IsCoherent (chartSchemeModule B S hS X M hM.toIsQuasicoherentOnSite V) :=
  have _hln : IsLocallyNoetherian (chartScheme V) := hV
  have _hq : SheafOfModules.IsQuasicoherent
      (chartSchemeModule B S hS X M hM.toIsQuasicoherentOnSite V) :=
    isQuasicoherent_chartSchemeModule B S hS X M hM.toIsQuasicoherentOnSite V
  have _hft : SheafOfModules.IsFiniteType
      (chartSchemeModule B S hS X M hM.toIsQuasicoherentOnSite V) :=
    isFiniteType_chartSchemeModule_of_isCoherent B S hS X M hM V
  Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isQuasicoherent_of_isFiniteType _

/-! ### Noetherian schemes among the charts -/

/-- **Every étale chart of a locally Noetherian algebraic space has locally Noetherian
scheme.**  Local Noetherianity of an algebraic space is the some-chart condition of Stacks 03E6;
this is the every-chart form, Stacks 03E8, whose locality input is an instance. -/
theorem isLocallyNoetherian_chartScheme
    (hLN : HasEtaleLocalProperty B S hS X.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (V : SmallEtale B S hS X.1) : IsLocallyNoetherian (chartScheme V) :=
  (exists_atlas_iff_forall_etale B S hS X.1
    (fun T : Scheme.{u} => IsLocallyNoetherian T) X.2).1 hLN V.obj.left V.obj.hom V.property

/-- **Every affine étale chart of a Noetherian algebraic space is a Noetherian affine chart.**
Its scheme is locally Noetherian by Stacks 03E8, and affine, so its ring of global sections is
Noetherian. -/
theorem isNoetherianAffineChart_of_isAffineChart (hZ : B.Contains (⊤_ Scheme.{u}))
    (hN : IsNoetherian B S hS hZ X.1) (A : SmallEtale B S hS X.1)
    (hA : IsAffineChart B S hS X.1 A) :
    IsNoetherianAffineChart B S hS X.1 A :=
  ⟨hA, isNoetherianRing_Γ_of_isLocallyNoetherian (chartScheme A) hA
    (isLocallyNoetherian_chartScheme B S hS X hN.2.2 A)⟩

/-- **The scheme of a Noetherian affine chart is a Noetherian scheme.**  It is affine, hence
quasi-compact, and its ring of global sections is Noetherian, so the single affine cover `⊤`
makes it locally Noetherian. -/
theorem isNoetherian_chartScheme_of_isNoetherianAffineChart (A : SmallEtale B S hS X.1)
    (hA : IsNoetherianAffineChart B S hS X.1 A) :
    _root_.AlgebraicGeometry.IsNoetherian (chartScheme A) :=
  have _haff : IsAffine (chartScheme A) := hA.1
  have _hln : IsLocallyNoetherian (chartScheme A) :=
    isLocallyNoetherian_of_affine_cover
      (S := fun _ : Unit => ⟨⊤, isAffineOpen_top (chartScheme A)⟩) (by simp) (fun _ => hA.2)
  ⟨⟩

/-- **The scheme of the product of two charts with quasi-compact schemes is a Noetherian
scheme**, on a quasi-separated algebraic space which is locally Noetherian.  Quasi-compactness of
the product is Stacks 073B on charts,
`AlgebraicGeometry.Space.SmallEtale.compactSpace_prod`, and local Noetherianity is Stacks 03E8 at
the product chart. -/
theorem isNoetherian_chartScheme_prod (hZ : B.Contains (⊤_ Scheme.{u}))
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (hLN : HasEtaleLocalProperty B S hS X.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (U V : SmallEtale B S hS X.1)
    (hU : CompactSpace (chartScheme U)) (hV : CompactSpace (chartScheme V)) :
    _root_.AlgebraicGeometry.IsNoetherian (chartScheme (U ⨯ V)) :=
  have _hln : IsLocallyNoetherian (chartScheme (U ⨯ V)) :=
    isLocallyNoetherian_chartScheme B S hS X hLN (U ⨯ V)
  have _hcomp : CompactSpace (chartScheme (U ⨯ V)) :=
    SmallEtale.compactSpace_prod B S hS X.1 hZ hqs U V hU hV
  ⟨⟩

/-! ### The kernel pair of a surjective Noetherian affine chart -/

/-- **A coherent module on a Noetherian algebraic space is coherent on a surjective Noetherian
affine chart and on its kernel pair.**  There is an étale chart `W` whose underlying scheme is
affine with Noetherian ring of global sections, which is surjective on points, such that the
chart restriction of a coherent `𝒪_X`-module is coherent on `W`, the scheme of the kernel pair
`W ⨯ W` is a Noetherian scheme, and the chart restriction is coherent there too.

The last two conclusions are what the Stacks 07UM argument needs in order to instantiate the
scheme-level Stacks 01YB on the kernel pair: that scheme is Noetherian but it is not an affine
chart, so `AlgebraicGeometry.Space.isCoherent_chartSchemeModule` does not reach it. -/
theorem exists_surjective_isNoetherianAffineChart_isNoetherian_prod_isCoherent_chartSchemeModule
    (hZ : B.Contains (⊤_ Scheme.{u})) (hN : IsNoetherian B S hS hZ X.1)
    (hM : IsCoherent B S hS X.1 X.2 M) :
    ∃ W : SmallEtale B S hS X.1, IsNoetherianAffineChart B S hS X.1 W ∧
      Function.Surjective (pointsMap B S hS
          (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj W)) W.1.hom) ∧
        SheafOfModules.IsCoherent
            (chartSchemeModule B S hS X M hM.toIsQuasicoherentOnSite W) ∧
          _root_.AlgebraicGeometry.IsNoetherian (chartScheme (W ⨯ W)) ∧
            SheafOfModules.IsCoherent
              (chartSchemeModule B S hS X M hM.toIsQuasicoherentOnSite (W ⨯ W)) := by
  obtain ⟨W, hW, -, hsurj⟩ := exists_surjective_isNoetherianAffineChart B S hS hZ X hN
  have _haff : IsAffine (chartScheme W) := hW.1
  have hprod : _root_.AlgebraicGeometry.IsNoetherian (chartScheme (W ⨯ W)) :=
    isNoetherian_chartScheme_prod B S hS X hZ hN.2.1 hN.2.2 W W inferInstance inferInstance
  exact ⟨W, hW, hsurj,
    isCoherent_chartSchemeModule_of_isLocallyNoetherian B S hS X M hM W
      (isLocallyNoetherian_chartScheme B S hS X hN.2.2 W),
    hprod,
    isCoherent_chartSchemeModule_of_isLocallyNoetherian B S hS X M hM (W ⨯ W)
      hprod.toIsLocallyNoetherian⟩

end AlgebraicGeometry.Space

end
