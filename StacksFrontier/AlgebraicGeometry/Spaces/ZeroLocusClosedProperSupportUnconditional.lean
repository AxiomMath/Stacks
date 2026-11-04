module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackPullbackStability
public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowupDominating
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionFlatDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.DevissageInputProof
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierEtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingClosedSubspaces
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingIdealChain
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingIdealFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingIdealZerothSchemeTheoreticSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleIso
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyPrincipalPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapSituationAffineAdjoint
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersions
public import StacksFrontier.AlgebraicGeometry.Spaces.SchematicLocusRelative
public import StacksFrontier.AlgebraicGeometry.Spaces.ZeroLocusClosedProperSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.ZeroLocusClosedUnconditional
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherentLocallyNoetherian

/-!
# Stacks 083M, unconditionally

In Situation Stacks 083F — a morphism `f : X ⟶ B` of algebraic spaces over a scheme `S` and a
map `u : ℱ ⟶ 𝒢` of quasi-coherent `𝒪_X`-modules — Stacks 083M says that if (1) `f` is locally of
finite presentation, (2) `𝒢` is of finite presentation and flat over `B`, and (3) the support of
`𝒢` is proper over `B`, then `F_zero` is an algebraic space and `F_zero ⟶ B` is a closed
immersion, which is of finite presentation as soon as `ℱ` is of finite type.

`StacksFrontier/AlgebraicGeometry/Spaces/ZeroLocusClosedProperSupport.lean` proves this from two
inputs: the dévissage of Stacks 0CWC, `AlgebraicGeometry.Space.ModuleMapSituation.DevissageInput`,
and the reduction of the second paragraph of the source's proof,
`AlgebraicGeometry.Space.ModuleMapSituation.FinitePresentationReduction`.  The first is now a
theorem, `AlgebraicGeometry.Space.ModuleMapSituation.devissageInput`.  This file proves the
second, field by field, from the hypotheses of Stacks 083M alone, and so states Stacks 083M with
no hypothesis beyond the source's.

## Main results

* `AlgebraicGeometry.Space.isFinitePresentation_ι_of_fg_definingIdealAt`: a closed subspace
  whose defining ideal is finitely generated on every affine étale chart has a finitely
  presented inclusion.  This is the implication of Stacks 084Q from finite type of the ideal to
  finite presentation of the closed immersion, read on affine étale charts.
* `AlgebraicGeometry.Space.isFinitePresentation_ι_of_definingIdealSheaf_eq_fittingIdeal_zero`:
  the closed subspace cut out by the zeroth Fitting ideal of a module of finite presentation has
  a finitely presented inclusion — Stacks 0CZ5 together with Stacks 084Q, as the source cites
  them.
* `AlgebraicGeometry.Space.isFlatOver_of_isFlatOver_modulePushforward`: flatness of `i_*ℋ` over
  the base along a closed immersion `i` gives flatness of `ℋ` — the source's "check on stalks".
* `AlgebraicGeometry.Space.ModuleMapSituation.isZeroAt_replaceSource_adjoint_iff`: Stacks 0CW7
  part (1) for a target module presented as a direct image up to isomorphism.
* `AlgebraicGeometry.Space.ModuleMapSituation.nonempty_fittingReduction`: the reduction of the
  second paragraph of the proof, constructed.
* `AlgebraicGeometry.Space.ModuleMapSituation.zeroLocusRepresentation_of_hasProperSupport`:
  **Stacks 083M**.

## References

* [Stacks Project, Tag 083M](https://stacks.math.columbia.edu/tag/083M)
* [Stacks Project, Tag 0CWC](https://stacks.math.columbia.edu/tag/0CWC)
* [Stacks Project, Tag 0CZ5](https://stacks.math.columbia.edu/tag/0CZ5)
* [Stacks Project, Tag 0CZ6](https://stacks.math.columbia.edu/tag/0CZ6)
* [Stacks Project, Tag 084Q](https://stacks.math.columbia.edu/tag/084Q)
* [Stacks Project, Tag 0561](https://stacks.math.columbia.edu/tag/0561)
* [Stacks Project, Tag 0CW7](https://stacks.math.columbia.edu/tag/0CW7)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Finite presentation of a closed subspace cut out by a finitely generated ideal -/

/-- **A closed subspace whose defining ideal is finitely generated on the affine étale charts
has a finitely presented inclusion.**  This is the implication of Stacks 084Q from finite type of
the ideal sheaf to finite presentation of the closed immersion.

Finite presentation of the inclusion is finite generation, over every affine open `A` of the
atlas `U` of `X`, of the ideal cut out by the base change of the inclusion to `U`
(`AlgebraicGeometry.Space.isFinitePresentation_ι_iff_fg_chartKer`).  The affine open `A` is
itself an affine étale chart of `X`; there the chart ideal is the inverse image of the one on
`U` (`AlgebraicGeometry.Space.schemeKer_snd_comp`) and it is the ideal sheaf of the defining
ideal at that chart (`AlgebraicGeometry.Space.ker_rep_snd_eq_ofIdealTop_definingIdealAt`), which
is finitely generated by hypothesis. -/
@[sga "3 XI 6.4" "partial"]
theorem isFinitePresentation_ι_of_fg_definingIdealAt (X : AlgebraicSpaces B S hS)
    (Z : ClosedSubspaces B S hS X.1)
    (hfg : ∀ W : SmallEtale B S hS X.1,
      IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj W) →
        (definingIdealAt B S hS X Z (op W)).FG) :
    IsFinitePresentation B S hS Z.1.ι := by
  rw [isFinitePresentation_ι_iff_fg_chartKer]
  intro A
  obtain ⟨V, r, hr, hrange, hV⟩ :=
    BigFppfOver.exists_affineOpen_restrict B S hS (atlasObj B S hS X) A
  let W : SmallEtale B S hS X.1 :=
    ⟨CostructuredArrow.mk (yoneda.map r ≫ atlasHom B S hS X),
      etale_comp_of_scheme B S hS r (atlasHom B S hS X) inferInstance (atlasHom_etale B S hS X)⟩
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj W.1.left) := hV
  have hker : (chartKer B S hS X Z (atlasHom B S hS X)).comap
      ((BigFppfOver.toScheme B S hS).map r) =
        Scheme.IdealSheafData.ofIdealTop (definingIdealAt B S hS X Z (op W)) := by
    rw [chartKer_eq, ← schemeKer_snd_comp]
    exact ker_rep_snd_eq_ofIdealTop_definingIdealAt B S hS X Z W
  have htop : (((chartKer B S hS X Z (atlasHom B S hS X)).comap
      ((BigFppfOver.toScheme B S hS).map r)).ideal ⟨⊤, isAffineOpen_top _⟩).FG := by
    rw [hker]
    exact (hfg W hV).map _
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion] at htop
  have hA : (⟨(BigFppfOver.toScheme B S hS).map r ''ᵁ ⊤,
      (isAffineOpen_top _).image_of_isOpenImmersion _⟩ :
        ((BigFppfOver.toScheme B S hS).obj (atlasObj B S hS X)).affineOpens) = A := by
    refine Subtype.ext ?_
    show (BigFppfOver.toScheme B S hS).map r ''ᵁ ⊤ = A.1
    rw [Scheme.Hom.image_top_eq_opensRange]
    exact TopologicalSpace.Opens.ext (by rwa [Scheme.Hom.coe_opensRange])
  subst hA
  have hsurj : Function.Surjective (((BigFppfOver.toScheme B S hS).map r).appIso ⊤).inv.hom :=
    (((BigFppfOver.toScheme B S hS).map r).appIso ⊤).symm.commRingCatIsoToRingEquiv.surjective
  have h2 := htop.map (((BigFppfOver.toScheme B S hS).map r).appIso ⊤).inv.hom
  rwa [Ideal.map_comap_of_surjective _ hsurj] at h2

/-- **The closed subspace cut out by the zeroth Fitting ideal of a module of finite presentation
has a finitely presented inclusion.**  This is the source's appeal to Stacks 0CZ5 and Stacks 084Q
in the proof of Stacks 083M: over an affine étale chart the defining ideal is the zeroth Fitting
ideal of the sections, which are a finitely presented module over the chart ring, so it is
finitely generated. -/
theorem isFinitePresentation_ι_of_definingIdealSheaf_eq_fittingIdeal_zero
    (X : AlgebraicSpaces B S hS) (G : Modules.{u, u} B S hS X.1 X.2)
    (hG : G.IsQuasicoherentOnSite) (hfp : SheafOfModules.IsFinitePresentationOnSite G)
    (Z : ClosedSubspaces B S hS X.1)
    (cutOut : definingIdealSheaf B S hS X Z = fittingIdeal B S hS X.1 X.2 G 0) :
    IsFinitePresentation B S hS Z.1.ι := by
  have hcart := isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS X.1 X.2 G hG
  have hfpW := module_finitePresentation_sections_of_isFinitePresentationOnSite G hG hfp
  have hfin : ∀ W : SmallEtale B S hS X.1,
      IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj W) →
        Module.Finite (chartRing B S hS X.1 X.2 W) (G.val.obj (op W)) := fun W hW => by
    have := hfpW W hW
    infer_instance
  refine isFinitePresentation_ι_of_fg_definingIdealAt B S hS X Z fun W hW => ?_
  have h1 : definingIdealAt B S hS X Z (op W) =
      (fittingIdeal B S hS X.1 X.2 G 0).toSubmodule.obj (op W) := by
    rw [← cutOut]
    rfl
  rw [h1, fittingIdeal_obj_eq_fittingIdealOnChart G hcart hfin 0 hW]
  exact fg_fittingIdealOnChart G 0 (hfpW W hW)

/-! ### Flatness along a closed immersion -/

/-- **Flatness of a direct image along a closed immersion descends to the module.**  Let
`i : Z ⟶ X` be a closed immersion, `g : X ⟶ T` and `ℋ` a quasi-coherent `𝒪_Z`-module whose
direct image `i_*ℋ` (Stacks 03LU) is quasi-coherent.  If `i_*ℋ` is flat over `T` then `ℋ` is
flat over `T` along `i ≫ g`.

The direct image of Stacks 03LU is the base-change direct image along a closed immersion
(`AlgebraicGeometry.Space.modulePushforwardIsoChartDirectImage`), for which this is
`AlgebraicGeometry.Space.isFlatOver_of_isFlatOver_chartDirectImage`. -/
theorem isFlatOver_of_isFlatOver_modulePushforward {Z X T : AlgebraicSpaces B S hS}
    (i : Z ⟶ X) (hi : IsClosedImmersion B S hS i.hom) (g : X ⟶ T)
    (H : Modules.{u, u} B S hS Z.1 Z.2) [H.IsQuasicoherentOnSite]
    (hqc : ((modulePushforward B S hS i).obj H).IsQuasicoherentOnSite)
    (h : IsFlatOver B S hS X.2 g.hom ((modulePushforward B S hS i).obj H)) :
    IsFlatOver B S hS Z.2 (i ≫ g).hom H := by
  let e := modulePushforwardIsoChartDirectImage B S hS i hi H
  have : (chartDirectImage.{u, u} B S hS i hi H).IsQuasicoherentOnSite :=
    SheafOfModules.IsQuasicoherentOnSite.of_iso e hqc
  exact isFlatOver_of_isFlatOver_chartDirectImage B S hS i hi g H
    (IsFlatOver.of_iso B S hS X.2 e h)

/-! ### Stacks 0CW7 for a module presented as a direct image up to isomorphism -/

variable {B S hS}

/-- The situation of Stacks 083F on the source of the data of Stacks 0CW7, with an arbitrary
target module `𝒢` and map `u : ℱ ⟶ 𝒢` in place of `i_*ℋ` and the adjoint of `v`. -/
def AffineAdjointData.targetSituation (A : AffineAdjointData.{u} B S hS)
    (G : Modules.{u, u} B S hS A.X.1 A.X.2) (hG : G.IsQuasicoherentOnSite) (u : A.F ⟶ G) :
    ModuleMapSituation.{u, u} B S hS where
  X := A.X
  Y := A.Y
  f := A.f
  F := A.F
  G := G
  quasicoherent_F := A.quasicoherent_F
  quasicoherent_G := hG
  u := u

/-- If `u ≫ e` is the adjoint of `v` for an isomorphism `e : 𝒢 ≅ i_*ℋ`, the situation of `u`
and the situation of the adjoint of `v` vanish after the same base changes: `(u ≫ e)_T` is
`u_T ≫ e_T` with `e_T` an isomorphism. -/
theorem AffineAdjointData.isZeroAt_sourceSituation_iff (A : AffineAdjointData.{u} B S hS)
    (hq : ((modulePushforward B S hS A.i).obj A.H).IsQuasicoherentOnSite)
    (G : Modules.{u, u} B S hS A.X.1 A.X.2) (hG : G.IsQuasicoherentOnSite) (u : A.F ⟶ G)
    (e : G ≅ (modulePushforward B S hS A.i).obj A.H)
    (hu : u ≫ e.hom = (modulePullbackAdjunction B S hS A.i).homEquiv A.F A.H A.v)
    (P : ModulePullbackSystem.{u, u} B S hS) (T : (A.sourceSituation hq).SchemesOver) :
    (A.sourceSituation hq).IsZeroAt P T ↔ (A.targetSituation G hG u).IsZeroAt P T := by
  have hc : (P.functor ((A.targetSituation G hG u).baseChangeProjection T)).map (u ≫ e.hom) =
      (P.functor ((A.targetSituation G hG u).baseChangeProjection T)).map u ≫
        ((P.functor ((A.targetSituation G hG u).baseChangeProjection T)).mapIso e).hom :=
    (P.functor ((A.targetSituation G hG u).baseChangeProjection T)).map_comp u e.hom
  have hc' := (congrArg (P.functor ((A.targetSituation G hG u).baseChangeProjection T)).map
    hu.symm).trans hc
  show (P.functor ((A.targetSituation G hG u).baseChangeProjection T)).map
      ((modulePullbackAdjunction B S hS A.i).homEquiv A.F A.H A.v) = 0 ↔
    (P.functor ((A.targetSituation G hG u).baseChangeProjection T)).map u = 0
  rw [hc']
  exact Preadditive.IsIso.comp_right_eq_zero _ _

namespace ModuleMapSituation

/-- The situation `AlgebraicGeometry.Space.AffineAdjointData.targetSituation` built from the
fields of a situation of Stacks 083F is that situation. -/
theorem isZeroAt_targetSituation_mk_iff (D : ModuleMapSituation.{u, u} B S hS)
    (Z : AlgebraicSpaces B S hS) (i : Z ⟶ D.X) (H : Modules.{u, u} B S hS Z.1 Z.2)
    (hH : H.IsQuasicoherentOnSite) (v : (modulePullback B S hS i).obj D.F ⟶ H)
    (P : ModulePullbackSystem.{u, u} B S hS) (T : D.SchemesOver) :
    ((AffineAdjointData.mk D.X D.Y Z D.f i D.F H D.quasicoherent_F hH v).targetSituation D.G
      D.quasicoherent_G D.u).IsZeroAt P T ↔ D.IsZeroAt P T :=
  Iff.rfl

/-- **Stacks 0CW7, part (1), for `𝒢 ≅ i_*ℋ`.**  Let `i : Z ⟶ X` be a closed immersion, `ℋ` a
quasi-coherent `𝒪_Z`-module and `e : 𝒢 ≅ i_*ℋ`.  Replacing `X` by `Z` and `u` by the adjoint
`v : i^*ℱ ⟶ ℋ` of `u` followed by `e` does not change the vanishing locus.

The adjoint situation is that of `AlgebraicGeometry.Space.AffineAdjointData`, a closed immersion
being affine (Stacks 07U2), so Stacks 0CW7 part (1) identifies its vanishing locus with that of
`u ≫ e`; and `u ≫ e` vanishes after a base change exactly when `u` does, `e` being an
isomorphism. -/
theorem isZeroAt_replaceSource_adjoint_iff (D : ModuleMapSituation.{u, u} B S hS)
    {Z : AlgebraicSpaces B S hS} (i : Z ⟶ D.X) (hi : IsClosedImmersion B S hS i.hom)
    (H : Modules.{u, u} B S hS Z.1 Z.2) (hH : H.IsQuasicoherentOnSite)
    (e : D.G ≅ (modulePushforward B S hS i).obj H)
    (hF' : ((modulePullback B S hS i).obj D.F).IsQuasicoherentOnSite)
    (v : (modulePullback B S hS i).obj D.F ⟶ H)
    (hv : (modulePullbackAdjunction B S hS i).homEquiv D.F H v = D.u ≫ e.hom)
    (T : D.SchemesOver) :
    (D.replaceSource Z (i ≫ D.f) ((modulePullback B S hS i).obj D.F) H hF' hH v).IsZeroAt
          (modulePullbackSystem B S hS) T ↔
      D.IsZeroAt (modulePullbackSystem B S hS) T := by
  have hq : ((modulePushforward B S hS i).obj H).IsQuasicoherentOnSite :=
    SheafOfModules.IsQuasicoherentOnSite.of_iso e D.quasicoherent_G
  let A : AffineAdjointData B S hS := .mk D.X D.Y Z D.f i D.F H D.quasicoherent_F hH v
  refine (A.isZeroAt_adjointSituation_iff hF' hq T (A.adjointAfterBaseChange hF' hq T
      (isAffineHom_of_isClosedImmersion B S hS i.hom hi))).trans (Iff.trans
    (A.isZeroAt_sourceSituation_iff hq D.G D.quasicoherent_G D.u e ?_
      (modulePullbackSystem B S hS) T) (D.isZeroAt_targetSituation_mk_iff Z i H hH _ _ T))
  dsimp only [A]
  exact hv.symm

/-! ### The reduction of the second paragraph of the proof, constructed -/

/-- **The reduction of the second paragraph of the proof of Stacks 083M, constructed** from the
hypotheses of Stacks 083M.

* `Z ⊆ X` is the closed subspace cut out by the zeroth Fitting ideal of `𝒢`, which is
  quasi-coherent by Stacks 0CZ5 and so cuts out a closed subspace by Stacks 03MB
  (`AlgebraicGeometry.Space.exists_fittingClosedSubspaces`);
* its inclusion `i` is of finite presentation, by Stacks 0CZ5 and Stacks 084Q
  (`AlgebraicGeometry.Space.isFinitePresentation_ι_of_definingIdealSheaf_eq_fittingIdeal_zero`);
* `|Z|` is the support of `𝒢` and `𝒢 ≅ i_*ℋ` for a quasi-coherent `𝒪_Z`-module `ℋ` of finite
  type, by Stacks 0CZ6 parts (2) and (3);
* `Z ⟶ B` is proper by Stacks 0CZE and 0CZC out of hypothesis (3), hence quasi-separated, hence
  decent (Stacks 03M5);
* `ℋ ≅ i^*i_*ℋ ≅ i^*𝒢` (Stacks 04CJ part (2)) is of finite presentation because `𝒢` is — the
  source's appeal to Stacks 0561;
* `ℋ` is flat over `B` because `i_*ℋ ≅ 𝒢` is
  (`AlgebraicGeometry.Space.isFlatOver_of_isFlatOver_modulePushforward`);
* `v : i^*ℱ ⟶ ℋ` is the adjoint of `u` followed by `𝒢 ≅ i_*ℋ`, and the two vanishing loci agree
  by Stacks 0CW7 part (1), `i` being affine (Stacks 07U2). -/
theorem nonempty_fittingReduction (D : ModuleMapSituation.{u, u} B S hS)
    (hf : IsLocallyOfFinitePresentation B S hS D.f.hom)
    (hGfp : SheafOfModules.IsFinitePresentationOnSite D.G)
    (hGflat : IsFlatOver B S hS D.X.property D.f.hom D.G)
    (hproper : HasProperSupport B S hS D.X.property D.Y.property D.f.hom
      (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hf)
      ((SheafOfModules.toSheaf _).obj D.G)) :
    Nonempty D.FinitePresentationReduction := by
  have := D.quasicoherent_G
  have hqcFit : ∀ r : ℕ,
      (fittingIdeal B S hS D.X.1 D.X.2 D.G r).toSheafOfModules.IsQuasicoherentOnSite := fun r =>
    (isFiniteTypeQuasicoherentIdeal_fittingIdeal_of_isFinitePresentationOnSite D.X D.G
      D.quasicoherent_G hGfp r).1
  obtain ⟨Zs, hZs, -⟩ := exists_fittingClosedSubspaces B S hS D.X D.G hqcFit
  obtain ⟨Z₀, cutOut⟩ : ∃ Z₀ : ClosedSubspaces B S hS D.X.1,
      definingIdealSheaf B S hS D.X Z₀ = fittingIdeal B S hS D.X.1 D.X.2 D.G 0 := ⟨Zs 0, hZs 0⟩
  obtain ⟨H, hHqc, hHft, ⟨e'⟩⟩ :=
    exists_module_on_fittingClosedSubspace B S hS D.X D.G Z₀ cutOut
  let i := closedSubspaceInclusion B S hS D.X Z₀
  have hi : IsClosedImmersion B S hS i.hom := Z₀.2.2
  have hrange : Set.range (pointsMap B S hS Z₀.1.toFunctor Z₀.1.ι) ⊆
      supportOfSheaf B S hS D.X.1 ((SheafOfModules.toSheaf _).obj D.G) :=
    (range_pointsMap_schemeTheoreticSupport_eq_supportOfSheaf B S hS D.X D.G Z₀
      cutOut).2.1.subset
  have hZB : IsProper B S hS (i.hom ≫ D.f.hom) :=
    isProper_comp_of_hasProperSupport_of_range_subset B S hS D.X.property D.Y.property D.f.hom
      (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hf) hproper
      (closedSubspaceToSpace B S hS D.X Z₀).2 i.hom hi hrange
  have hdec : IsDecent B S hS (i.hom ≫ D.f.hom) :=
    isDecent_of_isReasonable B S hS (closedSubspaceToSpace B S hS D.X Z₀).2 D.Y.2 _
      (isReasonable_of_isVeryReasonable B S hS (closedSubspaceToSpace B S hS D.X Z₀).2 D.Y.2
        (isVeryReasonable_of_isQuasiSeparated B S hS (closedSubspaceToSpace B S hS D.X Z₀).2
          D.Y.2 (isQuasiSeparated_of_isSeparated B S hS (IsProper.isSeparated B S hS hZB))))
  let e : D.G ≅ (modulePushforward B S hS i).obj H := e'.symm
  have hHfp : SheafOfModules.IsFinitePresentationOnSite H :=
    SheafOfModules.IsFinitePresentationOnSite.of_iso
      (((modulePullback B S hS i).mapIso e').symm ≪≫
        (modulePullbackCounitIso B S hS i hi).app H)
      (isFinitePresentationOnSite_modulePullback B S hS i D.G hGfp)
  have hflat : IsFlatOver B S hS (closedSubspaceToSpace B S hS D.X Z₀).2 (i ≫ D.f).hom H :=
    isFlatOver_of_isFlatOver_modulePushforward B S hS i hi D.f H
      (SheafOfModules.IsQuasicoherentOnSite.of_iso e D.quasicoherent_G)
      (IsFlatOver.of_iso B S hS D.X.2 e hGflat)
  have hqcPF : ((modulePullback B S hS i).obj D.F).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS i D.F D.quasicoherent_F
  exact ⟨
    { Z := closedSubspaceToSpace B S hS D.X Z₀
      i := i
      isClosedImmersion := hi
      isLocallyOfFinitePresentation :=
        (isFinitePresentation_ι_of_definingIdealSheaf_eq_fittingIdeal_zero B S hS D.X D.G
          D.quasicoherent_G hGfp Z₀ cutOut).1
      range_pointsMap_subset_support := hrange
      isDecent := hdec
      H := H
      quasicoherent_H := hHqc
      finiteType_H := hHft
      finitePresentation_H := hHfp
      flat_H := hflat
      iso_pushforward_H := e
      quasicoherent_pullback_F := hqcPF
      v := ((modulePullbackAdjunction B S hS i).homEquiv D.F H).symm (D.u ≫ e.hom)
      isZeroAt_iff := D.isZeroAt_replaceSource_adjoint_iff i hi H hHqc e hqcPF _
        (Equiv.apply_symm_apply _ _) }⟩

/-! ### Stacks 083M -/

/-- **Stacks 083M.**  In Situation 083F, assume that
1. `f` is locally of finite presentation,
2. `𝒢` is an `𝒪_X`-module of finite presentation flat over `B`,
3. the support of `𝒢` is proper over `B`.

Then the functor `F_zero` is an algebraic space and `F_zero ⟶ B` is a closed immersion; if `ℱ`
is of finite type, then `F_zero ⟶ B` is of finite presentation.

The conclusion `AlgebraicGeometry.Space.ModuleMapSituation.ZeroLocusRepresentation` is the
existence of a subfunctor `Z` of `B` which is a closed subspace (an algebraic space whose
inclusion is a closed immersion), whose inclusion is of finite presentation when `ℱ` is of finite
type, and which represents `F_zero`.  The hypotheses are exactly the source's.

The proof is the source's: pass to the closed subspace cut out by the zeroth Fitting ideal of
`𝒢` (`AlgebraicGeometry.Space.ModuleMapSituation.nonempty_fittingReduction`) and apply Stacks
0CWC there, whose dévissage is `AlgebraicGeometry.Space.ModuleMapSituation.devissageInput`.  The
case of the first paragraph of the proof, `f` of finite presentation, is the special case of a
morphism of finite presentation, which is in particular locally of finite presentation. -/
@[stacks 083M "every case: f locally of finite presentation (which includes the case of the \
first paragraph of the proof, f of finite presentation), G of finite presentation and flat over \
B, the support of G proper over B; F_zero is represented by a closed subspace of B, of finite \
presentation over B when F is of finite type -- at the source's hypotheses alone"]
theorem zeroLocusRepresentation_of_hasProperSupport (D : ModuleMapSituation.{u, u} B S hS)
    (hf : IsLocallyOfFinitePresentation B S hS D.f.hom)
    (hGfp : SheafOfModules.IsFinitePresentationOnSite D.G)
    (hGflat : IsFlatOver B S hS D.X.property D.f.hom D.G)
    (hproper : HasProperSupport B S hS D.X.property D.Y.property D.f.hom
      (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hf)
      ((SheafOfModules.toSheaf _).obj D.G)) :
    D.ZeroLocusRepresentation :=
  zeroLocusRepresentation (devissageInput B S hS) D hf hGfp hGflat hproper
    (D.nonempty_fittingReduction hf hGfp hGflat hproper).some

end ModuleMapSituation

end AlgebraicGeometry.Space

end
