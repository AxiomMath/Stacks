module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartFibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdeals
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ChartSystemEtalePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierEtaleEquiv
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.RelativeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.NilpotentApproximation
public import StacksFrontier.RingTheory.Etale.AffineStageCore

/-!
# The rings of the chart of a closed subspace

Let `Y` be an algebraic space with an affine étale chart `φ : V ⟶ Y`, and let `R = V ×_Y V`, with
projections `t, s : R ⟶ V`, be affine as well. Put `C = Γ(V)` and `E = Γ(R)`. A closed subspace
`Z ⊆ Y` has a chart ideal `K_Z ⊆ C`, the kernel of restriction to `Z ×_Y V`
(`AlgebraicGeometry.Space.chartIdealAt`). This file records how these ideals behave:

* they extend to the same ideal of `E` along `s` and along `t`;
* they reverse inclusions of closed subspaces (`AlgebraicGeometry.Space.definingIdealAt_antitone`);
* the chart ideal of an intersection is contained in the sum of the chart ideals.

These are the chart-level facts used in the proof of Stacks 07SQ for a directed system of closed
subspaces of one algebraic space.

## Main results

* `AlgebraicGeometry.Space.chartIdealAt_eq_ideal_chartKer`: the chart ideal is the ideal of
  global functions of the chart ideal sheaf.
* `AlgebraicGeometry.Space.map_chartIdealAt_eq`: `K_Z E` is the same along `t` and along `s`.
* `AlgebraicGeometry.Space.chartIdealAt_iInf_le`: `K_{⋂ Zᵢ} ⊆ ∑ K_{Zᵢ}`.
* `AlgebraicGeometry.Space.exists_affine_chart_affine_relation`: a quasi-compact separated space
  has an affine surjective étale chart with affine relation.
* `AlgebraicGeometry.Space.nonempty_closedChartData`: every closed subspace `Z` has a chart
  `V ×_Y Z` with relation `R ×_Y Z`, whose rings are `C ⧸ K_Z` and `E ⧸ K_Z E`.
* `AlgebraicGeometry.Space.exists_etale_faithfullyFlat_bijective_tensorLift`: for an affine
  algebraic space with an affine chart `V` and relation `R`, `Γ(F) → Γ(V)` is étale and
  faithfully flat and `Γ(V) ⊗_{Γ(F)} Γ(V) ≅ Γ(R)`.
* `AlgebraicGeometry.Space.exists_effective_of_isAffineSpace`: the same for an affine closed
  subspace, read on `C ⧸ K_Z` and `E ⧸ K_Z E`.

## References

* [Stacks Project, Tag 07SQ](https://stacks.math.columbia.edu/tag/07SQ)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- On an affine scheme, the composite of the identity open with itself under a morphism is the
morphism on global sections. -/
theorem Scheme.Hom.appLE_top_top {X Y : Scheme.{u}} (f : X ⟶ Y) (h : (⊤ : X.Opens) ≤ f ⁻¹ᵁ ⊤) :
    f.appLE ⊤ ⊤ h = f.appTop := by
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rfl

variable (Y : AlgebraicSpaces B S hS) {V : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] {φ : yoneda.obj V ⟶ Y.1}
  (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ)

/-- **The chart ideal is the ideal of global functions of the chart ideal sheaf.** -/
theorem chartIdealAt_eq_ideal_chartKer (Z : ClosedSubspaces B S hS Y.1) :
    chartIdealAt B S hS Y he Z =
      (chartKer B S hS Y Z φ).ideal ⟨⊤, (isAffineOpen_top _ : IsAffineOpen _)⟩ := by
  rw [chartIdealAt, definingIdealAt_eq_ker, chartKer, Scheme.Hom.ker_apply]
  rfl

/-- **The chart ideal of an intersection of closed subspaces is contained in the sum of their
chart ideals.** Let `K = ∑ K_{Zᵢ}`. The closed subscheme `V(K)` of the chart maps into every `Zᵢ`,
since `K` contains each `K_{Zᵢ}`, hence into their intersection; so the chart ideal of the
intersection is killed on `V(K)`, that is, contained in `K`. No directedness is needed. -/
theorem chartIdealAt_iInf_le {ι : Sort*} (Z : ι → ClosedSubspaces B S hS Y.1)
    (hZ : IsClosedSubspace B S hS (⨅ i, (Z i).1)) :
    chartIdealAt B S hS Y he ⟨⨅ i, (Z i).1, hZ⟩ ≤ ⨆ i, chartIdealAt B S hS Y he (Z i) := by
  let K := ⨆ i, chartIdealAt B S hS Y he (Z i)
  let U := chartOfSurjectiveEtale B S hS Y he
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj U.1.left) :=
    inferInstanceAs (IsAffine ((BigFppfOver.toScheme B S hS).obj V))
  have hK := ker_Γ_idealChartι B S hS K
  have hmem : U.1.hom.app (op (idealChart B S hS K)) (idealChartι B S hS K) ∈
      (⨅ i, (Z i).1).obj (op (idealChart B S hS K)) := by
    rw [Subfunctor.iInf_obj, Set.mem_iInter]
    exact fun i => (mem_obj_iff_definingIdealAt_le B S hS Y (Z i) U (idealChartι B S hS K)).2
      ((le_iSup (fun j => chartIdealAt B S hS Y he (Z j)) i).trans hK.ge)
  exact ((mem_obj_iff_definingIdealAt_le B S hS Y ⟨⨅ i, (Z i).1, hZ⟩ U
    (idealChartι B S hS K)).1 hmem).trans hK.le

variable {R : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj R)]
  {t s : R ⟶ V}

/-- **The extension of the chart ideal along a morphism of charts** `q : R ⟶ V` is the chart ideal
of `Z` on the chart `R ⟶ V ⟶ Y`. -/
theorem map_chartIdealAt_eq_ideal_chartKer (Z : ClosedSubspaces B S hS Y.1) (q : R ⟶ V) :
    (chartIdealAt B S hS Y he Z).map ((BigFppfOver.toScheme B S hS).map q).appTop.hom =
      (chartKer B S hS Y Z (yoneda.map q ≫ φ)).ideal
        ⟨⊤, (isAffineOpen_top _ : IsAffineOpen _)⟩ := by
  rw [← comap_chartKer B S hS Y Z φ q _ rfl, Stacks.Divisors.ideal_comap_appLE _ _ ⊤
    (isAffineOpen_top _) ⊤ (isAffineOpen_top _) le_top, chartIdealAt_eq_ideal_chartKer]
  exact congrArg (fun f => Ideal.map (CommRingCat.Hom.hom f) _)
    (Scheme.Hom.appLE_top_top _ _).symm

/-- **The chart ideal extends to the same ideal of `Γ(R)` along both projections.** Both
extensions are the chart ideal of `Z` on the chart `R ⟶ Y`, through `t` and through `s`, which
agree because `t` and `s` have the same composite with `φ`. -/
theorem map_chartIdealAt_eq (hts : yoneda.map t ≫ φ = yoneda.map s ≫ φ)
    (Z : ClosedSubspaces B S hS Y.1) :
    (chartIdealAt B S hS Y he Z).map ((BigFppfOver.toScheme B S hS).map t).appTop.hom =
      (chartIdealAt B S hS Y he Z).map ((BigFppfOver.toScheme B S hS).map s).appTop.hom := by
  rw [map_chartIdealAt_eq_ideal_chartKer, map_chartIdealAt_eq_ideal_chartKer, hts]

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj R)] in
/-- **A quasi-compact separated algebraic space has an affine surjective étale chart with affine
relation.** There is an affine scheme `V` with a surjective étale `φ : V ⟶ Y` (Stacks 03H6), and
`R = V ×_Y V` is affine because `Y` is separated. -/
theorem exists_affine_chart_affine_relation (hZ : B.Contains (⊤_ Scheme.{u}))
    (hYqc : IsQuasiCompactSpace B S hS Y.1) (hYsep : IsAbsolutelySeparated B S hS hZ Y.1) :
    ∃ (V R : BigFppfOver B S hS) (φ : yoneda.obj V ⟶ Y.1) (t s : R ⟶ V),
      IsAffine ((BigFppfOver.toScheme B S hS).obj V) ∧
      IsAffine ((BigFppfOver.toScheme B S hS).obj R) ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ ∧
      IsPullback (yoneda.map t) (yoneda.map s) φ φ := by
  obtain ⟨U, f, het, hsurj⟩ := exists_affine_isSurjective_etaleChart B S hS Y.1 Y.2 hYqc
  have het' : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) f := het
  have hU : IsAffine ((BigFppfOver.toScheme B S hS).obj ((BigAffineFppf.inclusion B S hS).obj U)) :=
    U.2
  have hpb := het'.rep.isPullback' f
  exact ⟨_, _, f, het'.rep.fst' f, het'.rep.snd f, hU,
    isAffine_of_isAbsolutelySeparated B S hS hZ hYsep hpb hU hU,
    (surjective_iff_surjective_pointsMap B S hS Y.1 Y.2 _ f).2 hsurj, het', hpb⟩

/-! ### The chart of a closed subspace -/

section ClosedChart

variable (hsurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ)
  (hts : yoneda.map t ≫ φ = yoneda.map s ≫ φ)

/-- **The chart data of a closed subspace.** For a closed subspace `Z` of `Y`, an affine
surjective étale chart `V' ⟶ Z` with affine relation `R' = V' ×_Z V'`, whose rings of global
functions are `C ⧸ K_Z` and `E ⧸ K_Z E`, compatibly with the two projections. -/
structure ClosedChartData (Z : ClosedSubspaces B S hS Y.1) where
  /-- The chart of `Z`. -/
  V' : BigFppfOver B S hS
  /-- The relation of the chart of `Z`. -/
  R' : BigFppfOver B S hS
  /-- The chart of `Z` is affine. -/
  isAffine_V' : IsAffine ((BigFppfOver.toScheme B S hS).obj V')
  /-- The relation of the chart of `Z` is affine. -/
  isAffine_R' : IsAffine ((BigFppfOver.toScheme B S hS).obj R')
  /-- The chart map. -/
  f : yoneda.obj V' ⟶ Z.1.toFunctor
  /-- The chart map is surjective. -/
  surj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) f
  /-- The chart map is étale. -/
  etale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) f
  /-- The first projection of the relation. -/
  t'' : R' ⟶ V'
  /-- The second projection of the relation. -/
  s'' : R' ⟶ V'
  /-- The relation is the kernel pair of the chart map. -/
  isPullback : IsPullback (yoneda.map t'') (yoneda.map s'') f f
  /-- The global functions of the chart. -/
  eV : Γ((BigFppfOver.toScheme B S hS).obj V', ⊤) ≃+*
    Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) ⧸ chartIdealAt B S hS Y he Z
  /-- The global functions of the relation. -/
  eR : Γ((BigFppfOver.toScheme B S hS).obj R', ⊤) ≃+*
    Γ((BigFppfOver.toScheme B S hS).obj R, ⊤) ⧸
      (chartIdealAt B S hS Y he Z).map ((BigFppfOver.toScheme B S hS).map s).appTop.hom
  /-- `eV` and `eR` are compatible with the second projection. -/
  eR_s : ∀ x, eR (((BigFppfOver.toScheme B S hS).map s'').appTop.hom x) =
    Stacks.AffineStageCore.sBar ((BigFppfOver.toScheme B S hS).map s).appTop.hom _ (eV x)
  /-- `eV` and `eR` are compatible with the first projection. -/
  eR_t : ∀ x, eR (((BigFppfOver.toScheme B S hS).map t'').appTop.hom x) =
    Stacks.AffineStageCore.tBar ((BigFppfOver.toScheme B S hS).map s).appTop.hom
      ((BigFppfOver.toScheme B S hS).map t).appTop.hom _ (map_chartIdealAt_eq Y he hts Z) (eV x)

variable {Y he} (hR : IsPullback (yoneda.map t) (yoneda.map s) φ φ)

/-- Pullback of global functions along a closed immersion into an affine scheme identifies the
global functions of the source with those of the target modulo the kernel. -/
noncomputable def appTopQuotientEquiv {X W : Scheme.{u}} [IsAffine W] (i : X ⟶ W)
    [_root_.AlgebraicGeometry.IsClosedImmersion i] (K : Ideal Γ(W, ⊤))
    (hK : RingHom.ker i.appTop.hom = K) :
    Γ(X, ⊤) ≃+* Γ(W, ⊤) ⧸ K :=
  (RingHom.quotientKerEquivOfSurjective
    (_root_.AlgebraicGeometry.IsClosedImmersion.isAffine_surjective_of_isAffine i).2).symm.trans
    (Ideal.quotEquivOfEq hK)

/-- `appTopQuotientEquiv` sends the pullback of a global function `c` of the target to the class
of `c` modulo the kernel. -/
theorem appTopQuotientEquiv_appTop {X W : Scheme.{u}} [IsAffine W] (i : X ⟶ W)
    [_root_.AlgebraicGeometry.IsClosedImmersion i] (K : Ideal Γ(W, ⊤))
    (hK : RingHom.ker i.appTop.hom = K) (c : Γ(W, ⊤)) :
    appTopQuotientEquiv i K hK (i.appTop.hom c) = Ideal.Quotient.mk K c := by
  rw [appTopQuotientEquiv, RingEquiv.trans_apply]
  have : (RingHom.quotientKerEquivOfSurjective
      (_root_.AlgebraicGeometry.IsClosedImmersion.isAffine_surjective_of_isAffine i).2).symm
      (i.appTop.hom c) = Ideal.Quotient.mk _ c :=
    (RingEquiv.symm_apply_eq _).2 rfl
  rw [this]
  rfl

/-- The kernel of global sections of the base change `V ×_Y Z ⟶ V` of a chart `φ'` is the ideal
of global functions of `chartKer`. -/
private theorem ker_appTop_snd_eq_ideal_chartKer (Z : ClosedSubspaces B S hS Y.1)
    {W : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj W)]
    (φ' : yoneda.obj W ⟶ Y.1) :
    RingHom.ker ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd φ')).appTop.hom =
      (chartKer B S hS Y Z φ').ideal ⟨⊤, (isAffineOpen_top _ : IsAffineOpen _)⟩ := by
  rw [chartKer, Scheme.Hom.ker_apply]
  rfl

include hsurj hR in
/-- **Every closed subspace has chart data**: the base change `V' = V ×_Y Z` of the chart, with
relation `R' = R ×_Y Z`. -/
theorem nonempty_closedChartData (Z : ClosedSubspaces B S hS Y.1) :
    Nonempty (ClosedChartData Y he hR.w Z) := by
  let G := BigFppfOver.toScheme B S hS
  let hrep := Z.2.2.rep
  let V' := hrep.pullback φ
  let vZ : V' ⟶ V := hrep.snd φ
  let f : yoneda.obj V' ⟶ Z.1.toFunctor := hrep.fst φ
  let R' := hrep.pullback (yoneda.map s ≫ φ)
  let rZ : R' ⟶ R := hrep.snd (yoneda.map s ≫ φ)
  let fR : yoneda.obj R' ⟶ Z.1.toFunctor := hrep.fst (yoneda.map s ≫ φ)
  have h1 : IsPullback f (yoneda.map vZ) Z.1.ι φ := hrep.isPullback φ
  have h2 : IsPullback fR (yoneda.map rZ) Z.1.ι (yoneda.map s ≫ φ) := hrep.isPullback _
  have hcs : fR ≫ Z.1.ι = yoneda.map (rZ ≫ s) ≫ φ := by
    rw [h2.w, Functor.map_comp, Category.assoc]
  have hct : fR ≫ Z.1.ι = yoneda.map (rZ ≫ t) ≫ φ := by
    rw [h2.w, Functor.map_comp, Category.assoc, hR.w]
  let s'' : R' ⟶ V' := hrep.lift fR (rZ ≫ s) hcs
  let t'' : R' ⟶ V' := hrep.lift fR (rZ ≫ t) hct
  have hs''f : yoneda.map s'' ≫ f = fR := hrep.lift_fst _ _ _
  have ht''f : yoneda.map t'' ≫ f = fR := hrep.lift_fst _ _ _
  have hs''v : s'' ≫ vZ = rZ ≫ s := hrep.lift_snd _ _ _
  have ht''v : t'' ≫ vZ = rZ ≫ t := hrep.lift_snd _ _ _
  -- the relation square
  have hQ : IsPullback (yoneda.map rZ) (yoneda.map s'') (yoneda.map s) (yoneda.map vZ) := by
    refine IsPullback.of_bot (h₂₁ := yoneda.map vZ) (v₂₁ := f) (v₂₂ := φ) (h₃₁ := Z.1.ι) ?_ ?_
      h1.flip
    · rw [hs''f]
      exact h2.flip
    · rw [← Functor.map_comp, ← Functor.map_comp, hs''v]
  have hrect := hQ.paste_horiz hR
  have hpb : IsPullback (yoneda.map t'') (yoneda.map s'') f f := by
    refine IsPullback.of_right (h₁₂ := yoneda.map vZ) (v₁₃ := φ) (h₂₂ := Z.1.ι) ?_ ?_ h1.flip
    · rw [← Functor.map_comp, ht''v, Functor.map_comp, h1.w]
      exact hrect
    · rw [ht''f, hs''f]
  -- affineness and rings
  have : _root_.AlgebraicGeometry.IsClosedImmersion (G.map vZ) :=
    isClosedImmersion_rep_snd B S hS Y Z φ
  have : _root_.AlgebraicGeometry.IsClosedImmersion (G.map rZ) :=
    isClosedImmersion_rep_snd B S hS Y Z _
  have hV' : IsAffine (G.obj V') :=
    (_root_.AlgebraicGeometry.IsClosedImmersion.isAffine_surjective_of_isAffine (G.map vZ)).1
  have hR' : IsAffine (G.obj R') :=
    (_root_.AlgebraicGeometry.IsClosedImmersion.isAffine_surjective_of_isAffine (G.map rZ)).1
  have hkerV : RingHom.ker (G.map vZ).appTop.hom = chartIdealAt B S hS Y he Z :=
    (ker_appTop_snd_eq_ideal_chartKer Z φ).trans (chartIdealAt_eq_ideal_chartKer Y he Z).symm
  have hkerR : RingHom.ker (G.map rZ).appTop.hom =
      (chartIdealAt B S hS Y he Z).map (G.map s).appTop.hom :=
    (ker_appTop_snd_eq_ideal_chartKer Z _).trans
      (map_chartIdealAt_eq_ideal_chartKer Y he Z s).symm
  let eV := appTopQuotientEquiv (G.map vZ) _ hkerV
  let eR := appTopQuotientEquiv (G.map rZ) _ hkerR
  have hcomp (q : R' ⟶ V') (q' : R ⟶ V) (hq : q ≫ vZ = rZ ≫ q') (h) (x : Γ(G.obj V', ⊤)) :
      eR ((G.map q).appTop.hom x) =
        Ideal.quotientMap _ (G.map q').appTop.hom h (eV x) := by
    obtain ⟨c, rfl⟩ :=
      (_root_.AlgebraicGeometry.IsClosedImmersion.isAffine_surjective_of_isAffine (G.map vZ)).2 x
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, ← Functor.map_comp, hq,
      Functor.map_comp, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      appTopQuotientEquiv_appTop, appTopQuotientEquiv_appTop]
    rfl
  exact ⟨⟨V', R', hV', hR', f, presheaf_of_isPullback B S hS h1.flip hsurj,
    presheaf_of_isPullback B S hS h1.flip he, t'', s'', hpb, eV, eR,
    hcomp s'' s hs''v _, hcomp t'' t ht''v _⟩⟩

end ClosedChart

/-! ### The rings of a chart of an affine algebraic space -/

section AffineChart

/-- **The rings of an affine chart of an affine algebraic space.** Let `F` be an affine algebraic
space with an affine surjective étale chart `f : V ⟶ F` and relation `R = V ×_F V`, with
projections `t, s`. Then with `A = Γ(F)` the ring map `A → Γ(V)` is étale and faithfully flat, and
`Γ(V) ⊗_A Γ(V) → Γ(R)`, `x ⊗ y ↦ s^*x · t^*y`, is bijective. -/
theorem exists_etale_faithfullyFlat_bijective_tensorLift {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAffineSpace B S hS F) {V R : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj R)]
    (f : yoneda.obj V ⟶ F)
    (hsurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) f)
    (het : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) f)
    {t s : R ⟶ V} (hR : IsPullback (yoneda.map t) (yoneda.map s) f f) :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra A Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)),
      Algebra.Etale A Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) ∧
      Module.FaithfullyFlat A Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) ∧
      ∃ hst : ((BigFppfOver.toScheme B S hS).map s).appTop.hom.comp
          (algebraMap A Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) =
        ((BigFppfOver.toScheme B S hS).map t).appTop.hom.comp
          (algebraMap A Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)),
      Function.Bijective (Stacks.AffineStageCore.tensorLift
        ((BigFppfOver.toScheme B S hS).map s).appTop.hom
        ((BigFppfOver.toScheme B S hS).map t).appTop.hom hst) := by
  let G := BigFppfOver.toScheme B S hS
  obtain ⟨T, hT, ⟨e⟩⟩ := hF
  let a : V ⟶ T := yoneda.preimage (f ≫ e.hom)
  have ha : yoneda.map a = f ≫ e.hom := yoneda.map_preimage _
  have hsq : IsPullback (𝟙 (yoneda.obj V)) (yoneda.map a) f e.inv :=
    IsPullback.of_horiz_isIso ⟨by rw [ha, Category.assoc, e.hom_inv_id, Category.comp_id,
      Category.id_comp]⟩
  have hEt : Etale (G.map a) :=
    (presheaf_yoneda_map_iff B S hS inferInstance a).1 (presheaf_of_isPullback B S hS hsq het)
  have hSu : Surjective (G.map a) :=
    (presheaf_yoneda_map_iff B S hS inferInstance a).1 (presheaf_of_isPullback B S hS hsq hsurj)
  let : Algebra Γ(G.obj T, ⊤) Γ(G.obj V, ⊤) := (G.map a).appTop.hom.toAlgebra
  -- the cartesian square of schemes
  have hpbY : IsPullback (yoneda.map s) (yoneda.map t) (yoneda.map a) (yoneda.map a) :=
    hR.flip.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) e (by simp) (by simp) (by simp [ha])
      (by simp [ha])
  have hpbC : IsPullback s t a a := hpbY.of_map_of_faithful yoneda
  have _ : PreservesLimitsOfShape WalkingCospan G :=
    preservesLimitsOfShape_walkingCospan_toScheme B S hS
  have hpbS : IsPullback (G.map s) (G.map t) (G.map a) (G.map a) := hpbC.map G
  have hpo := isPushout_appTop_of_isPullback hpbS
  have hst : (G.map s).appTop.hom.comp (algebraMap Γ(G.obj T, ⊤) Γ(G.obj V, ⊤)) =
      (G.map t).appTop.hom.comp (algebraMap Γ(G.obj T, ⊤) Γ(G.obj V, ⊤)) := by
    have hw : G.map s ≫ G.map a = G.map t ≫ G.map a := by
      rw [← G.map_comp, ← G.map_comp, hpbC.w]
    have := congrArg (fun m => (Scheme.Hom.appTop m).hom) hw
    show (G.map s).appTop.hom.comp (G.map a).appTop.hom =
      (G.map t).appTop.hom.comp (G.map a).appTop.hom
    simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp] using this
  refine ⟨Γ(G.obj T, ⊤), inferInstance, inferInstance, ?_, ?_, hst, ?_⟩
  · exact HasRingHomProperty.appTop (P := @Etale) _ hEt
  · have hFF : (G.map a).appTop.hom.FaithfullyFlat := by
      rw [← flat_and_surjective_SpecMap_iff]
      exact ⟨(HasRingHomProperty.Spec_iff (P := @Flat)).2 (Scheme.Hom.flat_appTop (G.map a)),
        (MorphismProperty.arrow_mk_iso_iff (P := @Surjective)
          (arrowIsoSpecΓOfIsAffine (G.map a))).1 hSu⟩
    exact hFF
  · have htp := CommRingCat.isPushout_tensorProduct Γ(G.obj T, ⊤) Γ(G.obj V, ⊤) Γ(G.obj V, ⊤)
    let i := htp.isoIsPushout _ _ hpo
    have hL := htp.inl_isoIsPushout_hom _ _ hpo
    have hRr := htp.inr_isoIsPushout_hom _ _ hpo
    have heq : ∀ x, Stacks.AffineStageCore.tensorLift (G.map s).appTop.hom (G.map t).appTop.hom
        hst x = i.hom.hom x := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul d d' =>
        rw [Stacks.AffineStageCore.tensorLift_tmul]
        have h1 : d ⊗ₜ[Γ(G.obj T, ⊤)] d' =
            (Algebra.TensorProduct.includeLeftRingHom (R := Γ(G.obj T, ⊤))
              (A := Γ(G.obj V, ⊤)) (B := Γ(G.obj V, ⊤)) d) *
            (Algebra.TensorProduct.includeRight (R := Γ(G.obj T, ⊤))
              (A := Γ(G.obj V, ⊤)) (B := Γ(G.obj V, ⊤)) d') := by
          simp
        rw [h1, map_mul]
        congr 1
        · exact (ConcreteCategory.congr_hom hL d).symm
        · exact (ConcreteCategory.congr_hom hRr d').symm
      | add x y hx hy => rw [map_add, map_add, hx, hy]
    exact funext heq ▸ ConcreteCategory.bijective_of_isIso i.hom

end AffineChart

/-! ### The rings of the chart of an affine closed subspace -/

section AffineClosed

variable {Y he} {t s : R ⟶ V} (hts : yoneda.map t ≫ φ = yoneda.map s ≫ φ)

/-- **The chart rings of an affine closed subspace.** Let `Z ⊆ Y` be a closed subspace which is an
affine algebraic space, with chart data `D`. Then there is a ring `A` (the global functions of
`Z`) with an étale, faithfully flat ring map `A → C ⧸ K_Z` such that
`(C ⧸ K_Z) ⊗_A (C ⧸ K_Z) → E ⧸ K_Z E`, `x ⊗ y ↦ s̄(x) · t̄(y)`, is bijective. This is the input
of the proof of Stacks 07SQ for a directed system of closed subspaces with affine intersection. -/
theorem exists_effective_of_isAffineSpace {Z : ClosedSubspaces B S hS Y.1}
    (D : ClosedChartData Y he hts Z) (hZ : IsAffineSpace B S hS Z.1.toFunctor) :
    ∃ (A : Type u) (_ : CommRing A)
      (_ : Algebra A (Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) ⧸ chartIdealAt B S hS Y he Z)),
      Algebra.Etale A (Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) ⧸ chartIdealAt B S hS Y he Z) ∧
      Module.FaithfullyFlat A
        (Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) ⧸ chartIdealAt B S hS Y he Z) ∧
      ∃ hst : (Stacks.AffineStageCore.sBar ((BigFppfOver.toScheme B S hS).map s).appTop.hom
            (chartIdealAt B S hS Y he Z)).comp (algebraMap A _) =
          (Stacks.AffineStageCore.tBar ((BigFppfOver.toScheme B S hS).map s).appTop.hom
            ((BigFppfOver.toScheme B S hS).map t).appTop.hom (chartIdealAt B S hS Y he Z)
            (map_chartIdealAt_eq Y he hts Z)).comp (algebraMap A _),
        Function.Bijective (Stacks.AffineStageCore.tensorLift
          (Stacks.AffineStageCore.sBar ((BigFppfOver.toScheme B S hS).map s).appTop.hom
            (chartIdealAt B S hS Y he Z))
          (Stacks.AffineStageCore.tBar ((BigFppfOver.toScheme B S hS).map s).appTop.hom
            ((BigFppfOver.toScheme B S hS).map t).appTop.hom (chartIdealAt B S hS Y he Z)
            (map_chartIdealAt_eq Y he hts Z)) hst) := by
  let G := BigFppfOver.toScheme B S hS
  have := D.isAffine_V'
  have := D.isAffine_R'
  obtain ⟨A, _, _, hEt, hFF, hst₀, hbij⟩ :=
    exists_etale_faithfullyFlat_bijective_tensorLift hZ D.f D.surj D.etale D.isPullback
  let σ := Stacks.AffineStageCore.sBar (G.map s).appTop.hom (chartIdealAt B S hS Y he Z)
  let τ := Stacks.AffineStageCore.tBar (G.map s).appTop.hom (G.map t).appTop.hom
    (chartIdealAt B S hS Y he Z) (map_chartIdealAt_eq Y he hts Z)
  let : Algebra A (Γ(G.obj V, ⊤) ⧸ chartIdealAt B S hS Y he Z) :=
    ((D.eV : Γ(G.obj D.V', ⊤) →+* _).comp (algebraMap A Γ(G.obj D.V', ⊤))).toAlgebra
  let eA : Γ(G.obj D.V', ⊤) ≃ₐ[A] (Γ(G.obj V, ⊤) ⧸ chartIdealAt B S hS Y he Z) :=
    { D.eV with commutes' := fun _ => rfl }
  have hσ : ∀ y, σ (D.eV y) = D.eR ((G.map D.s'').appTop.hom y) := fun y => (D.eR_s y).symm
  have hτ : ∀ y, τ (D.eV y) = D.eR ((G.map D.t'').appTop.hom y) := fun y => (D.eR_t y).symm
  have hst : σ.comp (algebraMap A _) = τ.comp (algebraMap A _) := by
    ext a
    show σ (D.eV (algebraMap A _ a)) = τ (D.eV (algebraMap A _ a))
    rw [hσ, hτ]
    exact congrArg D.eR (congrArg (fun g : A →+* _ => g a) hst₀)
  refine ⟨A, inferInstance, inferInstance, Algebra.Etale.of_equiv eA,
    Module.FaithfullyFlat.of_linearEquiv _ _ eA.symm.toLinearEquiv, hst, ?_⟩
  let T := Algebra.TensorProduct.congr eA eA
  have heq : ∀ x, Stacks.AffineStageCore.tensorLift σ τ hst x =
      D.eR (Stacks.AffineStageCore.tensorLift (G.map D.s'').appTop.hom
        (G.map D.t'').appTop.hom hst₀ (T.symm x)) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      obtain ⟨x, rfl⟩ := eA.surjective x
      obtain ⟨y, rfl⟩ := eA.surjective y
      have hT : T.symm (eA x ⊗ₜ eA y) = x ⊗ₜ y := by
        rw [AlgEquiv.symm_apply_eq]
        rfl
      rw [hT, Stacks.AffineStageCore.tensorLift_tmul, Stacks.AffineStageCore.tensorLift_tmul,
        map_mul]
      exact congrArg₂ (· * ·) (hσ x) (hτ y)
    | add x y hx hy =>
      simp only [map_add, hx, hy]
  rw [show (⇑(Stacks.AffineStageCore.tensorLift σ τ hst)) =
      ⇑D.eR ∘ ⇑(Stacks.AffineStageCore.tensorLift (G.map D.s'').appTop.hom
        (G.map D.t'').appTop.hom hst₀) ∘ ⇑T.symm from funext heq]
  exact D.eR.bijective.comp (hbij.comp T.symm.bijective)

end AffineClosed

end AlgebraicGeometry.Space

end
