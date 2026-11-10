/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Quot.QuotHilbertPolynomialProjectiveEmbedding
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertyRelativeAmple
public import StacksFrontier.AlgebraicGeometry.StalkwiseGeneration.Ample
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AmpleFormalSystemEmbeddedTuple
public import StacksFrontier.AlgebraicGeometry.Spaces.ClopenLiftOverHenselianPair
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedTwistedCohomology
public import StacksFrontier.AlgebraicGeometry.PowerFamilyBridge.Ample
public import StacksFrontier.AlgebraicGeometry.PushforwardCoherent
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.PushforwardAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedFiniteTypeOnCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedChartPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionReadingsFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionFromSite
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQuasicoherentPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.AffinePushforwardQuasicoherentUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.InvertibleQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuotOverSpace.BaseReading
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuotOverSpace.TwistingModule
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.Vanishing

/-!
# `Quot^P` for a relatively ample invertible module: the reduction to `ℙⁿ`

Let `f : X ⟶ B` be a proper morphism of finite presentation of algebraic spaces over `Spec ℤ`, `F`
a quasi-coherent `𝒪_X`-module of finite type, `L` an invertible `𝒪_X`-module ample on `X/B`
(Stacks 0D31) and `P` a numerical polynomial.  The proof of Stacks 0DPC reduces the properness of
`Quot^P_{F/X/B} ⟶ B` to affine `B` (Stacks 083R), embeds `X` into `ℙⁿ_B` with `𝒪(1)` restricting
to a power `L^{⊗ d}` (Stacks 01VS), replaces `(L, P(t))` by `(L^{⊗ d}, P(dt))` (Stacks 0DP8) and
transports `Quot^P` along the embedding (Stacks 0DP4) to `ℙⁿ_B`, where Stacks 0DPB applies.

This file carries out every step except the last, over each affine scheme `W` over `B`:

* the base change `X_W` is the algebraic space of a scheme `U`, since a relatively ample `L`
  makes `f` representable; `L_U` is ample (Stacks 01VK) and `U ⟶ W` is proper, so Stacks 01VS
  gives a closed immersion `i : U ⟶ ℙⁿ_W` over `W` with `L_U^{⊗ d} ≅ i^*𝒪(1)`;
* the comparison of `L_U^{⊗ d}` with the inverse image of `𝒪(1)` along the morphism of algebraic
  spaces `h_U ⟶ h_W × ℙⁿ_ℤ` is made on the Zariski site of `U` (Stacks 03DX), where tensor
  powers and inverse images are those of schemes;
* the direct image of `F_W` to `h_W × ℙⁿ_ℤ` is quasi-coherent of finite type, a closed immersion
  being finite.

## Main results

* `exists_closedImmersion_projectiveSite_of_isRelativelyAmple`: the projective embedding of a
  relatively ample affine base change (Stacks 01VS).
* `isRepresentedProper_canonicalBaseChanged_of_projectiveChart`: `Quot^{P, L_W}_{F_W/X_W/W}`
  is represented by a scheme proper over `W` once the corresponding `Quot` on `W × ℙⁿ` is.
* `isProperAlgebraicSpaceOver_hilbertPolynomialQuot_of_isRelativelyAmple_of_projective`: the
  proof of Stacks 0DPC from the affine case of Stacks 0DPB.

## References

* [Stacks Project, Tag 0DPC](https://stacks.math.columbia.edu/tag/0DPC)
* [Stacks Project, Tag 0DPB](https://stacks.math.columbia.edu/tag/0DPB)
* [Stacks Project, Tag 01VS](https://stacks.math.columbia.edu/tag/01VS)
* [Stacks Project, Tag 0DP4](https://stacks.math.columbia.edu/tag/0DP4)
* [Stacks Project, Tag 0DP8](https://stacks.math.columbia.edu/tag/0DP8)
* [Stacks Project, Tag 083R](https://stacks.math.columbia.edu/tag/083R)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.Space.QuotSituation

open ProjectiveQuot ProjectiveQuotOverSpace Stacks.AmpleProjectiveImmersion

variable {B : BigFppfSite.{u}}

local notation "ℤS" => B.contains_integerBase

local notation "𝒯" => BigFppfOver.toScheme B integerBase B.contains_integerBase

/-- **Stacks 01VS for a relatively ample affine base change.**  For `f : X ⟶ Y` proper, `L`
ample on `X/Y` and a cartesian square exhibiting `X ×_Y W` as a scheme `U` over an affine scheme
`W`, the reading `L_U` of `L` on `U` is invertible and some power `L_U^{⊗ d}`, `d ≥ 1`, is the
inverse image of `𝒪(1)` along a closed immersion `U ⟶ ℙⁿ_W` over `W`. -/
theorem exists_closedImmersion_projectiveSite_of_isRelativelyAmple
    {X Y : AlgebraicSpaces B integerBase ℤS} {f : X ⟶ Y} (hf : IsProper B integerBase ℤS f.hom)
    {L : Modules.{u, u} B integerBase ℤS X.1 X.2} (hL : IsRelativelyAmple B integerBase ℤS f L)
    (W U : BigFppfOver B integerBase ℤS) (hW : IsAffine ((𝒯).obj W))
    (ξ : yoneda.obj W ⟶ Y.1) (p : yoneda.obj U ⟶ X.1) (q : U ⟶ W)
    (hsq : IsPullback p (yoneda.map q) f.hom ξ) :
    ∃ _ : Stacks.Ample.IsInvertibleModule ((𝒯).obj U) (baseChangeModule B integerBase ℤS L U p),
      ∃ (n : ℕ) (d : ℕ) (_ : 1 ≤ d) (i : U ⟶ projectiveSite B n W),
        _root_.AlgebraicGeometry.IsClosedImmersion ((𝒯).map i) ∧
        i ≫ projectiveSiteStructure B n W = q ∧
        Nonempty (Stacks.Ample.tensorPowModule ((𝒯).obj U)
            (baseChangeModule B integerBase ℤS L U p) (d : ℤ) ≅
          (Scheme.Modules.pullback ((𝒯).map i)).obj
            (projectiveSpaceTwistingSheaf n ((𝒯).obj W))) := by
  obtain ⟨hinv, hamp⟩ := isAmple_baseChangeModule_of_isRelativelyAmple hL W U hW ξ p q hsq
  have hsq' := isPullback_homMk B integerBase ℤS X.2 (isAlgebraicSpace_yoneda B integerBase ℤS W)
    Y.2 (isAlgebraicSpace_yoneda B integerBase ℤS U) hsq
  have hq' : _root_.AlgebraicGeometry.IsProper ((𝒯).map q) :=
    (isProper_yoneda_map_iff B integerBase ℤS q).1
      ((isProper_isStableUnderBaseChange B integerBase ℤS).of_isPullback hsq' hf)
  obtain ⟨d₀, hd₀, h⟩ := Stacks.StalkwiseGeneration.exists_immersion_projectiveSpaceOver_of_isAmple
    ((𝒯).map q) _ hamp
  obtain ⟨n, i, hi, hover, ⟨e⟩⟩ := h d₀ le_rfl
  have hci : _root_.AlgebraicGeometry.IsClosedImmersion i :=
    Stacks.AmpleFormalSystemEmbeddedTuple.isClosedImmersion_of_isImmersion_over i hi hover
  refine ⟨hinv, n, d₀, hd₀, CurveFamily.homOfScheme i, hci, ?_, ⟨e⟩⟩
  exact (𝒯).map_injective (by rwa [Functor.map_comp])

/-! ### The identification `h_{ℙⁿ_W} ≅ h_W × ℙⁿ_ℤ` -/

/-- `h_W × ℙⁿ_ℤ ⟶ h_W` is the base change of `ℙⁿ_ℤ ⟶ Spec ℤ` along `h_W ⟶ Spec ℤ`. -/
theorem isPullback_productSpace_schemeSpace (n : ℕ) (W : BigFppfOver B integerBase ℤS) :
    IsPullback (productFst n (schemeSpace W)) (productSnd n (schemeSpace W))
      (quotSituation B n 0).f (schemeSpaceMap (toSiteBase B W)) := by
  have h : toBaseSpace (schemeSpace W) = schemeSpaceMap (toSiteBase B W) := Subsingleton.elim _ _
  rw [← h]
  exact isPullback_productSpace n (schemeSpace W)

/-- The algebraic space of `ℙⁿ_W` is the product `h_W × ℙⁿ_ℤ` of Stacks 0DPB: both are base
changes of `ℙⁿ_ℤ ⟶ Spec ℤ` along `W ⟶ Spec ℤ`. -/
def projectiveSiteProductIso (n : ℕ) (W : BigFppfOver B integerBase ℤS) :
    schemeSpace (projectiveSite B n W) ≅ productSpace n (schemeSpace W) :=
  (isPullback_projectiveSiteSpace (r := 0) W).isoIsPullback _ _
    (isPullback_productSpace_schemeSpace n W)

/-- Under `projectiveSiteProductIso`, the projection `h_W × ℙⁿ_ℤ ⟶ h_W` corresponds to the
structure morphism `ℙⁿ_W ⟶ W`. -/
@[reassoc (attr := simp)]
theorem projectiveSiteProductIso_hom_productSnd (n : ℕ) (W : BigFppfOver B integerBase ℤS) :
    (projectiveSiteProductIso n W).hom ≫ productSnd n (schemeSpace W) =
      schemeSpaceMap (projectiveSiteStructure B n W) := by
  unfold projectiveSiteProductIso
  exact IsPullback.isoIsPullback_hom_snd _ _ _ _

/-! ### The Zariski reading on a represented algebraic space -/

/-- The associated module of Stacks 03DU on the small étale site of `U`, read on `h_U`: the left
adjoint of the Zariski reading `AlgebraicGeometry.Space.representedZariskiModule`. -/
abbrev associatedSpaceModule (U : BigFppfOver B integerBase ℤS) :
    ((𝒯).obj U).Modules ⥤
      Modules.{u, u} B integerBase ℤS (yoneda.obj U) (isAlgebraicSpace_yoneda B integerBase ℤS U) :=
  _root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B) ((𝒯).obj U)
      U.left.property ⋙
    (representedSpaceModulesEquivalence B integerBase ℤS U).functor

/-- A quasi-coherent module on `h_U` is the associated module of its Zariski reading
(Stacks 03DX). -/
def associatedSpaceModuleReadingIso (U : BigFppfOver B integerBase ℤS)
    (N : Modules.{u, u} B integerBase ℤS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B integerBase ℤS U))
    (hN : N.IsQuasicoherentOnSite) :
    (associatedSpaceModule U).obj (representedZariskiModule B integerBase ℤS U N) ≅ N :=
  @asIso _ _ _ _ ((zariskiAdjunction B U).counit.app N) (isIso_zariskiAdjunction_counit_app U N hN)

/-- **The inverse image of the twisting module along a morphism into `ℙⁿ_W`.**  If a
quasi-coherent module `M` on `h_W × ℙⁿ_ℤ` is read on `ℙⁿ_W` as `𝒪(1)`, then its inverse image
along the morphism of algebraic spaces represented by `i : U ⟶ ℙⁿ_W` is the associated module of
`i^*𝒪(1)`. -/
def modulePullbackProjectiveSiteIso {U W : BigFppfOver B integerBase ℤS} {n : ℕ}
    (i : U ⟶ projectiveSite B n W)
    (M : Modules.{u, u} B integerBase ℤS (productSpace n (schemeSpace W)).1
      (productSpace n (schemeSpace W)).2) (hM : M.IsQuasicoherentOnSite)
    (eM : (isoReading (projectiveSiteProductIso n W)).obj M ≅
      projectiveSpaceTwistingSheaf n ((𝒯).obj W)) :
    (modulePullback B integerBase ℤS
        (schemeSpaceMap i ≫ (projectiveSiteProductIso n W).hom)).obj M ≅
      (associatedSpaceModule U).obj
        ((Scheme.Modules.pullback ((𝒯).map i)).obj (projectiveSpaceTwistingSheaf n ((𝒯).obj W))) :=
  let N := (modulePullback B integerBase ℤS (projectiveSiteProductIso n W).hom).obj M
  have hN : N.IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B integerBase ℤS _ M hM
  have hN' : ((modulePullback B integerBase ℤS (representedSpaceMap B integerBase ℤS i)).obj
      N).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B integerBase ℤS _ N hN
  ((modulePullbackCompIso B integerBase ℤS (schemeSpaceMap i)
      (projectiveSiteProductIso n W).hom).app M).symm ≪≫
    (associatedSpaceModuleReadingIso U _ hN').symm ≪≫
    (associatedSpaceModule U).mapIso
      ((representedZariskiModulePullbackIso B integerBase ℤS i
          (Functor.relativelyRepresentable.map yoneda i) N hN).symm ≪≫
        (Scheme.Modules.pullback ((𝒯).map i)).mapIso eM)

/-- **The tensor powers of a quasi-coherent invertible module on `h_U` are the associated modules
of the tensor powers of its reading on `U`** (Stacks 01CU on both sides, Stacks 03DX). -/
def invertibleTensorPowerAssociatedIso (U : BigFppfOver B integerBase ℤS)
    (M₀ : Modules.{u, u} B integerBase ℤS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B integerBase ℤS U))
    [hM₀ : Stacks.SheafOfModules.IsInvertible (structurePresheaf B integerBase ℤS (yoneda.obj U))
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B integerBase ℤS
        (yoneda.obj U) (isAlgebraicSpace_yoneda B integerBase ℤS U)).O)).property M₀]
    (hqc : M₀.IsQuasicoherentOnSite)
    [hN : Stacks.Ample.IsInvertibleModule ((𝒯).obj U)
      (restrictToChartScheme B integerBase ℤS (yoneda.obj U)
        (isAlgebraicSpace_yoneda B integerBase ℤS U) M₀ (idEtaleChart B integerBase ℤS U))]
    (d : ℤ) :
    invertibleTensorPower B integerBase ℤS (yoneda.obj U)
        (isAlgebraicSpace_yoneda B integerBase ℤS U) M₀ d ≅
      (associatedSpaceModule U).obj (Stacks.Ample.tensorPowModule ((𝒯).obj U)
        (restrictToChartScheme B integerBase ℤS (yoneda.obj U)
          (isAlgebraicSpace_yoneda B integerBase ℤS U) M₀ (idEtaleChart B integerBase ℤS U)) d) :=
  let N₀ := restrictToChartScheme B integerBase ℤS (yoneda.obj U)
    (isAlgebraicSpace_yoneda B integerBase ℤS U) M₀ (idEtaleChart B integerBase ℤS U)
  let e₁ : M₀ ≅ (associatedSpaceModule U).obj N₀ :=
    (associatedSpaceModuleReadingIso U M₀ hqc).symm ≪≫
      (associatedSpaceModule U).mapIso
        (restrictToChartSchemeIdEtaleChartIso B integerBase ℤS U M₀).symm
  haveI hΦ := isInvertible_representedSmallEtaleModuleEquivalence_functor_obj_associatedModule
    B integerBase ℤS U N₀ (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ N₀ hN)
  invertibleTensorPowerCongr B integerBase ℤS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B integerBase ℤS U) (hL' := hΦ) e₁ d ≪≫
    (representedAssociatedModuleTensorPowerIso B integerBase ℤS U N₀ d).symm ≪≫
    (associatedSpaceModule U).mapIso
      (Stacks.PowerFamilyBridge.invertibleTensorPowerModuleIso ((𝒯).obj U) N₀ d)

/-- **The direct image along a closed immersion of schemes of a quasi-coherent module of finite
type on the represented algebraic space is of finite type.**  Read on the Zariski site of the
target, the direct image is the scheme-level direct image of the reading, which is of finite type
because a closed immersion is finite; Stacks 03DX carries this back to the small étale site. -/
theorem isFiniteTypeOnSite_modulePushforward_representedSpaceMap
    {U V : BigFppfOver B integerBase ℤS} (g : U ⟶ V)
    [_root_.AlgebraicGeometry.IsClosedImmersion ((𝒯).map g)]
    (F : Modules.{u, u} B integerBase ℤS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B integerBase ℤS U))
    (hqc : F.IsQuasicoherentOnSite) (hft : SheafOfModules.IsFiniteTypeOnSite F) :
    SheafOfModules.IsFiniteTypeOnSite
      ((modulePushforward B integerBase ℤS (representedSpaceMap B integerBase ℤS g)).obj F) := by
  have hci : IsClosedImmersion B integerBase ℤS (representedSpaceMap B integerBase ℤS g).hom :=
    (presheaf_yoneda_map_iff B integerBase ℤS inferInstance g).2 inferInstance
  have hGqc := isQuasicoherentOnSite_modulePushforward_of_isClosedImmersion B integerBase ℤS _ hci
    F hqc
  let N := restrictToChartScheme B integerBase ℤS (yoneda.obj U)
    (isAlgebraicSpace_yoneda B integerBase ℤS U) F (idEtaleChart B integerBase ℤS U)
  have hNqc : N.IsQuasicoherent :=
    isQuasicoherent_restrictToChartScheme B integerBase ℤS (schemeSpace U) F hqc
      (idEtaleChart B integerBase ℤS U)
  have hNft : N.IsFiniteType := Stacks.SheafOfModules.Intrinsic.isFiniteType_of_iso
    (restrictToChartIsoRestrictToChartScheme B integerBase ℤS (G := F)
      (U := idEtaleChart B integerBase ℤS U))
    (isFiniteType_restrictToChart B integerBase ℤS (schemeSpace U) F hqc hft
      (idEtaleChart B integerBase ℤS U))
  let r := _root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) g.left
  have : _root_.AlgebraicGeometry.IsClosedImmersion r := ‹_›
  have hPqc := Stacks.Modules.isQuasicoherent_pushforward_of_isAffineHom r N hNqc
  have hPft := @Stacks.AlgebraicGeometry.PushforwardCoherent.isFiniteType_pushforward_of_isFinite
    _ _ r inferInstance N hNqc hNft
  let e := (associatedSpaceModuleReadingIso V _ hGqc).symm ≪≫
    (associatedSpaceModule V).mapIso
      ((restrictToChartSchemeIdEtaleChartIso B integerBase ℤS V _).symm ≪≫
        restrictToChartSchemePushforwardIdEtaleChartIso' B integerBase ℤS g F)
  exact Stacks.SheafOfModules.FiniteTypeTransport.isFiniteTypeOnSite_of_iso e.symm
    (isFiniteTypeOnSite_representedQuasicoherentSchemeEquivalence B integerBase ℤS V _ hPqc hPft)

/-! ### `Quot^P` over an affine base with a projective embedding of the base change -/

/-- The direct image of a module of finite type along an isomorphism of algebraic spaces is of
finite type. -/
private theorem isFiniteTypeOnSite_modulePushforward_hom {X Y : AlgebraicSpaces B integerBase ℤS}
    (e : X ≅ Y) {G : Modules.{u, u} B integerBase ℤS X.1 X.2}
    (hG : SheafOfModules.IsFiniteTypeOnSite G) :
    SheafOfModules.IsFiniteTypeOnSite ((modulePushforward B integerBase ℤS e.hom).obj G) :=
  Stacks.SheafOfModules.FiniteTypeTransport.isFiniteTypeOnSite_of_iso
    ((modulePushforwardInvIsoModulePullback B integerBase ℤS e.symm).app G).symm
    (isFiniteTypeOnSite_modulePullback B integerBase ℤS e.inv G hG)

/-- **Stacks 0DPC over an affine base, from a projective embedding of the base change.**  Let
`F/X/B` be a Quot situation with `X ⟶ B` separated and `F` of finite type, `L` an invertible
`𝒪_X`-module, and `P` a numerical polynomial.  Let `W` be a scheme over `B` whose base change
`X_W` is the algebraic space of a scheme `U` (the cartesian square `hsq`), and let
`i : U ⟶ ℙⁿ_W` be a closed immersion over `W` with `L_U^{⊗ d} ≅ i^*𝒪(1)` (Stacks 01VS).  Given a
module `M` on `h_W × ℙⁿ_ℤ` read on `ℙⁿ_W` as `𝒪(1)`, if every
`Quot^{P(d·), M}_{G/(W × ℙⁿ)/W}` with `G` quasi-coherent of finite type is represented by a
scheme proper over `W` (the affine case of Stacks 0DPB), then so is `Quot^{P, L_W}_{F_W/X_W/W}`.

The proof transports along `X_W ≅ h_U` (Stacks 0DP4 for an isomorphism), then along the closed
immersion `h_U ⟶ h_W × ℙⁿ_ℤ` with `L` replaced by `L^{⊗ d}` and `P(t)` by `P(dt)` (Stacks 0DP8
and 0DP4); the comparison of `L_U^{⊗ d}` with the inverse image of `M` is read on `U`
(Stacks 03DX). -/
theorem isRepresentedProper_canonicalBaseChanged_of_projectiveChart
    (D : QuotSituation B integerBase ℤS) (hsep : IsSeparated B integerBase ℤS D.f.hom)
    (hFft : SheafOfModules.IsFiniteTypeOnSite D.F)
    (L : Modules.{u, u} B integerBase ℤS D.X.1 D.X.2)
    [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B integerBase ℤS D.X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B integerBase ℤS D.X.1 D.X.2).O)).property L]
    {P : ℤ → ℤ} {p : Polynomial ℚ} (hP : ∀ m : ℤ, p.eval (m : ℚ) = (P m : ℚ))
    (W : BigFppfOver B integerBase ℤS) (ξ : yoneda.obj W ⟶ D.Y.obj)
    (U : BigFppfOver B integerBase ℤS) (x : yoneda.obj U ⟶ D.X.1) (q : U ⟶ W)
    (hsq : IsPullback x (yoneda.map q) D.f.hom ξ)
    [hN : Stacks.Ample.IsInvertibleModule ((𝒯).obj U) (baseChangeModule B integerBase ℤS L U x)]
    (n : ℕ) (d : ℕ) (hd : 1 ≤ d) (i : U ⟶ projectiveSite B n W)
    [hi : _root_.AlgebraicGeometry.IsClosedImmersion ((𝒯).map i)]
    (hiq : i ≫ projectiveSiteStructure B n W = q)
    (e : Stacks.Ample.tensorPowModule ((𝒯).obj U) (baseChangeModule B integerBase ℤS L U x)
        (d : ℤ) ≅
      (Scheme.Modules.pullback ((𝒯).map i)).obj (projectiveSpaceTwistingSheaf n ((𝒯).obj W)))
    (M : Modules.{u, u} B integerBase ℤS (productSpace n (schemeSpace W)).1
      (productSpace n (schemeSpace W)).2)
    [hM : Stacks.SheafOfModules.IsInvertible
      (structurePresheaf B integerBase ℤS (productSpace n (schemeSpace W)).1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B integerBase ℤS
        (productSpace n (schemeSpace W)).1 (productSpace n (schemeSpace W)).2).O)).property M]
    (eM : (isoReading (projectiveSiteProductIso n W)).obj M ≅
      projectiveSpaceTwistingSheaf n ((𝒯).obj W))
    (h : ∀ (G : Modules.{u, u} B integerBase ℤS (productSpace n (schemeSpace W)).1
        (productSpace n (schemeSpace W)).2) (hG : G.IsQuasicoherentOnSite),
      SheafOfModules.IsFiniteTypeOnSite G →
        (situation n (schemeSpace W) G hG).IsRepresentedProper
          ((situation n (schemeSpace W) G hG).hilbertPolynomialQuot M (hL := hM)
            (fun m => P (d * m)))) :
    (D.canonicalBaseChanged
        (ObjectProperty.homMk (Y := D.Y) (X := schemeSpace W) ξ)).IsRepresentedProper
      (@hilbertPolynomialQuot B integerBase ℤS
        (D.canonicalBaseChanged (ObjectProperty.homMk (Y := D.Y) (X := schemeSpace W) ξ))
        ((modulePullback B integerBase ℤS (D.baseChangedSourceProjection
          (ObjectProperty.homMk (Y := D.Y) (X := schemeSpace W) ξ))).obj L)
        (isInvertible_modulePullback B integerBase ℤS (D.baseChangedSourceProjection
          (ObjectProperty.homMk (Y := D.Y) (X := schemeSpace W) ξ)) L) P) := by
  let ξ' : schemeSpace W ⟶ D.Y := ObjectProperty.homMk (Y := D.Y) (X := schemeSpace W) ξ
  let DW := D.canonicalBaseChanged ξ'
  let x' : schemeSpace U ⟶ D.X := ObjectProperty.homMk x
  have hsq' : IsPullback x' (schemeSpaceMap q) D.f ξ' :=
    isPullback_homMk B integerBase ℤS D.X.2 (isAlgebraicSpace_yoneda B integerBase ℤS W) D.Y.2
      (isAlgebraicSpace_yoneda B integerBase ℤS U) hsq
  let ι : DW.X ≅ schemeSpace U :=
    (AlgebraicSpaces.isPullback_fiberProduct B integerBase ℤS D.f ξ').isoIsPullback _ _ hsq'
  have hι₁ : ι.hom ≫ x' = D.baseChangedSourceProjection ξ' :=
    IsPullback.isoIsPullback_hom_fst _ _ _ _
  have hι₂ : ι.hom ≫ schemeSpaceMap q = DW.f := IsPullback.isoIsPullback_hom_snd _ _ _ _
  have : IsIso ι.hom.hom := inferInstance
  have hιci : IsClosedImmersion B integerBase ℤS ι.hom.hom :=
    isClosedImmersion_of_isIso B integerBase ℤS ι.hom.hom
  have hsepW : IsSeparated B integerBase ℤS DW.f.hom :=
    isSeparated_of_isPullback B integerBase ℤS (IsPullback.of_hasPullback D.f.hom ξ'.hom) hsep
  have hsepU : IsSeparated B integerBase ℤS (schemeSpaceMap q).hom :=
    isSeparated_of_isPullback B integerBase ℤS hsq hsep
  let PS : QuotPushforwardSituation B integerBase ℤS :=
    { base := schemeSpace W
      X := DW.X
      Y := schemeSpace U
      π := ι.hom
      structureX := DW.f
      structureY := schemeSpaceMap q
      comp := hι₂
      F := DW.F
      quasicoherent := DW.quasicoherent
      affine := isAffineHom_of_isClosedImmersion B integerBase ℤS ι.hom.hom hιci
      quasiFinite := isQuasiFinite_of_isFinite B integerBase ℤS ι.hom.hom DW.X.2 (schemeSpace U).2
        (isFinite_of_isClosedImmersion B integerBase ℤS ι.hom.hom hιci)
      separatedX := hsepW
      separatedY := hsepU
      finitePresentationX := DW.finitePresentation
      finitePresentationY := (isFinitePresentation_isStableUnderBaseChange B integerBase
        ℤS).of_isPullback hsq' D.finitePresentation }
  let M₀ := (modulePullback B integerBase ℤS x').obj L
  have hM₀ : Stacks.SheafOfModules.IsInvertible
      (structurePresheaf B integerBase ℤS (yoneda.obj U))
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B integerBase ℤS
        (yoneda.obj U) (isAlgebraicSpace_yoneda B integerBase ℤS U)).O)).property M₀ :=
    isInvertible_modulePullback B integerBase ℤS x' L
  have hM₀qc : M₀.IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isInvertible x' L hL
  let κ := projectiveSiteProductIso n W
  let π₁ : schemeSpace U ⟶ productSpace n (schemeSpace W) := schemeSpaceMap i ≫ κ.hom
  have : IsIso κ.hom.hom := inferInstance
  have hπ₁ : IsClosedImmersion B integerBase ℤS π₁.hom :=
    isClosedImmersion_comp B integerBase ℤS (yoneda.map i) κ.hom.hom
      ((presheaf_yoneda_map_iff B integerBase ℤS inferInstance i).2 hi)
      (isClosedImmersion_of_isIso B integerBase ℤS κ.hom.hom)
  have hcomp₁ : π₁ ≫ productSnd n (schemeSpace W) = schemeSpaceMap q := by
    change (schemeSpaceMap i ≫ κ.hom) ≫ productSnd n (schemeSpace W) = schemeSpaceMap q
    rw [Category.assoc, projectiveSiteProductIso_hom_productSnd, ← hiq]
    exact ObjectProperty.hom_ext _ (yoneda.map_comp _ _).symm
  have hMqc : M.IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_of_isInvertible B integerBase ℤS _ M
      (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hM)
  let eL : (modulePullback B integerBase ℤS π₁).obj M ≅
      invertibleTensorPower B integerBase ℤS (yoneda.obj U)
        (isAlgebraicSpace_yoneda B integerBase ℤS U) M₀ (d : ℤ) :=
    modulePullbackProjectiveSiteIso i M hMqc eM ≪≫ (associatedSpaceModule U).mapIso e.symm ≪≫
      (invertibleTensorPowerAssociatedIso U M₀ (hM₀ := hM₀) hM₀qc (hN := hN) (d : ℤ)).symm
  let FU := (modulePushforward B integerBase ℤS ι.hom).obj DW.F
  have hFUqc : FU.IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePushforward_of_isIso B integerBase ℤS ι.symm DW.F DW.quasicoherent
  have hFUft : SheafOfModules.IsFiniteTypeOnSite FU :=
    isFiniteTypeOnSite_modulePushforward_hom ι
      (isFiniteTypeOnSite_modulePullback B integerBase ℤS _ D.F hFft)
  have hG : ((modulePushforward B integerBase ℤS π₁).obj FU).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePushforward_of_isClosedImmersion B integerBase ℤS π₁ hπ₁ FU hFUqc
  have hGft : SheafOfModules.IsFiniteTypeOnSite ((modulePushforward B integerBase ℤS π₁).obj FU) :=
    Stacks.SheafOfModules.FiniteTypeTransport.isFiniteTypeOnSite_of_iso
      ((modulePushforwardCompIso B integerBase ℤS (schemeSpaceMap i) κ.hom).app FU)
      (isFiniteTypeOnSite_modulePushforward_hom κ
        (isFiniteTypeOnSite_modulePushforward_representedSpaceMap i FU hFUqc hFUft))
  have hB := isRepresentedProper_hilbertPolynomialQuot_of_closedImmersion
    PS.directImageSituation hsepU M₀ (hL := hM₀) hP n π₁ hπ₁ hcomp₁ M (hM := hM)
    (by exact_mod_cast (show d ≠ 0 by omega)) eL hG (h _ hG hGft)
  have hM₀' : Stacks.SheafOfModules.IsInvertible
      (structurePresheaf B integerBase ℤS (schemeSpace U).1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B integerBase ℤS
        (schemeSpace U).1 (schemeSpace U).2).O)).property M₀ := hM₀
  have hA := PS.isRepresentedProper_hilbertPolynomialQuot_of_directImage hιci M₀ (hM := hM₀) P hB
  let e₀ : (modulePullback B integerBase ℤS ι.hom).obj M₀ ≅
      (modulePullback B integerBase ℤS (D.baseChangedSourceProjection ξ')).obj L :=
    (modulePullbackCompIso B integerBase ℤS ι.hom x').app L ≪≫
      eqToIso (congrArg (fun k => (modulePullback B integerBase ℤS k).obj L) hι₁)
  exact IsRepresentedProper.of_eq (hilbertPolynomialQuot_congr (D := DW) _
    (hL := isInvertible_modulePullback B integerBase ℤS ι.hom M₀)
    (hL' := isInvertible_modulePullback B integerBase ℤS (D.baseChangedSourceProjection ξ') L)
    e₀ P) hA

/-- **Stacks 0DPC from the affine case of Stacks 0DPB.**  Let `f : X ⟶ B` be proper and of finite
presentation, `F` a quasi-coherent `𝒪_X`-module of finite type, `L` an invertible `𝒪_X`-module
ample on `X/B` (Stacks 0D31) and `P` a numerical polynomial.  Suppose given, for every `n` and
every scheme `W`, a module `M n W` on `h_W × ℙⁿ_ℤ` read on `ℙⁿ_W` as `𝒪(1)`, such that over
affine `W` every `Quot^{P', M n W}_{G/(W × ℙⁿ)/W}` with `G` quasi-coherent of finite type and
`P'` numerical is represented by a scheme proper over `W`.  Then `Quot^{P, L}_{F/X/B}` is an
algebraic space proper over `B`.

The reduction to affine `W` is Stacks 083R; over affine `W` the base change `X_W` is a scheme `U`
(`L` is relatively ample, so `f` is representable) with `L_U` ample (Stacks 01VK), proper over
`W`, so Stacks 01VS embeds it in `ℙⁿ_W` with `𝒪(1)` restricting to a power of `L_U`. -/
theorem isProperAlgebraicSpaceOver_hilbertPolynomialQuot_of_isRelativelyAmple_of_projective
    (D : QuotSituation B integerBase ℤS) (hf : IsProper B integerBase ℤS D.f.hom)
    (hFft : SheafOfModules.IsFiniteTypeOnSite D.F)
    (L : Modules.{u, u} B integerBase ℤS D.X.1 D.X.2)
    [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B integerBase ℤS D.X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B integerBase ℤS D.X.1 D.X.2).O)).property L]
    (hamp : IsRelativelyAmple B integerBase ℤS D.f L)
    {P : ℤ → ℤ} {p : Polynomial ℚ} (hP : ∀ m : ℤ, p.eval (m : ℚ) = (P m : ℚ))
    (M : ∀ (n : ℕ) (W : BigFppfOver B integerBase ℤS),
      Modules.{u, u} B integerBase ℤS (productSpace n (schemeSpace W)).1
        (productSpace n (schemeSpace W)).2)
    [hM : ∀ (n : ℕ) (W : BigFppfOver B integerBase ℤS), Stacks.SheafOfModules.IsInvertible
      (structurePresheaf B integerBase ℤS (productSpace n (schemeSpace W)).1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B integerBase ℤS
        (productSpace n (schemeSpace W)).1 (productSpace n (schemeSpace W)).2).O)).property
      (M n W)]
    (eM : ∀ (n : ℕ) (W : BigFppfOver B integerBase ℤS),
      (isoReading (projectiveSiteProductIso n W)).obj (M n W) ≅
        projectiveSpaceTwistingSheaf n ((𝒯).obj W))
    (h : ∀ (n : ℕ) (W : BigFppfOver B integerBase ℤS), IsAffine ((𝒯).obj W) →
      ∀ (G : Modules.{u, u} B integerBase ℤS (productSpace n (schemeSpace W)).1
        (productSpace n (schemeSpace W)).2) (hG : G.IsQuasicoherentOnSite),
      SheafOfModules.IsFiniteTypeOnSite G → ∀ (P' : ℤ → ℤ) (p' : Polynomial ℚ),
        (∀ m : ℤ, p'.eval (m : ℚ) = (P' m : ℚ)) →
        (situation n (schemeSpace W) G hG).IsRepresentedProper
          ((situation n (schemeSpace W) G hG).hilbertPolynomialQuot (M n W) (hL := hM n W) P')) :
    D.IsProperAlgebraicSpaceOver (D.hilbertPolynomialQuot L P) := by
  refine D.isProperAlgebraicSpaceOver_hilbertPolynomialQuot_of_isRepresentedProper L P
    fun W ξ hW => ?_
  have hrep := hamp.relativelyRepresentable
  obtain ⟨hinv, n, d, hd, i, hci, hiq, ⟨e⟩⟩ :=
    exists_closedImmersion_projectiveSite_of_isRelativelyAmple hf hamp W (hrep.pullback ξ) hW ξ
      (hrep.fst ξ) (hrep.snd ξ) (hrep.isPullback ξ)
  refine isRepresentedProper_canonicalBaseChanged_of_projectiveChart D hf.isSeparated hFft L hP
    W ξ _ _ _ (hrep.isPullback ξ) (hN := hinv) n d hd i (hi := hci) hiq e (M n W) (hM := hM n W)
    (eM n W) fun G hG hGft => h n W hW G hG hGft _
      (p.comp (Polynomial.C (d : ℚ) * Polynomial.X)) fun m => ?_
  rw [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  exact_mod_cast hP ((d : ℤ) * m)

/-- The identification `h_{ℙⁿ_W} ≅ h_W × ℙⁿ_ℤ` is the one of the projective frame of the Quot
situation of Stacks 0DPB over `h_W`. -/
theorem baseSpaceIso_situationFrame (n : ℕ) (W : BigFppfOver B integerBase ℤS)
    (G : Modules.{u, u} B integerBase ℤS (productSpace n (schemeSpace W)).1
      (productSpace n (schemeSpace W)).2) (hG : G.IsQuasicoherentOnSite) :
    baseSpaceIso (situationFrame n (schemeSpace W) G hG) (Iso.refl _) =
      projectiveSiteProductIso n W := by
  ext1
  refine (isPullback_productSpace_schemeSpace n W).hom_ext ?_ ?_
  · rw [show productFst n (schemeSpace W) = (situationFrame n (schemeSpace W) G hG).toProjective
      from rfl, baseSpaceIso_hom_toProjective]
    unfold projectiveSiteProductIso
    exact (IsPullback.isoIsPullback_hom_fst _ _ _ _).symm
  · rw [projectiveSiteProductIso_hom_productSnd]
    simpa using baseSpaceIso_hom_f (situationFrame n (schemeSpace W) G hG) (Iso.refl _)

/-- **The pullback of `𝒪(1)` to `h_W × ℙⁿ_ℤ` is read on `ℙⁿ_W` as `𝒪(1)`.**  Along
`h_{ℙⁿ_W} ≅ h_W × ℙⁿ_ℤ` the projection to `ℙⁿ_ℤ` is represented by `ℙⁿ_W ⟶ ℙⁿ_ℤ`; the Zariski
reading commutes with that inverse image (Stacks 03DX), reads the associated module of `𝒪(1)` on
`ℙⁿ_ℤ` back as `𝒪(1)`, and `𝒪(1)` pulls back to `𝒪(1)`. -/
def isoReadingTwistingModuleIso (n : ℕ) (W : BigFppfOver B integerBase ℤS) :
    (isoReading (projectiveSiteProductIso n W)).obj
        ((modulePullback B integerBase ℤS (productFst n (schemeSpace W))).obj
          (twistingModuleBase B n)) ≅
      projectiveSpaceTwistingSheaf n ((𝒯).obj W) :=
  let g := projectiveSiteMap B n (toSiteBase B W)
  have hg : (projectiveSiteProductIso n W).hom ≫ productFst n (schemeSpace W) =
      representedSpaceMap B integerBase ℤS g := by
    unfold projectiveSiteProductIso
    exact IsPullback.isoIsPullback_hom_fst _ _ _ _
  let O := projectiveSpaceTwistingSheaf n ((𝒯).obj (siteBase B))
  have hO : O.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.isQuasicoherent_twistOver n _ 1
  have hbase : (twistingModuleBase B n).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_of_isInvertible B integerBase ℤS _ _
      (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
        (isInvertible_twistingModuleBase B n))
  haveI := isIso_zariskiAdjunction_unit_app (projectiveSiteBase B n) O hO
  ((representedSpaceModulesEquivalence B integerBase ℤS (projectiveSite B n W)).inverse ⋙
      _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((𝒯).obj (projectiveSite B n W)) (projectiveSite B n W).left.property).mapIso
      ((modulePullbackCompIso B integerBase ℤS (projectiveSiteProductIso n W).hom
          (productFst n (schemeSpace W))).app (twistingModuleBase B n) ≪≫
        eqToIso (congrArg (fun k => (modulePullback B integerBase ℤS k).obj
          (twistingModuleBase B n)) hg)) ≪≫
    (representedZariskiModulePullbackIso B integerBase ℤS g
      (Functor.relativelyRepresentable.map yoneda g) _ hbase).symm ≪≫
    (Scheme.Modules.pullback ((𝒯).map g)).mapIso
      (asIso ((zariskiAdjunction B (projectiveSiteBase B n)).unit.app O)).symm ≪≫
    ProjectiveQuot.twistingSheafPullbackIso n ((𝒯).map (toSiteBase B W)) 1

end AlgebraicGeometry.Space.QuotSituation

end
