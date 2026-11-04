module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHigherPushforwardVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentPushforwardReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeOnSiteAffineCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperHigherDirectImageCoherenceNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedHigherDirectImageQuasicoherent

/-!
# Coherence of the higher direct images along a proper morphism: the reduction to an affine base

Let `f : X ⟶ Y` be a proper morphism of algebraic spaces over `S` with `Y` locally Noetherian
and let `𝓕` be a coherent `𝒪_X`-module.  The source's proof of Stacks 08AR begins by localizing
on `Y`: the higher direct images commute with étale localization on `Y` (Stacks 071Z for the
étale base change of a higher direct image) and coherence is étale local on `Y`
(Stacks 07UB), so that `Y` may be assumed to be a Noetherian affine scheme.  This file carries
out that reduction with the library's names, and over a Noetherian affine base it applies the
dévissage of Stacks 08AN.

* `AlgebraicGeometry.Space.isCoherent_of_forall_affine_chart`: a quasi-coherent module on a
  locally Noetherian algebraic space is coherent as soon as its restriction to every affine
  étale chart is.  Coherence is quasi-coherence and finite type (Stacks 07UB (1)–(2)); for a
  module cartesian on affine charts finite type is finiteness of the sections over every affine
  chart, and those sections are the sections of the restriction over the identity chart.
* `AlgebraicGeometry.Space.isCoherent_rightDerived_of_isProper_of_affineBase`: Stacks 08AR
  from its case of a Noetherian affine base.  Quasi-coherence of `R^n f_*𝓕` is
  `AlgebraicGeometry.Space.isQuasicoherentOnSite_rightDerived_modulePushforward_of_isSeparated`,
  a proper morphism being quasi-compact and separated.
* `AlgebraicGeometry.Space.isCoherent_rightDerived_of_isProper_of_witness`: Stacks 08AR, granted
  only condition (3) of the dévissage of Stacks 08AN over Noetherian affine bases (the integral
  witness `hwitness`, which the source produces from Stacks 089J, 08AQ and 02O4).  The
  Noetherianity of the source over such a base is Stacks 04ZL with Stacks 06G4, and the
  quasi-coherence input of the dévissage is the separated case of Stacks 0720.

No `@[stacks 08AR]` attribute is attached: the integral witness is carried as a hypothesis.

## References

* [Stacks Project, Tag 08AR](https://stacks.math.columbia.edu/tag/08AR)
* [Stacks Project, Tag 07UB](https://stacks.math.columbia.edu/tag/07UB)
* [Stacks Project, Tag 071Z](https://stacks.math.columbia.edu/tag/071Z)
* [Stacks Project, Tag 04ZL](https://stacks.math.columbia.edu/tag/04ZL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 5000] CategoryTheory.IsGrothendieckAbelian.enoughInjectives

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Coherence is tested on the affine étale charts.**  Let `M` be a quasi-coherent module on a
locally Noetherian algebraic space `Y`.  If for every étale chart `V` of `Y` with affine
underlying scheme the restriction `M|_V` is a coherent module on the algebraic space `V`, then
`M` is coherent.

By Stacks 07UB, conditions (1) and (2), coherence is quasi-coherence and finite type; a
quasi-coherent module is cartesian on affine charts (Stacks 03DX), and for such modules finite
type is finiteness of the sections over every affine chart
(`AlgebraicGeometry.Space.isFiniteTypeOnSite_iff_forall_affine_moduleFinite`).  The sections of
`M` over `V` are the sections of `M|_V` over the identity chart of `V`. -/
theorem isCoherent_of_forall_affine_chart (Y : AlgebraicSpaces B S hS)
    (hY : HasEtaleLocalProperty B S hS Y.1 (fun V : Scheme.{u} ↦ IsLocallyNoetherian V))
    (M : Modules.{u, u} B S hS Y.1 Y.2) (hM : M.IsQuasicoherentOnSite)
    (h : ∀ V : SmallEtale B S hS Y.1,
      IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj V)) →
      IsCoherent B S hS (chartSpace B S hS Y V).1 (chartSpace B S hS Y V).2
        ((etaleModulePullback B S hS (chartToSpace B S hS Y V)
          (isEtale_chartToSpace B S hS Y V)).obj M)) :
    IsCoherent B S hS Y.1 Y.2 M := by
  have : Fact (HasEtaleLocalProperty B S hS Y.1 (fun V : Scheme.{u} ↦ IsLocallyNoetherian V)) :=
    ⟨hY⟩
  refine (isCoherent_iff_isQuasicoherentOnSite_and_isFiniteType B S hS Y.1 Y.2 M).2 ⟨hM, ?_⟩
  refine Stacks.SheafOfModules.presheafIsFiniteType_of_isFiniteTypeOnSite _ ?_
  refine (isFiniteTypeOnSite_iff_forall_affine_moduleFinite B S hS Y.1 Y.2 M
    (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS Y.1 Y.2 M hM)).2 fun V hV ↦ ?_
  have hN := h V hV
  have : SheafOfModules.IsCoherentOnSite
      ((etaleModulePullback B S hS (chartToSpace B S hS Y V)
        (isEtale_chartToSpace B S hS Y V)).obj M) := hN.toIsCoherentOnSite
  exact (isFiniteTypeOnSite_iff_forall_affine_moduleFinite B S hS _ _ _
    (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS _ _ _
      hN.toIsQuasicoherentOnSite)).1
    (isFiniteTypeOnSite_of_isCoherentOnSite B S hS (chartSpace B S hS Y V) _)
    (idEtaleChart B S hS ((SmallEtale.toOver B S hS Y.1).obj V)) hV

/-- The restriction of a coherent module along an étale morphism into a locally Noetherian
algebraic space is coherent: it is the pullback of Stacks 03LU
(`AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback`), which preserves coherence by
`AlgebraicGeometry.Space.isCoherent_modulePullback`. -/
theorem isCoherent_etaleModulePullback_of_isCoherent {X Y : AlgebraicSpaces B S hS}
    (hX : HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} ↦ IsLocallyNoetherian V))
    (g : X ⟶ Y) (hg : IsEtale B S hS g.hom) (G : Modules.{u, u} B S hS Y.1 Y.2)
    (hG : IsCoherent B S hS Y.1 Y.2 G) :
    IsCoherent B S hS X.1 X.2 ((etaleModulePullback B S hS g hg).obj G) :=
  have : Fact (HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} ↦ IsLocallyNoetherian V)) :=
    ⟨hX⟩
  isCoherent_of_iso B S hS X.2 ((modulePullbackIsoEtaleModulePullback B S hS g hg).app G)
    (isCoherent_modulePullback B S hS g G hG)

variable {X Y : AlgebraicSpaces B S hS}

/-- **Stacks 08AR from its case of a Noetherian affine base.**  Let `f : X ⟶ Y` be a proper
morphism of algebraic spaces over `S` with `Y` locally Noetherian and `𝓕` a coherent
`𝒪_X`-module.  If the higher direct images of coherent modules along every proper morphism to
a Noetherian affine scheme of the site are coherent (`haffine`), then so is every `R^n f_*𝓕`.

`R^n f_*𝓕` is quasi-coherent by the separated case of Stacks 0720.  Over an affine étale chart
`V` of `Y` its restriction is the higher direct image along the base change
`V ×_Y X ⟶ V` of the restriction of `𝓕` (Stacks 071Z, with Stacks 03F3 for the injectives),
the base change being proper (Stacks 0EPD) over the Noetherian affine scheme `V`. -/
theorem isCoherent_rightDerived_of_isProper_of_affineBase
    (haffine : ∀ (T : BigFppfOver B S hS),
      IsAffine ((BigFppfOver.toScheme B S hS).obj T) →
      IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj T) →
      ∀ (X' : AlgebraicSpaces B S hS) (f' : X' ⟶ schemeSpace T),
        IsProper B S hS f'.hom →
        ∀ F' : Modules.{u, u} B S hS X'.1 X'.2, IsCoherent B S hS X'.1 X'.2 F' →
          HasCoherentHigherDirectImages B S hS f' F')
    (f : X ⟶ Y) (hf : IsProper B S hS f.hom)
    (hY : HasEtaleLocalProperty B S hS Y.1 (fun V : Scheme.{u} ↦ IsLocallyNoetherian V))
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : IsCoherent B S hS X.1 X.2 F) (n : ℕ) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    IsCoherent B S hS Y.1 Y.2 (((modulePushforward B S hS f).rightDerived n).obj F) := by
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  refine isCoherent_of_forall_affine_chart B S hS Y hY _
    (isQuasicoherentOnSite_rightDerived_modulePushforward_of_isSeparated B S hS f hf.2.1.2 hf.1
      F hF.toIsQuasicoherentOnSite n) fun V hV ↦ ?_
  have := hasInjectiveResolutions_modules B S hS (chartBaseChangeSpace B S hS f V).1
    (chartBaseChangeSpace B S hS f V).2
  have sq := isPullback_chartBaseChangeInclusion B S hS f V
  have hVN : IsLocallyNoetherian
      ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj V)) :=
    (exists_atlas_iff_forall_etale B S hS Y.1 (fun T : Scheme.{u} ↦ IsLocallyNoetherian T)
      Y.2).1 hY V.obj.left V.obj.hom V.property
  have hf' : IsProper B S hS (chartBaseChangeProjection B S hS f V).hom :=
    isProper_of_isPullback B S hS (chartBaseChangeSpace B S hS f V).2 X.2
      (isAlgebraicSpace_yoneda B S hS _) Y.2
      (AlgebraicSpaces.isPullback_hom _ _ _ sq) hf
  have hUN : HasEtaleLocalProperty B S hS (chartBaseChangeSpace B S hS f V).1
      (fun V : Scheme.{u} ↦ IsLocallyNoetherian V) :=
    isLocallyNoetherian_of_isLocallyOfFiniteType B S hS (chartBaseChangeSpace B S hS f V).2
      (isAlgebraicSpace_yoneda B S hS _) _ hf'.2.1.1
      (hasEtaleLocalProperty_chart B S hS _ V hVN)
  exact isCoherent_of_iso B S hS _
    ((moduleHigherPushforwardEtaleBaseChangeIso_of_preservesInjectives B S hS
      (chartBaseChangeInclusion B S hS f V) (chartBaseChangeProjection B S hS f V) f
      (chartToSpace B S hS Y V) sq (isEtale_chartToSpace B S hS Y V)
      (preservesInjectiveObjects_etaleModulePullback B S hS _
        (isEtale_chartBaseChangeInclusion B S hS f V)) n).app F)
    (haffine _ hV hVN _ (chartBaseChangeProjection B S hS f V) hf' _
      (isCoherent_etaleModulePullback_of_isCoherent B S hS hUN _
        (isEtale_chartBaseChangeInclusion B S hS f V) F hF) n)

/-- **Stacks 08AR, granted the integral witness of the dévissage over Noetherian affine bases.**
Let `f : X ⟶ Y` be a proper morphism of algebraic spaces over `S` with `Y` locally Noetherian
and let `𝓕` be a coherent `𝒪_X`-module.  Then `R^n f_*𝓕` is coherent for every `n`, provided
`hwitness`: for every proper `f' : X' ⟶ T` to a Noetherian affine scheme `T` of the site,
condition (3) of Stacks 08AN holds on `X'` for the property that all higher direct images along
`f'` are coherent.

The reduction to a Noetherian affine base is
`AlgebraicGeometry.Space.isCoherent_rightDerived_of_isProper_of_affineBase`.  Over such a base
`X'` is Noetherian (Stacks 04ZL, `f'` being of finite presentation by Stacks 06G4), the
quasi-coherence input of the dévissage is the separated case of Stacks 0720, and the dévissage
itself is
`AlgebraicGeometry.Space.isCoherent_rightDerived_modulePushforward_of_isNoetherian_source`. -/
theorem isCoherent_rightDerived_of_isProper_of_witness
    (hwitness : ∀ (T : BigFppfOver B S hS),
      IsAffine ((BigFppfOver.toScheme B S hS).obj T) →
      IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj T) →
      ∀ (X' : AlgebraicSpaces B S hS) (f' : X' ⟶ schemeSpace T),
        IsProper B S hS f'.hom →
        HasCoherentWitnessOnIntegralSubspaces B S hS X' (HasCoherentHigherDirectImages B S hS f'))
    (f : X ⟶ Y) (hf : IsProper B S hS f.hom)
    (hY : HasEtaleLocalProperty B S hS Y.1 (fun V : Scheme.{u} ↦ IsLocallyNoetherian V))
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : IsCoherent B S hS X.1 X.2 F) (n : ℕ) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    IsCoherent B S hS Y.1 Y.2 (((modulePushforward B S hS f).rightDerived n).obj F) := by
  refine isCoherent_rightDerived_of_isProper_of_affineBase B S hS
    (fun T hT hTN X' f' hf' F' hF' ↦ ?_) f hf hY F hF n
  have hZ := BigFppfSite.contains_terminal B
  have hTY : HasEtaleLocalProperty B S hS (yoneda.obj T)
      (fun V : Scheme.{u} ↦ IsLocallyNoetherian V) :=
    hasEtaleLocalProperty_of_representable B S hS _ _ T (Iso.refl _) hTN
  have hTnoeth : IsNoetherian B S hS hZ (yoneda.obj T) :=
    ⟨IsAffineSpace.isQuasiCompactSpace ⟨T, hT, ⟨Iso.refl _⟩⟩,
      isAbsolutelyQuasiSeparated_of_isQuasiSeparatedScheme B S hS _ hZ
        ⟨T, inferInstance, ⟨Functor.representableByEquiv.symm (Iso.refl _)⟩⟩, hTY⟩
  have hX'noeth : IsNoetherian B S hS hZ X'.1 :=
    isNoetherian_of_isFinitePresentation B S hS hZ f'.hom X'.2 (isAlgebraicSpace_yoneda B S hS T)
      (isFinitePresentation_of_isFiniteType B S hS X'.2 (isAlgebraicSpace_yoneda B S hS T) f'.hom
        hTY hf'.2.1 (isQuasiSeparated_of_isSeparated B S hS hf'.1)) hTnoeth
  exact isCoherent_rightDerived_modulePushforward_of_isNoetherian_source B S hS hZ f' hX'noeth hTY
    (quasicoherentHigherDirectImages_of_isSeparated B S hS f' hf'.2.1.2 hf'.1)
    (hwitness T hT hTN X' f' hf') F' hF'

end AlgebraicGeometry.Space

end
