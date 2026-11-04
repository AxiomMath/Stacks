module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundleChartPresentation
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.TautologicalDatumBaseChangeSpec
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiModuleBase
public import StacksFrontier.AlgebraicGeometry.ModuleDescent.InvertibleInput

/-!
# The descent datum of the twist `𝒪(1)` over the chart bundles of a projective bundle

Let `X` be an algebraic space with its étale presentation `X = U/R` and `ℰ` a finite locally free
`𝒪_X`-module, and let `P = P_U/P_R` be the presentation of the projective bundle `P = 𝐏(ℰ)` by its
chart bundles (`AlgebraicGeometry.Space.projectiveBundleChartPresentation`). The chart bundle
`P_U = 𝐏(ℰ|_U)` carries its tautological quotient `π_U^*ℰ|_U ⟶ 𝒪_{P_U}(1)`. This file proves that
the two pullbacks of that quotient to `P_R`, read as quotients of the one module `(P_R ⟶ X)^*ℰ`
through the canonical identifications, **have the same kernel** — there is a morphism `β` of the
two pullbacks of `𝒪(1)` carrying the one quotient to the other.

## Main definitions

* `AlgebraicGeometry.Space.projectiveBundleChartTwist`: the twist `𝒪_{P_U}(1)` of the presenting
  chart bundle, as a quasi-coherent module on the represented algebraic space `P_U`.
* `AlgebraicGeometry.Space.projectiveBundleChartQuotient`: the tautological quotient
  `φ^*π^*ℰ ⟶ 𝒪_{P_U}(1)` on `P_U`, the morphism whose reading on the scheme `P_U` is the
  tautological quotient of `𝐏(ℰ|_U)`.
* `AlgebraicGeometry.Space.IsoCompatible` and `AlgebraicGeometry.Space.QuotientDescends`: a
  morphism `q : N ⟶ L` is compatible with an identification `a^*N ≅ b^*N` of its two inverse
  images when some `β : a^*L ⟶ b^*L` carries `a^*q` to `b^*q`.

## Main results

* `AlgebraicGeometry.Space.pullback_map_comp_eq_of_twistSpec`: the scheme-level shape: two
  base-change comparisons of the tautological quotient along the two legs of a relation combine
  into a comparison of the two pullbacks of the twist over the relation.
* `AlgebraicGeometry.Space.exists_pullback_map_comp_eq_of_reading`: a quotient of a pulled-back
  module on a represented algebraic space descends along a pair of morphisms of the site as soon
  as its reading on the schemes does.
* `AlgebraicGeometry.Space.projectiveBundleChartQuotient_descends`: **the tautological quotient of
  `P_U` descends along the two legs `P_R ⇉ P_U` of the relation.**

## References

* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
* [Stacks Project, Tag 03M3](https://stacks.math.columbia.edu/tag/03M3)
* [Stacks Project, Tag 0ERT](https://stacks.math.columbia.edu/tag/0ERT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-! ### The scheme-level shape -/

section Shape

variable {PR PU U R : Scheme.{u}} {t s : PR ⟶ PU} {ρ : PU ⟶ U} {ρR : PR ⟶ R} {tX sX : R ⟶ U}
  (ht : t ≫ ρ = ρR ≫ tX) (hs : s ≫ ρ = ρR ≫ sX) {EU : U.Modules} {ER : R.Modules}
  {TU : PU.Modules} {TR : PR.Modules}
  (univU : (Scheme.Modules.pullback ρ).obj EU ⟶ TU)
  (univR : (Scheme.Modules.pullback ρR).obj ER ⟶ TR)
  (cT : ER ≅ (Scheme.Modules.pullback tX).obj EU) (cS : ER ≅ (Scheme.Modules.pullback sX).obj EU)
  (θt : (Scheme.Modules.pullback t).obj TU ≅ TR) (θs : (Scheme.Modules.pullback s).obj TU ≅ TR)

/-- The canonical identification `t^*ρ^*E_U ≅ ρ_R^*tX^*E_U` along a commutative square
`t ≫ ρ = ρ_R ≫ tX`. -/
abbrev squarePullbackIso : (Scheme.Modules.pullback t).obj ((Scheme.Modules.pullback ρ).obj EU) ≅
    (Scheme.Modules.pullback ρR).obj ((Scheme.Modules.pullback tX).obj EU) :=
  (Scheme.Modules.pullbackComp t ρ).app EU ≪≫ (Scheme.Modules.pullbackCongr ht).app EU ≪≫
    ((Scheme.Modules.pullbackComp ρR tX).app EU).symm

/-- **Two base-change comparisons of a tautological quotient along the two legs of a relation
combine into a comparison of the two pullbacks of the twist.**  If the pullback of `univU` along
`t` is `univR` through `θt` and the canonical identification `t^*ρ^*E_U ≅ ρ_R^*E_R`, and
likewise along `s`, then `t^* univU ≫ θt ≫ θs⁻¹` is the canonical identification
`t^*ρ^*E_U ≅ s^*ρ^*E_U` through `ρ_R^*E_R`, followed by `s^* univU`. -/
theorem pullback_map_comp_eq_of_twistSpec
    (spect : (Scheme.Modules.pullback t).map univU ≫ θt.hom =
      (Scheme.Modules.pullbackComp t ρ).hom.app EU ≫
        (Scheme.Modules.pullbackCongr ht).hom.app EU ≫
        (Scheme.Modules.pullbackComp ρR tX).inv.app EU ≫
        (Scheme.Modules.pullback ρR).map cT.inv ≫ univR)
    (specs : (Scheme.Modules.pullback s).map univU ≫ θs.hom =
      (Scheme.Modules.pullbackComp s ρ).hom.app EU ≫
        (Scheme.Modules.pullbackCongr hs).hom.app EU ≫
        (Scheme.Modules.pullbackComp ρR sX).inv.app EU ≫
        (Scheme.Modules.pullback ρR).map cS.inv ≫ univR) :
    (Scheme.Modules.pullback t).map univU ≫ θt.hom ≫ θs.inv =
      ((squarePullbackIso ht).hom ≫ (Scheme.Modules.pullback ρR).map cT.inv ≫
        (Scheme.Modules.pullback ρR).map cS.hom ≫ (squarePullbackIso hs).inv) ≫
        (Scheme.Modules.pullback s).map univU := by
  have hs' : (Scheme.Modules.pullback s).map univU =
      ((Scheme.Modules.pullbackComp s ρ).hom.app EU ≫
        (Scheme.Modules.pullbackCongr hs).hom.app EU ≫
        (Scheme.Modules.pullbackComp ρR sX).inv.app EU ≫
        (Scheme.Modules.pullback ρR).map cS.inv ≫ univR) ≫ θs.inv := by
    rw [← specs, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [hs', reassoc_of% spect]
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.app_hom, Iso.app_inv, Iso.symm_hom, Iso.symm_inv,
    Category.assoc, Iso.inv_hom_id_app_assoc, Iso.hom_inv_id_app_assoc]
  congr 3
  rw [← Functor.map_comp_assoc (Scheme.Modules.pullback ρR) cS.hom cS.inv, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp]

end Shape

/-! ### The canonical comparison of a pulled-back module, through a factorization -/

section Canonical

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The comparisons of an inverse image with the iterated inverse image along two equal
morphisms differ by the transport along the equality. -/
theorem pullbackComparison_symm_trans_pullbackComparison {T Z W : AlgebraicSpaces B S hS}
    {g₁ g₂ : T ⟶ Z} (h : g₁ = g₂) (p : Z ⟶ W) {v : T ⟶ W} (h₁ : g₁ ≫ p = v)
    (h₂ : g₂ ≫ p = v) (M : Modules.{u, u} B S hS W.1 W.2) :
    (QuasiCoherentDescent.pullbackComparison B S hS g₁ p v h₁ M).symm ≪≫
        QuasiCoherentDescent.pullbackComparison B S hS g₂ p v h₂ M =
      eqToIso (congrArg (fun q : T ⟶ Z =>
        (modulePullback B S hS q).obj ((modulePullback B S hS p).obj M)) h) := by
  subst h
  rw [Iso.symm_self_id, eqToIso_refl]

/-- **The canonical comparison of the two inverse images of a pulled-back module.**  For
`a ≫ φ = b ≫ φ`, the canonical comparison `a^*φ^*(π^*M) ≅ b^*φ^*(π^*M)` is the composite of the
two identifications of the iterated inverse images with the inverse image along the common
composite `ψ_R` to the base of `M`, each taken through the factorization `ψ_U = φ ≫ π`. -/
theorem canonicalComparison_modulePullback_eq {T Y Z W : AlgebraicSpaces B S hS}
    (a b : T ⟶ Y) (φ : Y ⟶ Z) (π : Z ⟶ W) (h : a ≫ φ = b ≫ φ) {ψU : Y ⟶ W}
    (hU : φ ≫ π = ψU) {ψR : T ⟶ W} (wa : a ≫ ψU = ψR) (wb : b ≫ ψU = ψR)
    (M : Modules.{u, u} B S hS W.1 W.2) :
    QuasiCoherentDescent.canonicalComparison a b φ φ h ((modulePullback B S hS π).obj M) =
      ((modulePullback B S hS a).mapIso
          (QuasiCoherentDescent.pullbackComparison B S hS φ π ψU hU M).symm ≪≫
        (QuasiCoherentDescent.pullbackComparison B S hS a ψU ψR wa M).symm) ≪≫
      ((modulePullback B S hS b).mapIso
          (QuasiCoherentDescent.pullbackComparison B S hS φ π ψU hU M).symm ≪≫
        (QuasiCoherentDescent.pullbackComparison B S hS b ψU ψR wb M).symm).symm := by
  have e : ∀ (c : T ⟶ Y) (wc : c ≫ ψU = ψR) (hc : (c ≫ φ) ≫ π = ψR),
      (modulePullback B S hS c).mapIso
          (QuasiCoherentDescent.pullbackComparison B S hS φ π ψU hU M).symm ≪≫
        (QuasiCoherentDescent.pullbackComparison B S hS c ψU ψR wc M).symm =
      (QuasiCoherentDescent.pullbackComparison B S hS c φ (c ≫ φ) rfl
          ((modulePullback B S hS π).obj M)).symm ≪≫
        (QuasiCoherentDescent.pullbackComparison B S hS (c ≫ φ) π ψR hc M).symm := fun c wc hc => by
    rw [Functor.mapIso_symm, ← Iso.trans_symm,
      QuasiCoherentDescent.pullbackComparison_trans B S hS c φ π ψU hU (c ≫ φ) rfl ψR wc hc M,
      Iso.trans_symm]
  have hsa : (a ≫ φ) ≫ π = ψR := by rw [Category.assoc, hU, wa]
  have hsb : (b ≫ φ) ≫ π = ψR := by rw [Category.assoc, hU, wb]
  rw [e a wa hsa, e b wb hsb, Iso.trans_symm, Iso.symm_symm_eq, Iso.symm_symm_eq, Iso.trans_assoc,
    ← Iso.trans_assoc (QuasiCoherentDescent.pullbackComparison B S hS (a ≫ φ) π ψR hsa M).symm,
    pullbackComparison_symm_trans_pullbackComparison h π hsa hsb M]
  rfl

end Canonical

/-! ### The tautological quotients of the chart bundles over two morphisms of charts -/

section ChartTwist

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
  (E : Modules.{u, u} B S hS X.1 X.2) [hE : E.IsQuasicoherentOnSite]

/-- The twist `𝒪(1)` of the chart bundle `𝐏(ℰ|_V)`. -/
abbrev chartBundleTwist (V : SmallEtale B S hS X.1) : (chartBundle E V).Modules :=
  Stacks.RelativeProj.tautologicalDatumTwist (chartBundleModule E V)

/-- The tautological quotient `π_V^* ℰ|_V ⟶ 𝒪(1)` of the chart bundle. -/
abbrev chartBundleTautological (V : SmallEtale B S hS X.1) :
    (Scheme.Modules.pullback (chartBundleToChart E V)).obj (chartBundleModule E V) ⟶
      chartBundleTwist E V :=
  Stacks.RelativeProj.tautologicalDatumUniv (chartBundleModule E V)

/-- The comparison `h^* 𝒪_{𝐏(ℰ|_V)}(1) ≅ 𝒪_{𝐏(ℰ|_{V'})}(1)` of the twists along a morphism of
charts. -/
abbrev chartBundleTwistIso {V V' : SmallEtale B S hS X.1} (h : V' ⟶ V) :
    (Scheme.Modules.pullback (chartBundleMap E h)).obj (chartBundleTwist E V) ≅
      chartBundleTwist E V' :=
  Stacks.RelativeProj.tautologicalDatumTwistBaseChangeIso (chartSchemeMapOfSite h)
    (chartBundleModule E V) (chartBundleModule E V') (chartBundleModuleIso E h)

/-- The pullback of the tautological quotient of `𝐏(ℰ|_V)` along the morphism over `h : V' ⟶ V` is
the tautological quotient of `𝐏(ℰ|_{V'})`, through the canonical identification of the pulled-back
module. -/
theorem chartBundleTwistIso_spec {V V' : SmallEtale B S hS X.1} (h : V' ⟶ V) :
    (Scheme.Modules.pullback (chartBundleMap E h)).map (chartBundleTautological E V) ≫
        (chartBundleTwistIso E h).hom =
      (Scheme.Modules.pullbackComp (chartBundleMap E h) (chartBundleToChart E V)).hom.app
          (chartBundleModule E V) ≫
        (Scheme.Modules.pullbackCongr
          (Stacks.RelativeProj.projectiveBundleBaseChange_comp_projectiveBundleToBase
            (chartSchemeMapOfSite h) (chartBundleModule E V) (chartBundleModule E V')
            (chartBundleModuleIso E h))).hom.app (chartBundleModule E V) ≫
        (Scheme.Modules.pullbackComp (chartBundleToChart E V')
          (chartSchemeMapOfSite h)).inv.app (chartBundleModule E V) ≫
        (Scheme.Modules.pullback (chartBundleToChart E V')).map (chartBundleModuleIso E h).inv ≫
        chartBundleTautological E V' :=
  Stacks.RelativeProj.tautologicalDatumTwistBaseChangeIso_spec (chartSchemeMapOfSite h)
    (chartBundleModule E V) (chartBundleModule E V') (chartBundleModuleIso E h)

/-- **The two pullbacks of the tautological quotient of a chart bundle along two morphisms of
charts are the same quotient.** For `h₁ h₂ : V' ⟶ V`, the pullbacks along the two morphisms of
chart bundles `𝐏(ℰ|_{V'}) ⇉ 𝐏(ℰ|_V)` of the tautological quotient of `𝐏(ℰ|_V)` are both the
tautological quotient of `𝐏(ℰ|_{V'})`: the comparison of the two pulled-back twists through
`𝒪_{𝐏(ℰ|_{V'})}(1)` carries the one to the other, through the canonical identification of the two
pulled-back modules through `π_{V'}^* ℰ|_{V'}`. -/
theorem chartBundleTautological_pullback_comparison {V V' : SmallEtale B S hS X.1}
    (h₁ h₂ : V' ⟶ V) :
    (Scheme.Modules.pullback (chartBundleMap E h₁)).map (chartBundleTautological E V) ≫
        (chartBundleTwistIso E h₁).hom ≫ (chartBundleTwistIso E h₂).inv =
      ((squarePullbackIso (EU := chartBundleModule E V)
          (Stacks.RelativeProj.projectiveBundleBaseChange_comp_projectiveBundleToBase
            (chartSchemeMapOfSite h₁) (chartBundleModule E V) (chartBundleModule E V')
            (chartBundleModuleIso E h₁) : chartBundleMap E h₁ ≫ chartBundleToChart E V =
              chartBundleToChart E V' ≫ chartSchemeMapOfSite h₁)).hom ≫
        (Scheme.Modules.pullback (chartBundleToChart E V')).map (chartBundleModuleIso E h₁).inv ≫
        (Scheme.Modules.pullback (chartBundleToChart E V')).map (chartBundleModuleIso E h₂).hom ≫
        (squarePullbackIso (EU := chartBundleModule E V)
          (Stacks.RelativeProj.projectiveBundleBaseChange_comp_projectiveBundleToBase
            (chartSchemeMapOfSite h₂) (chartBundleModule E V) (chartBundleModule E V')
            (chartBundleModuleIso E h₂) : chartBundleMap E h₂ ≫ chartBundleToChart E V =
              chartBundleToChart E V' ≫ chartSchemeMapOfSite h₂)).inv) ≫
        (Scheme.Modules.pullback (chartBundleMap E h₂)).map (chartBundleTautological E V) := by
  have key := pullback_map_comp_eq_of_twistSpec (t := chartBundleMap E h₁)
    (s := chartBundleMap E h₂) (ρ := chartBundleToChart E V) (ρR := chartBundleToChart E V')
    (tX := chartSchemeMapOfSite h₁) (sX := chartSchemeMapOfSite h₂)
    (Stacks.RelativeProj.projectiveBundleBaseChange_comp_projectiveBundleToBase
      (chartSchemeMapOfSite h₁) (chartBundleModule E V) (chartBundleModule E V')
      (chartBundleModuleIso E h₁))
    (Stacks.RelativeProj.projectiveBundleBaseChange_comp_projectiveBundleToBase
      (chartSchemeMapOfSite h₂) (chartBundleModule E V) (chartBundleModule E V')
      (chartBundleModuleIso E h₂))
    (chartBundleTautological E V) (chartBundleTautological E V')
    (chartBundleModuleIso E h₁) (chartBundleModuleIso E h₂)
    (chartBundleTwistIso E h₁) (chartBundleTwistIso E h₂)
    (chartBundleTwistIso_spec E h₁) (chartBundleTwistIso_spec E h₂)
  refine Eq.trans key ?_
  congr 1

end ChartTwist

/-! ### A morphism read through the comparison along a morphism to a chart -/

section QuotientReading

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
  (E : Modules.{u, u} B S hS X.1 X.2) (hE : E.IsQuasicoherentOnSite)

/-- The morphism of readings on the scheme of `T` of `N ⟶ L` determined by a morphism
`univ : ρ^*ℰ_Y ⟶ T_U` of modules on the scheme of `T`, through the reading `κ₀` of
`N ≅ ψ_U^*ℰ`, the comparison `ρ^*ℰ_Y ≅ ℰ_T` along `ρ : T ⟶ Y` and the reading `εL` of `L`. -/
def quotientReadingOf {T Y : BigFppfOver B S hS} {ρ : T ⟶ Y}
    {ψY : representedAlgebraicSpace B S hS Y ⟶ X} {ψU : representedAlgebraicSpace B S hS T ⟶ X}
    (wρ : representedSpaceMap B S hS ρ ≫ ψY = ψU)
    {TU : ((BigFppfOver.toScheme B S hS).obj T).Modules}
    (univ : (Scheme.Modules.pullback
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) ρ.left)).obj
        (schemeReading E ψY) ⟶ TU)
    {N L : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)}
    (εL : representedZariskiModule B S hS T L ≅ TU)
    (κ₀ : N ≅ (modulePullback B S hS ψU).obj E) :
    representedZariskiModule B S hS T N ⟶ representedZariskiModule B S hS T L :=
  ((SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T) T.left.property).mapIso
      ((representedSmallEtaleModuleEquivalence B S hS T).inverse.mapIso κ₀)).hom ≫
    (schemeReadingPullbackIso E hE ρ wρ).inv ≫ univ ≫ εL.inv

end QuotientReading

/-! ### The tautological quotient on the presenting chart bundle, as a module on its space -/

section Bundle

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
  (E : Modules.{u, u} B S hS X.1 X.2) [hE : E.IsQuasicoherentOnSite]
  (hfree : SheafOfModules.IsFiniteLocallyFreeOnSite E)

/-- The twist of a chart bundle is quasi-coherent, being invertible. -/
instance isQuasicoherent_chartBundleTwist (V : SmallEtale B S hS X.1) :
    (chartBundleTwist E V).IsQuasicoherent := by
  have h1 : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (chartBundleTwist E V) 1 :=
    Stacks.ModuleDescent.isFiniteLocallyFreeOfRank_one_of_isInvertible _ _
      (Stacks.RelativeProj.isInvertible_tautologicalDatumTwist (chartBundleModule E V))
  have h2 : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (chartBundleTwist E V) :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ 1
  obtain ⟨c, hc, _⟩ := h2.exists_isFiniteLocallyFreeData
  have : c.IsLocallyFreeData := hc
  exact c.quasiCoherentData.isQuasicoherent

/-- The groupoid in algebraic spaces `(P_U, P_R)` of the presentation of the projective bundle by
its chart bundles. -/
abbrev projectiveBundleGroupoid := presentationGroupoid (projectiveBundleChartPresentation E hfree)

/-- The atlas `P_U ⟶ P` of the projective bundle, from the space of objects of its groupoid. -/
abbrev projectiveBundleAtlas :
    (projectiveBundleGroupoid E hfree).objects ⟶ projectiveBundle E hfree :=
  presentationAtlas (projectiveBundleChartPresentation E hfree)

/-- The presenting chart of `X`. -/
abbrev bundleBaseChart (X : AlgebraicSpaces B S hS) : SmallEtale B S hS X.1 :=
  presentationChart (projectiveBundlePresentation X)

/-- The projection of the presenting chart bundle to the presenting chart, as a morphism of the
site. -/
abbrev projectiveBundleChartProj :
    (projectiveBundleChartPresentation E hfree).U ⟶
      (SmallEtale.toOver B S hS X.1).obj (bundleBaseChart X) :=
  (projectiveBundleChartFamily E hfree).siteToChart (bundleBaseChart X)

/-- The square `P_U ⟶ U ⟶ X` equals `P_U ⟶ P ⟶ X`. -/
theorem representedSpaceMap_projectiveBundleChartProj_comp :
    representedSpaceMap B S hS (projectiveBundleChartProj E hfree) ≫
        chartToSpace B S hS X (bundleBaseChart X) =
      projectiveBundleAtlas E hfree ≫ projectiveBundleProj E hfree :=
  ObjectProperty.hom_ext _ (isPullback_projectiveBundleProj E hfree).w.symm

/-- The inverse image `φ^*π^*ℰ` of `ℰ` to the presenting chart bundle, along the atlas `φ` and the
projection `π` of the projective bundle. -/
abbrev projectiveBundleChartModule :
    Modules.{u, u} B S hS (projectiveBundleGroupoid E hfree).objects.1
      (projectiveBundleGroupoid E hfree).objects.2 :=
  (modulePullback B S hS (projectiveBundleAtlas E hfree)).obj
    ((modulePullback B S hS (projectiveBundleProj E hfree)).obj E)

/-- The inverse image `φ^*π^*ℰ` is quasi-coherent on the site. -/
theorem isQuasicoherentOnSite_projectiveBundleChartModule :
    (projectiveBundleChartModule E hfree).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ _
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ E hE)

/-- **The twist `𝒪_{P_U}(1)` of the presenting chart bundle, as a quasi-coherent module on the
space of objects of the groupoid** `P_U`. -/
def projectiveBundleChartTwist :
    Modules.{u, u} B S hS (projectiveBundleGroupoid E hfree).objects.1
      (projectiveBundleGroupoid E hfree).objects.2 :=
  ((representedQuasicoherentSchemeEquivalence B S hS
    (projectiveBundleChartPresentation E hfree).U).functor.obj
      ⟨chartBundleTwist E (bundleBaseChart X), isQuasicoherent_chartBundleTwist E _⟩).obj

/-- The twist `𝒪_{P_U}(1)` of the presenting chart bundle is quasi-coherent on the site. -/
theorem isQuasicoherentOnSite_projectiveBundleChartTwist :
    (projectiveBundleChartTwist E hfree).IsQuasicoherentOnSite :=
  ((representedQuasicoherentSchemeEquivalence B S hS
    (projectiveBundleChartPresentation E hfree).U).functor.obj
      ⟨chartBundleTwist E (bundleBaseChart X), isQuasicoherent_chartBundleTwist E _⟩).property

/-- The reading of the twist on the scheme `P_U` is the twist. -/
def projectiveBundleChartTwistReadingIso :
    representedZariskiModule B S hS (projectiveBundleChartPresentation E hfree).U
        (projectiveBundleChartTwist E hfree) ≅ chartBundleTwist E (bundleBaseChart X) :=
  representedZariskiModuleQuasicoherentSchemeIso B S hS
    (projectiveBundleChartPresentation E hfree).U
    ⟨chartBundleTwist E (bundleBaseChart X), isQuasicoherent_chartBundleTwist E _⟩

/-- The tautological quotient `φ^*π^*ℰ ⟶ 𝒪_{P_U}(1)` of the presenting chart bundle, read on the
scheme `P_U`: the reading `φ^*π^*ℰ ≅ ℰ_{P_U}` of the inverse image, the comparison
`ℰ_{P_U} ≅ ρ^*ℰ|_U` along the projection `ρ : P_U ⟶ U`, the tautological quotient of `𝐏(ℰ|_U)` and
the reading of the twist. -/
abbrev projectiveBundleChartQuotientReading :
    representedZariskiModule B S hS (projectiveBundleChartPresentation E hfree).U
        (projectiveBundleChartModule E hfree) ⟶
      representedZariskiModule B S hS (projectiveBundleChartPresentation E hfree).U
        (projectiveBundleChartTwist E hfree) :=
  quotientReadingOf E hE (representedSpaceMap_projectiveBundleChartProj_comp E hfree)
    (chartBundleTautological E (bundleBaseChart X)) (projectiveBundleChartTwistReadingIso E hfree)
    (QuasiCoherentDescent.pullbackComparison B S hS (projectiveBundleAtlas E hfree)
      (projectiveBundleProj E hfree) _ rfl E).symm

/-- **The tautological quotient `φ^*π^*ℰ ⟶ 𝒪_{P_U}(1)` on the space `P_U`**: the morphism of
modules on the small étale site of `P_U` whose reading on the scheme is the tautological
quotient, which exists and is unique. -/
def projectiveBundleChartQuotient :
    projectiveBundleChartModule E hfree ⟶ projectiveBundleChartTwist E hfree :=
  ((QuasiCoherentDescent.bijective_representedZariski_map B S hS _ _
    (isQuasicoherentOnSite_projectiveBundleChartModule E hfree)).2
      (projectiveBundleChartQuotientReading E hfree)).choose

/-- The reading of `projectiveBundleChartQuotient` on the scheme `P_U` is
`projectiveBundleChartQuotientReading`. -/
theorem representedZariski_map_projectiveBundleChartQuotient :
    (SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj (projectiveBundleChartPresentation E hfree).U)
        (projectiveBundleChartPresentation E hfree).U.left.property).map
      ((representedSmallEtaleModuleEquivalence B S hS
        (projectiveBundleChartPresentation E hfree).U).inverse.map
        (projectiveBundleChartQuotient E hfree)) =
      projectiveBundleChartQuotientReading E hfree :=
  ((QuasiCoherentDescent.bijective_representedZariski_map B S hS _ _
    (isQuasicoherentOnSite_projectiveBundleChartModule E hfree)).2
      (projectiveBundleChartQuotientReading E hfree)).choose_spec

end Bundle

/-! ### The assembly, at abstract categories -/

section Assembly

variable {CU C : Type*} {instCU : Category CU} {instC : Category C} (Ft Fs : CU ⥤ C)
  {RN RL ΦU ρE TU : CU} (RUq : RN ⟶ RL) {n₁ n₂ l₁ l₂ ΦR TR : C}
  (A₁ : n₁ ⟶ l₁) (A₂ : n₁ ⟶ n₂) (A₃ : n₂ ⟶ l₂)
  (T2tN : Ft.obj RN ≅ n₁) (T2sN : Fs.obj RN ≅ n₂) (T2tL : Ft.obj RL ≅ l₁) (T2sL : Fs.obj RL ≅ l₂)
  (κ : RN ≅ ΦU) (cρ : ρE ≅ ΦU) (univ : ρE ⟶ TU) (εL : RL ≅ TU)
  (cτ : Ft.obj ΦU ≅ ΦR) (cσ : Fs.obj ΦU ≅ ΦR)
  (θ₁ : Ft.obj TU ≅ TR) (θ₂ : Fs.obj TU ≅ TR) (Ξ : Ft.obj ρE ⟶ Fs.obj ρE)

/-- **The shape of the descent of a quotient**: if `RUq = κ ≫ cρ⁻¹ ≫ univ ≫ εL⁻¹` is carried by
the two comparisons `T2` to `A₁` and `A₃`, if `A₂` is `cτ ≫ cσ⁻¹` through `κ`, and if the two
pullbacks of `univ` agree through `θ₁ ≫ θ₂⁻¹` and `Ξ = cρ ≫ cτ ≫ cσ⁻¹ ≫ cρ⁻¹`, then `A₁`
followed by the transported `θ₁ ≫ θ₂⁻¹` is `A₂ ≫ A₃`. -/
private theorem descent_assembly_shape
    (hnatt : Ft.map RUq ≫ T2tL.hom = T2tN.hom ≫ A₁)
    (hnats : Fs.map RUq ≫ T2sL.hom = T2sN.hom ≫ A₃)
    (hRUq : RUq = κ.hom ≫ cρ.inv ≫ univ ≫ εL.inv)
    (hαE : T2tN.hom ≫ A₂ = Ft.map κ.hom ≫ cτ.hom ≫ cσ.inv ≫ Fs.map κ.inv ≫ T2sN.hom)
    (hsch : Ft.map univ ≫ θ₁.hom ≫ θ₂.inv = Ξ ≫ Fs.map univ)
    (hsq : Ξ = Ft.map cρ.hom ≫ cτ.hom ≫ cσ.inv ≫ Fs.map cρ.inv) :
    A₁ ≫ (T2tL.inv ≫ Ft.map εL.hom ≫ θ₁.hom ≫ θ₂.inv ≫ Fs.map εL.inv ≫ T2sL.hom) =
      A₂ ≫ A₃ := by
  rw [← cancel_epi T2tN.hom, ← reassoc_of% hnatt, reassoc_of% hαE]
  have hs : T2sN.hom ≫ A₃ =
      Fs.map κ.hom ≫ Fs.map cρ.inv ≫ Fs.map univ ≫ Fs.map εL.inv ≫ T2sL.hom := by
    rw [← hnats, hRUq]
    simp only [Functor.map_comp, Category.assoc]
  rw [hs, hRUq]
  simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc, Iso.map_inv_hom_id_assoc]
  rw [reassoc_of% hsch, hsq]
  simp only [Category.assoc, Iso.map_inv_hom_id_assoc]

end Assembly

section Assembly'

variable {CU CR C : Type*} {instCU : Category CU} {instCR : Category CR} {instC : Category C}
  (Ft Fs : CU ⥤ C)
  (Gf : CR ⥤ C) {RN RL ΦU ρE TU : CU} (RUq : RN ⟶ RL) {n₁ n₂ l₁ l₂ ΦR TR : C}
  {tXE sXE ER : CR}
  (A₁ : n₁ ⟶ l₁) (A₂ : n₁ ⟶ n₂) (A₃ : n₂ ⟶ l₂)
  (T2tN : Ft.obj RN ≅ n₁) (T2sN : Fs.obj RN ≅ n₂) (T2tL : Ft.obj RL ≅ l₁) (T2sL : Fs.obj RL ≅ l₂)
  (κ : RN ≅ ΦU) (cρ : ρE ≅ ΦU) (univ : ρE ⟶ TU) (εL : RL ≅ TU)
  (cτ : Ft.obj ΦU ≅ ΦR) (cσ : Fs.obj ΦU ≅ ΦR)
  (θ₁ : Ft.obj TU ≅ TR) (θ₂ : Fs.obj TU ≅ TR)
  {m₁ m₂ p₁ p₂ : C} (At₁ : Ft.obj ρE ≅ m₁) (At₂ : m₁ ≅ m₂) (At₃ : m₂ ≅ Gf.obj tXE)
  (As₁ : Fs.obj ρE ≅ p₁) (As₂ : p₁ ≅ p₂) (As₃ : p₂ ≅ Gf.obj sXE) (ct : tXE ≅ ER) (cs : sXE ≅ ER)
  (cR : Gf.obj ER ≅ ΦR)

/-- `AlgebraicGeometry.Space.descent_assembly_shape` with the comparison of the two pullbacks
of the module split along the two commutative squares of the relation. -/
private theorem descent_assembly_shape_of_squares
    (hnatt : Ft.map RUq ≫ T2tL.hom = T2tN.hom ≫ A₁)
    (hnats : Fs.map RUq ≫ T2sL.hom = T2sN.hom ≫ A₃)
    (hRUq : RUq = κ.hom ≫ cρ.inv ≫ univ ≫ εL.inv)
    (hαE : T2tN.hom ≫ A₂ = Ft.map κ.hom ≫ cτ.hom ≫ cσ.inv ≫ Fs.map κ.inv ≫ T2sN.hom)
    (hsch : Ft.map univ ≫ θ₁.hom ≫ θ₂.inv =
      ((At₁ ≪≫ At₂ ≪≫ At₃).hom ≫ Gf.map ct.hom ≫ Gf.map cs.inv ≫ (As₁ ≪≫ As₂ ≪≫ As₃).inv) ≫
        Fs.map univ)
    (hsqt : Ft.mapIso cρ ≪≫ cτ = At₁ ≪≫ At₂ ≪≫ At₃ ≪≫ Gf.mapIso ct ≪≫ cR)
    (hsqs : Fs.mapIso cρ ≪≫ cσ = As₁ ≪≫ As₂ ≪≫ As₃ ≪≫ Gf.mapIso cs ≪≫ cR) :
    A₁ ≫ (T2tL.inv ≫ Ft.map εL.hom ≫ θ₁.hom ≫ θ₂.inv ≫ Fs.map εL.inv ≫ T2sL.hom) =
      A₂ ≫ A₃ := by
  refine descent_assembly_shape Ft Fs RUq A₁ A₂ A₃ T2tN T2sN T2tL T2sL κ cρ univ εL cτ cσ θ₁ θ₂
    ((At₁ ≪≫ At₂ ≪≫ At₃).hom ≫ Gf.map ct.hom ≫ Gf.map cs.inv ≫ (As₁ ≪≫ As₂ ≪≫ As₃).inv)
    hnatt hnats hRUq hαE hsch ?_
  have ht := congrArg Iso.hom hsqt
  have hs := congrArg Iso.inv hsqs
  simp only [Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom, Functor.mapIso_inv] at ht hs
  simp only [Iso.trans_hom, Iso.trans_inv, Category.assoc]
  rw [← Category.assoc (Ft.map cρ.hom), ht]
  simp only [Category.assoc] at hs ⊢
  rw [hs]
  simp only [Iso.hom_inv_id_assoc]

end Assembly'

/-! ### The comparison over the relation, in the spelling of the site -/

section Relation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
  (E : Modules.{u, u} B S hS X.1 X.2) [hE : E.IsQuasicoherentOnSite]
  (hfree : SheafOfModules.IsFiniteLocallyFreeOnSite E)

omit hE in
/-- A commutative square of the site, read on the underlying morphisms of schemes. -/
theorem schemeHom_comp_eq_of_eq {P' P Y' Y : BigFppfOver B S hS} {t : P' ⟶ P} {ρ : P ⟶ Y}
    {ρ' : P' ⟶ Y'} {t' : Y' ⟶ Y} (heq : t ≫ ρ = ρ' ≫ t') :
    _root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) t.left ≫
        _root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) ρ.left =
      _root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) ρ'.left ≫
        _root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) t'.left :=
  congrArg (fun x : P' ⟶ Y =>
    _root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) x.left) heq

/-- The relation chart of the presentation of `X`. -/
abbrev bundleRelationChart (X : AlgebraicSpaces B S hS) : SmallEtale B S hS X.1 :=
  presentationRelationChart (projectiveBundlePresentation X)

/-- The square of the chart bundles over a morphism of charts, in the site. -/
theorem siteMap_comp_siteToChart {V V' : SmallEtale B S hS X.1} (h : V' ⟶ V) :
    (projectiveBundleChartFamily E hfree).siteMap h ≫
        (projectiveBundleChartFamily E hfree).siteToChart V =
      (projectiveBundleChartFamily E hfree).siteToChart V' ≫
        (SmallEtale.toOver B S hS X.1).map h :=
  ((projectiveBundleChartFamily E hfree).isPullback_siteMap h).w

end Relation

/-! ### The descent datum of the twist -/

section Descent

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
  (E : Modules.{u, u} B S hS X.1 X.2) [hE : E.IsQuasicoherentOnSite]
  (hfree : SheafOfModules.IsFiniteLocallyFreeOnSite E)

omit hE in
/-- `T2N ≪≫ (Rψ ≪≫ Rp) = Fκ ≪≫ (T2ψ ≪≫ Rp)` whenever `Fκ ≪≫ T2ψ = T2N ≪≫ Rψ`. -/
private theorem nat_shape {C₀ : Type*} {instC₀ : Category C₀} {a b c d e : C₀}
    (T2N : a ≅ b) (Rψ : b ≅ c) (Rp : c ≅ d) (Fκ : a ≅ e) (T2ψ : e ≅ c)
    (nat : Fκ ≪≫ T2ψ = T2N ≪≫ Rψ) : T2N ≪≫ (Rψ ≪≫ Rp) = Fκ ≪≫ (T2ψ ≪≫ Rp) := by
  rw [← Iso.trans_assoc, ← nat, Iso.trans_assoc]

omit hE in
/-- The abstract shape of the reading of the canonical comparison. -/
private theorem reading_shape {C₀ : Type*} {instC₀ : Category C₀} {a b d e f g h : C₀}
    (T2tN : a ≅ b) (Jt : b ≅ g) (Js : d ≅ g) (T2sN : e ≅ d) (Fκt : a ≅ f) (cτ : f ≅ g)
    (Fκs : e ≅ h) (cσ : h ≅ g) (ht : T2tN ≪≫ Jt = Fκt ≪≫ cτ) (hs : T2sN ≪≫ Js = Fκs ≪≫ cσ) :
    T2tN.hom ≫ (Jt ≪≫ Js.symm).hom = Fκt.hom ≫ cτ.hom ≫ cσ.inv ≫ Fκs.inv ≫ T2sN.hom := by
  have ht' := congrArg Iso.hom ht
  have hs' := congrArg Iso.inv hs
  simp only [Iso.trans_hom, Iso.trans_inv] at ht' hs'
  have hs'' : Js.inv = cσ.inv ≫ Fκs.inv ≫ T2sN.hom := by
    rw [← Category.assoc, ← hs', Category.assoc, Iso.inv_hom_id, Category.comp_id]
  simp only [Iso.trans_hom, Iso.symm_hom]
  rw [reassoc_of% ht', hs'']

/-- The relation's target leg of the presentation of the projective bundle, in the site. -/
abbrev bundleRelationTarget :
    (projectiveBundleChartPresentation E hfree).R ⟶ (projectiveBundleChartPresentation E hfree).U :=
  (projectiveBundleChartPresentation E hfree).target

/-- The relation's source leg of the presentation of the projective bundle, in the site. -/
abbrev bundleRelationSource :
    (projectiveBundleChartPresentation E hfree).R ⟶ (projectiveBundleChartPresentation E hfree).U :=
  (projectiveBundleChartPresentation E hfree).source

/-- The projection of the relation chart bundle to the relation chart, in the site. -/
abbrev bundleRelationProj :
    (projectiveBundleChartPresentation E hfree).R ⟶
      (SmallEtale.toOver B S hS X.1).obj (bundleRelationChart X) :=
  (projectiveBundleChartFamily E hfree).siteToChart (bundleRelationChart X)

/-- A leg of the relation chart bundle, over a morphism of charts `h`, followed by `P_U ⟶ P ⟶ X`
equals its projection to the relation chart followed by the relation chart's map to `X`. -/
private theorem representedSpaceMap_siteMap_comp_atlas_comp_proj
    (h : bundleRelationChart X ⟶ bundleBaseChart X) :
    representedSpaceMap B S hS ((projectiveBundleChartFamily E hfree).siteMap h) ≫
        (projectiveBundleAtlas E hfree ≫ projectiveBundleProj E hfree) =
      representedSpaceMap B S hS (bundleRelationProj E hfree) ≫
        chartToSpace B S hS X (bundleRelationChart X) :=
  ObjectProperty.hom_ext _ (by
    have h1 := (isPullback_projectiveBundleProj E hfree).w
    have h2 := siteMap_comp_siteToChart E hfree h
    have h3 := yoneda_map_toOver_map_comp_hom h
    exact (congrArg (yoneda.map ((projectiveBundleChartFamily E hfree).siteMap h) ≫ ·) h1).trans
      (by rw [← Category.assoc, ← Functor.map_comp, h2, Functor.map_comp, Category.assoc, h3]; rfl))

/-- The target leg of the relation chart bundle followed by `P_U ⟶ P ⟶ X` equals its projection
to the relation chart followed by the relation chart's map to `X`. -/
theorem representedSpaceMap_bundleRelationTarget_comp :
    representedSpaceMap B S hS (bundleRelationTarget E hfree) ≫
        (projectiveBundleAtlas E hfree ≫ projectiveBundleProj E hfree) =
      representedSpaceMap B S hS (bundleRelationProj E hfree) ≫
        chartToSpace B S hS X (bundleRelationChart X) :=
  representedSpaceMap_siteMap_comp_atlas_comp_proj E hfree _

/-- The source leg of the relation chart bundle followed by `P_U ⟶ P ⟶ X` equals its projection
to the relation chart followed by the relation chart's map to `X`. -/
theorem representedSpaceMap_bundleRelationSource_comp :
    representedSpaceMap B S hS (bundleRelationSource E hfree) ≫
        (projectiveBundleAtlas E hfree ≫ projectiveBundleProj E hfree) =
      representedSpaceMap B S hS (bundleRelationProj E hfree) ≫
        chartToSpace B S hS X (bundleRelationChart X) :=
  representedSpaceMap_siteMap_comp_atlas_comp_proj E hfree _

end Descent

/-! ### The descent of a quotient through the readings, at variable data -/

section Generic

attribute [local implicit_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
  (E : Modules.{u, u} B S hS X.1 X.2) (hE : E.IsQuasicoherentOnSite)

/-- The comparison of the two pullbacks of a tautological quotient over a relation through the
two commutative squares, as a named proposition. -/
def TwistComparisonHyp {T' T Y' Y : BigFppfOver B S hS} (g g' : T' ⟶ T) (ρ : T ⟶ Y)
    (ρ' : T' ⟶ Y') (tX sX : Y' ⟶ Y) {ψY : representedAlgebraicSpace B S hS Y ⟶ X}
    {ψY' : representedAlgebraicSpace B S hS Y' ⟶ X}
    (wtX : representedSpaceMap B S hS tX ≫ ψY = ψY')
    (wsX : representedSpaceMap B S hS sX ≫ ψY = ψY')
    (heqg : g ≫ ρ = ρ' ≫ tX) (heqg' : g' ≫ ρ = ρ' ≫ sX)
    {TU : ((BigFppfOver.toScheme B S hS).obj T).Modules}
    {TR : ((BigFppfOver.toScheme B S hS).obj T').Modules}
    (univ : (Scheme.Modules.pullback
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) ρ.left)).obj
        (schemeReading E ψY) ⟶ TU)
    (θ₁ : (Scheme.Modules.pullback
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) g.left)).obj TU ≅
        TR)
    (θ₂ : (Scheme.Modules.pullback
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) g'.left)).obj TU ≅
        TR) : Prop :=
  (Scheme.Modules.pullback
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) g.left)).map
          univ ≫ θ₁.hom ≫ θ₂.inv =
      ((squarePullbackIso (EU := schemeReading E ψY) (schemeHom_comp_eq_of_eq heqg)).hom ≫
        (Scheme.Modules.pullback (_root_.AlgebraicGeometry.SmallEtale.schemeHom
          (associatedBigEtaleSite B) ρ'.left)).map (schemeReadingPullbackIso E hE tX wtX).hom ≫
        (Scheme.Modules.pullback (_root_.AlgebraicGeometry.SmallEtale.schemeHom
          (associatedBigEtaleSite B) ρ'.left)).map (schemeReadingPullbackIso E hE sX wsX).inv ≫
        (squarePullbackIso (EU := schemeReading E ψY) (schemeHom_comp_eq_of_eq heqg')).inv) ≫
        (Scheme.Modules.pullback
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) g'.left)).map
          univ

/-- The reading of a morphism `q : N ⟶ L` of modules on `T` is a given morphism `univ` of
modules on the scheme of `T`, through the reading `κ₀` of `N ≅ ψ_U^*ℰ`, the comparison along
`ρ : T ⟶ Y` and the reading `εL` of `L`, as a named proposition. -/
def QuotientReadingHyp {T Y : BigFppfOver B S hS} {ρ : T ⟶ Y}
    {ψY : representedAlgebraicSpace B S hS Y ⟶ X} {ψU : representedAlgebraicSpace B S hS T ⟶ X}
    (wρ : representedSpaceMap B S hS ρ ≫ ψY = ψU)
    {TU : ((BigFppfOver.toScheme B S hS).obj T).Modules}
    (univ : (Scheme.Modules.pullback
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) ρ.left)).obj
        (schemeReading E ψY) ⟶ TU)
    {N L : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)}
    (εL : representedZariskiModule B S hS T L ≅ TU) (q : N ⟶ L)
    (κ₀ : N ≅ (modulePullback B S hS ψU).obj E) : Prop :=
  (SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T) T.left.property).map
      ((representedSmallEtaleModuleEquivalence B S hS T).inverse.map q) =
    quotientReadingOf E hE wρ univ εL κ₀

/-- **The reading of the canonical comparison of two pullbacks of a module**, along two
morphisms `g, g' : T' ⟶ T` of the site over `X`, is the composite of the comparisons of the
readings along `g` and `g'`. -/
theorem representedZariski_map_canonical_reading {T' T : BigFppfOver B S hS} (g g' : T' ⟶ T)
    {ψU : representedAlgebraicSpace B S hS T ⟶ X} {ψR : representedAlgebraicSpace B S hS T' ⟶ X}
    (wa : representedSpaceMap B S hS g ≫ ψU = ψR) (wb : representedSpaceMap B S hS g' ≫ ψU = ψR)
    {N : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)}
    (hN : N.IsQuasicoherentOnSite) (κ₀ : N ≅ (modulePullback B S hS ψU).obj E) :
    (representedZariskiModulePullbackIso B S hS g (relativelyRepresentable_yoneda_map B S hS g)
        N hN).hom ≫
      (SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T') T'.left.property).map
        ((representedSmallEtaleModuleEquivalence B S hS T').inverse.map
          ((((modulePullback B S hS (representedSpaceMap B S hS g)).mapIso κ₀ ≪≫
            (QuasiCoherentDescent.pullbackComparison B S hS (representedSpaceMap B S hS g) ψU ψR
              wa E).symm) ≪≫
          ((modulePullback B S hS (representedSpaceMap B S hS g')).mapIso κ₀ ≪≫
            (QuasiCoherentDescent.pullbackComparison B S hS (representedSpaceMap B S hS g') ψU ψR
              wb E).symm).symm).hom)) =
      (Scheme.Modules.pullback
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) g.left)).map
          ((SmallEtale.restrictModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj T) T.left.property).mapIso
            ((representedSmallEtaleModuleEquivalence B S hS T).inverse.mapIso κ₀)).hom ≫
        (schemeReadingPullbackIso E hE g wa).hom ≫ (schemeReadingPullbackIso E hE g' wb).inv ≫
        (Scheme.Modules.pullback
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) g'.left)).map
          ((SmallEtale.restrictModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj T) T.left.property).mapIso
            ((representedSmallEtaleModuleEquivalence B S hS T).inverse.mapIso κ₀)).inv ≫
        (representedZariskiModulePullbackIso B S hS g'
          (relativelyRepresentable_yoneda_map B S hS g') N hN).hom := by
  have key : ∀ (c : T' ⟶ T) (wc : representedSpaceMap B S hS c ≫ ψU = ψR),
      _ ≪≫ _ = _ ≪≫ schemeReadingPullbackIso E hE c wc := fun c wc =>
    (nat_shape _ _ ((SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T') T'.left.property).mapIso
      ((representedSmallEtaleModuleEquivalence B S hS T').inverse.mapIso
        (QuasiCoherentDescent.pullbackComparison B S hS (representedSpaceMap B S hS c) ψU ψR wc
          E).symm)) _ _
      (representedZariskiModulePullbackIso_naturality_iso B S hS c
        (relativelyRepresentable_yoneda_map B S hS c) hN
        (isQuasicoherentOnSite_modulePullback_schemeReading E hE ψU) κ₀)).trans rfl
  have hαE := reading_shape _ _ _ _ _ _ _ _ (key g wa) (key g' wb)
  rw [Functor.mapIso_hom, Functor.mapIso_inv] at hαE
  refine Eq.trans ?_ hαE
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Functor.mapIso_hom,
    Functor.mapIso_inv, Functor.map_comp, Category.assoc]

/-- The reading on `T'` of the descent of a quotient through the two commutative squares
`g ≫ ρ = ρ' ≫ tX` and `g' ≫ ρ = ρ' ≫ sX`. -/
theorem representedZariski_map_comp_reading
    {T' T Y' Y : BigFppfOver B S hS} (g g' : T' ⟶ T) {ρ : T ⟶ Y} {ρ' : T' ⟶ Y'}
    {tX sX : Y' ⟶ Y} {ψY : representedAlgebraicSpace B S hS Y ⟶ X}
    {ψY' : representedAlgebraicSpace B S hS Y' ⟶ X}
    {ψU : representedAlgebraicSpace B S hS T ⟶ X} {ψR : representedAlgebraicSpace B S hS T' ⟶ X}
    (wρ : representedSpaceMap B S hS ρ ≫ ψY = ψU)
    (wg : representedSpaceMap B S hS g ≫ ψU = ψR) (wg' : representedSpaceMap B S hS g' ≫ ψU = ψR)
    (wtX : representedSpaceMap B S hS tX ≫ ψY = ψY')
    (wsX : representedSpaceMap B S hS sX ≫ ψY = ψY')
    (wρ' : representedSpaceMap B S hS ρ' ≫ ψY' = ψR)
    (heqg : g ≫ ρ = ρ' ≫ tX) (heqg' : g' ≫ ρ = ρ' ≫ sX)
    {TU : ((BigFppfOver.toScheme B S hS).obj T).Modules}
    {TR : ((BigFppfOver.toScheme B S hS).obj T').Modules}
    (univ : (Scheme.Modules.pullback
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) ρ.left)).obj
        (schemeReading E ψY) ⟶ TU)
    (θ₁ : (Scheme.Modules.pullback
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) g.left)).obj TU ≅
        TR)
    (θ₂ : (Scheme.Modules.pullback
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) g'.left)).obj TU ≅
        TR)
    (hsch : TwistComparisonHyp E hE g g' ρ ρ' tX sX wtX wsX heqg heqg' univ θ₁ θ₂)
    {N L : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)}
    (hN : N.IsQuasicoherentOnSite) (hL : L.IsQuasicoherentOnSite)
    (εL : representedZariskiModule B S hS T L ≅ TU) (q : N ⟶ L)
    (κ₀ : N ≅ (modulePullback B S hS ψU).obj E)
    (hq : (SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property).map
        ((representedSmallEtaleModuleEquivalence B S hS T).inverse.map q) =
      ((SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property).mapIso
        ((representedSmallEtaleModuleEquivalence B S hS T).inverse.mapIso κ₀)).hom ≫
        (schemeReadingPullbackIso E hE ρ wρ).inv ≫ univ ≫ εL.inv)
 :
    (SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T') T'.left.property).map
        ((representedSmallEtaleModuleEquivalence B S hS T').inverse.map
          ((modulePullback B S hS (representedSpaceMap B S hS g)).map q)) ≫
      ((representedZariskiModulePullbackIso B S hS g
          (relativelyRepresentable_yoneda_map B S hS g) L hL).inv ≫
        (Scheme.Modules.pullback
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) g.left)).map
          εL.hom ≫ θ₁.hom ≫ θ₂.inv ≫
        (Scheme.Modules.pullback
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) g'.left)).map
          εL.inv ≫
        (representedZariskiModulePullbackIso B S hS g'
          (relativelyRepresentable_yoneda_map B S hS g') L hL).hom) =
      (SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T') T'.left.property).map
        ((representedSmallEtaleModuleEquivalence B S hS T').inverse.map
          ((((modulePullback B S hS (representedSpaceMap B S hS g)).mapIso κ₀ ≪≫
            (QuasiCoherentDescent.pullbackComparison B S hS (representedSpaceMap B S hS g) ψU ψR
              wg E).symm) ≪≫
          ((modulePullback B S hS (representedSpaceMap B S hS g')).mapIso κ₀ ≪≫
            (QuasiCoherentDescent.pullbackComparison B S hS (representedSpaceMap B S hS g') ψU ψR
              wg' E).symm).symm).hom)) ≫
      (SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T') T'.left.property).map
        ((representedSmallEtaleModuleEquivalence B S hS T').inverse.map
          ((modulePullback B S hS (representedSpaceMap B S hS g')).map q)) :=
  descent_assembly_shape_of_squares
    (Scheme.Modules.pullback
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) g.left))
    (Scheme.Modules.pullback
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) g'.left))
    (Scheme.Modules.pullback
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) ρ'.left))
    ((SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property).map
        ((representedSmallEtaleModuleEquivalence B S hS T).inverse.map q))
    _ _ _
    (representedZariskiModulePullbackIso B S hS g (relativelyRepresentable_yoneda_map B S hS g)
      N hN)
    (representedZariskiModulePullbackIso B S hS g' (relativelyRepresentable_yoneda_map B S hS g')
      N hN)
    (representedZariskiModulePullbackIso B S hS g (relativelyRepresentable_yoneda_map B S hS g)
      L hL)
    (representedZariskiModulePullbackIso B S hS g' (relativelyRepresentable_yoneda_map B S hS g')
      L hL)
    ((SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property).mapIso
        ((representedSmallEtaleModuleEquivalence B S hS T).inverse.mapIso κ₀))
    (schemeReadingPullbackIso E hE ρ wρ) univ εL
    (schemeReadingPullbackIso E hE g wg) (schemeReadingPullbackIso E hE g' wg') θ₁ θ₂
    _ _ _ _ _ _
    (schemeReadingPullbackIso E hE tX wtX) (schemeReadingPullbackIso E hE sX wsX)
    (schemeReadingPullbackIso E hE ρ' wρ')
    (representedZariskiModulePullbackIso_naturality B S hS g
      (relativelyRepresentable_yoneda_map B S hS g) hN hL q)
    (representedZariskiModulePullbackIso_naturality B S hS g'
      (relativelyRepresentable_yoneda_map B S hS g') hN hL q) hq
    (representedZariski_map_canonical_reading E hE g g' wg wg' hN κ₀) hsch
    (schemeReadingPullbackIso_square E hE heqg wρ wg wtX wρ')
    (schemeReadingPullbackIso_square E hE heqg' wρ wg' wsX wρ')

/-- A morphism `q : N ⟶ L` of modules on `A` is **compatible with an isomorphism**
`J : a^*N ≅ b^*N` of its two inverse images along `a, b : A' ⟶ A`: there is a morphism
`β : a^*L ⟶ b^*L` with `a^*q ≫ β = J ≫ b^*q`. -/
def IsoCompatible {A A' : AlgebraicSpaces B S hS} (a b : A' ⟶ A)
    {N L : Modules.{u, u} B S hS A.1 A.2}
    (J : (modulePullback B S hS a).obj N ≅ (modulePullback B S hS b).obj N) (q : N ⟶ L) :
    Prop :=
  ∃ β : (modulePullback B S hS a).obj L ⟶ (modulePullback B S hS b).obj L,
    (modulePullback B S hS a).map q ≫ β = J.hom ≫ (modulePullback B S hS b).map q

/-- A morphism `q : N ⟶ L` of modules on `T`, with `N ≅ ψ_U^*ℰ` through `κ₀`, **descends along
the pair `g, g' : T' ⟶ T`**: it is compatible with the identification `g^*N ≅ g'^*N` of the two
pullbacks through the two pullbacks of `ℰ` to `T'`. -/
def QuotientDescends {T' T : BigFppfOver B S hS} (g g' : T' ⟶ T)
    {ψU : representedAlgebraicSpace B S hS T ⟶ X} {ψR : representedAlgebraicSpace B S hS T' ⟶ X}
    (wg : representedSpaceMap B S hS g ≫ ψU = ψR) (wg' : representedSpaceMap B S hS g' ≫ ψU = ψR)
    {N L : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)}
    (q : N ⟶ L) (κ₀ : N ≅ (modulePullback B S hS ψU).obj E) : Prop :=
  IsoCompatible (representedSpaceMap B S hS g) (representedSpaceMap B S hS g')
    (((modulePullback B S hS (representedSpaceMap B S hS g)).mapIso κ₀ ≪≫
        (QuasiCoherentDescent.pullbackComparison B S hS (representedSpaceMap B S hS g) ψU ψR wg
          E).symm) ≪≫
      ((modulePullback B S hS (representedSpaceMap B S hS g')).mapIso κ₀ ≪≫
        (QuasiCoherentDescent.pullbackComparison B S hS (representedSpaceMap B S hS g') ψU ψR
          wg' E).symm).symm) q

/-- **The descent of a quotient of a pulled-back module through the readings on the schemes.**
Let `g, g' : T' ⟶ T` be two morphisms of the site over `X`, sitting in commutative squares
`g ≫ ρ = ρ' ≫ tX` and `g' ≫ ρ = ρ' ≫ sX`, let `q : N ⟶ L` be a morphism of modules on
`T` whose reading is `univ` through the reading `κ₀` of `N ≅ ψ_U^*ℰ` and the comparison along `ρ`,
and let `α : a^*N ⟶ b^*N` be the canonical comparison of the two pullbacks of `N` along
`a = g`, `b = g'`.  If the two pullbacks of `univ` are compared by `θ₁ ≫ θ₂⁻¹` through the
squares, then there is `β : a^*L ⟶ b^*L` with `a^*q ≫ β = α ≫ b^*q`. -/
theorem exists_pullback_map_comp_eq_of_reading
    {T' T Y' Y : BigFppfOver B S hS} (g g' : T' ⟶ T) {ρ : T ⟶ Y} {ρ' : T' ⟶ Y'}
    {tX sX : Y' ⟶ Y} {ψY : representedAlgebraicSpace B S hS Y ⟶ X}
    {ψY' : representedAlgebraicSpace B S hS Y' ⟶ X}
    {ψU : representedAlgebraicSpace B S hS T ⟶ X} {ψR : representedAlgebraicSpace B S hS T' ⟶ X}
    (wρ : representedSpaceMap B S hS ρ ≫ ψY = ψU)
    (wg : representedSpaceMap B S hS g ≫ ψU = ψR) (wg' : representedSpaceMap B S hS g' ≫ ψU = ψR)
    (wtX : representedSpaceMap B S hS tX ≫ ψY = ψY')
    (wsX : representedSpaceMap B S hS sX ≫ ψY = ψY')
    (wρ' : representedSpaceMap B S hS ρ' ≫ ψY' = ψR)
    (heqg : g ≫ ρ = ρ' ≫ tX) (heqg' : g' ≫ ρ = ρ' ≫ sX)
    {TU : ((BigFppfOver.toScheme B S hS).obj T).Modules}
    {TR : ((BigFppfOver.toScheme B S hS).obj T').Modules}
    (univ : (Scheme.Modules.pullback
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) ρ.left)).obj
        (schemeReading E ψY) ⟶ TU)
    (θ₁ : (Scheme.Modules.pullback
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) g.left)).obj TU ≅
        TR)
    (θ₂ : (Scheme.Modules.pullback
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) g'.left)).obj TU ≅
        TR)
    (hsch : TwistComparisonHyp E hE g g' ρ ρ' tX sX wtX wsX heqg heqg' univ θ₁ θ₂)
    {N L : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)}
    (hN : N.IsQuasicoherentOnSite) (hL : L.IsQuasicoherentOnSite)
    (εL : representedZariskiModule B S hS T L ≅ TU) (q : N ⟶ L)
    (κ₀ : N ≅ (modulePullback B S hS ψU).obj E)
    (hq : QuotientReadingHyp E hE wρ univ εL q κ₀) :
    QuotientDescends E g g' wg wg' q κ₀ := by
  unfold QuotientDescends IsoCompatible
  have hqL := isQuasicoherentOnSite_modulePullback_representedSpaceMap B S hS g
    (relativelyRepresentable_yoneda_map B S hS g) L hL
  have hqN := isQuasicoherentOnSite_modulePullback_representedSpaceMap B S hS g
    (relativelyRepresentable_yoneda_map B S hS g) N hN
  obtain ⟨β, hβ⟩ := (QuasiCoherentDescent.bijective_representedZariski_map B S hS _
    ((modulePullback B S hS (representedSpaceMap B S hS g')).obj L) hqL).2
    ((representedZariskiModulePullbackIso B S hS g
        (relativelyRepresentable_yoneda_map B S hS g) L hL).inv ≫
      (Scheme.Modules.pullback
        (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) g.left)).map
        εL.hom ≫ θ₁.hom ≫ θ₂.inv ≫
      (Scheme.Modules.pullback
        (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) g'.left)).map
        εL.inv ≫
      (representedZariskiModulePullbackIso B S hS g'
        (relativelyRepresentable_yoneda_map B S hS g') L hL).hom)
  dsimp only at hβ
  have key := representedZariski_map_comp_reading E hE g g' wρ wg wg' wtX wsX wρ' heqg heqg'
    univ θ₁ θ₂ hsch hN hL εL q κ₀ hq
  refine ⟨β, (QuasiCoherentDescent.bijective_representedZariski_map B S hS _ _ hqN).1 ?_⟩
  dsimp only
  rw [Functor.map_comp, Functor.map_comp, Functor.map_comp, Functor.map_comp, hβ, key]

end Generic

/-! ### The comparison of the two pulled-back quotients over the relation of the bundle -/

section Concrete

attribute [local implicit_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
  (E : Modules.{u, u} B S hS X.1 X.2) [hE : E.IsQuasicoherentOnSite]
  (hfree : SheafOfModules.IsFiniteLocallyFreeOnSite E)

/-- **The comparison of the two pullbacks of the tautological quotient over a pair of morphisms
of charts**, in the shape `AlgebraicGeometry.Space.TwistComparisonHyp`. -/
theorem twistComparisonHyp_chartBundle {V V' : SmallEtale B S hS X.1} (h₁ h₂ : V' ⟶ V) :
    TwistComparisonHyp E hE ((projectiveBundleChartFamily E hfree).siteMap h₁)
      ((projectiveBundleChartFamily E hfree).siteMap h₂)
      ((projectiveBundleChartFamily E hfree).siteToChart V)
      ((projectiveBundleChartFamily E hfree).siteToChart V')
      ((SmallEtale.toOver B S hS X.1).map h₁) ((SmallEtale.toOver B S hS X.1).map h₂)
      (representedSpaceMap_toOver_map_comp_chartToSpace h₁)
      (representedSpaceMap_toOver_map_comp_chartToSpace h₂)
      (siteMap_comp_siteToChart E hfree h₁) (siteMap_comp_siteToChart E hfree h₂)
      (chartBundleTautological E V) (chartBundleTwistIso E h₁) (chartBundleTwistIso E h₂) := by
  unfold TwistComparisonHyp
  have key := chartBundleTautological_pullback_comparison E h₁ h₂
  refine Eq.trans ?_ (Eq.trans key ?_)
  · rfl
  · congr 1

/-- The comparison of the two pullbacks of the tautological quotient of the presenting chart
bundle over the relation chart bundle, in the shape
`AlgebraicGeometry.Space.TwistComparisonHyp`. -/
theorem twistComparisonHyp_projectiveBundle :
    TwistComparisonHyp E hE
      ((projectiveBundleChartFamily E hfree).siteMap
        (presentationRelationTargetHom (projectiveBundlePresentation X)))
      ((projectiveBundleChartFamily E hfree).siteMap
        (presentationRelationSourceHom (projectiveBundlePresentation X)))
      ((projectiveBundleChartFamily E hfree).siteToChart (bundleBaseChart X))
      ((projectiveBundleChartFamily E hfree).siteToChart (bundleRelationChart X))
      ((SmallEtale.toOver B S hS X.1).map
        (presentationRelationTargetHom (projectiveBundlePresentation X)))
      ((SmallEtale.toOver B S hS X.1).map
        (presentationRelationSourceHom (projectiveBundlePresentation X)))
      (representedSpaceMap_toOver_map_comp_chartToSpace
        (presentationRelationTargetHom (projectiveBundlePresentation X)))
      (representedSpaceMap_toOver_map_comp_chartToSpace
        (presentationRelationSourceHom (projectiveBundlePresentation X)))
      (siteMap_comp_siteToChart E hfree
        (presentationRelationTargetHom (projectiveBundlePresentation X)))
      (siteMap_comp_siteToChart E hfree
        (presentationRelationSourceHom (projectiveBundlePresentation X)))
      (chartBundleTautological E (bundleBaseChart X))
      (chartBundleTwistIso E (presentationRelationTargetHom (projectiveBundlePresentation X)))
      (chartBundleTwistIso E (presentationRelationSourceHom (projectiveBundlePresentation X))) :=
  twistComparisonHyp_chartBundle E hfree _ _

/-- The reading of the tautological quotient of the presenting chart bundle, in the shape
`AlgebraicGeometry.Space.QuotientReadingHyp`. -/
theorem quotientReadingHyp_projectiveBundle :
    QuotientReadingHyp E hE (representedSpaceMap_projectiveBundleChartProj_comp E hfree)
      (chartBundleTautological E (bundleBaseChart X)) (projectiveBundleChartTwistReadingIso E hfree)
      (projectiveBundleChartQuotient E hfree)
      (QuasiCoherentDescent.pullbackComparison B S hS (projectiveBundleAtlas E hfree)
        (projectiveBundleProj E hfree) _ rfl E).symm :=
  representedZariski_map_projectiveBundleChartQuotient E hfree

/-- **The two pullbacks of the tautological quotient of `P_U` to `P_R` are the same quotient**:
there is a morphism `β` of the two pullbacks of `𝒪_{P_U}(1)` carrying the pullback of the
tautological quotient along the target leg, composed with the identification of the two
pullbacks of `φ^*π^*ℰ`, to its pullback along the source leg. -/
theorem projectiveBundleChartQuotient_descends :
    QuotientDescends E
      ((projectiveBundleChartFamily E hfree).siteMap
        (presentationRelationTargetHom (projectiveBundlePresentation X)))
      ((projectiveBundleChartFamily E hfree).siteMap
        (presentationRelationSourceHom (projectiveBundlePresentation X)))
      (ψU := projectiveBundleAtlas E hfree ≫ projectiveBundleProj E hfree)
      (ψR := representedSpaceMap B S hS
        ((projectiveBundleChartFamily E hfree).siteToChart (bundleRelationChart X)) ≫
          chartToSpace B S hS X (bundleRelationChart X))
      (representedSpaceMap_bundleRelationTarget_comp E hfree)
      (representedSpaceMap_bundleRelationSource_comp E hfree)
      (projectiveBundleChartQuotient E hfree)
      (QuasiCoherentDescent.pullbackComparison B S hS (projectiveBundleAtlas E hfree)
        (projectiveBundleProj E hfree) _ rfl E).symm :=
  exists_pullback_map_comp_eq_of_reading E hE
    ((projectiveBundleChartFamily E hfree).siteMap
      (presentationRelationTargetHom (projectiveBundlePresentation X)))
    ((projectiveBundleChartFamily E hfree).siteMap
      (presentationRelationSourceHom (projectiveBundlePresentation X)))
    (ρ := (projectiveBundleChartFamily E hfree).siteToChart (bundleBaseChart X))
    (ρ' := (projectiveBundleChartFamily E hfree).siteToChart (bundleRelationChart X))
    (ψY := chartToSpace B S hS X (bundleBaseChart X))
    (ψY' := chartToSpace B S hS X (bundleRelationChart X))
    (ψU := projectiveBundleAtlas E hfree ≫ projectiveBundleProj E hfree)
    (ψR := representedSpaceMap B S hS
      ((projectiveBundleChartFamily E hfree).siteToChart (bundleRelationChart X)) ≫
        chartToSpace B S hS X (bundleRelationChart X))
    (representedSpaceMap_projectiveBundleChartProj_comp E hfree)
    (representedSpaceMap_bundleRelationTarget_comp E hfree)
    (representedSpaceMap_bundleRelationSource_comp E hfree)
    (representedSpaceMap_toOver_map_comp_chartToSpace
      (presentationRelationTargetHom (projectiveBundlePresentation X)))
    (representedSpaceMap_toOver_map_comp_chartToSpace
      (presentationRelationSourceHom (projectiveBundlePresentation X))) rfl
    (siteMap_comp_siteToChart E hfree
      (presentationRelationTargetHom (projectiveBundlePresentation X)))
    (siteMap_comp_siteToChart E hfree
      (presentationRelationSourceHom (projectiveBundlePresentation X)))
    (chartBundleTautological E (bundleBaseChart X))
    (chartBundleTwistIso E (presentationRelationTargetHom (projectiveBundlePresentation X)))
    (chartBundleTwistIso E (presentationRelationSourceHom (projectiveBundlePresentation X)))
    (twistComparisonHyp_projectiveBundle E hfree)
    (isQuasicoherentOnSite_projectiveBundleChartModule E hfree)
    (isQuasicoherentOnSite_projectiveBundleChartTwist E hfree)
    (projectiveBundleChartTwistReadingIso E hfree) (projectiveBundleChartQuotient E hfree)
    (QuasiCoherentDescent.pullbackComparison B S hS (projectiveBundleAtlas E hfree)
      (projectiveBundleProj E hfree) _ rfl E).symm
    (quotientReadingHyp_projectiveBundle E hfree)

end Concrete

end AlgebraicGeometry.Space

end
