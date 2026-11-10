module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiCohomology
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionFunctorial
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionReadingsFunctor
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleOpenCoverQuasicoherence

/-!
# The associated module of a scheme module, restricted to an étale chart

Let `Z` be an object of the big fppf site over `S`, with underlying scheme `Z₀`, and `𝒢` a
quasi-coherent `𝒪_{Z₀}`-module. Its associated module `𝒢ᵃ`, read on the small étale site of the
algebraic space `h_Z = yoneda.obj Z`, is `AlgebraicGeometry.Space.representedModuleOf Z 𝒢`. The
Zariski restriction of `𝒢ᵃ` to the scheme of an étale chart `C` of `h_Z`, through the comparison
`ε_* = AlgebraicGeometry.Space.representedZariskiDirectImage`, is the inverse image of `𝒢` along
the morphism of schemes `C₀ ⟶ Z₀` underlying the chart.

## Main definitions

* `AlgebraicGeometry.Space.representedModuleOf`: `𝒢ᵃ`, on the small étale site of `h_Z`.
* `AlgebraicGeometry.Space.restrictToChartSchemeRepresentedModuleOfIso`: the restriction of `𝒢ᵃ`
  to the identity chart is `𝒢`.
* `AlgebraicGeometry.Space.representedEtaleChartToObject`: the morphism of the site underlying an
  étale chart of a represented algebraic space.
* `AlgebraicGeometry.Space.representedZariskiDirectImageChartIso`: `ε_*(𝒢ᵃ|_C) ≅ g^* 𝒢`.
* `AlgebraicGeometry.Space.isTerminalSelfOpensFunctorTop`: the chart of `yoneda.obj U` given by
  the open `⊤` is terminal.

## Main results

* `AlgebraicGeometry.Space.isQuasicoherentOnSite_representedModuleOf`: `𝒢ᵃ` is quasi-coherent.
* `AlgebraicGeometry.Space.isZero_rightDerived_globalSections_represented_of_isZero`: the
  cohomology of a quasi-coherent module on `h_U` vanishes where its Zariski cohomology does.

## References

* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 03M0](https://stacks.math.columbia.edu/tag/03M0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- `𝒢ᵃ`: the associated module of an `𝒪_{Z₀}`-module, read on the small étale site of the
algebraic space `yoneda.obj Z`. -/
abbrev representedModuleOf (Z : BigFppfOver B S hS)
    (G : ((BigFppfOver.toScheme B S hS).obj Z).Modules) :
    SheafOfModules.{u} (representedStructureRingSheaf B S hS Z) :=
  (representedSmallEtaleModuleEquivalence B S hS Z).functor.obj
    ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj Z) Z.left.property).obj G)

/-- The associated module of a quasi-coherent module is quasi-coherent. -/
theorem isQuasicoherentOnSite_representedModuleOf (Z : BigFppfOver B S hS)
    (G : ((BigFppfOver.toScheme B S hS).obj Z).Modules) (hG : G.IsQuasicoherent) :
    (representedModuleOf B S hS Z G).IsQuasicoherentOnSite :=
  (isQuasicoherentOnSite_representedSmallEtaleModule_iff B S hS Z _).2
    (_root_.AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_associatedModule_of_isQuasicoherent
      (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj Z) Z.left.property G hG)

/-- **The restriction of `𝒢ᵃ` to the identity chart is `𝒢`**, for a quasi-coherent
`𝒪_{Z₀}`-module `𝒢`. -/
def restrictToChartSchemeRepresentedModuleOfIso (Z : BigFppfOver B S hS)
    (G : ((BigFppfOver.toScheme B S hS).obj Z).Modules) (hG : G.IsQuasicoherent) :
    restrictToChartScheme B S hS (yoneda.obj Z) (isAlgebraicSpace_yoneda B S hS Z)
        (representedModuleOf B S hS Z G) (idEtaleChart B S hS Z) ≅ G :=
  restrictToChartSchemeIdEtaleChartIso B S hS Z _ ≪≫
    (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj Z) Z.left.property).mapIso
        ((representedSmallEtaleModuleEquivalence B S hS Z).unitIso.app _).symm ≪≫
    (restrictModuleAssociatedModuleIsoSelf G hG).symm

/-- The morphism of the site underlying an étale chart of a represented algebraic space: the
chart's structure morphism of presheaves is represented by it. -/
def representedEtaleChartToObject {Z : BigFppfOver B S hS} (C : SmallEtale B S hS (yoneda.obj Z)) :
    (SmallEtale.toOver B S hS (yoneda.obj Z)).obj C ⟶ Z :=
  Yoneda.fullyFaithful.preimage C.obj.hom

/-- The Yoneda image of `representedEtaleChartToObject B S hS C` is the structure morphism of the
chart `C`. -/
theorem yoneda_map_representedEtaleChartToObject {Z : BigFppfOver B S hS}
    (C : SmallEtale B S hS (yoneda.obj Z)) :
    yoneda.map (representedEtaleChartToObject B S hS C) = C.obj.hom :=
  Yoneda.fullyFaithful.map_preimage _

/-- **The restriction of `𝒢ᵃ` to an étale chart, read on the chart's scheme, is the inverse image
of `𝒢`.**  For a quasi-coherent `𝒪_{Z₀}`-module `𝒢` and an étale chart `C` of `yoneda.obj Z`,
`ε_*(𝒢ᵃ|_C) ≅ g^* 𝒢`, where `g : C₀ ⟶ Z₀` underlies the chart. -/
def representedZariskiDirectImageChartIso (Z : BigFppfOver B S hS)
    (G : ((BigFppfOver.toScheme B S hS).obj Z).Modules) (hG : G.IsQuasicoherent)
    (C : SmallEtale B S hS (yoneda.obj Z)) :
    (representedZariskiDirectImage B S hS ((SmallEtale.toOver B S hS (yoneda.obj Z)).obj C)).obj
        ((etaleModulePullback B S hS (chartToSpace B S hS (schemeSpace Z) C)
          (isEtale_chartToSpace B S hS (schemeSpace Z) C)).obj (representedModuleOf B S hS Z G)) ≅
      (Scheme.Modules.pullback
        ((BigFppfOver.toScheme B S hS).map (representedEtaleChartToObject B S hS C))).obj G := by
  set T := (SmallEtale.toOver B S hS (yoneda.obj Z)).obj C
  set M := representedModuleOf B S hS Z G
  have hM := isQuasicoherentOnSite_representedModuleOf B S hS Z G hG
  set N := (etaleModulePullback B S hS (chartToSpace B S hS (schemeSpace Z) C)
    (isEtale_chartToSpace B S hS (schemeSpace Z) C)).obj M
  refine (restrictToChartSchemeIdEtaleChartIso B S hS T N ≪≫
    selfOpensPushforwardIso B S hS T N).symm ≪≫ ?_
  refine (restrictToChartIsoRestrictToChartScheme B S hS (isAlgebraicSpace_yoneda B S hS T) N
    (idEtaleChart B S hS T)).symm ≪≫ ?_
  refine (restrictToChartFunctor B S hS (isAlgebraicSpace_yoneda B S hS T)
    (idEtaleChart B S hS T)).mapIso ((modulePullbackIsoEtaleModulePullback B S hS
      (chartToSpace B S hS (schemeSpace Z) C)
      (isEtale_chartToSpace B S hS (schemeSpace Z) C)).app M).symm ≪≫ ?_
  refine (restrictToChartBaseChangeIso B S hS (chartToSpace B S hS (schemeSpace Z) C) M hM
    (idEtaleChart B S hS Z) (idEtaleChart B S hS T) (representedEtaleChartToObject B S hS C)
    ?_).symm ≪≫ ?_
  · change yoneda.map (representedEtaleChartToObject B S hS C) ≫ 𝟙 _ = 𝟙 _ ≫ C.obj.hom
    rw [Category.comp_id, Category.id_comp, yoneda_map_representedEtaleChartToObject]
  exact (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map
    (representedEtaleChartToObject B S hS C))).mapIso
      (restrictToChartIsoRestrictToChartScheme B S hS (isAlgebraicSpace_yoneda B S hS Z) M
        (idEtaleChart B S hS Z) ≪≫ restrictToChartSchemeRepresentedModuleOfIso B S hS Z G hG)

/-- The étale chart of `yoneda.obj U` that the open `⊤` of the scheme underlying `U` becomes is
terminal. -/
def isTerminalSelfOpensFunctorTop (U : BigFppfOver B S hS) :
    IsTerminal ((selfOpensFunctor B S hS U).obj ⊤) :=
  IsTerminal.ofUniqueHom
    (fun V => (representedImageOpenAdjunctionSelf B S hS U).homEquiv V ⊤ (isTerminalTop.from _))
    (fun V _ => ((representedImageOpenAdjunctionSelf B S hS U).homEquiv V ⊤).symm.injective
      (Subsingleton.elim _ _))

/-- **Vanishing of cohomology on a scheme read as an algebraic space, from Zariski vanishing.**
For a quasi-coherent `𝒪_{h_U}`-module `N`, `H^q(h_U, N) = 0` as soon as the Zariski cohomology
`H^q(U₀, ε_* N)` vanishes. -/
theorem isZero_rightDerived_globalSections_represented_of_isZero (U : BigFppfOver B S hS)
    (N : SheafOfModules.{u} (representedStructureRingSheaf B S hS U))
    (hN : N.IsQuasicoherentOnSite) (q : ℕ)
    (h : IsZero ((((SheafOfModules.evaluation.{u}
      (chartScheme (idEtaleChart B S hS U)).ringCatSheaf (op ⊤))).rightDerived q).obj
        ((representedZariskiDirectImage B S hS U).obj N))) :
    have := hasInjectiveResolutions_modules B S hS (schemeSpace U).1 (schemeSpace U).2
    IsZero (((Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (schemeSpace U).1
        (schemeSpace U).2).O)).rightDerived q).obj N) := by
  have := hasInjectiveResolutions_modules B S hS (schemeSpace U).1 (schemeSpace U).2
  have := hasInjectiveResolutions_representedModules B S hS U
  have h1 : IsZero ((ModuleCat.restrictScalars (representedTopRingHom B S hS U)).obj
      (((SheafOfModules.evaluation.{u} (representedStructureRingSheaf B S hS U)
        (op ((selfOpensFunctor B S hS U).obj ⊤))).rightDerived q).obj N)) :=
    h.of_iso (representedZariskiCohomologyIso B S hS U N hN q)
  exact isZero_rightDerived_globalSections_of_isTerminalChart B S hS (schemeSpace U)
    (isTerminalSelfOpensFunctorTop B S hS U) N q
    (by rw [ModuleCat.isZero_iff_subsingleton] at h1 ⊢; assumption)

end AlgebraicGeometry.Space

end
