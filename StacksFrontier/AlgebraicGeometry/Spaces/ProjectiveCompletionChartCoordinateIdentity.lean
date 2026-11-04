module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveCompletionChartCoordinateValue

/-!
# The coordinates of `U ×_X V ⟶ 𝐏((ℰ ⊕ 𝒪)|_V)` are the values of `q`

Let `X` be an algebraic space, `ℰ` a finite locally free `𝒪_X`-module of rank `r`,
`P = 𝐏(ℰ ⊕ 𝒪_X)` with affine part `ι : U ⟶ P`, `u : U ⟶ X` and `q : u^*ℰ ⟶ 𝒪_U` the map
`m ↦ (m, 0)/s`, and `V` an affine étale chart of `X` with a morphism `m` to the presenting chart.
On the scheme of the chart `U_V = U ×_X V` of `U`, the reading of `q` through the canonical
identifications of the sources is the coordinate morphism `c_f = λ(σ'(-)) / λ(σ)` of the open
immersion `f : U ×_X V ⟶ 𝐏((ℰ ⊕ 𝒪)|_V)` (`Stacks.RelativeProj.UnitSplitting.splitCoordMap`) for the
split datum of `ℰ ⊕ 𝒪` on `V` (Stacks 0ERW, proof). Hence, for a trivialization
`e : ℰ|_V ≅ 𝒪_V^{⊕ n}`, the coordinates of `f` are the values of `q` on the inverse images of the
basis sections of `ℰ(V)`.

The statements take as hypotheses the unit compatibility of
`AlgebraicGeometry.Space.chartSectionsReadingEquiv` at `V` and at `U_V`.

## References

* [Stacks Project, Tag 0ERW](https://stacks.math.columbia.edu/tag/0ERW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local instance] HasBinaryBiproducts.of_hasBinaryProducts

attribute [-instance] CategoryTheory.catToReflQuiver

namespace AlgebraicGeometry.Space

attribute [local implicit_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite
  AlgebraicGeometry.Space.CartesianChartFamily.site
  AlgebraicGeometry.BigFppfOver.siteObjectOver
  AlgebraicGeometry.Space.CartesianChartFamily.siteToChart
  AlgebraicGeometry.BigFppfOver.siteMapOver

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
    (E : Modules.{u, u} B S hS X.1 X.2) {r : ℕ}
    (hr : RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS X.1 X.2) E r)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree
      (show SheafOfModules.{u} (structureRingSheaf B S hS X) from E)]
    {V : SmallEtale B S hS X.1} (m : V ⟶ bundleBaseChart X)

/-- The chart `U_V ⟶ U ⟶ P` is `U_V ⟶ P_U ⟶ P`, on points. -/
theorem affinePartChartOverChart_hom_comp :
    (affinePartChartOverChart E hr m).1.hom ≫ (projectiveCompletionAffinePartHom E hr).hom =
      yoneda.map (affinePartOverChartToPresenting E hr m) ≫
        (presentationChart (@projectiveBundleChartPresentation B S hS X (addUnit X.2 E)
          (isQuasicoherentOnSite_addUnit hr) (isFiniteLocallyFreeOnSite_addUnit hr))).1.hom := by
  have h := (@isPullback_splitEpiComplementChart B S hS X (addUnit X.2 E) E
    (isQuasicoherentOnSite_addUnit hr) (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
    biprod.fst biprod.inl biprod.inl_fst (isFiniteLocallyFreeOnSite_addUnit hr)
    hr.isFiniteLocallyFreeOnSite V m).w
  refine h.trans ?_
  exact ((congrArg (· ≫ _) (yoneda.map_comp _ _)).trans (Category.assoc _ _ _)).symm

/-- The chart `U_V ⟶ U` followed by `ι : U ⟶ P` is `U_V ⟶ P_U ⟶ P`. -/
theorem representedSpaceMap_affinePartOverChartToPresenting_comp_atlas :
    representedSpaceMap B S hS (affinePartOverChartToPresenting E hr m) ≫
        @projectiveBundleAtlas B S hS X (addUnit X.2 E) (isQuasicoherentOnSite_addUnit hr)
          (isFiniteLocallyFreeOnSite_addUnit hr) =
      chartToSpace B S hS _ (affinePartChartOverChart E hr m) ≫
        projectiveCompletionAffinePartHom E hr :=
  ObjectProperty.hom_ext _ (affinePartChartOverChart_hom_comp E hr m).symm

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree
      (show SheafOfModules.{u} (structureRingSheaf B S hS X) from E)] in
/-- The presenting chart of `P` followed by `π : P ⟶ X` is `P_U ⟶ U_X ⟶ X`, on points. -/
theorem presentationChart_projectiveCompletion_hom_comp :
    (presentationChart (@projectiveBundleChartPresentation B S hS X (addUnit X.2 E)
          (isQuasicoherentOnSite_addUnit hr) (isFiniteLocallyFreeOnSite_addUnit hr))).1.hom ≫
        (projectiveCompletionProj E hr).hom =
      yoneda.map (@projectiveBundleChartProj B S hS X (addUnit X.2 E)
          (isQuasicoherentOnSite_addUnit hr) (isFiniteLocallyFreeOnSite_addUnit hr)) ≫
        (bundleBaseChart X).1.hom :=
  (@isPullback_projectiveBundleProj B S hS X (addUnit X.2 E) (isQuasicoherentOnSite_addUnit hr)
    (isFiniteLocallyFreeOnSite_addUnit hr)).w

/-- **The identification `u^*𝒪_X ≅ 𝒪_U` through `ι^*𝒪_P` sends the unit section to `1` at the
chart `U_V`.** -/
theorem modulePullbackUnitCompIso_inv_comp_unitIso_unit_affinePartChart :
    ((modulePullbackUnitCompIso (projectiveCompletionAffinePartHom E hr)
        (projectiveCompletionProj E hr)).inv ≫
      (modulePullbackUnitIso B S hS (projectiveCompletionAffinePartHom E hr)).hom).val.app
        (op (affinePartChartOverChart E hr m))
        ((modulePullbackUnitIso B S hS (projectiveCompletionAffinePartProj E hr)).inv.val.app
          (op (affinePartChartOverChart E hr m))
          (1 : (structureRingSheaf B S hS (projectiveCompletionAffinePart E hr)).obj.obj
            (op (affinePartChartOverChart E hr m)))) =
      (1 : (structureRingSheaf B S hS (projectiveCompletionAffinePart E hr)).obj.obj
            (op (affinePartChartOverChart E hr m))) := by
  have h := modulePullbackUnitCompIso_inv_comp_unitIso_unit (projectiveCompletionAffinePartHom E hr)
    (projectiveCompletionProj E hr) (Uc := affinePartChartOverChart E hr m)
    (W := presentationChart (@projectiveBundleChartPresentation B S hS X (addUnit X.2 E)
          (isQuasicoherentOnSite_addUnit hr) (isFiniteLocallyFreeOnSite_addUnit hr)))
    (V := bundleBaseChart X) (affinePartOverChartToPresenting E hr m)
    (@projectiveBundleChartProj B S hS X (addUnit X.2 E)
          (isQuasicoherentOnSite_addUnit hr) (isFiniteLocallyFreeOnSite_addUnit hr))
    (affinePartChartOverChart_hom_comp E hr m)
    (presentationChart_projectiveCompletion_hom_comp E hr)
  with_reducible exact h

/-- The morphism `A = U ×_X V ⟶ V` of the site, in the spelling of the readings. -/
abbrev affinePartChartToChart :
    chartFppfObject B S hS (projectiveCompletionAffinePart E hr) (affinePartChartOverChart E hr m) ⟶
      (SmallEtale.toOver B S hS X.1).obj V :=
  (@splitEpiComplementChartHom B S hS X (addUnit X.2 E) E
      (isQuasicoherentOnSite_addUnit hr) (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
      biprod.fst biprod.inl biprod.inl_fst (isFiniteLocallyFreeOnSite_addUnit hr)
      hr.isFiniteLocallyFreeOnSite V m :
    chartFppfObject B S hS (projectiveCompletionAffinePart E hr) (affinePartChartOverChart E hr m) ⟶
      (@projectiveBundleChartFamily B S hS X (addUnit X.2 E) (isQuasicoherentOnSite_addUnit hr)
        (isFiniteLocallyFreeOnSite_addUnit hr)).site V) ≫
    (@projectiveBundleChartFamily B S hS X (addUnit X.2 E) (isQuasicoherentOnSite_addUnit hr)
      (isFiniteLocallyFreeOnSite_addUnit hr)).siteToChart V

/-- The morphism `A = U ×_X V ⟶ V` followed by `V ⟶ X` is the chart `A ⟶ U` followed by
`π ∘ ι : U ⟶ X`. -/
theorem representedSpaceMap_affinePartChartToChart_comp :
    representedSpaceMap B S hS (affinePartChartToChart E hr m) ≫ chartToSpace B S hS X V =
      chartToSpace B S hS _ (affinePartChartOverChart E hr m) ≫
        (projectiveCompletionAffinePartHom E hr ≫ projectiveCompletionProj E hr) :=
  representedSpaceMap_affinePartOverChartToChart_comp E hr m

/-- The open immersion `A = U ×_X V ⟶ 𝐏((ℰ ⊕ 𝒪)|_V)`, in the spelling of the readings. -/
abbrev affinePartChartToChartBundle :
    (BigFppfOver.toScheme B S hS).obj
        (chartFppfObject B S hS (projectiveCompletionAffinePart E hr)
          (affinePartChartOverChart E hr m)) ⟶
      @chartBundle B S hS X (addUnit X.2 E) (isQuasicoherentOnSite_addUnit hr) V :=
  @chartBundleHomOfSite B S hS X (addUnit X.2 E) (isQuasicoherentOnSite_addUnit hr)
    (isFiniteLocallyFreeOnSite_addUnit hr) V
    (chartFppfObject B S hS (projectiveCompletionAffinePart E hr) (affinePartChartOverChart E hr m))
    (@splitEpiComplementChartHom B S hS X (addUnit X.2 E) E
      (isQuasicoherentOnSite_addUnit hr) (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
      biprod.fst biprod.inl biprod.inl_fst (isFiniteLocallyFreeOnSite_addUnit hr)
      hr.isFiniteLocallyFreeOnSite V m)

/-- The open immersion `A ⟶ 𝐏((ℰ ⊕ 𝒪)|_V)` followed by the projection `𝐏((ℰ ⊕ 𝒪)|_V) ⟶ V` is the
morphism of schemes underlying `A ⟶ V`. -/
theorem affinePartChartToChartBundle_comp :
    affinePartChartToChartBundle E hr m ≫
        @chartBundleToChart B S hS X (addUnit X.2 E) (isQuasicoherentOnSite_addUnit hr) V =
      _root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
        (affinePartChartToChart E hr m).left :=
  rfl

/-- The pullback of `𝒪(1)` to `A` along `A ⟶ 𝐏((ℰ ⊕ 𝒪)|_V)`. -/
abbrev affinePartChartTwist :
    ((BigFppfOver.toScheme B S hS).obj
      (chartFppfObject B S hS (projectiveCompletionAffinePart E hr)
        (affinePartChartOverChart E hr m))).Modules :=
  haveI := @isQuasicoherent_chartBundleModule B S hS X (addUnit X.2 E)
    (isQuasicoherentOnSite_addUnit hr) V
  (Scheme.Modules.pullback (affinePartChartToChartBundle E hr m)).obj
    (Stacks.RelativeProj.tautologicalDatum (chartBundleModule (addUnit X.2 E) V)).twist

/-- The reading of `σ₀` on `V` followed by the pulled-back tautological quotient of
`𝐏((ℰ ⊕ 𝒪)|_V)` along `A ⟶ 𝐏((ℰ ⊕ 𝒪)|_V)`. -/
abbrev affinePartChartQuotientMap {M : Modules.{u, u} B S hS X.1 X.2} (σ₀ : M ⟶ addUnit X.2 E) :
    haveI := @isQuasicoherent_chartBundleModule B S hS X (addUnit X.2 E)
      (isQuasicoherentOnSite_addUnit hr) V
    (Scheme.Modules.pullback
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
        (affinePartChartToChart E hr m).left)).obj
        (schemeReading M (chartToSpace B S hS X V)) ⟶
      (Scheme.Modules.pullback (affinePartChartToChartBundle E hr m)).obj
        (Stacks.RelativeProj.tautologicalDatum (chartBundleModule (addUnit X.2 E) V)).twist :=
  haveI := @isQuasicoherent_chartBundleModule B S hS X (addUnit X.2 E)
    (isQuasicoherentOnSite_addUnit hr) V
  (Scheme.Modules.pullback (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
      (affinePartChartToChart E hr m).left)).map
    (schemeReadingMap (chartToSpace B S hS X V) σ₀) ≫
    (Stacks.RelativeProj.tautologicalDatum (chartBundleModule (addUnit X.2 E) V)).overQuotientMap
      (affinePartChartToChartBundle E hr m) (affinePartChartToChartBundle_comp E hr m)

end AlgebraicGeometry.Space

end
