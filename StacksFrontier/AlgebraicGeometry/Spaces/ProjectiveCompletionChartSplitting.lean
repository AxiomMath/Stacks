module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveCompletionVectorBundleChartSquare
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.SplitQuotientComplementAffineSpace

/-!
# The split datum of the projective completion on an étale chart

Let `X` be an algebraic space and `ℰ` a finite locally free `𝒪_X`-module. On the scheme of an
étale chart `V` of `X` the readings of `ℰ ⊕ 𝒪_X ⟶ ℰ`, `ℰ ⟶ ℰ ⊕ 𝒪_X` and of the summand `𝒪_X`
form a split short exact sequence `0 ⟶ 𝒪_V ⟶ (ℰ ⊕ 𝒪)|_V ⟶ ℰ|_V ⟶ 0`
(`Stacks.RelativeProj.UnitSplitting`), the input of the identification of the complement of
`𝐏(ℰ|_V)` in `𝐏((ℰ ⊕ 𝒪)|_V)` with affine space (Stacks 0ERW, proof).

## Main definitions

* `AlgebraicGeometry.Space.chartUnitReadingIso`: the reading of `𝒪_X` on a chart is `𝒪_V`.
* `AlgebraicGeometry.Space.completionChartUnitSplitting`: the split datum on a chart.
* `AlgebraicGeometry.Space.affinePartOverChartToChartBundle`: the open immersion
  `U ×_X V ⟶ 𝐏((ℰ ⊕ 𝒪)|_V)`.
* `AlgebraicGeometry.Space.affinePartOverChartIsoComplement`: the isomorphism of `U ×_X V` with
  the complement of `𝐏(ℰ|_V)` in `𝐏((ℰ ⊕ 𝒪)|_V)`.

## Main results

* `AlgebraicGeometry.Space.range_affinePartOverChartToChartBundle`: the image of `U ×_X V` in
  `𝐏((ℰ ⊕ 𝒪)|_V)` is the complement of `𝐏(ℰ|_V)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [local instance] HasBinaryBiproducts.of_hasBinaryProducts

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}

/-- The identification of the reading of `𝒪_X` on an étale chart `V` with `𝒪_V`. -/
abbrev chartUnitReadingIso (V : SmallEtale B S hS X.1) :
    schemeReading (T := (SmallEtale.toOver B S hS X.1).obj V)
        (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O))) (chartToSpace B S hS X V) ≅
      Scheme.unitModule (chartScheme V) :=
  schemeReadingChartIso _ _ ≪≫ restrictToChartSchemeUnitIso B S hS X.1 X.2 _

variable (E : Modules.{u, u} B S hS X.1 X.2) (V : SmallEtale B S hS X.1)

/-- **The split datum of `0 ⟶ 𝒪 ⟶ ℰ ⊕ 𝒪 ⟶ ℰ ⟶ 0` on the scheme of an étale chart.** -/
def completionChartUnitSplitting :
    Stacks.RelativeProj.UnitSplitting (chartModuleMap (biprod.fst : addUnit X.2 E ⟶ E) V) where
  σ := (chartUnitReadingIso V).inv ≫ chartModuleMap (addUnitInr X.2 E) V
  τ := chartModuleMap (addUnitSnd X.2 E) V ≫ (chartUnitReadingIso V).hom
  σ' := chartModuleMap (biprod.inl : E ⟶ addUnit X.2 E) V
  hsplit := by
    have hs : addUnitSnd X.2 E ≫ addUnitInr X.2 E + biprod.fst ≫ biprod.inl =
        𝟙 (addUnit X.2 E) := by
      rw [add_comm]
      exact biprod.total
    rw [Category.assoc, Iso.hom_inv_id_assoc]
    exact ((congrArg₂ (· + ·)
        (schemeReadingMap_comp (T := (SmallEtale.toOver B S hS X.1).obj V)
          (chartToSpace B S hS X V) _ _).symm
        (schemeReadingMap_comp (T := (SmallEtale.toOver B S hS X.1).obj V)
          (chartToSpace B S hS X V) _ _).symm).trans
      (schemeReadingMap_add (T := (SmallEtale.toOver B S hS X.1).obj V)
        (chartToSpace B S hS X V) _ _).symm).trans
      ((congrArg (schemeReadingMap (T := (SmallEtale.toOver B S hS X.1).obj V)
        (chartToSpace B S hS X V)) hs).trans
        (schemeReadingMap_id (T := (SmallEtale.toOver B S hS X.1).obj V)
          (chartToSpace B S hS X V)))
  hσu := by
    have h : chartModuleMap (addUnitInr X.2 E) V ≫
        chartModuleMap (biprod.fst : addUnit X.2 E ⟶ E) V = 0 :=
      (schemeReadingMap_comp (T := (SmallEtale.toOver B S hS X.1).obj V)
          (chartToSpace B S hS X V) _ _).symm.trans
        ((congrArg (schemeReadingMap (T := (SmallEtale.toOver B S hS X.1).obj V)
          (chartToSpace B S hS X V)) biprod.inr_fst).trans
          (schemeReadingMap_zero (T := (SmallEtale.toOver B S hS X.1).obj V)
            (chartToSpace B S hS X V)))
    rw [Category.assoc, h, comp_zero]
  hστ := by
    have h : chartModuleMap (addUnitInr X.2 E) V ≫ chartModuleMap (addUnitSnd X.2 E) V = 𝟙 _ :=
      (schemeReadingMap_comp (T := (SmallEtale.toOver B S hS X.1).obj V)
          (chartToSpace B S hS X V) _ _).symm.trans
        ((congrArg (schemeReadingMap (T := (SmallEtale.toOver B S hS X.1).obj V)
          (chartToSpace B S hS X V)) biprod.inr_snd).trans
          (schemeReadingMap_id (T := (SmallEtale.toOver B S hS X.1).obj V)
            (chartToSpace B S hS X V)))
    rw [Category.assoc, ← Category.assoc (chartModuleMap (addUnitInr X.2 E) V), h,
      Category.id_comp, Iso.inv_hom_id]
  hσ'τ := by
    have h : chartModuleMap (biprod.inl : E ⟶ addUnit X.2 E) V ≫
        chartModuleMap (addUnitSnd X.2 E) V = 0 :=
      (schemeReadingMap_comp (T := (SmallEtale.toOver B S hS X.1).obj V)
          (chartToSpace B S hS X V) _ _).symm.trans
        ((congrArg (schemeReadingMap (T := (SmallEtale.toOver B S hS X.1).obj V)
          (chartToSpace B S hS X V)) biprod.inl_snd).trans
          (schemeReadingMap_zero (T := (SmallEtale.toOver B S hS X.1).obj V)
            (chartToSpace B S hS X V)))
    rw [← Category.assoc, h, zero_comp]
  hσ'u :=
    (schemeReadingMap_comp (T := (SmallEtale.toOver B S hS X.1).obj V)
        (chartToSpace B S hS X V) _ _).symm.trans
      ((congrArg (schemeReadingMap (T := (SmallEtale.toOver B S hS X.1).obj V)
        (chartToSpace B S hS X V)) biprod.inl_fst).trans
        (schemeReadingMap_id (T := (SmallEtale.toOver B S hS X.1).obj V)
          (chartToSpace B S hS X V)))

attribute [local implicit_reducible] AlgebraicGeometry.Space.CartesianChartFamily.site
  AlgebraicGeometry.BigFppfOver.siteObjectOver

variable {r : ℕ}
    (hr : RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS X.1 X.2) E r)
    {V} (m : V ⟶ bundleBaseChart X)

/-- The open immersion `U ×_X V ⟶ 𝐏((ℰ ⊕ 𝒪)|_V)` of schemes. -/
abbrev affinePartOverChartToChartBundle :
    (BigFppfOver.toScheme B S hS).obj (projectiveCompletionAffinePartOverChart E hr m) ⟶
      @chartBundle B S hS X (addUnit X.2 E) (isQuasicoherentOnSite_addUnit hr) V :=
  (BigFppfOver.toScheme B S hS).map (@splitEpiComplementChartHom B S hS X (addUnit X.2 E) E
    (isQuasicoherentOnSite_addUnit hr) (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
    biprod.fst biprod.inl biprod.inl_fst (isFiniteLocallyFreeOnSite_addUnit hr)
    hr.isFiniteLocallyFreeOnSite V m)

/-- The morphism `affinePartOverChartToChartBundle` is an open immersion. -/
instance : _root_.AlgebraicGeometry.IsOpenImmersion (affinePartOverChartToChartBundle E hr m) :=
  @isOpenImmersion_splitEpiComplementChartHom B S hS X (addUnit X.2 E) E
    (isQuasicoherentOnSite_addUnit hr) (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
    biprod.fst biprod.inl biprod.inl_fst (isFiniteLocallyFreeOnSite_addUnit hr)
    hr.isFiniteLocallyFreeOnSite V m

/-- The image of `U ×_X V` in `𝐏((ℰ ⊕ 𝒪)|_V)` is the complement of `𝐏(ℰ|_V)`. -/
theorem range_affinePartOverChartToChartBundle :
    Set.range (affinePartOverChartToChartBundle E hr m).base =
      Set.range (@Stacks.RelativeProj.splitQuotientComplement _ _ _
        (@isQuasicoherent_chartBundleModule B S hS X (addUnit X.2 E)
          (isQuasicoherentOnSite_addUnit hr) V)
        (@isQuasicoherent_chartBundleModule B S hS X E
          (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr) V)
        (chartModuleMap (biprod.fst : addUnit X.2 E ⟶ E) V)
        (epi_chartModuleMap biprod.fst biprod.inl biprod.inl_fst V)).ι.base := by
  rw [Scheme.Opens.range_ι]
  have h0 := @range_splitEpiComplementChartHom B S hS X (addUnit X.2 E) E
    (isQuasicoherentOnSite_addUnit hr) (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
    biprod.fst biprod.inl biprod.inl_fst (isFiniteLocallyFreeOnSite_addUnit hr)
    hr.isFiniteLocallyFreeOnSite V m
  exact h0

/-- **`U ×_X V` is the open complement of `𝐏(ℰ|_V)` in `𝐏((ℰ ⊕ 𝒪)|_V)`.** -/
def affinePartOverChartIsoComplement :
    (BigFppfOver.toScheme B S hS).obj (projectiveCompletionAffinePartOverChart E hr m) ≅
      (@Stacks.RelativeProj.splitQuotientComplement _ _ _
        (@isQuasicoherent_chartBundleModule B S hS X (addUnit X.2 E)
          (isQuasicoherentOnSite_addUnit hr) V)
        (@isQuasicoherent_chartBundleModule B S hS X E
          (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr) V)
        (chartModuleMap (biprod.fst : addUnit X.2 E ⟶ E) V)
        (epi_chartModuleMap biprod.fst biprod.inl biprod.inl_fst V)).toScheme :=
  IsOpenImmersion.isoOfRangeEq _ _ (range_affinePartOverChartToChartBundle E hr m)

/-- The isomorphism `affinePartOverChartIsoComplement` followed by the inclusion of the complement
of `𝐏(ℰ|_V)` is the open immersion `affinePartOverChartToChartBundle`. -/
theorem affinePartOverChartIsoComplement_hom_ι :
    (affinePartOverChartIsoComplement E hr m).hom ≫
        (@Stacks.RelativeProj.splitQuotientComplement _ _ _
          (@isQuasicoherent_chartBundleModule B S hS X (addUnit X.2 E)
          (isQuasicoherentOnSite_addUnit hr) V)
          (@isQuasicoherent_chartBundleModule B S hS X E
            (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr) V)
          (chartModuleMap (biprod.fst : addUnit X.2 E ⟶ E) V)
          (epi_chartModuleMap biprod.fst biprod.inl biprod.inl_fst V)).ι =
      affinePartOverChartToChartBundle E hr m :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

end AlgebraicGeometry.Space

end
