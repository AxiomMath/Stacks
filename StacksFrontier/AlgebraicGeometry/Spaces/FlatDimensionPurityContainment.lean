module

public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.ChartDiagramRelativeAssassin
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.SpaceContainmentGeneralBase
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.SpaceContainmentNeighbourhood
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleOpenOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibreConditions
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.PurityClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.RelativelyPureModules
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatDimensionPresentedLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicPullbackWeaklyAssociated
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperPushforwardFibreLength
public import StacksFrontier.AlgebraicGeometry.Spaces.ZeroLocusClosedUnconditional
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.SpaceRelativeEtaleInvariance

/-!
# Purity spreads the containment of the relative assassin

This is the step of the proof of Stacks 0CX1 that uses purity. In Situation 0CWU with `f` and
`F` of finite presentation and `F` pure relative to `Y`, let `V` be an affine test scheme whose
structure morphism to `Y` is locally quasi-finite, and let `U` be an affine surjective étale chart
of `X_V`. If an open `O` of `U` contains the fibre over a point `v` of `V`, then over an open
neighbourhood of `v` every point of the relative assassin of the chart lies over the same point
of `X_V` as some point of `O`.

The source's argument: the image `W` of `O` in `|X_V|` is open and quasi-compact over `V`, the set
`E = {t ∈ V : Ass_{X_t}(F_t) ⊆ W}` is locally constructible by Divisors on Spaces 0CVV, it
contains every generalization of `v` because `F` is pure along the fibre over `v`, and so it is a
neighbourhood of `v` by Morphisms 05LW.

## Main definitions

* `AlgebraicGeometry.Space.FlatDimensionSituation.fpPrePureSituation`: the pre-pure situation of
  Stacks 0CV6 of Situation 0CWU when `f` is of finite presentation; finite presentation makes `f`
  of finite type and decent.

## Main results

* `AlgebraicGeometry.Space.FlatDimensionSituation.exists_specializes_of_isPureAbove`: purity
  specializes every point of the relative assassin of `X_V` over a generalization of `v` into the
  fibre over `v`.
* `AlgebraicGeometry.Space.FlatDimensionSituation.exists_isOpen_relativeAssassin_subset_image`:
  the spreading out of the containment.

## References

* [Stacks Project, Tag 0CX1](https://stacks.math.columbia.edu/tag/0CX1)
* [Stacks Project, Tag 0CVD](https://stacks.math.columbia.edu/tag/0CVD)
* [Stacks Project, Tag 0CVV](https://stacks.math.columbia.edu/tag/0CVV)
* [Stacks Project, Tag 05LW](https://stacks.math.columbia.edu/tag/05LW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] pointTopology

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for pullbacks in the presheaf category over the big fppf site times out
-- at the default limit
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_FlatDimensionPurityContainment :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

/-- Shortcut for pullbacks of presheaves on the big fppf site over `S`. -/
local instance (priority := high) hasPullback_presheaf_FlatDimensionPurityContainment
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

namespace FlatDimensionSituation

variable (D : FlatDimensionSituation.{u} B S hS)

/-- **The pre-pure situation of Situation 0CWU with `f` of finite presentation**, at a point `y`
of `Y`: a morphism of finite presentation is of finite type and decent, which is what Situation
0CV6 asks, and the module of Situation 0CWU is of finite type and quasi-coherent. -/
abbrev fpPrePureSituation (hf : IsFinitePresentation B S hS D.f.hom)
    (y : points B S hS D.Y.1) : PrePureSituation.{u, u} B S hS :=
  { X := D.X.1
    Y := D.Y.1
    hX := D.X.2
    hY := D.Y.2
    f := D.f.hom
    finiteType := isFiniteType_of_isFinitePresentation B S hS hf
    decent := isDecent_of_isFinitePresentation B S hS D.f hf
    F := D.F
    moduleFiniteType := D.finiteType
    moduleQuasicoherent := D.quasicoherent
    y := y }

/-- The base change `X_T` as the fibre product `T ×_Y X` of the impurity diagrams of Stacks 0CV7:
the symmetry isomorphism of fibre products. -/
def baseChangeIsoImpurity (T : SchemesOver D.Y) :
    (baseChangeSpace D.f T).1 ≅ pullback T.hom.hom D.f.hom :=
  pullbackSymmetry D.f.hom T.hom.hom

/-- The isomorphism `baseChangeIsoImpurity` followed by the projection `T ×_Y X ⟶ T` is the
morphism `baseChangeInclusion D.f T` from `X_T` to `T`. -/
theorem baseChangeIsoImpurity_hom_fst (T : SchemesOver D.Y) :
    (D.baseChangeIsoImpurity T).hom ≫ pullback.fst T.hom.hom D.f.hom =
      (baseChangeInclusion D.f T).hom :=
  pullbackSymmetry_hom_comp_fst _ _

/-- The isomorphism `baseChangeIsoImpurity` followed by the projection `T ×_Y X ⟶ X` is the
morphism `baseChangeProjection D.f T` from `X_T` to `X`. -/
theorem baseChangeIsoImpurity_hom_snd (T : SchemesOver D.Y) :
    (D.baseChangeIsoImpurity T).hom ≫ pullback.snd T.hom.hom D.f.hom =
      (baseChangeProjection D.f T).hom :=
  pullbackSymmetry_hom_comp_snd _ _

/-- **Purity specializes the relative assassin into the fibre.** Let `T` be a test scheme whose
structure morphism to `Y` is locally quasi-finite, let `t ⤳ v` be a specialization in `T`, and
let `ξ` be a point of `Ass_{X_T/T}(F_T)` over `t`. If `F` is pure relative to `Y`, then `ξ`
specializes to a point of `X_T` over `v`.

The impurity diagram is `(T ⟶ Y, t ⤳ v, ξ)`. Its structure morphism is quasi-finite at `v`, so
purity of `F` above the image of `v` says it is not an impurity; since `ξ` is in the relative
assassin, `v` is the image of a point of the closure of `ξ`. -/
theorem exists_specializes_of_isPureAbove (hf : IsFinitePresentation B S hS D.f.hom)
    (hpure : ∀ y, IsPureAbove (D.fpPrePureSituation hf y)) (T : SchemesOver D.Y)
    (hqf : IsLocallyQuasiFinite B S hS T.hom.hom)
    {t v : (BigFppfOver.toScheme B S hS).obj T.left} (htv : t ⤳ v)
    {ξ : points B S hS (baseChangeSpace D.f T).1}
    (hξ : IsRelativeWeaklyAssociatedPoint B S hS (baseChangeInclusion D.f T)
      (D.toFlatnessSituation.baseChangeModule T) ξ)
    (hξt : pointsToScheme B S hS T.left
      (pointsMap B S hS _ (baseChangeInclusion D.f T).hom ξ) = t) :
    ∃ θ : points B S hS (baseChangeSpace D.f T).1, ξ ⤳ θ ∧
      pointsToScheme B S hS T.left
        (pointsMap B S hS _ (baseChangeInclusion D.f T).hom θ) = v := by
  set e := D.baseChangeIsoImpurity T
  set P := D.fpPrePureSituation hf
    (pointsMap B S hS _ T.hom.hom ((pointsEquivScheme B S hS T.left).symm v))
  have hinv : pointsMap B S hS _ e.inv (pointsMap B S hS _ e.hom ξ) = ξ := by
    rw [← pointsMap_comp_apply, Iso.hom_inv_id, pointsMap_id, id_eq]
  have hinvfst : e.inv ≫ (baseChangeInclusion D.f T).hom = pullback.fst T.hom.hom D.f.hom := by
    rw [Iso.inv_comp_eq, D.baseChangeIsoImpurity_hom_fst T]
  have ht' : pointsMap B S hS _ (pullback.fst T.hom.hom D.f.hom) (pointsMap B S hS _ e.hom ξ) =
      (pointsEquivScheme B S hS T.left).symm t := by
    rw [← pointsMap_comp_apply, D.baseChangeIsoImpurity_hom_fst T, ← hξt]
    exact ((pointsEquivScheme B S hS T.left).symm_apply_apply _).symm
  let Dg : ImpurityDiagram P :=
    { T := T.left
      g := T.hom.hom
      t' := (pointsEquivScheme B S hS T.left).symm t
      t := (pointsEquivScheme B S hS T.left).symm v
      specializes := by
        change (pointsEquivScheme B S hS T.left) ((pointsEquivScheme B S hS T.left).symm t) ⤳
          (pointsEquivScheme B S hS T.left) ((pointsEquivScheme B S hS T.left).symm v)
        simpa only [Equiv.apply_symm_apply] using htv
      mapsToChosenPoint := rfl
      xi := pointsMap B S hS _ e.hom ξ
      xi_liesOver := ht' }
  have hass : Dg.IsRelativeWeakAssassinPoint Dg.xi := by
    rw [ImpurityDiagram.isRelativeWeakAssassinPoint_iff]
    let φ : P.baseChangeSpace Dg.T Dg.g ⟶ baseChangeSpace D.f T := ObjectProperty.homMk e.inv
    have hcomp : φ ≫ baseChangeInclusion D.f T = P.baseChangeToBase Dg.T Dg.g := by
      apply ObjectProperty.hom_ext
      exact hinvfst
    have hcompX : φ ≫ baseChangeProjection D.f T = P.baseChangeToSource Dg.T Dg.g := by
      apply ObjectProperty.hom_ext
      change e.inv ≫ (baseChangeProjection D.f T).hom = pullback.snd T.hom.hom D.f.hom
      rw [Iso.inv_comp_eq, D.baseChangeIsoImpurity_hom_snd T]
    have hmod : (modulePullback B S hS φ).obj (D.toFlatnessSituation.baseChangeModule T) ≅
        P.baseChangeModule Dg.T Dg.g :=
      ((modulePullbackTriangle B S hS hcompX).app D.F).symm
    have h1 := (isRelativeWeaklyAssociatedPoint_modulePullback_iff B S hS φ
      (isEtale_of_presheaf_etale B S hS (presheaf_etale_of_iso B S hS e.symm))
      (baseChangeInclusion D.f T) (D.toFlatnessSituation.baseChangeModule T) Dg.xi).2 (by
        change IsRelativeWeaklyAssociatedPoint B S hS _ _
          (pointsMap B S hS _ e.inv (pointsMap B S hS _ e.hom ξ))
        rwa [hinv])
    rw [hcomp] at h1
    exact (isRelativeWeaklyAssociatedPoint_congr (P.baseChangeToBase Dg.T Dg.g) hmod Dg.xi).1 h1
  obtain ⟨θ', hθ'spec, hθ'⟩ := Dg.mem_image_closure_xi_iff.1 <| not_not.1 fun hcon ↦
    hpure _ Dg (isQuasiFiniteAt_of_isLocallyQuasiFinite B S hS
      (isAlgebraicSpace_yoneda B S hS T.left) hqf _) ⟨hass, hcon⟩
  refine ⟨pointsMap B S hS _ e.inv θ', ?_, ?_⟩
  · rw [← hinv]
    exact hθ'spec.map (continuous_pointsMap B S hS e.inv)
  · have h2 : pointsMap B S hS _ (baseChangeInclusion D.f T).hom (pointsMap B S hS _ e.inv θ') =
        pointsMap B S hS _ (pullback.fst T.hom.hom D.f.hom) θ' := by
      rw [← hinvfst]
      exact (congrFun (pointsMap_comp B S hS _ e.inv _) θ').symm
    refine (congrArg (pointsToScheme B S hS T.left) h2).trans ?_
    change pointsToScheme B S hS T.left (pointsMap B S hS Dg.baseChange Dg.toT θ') = v
    rw [hθ']
    exact (pointsEquivScheme B S hS T.left).apply_symm_apply v

/-- A point of an étale chart of `X_T` and its image in the scheme underlying `T` determine the
same point of `T`: the chart morphism of the presented situation reads the map `X_T ⟶ T` on
points. -/
theorem pointsToScheme_pointsMap_chartSchemeToPoints (n : ℕ) (T : SchemesOver D.Y)
    (U : SmallEtale B S hS (baseChangeSpace D.f T).1) (z : chartScheme U) :
    pointsToScheme B S hS T.left (pointsMap B S hS _ (baseChangeInclusion D.f T).hom
      (chartSchemeToPoints B S hS _ U z)) = (D.stageSituation B S hS n T U).f z := by
  have h := chartSchemeToPoints_map_chartDiagram B S hS
    (identityTargetChartDiagram B S hS (baseChangeInclusion D.f T) U) z
  have h' : (pointsEquivScheme B S hS T.left).symm ((D.stageSituation B S hS n T U).f z) =
      pointsMap B S hS _ (baseChangeInclusion D.f T).hom (chartSchemeToPoints B S hS _ U z) :=
    (chartSchemeToPoints_idEtaleChart B S hS T.left _).symm.trans h
  exact (congrArg (pointsToScheme B S hS T.left) h').symm.trans
    ((pointsEquivScheme B S hS T.left).apply_symm_apply _)

/-- The map from the scheme of an étale chart to the points of the space is open. -/
theorem isOpenMap_chartSchemeToPoints (X : AlgebraicSpaces B S hS)
    (U : SmallEtale B S hS X.1) : IsOpenMap (chartSchemeToPoints B S hS X.1 U) := by
  have h : chartSchemeToPoints B S hS X.1 U = pointsMap B S hS
      (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj U)) U.obj.hom ∘
        (schemePointsHomeomorph B S hS ((SmallEtale.toOver B S hS X.1).obj U)).symm := by
    funext x
    exact chartSchemeToPoints_eq_pointsMap_pointsEquivScheme_symm B S hS X.1 U x
  rw [h]
  exact (isOpenMap_pointsMap_of_isEtale B S hS U.obj.hom
    (isAlgebraicSpace_yoneda B S hS _) X.2
    ((isEtale_iff_presheaf_of_yoneda B S hS U.obj.hom).2 U.property)).comp
      (Homeomorph.isOpenMap _)

/-- A quasi-compact open between the fibre of a quasi-compact morphism over a point and a given
open containing it. -/
theorem _root_.AlgebraicGeometry.exists_isCompact_isOpen_fibre_subset {X Y : Scheme.{u}}
    (f : X ⟶ Y) [QuasiCompact f] (y : Y) {O : Set X} (hO : IsOpen O) (h : f ⁻¹' {y} ⊆ O) :
    ∃ K : Set X, IsCompact K ∧ IsOpen K ∧ f ⁻¹' {y} ⊆ K ∧ K ⊆ O := by
  have hKO : Set.range (f.fiberι y) ⊆ O := by rwa [f.range_fiberι]
  obtain ⟨K, hKc, hKo, hfibK, hKO'⟩ :=
    PrespectralSpace.exists_isCompact_and_isOpen_between
      (isCompact_range (f.fiberι y).continuous) hO hKO
  refine ⟨K, hKc, hKo, ?_, hKO'⟩
  rwa [← f.range_fiberι]

/-- In a quasi-separated scheme, a quasi-compact open meets the preimage of a quasi-compact open
under a quasi-compact morphism in a quasi-compact set. -/
theorem _root_.AlgebraicGeometry.isCompact_inter_preimage {X Y : Scheme.{u}}
    [QuasiSeparatedSpace X] (f : X ⟶ Y) [QuasiCompact f] {K : Set X} (hKo : IsOpen K)
    (hKc : IsCompact K) {A : Set Y} (hAo : IsOpen A) (hAc : IsCompact A) :
    IsCompact (K ∩ f ⁻¹' A) :=
  QuasiSeparatedSpace.inter_isCompact _ _ hKo hKc (hAo.preimage f.continuous)
    (QuasiCompact.isCompact_preimage _ hAo hAc)

/-- **The containment of the relative assassin spreads out, by purity.** Let `T` be an affine
test scheme whose structure morphism to `Y` is locally quasi-finite, `U` an affine surjective
étale chart of `X_T`, `v` a point of `T` and `O` an open of `U` containing the fibre of `U` over
`v`. Then there is an open neighbourhood `W` of `v` such that every point of the relative
assassin of the presented situation lying over `W` has the same image in `|X_T|` as some point
of `O`.

The image `W'` of a quasi-compact open `K` between the fibre and `O` is open in `|X_T|` and
quasi-compact over `T`; the locus of points of `T` over which `Ass_{X_T/T}(F_T)` lies in `W'` is
locally constructible by Stacks 0CVV; it contains every generalization of `v` by purity
(`exists_specializes_of_isPureAbove`), the open `W'` containing the fibre over `v`; so it is a
neighbourhood of `v` by Stacks 05LW. A point of the relative assassin of the chart lies in
`Ass_{X_T/T}(F_T)`, and so lies over `W'`. -/
theorem exists_isOpen_relativeAssassin_subset_image (hf : IsFinitePresentation B S hS D.f.hom)
    (hF : SheafOfModules.IsFinitePresentationOnSite D.F)
    (hpure : ∀ y, IsPureAbove (D.fpPrePureSituation hf y)) (n : ℕ) (T : SchemesOver D.Y)
    (hTaff : IsAffine ((BigFppfOver.toScheme B S hS).obj T.left))
    (hqf : IsLocallyQuasiFinite B S hS T.hom.hom)
    (U : SmallEtale B S hS (baseChangeSpace D.f T).1) (hU : IsSurjective B S hS U.obj.hom)
    (hUaff : IsAffine (chartScheme U)) (v : (BigFppfOver.toScheme B S hS).obj T.left)
    (O : Set (chartScheme U)) (hO : IsOpen O)
    (hvO : (D.stageSituation B S hS n T U).f ⁻¹' {v} ⊆ O) :
    ∃ W : Set ((BigFppfOver.toScheme B S hS).obj T.left), IsOpen W ∧ v ∈ W ∧
      ∀ x ∈ Stacks.Divisors.relativeAssassin (D.stageSituation B S hS n T U).f
          (D.stageSituation B S hS n T U).F, (D.stageSituation B S hS n T U).f x ∈ W →
        ∃ a ∈ O, chartSchemeToPoints B S hS _ U a = chartSchemeToPoints B S hS _ U x := by
  have hqcE : QuasiCompact (D.stageSituation B S hS n T U).f :=
    D.quasiCompact_stageSituation_f B S hS n T hTaff U hUaff
  have : IsAffine (D.stageSituation B S hS n T U).X := hUaff
  obtain ⟨K, hKc, hKo, hfibK, hKO'⟩ :=
    exists_isCompact_isOpen_fibre_subset (D.stageSituation B S hS n T U).f v hO hvO
  set ψ := chartSchemeToPoints B S hS _ U
  set W' : Set (points B S hS (baseChangeSpace D.f T).1) := ψ '' K
  have hW'open : IsOpen W' := isOpenMap_chartSchemeToPoints (baseChangeSpace D.f T) U K hKo
  have hC1 := D.pointsToScheme_pointsMap_chartSchemeToPoints n T U
  -- finite presentation of `X_T ⟶ T`, by Stacks 03XR
  have hfp : IsFinitePresentation B S hS (baseChangeInclusion D.f T).hom :=
    have := isFinitePresentation_isStableUnderBaseChange B S hS
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := fun ⦃_F _G : AlgebraicSpaces B S hS⦄ (g : _F ⟶ _G) =>
        IsFinitePresentation B S hS g.hom)
      (AlgebraicSpaces.isPullback_fiberProduct B S hS D.f T.hom) hf
  have hqc := D.isQuasicoherentOnSite_baseChangeModule B S hS T
  have hFT := D.isFinitePresentationOnSite_baseChangeModule B S hS hF T
  -- the image of `K` is quasi-compact over `T`
  have hUqc : ∀ A : ((BigFppfOver.toScheme B S hS).obj T.left).Opens,
      IsCompact (A : Set ((BigFppfOver.toScheme B S hS).obj T.left)) →
      IsCompact (W' ∩ (fun x => schemeSpacePointToScheme B S hS T.left
        (pointsMap B S hS _ (baseChangeInclusion D.f T).hom x)) ⁻¹'
          (A : Set ((BigFppfOver.toScheme B S hS).obj T.left))) := by
    intro A hA
    have hmem : ∀ k, schemeSpacePointToScheme B S hS T.left
        (pointsMap B S hS _ (baseChangeInclusion D.f T).hom (ψ k)) ∈
          (A : Set ((BigFppfOver.toScheme B S hS).obj T.left)) ↔
        (D.stageSituation B S hS n T U).f k ∈
          (A : Set ((BigFppfOver.toScheme B S hS).obj T.left)) :=
      fun k ↦ Iff.of_eq (congrArg (· ∈ (A : Set _)) (hC1 k))
    have heq : W' ∩ (fun x => schemeSpacePointToScheme B S hS T.left
        (pointsMap B S hS _ (baseChangeInclusion D.f T).hom x)) ⁻¹'
          (A : Set ((BigFppfOver.toScheme B S hS).obj T.left)) =
        ψ '' (K ∩ (D.stageSituation B S hS n T U).f ⁻¹'
          (show Set (D.stageSituation B S hS n T U).S from
            (A : Set ((BigFppfOver.toScheme B S hS).obj T.left)))) := by
      ext y
      constructor
      · rintro ⟨⟨k, hk, rfl⟩, hkA⟩
        exact ⟨k, ⟨hk, (hmem k).1 hkA⟩, rfl⟩
      · rintro ⟨k, ⟨hk, hkA⟩, rfl⟩
        exact ⟨⟨k, hk, rfl⟩, (hmem k).2 hkA⟩
    rw [heq]
    refine IsCompact.image ?_ (continuous_chartSchemeToPoints B S hS U)
    exact isCompact_inter_preimage (D.stageSituation B S hS n T U).f hKo hKc A.2 hA
  have hloc := isLocallyConstructible_relativeAssassinContainmentLocus_of_isFinitePresentation
    B S hS T.left (baseChangeInclusion D.f T) hfp (D.toFlatnessSituation.baseChangeModule T) hqc
    hFT W' hW'open hUqc
  -- the locus contains every generalization of `v`, by purity
  have hspec : {t : (BigFppfOver.toScheme B S hS).obj T.left | t ⤳ v} ⊆
      relativeAssassinContainmentLocus B S hS T.left (baseChangeInclusion D.f T)
        (D.toFlatnessSituation.baseChangeModule T) W' := by
    intro t ht ξ hξ hξt
    obtain ⟨θ, hθ, hθv⟩ := D.exists_specializes_of_isPureAbove hf hpure T hqf ht hξ hξt
    obtain ⟨z, rfl⟩ := surjective_chartSchemeToPoints_of_isSurjective U hU θ
    exact hθ.mem_open hW'open ⟨z, hfibK ((hC1 z).symm.trans hθv), rfl⟩
  obtain ⟨W, hWsub, hWo, hvW⟩ :=
    mem_nhds_iff.1 (mem_nhds_of_isLocallyConstructible_of_specializes_subset hloc hspec)
  refine ⟨W, hWo, hvW, fun x hx hxW ↦ ?_⟩
  have hξ : IsRelativeWeaklyAssociatedPoint B S hS (baseChangeInclusion D.f T)
      (D.toFlatnessSituation.baseChangeModule T) (ψ x) :=
    isRelativeWeaklyAssociatedPoint_of_mem_relativeAssassin_chartDiagram B S hS
      (baseChangeInclusion D.f T) (D.toFlatnessSituation.baseChangeModule T) hqc
      (identityTargetChartDiagram B S hS (baseChangeInclusion D.f T) U) x hx
  obtain ⟨a, haK, ha⟩ := hWsub hxW (ψ x) hξ (hC1 x)
  exact ⟨a, hKO' haK, ha⟩

end FlatDimensionSituation

end AlgebraicGeometry.Space

end
