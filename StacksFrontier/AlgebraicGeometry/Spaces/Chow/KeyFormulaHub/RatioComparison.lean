module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaHub.ChartMeromorphicEtaleFraction
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaHub.GenericStalkEtaleLocalRing
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorCanonicalRatio
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorGenericStalkGeneratingChart
public import StacksFrontier.AlgebraicGeometry.Spaces.PicardTensorRatio
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleSitePoint

/-!
# The two ratios of a meromorphic section, compared in the étale local ring

Let `X` be a decent, locally Noetherian, integral algebraic space, let `ℒ` be an invertible
`𝒪_X`-module, let `Z ⊂ X` be a prime divisor with generic point `ξ` and let `x̄` be a geometric
point of `X` over `ξ`. A meromorphic section `s` of `ℒ` has two ratios:

* `s / s_ξ`, the ratio against the generator chosen at `ξ`
  (`AlgebraicGeometry.Space.PrimeDivisor.canonicalGenericRatio`), in `Q(𝒪^h_{X, ξ})`, and
* `s / e`, the ratio against a free generator `e` of `ℒ` over an affine étale chart `V`
  (`AlgebraicGeometry.Space.chartRatio`), in `𝒦_X(V)`.

Read in `Q(𝒪_{X, x̄})` through any small étale neighbourhood `(V, v)` of `x̄`, the two differ by a
unit `λ` of `𝒪_{X, x̄}` which does not depend on `s`: it is the ratio of the two generators.

## Main results

* `AlgebraicGeometry.Space.PrimeDivisor.exists_sieve_forall_genericStalkCoefficient_eq_mul`: over
  the charts of a covering sieve of the base change of `V` to `Spec(𝒪_{U, u})`, the coefficient
  `s / s_ξ` is a unit times the ratio `s / e`, the unit depending only on the chart.
* `AlgebraicGeometry.Space.PrimeDivisor.exists_unit_canonicalGenericRatio_eq`: the comparison
  in `Q(𝒪_{X, x̄})`.

## References

* [Stacks Project, Tag 0EPR](https://stacks.math.columbia.edu/tag/0EPR)
* [Stacks Project, Tag 0EQU](https://stacks.math.columbia.edu/tag/0EQU)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TensorProduct
open scoped nonZeroDivisors

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] chartMeromorphicAlgebra chartMeromorphicFunctionAlgebra
attribute [local instance] meromorphicSectionModuleRingedSiteModule
attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) (Z : PrimeDivisor B S hS X)

/-! ### The comparison of the two generators over a covering sieve, uniformly in the section -/

include hX in
/-- **The two readings of every meromorphic section agree up to one unit over a common chart.**
Let `ℒ` be free on `e` over an étale chart `V` of `X`. Over the charts of a covering sieve of the
base change of `V` to `Spec(𝒪_{U, u})` there is a unit of the regular functions — the ratio of the
inverse image of `e` to the generator chosen at `ξ` — such that for *every* meromorphic section
`t` of `ℒ` the restriction of the coefficient `t / s_ξ` is that unit times the pullback of the
ratio `t / e`.

This is
`AlgebraicGeometry.Space.PrimeDivisor.exists_sieve_genericStalkCoefficient_eq_mul_chartRatio`
with the sieve and the unit chosen before the section: neither depends on it. -/
theorem PrimeDivisor.exists_sieve_forall_genericStalkCoefficient_eq_mul
    (L : Modules.{u, u} B S hS X hX) (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L)
    (V : SmallEtale B S hS X)
    (e : (W : SmallEtale B S hS X) → (W ⟶ V) → L.val.obj (op W))
    (hecompat : ∀ (W W' : SmallEtale B S hS X) (k : W ⟶ V) (g : W' ⟶ W),
      (L.val.map g.op).hom (e W k) = e W' (g ≫ k))
    (hebij : ∀ (W : SmallEtale B S hS X) (k : W ⟶ V),
      Function.Bijective fun r : chartRing B S hS X hX W ↦ r • e W k) :
    ∃ T : Sieve (Z.genericStalkBaseChangeChart B S hS hX hdec V),
      T ∈ SmallEtale.topology B S hS (Z.genericStalkSpace B S hS hX hdec).1
          (Z.genericStalkBaseChangeChart B S hS hX hdec V) ∧
        ∀ ⦃Q : SmallEtale B S hS (Z.genericStalkSpace B S hS hX hdec).1⦄
          (ι : Q ⟶ Z.genericStalkBaseChangeChart B S hS hX hdec V), T ι →
            ∃ v : (chartRing B S hS (Z.genericStalkSpace B S hS hX hdec).1
              (Z.genericStalkSpace B S hS hX hdec).2 Q)ˣ,
              ∀ t : MeromorphicSection.{u, u} B S hS X hX L,
                ((Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS
                    (Z.genericStalkSpace B S hS hX hdec).1
                    (Z.genericStalkSpace B S hS hX hdec).2).O).obj.map
                  (ι ≫ chartToIdEtaleChart B S hS
                    (Z.genericStalkBaseChangeChart B S hS hX hdec V)).op).hom
                  (Z.genericStalkCoefficient B S hS hX hdec L hL t) =
                algebraMap (chartRing B S hS (Z.genericStalkSpace B S hS hX hdec).1
                    (Z.genericStalkSpace B S hS hX hdec).2 Q)
                  ((meromorphicChartSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
                    (Z.genericStalkSpace B S hS hX hdec).2).obj.obj (op Q))
                  (v : chartRing B S hS (Z.genericStalkSpace B S hS hX hdec).1
                    (Z.genericStalkSpace B S hS hX hdec).2 Q) *
                  Z.baseChangeChartRatio B S hS hX hdec L t V e hecompat hebij ι := by
  set jm := Z.genericStalkMorphism B S hS hX hdec
  set hj := Z.pullbacksMeromorphicSections_genericStalkMorphism B S hS hX hdec
  set d := Z.genericStalkBaseChangeDiagram B S hS hX hdec V
  obtain ⟨T, hT, hTbij⟩ := exists_sieve_bijective_smul_modulePullbackChartSection B S hS jm L
    (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hL) d e hecompat hebij
  refine ⟨T, hT, fun Q ι hι ↦ ?_⟩
  have hgbij := Category.id_comp ι ▸ hTbij ι hι Q (𝟙 Q)
  obtain ⟨v, hv⟩ := Z.exists_isUnit_smul_genericStalkGenerator B S hS hX hdec L hL Q
    (ι ≫ chartToIdEtaleChart B S hS (Z.genericStalkBaseChangeChart B S hS hX hdec V))
    (modulePullbackChartSectionRestrict B S hS jm L d (e d.V (𝟙 d.V)) ι) hgbij
  refine ⟨v, fun t ↦ ?_⟩
  set c := chartRatio B S hS X hX L V e hecompat hebij t
  have hpres := eval_eq_toMeromorphicSectionSheaf_tmul_chartRatio B S hS X hX L V e hecompat
    hebij t
  -- the presentation over the base-changed chart itself
  have hEid : modulePullbackChartSectionRestrict B S hS jm L d (e d.V (𝟙 d.V)) (𝟙 d.U) =
      (modulePullbackChartFMap B S hS jm L).app d (e d.V (𝟙 d.V)) :=
    CategoryTheory.congr_fun
      (((modulePullback B S hS jm).obj L).val.presheaf.map_id (op d.U))
      ((modulePullbackChartFMap B S hS jm L).app d (e d.V (𝟙 d.V)))
  have hvalue : (pullbackMeromorphicSection B S hS jm L hj t).eval (op d.U) =
      toMeromorphicSectionSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
        (Z.genericStalkSpace B S hS hX hdec).2 ((modulePullback B S hS jm).obj L) d.U
        ((chartMeromorphicPullbackHom B S hS jm hj d c) ⊗ₜ[chartRing B S hS
            (Z.genericStalkSpace B S hS hX hdec).1
            (Z.genericStalkSpace B S hS hX hdec).2 d.U]
          modulePullbackChartSectionRestrict B S hS jm L d (e d.V (𝟙 d.V)) (𝟙 d.U) :
          (meromorphicSectionModule B S hS (Z.genericStalkSpace B S hS hX hdec).1
            (Z.genericStalkSpace B S hS hX hdec).2
            ((modulePullback B S hS jm).obj L)).obj (op d.U)) := by
    rw [hEid]
    refine (pullbackMeromorphicSection_eval_chartDiagram B S hS jm L hj t d
      (c ⊗ₜ[chartRing B S hS X hX d.V] e d.V (𝟙 d.V) :
        (meromorphicSectionModule B S hS X hX L).obj (op d.V)) hpres).trans
      (congrArg (toMeromorphicSectionSheaf B S hS
        (Z.genericStalkSpace B S hS hX hdec).1 (Z.genericStalkSpace B S hS hX hdec).2
        ((modulePullback B S hS jm).obj L) d.U)
        (chartPullbackMeromorphicSectionsSheaf_tmul B S hS jm L hj d c (e d.V (𝟙 d.V))))
  have hEcompat : ∀ (W₁ W₂ : SmallEtale B S hS (Z.genericStalkSpace B S hS hX hdec).1)
      (k₁ : W₁ ⟶ d.U) (g : W₂ ⟶ W₁),
      (((modulePullback B S hS jm).obj L).val.map g.op).hom
          (modulePullbackChartSectionRestrict B S hS jm L d (e d.V (𝟙 d.V)) k₁) =
        modulePullbackChartSectionRestrict B S hS jm L d (e d.V (𝟙 d.V)) (g ≫ k₁) :=
    fun _ _ k₁ g ↦ modulePullbackChartSectionRestrict_map B S hS jm L d (e d.V (𝟙 d.V)) k₁ g
  have hXrestrict := eval_eq_toMeromorphicSectionSheaf_tmul_restrict B S hS
    (Z.genericStalkSpace B S hS hX hdec).1 (Z.genericStalkSpace B S hS hX hdec).2
    ((modulePullback B S hS jm).obj L) (pullbackMeromorphicSection B S hS jm L hj t) d.U
    (fun W₁ k₁ ↦ modulePullbackChartSectionRestrict B S hS jm L d (e d.V (𝟙 d.V)) k₁)
    hEcompat (chartMeromorphicPullbackHom B S hS jm hj d c) hvalue
  refine Z.genericStalkCoefficient_eq_of_eval_eq B S hS hX hdec L hL t Q
    (ι ≫ chartToIdEtaleChart B S hS (Z.genericStalkBaseChangeChart B S hS hX hdec V)) _
    ((hXrestrict Q ι).trans ?_)
  refine congrArg (toMeromorphicSectionSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
    (Z.genericStalkSpace B S hS hX hdec).2 ((modulePullback B S hS jm).obj L) Q) ?_
  rw [hv]
  exact meromorphicSectionModule_tmul_smul B S hS (Z.genericStalkSpace B S hS hX hdec).1
    (Z.genericStalkSpace B S hS hX hdec).2 _ Q (v : _) _ _

/-! ### Lifting a geometric point through a covering sieve -/

/-- **A lift of a geometric point into an étale chart lifts further through a covering sieve of
that chart, to a member with affine scheme.** The sieve contains a chosen covering family, through
a member of which the lift factors by joint surjectivity of the fibre functor, and the affine
charts of that member cover it. -/
theorem exists_affine_mem_lift_of_mem_topology {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (x : GeometricPoint B S hS F) {W : SmallEtale B S hS F} {T : Sieve W}
    (hT : T ∈ SmallEtale.topology B S hS F W) (p : x.val.siteObject ⟶ W.obj.left)
    (hp : W.obj.hom.app (op x.val.siteObject) p = x.val.value) :
    ∃ (Q : SmallEtale B S hS F) (ι : Q ⟶ W) (_ : T ι) (_ : IsAffine (chartScheme Q))
      (q : x.val.siteObject ⟶ Q.obj.left)
      (_ : Q.obj.hom.app (op x.val.siteObject) q = x.val.value),
      q ≫ (SmallEtale.toOver B S hS F).map ι = p := by
  obtain ⟨R, hR, hRT⟩ := (SmallEtale.mem_topology_iff B S hS F).1 hT
  obtain ⟨V₁, f₁, hf₁, q₁, hq₁⟩ := geometricFiber_jointly_surjective B S hS F x R hR ⟨p, hp⟩
  obtain ⟨J, Y, a, haff, hcov, -⟩ := SmallEtale.exists_affine_etale_ofArrows B S hS F V₁
  obtain ⟨R₂, hR₂, hR₂T⟩ := (SmallEtale.mem_topology_iff B S hS F).1 hcov
  obtain ⟨V₂, f₂, hf₂, q₂, hq₂⟩ := geometricFiber_jointly_surjective B S hS F x R₂ hR₂ q₁
  obtain ⟨j, c, rfl⟩ := (Sieve.mem_ofArrows_iff Y a f₂).1 (hR₂T _ f₂ hf₂)
  refine ⟨Y j, a j ≫ f₁, T.downward_closed (hRT _ f₁ hf₁) _, haff j,
    q₂.1 ≫ (SmallEtale.toOver B S hS F).map c, ((geometricFiber B S hS F x).map c q₂).2, ?_⟩
  have h₁ := congrArg Subtype.val hq₁
  have h₂ := congrArg Subtype.val hq₂
  change q₁.1 ≫ (SmallEtale.toOver B S hS F).map f₁ = p at h₁
  change q₂.1 ≫ (SmallEtale.toOver B S hS F).map (c ≫ a j) = q₁.1 at h₂
  rw [← h₁, ← h₂, Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]

/-! ### A lift of a geometric point of `Spec(A)` into the base change of a chart -/

/-- **A geometric point of `Spec(𝒪_{U, u})` together with a lift of its image to an étale chart
`V` of `X` lifts to the base change of `V` to `Spec(𝒪_{U, u})`**, compatibly with both: the base
change is a fibre product of presheaves. -/
theorem PrimeDivisor.exists_lift_genericStalkBaseChangeChart
    (ybar : GeometricPoint B S hS (Z.genericStalkSpace B S hS hX hdec).1)
    (V : SmallEtale B S hS X) (pV : ybar.val.siteObject ⟶ V.obj.left)
    (hpV : V.obj.hom.app (op ybar.val.siteObject) pV =
      (Z.genericStalkMorphism B S hS hX hdec).hom.app (op ybar.val.siteObject) ybar.val.value) :
    ∃ ℓ : ybar.val.siteObject ⟶ (Z.genericStalkBaseChangeChart B S hS hX hdec V).obj.left,
      (Z.genericStalkBaseChangeChart B S hS hX hdec V).obj.hom.app (op ybar.val.siteObject) ℓ =
          ybar.val.value ∧
        ℓ ≫ (Z.genericStalkBaseChangeDiagram B S hS hX hdec V).g = pV := by
  have hpb := (Z.representable_genericStalkMorphism B S hS hX hdec).isPullback V.obj.hom
  have w : yonedaEquiv.symm ybar.val.value ≫ (Z.genericStalkMorphism B S hS hX hdec).hom =
      yoneda.map pV ≫ V.obj.hom := by
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp, Equiv.apply_symm_apply, yonedaEquiv_comp, yonedaEquiv_yoneda_map]
    exact hpV.symm
  refine ⟨yoneda.preimage (hpb.lift _ _ w), ?_, ?_⟩
  · have h' := congrArg yonedaEquiv (hpb.lift_fst _ _ w)
    rwa [← Functor.map_preimage yoneda (hpb.lift _ _ w), yonedaEquiv_comp,
      yonedaEquiv_yoneda_map, Equiv.apply_symm_apply] at h'
  · refine yoneda.map_injective ?_
    exact (yoneda.map_comp _ _).trans
      ((congrArg (· ≫ _) (Functor.map_preimage yoneda (hpb.lift _ _ w))).trans
        (hpb.lift_snd _ _ w))

/-! ### The comparison in the étale local ring -/

section Comparison

variable (hInt : IsIntegralSpace B S hS X)
  (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} ↦ IsLocallyNoetherian Y))

include hInt in
/-- On an integral algebraic space every weakly associated point has codimension zero, the space
being reduced: hypothesis (a) of Stacks 0EN6. -/
theorem localRingDimension_eq_zero_of_mem_weaklyAssociatedPointsOfSpace_of_isIntegralSpace :
    ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS ⟨X, hX⟩, localRingDimension B S hS z = 0 :=
  fun _ hz ↦ by
    rwa [weaklyAssociatedPointsOfSpace_eq_setOf_localRingDimension_eq_zero B S hS _
      hInt.hasEtaleLocalProperty_isReduced] at hz

variable (L : Modules.{u, u} B S hS X hX) (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L)

include hInt hN in
/-- **The comparison of the two ratios at a geometric point coming from `Spec(A)`.** This is
`AlgebraicGeometry.Space.PrimeDivisor.exists_unit_canonicalGenericRatio_eq` for a geometric point
of `X` of the form `j(ȳ)`, with `ȳ` lifting to `U` through the residue field of `u`. -/
theorem PrimeDivisor.exists_unit_canonicalGenericRatio_eq_of_genericStalk
    (ybar : GeometricPoint B S hS (Z.genericStalkSpace B S hS hX hdec).1)
    (hy : (geometricPointMap (Z.genericStalkMorphism B S hS hX hdec).hom ybar).LiesOver
      (Z.genericPoint B S hS X))
    (hlift : ybar.val.value ≫ Z.genericStalkSpecToChart B S hS hX hdec =
      (Z.genericChart B S hS hX hdec).liftGeometricPoint _ hy)
    (N : SmallEtaleNeighborhood (geometricPointMap (Z.genericStalkMorphism B S hS hX hdec).hom
        ybar))
    (hV : IsAffine (chartScheme N.chart))
    (e : (W : SmallEtale B S hS X) → (W ⟶ N.chart) → L.val.obj (op W))
    (hecompat : ∀ (W W' : SmallEtale B S hS X) (k : W ⟶ N.chart) (g : W' ⟶ W),
      (L.val.map g.op).hom (e W k) = e W' (g ≫ k))
    (hebij : ∀ (W : SmallEtale B S hS X) (k : W ⟶ N.chart),
      Function.Bijective fun r : chartRing B S hS X hX W ↦ r • e W k) :
    ∃ μ : (etaleLocalRing B S hS X
        (geometricPointMap (Z.genericStalkMorphism B S hS hX hdec).hom ybar) : Type (u + 1))ˣ,
      ∀ t : MeromorphicSection.{u, u} B S hS X hX L,
        Z.genericTotalFractionRingToEtaleFractionRing B S hS X hX hdec
            (Z.henselianToEtaleLocalRing B S hS hX hdec hy)
            (fun _ hr ↦ Z.henselianToEtaleLocalRing_mem_nonZeroDivisors B S hS hX hdec hy hr)
            (Z.canonicalGenericRatio B S hS hX hdec L hL hInt hN t) =
          affineChartMeromorphicToEtaleFractionRing B S hS ⟨X, hX⟩
              (localRingDimension_eq_zero_of_mem_weaklyAssociatedPointsOfSpace_of_isIntegralSpace
                B S hS hX hInt)
              (hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian B S hS X hX hN) N hV
              (chartRatio B S hS X hX L N.chart e hecompat hebij t) *
            algebraMap _ _ (μ : (etaleLocalRing B S hS X
              (geometricPointMap (Z.genericStalkMorphism B S hS hX hdec).hom ybar) : Type (u + 1)))
                  := by
  -- the isomorphism of étale local rings along `j`
  set ρe := RingEquiv.ofBijective _
    (Z.bijective_etaleLocalRingMap_genericStalkMorphism B S hS hX hdec ybar hy hlift)
  -- the hypotheses of Stacks 0EN6 on `Spec(A)`
  have hwaY := Z.localRingDimension_eq_zero_of_mem_weaklyAssociated_genericStalkSpace B S hS hX
    hdec hInt
  have hfinY := Z.hasLocallyFiniteIrreducibleComponents_genericStalkSpace B S hS hX hdec hN
  -- the comparison chart
  obtain ⟨pP, hpP, hpPg⟩ := Z.exists_lift_genericStalkBaseChangeChart B S hS hX hdec ybar
    N.chart N.point N.point_comp
  obtain ⟨T, hT, hTv⟩ := Z.exists_sieve_forall_genericStalkCoefficient_eq_mul B S hS hX hdec L hL
    N.chart e hecompat hebij
  obtain ⟨Q, ι, hι, hQ, q, hq, hqι⟩ := exists_affine_mem_lift_of_mem_topology B S hS ybar hT pP hpP
  obtain ⟨v, hv⟩ := hTv ι hι
  let NQ : SmallEtaleNeighborhood ybar := ⟨Q, q, hq⟩
  have hqA : q ≫ (SmallEtale.toOver B S hS (Z.genericStalkSpace B S hS hX hdec).1).map
      (ι ≫ chartToIdEtaleChart B S hS (Z.genericStalkBaseChangeChart B S hS hX hdec N.chart)) =
      ybar.val.value := by
    refine (congrArg (q ≫ ·) (Functor.map_comp _ _ _)).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ _) hqι).trans ?_
    exact (congrArg (fun α ↦ α.app (op ybar.val.siteObject) pP)
      (Functor.map_preimage yoneda
        (Z.genericStalkBaseChangeChart B S hS hX hdec N.chart).obj.hom)).trans hpP
  let mA : NQ ⟶ Z.genericStalkNeighborhood B S hS hX hdec ybar :=
    ⟨ι ≫ chartToIdEtaleChart B S hS (Z.genericStalkBaseChangeChart B S hS hX hdec N.chart), hqA⟩
  -- the map `𝒪_Y(Q) → 𝒪_{X, x̄}`
  let κ := ρe.symm.toRingHom.comp (etaleLocalRingGerm B S hS (Z.genericStalkSpace B S hS hX hdec).1
      ybar (op NQ))
  -- on regular functions of `Spec(A)` it is the map of Stacks 0EMZ
  have hκA : ∀ a : (structurePresheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1).obj (op
      (Z.genericStalkChart B S hS hX hdec)),
      κ (((structurePresheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1).map
          (ι ≫ chartToIdEtaleChart B S hS (Z.genericStalkBaseChangeChart B S hS hX hdec
              N.chart)).op).hom a) =
        Z.henselianToEtaleLocalRing B S hS hX hdec hy
          (Z.genericStalkSectionsToHenselian B S hS hX hdec a) := by
    intro a
    have h1 : etaleLocalRingGerm B S hS (Z.genericStalkSpace B S hS hX hdec).1 ybar (op NQ)
        (((structurePresheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1).map
          (ι ≫ chartToIdEtaleChart B S hS (Z.genericStalkBaseChangeChart B S hS hX hdec
              N.chart)).op).hom a) =
        etaleLocalRingGerm B S hS (Z.genericStalkSpace B S hS hX hdec).1 ybar (op
            (Z.genericStalkNeighborhood B S hS hX hdec ybar)) a :=
      RingHom.congr_fun (etaleLocalRingGerm_comp_map B S hS mA) a
    change ρe.symm (etaleLocalRingGerm B S hS (Z.genericStalkSpace B S hS hX hdec).1 ybar (op NQ)
        _) = _
    rw [h1, ← Z.etaleLocalRingMap_genericStalkToEtaleLocalRing_ΓSpecIso B S hS hX hdec ybar hy
        hlift a]
    change ρe.symm (ρe _) = _
    rw [RingEquiv.symm_apply_apply]
    exact (Z.henselianToEtaleLocalRing_stalkToHenselianLocalRing B S hS hX hdec hy _).symm
  -- on regular functions of `V` it is the germ at `x̄`
  have hcommQ : Q.obj.hom ≫ (Z.genericStalkMorphism B S hS hX hdec).hom =
      yoneda.map ((SmallEtale.toOver B S hS (Z.genericStalkSpace B S hS hX hdec).1).map ι ≫
        (Z.genericStalkBaseChangeDiagram B S hS hX hdec N.chart).g) ≫ N.chart.obj.hom := by
    refine ((congrArg (· ≫ (Z.genericStalkMorphism B S hS hX hdec).hom)
      (CostructuredArrow.w ι.hom).symm).trans (Category.assoc _ _ _)).trans ?_
    refine (congrArg (yoneda.map ι.hom.left ≫ ·)
      (Z.genericStalkBaseChangeDiagram B S hS hX hdec N.chart).comm).trans ?_
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ N.chart.obj.hom)
      (yoneda.map_comp _ _).symm)
  have hpointQ : NQ.point ≫ ((SmallEtale.toOver B S hS (Z.genericStalkSpace B S hS hX hdec).1).map
      ι ≫
      (Z.genericStalkBaseChangeDiagram B S hS hX hdec N.chart).g) = N.point :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hqι).trans hpPg)
  have hκV : ∀ b : (structurePresheaf B S hS X).obj (op N.chart),
      κ ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
          ((SmallEtale.toOver B S hS (Z.genericStalkSpace B S hS hX hdec).1).map ι ≫
            (Z.genericStalkBaseChangeDiagram B S hS hX hdec N.chart).g)).op).hom b) =
        etaleLocalRingGerm B S hS X _ (op N) b := by
    intro b
    exact (congrArg ρe.symm (RingHom.congr_fun (etaleLocalRingMap_isEtaleLocalRingMap
      (Z.genericStalkSpace B S hS hX hdec).2 (Z.genericStalkMorphism B S hS hX hdec).hom ybar NQ N
      _ hcommQ hpointQ) b)).trans (RingEquiv.symm_apply_apply ρe _)
  -- the reading of the meromorphic functions on `Q` in `Q(𝒪_{X, x̄})`
  have hκ0 : ∀ y ∈ ((structurePresheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1).obj (op Q))⁰,
      κ y ∈ nonZeroDivisors (etaleLocalRing B S hS X (geometricPointMap (Z.genericStalkMorphism B S
      hS hX hdec).hom ybar) : Type (u + 1)) := by
    intro y hy'
    rw [← MulEquivClass.map_nonZeroDivisors ρe.symm]
    exact Submonoid.mem_map_of_mem _
      (etaleLocalRingGerm_mem_nonZeroDivisors B S hS (Z.genericStalkSpace B S hS hX hdec) NQ
        hQ hy')
  have := isFractionRing_meromorphicFunctionSheaf_obj B S hS (Z.genericStalkSpace B S hS hX hdec)
      hwaY hfinY Q hQ
  let ΘQ : (meromorphicFunctionSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
      (Z.genericStalkSpace B S hS hX hdec).2).obj.obj (op Q) →+* FractionRing (etaleLocalRing B S
      hS X (geometricPointMap (Z.genericStalkMorphism B S hS hX hdec).hom ybar) : Type (u + 1)) :=
    IsLocalization.lift (M := ((structurePresheaf B S hS (Z.genericStalkSpace B S hS hX
        hdec).1).obj (op Q))⁰)
      (g := (algebraMap (etaleLocalRing B S hS X (geometricPointMap (Z.genericStalkMorphism B S hS
          hX hdec).hom ybar) : Type (u + 1)) (FractionRing (etaleLocalRing B S hS X
          (geometricPointMap (Z.genericStalkMorphism B S hS hX hdec).hom ybar) : Type (u +
          1)))).comp κ)
      fun y ↦ IsLocalization.map_units _ ⟨_, hκ0 _ y.2⟩
  have hΘQ : ∀ c, ΘQ (algebraMap ((structurePresheaf B S hS (Z.genericStalkSpace B S hS hX
      hdec).1).obj (op Q))
      ((meromorphicFunctionSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1 (Z.genericStalkSpace
          B S hS hX hdec).2).obj.obj (op Q)) c) =
        algebraMap (etaleLocalRing B S hS X (geometricPointMap (Z.genericStalkMorphism B S hS hX
            hdec).hom ybar) : Type (u + 1)) (FractionRing (etaleLocalRing B S hS X
            (geometricPointMap (Z.genericStalkMorphism B S hS hX hdec).hom ybar) : Type (u + 1)))
            (κ c) :=
    fun c ↦ IsLocalization.lift_eq _ _
  -- on the side of `Spec(A)`
  have := Z.isFractionRing_genericStalkMeromorphic B S hS hX hdec hInt hN
  have hAside : ΘQ.comp ((meromorphicFunctionSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
      (Z.genericStalkSpace B S hS hX hdec).2).obj.map
      (ι ≫ chartToIdEtaleChart B S hS (Z.genericStalkBaseChangeChart B S hS hX hdec
          N.chart)).op).hom =
      (Z.genericTotalFractionRingToEtaleFractionRing B S hS X hX hdec
          (Z.henselianToEtaleLocalRing B S hS hX hdec hy)
          (fun _ hr ↦ Z.henselianToEtaleLocalRing_mem_nonZeroDivisors B S hS hX hdec hy hr)).comp
        (Z.genericStalkMeromorphicToGeneric B S hS hX hdec hInt hN) := by
    refine IsLocalization.ringHom_ext
      ((structurePresheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1).obj (op
          (Z.genericStalkChart B S hS hX hdec)))⁰
      (RingHom.ext fun w ↦ ?_)
    have hnat := ConcreteCategory.congr_hom ((toMeromorphicFunctionSheaf B S hS
        (Z.genericStalkSpace B S hS hX hdec).1 (Z.genericStalkSpace B S hS hX
        hdec).2).hom.naturality
      (ι ≫ chartToIdEtaleChart B S hS (Z.genericStalkBaseChangeChart B S hS hX hdec N.chart)).op) w
    change ΘQ (((meromorphicFunctionSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
        (Z.genericStalkSpace B S hS hX hdec).2).obj.map
        (ι ≫ chartToIdEtaleChart B S hS (Z.genericStalkBaseChangeChart B S hS hX hdec
            N.chart)).op).hom
          (((toMeromorphicFunctionSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
              (Z.genericStalkSpace B S hS hX hdec).2).hom.app
            (op (Z.genericStalkChart B S hS hX hdec))).hom w)) =
      Z.genericTotalFractionRingToEtaleFractionRing B S hS X hX hdec
          (Z.henselianToEtaleLocalRing B S hS hX hdec hy)
          (fun _ hr ↦ Z.henselianToEtaleLocalRing_mem_nonZeroDivisors B S hS hX hdec hy hr)
        (Z.genericStalkMeromorphicToGeneric B S hS hX hdec hInt hN (algebraMap _ _ w))
    refine (congrArg ΘQ hnat.symm).trans ((hΘQ _).trans ?_)
    rw [Z.genericStalkMeromorphicToGeneric_algebraMap B S hS hX hdec hInt hN w,
      Z.genericTotalFractionRingToEtaleFractionRing_algebraMap]
    exact congrArg (algebraMap _ _) (hκA w)
  -- on the side of `V`
  have hwaX := localRingDimension_eq_zero_of_mem_weaklyAssociatedPointsOfSpace_of_isIntegralSpace
    B S hS hX hInt
  have hfinX := hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian B S hS X hX hN
  let := chartMeromorphicFunctionAlgebra B S hS ⟨X, hX⟩ N.chart
  have := isFractionRing_meromorphicFunctionSheaf_obj B S hS ⟨X, hX⟩ hwaX hfinX N.chart hV
  have hVside : (ΘQ.comp ((meromorphicFunctionSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
      (Z.genericStalkSpace B S hS hX hdec).2).obj.map ι.op).hom).comp
      (chartMeromorphicPullbackHom B S hS (Z.genericStalkMorphism B S hS hX hdec)
        (Z.pullbacksMeromorphicSections_genericStalkMorphism B S hS hX hdec)
        (Z.genericStalkBaseChangeDiagram B S hS hX hdec N.chart)) =
      affineChartMeromorphicToEtaleFractionRing B S hS ⟨X, hX⟩ hwaX hfinX N hV := by
    refine IsLocalization.ringHom_ext ((structurePresheaf B S hS X).obj (op N.chart))⁰
      (j := ((ΘQ.comp ((meromorphicFunctionSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
          (Z.genericStalkSpace B S hS hX hdec).2).obj.map ι.op).hom).comp
        (chartMeromorphicPullbackHom B S hS (Z.genericStalkMorphism B S hS hX hdec)
          (Z.pullbacksMeromorphicSections_genericStalkMorphism B S hS hX hdec)
          (Z.genericStalkBaseChangeDiagram B S hS hX hdec N.chart)) :
            (meromorphicFunctionSheaf B S hS X hX).obj.obj (op N.chart) →+* FractionRing
                (etaleLocalRing B S hS X (geometricPointMap (Z.genericStalkMorphism B S hS hX
                hdec).hom ybar) : Type (u + 1))))
      (RingHom.ext fun b ↦ ?_)
    have hpb := RingHom.congr_fun (chartMeromorphicFunctionPullback_algebraMap B S hS
      (Z.genericStalkMorphism B S hS hX hdec)
      (Z.pullbacksMeromorphicSections_genericStalkMorphism B S hS hX hdec)
      (Z.genericStalkBaseChangeDiagram B S hS hX hdec N.chart)) b
    have hnat := ConcreteCategory.congr_hom
      ((toMeromorphicFunctionSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
          (Z.genericStalkSpace B S hS hX hdec).2).hom.naturality ι.op)
      (chartDiagramRestrict B S hS (Z.genericStalkMorphism B S hS hX hdec)
        (Z.genericStalkBaseChangeDiagram B S hS hX hdec N.chart) b)
    change ΘQ (((meromorphicFunctionSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
        (Z.genericStalkSpace B S hS hX hdec).2).obj.map ι.op).hom
        (chartMeromorphicPullbackHom B S hS (Z.genericStalkMorphism B S hS hX hdec)
          (Z.pullbacksMeromorphicSections_genericStalkMorphism B S hS hX hdec)
          (Z.genericStalkBaseChangeDiagram B S hS hX hdec N.chart)
          (((toMeromorphicFunctionSheaf B S hS X hX).hom.app (op N.chart)).hom b))) =
      affineChartMeromorphicToEtaleFractionRing B S hS ⟨X, hX⟩ hwaX hfinX N hV (algebraMap _ _ b)
    refine (congrArg (fun z ↦ ΘQ (((meromorphicFunctionSheaf B S hS (Z.genericStalkSpace B S hS hX
        hdec).1 (Z.genericStalkSpace B S hS hX hdec).2).obj.map
      ι.op).hom z)) hpb).trans ?_
    refine (congrArg ΘQ hnat.symm).trans ((hΘQ _).trans ?_)
    refine Eq.trans ?_
      (affineChartMeromorphicToEtaleFractionRing_algebraMap B S hS ⟨X, hX⟩ hwaX hfinX N hV b).symm
    refine congrArg (algebraMap _ _) (Eq.trans ?_ (hκV b))
    refine congrArg κ ?_
    have hΓ : Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
        ((SmallEtale.toOver B S hS (Z.genericStalkSpace B S hS hX hdec).1).map ι ≫
          (Z.genericStalkBaseChangeDiagram B S hS hX hdec N.chart).g)).op =
        Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
          (Z.genericStalkBaseChangeDiagram B S hS hX hdec N.chart).g).op ≫
        Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
          ((SmallEtale.toOver B S hS (Z.genericStalkSpace B S hS hX hdec).1).map ι)).op :=
      (congrArg (fun f ↦ Scheme.Γ.map (Opposite.op f))
        ((BigFppfOver.toScheme B S hS).map_comp _ _)).trans (Scheme.Γ.map_comp _ _)
    exact (ConcreteCategory.congr_hom hΓ b).symm
  refine ⟨Units.map κ.toMonoidHom v, fun t ↦ ?_⟩
  have h1 := RingHom.congr_fun hAside (Z.genericStalkCoefficient B S hS hX hdec L hL t)
  have h3 := RingHom.congr_fun hVside (chartRatio B S hS X hX L N.chart e hecompat hebij t)
  refine h1.symm.trans ((congrArg ΘQ (hv t)).trans ((map_mul ΘQ _ _).trans ?_))
  exact (congrArg₂ (· * ·) (hΘQ _) h3).trans (mul_comm _ _)

include hInt hN in
/-- **The two ratios of a meromorphic section differ by one unit of the étale local ring.** Let
`X` be a decent, locally Noetherian, integral algebraic space, `ℒ` an invertible `𝒪_X`-module,
`Z ⊂ X` a prime divisor with generic point `ξ`, `x̄` a geometric point of `X` over `ξ` and
`(V, v)` a small étale neighbourhood of `x̄` with affine scheme over which `ℒ` is free on `e`.
Then there is a unit `μ` of `𝒪_{X, x̄}` such that for every meromorphic section `s` of `ℒ`, the
image in `Q(𝒪_{X, x̄})` of the ratio `s / s_ξ` against the generator chosen at `ξ`
(`AlgebraicGeometry.Space.PrimeDivisor.canonicalGenericRatio`, read through the map of
Stacks 0EMZ) is the image of the ratio `s / e` (`AlgebraicGeometry.Space.chartRatio`, read through
the germ at `x̄`) times `μ`.

The unit is the ratio of the two generators, so it does not depend on `s`. It is computed over a
chart of `Spec(𝒪_{U, u})` lying over both `V` and `Spec(𝒪_{U, u})`, and carried to `𝒪_{X, x̄}`
through the étale local ring of `Spec(𝒪_{U, u})` at the geometric point over `x̄`, which the map of
étale local rings along `Spec(𝒪_{U, u}) ⟶ X` identifies with `𝒪_{X, x̄}`
(`AlgebraicGeometry.Space.PrimeDivisor.bijective_etaleLocalRingMap_genericStalkMorphism`). -/
theorem PrimeDivisor.exists_unit_canonicalGenericRatio_eq
    {xbar : GeometricPoint B S hS X} (hxbar : xbar.LiesOver (Z.genericPoint B S hS X))
    (N : SmallEtaleNeighborhood xbar) (hV : IsAffine (chartScheme N.chart))
    (e : (W : SmallEtale B S hS X) → (W ⟶ N.chart) → L.val.obj (op W))
    (hecompat : ∀ (W W' : SmallEtale B S hS X) (k : W ⟶ N.chart) (g : W' ⟶ W),
      (L.val.map g.op).hom (e W k) = e W' (g ≫ k))
    (hebij : ∀ (W : SmallEtale B S hS X) (k : W ⟶ N.chart),
      Function.Bijective fun r : chartRing B S hS X hX W ↦ r • e W k) :
    ∃ μ : (etaleLocalRing B S hS X xbar : Type (u + 1))ˣ,
      ∀ t : MeromorphicSection.{u, u} B S hS X hX L,
        Z.genericTotalFractionRingToEtaleFractionRing B S hS X hX hdec
            (Z.henselianToEtaleLocalRing B S hS hX hdec hxbar)
            (fun _ hr ↦ Z.henselianToEtaleLocalRing_mem_nonZeroDivisors B S hS hX hdec hxbar hr)
            (Z.canonicalGenericRatio B S hS hX hdec L hL hInt hN t) =
          affineChartMeromorphicToEtaleFractionRing B S hS ⟨X, hX⟩
              (localRingDimension_eq_zero_of_mem_weaklyAssociatedPointsOfSpace_of_isIntegralSpace
                B S hS hX hInt)
              (hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian B S hS X hX hN) N hV
              (chartRatio B S hS X hX L N.chart e hecompat hebij t) *
            algebraMap _ _ (μ : (etaleLocalRing B S hS X xbar : Type (u + 1))) := by
  have key : ∀ {x₁ x₂ : GeometricPoint B S hS X} (_ : x₁ = x₂)
      (h₁ : x₁.LiesOver (Z.genericPoint B S hS X)) (h₂ : x₂.LiesOver (Z.genericPoint B S hS X)),
      HEq ((Z.genericChart B S hS hX hdec).liftGeometricPoint x₁ h₁)
        ((Z.genericChart B S hS hX hdec).liftGeometricPoint x₂ h₂) := by
    rintro _ _ rfl _ _
    rfl
  obtain ⟨ybar, hyb, hlift⟩ : ∃ ybar : GeometricPoint B S hS (Z.genericStalkSpace B S hS hX hdec).1,
      geometricPointMap (Z.genericStalkMorphism B S hS hX hdec).hom ybar = xbar ∧
      ∀ h : (geometricPointMap (Z.genericStalkMorphism B S hS hX hdec).hom ybar).LiesOver
          (Z.genericPoint B S hS X),
        ybar.val.value ≫ Z.genericStalkSpecToChart B S hS hX hdec =
          (Z.genericChart B S hS hX hdec).liftGeometricPoint _ h := by
    refine ⟨Z.genericStalkGeometricPoint B S hS hX hdec hxbar,
      Z.geometricPointMap_genericStalkGeometricPoint B S hS hX hdec hxbar, fun h ↦ ?_⟩
    rw [Z.genericStalkGeometricPoint_value_comp B S hS hX hdec hxbar]
    exact eq_of_heq (key (Z.geometricPointMap_genericStalkGeometricPoint B S hS hX hdec
      hxbar).symm hxbar h)
  subst hyb
  exact Z.exists_unit_canonicalGenericRatio_eq_of_genericStalk B S hS hX hdec hInt hN L hL ybar
    hxbar (hlift hxbar) N hV e hecompat hebij

end Comparison

end AlgebraicGeometry.Space

end
