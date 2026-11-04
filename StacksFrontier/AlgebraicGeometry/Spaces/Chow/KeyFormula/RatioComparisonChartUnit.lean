module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaHub.RatioComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaLocal.Chart
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricEvaluationRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.PicardWeilDivisorClassIntegral

/-!
# The unit of the ratio comparison is the germ of a function on a chart of `Spec 𝒪_{U, u}`

Let `X` be a decent, locally Noetherian, integral algebraic space, `Z ⊂ X` a prime divisor with
generic point `ξ`, `ℒ` an invertible `𝒪_X`-module free on `e` over an étale chart `V`, and `x̄` a
geometric point of `X` over `ξ`.  The ratio comparison (H3,
`AlgebraicGeometry.Space.PrimeDivisor.exists_unit_canonicalGenericRatio_eq`) provides a unit `μ`
of `𝒪_{X, x̄}` with `s / s_ξ = (s / e) · μ` in `Q(𝒪_{X, x̄})` for every meromorphic section `s`.
This file makes `μ` explicit: over a chart `Q` of `Spec 𝒪_{U, u}` over the base change of `V`, on
which the inverse image of `e` is `v · s_ξ`, the relation holds with the image of `v` in
`𝒪_{X, x̄}`, and the unit is unique.

## Main results

* `AlgebraicGeometry.Space.PrimeDivisor.genericStalkCoefficient_restrict_eq_mul_of_eq_smul`: on
  `Q`, `t / s_ξ = v · (t / e)` for every meromorphic section `t`.
* `AlgebraicGeometry.Space.PrimeDivisor.canonicalGenericRatio_eq_mul_of_genericStalkChart`: the
  relation of H3 with the image of `v`.
* `AlgebraicGeometry.Space.PrimeDivisor.eq_of_canonicalGenericRatio_eq_mul`: uniqueness of the
  unit of H3.
* `AlgebraicGeometry.Space.PrimeDivisor.geometricEval_etaleLocalRingMap_symm_germ`: the value of
  the image of `v` at `x̄`.

## References

* [Stacks Project, Tag 0EPR](https://stacks.math.columbia.edu/tag/0EPR)
* [Stacks Project, Section 0EQU](https://stacks.math.columbia.edu/tag/0EQU)
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

/-! ### The coefficient comparison over one chart, from the comparison of the generators -/

/-- **The coefficient `t / s_ξ` over a chart `Q` of `Spec 𝒪_{U, u}` over the base change of `V`
is `v` times the ratio `t / e`**, for `v` with `e|_Q = v · s_ξ|_Q`. -/
theorem PrimeDivisor.genericStalkCoefficient_restrict_eq_mul_of_eq_smul
    (L : Modules.{u, u} B S hS X hX) (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L)
    (V : SmallEtale B S hS X)
    (e : (W : SmallEtale B S hS X) → (W ⟶ V) → L.val.obj (op W))
    (hecompat : ∀ (W W' : SmallEtale B S hS X) (k : W ⟶ V) (g : W' ⟶ W),
      (L.val.map g.op).hom (e W k) = e W' (g ≫ k))
    (hebij : ∀ (W : SmallEtale B S hS X) (k : W ⟶ V),
      Function.Bijective fun r : chartRing B S hS X hX W ↦ r • e W k)
    {Q : SmallEtale B S hS (Z.genericStalkSpace B S hS hX hdec).1}
    (ι : Q ⟶ Z.genericStalkBaseChangeChart B S hS hX hdec V)
    (v : chartRing B S hS (Z.genericStalkSpace B S hS hX hdec).1
      (Z.genericStalkSpace B S hS hX hdec).2 Q)
    (hv : modulePullbackChartSectionRestrict B S hS (Z.genericStalkMorphism B S hS hX hdec) L
        (Z.genericStalkBaseChangeDiagram B S hS hX hdec V) (e V (𝟙 V)) (𝟙 Q ≫ ι) =
      v • Z.genericStalkGenerator B S hS hX hdec L hL Q
        (ι ≫ chartToIdEtaleChart B S hS (Z.genericStalkBaseChangeChart B S hS hX hdec V)))
    (t : MeromorphicSection.{u, u} B S hS X hX L) :
    ((Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS
        (Z.genericStalkSpace B S hS hX hdec).1
        (Z.genericStalkSpace B S hS hX hdec).2).O).obj.map
      (ι ≫ chartToIdEtaleChart B S hS
        (Z.genericStalkBaseChangeChart B S hS hX hdec V)).op).hom
      (Z.genericStalkCoefficient B S hS hX hdec L hL t) =
    algebraMap (chartRing B S hS (Z.genericStalkSpace B S hS hX hdec).1
        (Z.genericStalkSpace B S hS hX hdec).2 Q)
      ((meromorphicChartSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
        (Z.genericStalkSpace B S hS hX hdec).2).obj.obj (op Q)) v *
      Z.baseChangeChartRatio B S hS hX hdec L t V e hecompat hebij ι := by
  have hv' : modulePullbackChartSectionRestrict B S hS (Z.genericStalkMorphism B S hS hX hdec) L
      (Z.genericStalkBaseChangeDiagram B S hS hX hdec V)
      (e (Z.genericStalkBaseChangeDiagram B S hS hX hdec V).V
        (𝟙 (Z.genericStalkBaseChangeDiagram B S hS hX hdec V).V)) (𝟙 Q ≫ ι) =
      v • Z.genericStalkGenerator B S hS hX hdec L hL Q
        (ι ≫ chartToIdEtaleChart B S hS (Z.genericStalkBaseChangeChart B S hS hX hdec V)) := hv
  clear hv
  set jm := Z.genericStalkMorphism B S hS hX hdec
  set hj := Z.pullbacksMeromorphicSections_genericStalkMorphism B S hS hX hdec
  set d := Z.genericStalkBaseChangeDiagram B S hS hX hdec V
  set g := modulePullbackChartSectionRestrict B S hS jm L d (e d.V (𝟙 d.V)) (𝟙 Q ≫ ι)
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
    refine Eq.trans (pullbackMeromorphicSection_eval_chartDiagram B S hS jm L hj t d
      (c ⊗ₜ[chartRing B S hS X hX d.V] e d.V (𝟙 d.V) :
        (meromorphicSectionModule B S hS X hX L).obj (op d.V)) hpres) ?_
    rw [chartPullbackMeromorphicSectionsSheaf_tmul B S hS jm L hj d c (e d.V (𝟙 d.V)), hEid]
    rfl
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
  have hpresQ : (pullbackMeromorphicSection B S hS jm L hj t).eval (op Q) =
      toMeromorphicSectionSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
        (Z.genericStalkSpace B S hS hX hdec).2 ((modulePullback B S hS jm).obj L) Q
        ((((Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS
              (Z.genericStalkSpace B S hS hX hdec).1
              (Z.genericStalkSpace B S hS hX hdec).2).O).obj.map ι.op).hom
            (chartMeromorphicPullbackHom B S hS jm hj d c)) ⊗ₜ[chartRing B S hS
          (Z.genericStalkSpace B S hS hX hdec).1
          (Z.genericStalkSpace B S hS hX hdec).2 Q] g :
          (meromorphicSectionModule B S hS (Z.genericStalkSpace B S hS hX hdec).1
            (Z.genericStalkSpace B S hS hX hdec).2
            ((modulePullback B S hS jm).obj L)).obj (op Q)) := by
    rw [hXrestrict Q ι]
    simp only [g]
    erw [Category.id_comp]
    rfl
  refine Z.genericStalkCoefficient_eq_of_eval_eq B S hS hX hdec L hL t Q
    (ι ≫ chartToIdEtaleChart B S hS (Z.genericStalkBaseChangeChart B S hS hX hdec V)) _
    (hpresQ.trans ?_)
  refine congrArg (toMeromorphicSectionSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
    (Z.genericStalkSpace B S hS hX hdec).2 ((modulePullback B S hS jm).obj L) Q) ?_
  rw [hv']
  exact meromorphicSectionModule_tmul_smul B S hS (Z.genericStalkSpace B S hS hX hdec).1
    (Z.genericStalkSpace B S hS hX hdec).2 _ Q v _ _


/-! ### The comparison in the étale local ring, with the unit of the chart -/

section Comparison

variable (hInt : IsIntegralSpace B S hS X)
  (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} ↦ IsLocallyNoetherian Y))
  (L : Modules.{u, u} B S hS X hX) (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L)

include hInt hN in
/-- **The unit of the ratio comparison (H3) at a geometric point coming from `Spec 𝒪_{U, u}`
is the germ of the unit of the chart.**  Let `Q` be an affine chart of `Spec 𝒪_{U, u}` over the
base change of `V`, through which the geometric point `ȳ` lifts compatibly with its lift to `V`,
and `v` a regular function on `Q` with `t / s_ξ = v · (t / e)` on `Q` for every meromorphic
section `t`.  Then the relation of
`AlgebraicGeometry.Space.PrimeDivisor.exists_unit_canonicalGenericRatio_eq_of_genericStalk` holds
with the image of `v` in `𝒪_{X, x̄}`. -/
theorem PrimeDivisor.canonicalGenericRatio_eq_mul_of_genericStalkChart
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
      Function.Bijective fun r : chartRing B S hS X hX W ↦ r • e W k)
    (pP : ybar.val.siteObject ⟶ (Z.genericStalkBaseChangeChart B S hS hX hdec N.chart).obj.left)
    (hpP : (Z.genericStalkBaseChangeChart B S hS hX hdec N.chart).obj.hom.app
      (op ybar.val.siteObject) pP = ybar.val.value)
    (hpPg : pP ≫ (Z.genericStalkBaseChangeDiagram B S hS hX hdec N.chart).g = N.point)
    {Q : SmallEtale B S hS (Z.genericStalkSpace B S hS hX hdec).1}
    (ι : Q ⟶ Z.genericStalkBaseChangeChart B S hS hX hdec N.chart)
    (hQ : IsAffine (chartScheme Q)) (q : ybar.val.siteObject ⟶ Q.obj.left)
    (hq : Q.obj.hom.app (op ybar.val.siteObject) q = ybar.val.value)
    (hqι : q ≫ (SmallEtale.toOver B S hS (Z.genericStalkSpace B S hS hX hdec).1).map ι = pP)
    (v : chartRing B S hS (Z.genericStalkSpace B S hS hX hdec).1
      (Z.genericStalkSpace B S hS hX hdec).2 Q)
    (hv : ∀ t : MeromorphicSection.{u, u} B S hS X hX L,
      ((Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS
          (Z.genericStalkSpace B S hS hX hdec).1
          (Z.genericStalkSpace B S hS hX hdec).2).O).obj.map
        (ι ≫ chartToIdEtaleChart B S hS
          (Z.genericStalkBaseChangeChart B S hS hX hdec N.chart)).op).hom
        (Z.genericStalkCoefficient B S hS hX hdec L hL t) =
      algebraMap (chartRing B S hS (Z.genericStalkSpace B S hS hX hdec).1
          (Z.genericStalkSpace B S hS hX hdec).2 Q)
        ((meromorphicChartSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
          (Z.genericStalkSpace B S hS hX hdec).2).obj.obj (op Q)) v *
        Z.baseChangeChartRatio B S hS hX hdec L t N.chart e hecompat hebij ι)
    (t : MeromorphicSection.{u, u} B S hS X hX L) :
    Z.genericTotalFractionRingToEtaleFractionRing B S hS X hX hdec
        (Z.henselianToEtaleLocalRing B S hS hX hdec hy)
        (fun _ hr ↦ Z.henselianToEtaleLocalRing_mem_nonZeroDivisors B S hS hX hdec hy hr)
        (Z.canonicalGenericRatio B S hS hX hdec L hL hInt hN t) =
      affineChartMeromorphicToEtaleFractionRing B S hS ⟨X, hX⟩
          (localRingDimension_eq_zero_of_mem_weaklyAssociatedPointsOfSpace_of_isIntegralSpace
            B S hS hX hInt)
          (hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian B S hS X hX hN) N hV
          (chartRatio B S hS X hX L N.chart e hecompat hebij t) *
        algebraMap _ _ ((RingEquiv.ofBijective _
          (Z.bijective_etaleLocalRingMap_genericStalkMorphism B S hS hX hdec ybar hy hlift)).symm
          (etaleLocalRingGerm B S hS (Z.genericStalkSpace B S hS hX hdec).1 ybar
            (op (⟨Q, q, hq⟩ : SmallEtaleNeighborhood ybar)) v)) := by
  -- the isomorphism of étale local rings along `j`
  have hbij := Z.bijective_etaleLocalRingMap_genericStalkMorphism B S hS hX hdec ybar hy hlift
  set ρe := RingEquiv.ofBijective _ hbij
  -- the hypotheses of Stacks 0EN6 on `Spec(A)`
  have hwaY := Z.localRingDimension_eq_zero_of_mem_weaklyAssociated_genericStalkSpace B S hS hX
    hdec hInt
  have hfinY := Z.hasLocallyFiniteIrreducibleComponents_genericStalkSpace B S hS hX hdec hN
  -- the comparison chart
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
    show ρe.symm (etaleLocalRingGerm B S hS (Z.genericStalkSpace B S hS hX hdec).1 ybar (op NQ)
        _) = _
    rw [h1, ← Z.etaleLocalRingMap_genericStalkToEtaleLocalRing_ΓSpecIso B S hS hX hdec ybar hy
        hlift a]
    show ρe.symm (ρe _) = _
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
    have h := RingHom.congr_fun (etaleLocalRingMap_isEtaleLocalRingMap (Z.genericStalkSpace B S hS
        hX hdec).2
      (Z.genericStalkMorphism B S hS hX hdec).hom ybar NQ N _ hcommQ hpointQ) b
    exact (congrArg ρe.symm h).trans (RingEquiv.symm_apply_apply ρe _)
  -- the reading of the meromorphic functions on `Q` in `Q(𝒪_{X, x̄})`
  have hκ0 : ∀ y ∈ ((structurePresheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1).obj (op Q))⁰,
      κ y ∈ nonZeroDivisors (etaleLocalRing B S hS X (geometricPointMap (Z.genericStalkMorphism B S
      hS hX hdec).hom ybar) : Type (u + 1)) := by
    intro y hy'
    have h := etaleLocalRingGerm_mem_nonZeroDivisors B S hS (Z.genericStalkSpace B S hS hX hdec) NQ
        hQ hy'
    rw [← MulEquivClass.map_nonZeroDivisors ρe.symm]
    exact Submonoid.mem_map_of_mem _ h
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
    show ΘQ (((meromorphicFunctionSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
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
    show ΘQ (((meromorphicFunctionSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
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
  -- conclusion
  have h1 := RingHom.congr_fun hAside (Z.genericStalkCoefficient B S hS hX hdec L hL t)
  have h2 := RingHom.congr_fun hVside (chartRatio B S hS X hX L N.chart e hecompat hebij t)
  refine h1.symm.trans ((congrArg ΘQ (hv t)).trans ((map_mul ΘQ _ _).trans ?_))
  exact (congrArg₂ (· * ·) (hΘQ _) h2).trans (mul_comm _ _)

include hInt hN in
/-- **The unit of the ratio comparison (H3) is unique**: the image of the ratio `s / e` of a
regular meromorphic section is a unit of `Q(𝒪_{X, x̄})`. -/
theorem PrimeDivisor.eq_of_canonicalGenericRatio_eq_mul
    {xbar : GeometricPoint B S hS X} (hxbar : xbar.LiesOver (Z.genericPoint B S hS X))
    (N : SmallEtaleNeighborhood xbar) (hV : IsAffine (chartScheme N.chart))
    (e : (W : SmallEtale B S hS X) → (W ⟶ N.chart) → L.val.obj (op W))
    (hecompat : ∀ (W W' : SmallEtale B S hS X) (k : W ⟶ N.chart) (g : W' ⟶ W),
      (L.val.map g.op).hom (e W k) = e W' (g ≫ k))
    (hebij : ∀ (W : SmallEtale B S hS X) (k : W ⟶ N.chart),
      Function.Bijective fun r : chartRing B S hS X hX W ↦ r • e W k)
    (μ₁ μ₂ : (etaleLocalRing B S hS X xbar : Type (u + 1)))
    (h₁ : ∀ t : MeromorphicSection.{u, u} B S hS X hX L,
      Z.genericTotalFractionRingToEtaleFractionRing B S hS X hX hdec
          (Z.henselianToEtaleLocalRing B S hS hX hdec hxbar)
          (fun _ hr ↦ Z.henselianToEtaleLocalRing_mem_nonZeroDivisors B S hS hX hdec hxbar hr)
          (Z.canonicalGenericRatio B S hS hX hdec L hL hInt hN t) =
        affineChartMeromorphicToEtaleFractionRing B S hS ⟨X, hX⟩
            (localRingDimension_eq_zero_of_mem_weaklyAssociatedPointsOfSpace_of_isIntegralSpace
              B S hS hX hInt)
            (hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian B S hS X hX hN) N hV
            (chartRatio B S hS X hX L N.chart e hecompat hebij t) *
          algebraMap _ _ μ₁)
    (h₂ : ∀ t : MeromorphicSection.{u, u} B S hS X hX L,
      Z.genericTotalFractionRingToEtaleFractionRing B S hS X hX hdec
          (Z.henselianToEtaleLocalRing B S hS hX hdec hxbar)
          (fun _ hr ↦ Z.henselianToEtaleLocalRing_mem_nonZeroDivisors B S hS hX hdec hxbar hr)
          (Z.canonicalGenericRatio B S hS hX hdec L hL hInt hN t) =
        affineChartMeromorphicToEtaleFractionRing B S hS ⟨X, hX⟩
            (localRingDimension_eq_zero_of_mem_weaklyAssociatedPointsOfSpace_of_isIntegralSpace
              B S hS hX hInt)
            (hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian B S hS X hX hN) N hV
            (chartRatio B S hS X hX L N.chart e hecompat hebij t) *
          algebraMap _ _ μ₂) :
    μ₁ = μ₂ := by
  obtain ⟨s, hs⟩ := exists_isRegularMeromorphicSection_of_isIntegralSpace B S hS hX hInt hN L hL
  have hwa := localRingDimension_eq_zero_of_mem_weaklyAssociatedPointsOfSpace_of_isIntegralSpace
    B S hS hX hInt
  have hfin := hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian B S hS X hX hN
  have hu := (isUnit_chartRatio_of_isRegularMeromorphicSection B S hS ⟨X, hX⟩ hwa hfin L N.chart hV
    e hecompat hebij s hs).map (affineChartMeromorphicToEtaleFractionRing B S hS ⟨X, hX⟩ hwa hfin N
      hV)
  exact IsFractionRing.injective _ (FractionRing (etaleLocalRing B S hS X xbar : Type (u + 1)))
    (hu.mul_left_cancel ((h₁ s).symm.trans (h₂ s)))

/-- **Geometric evaluation of the germ of a function on a chart of `Spec 𝒪_{U, u}`, carried to
`𝒪_{X, x̄}`**: it is the value of the function at the lift of `ȳ`. -/
theorem PrimeDivisor.geometricEval_etaleLocalRingMap_symm_germ
    (ybar : GeometricPoint B S hS (Z.genericStalkSpace B S hS hX hdec).1)
    (hy : (geometricPointMap (Z.genericStalkMorphism B S hS hX hdec).hom ybar).LiesOver
      (Z.genericPoint B S hS X))
    (hlift : ybar.val.value ≫ Z.genericStalkSpecToChart B S hS hX hdec =
      (Z.genericChart B S hS hX hdec).liftGeometricPoint _ hy)
    (NQ : SmallEtaleNeighborhood ybar)
    (v : (structurePresheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1).obj (op NQ.chart)) :
    geometricEval B S hS X (geometricPointMap (Z.genericStalkMorphism B S hS hX hdec).hom ybar)
        ((RingEquiv.ofBijective _
          (Z.bijective_etaleLocalRingMap_genericStalkMorphism B S hS hX hdec ybar hy hlift)).symm
          (etaleLocalRingGerm B S hS (Z.genericStalkSpace B S hS hX hdec).1 ybar (op NQ) v)) =
      geometricEvalApp B S hS (Z.genericStalkSpace B S hS hX hdec).1 NQ v := by
  have h := RingHom.congr_fun (geometricEval_comp_of_relativelyRepresentable B S hS
    (Z.genericStalkMorphism B S hS hX hdec) (Z.representable_genericStalkMorphism B S hS hX hdec)
    ybar (etaleLocalRingMap_isEtaleLocalRingMap (Z.genericStalkSpace B S hS hX hdec).2
      (Z.genericStalkMorphism B S hS hX hdec).hom ybar))
    ((RingEquiv.ofBijective _
      (Z.bijective_etaleLocalRingMap_genericStalkMorphism B S hS hX hdec ybar hy hlift)).symm
      (etaleLocalRingGerm B S hS (Z.genericStalkSpace B S hS hX hdec).1 ybar (op NQ) v))
  refine h.symm.trans ?_
  refine (congrArg (geometricEval B S hS (Z.genericStalkSpace B S hS hX hdec).1 ybar)
    (RingEquiv.apply_symm_apply (RingEquiv.ofBijective _
      (Z.bijective_etaleLocalRingMap_genericStalkMorphism B S hS hX hdec ybar hy hlift))
        _)).trans ?_
  exact geometricEval_etaleLocalRingGerm B S hS _ ybar NQ v

end Comparison

end AlgebraicGeometry.Space

end
