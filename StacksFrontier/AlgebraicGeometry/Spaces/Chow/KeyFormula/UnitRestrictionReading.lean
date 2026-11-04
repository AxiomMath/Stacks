module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormula.EtaleResidueFieldComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormula.GenericFieldStalkRatioUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormula.RatioComparisonChartUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaProof.Branch

/-!
# The reading of the restricted generators (G2) for the key formula, Stacks 0EQV

Let `X` be a decent, locally Noetherian, integral algebraic space, `Z ⊂ X` a prime divisor with
generic point `ξ`, `ℒ` an invertible `𝒪_X`-module free on `e` over an affine étale chart `V`,
`W' = V ×_X Z` and `q'` a point of `W'` over `ξ`, with image `q` in `V` and geometric point `x̄`
over `q`.  For a unit `v` of `𝒪^h_{X, ξ}`, the restriction `(v s_ξ)|_Z` is `c · e|_Z` on `W'`, and
(G2) says that the value of `c` at `q'`, read in `κ(𝒪_{X, x̄})`, is `v̄ μ̄⁻¹` for the unit `μ` of
the ratio comparison (H3) at `x̄`.

The proof reads everything in the field `Ω` of `x̄`, where evaluation is injective on
`κ(𝒪_{X, x̄})`.  The geometric point comes from a geometric point `ȳ` of `Spec 𝒪_{U, u}`, which
lifts to an affine chart `Q` of `Spec 𝒪_{U, u}` over the base change of `V` on which
`e = v_Q · s_ξ`; then `μ` is the germ of `v_Q`
(`AlgebraicGeometry.Space.PrimeDivisor.canonicalGenericRatio_eq_mul_of_genericStalkChart` and the
uniqueness `AlgebraicGeometry.Space.PrimeDivisor.eq_of_canonicalGenericRatio_eq_mul`).  On
`P = Spec κ(u) ×_{Spec 𝒪_{U, u}} Q` the ratio of `e|_Z` to `s_ξ` is the pullback of `v_Q`
(`AlgebraicGeometry.Space.PrimeDivisor.genericFieldChartRatio_stalkBaseChange_eq`), and the point
of `P` over `x̄` evaluates the comparison of the two readings
(`AlgebraicGeometry.Space.PrimeDivisor.baseChangeChartSectionReading_mul_eq_of_point`).

## Main results

* `AlgebraicGeometry.Space.PrimeDivisor.baseChangeChartSectionReading_mul_geometricEval`: the
  reading of a meromorphic section of `ℒ|_Z` at `q'`, in `Ω`, times the value of `μ` at `x̄`, is
  its value at the generic point read in `Ω`.
* `AlgebraicGeometry.Space.PrimeDivisor.unitRestrictionReading`: (G2).

## References

* [Stacks Project, Tag 0EQV](https://stacks.math.columbia.edu/tag/0EQV)
* [Stacks Project, Section 0EQU](https://stacks.math.columbia.edu/tag/0EQU)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) (Z : PrimeDivisor B S hS X)

/-! ### Points of `P = Spec κ(u) ×_{Spec 𝒪_{U, u}} Q` -/

section Points

/-- The closed point `Spec κ(u) → Spec 𝒪_{U, u}` is the residue-field point of the closed
point of `Spec 𝒪_{U, u}`. -/
theorem PrimeDivisor.genericFieldToStalkSpec_eq_genericStalkResidueFieldPoint :
    Z.genericFieldToStalkSpec B S hS hX hdec = Z.genericStalkResidueFieldPoint B S hS hX hdec :=
  rfl

/-- **A geometric point of `Spec 𝒪_{U, u}` over a geometric point `x̄` of `X` over `ξ`**, lying
over `x̄` on the nose, whose lift to the chosen chart is the lift of `x̄`, and whose value factors
through the closed point `Spec κ(u) → Spec 𝒪_{U, u}` along the factorization of `x̄` through the
residue-field point of the chart. -/
theorem PrimeDivisor.exists_genericStalkGeometricPoint {xbar : GeometricPoint B S hS X}
    (hxbar : xbar.LiesOver (Z.genericPoint B S hS X)) :
    ∃ ybar : GeometricPoint B S hS (Z.genericStalkSpace B S hS hX hdec).1,
      geometricPointMap (Z.genericStalkMorphism B S hS hX hdec).hom ybar = xbar ∧
      (∀ h : (geometricPointMap (Z.genericStalkMorphism B S hS hX hdec).hom ybar).LiesOver
          (Z.genericPoint B S hS X),
        ybar.val.value ≫ Z.genericStalkSpecToChart B S hS hX hdec =
          (Z.genericChart B S hS hX hdec).liftGeometricPoint _ h) ∧
      (∀ h : (geometricPointMap (Z.genericStalkMorphism B S hS hX hdec).hom ybar).LiesOver
          (Z.genericPoint B S hS X),
        (Z.genericChart B S hS hX hdec).liftResidueField _ h ≫
          Z.genericFieldToStalkSpec B S hS hX hdec = ybar.val.value) := by
  have key : ∀ {β : GeometricPoint B S hS X → Type _}
      (f : ∀ x, x.LiesOver (Z.genericPoint B S hS X) → β x) {x₁ x₂ : GeometricPoint B S hS X}
      (_ : x₁ = x₂) (h₁ : x₁.LiesOver (Z.genericPoint B S hS X))
      (h₂ : x₂.LiesOver (Z.genericPoint B S hS X)), HEq (f x₁ h₁) (f x₂ h₂) := by
    rintro _ _ _ _ rfl _ _
    rfl
  refine ⟨Z.genericStalkGeometricPoint B S hS hX hdec hxbar,
    Z.geometricPointMap_genericStalkGeometricPoint B S hS hX hdec hxbar, fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [Z.genericStalkGeometricPoint_value_comp B S hS hX hdec hxbar]
    exact eq_of_heq (key (Z.genericChart B S hS hX hdec).liftGeometricPoint
      (Z.geometricPointMap_genericStalkGeometricPoint B S hS hX hdec hxbar).symm hxbar h)
  · exact (congrArg (_ ≫ ·) (Z.genericFieldToStalkSpec_eq_genericStalkResidueFieldPoint B S hS
      hX hdec)).trans (congrArg (· ≫ Z.genericStalkResidueFieldPoint B S hS hX hdec)
      (eq_of_heq (key (Z.genericChart B S hS hX hdec).liftResidueField
        (Z.geometricPointMap_genericStalkGeometricPoint B S hS hX hdec hxbar) h hxbar)))

variable (Q : SmallEtale B S hS (Z.genericStalkSpace B S hS hX hdec).1)

/-- **A point of `P = Spec κ(u) ×_{Spec 𝒪_{U, u}} Q`** from a point `a` of `Spec κ(u)` and a
point `q` of `Q` over the same point of `Spec 𝒪_{U, u}`. -/
def PrimeDivisor.genericFieldStalkBaseChangeLift {T : BigFppfOver B S hS}
    (a : T ⟶ Z.genericFieldSpec B S hS hX hdec) (q : T ⟶ Q.obj.left)
    (h : yoneda.map a ≫ (Z.genericFieldToStalk B S hS hX hdec).hom = yoneda.map q ≫ Q.1.hom) :
    T ⟶ (Z.genericFieldStalkBaseChangeChart B S hS hX hdec Q).obj.left :=
  (Z.representable_genericFieldToStalk B S hS hX hdec).lift (yoneda.map a) q h

/-- The point of `P` lies over `q`. -/
theorem PrimeDivisor.genericFieldStalkBaseChangeLift_snd {T : BigFppfOver B S hS}
    (a : T ⟶ Z.genericFieldSpec B S hS hX hdec) (q : T ⟶ Q.obj.left)
    (h : yoneda.map a ≫ (Z.genericFieldToStalk B S hS hX hdec).hom = yoneda.map q ≫ Q.1.hom) :
    Z.genericFieldStalkBaseChangeLift B S hS hX hdec Q a q h ≫
        (Z.representable_genericFieldToStalk B S hS hX hdec).snd Q.obj.hom = q :=
  (Z.representable_genericFieldToStalk B S hS hX hdec).lift_snd _ _ _

/-- The point of `P` lies over `a`. -/
theorem PrimeDivisor.genericFieldStalkBaseChangeLift_toId {T : BigFppfOver B S hS}
    (a : T ⟶ Z.genericFieldSpec B S hS hX hdec) (q : T ⟶ Q.obj.left)
    (h : yoneda.map a ≫ (Z.genericFieldToStalk B S hS hX hdec).hom = yoneda.map q ≫ Q.1.hom) :
    Z.genericFieldStalkBaseChangeLift B S hS hX hdec Q a q h ≫
        (SmallEtale.toOver B S hS (Z.genericFieldSpace B S hS hX hdec).1).map
          (chartToIdEtaleChart B S hS (Z.genericFieldStalkBaseChangeChart B S hS hX hdec Q)) =
      a := by
  apply yoneda.map_injective
  refine (yoneda.map_comp _ _).trans ?_
  refine (congrArg (yoneda.map (Z.genericFieldStalkBaseChangeLift B S hS hX hdec Q a q h) ≫ ·)
    (Functor.map_preimage yoneda _)).trans ?_
  exact (Z.representable_genericFieldToStalk B S hS hX hdec).lift_fst _ _ _

end Points

/-! ### The reading of a meromorphic section of `ℒ|_Z` against `e|_Z`, in the field of `x̄` -/

section Core

attribute [local instance] chartMeromorphicAlgebra chartMeromorphicFunctionAlgebra
attribute [local instance] meromorphicSectionModuleRingedSiteModule

variable (hInt : IsIntegralSpace B S hS X)
  (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} ↦ IsLocallyNoetherian Y))
  (L : Modules.{u, u} B S hS X hX) (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L)

include hInt hN in
/-- **The reading of a meromorphic section `σ` of `ℒ|_Z` at a point `q'` of `W' = V ×_X Z`,
in the field of a geometric point `x̄` over `ξ`, times the value at `x̄` of the unit `μ` of the
ratio comparison (H3), is the value of `σ` at the generic point, read in the field of `x̄`.**
Here `(V, x̄ → V)` is a small étale neighbourhood of `x̄` with affine scheme over which `ℒ` is
free on `e`, and the lift of `x̄` to `V` is `Spec ψ` followed by `Spec κ(π q') → V`. -/
theorem PrimeDivisor.baseChangeChartSectionReading_mul_geometricEval
    {xbar : GeometricPoint B S hS X} (hxbar : xbar.LiesOver (Z.genericPoint B S hS X))
    (N : SmallEtaleNeighborhood xbar) (hV : IsAffine (chartScheme N.chart))
    (e : (W : SmallEtale B S hS X) → (W ⟶ N.chart) → L.val.obj (op W))
    (hecompat : ∀ (W W' : SmallEtale B S hS X) (k : W ⟶ N.chart) (g : W' ⟶ W),
      (L.val.map g.op).hom (e W k) = e W' (g ≫ k))
    (hebij : ∀ (W : SmallEtale B S hS X) (k : W ⟶ N.chart),
      Function.Bijective fun r : chartRing B S hS X hX W ↦ r • e W k)
    (hW : IsAffine (chartScheme (Z.baseChangeChart B S hS hX N.chart)))
    (hK : @IsFractionRing ((structurePresheaf B S hS (Z.space B S hS).1).obj
        (op (Z.baseChangeChart B S hS hX N.chart))) _
      ((meromorphicFunctionSheaf B S hS (Z.space B S hS).1 (Z.space B S hS).2).obj.obj
        (op (Z.baseChangeChart B S hS hX N.chart))) _
      (chartMeromorphicFunctionAlgebra B S hS (X := Z.space B S hS)
        (Z.baseChangeChart B S hS hX N.chart)))
    (q' : chartScheme (Z.baseChangeChart B S hS hX N.chart))
    (hz : IsField ((chartScheme (Z.baseChangeChart B S hS hX N.chart)).presheaf.stalk q'))
    (ψ : (chartScheme N.chart).residueField (Z.baseChangeChartProj B S hS hX N.chart q') ⟶
      .of xbar.val.carrier)
    (hψ : (BigFppfOver.toScheme B S hS).map N.point =
      Spec.map ψ ≫ (chartScheme N.chart).fromSpecResidueField
        (Z.baseChangeChartProj B S hS hX N.chart q'))
    (μ : (etaleLocalRing B S hS X xbar : Type (u + 1)))
    (hμ : ∀ t : MeromorphicSection.{u, u} B S hS X hX L,
      Z.genericTotalFractionRingToEtaleFractionRing B S hS X hX hdec
          (Z.henselianToEtaleLocalRing B S hS hX hdec hxbar)
          (fun _ hr ↦ Z.henselianToEtaleLocalRing_mem_nonZeroDivisors B S hS hX hdec hxbar hr)
          (Z.canonicalGenericRatio B S hS hX hdec L hL hInt hN t) =
        affineChartMeromorphicToEtaleFractionRing B S hS ⟨X, hX⟩
            (localRingDimension_eq_zero_of_mem_weaklyAssociatedPointsOfSpace_of_isIntegralSpace
              B S hS hX hInt)
            (hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian B S hS X hX hN) N hV
            (chartRatio B S hS X hX L N.chart e hecompat hebij t) *
          algebraMap _ _ μ)
    (σ : MeromorphicSection.{u, u} B S hS Z.subspace.toFunctor Z.closed.1
      (Z.restrictModule B S hS hX L)) :
    ψ ((Z.baseChangeChartResidueFieldEquiv B S hS hX N.chart q').symm
        (Z.baseChangeChartSectionReading B S hS hX L hL N.chart e hecompat hebij hW hK q' hz σ)) *
      geometricEval B S hS X xbar μ =
      Z.genericResidueFieldToGeometric B S hS hX hdec hxbar
        (Z.genericFieldValue B S hS hX hdec L hL σ) := by
  obtain ⟨ybar, hyb, hlift, hval⟩ := Z.exists_genericStalkGeometricPoint B S hS hX hdec hxbar
  subst hyb
  -- the data of the ratio comparison over a chart `Q` of `Spec 𝒪_{U, u}`
  obtain ⟨pP, hpP, hpPg⟩ := Z.exists_lift_genericStalkBaseChangeChart B S hS hX hdec ybar
    N.chart N.point N.point_comp
  obtain ⟨T, hT, hTbij⟩ := exists_sieve_bijective_smul_modulePullbackChartSection B S hS
    (Z.genericStalkMorphism B S hS hX hdec) L
    (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hL)
    (Z.genericStalkBaseChangeDiagram B S hS hX hdec N.chart) e hecompat hebij
  obtain ⟨Q, ι, hι, hQ, q, hq, hqι⟩ := exists_affine_mem_lift_of_mem_topology B S hS ybar hT pP hpP
  obtain ⟨v, hv⟩ := Z.exists_isUnit_smul_genericStalkGenerator B S hS hX hdec L hL Q
    (ι ≫ chartToIdEtaleChart B S hS (Z.genericStalkBaseChangeChart B S hS hX hdec N.chart))
    (modulePullbackChartSectionRestrict B S hS (Z.genericStalkMorphism B S hS hX hdec) L
      (Z.genericStalkBaseChangeDiagram B S hS hX hdec N.chart) (e N.chart (𝟙 N.chart)) (𝟙 Q ≫ ι))
    (hTbij ι hι Q (𝟙 Q))
  have hvt := Z.genericStalkCoefficient_restrict_eq_mul_of_eq_smul B S hS hX hdec L hL N.chart e
    hecompat hebij ι (v : chartRing B S hS (Z.genericStalkSpace B S hS hX hdec).1
      (Z.genericStalkSpace B S hS hX hdec).2 Q) hv
  have hμ0 := Z.canonicalGenericRatio_eq_mul_of_genericStalkChart B S hS hX hdec hInt hN L hL
    ybar hxbar (hlift hxbar) N hV e hecompat hebij pP hpP hpPg ι hQ q hq hqι _ hvt
  have hμeq := Z.eq_of_canonicalGenericRatio_eq_mul B S hS hX hdec hInt hN L hL hxbar N hV e
    hecompat hebij μ _ hμ hμ0
  have hev : geometricEval B S hS X _ μ =
      geometricEvalApp B S hS (Z.genericStalkSpace B S hS hX hdec).1
        (⟨Q, q, hq⟩ : SmallEtaleNeighborhood ybar)
        (v : chartRing B S hS (Z.genericStalkSpace B S hS hX hdec).1
          (Z.genericStalkSpace B S hS hX hdec).2 Q) :=
    hμeq ▸ Z.geometricEval_etaleLocalRingMap_symm_germ B S hS hX hdec ybar hxbar (hlift hxbar)
      ⟨Q, q, hq⟩ (v : chartRing B S hS (Z.genericStalkSpace B S hS hX hdec).1
        (Z.genericStalkSpace B S hS hX hdec).2 Q)
  -- the point `t` of `P = Spec κ(u) ×_{Spec 𝒪_{U, u}} Q` over `x̄`
  have hcond : yoneda.map ((Z.genericChart B S hS hX hdec).liftResidueField _ hxbar) ≫
      (Z.genericFieldToStalk B S hS hX hdec).hom = yoneda.map q ≫ Q.1.hom := by
    refine (yoneda.map_comp ((Z.genericChart B S hS hX hdec).liftResidueField _ hxbar)
      (Z.genericFieldToStalkSpec B S hS hX hdec)).symm.trans ?_
    have hpre : q ≫ yoneda.preimage Q.obj.hom = ybar.val.value :=
      (congrArg (fun α ↦ α.app (op ybar.val.siteObject) q)
        (Functor.map_preimage yoneda Q.obj.hom)).trans hq
    refine (congrArg yoneda.map ((hval hxbar).trans hpre.symm)).trans ?_
    exact (yoneda.map_comp _ _).trans (congrArg (yoneda.map q ≫ ·)
      (Functor.map_preimage yoneda Q.obj.hom))
  set t := Z.genericFieldStalkBaseChangeLift B S hS hX hdec Q
    ((Z.genericChart B S hS hX hdec).liftResidueField _ hxbar) q hcond with ht
  have hφ : (BigFppfOver.toScheme B S hS).map (t ≫ (SmallEtale.toOver B S hS _).map
      (chartToIdEtaleChart B S hS (Z.genericFieldStalkBaseChangeChart B S hS hX hdec Q))) =
      Spec.map (CommRingCat.ofHom (Z.genericResidueFieldToGeometric B S hS hX hdec hxbar)) := by
    refine (congrArg (BigFppfOver.toScheme B S hS).map
      (Z.genericFieldStalkBaseChangeLift_toId B S hS hX hdec Q _ q hcond)).trans ?_
    exact (spec_fieldValuedPointHom B S hS X _ _ _).symm
  have hpointQ : q ≫ (SmallEtale.toOver B S hS (Z.genericStalkSpace B S hS hX hdec).1).map ι ≫
      (Z.genericStalkBaseChangeDiagram B S hS hX hdec N.chart).g = N.point :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hqι).trans hpPg)
  have hψ' : (BigFppfOver.toScheme B S hS).map
      (t ≫ Z.genericFieldStalkBaseChangeToChart B S hS hX hdec N.chart Q ι) =
      Spec.map (CommRingCat.ofHom
        (Z.baseChangeChartResidueFieldEquiv B S hS hX N.chart q').symm.toRingHom ≫ ψ) ≫
        (chartScheme (Z.baseChangeChart B S hS hX N.chart)).fromSpecResidueField q' := by
    have := Z.isClosedImmersion_baseChangeChartProj B S hS hX N.chart
    apply (cancel_mono (Z.baseChangeChartProj B S hS hX N.chart)).1
    refine Eq.trans ?_ (((Category.assoc _ _ _).trans
      (Z.SpecMap_baseChangeChartResidueFieldEquiv_symm B S hS hX N.chart q' ψ)).trans hψ.symm).symm
    refine ((BigFppfOver.toScheme B S hS).map_comp _ _).symm.trans
      (congrArg (BigFppfOver.toScheme B S hS).map ?_)
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (t ≫ ·) (Z.genericFieldStalkBaseChangeToChart_comp_g B S hS hX hdec N.chart
      Q ι)).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ _) (Z.genericFieldStalkBaseChangeLift_snd B S hS hX hdec Q _ q
      hcond)).trans ?_
    exact hpointQ
  -- the reading at the field point `t`
  have hA := Z.baseChangeChartSectionReading_mul_eq_of_point B S hS hX hdec N.chart q' L hL e
    hecompat hebij hW hK hz (Z.genericFieldStalkBaseChangeChart B S hS hX hdec Q)
    (Z.genericFieldStalkBaseChangeToChart B S hS hX hdec N.chart Q ι)
    (Z.genericFieldStalkBaseChangeToChart_comm B S hS hX hdec N.chart Q ι) σ
    (geometricPointMap (Z.genericStalkMorphism B S hS hX hdec).hom ybar).val t
    (Z.genericResidueFieldToGeometric B S hS hX hdec hxbar) hφ _ hψ'
  -- the ratio `w` on `P` is the pullback of `v`
  have hc : (Z.genericFieldStalkBaseChangeChart B S hS hX hdec Q).1.hom ≫
      (Z.genericFieldToStalk B S hS hX hdec).hom =
      yoneda.map ((Z.representable_genericFieldToStalk B S hS hX hdec).snd Q.obj.hom) ≫
        Q.1.hom :=
    ((Z.representable_genericFieldToStalk B S hS hX hdec).isPullback Q.obj.hom).w
  have hb : (Z.baseChangeChart B S hS hX N.chart).1.hom ≫ (Z.inclusion B S hS hX).hom =
      yoneda.map ((SmallEtale.toOver B S hS Z.subspace.toFunctor).map
        (𝟙 (Z.baseChangeChart B S hS hX N.chart)) ≫
          (Z.baseChangeChartDiagram B S hS hX N.chart).g) ≫ N.chart.1.hom :=
    (Z.baseChangeChartGeneratorDiagram B S hS hX N.chart
      (𝟙 (Z.baseChangeChart B S hS hX N.chart))).comm
  have hw := Z.genericFieldChartRatio_stalkBaseChange_eq B S hS hX hdec L hL N.chart e hecompat Q ι
    (Z.genericStalkBaseChangeChart_comm B S hS hX hdec N.chart Q ι) hb hc _ hv
  -- the value of the pullback of `v` at `t`
  have hevt : (Scheme.ΓSpecIso (CommRingCat.of ybar.val.carrier)).hom.hom
      ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map t).op).hom
        (chartDiagramPullback B S hS (Z.genericFieldToStalk B S hS hX hdec)
          ⟨Z.genericFieldStalkBaseChangeChart B S hS hX hdec Q, Q,
            (Z.representable_genericFieldToStalk B S hS hX hdec).snd Q.obj.hom, hc⟩
          (v : chartRing B S hS (Z.genericStalkSpace B S hS hX hdec).1
            (Z.genericStalkSpace B S hS hX hdec).2 Q))) =
      geometricEvalApp B S hS (Z.genericStalkSpace B S hS hX hdec).1
        (⟨Q, q, hq⟩ : SmallEtaleNeighborhood ybar)
        (v : chartRing B S hS (Z.genericStalkSpace B S hS hX hdec).1
          (Z.genericStalkSpace B S hS hX hdec).2 Q) := by
    have h1 : (BigFppfOver.toScheme B S hS).map t ≫ (BigFppfOver.toScheme B S hS).map
        ((Z.representable_genericFieldToStalk B S hS hX hdec).snd Q.obj.hom) =
        (BigFppfOver.toScheme B S hS).map q :=
      ((BigFppfOver.toScheme B S hS).map_comp _ _).symm.trans (congrArg _
        (Z.genericFieldStalkBaseChangeLift_snd B S hS hX hdec Q _ q hcond))
    have h2 : Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map q).op =
        Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
          ((Z.representable_genericFieldToStalk B S hS hX hdec).snd Q.obj.hom)).op ≫
        Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map t).op :=
      (congrArg (fun f ↦ Scheme.Γ.map (Opposite.op f)) h1.symm).trans (Scheme.Γ.map_comp _ _)
    exact congrArg (fun φ ↦ (Scheme.ΓSpecIso (CommRingCat.of ybar.val.carrier)).hom.hom
      (φ.hom (v : chartRing B S hS (Z.genericStalkSpace B S hS hX hdec).1
        (Z.genericStalkSpace B S hS hX hdec).2 Q))) h2.symm
  rw [hw] at hA
  refine Eq.trans ?_ hA
  exact congrArg₂ (· * ·) rfl (hev.trans hevt.symm)

end Core

/-! ### (G2) -/

section UnitReading

variable (hInt : IsIntegralSpace B S hS X)
  (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} ↦ IsLocallyNoetherian Y))
  (V : SmallEtale B S hS X) (hV : IsAffine (chartScheme V))
  (L : Modules.{u, u} B S hS X hX) (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L)
  (e : (W : SmallEtale B S hS X) → (W ⟶ V) → L.val.obj (op W))
  (hecompat : ∀ (W W' : SmallEtale B S hS X) (k : W ⟶ V) (g : W' ⟶ W),
    (L.val.map g.op).hom (e W k) = e W' (g ≫ k))
  (hebij : ∀ (W : SmallEtale B S hS X) (k : W ⟶ V),
    Function.Bijective fun r : chartRing B S hS X hX W ↦ r • e W k)
  (hNZ : HasEtaleLocalProperty B S hS Z.subspace.toFunctor
    (fun Y : Scheme.{u} ↦ IsLocallyNoetherian Y))
  (hV' : IsAffine (chartScheme (Z.baseChangeChart B S hS hX V)))

/-- **(G2) for the key formula, Stacks 0EQV.** At every point `q'` of `W' = V ×_X Z` over the
generic point of `Z`, the value at `q'` of the coefficient of `(v s_ξ)|_Z` against the restricted
generator `e|_Z`, moved to `κ(q) = κ(q')` and read in `κ(𝒪_{X, x̄})`, is `v̄ μ̄⁻¹` for every unit
`μ` of the ratio comparison (H3) at `q`. -/
theorem PrimeDivisor.unitRestrictionReading
    (v : (↥(Z.genericHenselianLocalRing B S hS hX hdec))ˣ) :
    Z.UnitRestrictionReading B S hS hX hdec hInt hN V hV L hL e hecompat hebij hNZ hV' v := by
  intro q' hq' μ hμ
  let := isLocalRing_etaleLocalRing B S hS X hX
    (chartGeometricPointAt B S hS hX V (Z.baseChangeChartProj B S hS hX V q'))
  let := henselianLocalRing_isLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
  obtain ⟨ψ, hψ⟩ := Scheme.exists_eq_SpecMap_comp_fromSpecResidueField
    ((BigFppfOver.toScheme B S hS).map
      (chartNeighborhoodAt B S hS hX V (Z.baseChangeChartProj B S hS hX V q')).point)
    (chartPoint_chartNeighborhoodAt B S hS hX V (Z.baseChangeChartProj B S hS hX V q'))
  have hcore := Z.baseChangeChartSectionReading_mul_geometricEval B S hS hX hdec hInt hN L hL
    (Z.liesOver_chartGeometricPointAt_baseChangeChartProj B S hS hX V q' hq')
    (chartNeighborhoodAt B S hS hX V (Z.baseChangeChartProj B S hS hX V q')) hV e hecompat hebij
    hV' (isFractionRing_meromorphicFunctionSheaf_obj B S hS (Z.space B S hS)
      (localRingDimension_eq_zero_of_mem_weaklyAssociatedPointsOfSpace_of_isIntegralSpace
        B S hS Z.closed.1 Z.integral)
      (hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian B S hS
        Z.subspace.toFunctor Z.closed.1 hNZ) _ hV') q'
    (Z.isField_stalk_baseChangeChart B S hS hX V q' hq') ψ hψ μ.val hμ
    (Z.henselianUnitRestriction B S hS hX hdec hN L hL v)
  have hval : Z.genericFieldValue B S hS hX hdec L hL
      (Z.henselianUnitRestriction B S hS hX hdec hN L hL v) =
      (Z.genericResidueFieldEquivHenselian B S hS hX hdec).symm
        (IsLocalRing.residue _ (v : ↥(Z.genericHenselianLocalRing B S hS hX hdec))) :=
    Z.genericFieldValue_genericRestrictionOf B S hS hX hdec hN L hL _
  have hH : etaleResidueFieldEval B S hS hX
      (chartGeometricPointAt B S hS hX V (Z.baseChangeChartProj B S hS hX V q'))
      (Z.henselianResidueFieldToEtale B S hS hX hdec
        (Z.liesOver_chartGeometricPointAt_baseChangeChartProj B S hS hX V q' hq')
        (IsLocalRing.residue _ (v : ↥(Z.genericHenselianLocalRing B S hS hX hdec)))) =
      Z.genericResidueFieldToGeometric B S hS hX hdec
        (Z.liesOver_chartGeometricPointAt_baseChangeChartProj B S hS hX V q' hq')
        (Z.genericFieldValue B S hS hX hdec L hL
          (Z.henselianUnitRestriction B S hS hX hdec hN L hL v)) := by
    rw [hval, ← Z.etaleResidueFieldEval_henselianToEtaleLocalRing B S hS hX hdec
      (Z.liesOver_chartGeometricPointAt_baseChangeChartProj B S hS hX V q' hq'),
      RingEquiv.apply_symm_apply]
    rfl
  have hne : geometricEval B S hS X
      (chartGeometricPointAt B S hS hX V (Z.baseChangeChartProj B S hS hX V q')) μ.val ≠ 0 :=
    (μ.isUnit.map (geometricEval B S hS X _)).ne_zero
  apply (etaleResidueFieldEval B S hS hX
    (chartGeometricPointAt B S hS hX V (Z.baseChangeChartProj B S hS hX V q'))).injective
  rw [map_mul, map_inv₀, hH, etaleResidueFieldEval_residue]
  refine (etaleResidueFieldEval_map_chartStalkToEtaleLocalRing B S hS hX _
    (chartPoint_chartNeighborhoodAt B S hS hX V (Z.baseChangeChartProj B S hS hX V q')) ψ hψ
    _).trans ?_
  exact (eq_mul_inv_iff_mul_eq₀ hne).2 hcore

end UnitReading

end AlgebraicGeometry.Space

end
