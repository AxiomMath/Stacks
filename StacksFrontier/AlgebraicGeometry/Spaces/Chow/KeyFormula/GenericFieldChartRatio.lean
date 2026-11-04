module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormula.GenericPointChartReading
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormula.GenericRestriction

/-!
# Reading a meromorphic section of `ℒ|_Z` on a chart of `Spec κ(u)` over the base-change chart

Let `X` be a decent algebraic space, `Z ⊂ X` a prime divisor with chosen residue-field point
`ρ_Z : Spec κ(u) → Z`, `ℒ` an invertible `𝒪_X`-module free on a family `e` over an étale chart
`V` of `X`, and `W' = V ×_X Z` the base-change chart of `Z`, over which `ℒ|_Z` is free on the
restricted family `e|_Z`.  A meromorphic section `σ` of `ℒ|_Z` is `c · e|_Z` over `W'`
(`AlgebraicGeometry.Space.PrimeDivisor.baseChangeChartSectionCoefficient`), and its value at the
generic point of `Z` is read by pulling it back along `ρ_Z`
(`AlgebraicGeometry.Space.PrimeDivisor.genericFieldValue`).  The chart `W'` need not receive
`ρ_Z`, so the two readings are compared on an étale chart `P` of `Spec κ(u)` with a morphism to
`W'` over `ρ_Z`: there the inverse image of `e|_Z` is `w` times the image of the generator `s_ξ`
for a function `w` on `P`, and the pullback of `c` times `w` is the value of `σ`.

## Main definitions

* `AlgebraicGeometry.Space.PrimeDivisor.genericFieldChartDiagram`: the square `(P, W')` over
  `ρ_Z`.
* `AlgebraicGeometry.Space.PrimeDivisor.genericFieldChartRatio`: the function `w` on `P` with
  `ρ_Z^*(e|_Z) = w · s_ξ`.

## Main results

* `AlgebraicGeometry.Space.PrimeDivisor.chartMeromorphicPullbackHom_mul_genericFieldChartRatio`:
  on `P`, the pullback of the coefficient `c` of `σ` times `w` is the value of `σ`.
* `AlgebraicGeometry.Space.PrimeDivisor.chartDiagramRestrict_mul_genericFieldChartRatio`: the same
  cleared of denominators, as regular functions on `P`.

## References

* [Stacks Project, Section 0EQU](https://stacks.math.columbia.edu/tag/0EQU)
* [Stacks Project, Tag 0ENC](https://stacks.math.columbia.edu/tag/0ENC)
-/
@[expose] public noncomputable section

open CategoryTheory Opposite TensorProduct

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology
attribute [local instance] chartMeromorphicAlgebra
attribute [local instance] meromorphicSectionModuleRingedSiteModule

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) (Z : PrimeDivisor B S hS X)

/-! ### The ratio of the restricted generator to `s_ξ` on a chart of `Spec κ(u)` over `W'` -/

variable (L : Modules.{u, u} B S hS X hX) (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L)
    (V : SmallEtale B S hS X)
    (e : (W' : SmallEtale B S hS X) → (W' ⟶ V) → L.val.obj (op W'))
    (hcompat : ∀ (W₁ W₂ : SmallEtale B S hS X) (k : W₁ ⟶ V) (g : W₂ ⟶ W₁),
      (L.val.map g.op).hom (e W₁ k) = e W₂ (g ≫ k))
    (hfree : ∀ (W₁ : SmallEtale B S hS X) (k : W₁ ⟶ V),
      Function.Bijective fun r : chartRing B S hS X hX W₁ ↦ r • e W₁ k)
    (P : SmallEtale B S hS (Z.genericFieldSpace B S hS hX hdec).1)
    (g : (SmallEtale.toOver B S hS _).obj P ⟶
      (SmallEtale.toOver B S hS Z.subspace.toFunctor).obj (Z.baseChangeChart B S hS hX V))
    (hg : P.1.hom ≫ (Z.genericFieldMorphism B S hS hX hdec).hom =
      yoneda.map g ≫ (Z.baseChangeChart B S hS hX V).1.hom)

/-- The square `(P, W')` over `ρ_Z` for an étale chart `P` of `Spec κ(u)` with a morphism `g` to
the base-change chart `W' = V ×_X Z` over `ρ_Z`. -/
abbrev PrimeDivisor.genericFieldChartDiagram :
    ChartDiagram B S hS (Z.genericFieldSpace B S hS hX hdec).1 Z.subspace.toFunctor
      (Z.genericFieldMorphism B S hS hX hdec).hom :=
  ⟨P, Z.baseChangeChart B S hS hX V, g, hg⟩

/-- **The ratio `w` of the inverse image of `e|_Z` to the image of `s_ξ`** on an étale chart `P`
of `Spec κ(u)` over the base-change chart `W' = V ×_X Z`. -/
def PrimeDivisor.genericFieldChartRatio :
    chartRing B S hS (Z.genericFieldSpace B S hS hX hdec).1 (Z.genericFieldSpace B S hS hX hdec).2
      P :=
  (Equiv.ofBijective _ (Z.bijective_smul_genericFieldGenerator B S hS hX hdec L hL
    P
    (chartToIdEtaleChart B S hS _))).symm
    ((modulePullbackChartFMap B S hS (Z.genericFieldMorphism B S hS hX hdec)
      (Z.restrictModule B S hS hX L)).app
      (Z.genericFieldChartDiagram B S hS hX hdec V P g hg)
      (Z.baseChangeChartGenerator B S hS hX L V e (Z.baseChangeChart B S hS hX V)
        (𝟙 (Z.baseChangeChart B S hS hX V))))

/-- **The defining property of `w`**: the inverse image of `e|_Z` on `P` is `w` times the image
of `s_ξ`. -/
theorem PrimeDivisor.modulePullbackChartFMap_baseChangeChartGenerator_eq_genericFieldChartRatio_smul
    : (modulePullbackChartFMap B S hS (Z.genericFieldMorphism B S hS hX hdec)
      (Z.restrictModule B S hS hX L)).app
      (Z.genericFieldChartDiagram B S hS hX hdec V P g hg)
      (Z.baseChangeChartGenerator B S hS hX L V e (Z.baseChangeChart B S hS hX V)
        (𝟙 (Z.baseChangeChart B S hS hX V))) =
      Z.genericFieldChartRatio B S hS hX hdec L hL V e P g hg •
        Z.genericFieldGenerator B S hS hX hdec L hL
          P
          (chartToIdEtaleChart B S hS _) :=
  ((Equiv.ofBijective _ (Z.bijective_smul_genericFieldGenerator B S hS hX hdec L hL
    P
    (chartToIdEtaleChart B S hS _))).apply_symm_apply _).symm

/-- **The two readings of a meromorphic section of `ℒ|_Z` on `P`**: the pullback along `ρ_Z`
of the coefficient `c` of `σ` against `e|_Z` over `W'`, times the ratio `w` of `e|_Z` to `s_ξ`,
is the restriction to `P` of the value of `σ` at the generic point. -/
theorem PrimeDivisor.chartMeromorphicPullbackHom_mul_genericFieldChartRatio
    (σ : MeromorphicSection.{u, u} B S hS Z.subspace.toFunctor Z.closed.1
      (Z.restrictModule B S hS hX L)) :
    chartMeromorphicPullbackHom B S hS (Z.genericFieldMorphism B S hS hX hdec)
        (Z.pullbacksMeromorphicSections_genericFieldMorphism B S hS hX hdec)
        (Z.genericFieldChartDiagram B S hS hX hdec V P g hg)
        (Z.baseChangeChartSectionCoefficient B S hS hX L hL V e hcompat hfree σ) *
      algebraMap (chartRing B S hS (Z.genericFieldSpace B S hS hX hdec).1
          (Z.genericFieldSpace B S hS hX hdec).2
          P)
        ((meromorphicChartSheaf B S hS (Z.genericFieldSpace B S hS hX hdec).1
          (Z.genericFieldSpace B S hS hX hdec).2).obj.obj
          (op P))
        (Z.genericFieldChartRatio B S hS hX hdec L hL V e P g hg) =
      ((meromorphicChartSheaf B S hS (Z.genericFieldSpace B S hS hX hdec).1
          (Z.genericFieldSpace B S hS hX hdec).2).obj.map
        (chartToIdEtaleChart B S hS
          P).op).hom
        (Z.genericFieldMeromorphicEquiv B S hS hX hdec
          (Z.genericFieldValue B S hS hX hdec L hL σ)) := by
  have h1 := pullbackMeromorphicSection_eval_chartDiagram B S hS
    (Z.genericFieldMorphism B S hS hX hdec) (Z.restrictModule B S hS hX L)
    (Z.pullbacksMeromorphicSections_genericFieldMorphism B S hS hX hdec) σ
    (Z.genericFieldChartDiagram B S hS hX hdec V P g hg) _
    (eval_eq_toMeromorphicSectionSheaf_tmul_chartRatio B S hS Z.subspace.toFunctor Z.closed.1
      (Z.restrictModule B S hS hX L) (Z.baseChangeChart B S hS hX V)
      (Z.baseChangeChartGenerator B S hS hX L V e)
      (Z.baseChangeChartGenerator_compat B S hS hX L V e hcompat)
      (Z.bijective_smul_baseChangeChartGenerator B S hS hX L hL V e hcompat hfree) σ)
  have h2 := eval_eq_toMeromorphicSectionSheaf_tmul_restrict B S hS
    (Z.genericFieldSpace B S hS hX hdec).1 (Z.genericFieldSpace B S hS hX hdec).2
    ((modulePullback B S hS (Z.genericFieldMorphism B S hS hX hdec)).obj
      (Z.restrictModule B S hS hX L))
    (pullbackMeromorphicSection B S hS (Z.genericFieldMorphism B S hS hX hdec)
      (Z.restrictModule B S hS hX L)
      (Z.pullbacksMeromorphicSections_genericFieldMorphism B S hS hX hdec) σ)
    (Z.genericFieldChart B S hS hX hdec) (Z.genericFieldGenerator B S hS hX hdec L hL)
    (Z.genericFieldGenerator_compat B S hS hX hdec L hL) _
    (Z.genericFieldValue_spec B S hS hX hdec L hL σ)
    P
    (chartToIdEtaleChart B S hS _)
  refine (mul_comm _ _).trans ((Z.bijective_genericFieldTmul B S hS hX hdec L hL _
    (chartToIdEtaleChart B S hS _)).1 (Eq.trans ?_ h2))
  refine Eq.trans ?_ h1.symm
  refine congrArg (toMeromorphicSectionSheaf B S hS (Z.genericFieldSpace B S hS hX hdec).1
    (Z.genericFieldSpace B S hS hX hdec).2
    ((modulePullback B S hS (Z.genericFieldMorphism B S hS hX hdec)).obj
      (Z.restrictModule B S hS hX L))
    P) ?_
  refine Eq.trans ?_ (chartPullbackMeromorphicSectionsSheaf_tmul B S hS
    (Z.genericFieldMorphism B S hS hX hdec) (Z.restrictModule B S hS hX L)
    (Z.pullbacksMeromorphicSections_genericFieldMorphism B S hS hX hdec)
    (Z.genericFieldChartDiagram B S hS hX hdec V P g hg) _ _).symm
  refine Eq.trans (meromorphicSectionModule_tmul_smul B S hS
    (Z.genericFieldSpace B S hS hX hdec).1 (Z.genericFieldSpace B S hS hX hdec).2
    ((modulePullback B S hS (Z.genericFieldMorphism B S hS hX hdec)).obj
      (Z.restrictModule B S hS hX L))
    P _ _ _).symm ?_
  exact congrArg (fun z ↦ _ ⊗ₜ[chartRing B S hS (Z.genericFieldSpace B S hS hX hdec).1
      (Z.genericFieldSpace B S hS hX hdec).2
      P] z)
    (Z.modulePullbackChartFMap_baseChangeChartGenerator_eq_genericFieldChartRatio_smul
      B S hS hX hdec L hL V e P g hg).symm

/-- **The comparison on `P` cleared of denominators.**  If the coefficient `c` of `σ` against
`e|_Z` over `W'` is `c₁ / c₂`, then on `P` the pullback of `c₁` times `w` is the value of `σ`
times the pullback of `c₂`, as regular functions. -/
theorem PrimeDivisor.chartDiagramRestrict_mul_genericFieldChartRatio
    (σ : MeromorphicSection.{u, u} B S hS Z.subspace.toFunctor Z.closed.1
      (Z.restrictModule B S hS hX L))
    (c₁ c₂ : (structurePresheaf B S hS (Z.space B S hS).1).obj
      (op (Z.baseChangeChart B S hS hX V)))
    (hc : Z.baseChangeChartSectionCoefficient B S hS hX L hL V e hcompat hfree σ *
        chartToMeromorphic (X := Z.space B S hS) (Z.baseChangeChart B S hS hX V) c₂ =
      chartToMeromorphic (X := Z.space B S hS) (Z.baseChangeChart B S hS hX V) c₁) :
    chartDiagramRestrict B S hS (Z.genericFieldMorphism B S hS hX hdec)
        (Z.genericFieldChartDiagram B S hS hX hdec V P g hg) c₁ *
      Z.genericFieldChartRatio B S hS hX hdec L hL V e P g hg =
      (show chartRing B S hS (Z.genericFieldSpace B S hS hX hdec).1
          (Z.genericFieldSpace B S hS hX hdec).2
          P from
        ((structurePresheaf B S hS (Z.genericFieldSpace B S hS hX hdec).1).map
          (chartToIdEtaleChart B S hS
            P).op).hom
          ((Scheme.ΓSpecIso (CommRingCat.of (Z.genericResidueField B S hS hX hdec))).inv.hom
            (Z.genericFieldValue B S hS hX hdec L hL σ))) *
        chartDiagramRestrict B S hS (Z.genericFieldMorphism B S hS hX hdec)
          (Z.genericFieldChartDiagram B S hS hX hdec V P g hg) c₂ := by
  have hpb := fun r ↦ RingHom.congr_fun (chartMeromorphicFunctionPullback_algebraMap B S hS
    (Z.genericFieldMorphism B S hS hX hdec)
    (Z.pullbacksMeromorphicSections_genericFieldMorphism B S hS hX hdec)
    (Z.genericFieldChartDiagram B S hS hX hdec V P g hg)) r
  have hA := Z.chartMeromorphicPullbackHom_mul_genericFieldChartRatio B S hS hX hdec L hL V e
    hcompat hfree P g hg σ
  have hnat := chartToMeromorphic_naturality (X := Z.genericFieldSpace B S hS hX hdec)
    (chartToIdEtaleChart B S hS
      P)
    ((Scheme.ΓSpecIso (CommRingCat.of (Z.genericResidueField B S hS hX hdec))).inv.hom
      (Z.genericFieldValue B S hS hX hdec L hL σ))
  apply injective_toMeromorphicFunctionSheaf B S hS (Z.genericFieldSpace B S hS hX hdec).1
    (Z.genericFieldSpace B S hS hX hdec).2
    P
  refine (map_mul _ _ _).trans (Eq.trans ?_ (map_mul _ _ _).symm)
  have h1 := (hpb c₁).symm
  have h2 := (hpb c₂).symm
  have hc' := (RingHom.map_mul (chartMeromorphicPullbackHom B S hS
      (Z.genericFieldMorphism B S hS hX hdec)
      (Z.pullbacksMeromorphicSections_genericFieldMorphism B S hS hX hdec)
      (Z.genericFieldChartDiagram B S hS hX hdec V P g hg)) _ _).symm.trans
    (congrArg (chartMeromorphicPullbackHom B S hS (Z.genericFieldMorphism B S hS hX hdec)
      (Z.pullbacksMeromorphicSections_genericFieldMorphism B S hS hX hdec)
      (Z.genericFieldChartDiagram B S hS hX hdec V P g hg)) hc)
  have aux : ∀ {R : Type u} [CommRing R] {x₁ x₂ y c w v : R}, x₁ = c * y → x₂ = y →
      c * w = v → x₁ * w = v * x₂ := by
    intro R _ x₁ x₂ y c w v h₁ h₂ h₃
    rw [h₁, h₂, ← h₃, mul_right_comm]
  exact aux (h1.trans hc'.symm) h2 (hA.trans hnat.symm)

end AlgebraicGeometry.Space

end
