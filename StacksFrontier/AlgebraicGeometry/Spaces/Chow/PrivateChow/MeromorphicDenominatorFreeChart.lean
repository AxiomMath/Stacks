module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChow.MeromorphicDenominatorIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionSheafGenerator

/-!
# The ideal of denominators over a chart trivializing the module

Over an étale chart `V` on which the invertible module `ℒ` is free on a generator `e`, a
meromorphic section is `t = c · e` with `c = t / e ∈ 𝒦_X(V)` its chart ratio, and the ideal of
denominators of `t` over `V` is `{a : a c ∈ 𝒪_X(V)}`; the numerator of a denominator `a` is
`y · e` with `y = a c`.

## Main results

* `AlgebraicGeometry.Space.isMeromorphicDenominator_iff_of_free`.
* `AlgebraicGeometry.Space.meromorphicDenominatorNumerator_eq_smul_of_free`.
-/

@[expose] public section

open CategoryTheory Opposite TensorProduct

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] chartMeromorphicAlgebra
attribute [local instance] meromorphicSectionModuleRingedSiteModule

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : AlgebraicSpaces B S hS) (L : Modules.{u, u} B S hS X.1 X.2)
  (t : MeromorphicSection.{u, u} B S hS X.1 X.2 L) (V : SmallEtale B S hS X.1)
  (e : (W : SmallEtale B S hS X.1) → (W ⟶ V) → L.val.obj (op W))
  (hcompat : ∀ (W W' : SmallEtale B S hS X.1) (k : W ⟶ V) (g : W' ⟶ W),
    (L.val.map g.op).hom (e W k) = e W' (g ≫ k))
  (hfree : ∀ (W : SmallEtale B S hS X.1) (k : W ⟶ V),
    Function.Bijective fun r : chartRing B S hS X.1 X.2 W ↦ r • e W k)

/-- The meromorphic value of a multiple of the generator. -/
theorem toMeromorphicSectionValue_smul_generator (y : chartRing B S hS X.1 X.2 V) :
    toMeromorphicSectionValue B S hS X.1 X.2 L V (y • e V (𝟙 V)) =
      toMeromorphicSectionSheaf B S hS X.1 X.2 L V
        (chartMeromorphicScalar B S hS X V y ⊗ₜ[chartRing B S hS X.1 X.2 V] e V (𝟙 V) :
          (meromorphicSectionModule B S hS X.1 X.2 L).obj (op V)) := by
  rw [toMeromorphicSectionValue_eq, pureMeromorphicSection_smul_eq_algebraMap_tmul]
  rfl

/-- A multiple of `t` over the chart, through the chart ratio. -/
theorem chartMeromorphicScalar_smul_eval_eq (a : chartRing B S hS X.1 X.2 V) :
    chartMeromorphicScalar B S hS X V a • t.eval (op V) =
      toMeromorphicSectionSheaf B S hS X.1 X.2 L V
        ((chartMeromorphicScalar B S hS X V a * chartRatio B S hS X.1 X.2 L V e hcompat hfree t)
          ⊗ₜ[chartRing B S hS X.1 X.2 V] e V (𝟙 V) :
          (meromorphicSectionModule B S hS X.1 X.2 L).obj (op V)) := by
  rw [eval_eq_toMeromorphicSectionSheaf_tmul_chartRatio B S hS X.1 X.2 L V e hcompat hfree t]
  refine (toMeromorphicSectionSheaf_smul B S hS X.1 X.2 L V _ _).symm.trans ?_
  congr 1

/-- **The ideal of denominators over a trivializing chart**: `a` is a denominator of `t` exactly
when `a c` is a regular function, `c` the chart ratio. -/
theorem isMeromorphicDenominator_iff_of_free (a : chartRing B S hS X.1 X.2 V) :
    IsMeromorphicDenominator B S hS X L t V a ↔
      ∃ y : chartRing B S hS X.1 X.2 V, chartMeromorphicScalar B S hS X V y =
        chartMeromorphicScalar B S hS X V a * chartRatio B S hS X.1 X.2 L V e hcompat hfree t := by
  have hinj := (bijective_toMeromorphicSectionSheaf_tmul B S hS X.1 X.2 L V e hcompat hfree).1
  constructor
  · rintro ⟨m, hm⟩
    obtain ⟨y, rfl⟩ := (hfree V (𝟙 V)).2 m
    refine ⟨y, hinj ?_⟩
    dsimp only
    rwa [← toMeromorphicSectionValue_smul_generator, ← chartMeromorphicScalar_smul_eval_eq]
  · rintro ⟨y, hy⟩
    refine ⟨y • e V (𝟙 V), ?_⟩
    rw [toMeromorphicSectionValue_smul_generator, chartMeromorphicScalar_smul_eval_eq, hy]

variable (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (structureCommRings B S hS X)
  (structureRingSheaf B S hS X).property L)

include hL in
/-- **The numerator of a denominator over a trivializing chart**: if `y = a c` then
`a · t = y · e`. -/
theorem meromorphicDenominatorNumerator_eq_smul_of_free {a : chartRing B S hS X.1 X.2 V}
    (ha : IsMeromorphicDenominator B S hS X L t V a) {y : chartRing B S hS X.1 X.2 V}
    (hy : chartMeromorphicScalar B S hS X V y =
      chartMeromorphicScalar B S hS X V a * chartRatio B S hS X.1 X.2 L V e hcompat hfree t) :
    meromorphicDenominatorNumerator B S hS X L t ha = y • e V (𝟙 V) :=
  (eq_meromorphicDenominatorNumerator B S hS X L t hL ha (by
    rw [toMeromorphicSectionValue_smul_generator, chartMeromorphicScalar_smul_eval_eq, hy])).symm

end AlgebraicGeometry.Space

end
