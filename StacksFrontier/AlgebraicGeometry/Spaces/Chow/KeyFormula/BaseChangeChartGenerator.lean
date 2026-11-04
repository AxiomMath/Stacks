module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormula.GenericFieldValue
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaLocal.PrimeDivisorChart
public import StacksFrontier.AlgebraicGeometry.Spaces.FreeGeneratorSieveDescent

/-!
# A free generator of `ℒ` over a chart restricts to a free generator of `ℒ|_Z`

Let `X` be an algebraic space, `Z ⊂ X` a prime divisor, `ℒ` an invertible `𝒪_X`-module and `W` an
étale chart of `X` over which `ℒ` is free on a compatible family `e` (the idiom of
`AlgebraicGeometry.Space.chartRatio`). The base change `W ×_X Z` is an étale chart of `Z`
(`AlgebraicGeometry.Space.PrimeDivisor.baseChangeChart`). This file restricts `e` to a
compatible family of free generators of the restriction `ℒ|_Z` over the charts of `Z` over
`W ×_X Z`: over such a chart `W'` it is the inverse image of `e` along the square
`(W', W)` over the closed immersion `Z → X`.

Freeness is local: the inverse image of a free generator is a free generator over a covering
sieve (`AlgebraicGeometry.Space.exists_sieve_bijective_smul_modulePullbackChartSection`), and
free generation descends along covering sieves
(`AlgebraicGeometry.Space.bijective_smul_of_sieve`), so no refinement of `W ×_X Z` is needed.

## Main definitions

* `AlgebraicGeometry.Space.PrimeDivisor.baseChangeChartGeneratorDiagram`: the square `(W', W)`.
* `AlgebraicGeometry.Space.PrimeDivisor.baseChangeChartGenerator`: the restricted family.

## Main results

* `AlgebraicGeometry.Space.PrimeDivisor.baseChangeChartGenerator_compat`: it is compatible with
  restriction.
* `AlgebraicGeometry.Space.PrimeDivisor.bijective_smul_baseChangeChartGenerator`: it freely
  generates `ℒ|_Z` over every chart over `W ×_X Z`.

## References

* [Stacks Project, Tag 0EQV](https://stacks.math.columbia.edu/tag/0EQV)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (Z : PrimeDivisor B S hS X) (L : Modules.{u, u} B S hS X hX)
    (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L) (W : SmallEtale B S hS X)
    (e : (W' : SmallEtale B S hS X) → (W' ⟶ W) → L.val.obj (op W'))
    (hcompat : ∀ (W₁ W₂ : SmallEtale B S hS X) (k : W₁ ⟶ W) (g : W₂ ⟶ W₁),
      (L.val.map g.op).hom (e W₁ k) = e W₂ (g ≫ k))
    (hfree : ∀ (W₁ : SmallEtale B S hS X) (k : W₁ ⟶ W),
      Function.Bijective fun r : chartRing B S hS X hX W₁ ↦ r • e W₁ k)

/-- **The square `(W', W)` over the closed immersion `Z → X`** for a chart `W'` of `Z` over the
base change `W ×_X Z`. -/
def PrimeDivisor.baseChangeChartGeneratorDiagram {W' : SmallEtale B S hS Z.subspace.toFunctor}
    (k : W' ⟶ Z.baseChangeChart B S hS hX W) :
    ChartDiagram B S hS Z.subspace.toFunctor X (Z.inclusionHom B S hS hX).hom where
  U := W'
  V := W
  g := (SmallEtale.toOver B S hS Z.subspace.toFunctor).map k ≫
    (Z.baseChangeChartDiagram B S hS hX W).g
  comm := by
    change W'.obj.hom ≫ (Z.inclusionHom B S hS hX).hom =
      yoneda.map ((SmallEtale.toOver B S hS Z.subspace.toFunctor).map k ≫
        (Z.baseChangeChartDiagram B S hS hX W).g) ≫ W.obj.hom
    refine (congrArg (· ≫ (Z.inclusionHom B S hS hX).hom) (CostructuredArrow.w k.hom).symm).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (yoneda.map ((SmallEtale.toOver B S hS Z.subspace.toFunctor).map k) ≫ ·)
      (Z.baseChangeChartDiagram B S hS hX W).comm).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    exact congrArg (· ≫ W.obj.hom) (yoneda.map_comp _ _).symm

/-- **The restriction of the free family `e` to `ℒ|_Z`** over the charts of `Z` over
`W ×_X Z`: the inverse image of `e` along the square `(W', W)`. -/
def PrimeDivisor.baseChangeChartGenerator (W' : SmallEtale B S hS Z.subspace.toFunctor)
    (k : W' ⟶ Z.baseChangeChart B S hS hX W) :
    (Z.restrictModule B S hS hX L).val.obj (op W') :=
  (modulePullbackChartFMap B S hS (Z.inclusionHom B S hS hX) L).app
    (Z.baseChangeChartGeneratorDiagram B S hS hX W k) (e W (𝟙 W))

include hcompat in
/-- The restricted family is compatible with restriction. -/
theorem PrimeDivisor.baseChangeChartGenerator_compat
    (W₁ W₂ : SmallEtale B S hS Z.subspace.toFunctor)
    (k : W₁ ⟶ Z.baseChangeChart B S hS hX W) (g : W₂ ⟶ W₁) :
    ((Z.restrictModule B S hS hX L).val.map g.op).hom
        (Z.baseChangeChartGenerator B S hS hX L W e W₁ k) =
      Z.baseChangeChartGenerator B S hS hX L W e W₂ (g ≫ k) := by
  have hsq : (SmallEtale.toOver B S hS Z.subspace.toFunctor).map g ≫
      (Z.baseChangeChartGeneratorDiagram B S hS hX W k).g =
      (Z.baseChangeChartGeneratorDiagram B S hS hX W (g ≫ k)).g ≫
        (SmallEtale.toOver B S hS X).map (𝟙 W) :=
    ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ (Z.baseChangeChartDiagram B S hS hX W).g)
      ((SmallEtale.toOver B S hS Z.subspace.toFunctor).map_comp g k).symm)).trans
      ((Category.comp_id _).symm.trans (congrArg (_ ≫ ·)
        ((SmallEtale.toOver B S hS X).map_id W).symm))
  have h1 : (modulePullbackChartFMap B S hS (Z.inclusionHom B S hS hX) L).app
        (Z.baseChangeChartGeneratorDiagram B S hS hX W (g ≫ k))
        ((L.val.map (𝟙 W).op).hom (e W (𝟙 W))) =
      ((Z.restrictModule B S hS hX L).val.map g.op).hom
        ((modulePullbackChartFMap B S hS (Z.inclusionHom B S hS hX) L).app
          (Z.baseChangeChartGeneratorDiagram B S hS hX W k) (e W (𝟙 W))) :=
    (modulePullbackChartFMap B S hS (Z.inclusionHom B S hS hX) L).naturality
      (Z.baseChangeChartGeneratorDiagram B S hS hX W k)
      (Z.baseChangeChartGeneratorDiagram B S hS hX W (g ≫ k)) g (𝟙 W) hsq (e W (𝟙 W))
  have h2 : (L.val.map (𝟙 W).op).hom (e W (𝟙 W)) = e W (𝟙 W) :=
    (hcompat W W (𝟙 W) (𝟙 W)).trans (congrArg (e W) (Category.id_comp _))
  rw [h2] at h1
  unfold PrimeDivisor.baseChangeChartGenerator
  rw [← h1]

include hcompat hfree hL in
/-- **The restricted family freely generates `ℒ|_Z`** over every chart over `W ×_X Z`. -/
theorem PrimeDivisor.bijective_smul_baseChangeChartGenerator
    (W₁ : SmallEtale B S hS Z.subspace.toFunctor) (k : W₁ ⟶ Z.baseChangeChart B S hS hX W) :
    Function.Bijective fun r : chartRing B S hS Z.subspace.toFunctor Z.closed.1 W₁ ↦
      r • Z.baseChangeChartGenerator B S hS hX L W e W₁ k := by
  obtain ⟨T, hT, hloc⟩ := exists_sieve_bijective_smul_modulePullbackChartSection B S hS
    (Z.inclusionHom B S hS hX) L
    (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hL)
    (Z.baseChangeChartGeneratorDiagram B S hS hX W k) e hcompat hfree
  refine bijective_smul_of_sieve B S hS (Z.space B S hS) (Z.restrictModule B S hS hX L) W₁ _ T hT
    fun W₂ ι hι => ?_
  have hEq : (chartRestrictLinear (Z.restrictModule B S hS hX L) ι)
      (Z.baseChangeChartGenerator B S hS hX L W e W₁ k) =
      modulePullbackChartSectionRestrict B S hS (Z.inclusionHom B S hS hX) L
        (Z.baseChangeChartGeneratorDiagram B S hS hX W k) (e W (𝟙 W)) (𝟙 W₂ ≫ ι) := by
    unfold modulePullbackChartSectionRestrict
    simp only
    rfl
  rw [hEq]
  exact hloc ι hι W₂ (𝟙 W₂)

end AlgebraicGeometry.Space

end
