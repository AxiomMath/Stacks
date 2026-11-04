module

public import StacksFrontier.AlgebraicGeometry.NaiveCotangentDeterminant.Sheaf

/-!
# Base change of `det(NL_{Y/X})`

Consider a commutative square of schemes

```
Y' --b--> Y
|f'       |f
X' --a--> X
```

(`w : b ≫ f = f' ≫ a`) with `f` and `f'` syntomic. For a chart `(U, V)` of `f` and a chart
`(U', V')` of `f'` with `U' ⊆ a⁻¹U` and `V' ⊆ b⁻¹V` the restriction maps form a commutative square
of rings `Γ(X, U) → Γ(X', U')`, `Γ(Y, V) → Γ(Y', V')`; when it is good for the naive cotangent
complex it carries the base change map `det(NL_{Γ(V)/Γ(U)}) → det(NL_{Γ(V')/Γ(U')})`
(`NaiveCotangent.detNLMap`). This file proves that these maps are compatible with the
restriction maps of the two determinant sheaves on both sides.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.detNLSquareMap`: the base change map along a good square of
  charts.
* `AlgebraicGeometry.Scheme.Hom.ChartOver`: a chart of `f'` lies over a chart of `f` when its
  opens map into those of the chart of `f` and the square of rings is good.

## Main results

* `AlgebraicGeometry.Scheme.Hom.detNLSquareMap_detNLChartRestrict` and
  `AlgebraicGeometry.Scheme.Hom.detNLChartRestrict_detNLSquareMap`: compatibility with the
  restriction maps on the source and on the target.
* `AlgebraicGeometry.Scheme.Hom.isBaseChangeAlong_detNLSquareMap`: the base change map
  identifies `det(NL_{Γ(V')/Γ(U')})` with `Γ(Y', V') ⊗_{Γ(Y, V)} det(NL_{Γ(V)/Γ(U)})`.
* `AlgebraicGeometry.Scheme.Hom.ChartOver.map_detNLChartRestrict`: the base change maps along
  charts lying over charts form a morphism of chart module systems.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y X' Y' : Scheme.{u}} {f : Y ⟶ X} {f' : Y' ⟶ X'} {a : X' ⟶ X} {b : Y' ⟶ Y}
  (w : b ≫ f = f' ≫ a) (hf : Syntomic f) (hf' : Syntomic f')

/-- **The base change map `det(NL_{Γ(V)/Γ(U)}) → det(NL_{Γ(V')/Γ(U')})`** along a good square of
charts over the commutative square `b ≫ f = f' ≫ a`, semilinear along `Γ(Y, V) → Γ(Y', V')`. -/
def detNLSquareMap (c : f.chartIndex.ι) (c' : f'.chartIndex.ι) (hU : c'.1.1.1 ≤ a ⁻¹ᵁ c.1.1.1)
    (hV : c'.1.2.1 ≤ b ⁻¹ᵁ c.1.2.1) (hsq : f.IsGoodChartSquare w c.2 c'.2 hU hV) :
    f.detNLChart hf c →ₛₗ[(b.appLE c.1.2.1 c'.1.2.1 hV).hom] f'.detNLChart hf' c' :=
  letI := f.chartAlgebra c.2
  letI := f'.chartAlgebra c'.2
  letI := a.chartAlgebra hU
  letI := b.chartAlgebra hV
  letI := squareAlgebra f' a hU c'.2
  haveI := isScalarTower_squareAlgebra_left hU c'.2
  haveI := f.isScalarTower_squareAlgebra_right w c.2 hU hV c'.2
  haveI := f.syntomic_chartAlgebra hf c.1.1 c.1.2 c.2
  haveI := f'.syntomic_chartAlgebra hf' c'.1.1 c'.1.2 c'.2
  NaiveCotangent.detNLMap hsq

section Refine

variable (c c₁ : f.chartIndex.ι) (c₁' : f'.chartIndex.ι) (hc : f.chartIndex.Refines c₁ c)
  (hU₁ : c₁'.1.1.1 ≤ a ⁻¹ᵁ c₁.1.1.1) (hV₁ : c₁'.1.2.1 ≤ b ⁻¹ᵁ c₁.1.2.1)

/-- Restricting to a refinement on the source and then base changing along a good square is base
changing along a good composite square. -/
private theorem exists_isGoodChartSquare_detNLSquareMap_detNLChartRestrict
    (hsq₁ : f.IsGoodChartSquare w c₁.2 c₁'.2 hU₁ hV₁) :
    ∃ hsq₃ : f.IsGoodChartSquare w c.2 c₁'.2 (hU₁.trans (a.preimage_mono hc.1.le))
      (hV₁.trans (b.preimage_mono hc.2.le)),
      ∀ x : f.detNLChart hf c,
        detNLSquareMap w hf hf' c₁ c₁' hU₁ hV₁ hsq₁ (f.detNLChartRestrict hf hc x) =
          detNLSquareMap w hf hf' c c₁' _ _ hsq₃ x := by
  let := f.chartAlgebra c.2
  let := f.chartAlgebra c₁.2
  let := f'.chartAlgebra c₁'.2
  let := X.restrictAlgebra hc.1.le
  let := Y.restrictAlgebra hc.2.le
  let := f.chartAlgebra (hc.2.le.trans c.2)
  let := a.chartAlgebra hU₁
  let := b.chartAlgebra hV₁
  let := squareAlgebra f' a hU₁ c₁'.2
  let := a.chartAlgebra (hU₁.trans (a.preimage_mono hc.1.le))
  let := b.chartAlgebra (hV₁.trans (b.preimage_mono hc.2.le))
  let := squareAlgebra f' a (hU₁.trans (a.preimage_mono hc.1.le)) c₁'.2
  have := f.isScalarTower_chartAlgebra_restrict c.2 c₁.2 hc.1.le hc.2.le
  have := f.isScalarTower_restrict_chartAlgebra c.2 hc.2.le
  have := isScalarTower_squareAlgebra_left hU₁ c₁'.2
  have := f.isScalarTower_squareAlgebra_right w c₁.2 hU₁ hV₁ c₁'.2
  have := isScalarTower_squareAlgebra_left (hU₁.trans (a.preimage_mono hc.1.le)) c₁'.2
  have := f.isScalarTower_squareAlgebra_right w c.2 (hU₁.trans (a.preimage_mono hc.1.le))
    (hV₁.trans (b.preimage_mono hc.2.le)) c₁'.2
  have : IsScalarTower Γ(X, c.1.1.1) Γ(X, c₁.1.1.1) Γ(X', c₁'.1.1.1) :=
    .of_algebraMap_eq fun x => by
      simp only [RingHom.algebraMap_toAlgebra, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
  have : IsScalarTower Γ(Y, c.1.2.1) Γ(Y, c₁.1.2.1) Γ(Y', c₁'.1.2.1) :=
    .of_algebraMap_eq fun x => by
      simp only [RingHom.algebraMap_toAlgebra, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
  have := f.syntomic_chartAlgebra hf c.1.1 c.1.2 c.2
  have := f.syntomic_chartAlgebra hf c₁.1.1 c₁.1.2 c₁.2
  have := f'.syntomic_chartAlgebra hf' c₁'.1.1 c₁'.1.2 c₁'.2
  have hsq₂ := f.isGoodSquare_of_isBasicOpenOf c.2 c₁.2 hc.1 hc.2
  have hsq₃ := NaiveCotangent.IsGoodSquare.trans hsq₂ hsq₁
  exact ⟨hsq₃, fun x => NaiveCotangent.detNLMap_detNLMap hsq₂ hsq₁ hsq₃ x⟩

include hf hf' in
/-- A good square of charts preceded by a refinement on the source is good. -/
theorem isGoodChartSquare_of_refines_left (hsq₁ : f.IsGoodChartSquare w c₁.2 c₁'.2 hU₁ hV₁) :
    f.IsGoodChartSquare w c.2 c₁'.2 (hU₁.trans (a.preimage_mono hc.1.le))
      (hV₁.trans (b.preimage_mono hc.2.le)) :=
  (exists_isGoodChartSquare_detNLSquareMap_detNLChartRestrict w hf hf' c c₁ c₁' hc hU₁ hV₁
    hsq₁).1

/-- **The base change maps are compatible with the restriction maps of `det(NL_{Y/X})`**:
restricting to a refinement `c₁` of `c` and then base changing along a good square from `c₁` to
`c₁'` is base changing along the composite square. -/
theorem detNLSquareMap_detNLChartRestrict (hsq₁ : f.IsGoodChartSquare w c₁.2 c₁'.2 hU₁ hV₁)
    (hsq₃ : f.IsGoodChartSquare w c.2 c₁'.2 (hU₁.trans (a.preimage_mono hc.1.le))
      (hV₁.trans (b.preimage_mono hc.2.le))) (x : f.detNLChart hf c) :
    detNLSquareMap w hf hf' c₁ c₁' hU₁ hV₁ hsq₁ (f.detNLChartRestrict hf hc x) =
      detNLSquareMap w hf hf' c c₁' _ _ hsq₃ x :=
  (exists_isGoodChartSquare_detNLSquareMap_detNLChartRestrict w hf hf' c c₁ c₁' hc hU₁ hV₁
    hsq₁).2 x

end Refine

section RefineTarget

variable (c : f.chartIndex.ι) (c' c₁' : f'.chartIndex.ι) (hc' : f'.chartIndex.Refines c₁' c')
  (hU : c'.1.1.1 ≤ a ⁻¹ᵁ c.1.1.1) (hV : c'.1.2.1 ≤ b ⁻¹ᵁ c.1.2.1)

/-- Base changing along a good square and then restricting to a refinement on the target is base
changing along a good composite square. -/
private theorem exists_isGoodChartSquare_detNLChartRestrict_detNLSquareMap
    (hsq : f.IsGoodChartSquare w c.2 c'.2 hU hV) :
    ∃ hsq₃ : f.IsGoodChartSquare w c.2 c₁'.2 (hc'.1.le.trans hU) (hc'.2.le.trans hV),
      ∀ x : f.detNLChart hf c,
        f'.detNLChartRestrict hf' hc' (detNLSquareMap w hf hf' c c' hU hV hsq x) =
          detNLSquareMap w hf hf' c c₁' _ _ hsq₃ x := by
  let := f.chartAlgebra c.2
  let := f'.chartAlgebra c'.2
  let := f'.chartAlgebra c₁'.2
  let := a.chartAlgebra hU
  let := b.chartAlgebra hV
  let := squareAlgebra f' a hU c'.2
  let := X'.restrictAlgebra hc'.1.le
  let := Y'.restrictAlgebra hc'.2.le
  let := f'.chartAlgebra (hc'.2.le.trans c'.2)
  let := a.chartAlgebra (hc'.1.le.trans hU)
  let := b.chartAlgebra (hc'.2.le.trans hV)
  let := squareAlgebra f' a (hc'.1.le.trans hU) c₁'.2
  have := isScalarTower_squareAlgebra_left hU c'.2
  have := f.isScalarTower_squareAlgebra_right w c.2 hU hV c'.2
  have := f'.isScalarTower_chartAlgebra_restrict c'.2 c₁'.2 hc'.1.le hc'.2.le
  have := f'.isScalarTower_restrict_chartAlgebra c'.2 hc'.2.le
  have := isScalarTower_squareAlgebra_left (hc'.1.le.trans hU) c₁'.2
  have := f.isScalarTower_squareAlgebra_right w c.2 (hc'.1.le.trans hU) (hc'.2.le.trans hV)
    c₁'.2
  have : IsScalarTower Γ(X, c.1.1.1) Γ(X', c'.1.1.1) Γ(X', c₁'.1.1.1) :=
    .of_algebraMap_eq fun x => by
      simp only [RingHom.algebraMap_toAlgebra, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
  have : IsScalarTower Γ(Y, c.1.2.1) Γ(Y', c'.1.2.1) Γ(Y', c₁'.1.2.1) :=
    .of_algebraMap_eq fun x => by
      simp only [RingHom.algebraMap_toAlgebra, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
  have := f.syntomic_chartAlgebra hf c.1.1 c.1.2 c.2
  have := f'.syntomic_chartAlgebra hf' c'.1.1 c'.1.2 c'.2
  have := f'.syntomic_chartAlgebra hf' c₁'.1.1 c₁'.1.2 c₁'.2
  have hsq₂ := f'.isGoodSquare_of_isBasicOpenOf c'.2 c₁'.2 hc'.1 hc'.2
  have hsq₃ := NaiveCotangent.IsGoodSquare.trans hsq hsq₂
  exact ⟨hsq₃, fun x => NaiveCotangent.detNLMap_detNLMap hsq hsq₂ hsq₃ x⟩

include hf hf' in
/-- A good square of charts followed by a refinement on the target is good. -/
theorem isGoodChartSquare_of_refines_right (hsq : f.IsGoodChartSquare w c.2 c'.2 hU hV) :
    f.IsGoodChartSquare w c.2 c₁'.2 (hc'.1.le.trans hU) (hc'.2.le.trans hV) :=
  (exists_isGoodChartSquare_detNLChartRestrict_detNLSquareMap w hf hf' c c' c₁' hc' hU hV hsq).1

/-- **The base change maps are compatible with the restriction maps of `det(NL_{Y'/X'})`**:
base changing along a good square from `c` to `c'` and then restricting to a refinement `c₁'` of
`c'` is base changing along the composite square. -/
theorem detNLChartRestrict_detNLSquareMap (hsq : f.IsGoodChartSquare w c.2 c'.2 hU hV)
    (hsq₃ : f.IsGoodChartSquare w c.2 c₁'.2 (hc'.1.le.trans hU) (hc'.2.le.trans hV))
    (x : f.detNLChart hf c) :
    f'.detNLChartRestrict hf' hc' (detNLSquareMap w hf hf' c c' hU hV hsq x) =
      detNLSquareMap w hf hf' c c₁' _ _ hsq₃ x :=
  (exists_isGoodChartSquare_detNLChartRestrict_detNLSquareMap w hf hf' c c' c₁' hc' hU hV
    hsq).2 x

end RefineTarget


/-- The base change map along a good square of charts exhibits `det(NL_{Γ(V')/Γ(U')})` as the
base change `Γ(Y', V') ⊗_{Γ(Y, V)} det(NL_{Γ(V)/Γ(U)})`. -/
theorem isBaseChangeAlong_detNLSquareMap (c : f.chartIndex.ι) (c' : f'.chartIndex.ι)
    (hU : c'.1.1.1 ≤ a ⁻¹ᵁ c.1.1.1) (hV : c'.1.2.1 ≤ b ⁻¹ᵁ c.1.2.1)
    (hsq : f.IsGoodChartSquare w c.2 c'.2 hU hV) :
    (detNLSquareMap w hf hf' c c' hU hV hsq).IsBaseChangeAlong := by
  let := f.chartAlgebra c.2
  let := f'.chartAlgebra c'.2
  let := a.chartAlgebra hU
  let := b.chartAlgebra hV
  let := squareAlgebra f' a hU c'.2
  have := isScalarTower_squareAlgebra_left hU c'.2
  have := f.isScalarTower_squareAlgebra_right w c.2 hU hV c'.2
  have := f.syntomic_chartAlgebra hf c.1.1 c.1.2 c.2
  have := f'.syntomic_chartAlgebra hf' c'.1.1 c'.1.2 c'.2
  let : Module Γ(Y, c.1.2.1) (f'.detNLChart hf' c') :=
    Module.compHom _ (b.appLE c.1.2.1 c'.1.2.1 hV).hom
  have : IsScalarTower Γ(Y, c.1.2.1) Γ(Y', c'.1.2.1) (f'.detNLChart hf' c') :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  exact IsBaseChange.of_equiv (NaiveCotangent.detNLBaseChangeLinearEquiv hsq)
    (NaiveCotangent.detNLBaseChangeLinearEquiv_one_tmul _)

/-- The base change map along a good square of charts of locally quasi-finite syntomic morphisms
carries `δ(NL_{Γ(V)/Γ(U)})` to `δ(NL_{Γ(V')/Γ(U')})`. -/
theorem detNLSquareMap_deltaNLChart [LocallyQuasiFinite f] [LocallyQuasiFinite f']
    (c : f.chartIndex.ι) (c' : f'.chartIndex.ι) (hU : c'.1.1.1 ≤ a ⁻¹ᵁ c.1.1.1)
    (hV : c'.1.2.1 ≤ b ⁻¹ᵁ c.1.2.1) (hsq : f.IsGoodChartSquare w c.2 c'.2 hU hV) :
    detNLSquareMap w hf hf' c c' hU hV hsq (f.deltaNLChart hf c) = f'.deltaNLChart hf' c' := by
  let := f.chartAlgebra c.2
  let := f'.chartAlgebra c'.2
  let := a.chartAlgebra hU
  let := b.chartAlgebra hV
  let := squareAlgebra f' a hU c'.2
  have := isScalarTower_squareAlgebra_left hU c'.2
  have := f.isScalarTower_squareAlgebra_right w c.2 hU hV c'.2
  have := f.syntomic_chartAlgebra hf c.1.1 c.1.2 c.2
  have := f'.syntomic_chartAlgebra hf' c'.1.1 c'.1.2 c'.2
  have := f.quasiFinite_chartAlgebra inferInstance c.1.1 c.1.2 c.2
  have := f'.quasiFinite_chartAlgebra inferInstance c'.1.1 c'.1.2 c'.2
  exact NaiveCotangent.detNLMap_deltaNL hsq

/-! ### Charts lying over charts -/

/-- A chart `c'` of `f'` *lies over* a chart `c` of `f` along the square `b ≫ f = f' ≫ a` when
`U' ⊆ a⁻¹U`, `V' ⊆ b⁻¹V` and the square of rings of the two charts is good. -/
def ChartOver (c' : f'.chartIndex.ι) (c : f.chartIndex.ι) : Prop :=
  ∃ (hU : c'.1.1.1 ≤ a ⁻¹ᵁ c.1.1.1) (hV : c'.1.2.1 ≤ b ⁻¹ᵁ c.1.2.1),
    f.IsGoodChartSquare w c.2 c'.2 hU hV

/-- The base change map along a chart lying over a chart. -/
abbrev ChartOver.map {c' : f'.chartIndex.ι} {c : f.chartIndex.ι} (h : ChartOver w c' c) :
    f.detNLChart hf c →ₛₗ[(b.appLE c.1.2.1 c'.1.2.1 h.snd.fst).hom] f'.detNLChart hf' c' :=
  detNLSquareMap w hf hf' c c' h.fst h.snd.fst h.snd.snd

include hf hf' in
/-- A refinement of a chart lying over `c` lies over `c`. -/
theorem ChartOver.of_refines {c'' c' : f'.chartIndex.ι} {c : f.chartIndex.ι}
    (h : ChartOver w c' c) (h' : f'.chartIndex.Refines c'' c') : ChartOver w c'' c :=
  ⟨_, _, isGoodChartSquare_of_refines_right w hf hf' c c' c'' h' h.fst h.snd.fst h.snd.snd⟩

/-- The base change maps along charts lying over charts commute with the restriction maps. -/
theorem ChartOver.map_detNLChartRestrict {c₁' c' : f'.chartIndex.ι} {c₁ c : f.chartIndex.ι}
    (h : ChartOver w c' c) (h₁ : ChartOver w c₁' c₁) (hc : f.chartIndex.Refines c₁ c)
    (hc' : f'.chartIndex.Refines c₁' c') (x : f.detNLChart hf c) :
    h₁.map w hf hf' (f.detNLChartRestrict hf hc x) =
      f'.detNLChartRestrict hf' hc' (h.map w hf hf' x) := by
  have hsq₃ := isGoodChartSquare_of_refines_right w hf hf' c c' c₁' hc' h.fst h.snd.fst
    h.snd.snd
  exact (detNLSquareMap_detNLChartRestrict w hf hf' c c₁ c₁' hc h₁.fst h₁.snd.fst h₁.snd.snd
    hsq₃ x).trans (detNLChartRestrict_detNLSquareMap w hf hf' c c' c₁' hc' h.fst h.snd.fst
      h.snd.snd hsq₃ x).symm

end AlgebraicGeometry.Scheme.Hom

end
