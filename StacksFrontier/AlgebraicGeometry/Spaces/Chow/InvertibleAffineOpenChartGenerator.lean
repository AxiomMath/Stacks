module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartOpenRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRelativeSpecGlobalSections
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.TrivialisingChartOfGenerator
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeOnSiteAffineCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ZeroSchemeChartIdealSheafAffineLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.InvertibleDenseAffineTrivialization

/-!
# An invertible module is free on an affine open of every chart, around every point

Let `X` be an algebraic space over a scheme `S` of a big fppf site `B`, let `ℒ` be an invertible
`𝒪_X`-module, let `V` be an étale scheme chart of `X` — **not** assumed affine — and let `v` be a
point of `chartScheme V`.  Then some affine open `O ∋ v` of `chartScheme V`, read as an étale
chart of `X` through `AlgebraicGeometry.Space.openChart`, carries a free generator of `ℒ`, and
hence (`AlgebraicGeometry.Space.isTrivialisingChart_of_bijective_smul`) a compatible family of
free generators over the charts above it.

This is **Zariski**-local triviality of an invertible module on a chart. Stacks 0B8Q, in the form
`AlgebraicGeometry.Space.exists_generator_cover_smul_of_isInvertible`, gives only *étale*-local
triviality: a covering family of the chart whose members are arbitrary charts over it, so that a
member through a prescribed point is an étale neighbourhood of that point and not an open of the
chart scheme.

## Main results

* `AlgebraicGeometry.Space.exists_affineOpen_bijective_smul_of_isInvertible`: **an invertible
  module has a free generator over the chart cut out by some affine open neighbourhood of any
  prescribed point of any chart.**
* `AlgebraicGeometry.Space.exists_affineOpen_isTrivialisingChart_of_isInvertible`: the same with
  the compatible family of free generators over the charts above that open.
* `exists_affineOpen_isRegular_ideal_ker_closedSubspaceBaseChangeChartProj_zeroScheme_eq_span`:
  for a regular section `s` of an invertible module, the chart ideal sheaf of `Z(s)` is generated
  by a single regular function on some affine open neighbourhood of any point of any chart.

## References

* [Stacks Project, Tag 0B8Q](https://stacks.math.columbia.edu/tag/0B8Q)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 0EQL](https://stacks.math.columbia.edu/tag/0EQL)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **An invertible module has a free generator over the chart cut out by an affine open
neighbourhood of any prescribed point of any chart.**  Let `ℒ` be an invertible `𝒪_X`-module, let
`V` be an étale scheme chart of `X` and let `v` be a point of `chartScheme V`.  Then there is an
affine open `O` of `chartScheme V` containing `v` and a section of `ℒ` over the étale chart `O`
cuts out which generates the sections there freely over the regular functions.

Neither `V` nor its scheme is assumed affine: this is the Zariski-local triviality of an
invertible module on a chart, and the affineness of the chart over which the generator lives is
the affineness of the open `O`. -/
theorem exists_affineOpen_bijective_smul_of_isInvertible (X : AlgebraicSpaces B S hS)
    (L : Modules.{u, u} B S hS X.1 X.2)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property L)
    (V : SmallEtale B S hS X.1) (v : chartScheme V) :
    ∃ (O : (chartScheme V).affineOpens) (_ : v ∈ O.1)
      (t : L.val.obj (op (openChart B S hS X.1 V O.1))),
      Function.Bijective
        fun r : chartRing B S hS X.1 X.2 (openChart B S hS X.1 V O.1) ↦ r • t := by
  classical
  have hLc : IsCartesianOnAffineCharts L := isCartesianOnAffineCharts_of_isInvertible B S hS X L hL
  obtain ⟨O₁, hO₁, hvO₁, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := chartScheme V) (x := v) (U := ⊤) trivial
  set C₁ : SmallEtale B S hS X.1 := openChart B S hS X.1 V O₁
  have hC₁aff : IsAffine (chartScheme C₁) :=
    isAffine_chartScheme_openChart B S hS X.1 V ⟨O₁, hO₁⟩
  set pt : chartScheme C₁ := (⟨v, hvO₁⟩ : O₁.toScheme)
  set p : Ideal (chartRing B S hS X.1 X.2 C₁) :=
    ((isAffineOpen_top (chartScheme C₁)).primeIdealOf ⟨pt, trivial⟩).asIdeal
  have : p.IsPrime := ((isAffineOpen_top (chartScheme C₁)).primeIdealOf ⟨pt, trivial⟩).isPrime
  obtain ⟨f, hf, m, hm⟩ := (isFiniteLocallyFreeOfRank_one_sections (hF := X.2) L hLc
    (isFiniteLocallyFreeOfRank_one_of_isInvertible B S hS X L hL) C₁
      hC₁aff).exists_isFreeGeneratorAway p
  set Q : (chartScheme C₁).Opens := (chartScheme C₁).basicOpen f with hQ
  set Cg : SmallEtale B S hS X.1 := openChart B S hS X.1 C₁ Q
  have hCgaff : IsAffine (chartScheme Cg) :=
    isAffine_chartScheme_openChart_basicOpen B S hS X.1 C₁ hC₁aff f
  have hptQ : pt ∈ Q := by
    let : Algebra (chartRing B S hS X.1 X.2 C₁) ((chartScheme C₁).presheaf.stalk pt) :=
      ((chartScheme C₁).presheaf.germ ⊤ pt trivial).hom.toAlgebra
    have : IsLocalization.AtPrime ((chartScheme C₁).presheaf.stalk pt) p :=
      (isAffineOpen_top (chartScheme C₁)).isLocalization_stalk ⟨pt, trivial⟩
    rw [hQ, (chartScheme C₁).mem_basicOpen f pt trivial]
    exact (IsLocalization.AtPrime.isUnit_to_map_iff
      ((chartScheme C₁).presheaf.stalk pt) p f).mpr hf
  obtain ⟨O, hO, hvO, hOsub⟩ := exists_isAffineOpen_mem_and_subset (X := chartScheme V) (x := v)
    (U := O₁.ι ''ᵁ Q) ⟨pt, hptQ, rfl⟩
  have hOO₁ : O ≤ O₁ := fun z hz => by
    obtain ⟨q, -, hq⟩ := hOsub hz
    exact hq ▸ q.2
  set κ₀ : openChart B S hS X.1 V O ⟶ C₁ := openChartHomOfLE B S hS X.1 V hOO₁
  have htop : (⊤ : (chartScheme (openChart B S hS X.1 V O)).Opens) ≤
      chartSchemeMap κ₀ ⁻¹ᵁ Q := by
    intro z _
    let z' : (↥O) := z
    obtain ⟨q, hqQ, hq⟩ := hOsub z'.2
    show (chartSchemeMap κ₀).base z ∈ Q
    rwa [show (chartSchemeMap κ₀).base z = q from
      Subtype.ext ((Scheme.homOfLE_apply hOO₁ z').trans hq.symm)]
  have hOaff : IsAffine (chartScheme (openChart B S hS X.1 V O)) :=
    isAffine_chartScheme_openChart B S hS X.1 V ⟨O, hO⟩
  let := chartAlgebra (hF := X.2) (openChartInclusion B S hS X.1 C₁ Q)
  let := chartSectionsModule L (openChartInclusion B S hS X.1 C₁ Q)
  have := chartSections_isScalarTower L (openChartInclusion B S hS X.1 C₁ Q)
  have := isLocalization_away_chartRing_openChart_basicOpen B S hS X.2 C₁ hC₁aff f
  have := isLocalizedModule_chartRestrictLinear_openChart_basicOpen B S hS X.2 L hLc C₁ hC₁aff f
  have hgen := Module.isFreeGeneratorAway_bijective_smul
    (A' := chartRing B S hS X.1 X.2 (openChart B S hS X.1 C₁ Q))
    (chartRestrictLinear L (openChartInclusion B S hS X.1 C₁ Q)) hm
  exact ⟨⟨O, hO⟩, hvO, _, bijective_smul_map_of_bijective_smul (hF := X.2) L hLc hCgaff hOaff
    ((openChartTopIso B S hS X.1 (openChart B S hS X.1 V O)).inv ≫
      openChartHomOfLE B S hS X.1 (openChart B S hS X.1 V O) htop ≫
      openChartRestrict B S hS X.1 κ₀ Q) hgen⟩

/-- **An invertible module is trivialised by the chart cut out by some affine open neighbourhood
of any prescribed point of any chart.**  Let `ℒ` be an invertible `𝒪_X`-module, let `V` be an
étale scheme chart of `X` and let `v` be a point of `chartScheme V`.  Then there is an affine open
`O` of `chartScheme V` containing `v` and a free generator of `ℒ` over the étale chart `O` cuts
out, and that chart carries a compatible family of free generators over the charts above it. -/
theorem exists_affineOpen_isTrivialisingChart_of_isInvertible (X : AlgebraicSpaces B S hS)
    (L : Modules.{u, u} B S hS X.1 X.2)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property L)
    (V : SmallEtale B S hS X.1) (v : chartScheme V) :
    ∃ (O : (chartScheme V).affineOpens) (_ : v ∈ O.1)
      (t : L.val.obj (op (openChart B S hS X.1 V O.1))),
      Function.Bijective
          (fun r : chartRing B S hS X.1 X.2 (openChart B S hS X.1 V O.1) ↦ r • t) ∧
        IsTrivialisingChart B S hS L (openChart B S hS X.1 V O.1) := by
  obtain ⟨O, hvO, t, ht⟩ := exists_affineOpen_bijective_smul_of_isInvertible B S hS X L hL V v
  have hOaff : IsAffine (chartScheme (openChart B S hS X.1 V O.1)) :=
    isAffine_chartScheme_openChart B S hS X.1 V O
  exact ⟨O, hvO, t, ht,
    isTrivialisingChart_of_bijective_smul_of_isInvertible B S hS L hL
      (openChart B S hS X.1 V O.1) hOaff t ht⟩

/-- **The local equation of the zero scheme of a regular section on an arbitrary chart, at an
arbitrary point.**  Let `ℒ` be an invertible `𝒪_X`-module with a **regular** global section `s`,
let `V` be an étale scheme chart of `X` — not assumed affine — and let `v` be a point of
`chartScheme V`.  Then some affine open `O ∋ v` of `chartScheme V` carries a single *regular*
function `a` generating the ideal which the chart ideal sheaf of `Z(s)` attaches to `O`. -/
theorem exists_affineOpen_isRegular_ideal_ker_closedSubspaceBaseChangeChartProj_zeroScheme_eq_span
    (X : AlgebraicSpaces B S hS) (L : Modules.{u, u} B S hS X.1 X.2)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property L)
    (s : L.sections)
    (hsreg : AlgebraicGeometry.IsRegularSection (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property s)
    (V : SmallEtale B S hS X.1) (v : chartScheme V) :
    ∃ (O : (chartScheme V).affineOpens) (_ : v ∈ O.1) (a : Γ(chartScheme V, O.1)),
      _root_.IsRegular a ∧
        (closedSubspaceBaseChangeChartProj B S hS X.2 (zeroScheme B S hS X L s).1
          (zeroScheme B S hS X L s).2 V).ker.ideal O = Ideal.span {a} := by
  obtain ⟨O, hvO, t, ht⟩ := exists_affineOpen_bijective_smul_of_isInvertible B S hS X L hL V v
  exact ⟨O, hvO, exists_isRegular_ideal_ker_closedSubspaceBaseChangeChartProj_zeroScheme_eq_span
    B S hS X L hL s hsreg V O t ht⟩

end AlgebraicGeometry.Space

end
