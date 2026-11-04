module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingModuleGluing0BVG
public import StacksFrontier.AlgebraicGeometry.TateMap.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Finite
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.QuasiFinite
public import StacksFrontier.RingTheory.TateMap.DetNLBaseChangeComp
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleCompare
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Sheaf
public import StacksFrontier.AlgebraicGeometry.InvertibleRankOneModule.Basic
public import StacksFrontier.AlgebraicGeometry.ModuleDescent.InvertibleInput
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineLocalFree

/-!
# The determinant of the naive cotangent complex of a locally quasi-finite syntomic morphism

Let `f : Y ⟶ X` be a locally quasi-finite syntomic morphism of schemes. On every affine chart
`V = Spec B ⊆ f⁻¹(U)`, `U = Spec A`, the naive cotangent complex `NL_{B/A}` is a perfect
two-term complex of rank zero, with determinant `det(NL_{B/A})`, an invertible `B`-module, and
canonical element `δ(NL_{B/A})` (Stacks, Section 0FKB). This file glues these into an invertible
`𝒪_Y`-module `det(NL_{Y/X})` with a global section `δ(NL_{Y/X})`.

## Main definitions

* `AlgebraicGeometry.TateMap.detNL f hf`: the `𝒪_Y`-module `det(NL_{Y/X})`.
* `AlgebraicGeometry.TateMap.detNLChartEquiv`: its sections over an affine chart are
  `det(NL_{B/A})`.
* `AlgebraicGeometry.TateMap.deltaNL f hf`: the global section `δ(NL_{Y/X})`.

## Main results

* `AlgebraicGeometry.TateMap.detNLChartEquiv_restrict`: the chart identifications are
  compatible with base change on basic-open restriction squares.
* `AlgebraicGeometry.TateMap.isInvertible_detNL`: `det(NL_{Y/X})` is invertible.
* `AlgebraicGeometry.TateMap.detNLChartEquiv_deltaNL`: `δ(NL_{Y/X})` restricts to
  `δ(NL_{B/A})` on every affine chart.

## Implementation notes

The module is glued from the chart sheaves of the *adapted opens* of `f` (affine opens of the
source over affine opens of the base, `Stacks.Discriminant.AdaptedOpen`), compared over adapted
opens good for two charts through the *hub* of the smaller one: the sections of the chart sheaf
of `i` over a principal open `k` of it are `Γ(k) ⊗_{Γ(i)} det(NL_i)`, which the base change of
the determinant along the chart base change from `i` to `k` identifies with `det(NL_k)`. All
comparisons at one adapted open factor through its hub, so the cocycle identity is free; the
restriction compatibility is the composition law of the base change of the determinant. Unlike
the relative dualizing module, no Noetherian hypothesis is needed.

## References

* [Stacks Project, Section 0FKB](https://stacks.math.columbia.edu/tag/0FKB)
* [Stacks Project, Tag 0FJX](https://stacks.math.columbia.edu/tag/0FJX)
* [Stacks Project, Tag 00AM](https://stacks.math.columbia.edu/tag/00AM)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open scoped TensorProduct

open Stacks.Discriminant Stacks.AlgebraicGeometry.QuasicoherentBaseChange

universe u

namespace AlgebraicGeometry.TateMap

variable {X Y : Scheme.{u}} (f : Y ⟶ X) (hf : IsQuasiFiniteSyntomic f)

/-- The determinant of the naive cotangent complex of the coordinate-ring map of an adapted open
of `f`, as a module over the functions on its source open. -/
abbrev chartDetNL (k : AdaptedOpen f) : ModuleCat.{u} Γ(Y, k.source.1) :=
  letI : Algebra Γ(X, k.base.1) Γ(Y, k.source.1) :=
    (f.appLE k.base k.source k.source_le).hom.toAlgebra
  haveI := algebra_syntomic_appLE hf.2 k.base k.source k.source_le
  ModuleCat.of _ (Stacks.TateMap.detNL Γ(X, k.base.1) Γ(Y, k.source.1))

/-- The sheaf of `𝒪_Y`-modules determined by `chartDetNL` on the source open of an adapted
open. -/
abbrev chartDetNLSheaf (k : AdaptedOpen f) : Y.Modules :=
  Stacks.Modules.chartSheaf k.source (chartDetNL f hf k)

/-- The chart base change from an adapted open `i` to an adapted open `k` good for it. -/
def goodChartBaseChange (k i : AdaptedOpen f) (hki : k.Good i.source i.base) :
    letI : Algebra Γ(X, i.base.1) Γ(Y, i.source.1) :=
      (f.appLE i.base i.source i.source_le).hom.toAlgebra
    letI : Algebra Γ(X, k.base.1) Γ(Y, k.source.1) :=
      (f.appLE k.base k.source k.source_le).hom.toAlgebra
    letI : Algebra Γ(X, i.base.1) Γ(X, k.base.1) :=
      (X.presheaf.map (homOfLE hki.baseLE).op).hom.toAlgebra
    letI : Algebra Γ(Y, i.source.1) Γ(Y, k.source.1) :=
      (Y.presheaf.map (homOfLE hki.le).op).hom.toAlgebra
    Stacks.TateMap.ChartBaseChange Γ(X, i.base.1) Γ(Y, i.source.1) Γ(X, k.base.1)
      Γ(Y, k.source.1) :=
  chartBaseChangeBasicOpen f i.base i.source i.source_le k.base.1 k.source.1 hki.2.choose
    hki.1.choose hki.2.choose_spec.symm hki.1.choose_spec.symm hki.baseLE hki.le k.source_le

/-- **The hub comparison.** The sections over an adapted open `k` of the chart sheaf of an
adapted open `i` that `k` is good for are `det(NL)` of the chart `k`: the sections are the
localization `Γ(k) ⊗_{Γ(i)} det(NL_i)`, which base change identifies with `det(NL_k)`. -/
def detNLHub (k i : AdaptedOpen f) (hki : k.Good i.source i.base) :
    Γ(chartDetNLSheaf f hf i, k.source.1) ≃ₗ[Γ(Y, k.source.1)] chartDetNL f hf k := by
  letI : Algebra Γ(X, i.base.1) Γ(Y, i.source.1) :=
    (f.appLE i.base i.source i.source_le).hom.toAlgebra
  letI : Algebra Γ(X, k.base.1) Γ(Y, k.source.1) :=
    (f.appLE k.base k.source k.source_le).hom.toAlgebra
  letI : Algebra Γ(X, i.base.1) Γ(X, k.base.1) :=
    (X.presheaf.map (homOfLE hki.baseLE).op).hom.toAlgebra
  letI : Algebra Γ(Y, i.source.1) Γ(Y, k.source.1) :=
    (Y.presheaf.map (homOfLE hki.le).op).hom.toAlgebra
  haveI := algebra_syntomic_appLE hf.2 i.base i.source i.source_le
  haveI := algebra_syntomic_appLE hf.2 k.base k.source k.source_le
  haveI : IsLocalization.Away hki.1.choose Γ(Y, k.source.1) :=
    i.source.2.isLocalization_of_eq_basicOpen _ (homOfLE hki.le) hki.1.choose_spec.symm
  letI := moduleOfLE (chartDetNLSheaf f hf i) hki.le
  letI := isScalarTowerOfLE (chartDetNLSheaf f hf i) hki.le
  have hloc := Stacks.Modules.isLocalizedModule_chartSectionOfLE i.source (chartDetNL f hf i)
    hki.1.choose hki.le hki.1.choose_spec.symm
  have hbc := IsLocalizedModule.isBaseChange (Submonoid.powers hki.1.choose) Γ(Y, k.source.1)
    (Stacks.Modules.chartSectionOfLE i.source (chartDetNL f hf i) hki.le)
  exact hbc.equiv.symm ≪≫ₗ Stacks.TateMap.detNLBaseChange (goodChartBaseChange f k i hki)

/-- The hub comparison on the section of the chart sheaf determined by an element `m`: base change
of `1 ⊗ m`. -/
theorem detNLHub_chartSection (k i : AdaptedOpen f) (hki : k.Good i.source i.base)
    (m : chartDetNL f hf i) :
    letI : Algebra Γ(X, i.base.1) Γ(Y, i.source.1) :=
      (f.appLE i.base i.source i.source_le).hom.toAlgebra
    letI : Algebra Γ(X, k.base.1) Γ(Y, k.source.1) :=
      (f.appLE k.base k.source k.source_le).hom.toAlgebra
    letI : Algebra Γ(X, i.base.1) Γ(X, k.base.1) :=
      (X.presheaf.map (homOfLE hki.baseLE).op).hom.toAlgebra
    letI : Algebra Γ(Y, i.source.1) Γ(Y, k.source.1) :=
      (Y.presheaf.map (homOfLE hki.le).op).hom.toAlgebra
    haveI := algebra_syntomic_appLE hf.2 i.base i.source i.source_le
    haveI := algebra_syntomic_appLE hf.2 k.base k.source k.source_le
    detNLHub f hf k i hki (Stacks.Modules.chartSection i.source (chartDetNL f hf i) k.source.1 m) =
      Stacks.TateMap.detNLBaseChange (goodChartBaseChange f k i hki)
        ((1 : Γ(Y, k.source.1)) ⊗ₜ[Γ(Y, i.source.1)] m) := by
  let : Algebra Γ(X, i.base.1) Γ(Y, i.source.1) :=
    (f.appLE i.base i.source i.source_le).hom.toAlgebra
  let : Algebra Γ(X, k.base.1) Γ(Y, k.source.1) :=
    (f.appLE k.base k.source k.source_le).hom.toAlgebra
  let : Algebra Γ(X, i.base.1) Γ(X, k.base.1) :=
    (X.presheaf.map (homOfLE hki.baseLE).op).hom.toAlgebra
  let : Algebra Γ(Y, i.source.1) Γ(Y, k.source.1) :=
    (Y.presheaf.map (homOfLE hki.le).op).hom.toAlgebra
  have := algebra_syntomic_appLE hf.2 i.base i.source i.source_le
  have := algebra_syntomic_appLE hf.2 k.base k.source k.source_le
  have : IsLocalization.Away hki.1.choose Γ(Y, k.source.1) :=
    i.source.2.isLocalization_of_eq_basicOpen _ (homOfLE hki.le) hki.1.choose_spec.symm
  let := moduleOfLE (chartDetNLSheaf f hf i) hki.le
  let := isScalarTowerOfLE (chartDetNLSheaf f hf i) hki.le
  have hloc := Stacks.Modules.isLocalizedModule_chartSectionOfLE i.source (chartDetNL f hf i)
    hki.1.choose hki.le hki.1.choose_spec.symm
  have hbc := IsLocalizedModule.isBaseChange (Submonoid.powers hki.1.choose) Γ(Y, k.source.1)
    (Stacks.Modules.chartSectionOfLE i.source (chartDetNL f hf i) hki.le)
  show Stacks.TateMap.detNLBaseChange (goodChartBaseChange f k i hki)
    (hbc.equiv.symm (Stacks.Modules.chartSectionOfLE i.source (chartDetNL f hf i) hki.le m)) = _
  rw [hbc.equiv_symm_apply m]

/-- Restriction maps of functions along a chain of opens `W ≤ V ≤ U` compose. -/
private theorem presheaf_map_hom_comp {Z : Scheme.{u}} {U V W : Z.Opens} (hVU : V ≤ U)
    (hWV : W ≤ V) (hWU : W ≤ U) :
    (Z.presheaf.map (homOfLE hWU).op).hom =
      (Z.presheaf.map (homOfLE hWV).op).hom.comp (Z.presheaf.map (homOfLE hVU).op).hom := by
  rw [← CommRingCat.hom_comp, ← Functor.map_comp]
  rfl

/-- **The hub comparisons of two nested adapted opens are intertwined by base change.** For
adapted opens `l ⊆ k` (sources and bases) both good for `i`, and any chart base change datum `D`
from `k` to `l`, the hub of `l` on the restriction of a section is the base change along `D` of
the hub of `k`. -/
theorem detNLHub_restrict (k l i : AdaptedOpen f) (hki : k.Good i.source i.base)
    (hli : l.Good i.source i.base) (hW : l.source.1 ≤ k.source.1) (hB : l.base.1 ≤ k.base.1) :
    letI : Algebra Γ(X, k.base.1) Γ(Y, k.source.1) :=
      (f.appLE k.base k.source k.source_le).hom.toAlgebra
    letI : Algebra Γ(X, l.base.1) Γ(Y, l.source.1) :=
      (f.appLE l.base l.source l.source_le).hom.toAlgebra
    letI : Algebra Γ(X, k.base.1) Γ(X, l.base.1) :=
      (X.presheaf.map (homOfLE hB).op).hom.toAlgebra
    letI : Algebra Γ(Y, k.source.1) Γ(Y, l.source.1) :=
      (Y.presheaf.map (homOfLE hW).op).hom.toAlgebra
    haveI := algebra_syntomic_appLE hf.2 k.base k.source k.source_le
    haveI := algebra_syntomic_appLE hf.2 l.base l.source l.source_le
    ∀ (D : Stacks.TateMap.ChartBaseChange Γ(X, k.base.1) Γ(Y, k.source.1) Γ(X, l.base.1)
        Γ(Y, l.source.1)) (s : Γ(chartDetNLSheaf f hf i, k.source.1)),
      detNLHub f hf l i hli ((chartDetNLSheaf f hf i).presheaf.map (homOfLE hW).op s) =
        Stacks.TateMap.detNLBaseChange D ((1 : Γ(Y, l.source.1)) ⊗ₜ detNLHub f hf k i hki s) := by
  intro D s
  let : Algebra Γ(X, i.base.1) Γ(Y, i.source.1) :=
    (f.appLE i.base i.source i.source_le).hom.toAlgebra
  let : Algebra Γ(X, k.base.1) Γ(Y, k.source.1) :=
    (f.appLE k.base k.source k.source_le).hom.toAlgebra
  let : Algebra Γ(X, l.base.1) Γ(Y, l.source.1) :=
    (f.appLE l.base l.source l.source_le).hom.toAlgebra
  let : Algebra Γ(X, k.base.1) Γ(X, l.base.1) :=
    (X.presheaf.map (homOfLE hB).op).hom.toAlgebra
  let : Algebra Γ(Y, k.source.1) Γ(Y, l.source.1) :=
    (Y.presheaf.map (homOfLE hW).op).hom.toAlgebra
  let : Algebra Γ(X, i.base.1) Γ(X, k.base.1) :=
    (X.presheaf.map (homOfLE hki.baseLE).op).hom.toAlgebra
  let : Algebra Γ(Y, i.source.1) Γ(Y, k.source.1) :=
    (Y.presheaf.map (homOfLE hki.le).op).hom.toAlgebra
  let : Algebra Γ(X, i.base.1) Γ(X, l.base.1) :=
    (X.presheaf.map (homOfLE hli.baseLE).op).hom.toAlgebra
  let : Algebra Γ(Y, i.source.1) Γ(Y, l.source.1) :=
    (Y.presheaf.map (homOfLE hli.le).op).hom.toAlgebra
  have := algebra_syntomic_appLE hf.2 i.base i.source i.source_le
  have := algebra_syntomic_appLE hf.2 k.base k.source k.source_le
  have := algebra_syntomic_appLE hf.2 l.base l.source l.source_le
  have : IsScalarTower Γ(X, i.base.1) Γ(X, k.base.1) Γ(X, l.base.1) :=
    IsScalarTower.of_algebraMap_eq' (presheaf_map_hom_comp hki.baseLE hB hli.baseLE)
  have : IsScalarTower Γ(Y, i.source.1) Γ(Y, k.source.1) Γ(Y, l.source.1) :=
    IsScalarTower.of_algebraMap_eq' (presheaf_map_hom_comp hki.le hW hli.le)
  -- on the sections determined by elements of the chart module
  have hgen : ∀ m : chartDetNL f hf i,
      detNLHub f hf l i hli ((chartDetNLSheaf f hf i).presheaf.map (homOfLE hW).op
        (Stacks.Modules.chartSection i.source (chartDetNL f hf i) k.source.1 m)) =
      Stacks.TateMap.detNLBaseChange D ((1 : Γ(Y, l.source.1)) ⊗ₜ detNLHub f hf k i hki
        (Stacks.Modules.chartSection i.source (chartDetNL f hf i) k.source.1 m)) := by
    intro m
    rw [Stacks.Modules.chartSection_res, detNLHub_chartSection, detNLHub_chartSection,
      Stacks.TateMap.detNLBaseChange_comp (goodChartBaseChange f k i hki) D
        (goodChartBaseChange f l i hli)]
    simp only [LinearEquiv.trans_apply]
    congr 1
  -- reduce to those sections, `s` being a fraction of one of them
  have : IsLocalization.Away hki.1.choose Γ(Y, k.source.1) :=
    i.source.2.isLocalization_of_eq_basicOpen _ (homOfLE hki.le) hki.1.choose_spec.symm
  let := moduleOfLE (chartDetNLSheaf f hf i) hki.le
  have hloc := Stacks.Modules.isLocalizedModule_chartSectionOfLE i.source (chartDetNL f hf i)
    hki.1.choose hki.le hki.1.choose_spec.symm
  obtain ⟨⟨m, ⟨_, n, rfl⟩⟩, hs⟩ := hloc.surj s
  change (Y.presheaf.map (homOfLE hki.le).op (hki.1.choose ^ n)) • s =
    Stacks.Modules.chartSection i.source (chartDetNL f hf i) k.source.1 m at hs
  set r := Y.presheaf.map (homOfLE hki.le).op (hki.1.choose ^ n)
  have hr : IsUnit (Y.presheaf.map (homOfLE hW).op r) := by
    have : IsUnit r := by
      show IsUnit (algebraMap Γ(Y, i.source.1) Γ(Y, k.source.1) (hki.1.choose ^ n))
      rw [map_pow]
      exact (IsLocalization.Away.algebraMap_isUnit hki.1.choose).pow n
    exact this.map _
  refine hr.smul_left_cancel.mp ?_
  have h₁ := hgen m
  rw [← hs, Scheme.Modules.map_smul, map_smul, map_smul, TensorProduct.tmul_smul] at h₁
  rw [h₁, ← map_smul]
  congr 1

/-- The comparison of the chart sheaves of two adapted opens over an adapted open good for both,
through the hub of the latter. -/
def detNLComparison (k i j : AdaptedOpen f) (hki : k.Good i.source i.base)
    (hkj : k.Good j.source j.base) :
    Γ(chartDetNLSheaf f hf i, k.source.1) ≃ₗ[Γ(Y, k.source.1)]
      Γ(chartDetNLSheaf f hf j, k.source.1) :=
  (detNLHub f hf k i hki).trans (detNLHub f hf k j hkj).symm

/-- The cocycle identity, free because the three comparisons factor through one hub. -/
theorem detNLComparison_trans (k i j m : AdaptedOpen f) (hi : k.Good i.source i.base)
    (hj : k.Good j.source j.base) (hm : k.Good m.source m.base)
    (s : Γ(chartDetNLSheaf f hf i, k.source.1)) :
    detNLComparison f hf k j m hj hm (detNLComparison f hf k i j hi hj s) =
      detNLComparison f hf k i m hi hm s := by
  simp only [detNLComparison, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]

/-- A principal open of an affine open `V'` contained in a smaller affine open `V` is a
principal open of `V`. -/
private theorem exists_basicOpen_eq_of_le {Z : Scheme.{u}} {V' V : Z.Opens} (g : Γ(Z, V'))
    {W : Z.Opens} (hW : Z.basicOpen g = W) (hWV : W ≤ V) (hVV' : V ≤ V') :
    ∃ g' : Γ(Z, V), Z.basicOpen g' = W :=
  ⟨Z.presheaf.map (homOfLE hVV').op g, by rw [Scheme.basicOpen_res, hW, inf_eq_right.mpr hWV]⟩

/-- **The comparison commutes with restriction**, along any nesting of adapted opens good for
both charts. -/
theorem detNLComparison_restrict (k l i j : AdaptedOpen f) (hki : k.Good i.source i.base)
    (hkj : k.Good j.source j.base) (hli : l.Good i.source i.base)
    (hlj : l.Good j.source j.base) (hW : l.source.1 ≤ k.source.1)
    (s : Γ(chartDetNLSheaf f hf i, k.source.1)) :
    detNLComparison f hf l i j hli hlj
        ((chartDetNLSheaf f hf i).presheaf.map (homOfLE hW).op s) =
      (chartDetNLSheaf f hf j).presheaf.map (homOfLE hW).op
        (detNLComparison f hf k i j hki hkj s) := by
  refine AdaptedOpen.restrict_comparison_of_source_le (f := f) (fun m ↦ m.source)
    (fun m ↦ m.base) (chartDetNLSheaf f hf)
    (fun m a b ha hb ↦ detNLComparison f hf m a b ha hb)
    (fun k l i j hki hkj hli hlj hW hB s ↦ ?_) k l i j hki hkj hli hlj hW s
  obtain ⟨a', ha'⟩ := exists_basicOpen_eq_of_le hli.2.choose hli.2.choose_spec hB hki.baseLE
  obtain ⟨g', hg'⟩ := exists_basicOpen_eq_of_le hli.1.choose hli.1.choose_spec hW hki.le
  let D := chartBaseChangeBasicOpen f k.base k.source k.source_le l.base.1 l.source.1 a' g'
    ha'.symm hg'.symm hB hW l.source_le
  apply (detNLHub f hf l j hlj).injective
  simp only [detNLComparison, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  rw [detNLHub_restrict f hf k l i hki hli hW hB D s,
    detNLHub_restrict f hf k l j hkj hlj hW hB D, LinearEquiv.apply_symm_apply]

/-- **Glueing data for `det(NL_{Y/X})`**: a quasi-coherent `𝒪_Y`-module whose sections over every
open inside the source open of an adapted open `i` are those of the chart sheaf of `i`,
compatibly with restriction and with the comparisons. -/
structure GluedDetNL where
  /-- The glued module. -/
  sheaf : Y.Modules
  /-- The identification of its sections with those of a chart sheaf. -/
  sections : ∀ (i : AdaptedOpen f) (W : Y.Opens), W ≤ i.source.1 →
    Γ(sheaf, W) ≃ₗ[Γ(Y, W)] Γ(chartDetNLSheaf f hf i, W)
  /-- The glued module is quasi-coherent. -/
  isQuasicoherent : sheaf.IsQuasicoherent
  /-- The identifications commute with restriction. -/
  sections_restrict : ∀ (i : AdaptedOpen f) (W W' : Y.Opens) (hW : W ≤ i.source.1)
    (h : W' ≤ W) (s : Γ(sheaf, W)),
    sections i W' (h.trans hW) (sheaf.presheaf.map (homOfLE h).op s) =
      (chartDetNLSheaf f hf i).presheaf.map (homOfLE h).op (sections i W hW s)
  /-- The identifications are intertwined by the comparisons. -/
  sections_comparison : ∀ (k i j : AdaptedOpen f) (hki : k.Good i.source i.base)
    (hkj : k.Good j.source j.base) (s : Γ(sheaf, k.source.1)),
    sections j k.source.1 hkj.le s =
      detNLComparison f hf k i j hki hkj (sections i k.source.1 hki.le s)

/-- **The determinant of the naive cotangent complex can be glued.** -/
theorem nonempty_gluedDetNL : Nonempty (GluedDetNL f hf) := by
  obtain ⟨t, tm, tt, hagree⟩ := Stacks.Modules.exists_transData_of_basis
    (fun i : AdaptedOpen f ↦ i.source.1) (chartDetNLSheaf f hf)
    (fun k : AdaptedOpen f ↦ k.source.1) (fun k i ↦ k.Good i.source i.base)
    (fun _ _ h ↦ h.le)
    (AdaptedOpen.exists_good_pair (f := f) (fun m : AdaptedOpen f ↦ m.source)
      (fun m : AdaptedOpen f ↦ m.base) fun m ↦ m.source_le)
    (AdaptedOpen.exists_good_triple (f := f) (fun m : AdaptedOpen f ↦ m.source)
      (fun m : AdaptedOpen f ↦ m.base) fun m ↦ m.source_le)
    (fun m a b ha hb ↦ detNLComparison f hf m a b ha hb)
    (detNLComparison_restrict f hf) (detNLComparison_trans f hf)
  let G := Stacks.SheafOfModules.OModuleGlueData.ofModules (U := fun i : AdaptedOpen f ↦ i.source.1)
    (chartDetNLSheaf f hf) t tm tt
  exact ⟨{
    sheaf := G.gluedModules
    sections := fun i V hV ↦ G.chartLinearEquiv i hV
    isQuasicoherent := Stacks.SheafOfModules.isQuasicoherent_gluedModules_ofModules
      (iSup_adaptedOpen_source_eq_top f) (chartDetNLSheaf f hf) t tm tt
      (fun i ↦ Stacks.Modules.isQuasicoherent_restrict_chartSheaf _ _)
    sections_restrict := fun i V V' hV h s ↦ G.chartLinearEquiv_restrict i hV h s
    sections_comparison := fun k i j hki hkj s ↦
      (G.trans_chartLinearEquiv i j hki.le hkj.le s).symm.trans (hagree k i j hki hkj _) }⟩

/-- The chosen glueing of `det(NL_{Y/X})`. -/
def gluedDetNL : GluedDetNL f hf :=
  (nonempty_gluedDetNL f hf).some

/-- **The determinant `det(NL_{Y/X})`** of the naive cotangent complex of a locally quasi-finite
syntomic morphism, as an `𝒪_Y`-module: glued from `det(NL_{B/A})` on the affine charts. -/
abbrev detNL : Y.Modules :=
  (gluedDetNL f hf).sheaf

/-- `det(NL_{Y/X})` is quasi-coherent. -/
theorem isQuasicoherent_detNL : (detNL f hf).IsQuasicoherent :=
  (gluedDetNL f hf).isQuasicoherent

/-- **The chart identification of `det(NL_{Y/X})`.** On an affine chart `V ⊆ f⁻¹(U)`, the
sections of `det(NL_{Y/X})` over `V` are `det(NL_{Γ(Y, V)/Γ(X, U)})`. -/
def detNLChartEquiv (U : X.affineOpens) (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1) :
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
    haveI := algebra_syntomic_appLE hf.2 U V hVU
    Γ(detNL f hf, V.1) ≃ₗ[Γ(Y, V.1)] Stacks.TateMap.detNL Γ(X, U.1) Γ(Y, V.1) :=
  (gluedDetNL f hf).sections ⟨V, U, hVU⟩ V.1 le_rfl ≪≫ₗ
    (Stacks.Modules.chartTopEquiv V (chartDetNL f hf ⟨V, U, hVU⟩)).symm

/-- Base change along a chart base change of `A → B` to itself fixes `1 ⊗ x`, for any algebra
structures of `A` and `B` over themselves that are the identity. -/
theorem detNLBaseChange_one_tmul_of_eq_id {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {instA : Algebra A A} {instB : Algebra B B} (hA : instA = Algebra.id A)
    (hB : instB = Algebra.id B) [Algebra.Syntomic A B]
    (D : Stacks.TateMap.ChartBaseChange A B A B) (x : Stacks.TateMap.detNL A B) :
    letI : Module B B := Algebra.toModule
    Stacks.TateMap.detNLBaseChange D ((1 : B) ⊗ₜ[B] x) = x := by
  subst hA hB
  rw [Stacks.TateMap.detNLBaseChange_refl D]
  exact (TensorProduct.lid_tmul _ _).trans (one_smul _ _)

/-- Restriction of functions along an equality of opens is the identity algebra structure. -/
theorem presheaf_map_toAlgebra_eq_id {Z : Scheme.{u}} {W : Z.Opens} (h : W ≤ W) :
    (Z.presheaf.map (homOfLE h).op).hom.toAlgebra = Algebra.id Γ(Z, W) := by
  refine Algebra.algebra_ext _ _ fun r ↦ ?_
  show (Z.presheaf.map (homOfLE h).op).hom r = r
  rw [show homOfLE h = 𝟙 W from Subsingleton.elim _ _, op_id, CategoryTheory.Functor.map_id]
  rfl

/-- The hub comparison of an adapted open with itself is the inverse of the identification of the
sections of its chart sheaf over its source open. -/
theorem detNLHub_self (j : AdaptedOpen f) (hjj : j.Good j.source j.base)
    (y : chartDetNL f hf j) :
    detNLHub f hf j j hjj (Stacks.Modules.chartSection j.source (chartDetNL f hf j) j.source.1 y) =
      y := by
  let : Algebra Γ(X, j.base.1) Γ(Y, j.source.1) :=
    (f.appLE j.base j.source j.source_le).hom.toAlgebra
  have := algebra_syntomic_appLE hf.2 j.base j.source j.source_le
  rw [detNLHub_chartSection]
  exact detNLBaseChange_one_tmul_of_eq_id (presheaf_map_toAlgebra_eq_id _)
    (presheaf_map_toAlgebra_eq_id _) _ y

/-- **The chart identifications of `det(NL_{Y/X})` are compatible with base change on a
basic-open restriction square.** -/
theorem detNLChartEquiv_restrict (U : X.affineOpens) (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1)
    (a : Γ(X, U.1)) (b : Γ(Y, V.1)) (hba : Y.basicOpen b ≤ f ⁻¹ᵁ X.basicOpen a) :
    let Ua : X.affineOpens := ⟨X.basicOpen a, U.2.basicOpen a⟩
    let Vb : Y.affineOpens := ⟨Y.basicOpen b, V.2.basicOpen b⟩
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
    letI : Algebra Γ(X, Ua.1) Γ(Y, Vb.1) := (f.appLE Ua Vb hba).hom.toAlgebra
    letI : Algebra Γ(X, U.1) Γ(X, Ua.1) :=
      (X.presheaf.map (homOfLE (X.basicOpen_le a)).op).hom.toAlgebra
    letI : Algebra Γ(Y, V.1) Γ(Y, Vb.1) :=
      (Y.presheaf.map (homOfLE (Y.basicOpen_le b)).op).hom.toAlgebra
    haveI := algebra_syntomic_appLE hf.2 U V hVU
    haveI := algebra_syntomic_appLE hf.2 Ua Vb hba
    ∀ (D : Stacks.TateMap.ChartBaseChange Γ(X, U.1) Γ(Y, V.1) Γ(X, Ua.1) Γ(Y, Vb.1))
      (t : Γ(detNL f hf, V.1)),
      detNLChartEquiv f hf Ua Vb hba
          ((detNL f hf).presheaf.map (homOfLE (Y.basicOpen_le b)).op t) =
        Stacks.TateMap.detNLBaseChange D ((1 : Γ(Y, Vb.1)) ⊗ₜ detNLChartEquiv f hf U V hVU t) := by
  intro Ua Vb D t
  let i : AdaptedOpen f := ⟨V, U, hVU⟩
  let j : AdaptedOpen f := ⟨Vb, Ua, hba⟩
  have hji : j.Good i.source i.base := ⟨⟨b, rfl⟩, ⟨a, rfl⟩⟩
  have hjj : j.Good j.source j.base := ⟨⟨1, Y.basicOpen_one⟩, ⟨1, X.basicOpen_one⟩⟩
  set m := detNLChartEquiv f hf U V hVU t with hm
  have h₁ : (gluedDetNL f hf).sections i V.1 le_rfl t =
      Stacks.Modules.chartSection V (chartDetNL f hf i) V.1 m := by
    rw [hm]
    exact ((Stacks.Modules.chartTopEquiv V (chartDetNL f hf i)).apply_symm_apply _).symm
  have h₂ : (gluedDetNL f hf).sections i Vb.1 hji.le
      ((detNL f hf).presheaf.map (homOfLE (Y.basicOpen_le b)).op t) =
      Stacks.Modules.chartSection V (chartDetNL f hf i) Vb.1 m := by
    have h := (gluedDetNL f hf).sections_restrict i V.1 Vb.1 le_rfl (Y.basicOpen_le b) t
    rwa [h₁, Stacks.Modules.chartSection_res] at h
  have h₃ := (gluedDetNL f hf).sections_comparison j i j hji hjj
    ((detNL f hf).presheaf.map (homOfLE (Y.basicOpen_le b)).op t)
  rw [h₂] at h₃
  show (Stacks.Modules.chartTopEquiv Vb (chartDetNL f hf j)).symm
    ((gluedDetNL f hf).sections j Vb.1 le_rfl _) = _
  rw [h₃, detNLComparison, LinearEquiv.trans_apply, detNLHub_chartSection,
    LinearEquiv.symm_apply_eq, LinearEquiv.symm_apply_eq, Stacks.Modules.chartTopEquiv_apply,
    detNLHub_self]
  rfl

/-- **`det(NL_{Y/X})` is an invertible `𝒪_Y`-module**: its sections over every affine chart are
`det(NL_{B/A})`, an invertible `B`-module. -/
theorem isInvertible_detNL :
    Stacks.SheafOfModules.IsInvertible Y.presheaf (structureSheafRing Y.toRingedSpace).property
      (detNL f hf) := by
  have := isQuasicoherent_detNL f hf
  refine (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ (detNL f hf)).mpr ?_
  refine Stacks.ModuleDescent.isInvertible_of_isFiniteLocallyFreeOfRank_one Y (detNL f hf) ?_
  refine (Scheme.Modules.isFiniteLocallyFreeOfRank_iff (detNL f hf) 1).mp ?_
  refine Stacks.Modules.isFiniteLocallyFreeOfRank_of_module_affineOpens (detNL f hf) 1
    fun y ↦ ?_
  obtain ⟨U, V, hyV, hVU⟩ := exists_affineChartPair f y
  refine ⟨V, hyV, ?_⟩
  let : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
  have := algebra_syntomic_appLE hf.2 U V hVU
  have := Module.Invertible.congr (detNLChartEquiv f hf U V hVU).symm
  exact Module.isFiniteLocallyFreeOfRank_one_of_invertible

/-- The canonical section `δ(NL_{B/A})` of `det(NL_{Y/X})` over the source open of an adapted
open `i`, read through the chart identification. -/
def localDeltaNL (i : AdaptedOpen f) : Γ(detNL f hf, i.source.1) :=
  letI : Algebra Γ(X, i.base.1) Γ(Y, i.source.1) :=
    (f.appLE i.base i.source i.source_le).hom.toAlgebra
  haveI := algebra_syntomic_appLE hf.2 i.base i.source i.source_le
  haveI : Algebra.QuasiFinite Γ(X, i.base.1) Γ(Y, i.source.1) :=
    AlgebraicGeometry.quasiFinite_appLE hf.1 i.base i.source i.source_le
  (detNLChartEquiv f hf i.base i.source i.source_le).symm
    (Stacks.TateMap.deltaNL Γ(X, i.base.1) Γ(Y, i.source.1))

/-- The hub comparison carries the restriction of the canonical section of a chart to the
canonical section of an adapted open good for it. -/
theorem detNLHub_sections_localDeltaNL (k i : AdaptedOpen f) (hki : k.Good i.source i.base) :
    letI : Algebra Γ(X, k.base.1) Γ(Y, k.source.1) :=
      (f.appLE k.base k.source k.source_le).hom.toAlgebra
    haveI := algebra_syntomic_appLE hf.2 k.base k.source k.source_le
    haveI : Algebra.QuasiFinite Γ(X, k.base.1) Γ(Y, k.source.1) :=
      AlgebraicGeometry.quasiFinite_appLE hf.1 k.base k.source k.source_le
    detNLHub f hf k i hki ((gluedDetNL f hf).sections i k.source.1 hki.le
        ((detNL f hf).presheaf.map (homOfLE hki.le).op (localDeltaNL f hf i))) =
      Stacks.TateMap.deltaNL Γ(X, k.base.1) Γ(Y, k.source.1) := by
  let : Algebra Γ(X, i.base.1) Γ(Y, i.source.1) :=
    (f.appLE i.base i.source i.source_le).hom.toAlgebra
  let : Algebra Γ(X, k.base.1) Γ(Y, k.source.1) :=
    (f.appLE k.base k.source k.source_le).hom.toAlgebra
  let : Algebra Γ(X, i.base.1) Γ(X, k.base.1) :=
    (X.presheaf.map (homOfLE hki.baseLE).op).hom.toAlgebra
  let : Algebra Γ(Y, i.source.1) Γ(Y, k.source.1) :=
    (Y.presheaf.map (homOfLE hki.le).op).hom.toAlgebra
  have := algebra_syntomic_appLE hf.2 i.base i.source i.source_le
  have := algebra_syntomic_appLE hf.2 k.base k.source k.source_le
  have : Algebra.QuasiFinite Γ(X, i.base.1) Γ(Y, i.source.1) :=
    AlgebraicGeometry.quasiFinite_appLE hf.1 i.base i.source i.source_le
  have : Algebra.QuasiFinite Γ(X, k.base.1) Γ(Y, k.source.1) :=
    AlgebraicGeometry.quasiFinite_appLE hf.1 k.base k.source k.source_le
  have h₁ : (gluedDetNL f hf).sections i i.source.1 le_rfl (localDeltaNL f hf i) =
      Stacks.Modules.chartSection i.source (chartDetNL f hf i) i.source.1
        (Stacks.TateMap.deltaNL Γ(X, i.base.1) Γ(Y, i.source.1)) := by
    simp only [localDeltaNL, detNLChartEquiv, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
      LinearEquiv.symm_symm, LinearEquiv.apply_symm_apply]
    rfl
  have h₂ := (gluedDetNL f hf).sections_restrict i i.source.1 k.source.1 le_rfl hki.le
    (localDeltaNL f hf i)
  rw [h₁, Stacks.Modules.chartSection_res] at h₂
  show detNLHub f hf k i hki ((gluedDetNL f hf).sections i k.source.1 (hki.le.trans le_rfl)
    ((gluedDetNL f hf).sheaf.presheaf.map (homOfLE hki.le).op (localDeltaNL f hf i))) = _
  rw [h₂, detNLHub_chartSection]
  exact Stacks.TateMap.detNLBaseChange_delta _

/-- The canonical sections of the charts agree on overlaps. -/
theorem isCompatible_localDeltaNL :
    TopCat.Presheaf.IsCompatible (detNL f hf).presheaf (fun i : AdaptedOpen f ↦ i.source.1)
      (localDeltaNL f hf) := by
  intro i j
  refine (Scheme.Modules.isSheaf (detNL f hf)).section_ext fun y hy ↦ ?_
  obtain ⟨k, hki, hkj, hyk, hkW⟩ := AdaptedOpen.exists_good_pair (f := f)
    (fun m : AdaptedOpen f ↦ m.source) (fun m : AdaptedOpen f ↦ m.base) (fun m ↦ m.source_le)
    i j (i.source.1 ⊓ j.source.1) le_rfl y hy
  refine ⟨k.source.1, hkW, hyk, ?_⟩
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
    ← Functor.map_comp]
  show (detNL f hf).presheaf.map (homOfLE hki.le).op (localDeltaNL f hf i) =
    (detNL f hf).presheaf.map (homOfLE hkj.le).op (localDeltaNL f hf j)
  apply ((gluedDetNL f hf).sections j k.source.1 hkj.le).injective
  rw [(gluedDetNL f hf).sections_comparison k i j hki hkj, detNLComparison,
    LinearEquiv.trans_apply, detNLHub_sections_localDeltaNL, LinearEquiv.symm_apply_eq,
    detNLHub_sections_localDeltaNL]

/-- **The canonical global section `δ(NL_{Y/X})`** of `det(NL_{Y/X})`, glued from the sections
`δ(NL_{B/A})` of the affine charts. -/
def deltaNL : Γ(detNL f hf, ⊤) :=
  (TopCat.Sheaf.existsUnique_gluing'
    (⟨(detNL f hf).presheaf, (detNL f hf).isSheaf⟩ : TopCat.Sheaf Ab (Y : TopCat.{u}))
    (fun i : AdaptedOpen f ↦ i.source.1) ⊤ (fun _ ↦ homOfLE le_top)
    (le_of_eq (iSup_adaptedOpen_source_eq_top f).symm) (localDeltaNL f hf)
    (isCompatible_localDeltaNL f hf)).exists.choose

/-- **`δ(NL_{Y/X})` is `δ(NL_{B/A})` on every affine chart.** -/
theorem detNLChartEquiv_deltaNL (U : X.affineOpens) (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1) :
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
    haveI := algebra_syntomic_appLE hf.2 U V hVU
    haveI : Algebra.QuasiFinite Γ(X, U.1) Γ(Y, V.1) :=
      AlgebraicGeometry.quasiFinite_appLE hf.1 U V hVU
    detNLChartEquiv f hf U V hVU
        ((detNL f hf).presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op (deltaNL f hf)) =
      Stacks.TateMap.deltaNL Γ(X, U.1) Γ(Y, V.1) := by
  have h : (detNL f hf).presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op (deltaNL f hf) =
      localDeltaNL f hf ⟨V, U, hVU⟩ :=
    Exists.choose_spec (p := fun s ↦ ∀ i : AdaptedOpen f, (detNL f hf).presheaf.map
      (homOfLE le_top).op s = localDeltaNL f hf i) _ ⟨V, U, hVU⟩
  rw [h]
  exact LinearEquiv.apply_symm_apply _ _

end AlgebraicGeometry.TateMap

end
