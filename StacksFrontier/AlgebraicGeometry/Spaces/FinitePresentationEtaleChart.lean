module

public import StacksFrontier.AlgebraicGeometry.Descent.Modules.FpqcFinitePresentation
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.Basic
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.FinitePresentationDegreeMinusOne
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyProjectiveEtaleChart

/-!
# Finite presentation of a module on an algebraic space is tested on one étale chart

Let `F` be an algebraic space over a scheme `S` of a big fppf site and let `M` be a
quasi-coherent `𝒪_F`-module.  Restricting `M` to an étale scheme chart `U` gives a sheaf of
modules `M|_U` on the Zariski site of `chartScheme U`
(`AlgebraicGeometry.Space.restrictToChartScheme`), to which the scheme-level notion of finite
presentation applies.  This file proves that the restriction is of finite presentation on *one*
chart whose structure morphism is surjective on points exactly when it is of finite presentation
on *every* chart.

This is the finite-presentation analogue of Stacks 060Q,
`AlgebraicGeometry.Space.exists_surjective_isLocallyProjective_iff_forall` of
`StacksFrontier/AlgebraicGeometry/Spaces/LocallyProjectiveEtaleChart.lean`, with the same proof:
given a surjective chart `U` and an arbitrary chart `V`, the fibre product `U ×_F V` is an étale
chart `W` lying over both, and `chartScheme W ⟶ chartScheme V` is surjective and étale, hence an
fpqc covering.  The restriction `M|_W` is the Zariski pullback of `M|_U`, so it is of finite
presentation, and it is also the pullback of `M|_V`, so Stacks 05B0 descends finite presentation
to `V`.

## Main results

* `AlgebraicGeometry.Space.isFinitePresentation_restrictToChartScheme_of_isSurjective`: the
  passage from one surjective chart to an arbitrary chart.
* `AlgebraicGeometry.Space.exists_surjective_isFinitePresentation_iff_forall`: the two readings
  agree.

## Implementation notes

The three inputs are the ones Stacks 060Q uses, with local projectivity replaced by finite
presentation: stability of finite presentation under pullback of schemes is
`Stacks.AlgebraicGeometry.ModuleLimits.isFinitePresentation_pullback`; the identification of the
restriction to a chart over `U` with the pullback of `M|_U` is
`AlgebraicGeometry.Space.nonempty_pullback_restrictToChartScheme`; and the descent step is
Stacks 05B0, `AlgebraicGeometry.isFinitePresentation_of_pullback_fpqcCover`.  All three are
available for a module quasi-coherent on the small étale site, which is the only condition the
statements below ask of the module.

A single surjective étale morphism of schemes is an fpqc covering by
`AlgebraicGeometry.Space.ofArrows_mem_fpqcPrecoverage_of_surjective_etale`, so the covering used
in the descent has one member and no quasi-compactness is checked.

The module universe is the universe `u` of the schemes, where
`AlgebraicGeometry.Space.restrictToChartScheme` lands in `AlgebraicGeometry.Scheme.Modules` of
the chart.

## References

* [Stacks Project, Tag 060Q](https://stacks.math.columbia.edu/tag/060Q)
* [Stacks Project, Tag 05B0](https://stacks.math.columbia.edu/tag/05B0)
* [Stacks Project, Tag 03M0](https://stacks.math.columbia.edu/tag/03M0)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hZ : IsAlgebraicSpace B S hS Z)

/-- **From one surjective chart to every chart.** If the restriction of a quasi-coherent
`𝒪_Z`-module to one étale chart surjective on points is of finite presentation, then so is its
restriction to every étale chart.

The fibre product `W` of the two charts maps to both; `M|_W` is the Zariski pullback of `M|_A`,
hence of finite presentation, and it is also the pullback of `M|_{A'}` along a surjective étale,
hence fpqc, covering, so Stacks 05B0 descends finite presentation to `A'`. -/
theorem isFinitePresentation_restrictToChartScheme_of_isSurjective
    (M : Modules.{u, u} B S hS Z hZ) (hM : M.IsQuasicoherentOnSite)
    (A : SmallEtale B S hS Z) (hsurj : IsSurjective B S hS A.1.hom)
    (hA : (restrictToChartScheme B S hS Z hZ M A).IsFinitePresentation)
    (A' : SmallEtale B S hS Z) :
    (restrictToChartScheme B S hS Z hZ M A').IsFinitePresentation := by
  obtain ⟨W, a, b, hsurja, hetalea⟩ := exists_chart_over_of_isSurjective B S hS Z hZ A hsurj A'
  obtain ⟨eb⟩ := nonempty_pullback_restrictToChartScheme B S hS ⟨Z, hZ⟩ M hM b
  obtain ⟨ea⟩ := nonempty_pullback_restrictToChartScheme B S hS ⟨Z, hZ⟩ M hM a
  have : (restrictToChartScheme B S hS Z hZ M A).IsFinitePresentation := hA
  have hW : (restrictToChartScheme B S hS Z hZ M W).IsFinitePresentation :=
    SheafOfModules.IsFinitePresentation.of_iso
      (Stacks.AlgebraicGeometry.ModuleLimits.isFinitePresentation_pullback (chartSchemeMap b)
        (restrictToChartScheme B S hS Z hZ M A)) eb
  have : (restrictToChartScheme B S hS Z hZ M A').IsQuasicoherent :=
    isQuasicoherent_restrictToChartScheme B S hS ⟨Z, hZ⟩ M hM A'
  let 𝒰etale : (chartScheme A').Cover.{0} (Scheme.precoverage @Etale) :=
    Scheme.Cover.mkOfCovers PUnit.{1} (fun _ => chartScheme W) (fun _ => chartSchemeMap a)
      (fun y => ⟨PUnit.unit, (hsurja.surj y).choose, (hsurja.surj y).choose_spec⟩)
      (fun _ => hetalea)
  let 𝒰 : (chartScheme A').Cover.{0} Scheme.fpqcPrecoverage :=
    { __ := 𝒰etale.toPreZeroHypercover
      mem₀ := ofArrows_mem_fpqcPrecoverage_of_surjective_etale (chartSchemeMap a) hsurja hetalea }
  exact _root_.AlgebraicGeometry.isFinitePresentation_of_pullback_fpqcCover _ 𝒰
    fun _ => SheafOfModules.IsFinitePresentation.of_iso hW ea.symm

/-- **Finite presentation of a chart restriction may be read on one surjective chart.** The
restriction of a quasi-coherent `𝒪_Z`-module to the Zariski site of an étale chart scheme is of
finite presentation for *some* chart whose structure morphism is surjective on points if and only
if it is of finite presentation for *every* étale chart.

The implication from one chart to all of them is
`AlgebraicGeometry.Space.isFinitePresentation_restrictToChartScheme_of_isSurjective`; the
converse needs only that an algebraic space has a chart surjective on points at all, namely its
atlas. -/
theorem exists_surjective_isFinitePresentation_iff_forall (M : Modules.{u, u} B S hS Z hZ)
    (hM : M.IsQuasicoherentOnSite) :
    (∃ A : SmallEtale B S hS Z, IsSurjective B S hS A.1.hom ∧
        (restrictToChartScheme B S hS Z hZ M A).IsFinitePresentation) ↔
      ∀ A : SmallEtale B S hS Z, (restrictToChartScheme B S hS Z hZ M A).IsFinitePresentation := by
  refine ⟨fun ⟨A, hsurj, hA⟩ =>
    isFinitePresentation_restrictToChartScheme_of_isSurjective B S hS Z hZ M hM A hsurj hA,
    fun h => ?_⟩
  obtain ⟨A, hA⟩ := exists_surjective_smallEtale_chart B S hS Z hZ
  exact ⟨A, hA, h A⟩

end AlgebraicGeometry.Space

end
