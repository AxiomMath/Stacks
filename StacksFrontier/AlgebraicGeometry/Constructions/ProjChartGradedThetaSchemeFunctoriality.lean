module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartDivisionPullback
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartGradedDivision
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartGradedPullback

/-!
# The chart-level `θ` of Stacks Tag 01NK is functorial in the scheme, in natural degree

`StacksFrontier/AlgebraicGeometry/Constructions/ProjChartGradedThetaRingFunctoriality.lean` proves
that the chart-level comparison of [Stacks, Tag 01NK] is functorial in the **graded ring**: for
`φ : 𝒜 →+*ᵍ ℬ`, the chart section of the pulled-back datum `comap φ ψ` is the chart section of
`ψ` at the image fraction. This file proves functoriality in the **scheme**: for a morphism
`j : T' ⟶ T` and a datum `ψ'` on `(T', j^*L)` whose values are the pullbacks of the values of
`ψ` — the hypothesis `hψ` that
`StacksFrontier/AlgebraicGeometry/Constructions/ProjChartGradedPullback.lean` carries throughout —
the chart section of `ψ'` is the pullback of the chart section of `ψ`.

Both halves are needed by the nested compatibility of the relative `θ` of [Stacks, Tag 01O9],
whose datum over an affine `V` of the base is
`…RelativeProjInvertibleMorphism.GradedPowerMap.affineDatum V`: for `Z ≤ V` it compares the
comparison for two graded rings *and* two schemes.

## Main results

* `…ProjChartGradedThetaSchemeFunctoriality.chartSectionOf_pullback`: **the section
  `ψ'(x) / ψ'(f ^ m)` over `V'` is the pullback of `ψ(x) / ψ(f ^ m)` over `V`**, on a
  representative.
* `…ProjChartGradedThetaSchemeFunctoriality.chartSection_pullback`: **the same for the map
  `(A_f)_n ⟶ Γ(L ^⊗ n, V)` itself**, with no representative in the statement.

## The route

The whole content is
`…ProjChartDivisionPullback.divTop_pullSection` — that `Stacks.TensorPowerDivision.divTop`
commutes with `…ProjChartRatioPullback.pullSection` — applied at the denominator `ψ(f ^ m)` and
the numerator `ψ(x)`. The hypothesis `hψ` rewrites the two values of `ψ'` into pullbacks of
values of `ψ`, which `…ProjChartGradedDivision.divTop_congr_sections` absorbs along with the
nonvanishing proofs, those being propositions. Nothing else enters, and in particular no
multiplicativity of `pullSection` on sections.

## The integer degrees are elsewhere

**This file covers only the natural degrees**, and the integer degrees are now covered too, in
`StacksFrontier/AlgebraicGeometry/Constructions/ProjChartGradedIntThetaSchemeFunctoriality.lean`:
`…ProjChartGradedIntThetaSchemeFunctoriality.intChartSection_pullback` is this file's statement
for `…ProjChartGradedDivision.intChartSection`, over [Stacks, Tag 01CU]'s integer tensor powers,
in every degree of `ℤ`. Together the two give the scheme half of `θ`'s functoriality outright.

The note that stood here said the integer-degree coherence was only *reduced* and that no
comparison was known to intertwine the two multiplications in negative degrees. Both halves were
wrong. `…ProjChartIntMulMapPullback.intCompare_intMulMap` proves the intertwining with no
hypothesis for the canonical comparison `…ProjChartIntPullbackMul.intPullIso` of Tag 01CU's own
powers, in every pair of integer degrees, and
`…ProjChartIntMulMapPullback.intDivTop_intPullSection` is the division coherence with the
hypothesis discharged.

## References

* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj (integerGrading)
open Stacks.TensorPowers (natTensorPow)
open Stacks.NonvanishingOpen (nonvanishingOpen)
open Stacks.GradedLocalization (gradedPiece)
open Stacks.MorphismToProj (HomogeneousRatios)
open Stacks.AlgebraicGeometry.ProjChartFullGraded (GradedSections)
open Stacks.AlgebraicGeometry.ProjChartGradedDivision
open Stacks.AlgebraicGeometry.ProjChartRatioPullback (pullSection)
open Stacks.AlgebraicGeometry.ProjChartDivisionPullback (pullSectionOn divTop_pullSection)

universe u w

namespace Stacks.AlgebraicGeometry.ProjChartGradedThetaSchemeFunctoriality

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜] {T T' : Scheme.{u}} (j : T' ⟶ T) (L : T.Modules)
  [Stacks.Ample.IsInvertibleModule T L] (ψ : GradedSections 𝒜 L)
  (ψ' : GradedSections 𝒜 ((Scheme.Modules.pullback j).obj L))
  (hψ : ∀ (n : ℕ) (a : 𝒜 n), ψ'.toFun n a = pullSection j L n (ψ.toFun n a))
  {d : ℕ} {f : A} (hf : f ∈ 𝒜 d) {V : T.Opens}
  (hV : V ≤ nonvanishingOpen T (natTensorPow L d) (ψ.toFun d ⟨f, hf⟩)) {V' : T'.Opens}
  (hVV' : V' ≤ j ⁻¹ᵁ V)
  (hV' : V' ≤ nonvanishingOpen T' (natTensorPow ((Scheme.Modules.pullback j).obj L) d)
    (ψ'.toFun d ⟨f, hf⟩))

include hψ hV hVV' hV'

/-- **The chart section of the pulled-back datum is the pullback of the chart section**, on a
representative: for `x` homogeneous of degree `m d + n`, the section `ψ'(x) / ψ'(f ^ m)` of
`(j^*L) ^⊗ n` over `V'` is the pullback of the section `ψ(x) / ψ(f ^ m)` of `L ^⊗ n` over `V`.

Both values of `ψ'` are pullbacks of the corresponding values of `ψ` by `hψ`, which
`…ProjChartGradedDivision.divTop_congr_sections` substitutes together with the nonvanishing
proofs; what is left is
`…ProjChartDivisionPullback.divTop_pullSection` at the denominator `ψ(f ^ m)`. -/
public theorem chartSectionOf_pullback (n m : ℕ) {x : A} (hx : x ∈ 𝒜 (m * d + n)) :
    chartSectionOf ψ' hf hV' n m hx
      = pullSectionOn j L n hVV' (chartSectionOf ψ hf hV n m hx) := by
  have hpow : f ^ m ∈ 𝒜 (m * d) := HomogeneousRatios.pow_mem hf m
  have hpv : V' ≤ nonvanishingOpen T'
      (natTensorPow ((Scheme.Modules.pullback j).obj L) (m * d))
      (pullSection j L (m * d) (ψ.toFun (m * d) ⟨f ^ m, hpow⟩)) :=
    (hψ (m * d) ⟨f ^ m, hpow⟩) ▸ ψ'.le_nonvanishingOpen_pow hf hV' m
  exact (divTop_congr_sections (hψ (m * d) ⟨f ^ m, hpow⟩) (hψ (m * d + n) ⟨x, hx⟩)
      (ψ'.le_nonvanishingOpen_pow hf hV' m) hpv).trans
    (divTop_pullSection j L (ψ.toFun (m * d) ⟨f ^ m, hpow⟩)
      (ψ.le_nonvanishingOpen_pow hf hV m) (ψ.toFun (m * d + n) ⟨x, hx⟩) hVV' hpv)

/-- **The chart-level comparison of the pulled-back datum is the pullback of that of `ψ`**, in
every natural degree and with no representative in the statement.

Both maps are defined by choice and computed by *any* representative
(`…ProjChartGradedDivision.chartSection_mk`), so one representative of `y`, which
`…ProjChartGradedDivision.exists_rep` supplies, reduces the claim to
`chartSectionOf_pullback`. -/
public theorem chartSection_pullback (n : ℕ)
    (y : gradedPiece 𝒜 (integerGrading (S := A) 𝒜) f (n : ℤ)) :
    chartSection ψ' hf hV' n y = pullSectionOn j L n hVV' (chartSection ψ hf hV n y) := by
  obtain ⟨m, x, hx, hy⟩ := exists_rep n y hf
  exact ((chartSection_mk ψ' hf hV' n y m x hx hy).trans
      (chartSectionOf_pullback j L ψ ψ' hψ hf hV hVV' hV' n m hx)).trans
    (congrArg (pullSectionOn j L n hVV') (chartSection_mk ψ hf hV n y m x hx hy).symm)

end Stacks.AlgebraicGeometry.ProjChartGradedThetaSchemeFunctoriality

end
