module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartIntMulMapPullback
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartGradedIntegerValues
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.AffineVeroneseNaturality

/-!
# The chart-level `θ` of Stacks Tag 01NK is functorial in the scheme, in every integer degree

`StacksFrontier.AlgebraicGeometry.Constructions.ProjChartGradedThetaSchemeFunctoriality` proves
functoriality of the chart-level comparison of [Stacks, Tag 01NK] in the **scheme** for the
natural degrees, where the quotient is taken in the iterated tensor products
`Stacks.TensorPowers.natTensorPow`. This file does the same in **every integer degree**, where
the quotient is `Stacks.TensorPowerDivision.intDivTop` in [Stacks, Tag 01CU]'s family
`Stacks.AmpleProjectiveImmersion.tensorPowerModule` — the family
`Stacks.AlgebraicGeometry.ProjChartGradedDivision.intChartSectionOf`, and so `θ` itself, actually
divides in.

Both halves are needed by the nested compatibility of the relative `θ` of [Stacks, Tag 01O9],
whose datum over an affine `V` of the base is
`…RelativeProjInvertibleMorphism.GradedPowerMap.affineDatum V`: for `Z ≤ V` it compares the
comparison for two graded rings *and* two schemes. The graded-ring half is
`…ProjChartGradedThetaRingFunctoriality.intChartSection_comap`.

## Main results

* `…intPullSection_intPowReindex`: pulling a section back commutes with reindexing the integer
  tensor powers along an equality of degrees.
* `…intValue_pullback`: **the values of the pulled-back datum, in Tag 01CU's family, are the
  pullbacks of the values of `ψ`** — the hypothesis `hψ` transported along
  `Stacks.AlgebraicGeometry.CoherentMulSections.powCompare`.
* `…intChartSectionOf_pullback`: **the section `ψ'(x) / ψ'(f ^ j')` over `V'` is the pullback of
  `ψ(x) / ψ(f ^ j')` over `V`**, on a representative, in every integer degree.
* `…intChartSection_pullback`: **the same for the map `(A_f)_n ⟶ Γ(L ^⊗ n, V)` itself**, with no
  representative in the statement.

## The route

The content is `…ProjChartIntMulMapPullback.intDivTop_intPullSection` — that
`Stacks.TensorPowerDivision.intDivTop` commutes with pullback through the canonical comparison
`…ProjChartIntMulMapPullback.intCompare` of the integer powers — applied at the denominator
`ψ(f ^ j')` and the numerator `ψ(x)`. That statement is unconditional: the comparison `intCompare`
does intertwine the two multiplications in negative degrees, so no hypothesis remains.

Two further crossings are needed here that the natural-degree file does not meet, because
`intChartSectionOf` divides in a *different* family from the one `hψ` speaks about.

* **The transport `powCompare`.** `…ProjChartGradedDivision.intValue` is a value of `ψ` carried
  from `natTensorPow L k` to `tensorPowerModule T L (k : ℤ)`. So `intValue_pullback` needs the
  transport to commute with pullback, which is
  `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.pullPowCompare_eq_powComparePull`, proved
  unconditionally; the comparison `…RelativeProjQcohSheaf.laurentPullback` appearing there **is**
  `…ProjChartIntPullbackMul.intPullIso`, and hence `intCompare`, by `rfl`.
* **The reindexing.** `intChartSectionOf` reads the numerator at a natural-number index and
  transports it to the degree the quotient needs, by
  `Stacks.TensorPowerDivision.intPowReindex`. That transport is defined by substituting the
  equality of degrees, so `intPullSection_intPowReindex` is `subst` followed by `rfl`.

## References

* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj (integerGrading)
open Stacks.TensorPowers (natTensorPow)
open Stacks.NonvanishingOpen (nonvanishingOpen)
open Stacks.GradedLocalization (gradedPiece)
open Stacks.AmpleProjectiveImmersion (tensorPowerModule)
open Stacks.AlgebraicGeometry.CoherentMulSections (powCompare)
open Stacks.AlgebraicGeometry.ProjChartFullGraded (GradedSections)
open Stacks.AlgebraicGeometry.ProjChartGradedDivision (intValue intChartSectionOf intChartSection
  intChartSection_mk exists_int_rep intDivTop_congr_sections le_nonvanishingOpen_intValue_pow)
open Stacks.AlgebraicGeometry.ProjChartRatioPullback (pullSection pullbackNatTensorPowIso
  top_le_preimage_top)
open Stacks.AlgebraicGeometry.ProjChartDivisionPullback (app_pullbackSectionHom)
open Stacks.AlgebraicGeometry.ProjChartIntDivisionPullback (IntCompare intPullSection
  intPullSectionOn)
open Stacks.AlgebraicGeometry.ProjChartIntMulMapPullback (intCompare)
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf (pullPowCompare powComparePull
  pullPowCompare_eq_powComparePull)
open Stacks.TensorPowerDivision (intDivTop intPowReindex)

universe u w

namespace Stacks.AlgebraicGeometry.ProjChartGradedIntThetaSchemeFunctoriality

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {T T' : Scheme.{u}} (j : T' ⟶ T) (L : T.Modules)
  [Stacks.Ample.IsInvertibleModule T L]

/-! ### The comparison family against reindexing -/

/-- **Pulling a section back commutes with reindexing the integer tensor powers.**
`Stacks.TensorPowerDivision.intPowReindex` is the transport along an equality of degrees, so
substituting the equality reduces this to reflexivity. -/
theorem intPullSection_intPowReindex (c : IntCompare j L) {a b : ℤ} (h : a = b)
    (y : Γ(tensorPowerModule T L a, ⊤)) :
    intPullSection j L c b ((intPowReindex L h).hom.app ⊤ y)
      = (intPowReindex ((Scheme.Modules.pullback j).obj L) h).hom.app ⊤
          (intPullSection j L c a y) := by
  subst h
  rfl

/-! ### The values of `ψ` -/

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜] (ψ : GradedSections 𝒜 L)
  (ψ' : GradedSections 𝒜 ((Scheme.Modules.pullback j).obj L))
  (hψ : ∀ (n : ℕ) (a : 𝒜 n), ψ'.toFun n a = pullSection j L n (ψ.toFun n a))

include hψ

/-- **The values of the pulled-back datum, in Tag 01CU's family, are the pullbacks of the values
of `ψ`.**

The hypothesis `hψ` says this for the iterated powers `Stacks.TensorPowers.natTensorPow`, and
`Stacks.AlgebraicGeometry.ProjChartGradedDivision.intValue` is the transport of a value along
`Stacks.AlgebraicGeometry.CoherentMulSections.powCompare`; so what has to be crossed is exactly
that the transport commutes with pullback, which is
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.pullPowCompare_eq_powComparePull`, together with
the naturality `…ProjChartDivisionPullback.app_pullbackSectionHom` of `pullbackSectionHom` in the
module. -/
theorem intValue_pullback (k : ℕ) (p : 𝒜 k) :
    intValue ψ' k p = intPullSection j L (intCompare j L) (k : ℤ) (intValue ψ k p) := by
  have e1 : pullPowCompare j L k
      = (pullbackNatTensorPowIso j L k).inv ≫
        (powCompare ((Scheme.Modules.pullback j).obj L) k).hom := rfl
  have e2 : powComparePull j L k
      = (Scheme.Modules.pullback j).map (powCompare L k).hom ≫ intCompare j L (k : ℤ) := rfl
  have hsq := (e1.symm.trans (pullPowCompare_eq_powComparePull j L k)).trans e2
  have key := ConcreteCategory.congr_hom
    (congrArg (fun m : (Scheme.Modules.pullback j).obj (natTensorPow L k) ⟶
        tensorPowerModule T' ((Scheme.Modules.pullback j).obj L) (k : ℤ) => m.app ⊤) hsq)
    (pullbackSectionHom j (natTensorPow L k) ⊤ ⊤ (top_le_preimage_top j) (ψ.toFun k p))
  simp only at key
  exact (congrArg
      (fun z => (powCompare ((Scheme.Modules.pullback j).obj L) k).hom.app ⊤ z) (hψ k p)).trans
    (key.trans (congrArg (fun z => (intCompare j L (k : ℤ)).app ⊤ z)
      (app_pullbackSectionHom j (powCompare L k).hom ⊤ ⊤ (top_le_preimage_top j)
        (ψ.toFun k p))))

/-! ### The chart sections -/

variable {d : ℕ} {f : A} (hf : f ∈ 𝒜 d) {V : T.Opens}
  (hV : V ≤ nonvanishingOpen T (natTensorPow L d) (ψ.toFun d ⟨f, hf⟩)) {V' : T'.Opens}
  (hVV' : V' ≤ j ⁻¹ᵁ V)
  (hV' : V' ≤ nonvanishingOpen T' (natTensorPow ((Scheme.Modules.pullback j).obj L) d)
    (ψ'.toFun d ⟨f, hf⟩))

include hV hVV' hV'

/-- **The chart section of the pulled-back datum is the pullback of the chart section, in every
integer degree**, on a representative: for `x` homogeneous of degree `e` with `j' d + n = e`, the
section `ψ'(x) / ψ'(f ^ j')` of `(j^*L) ^⊗ n` over `V'` is the pullback of `ψ(x) / ψ(f ^ j')` over
`V`.

The integer-degree counterpart of
`…ProjChartGradedThetaSchemeFunctoriality.chartSectionOf_pullback`. Both values of `ψ'` are
pullbacks of the corresponding values of `ψ` by `intValue_pullback`, the numerator's reindexing
passes by `intPullSection_intPowReindex`, and what is left is
`…ProjChartIntMulMapPullback.intDivTop_intPullSection`. -/
theorem intChartSectionOf_pullback (n : ℤ) (j' e : ℕ)
    (he : ((j' * d : ℕ) : ℤ) + n = (e : ℕ)) {x : A} (hx : x ∈ 𝒜 e) :
    intChartSectionOf ψ' hf hV' n j' e he hx
      = intPullSectionOn j L (intCompare j L) n hVV'
          (intChartSectionOf ψ hf hV n j' e he hx) := by
  set p : 𝒜 (j' * d) := ⟨f ^ j', Stacks.MorphismToProj.HomogeneousRatios.pow_mem hf j'⟩
  have hden := intValue_pullback j L ψ ψ' hψ (j' * d) p
  have hnum : (intPowReindex ((Scheme.Modules.pullback j).obj L) he.symm).hom.app ⊤
        (intValue ψ' e ⟨x, hx⟩)
      = intPullSection j L (intCompare j L) (((j' * d : ℕ) : ℤ) + n)
          ((intPowReindex L he.symm).hom.app ⊤ (intValue ψ e ⟨x, hx⟩)) := by
    rw [intValue_pullback j L ψ ψ' hψ e ⟨x, hx⟩, intPullSection_intPowReindex]
  have hV2 : V' ≤ nonvanishingOpen T'
      (tensorPowerModule T' ((Scheme.Modules.pullback j).obj L) ((j' * d : ℕ) : ℤ))
      (intPullSection j L (intCompare j L) ((j' * d : ℕ) : ℤ) (intValue ψ (j' * d) p)) :=
    hden ▸ le_nonvanishingOpen_intValue_pow ψ' hf hV' j'
  exact (intDivTop_congr_sections hden n hnum
      (le_nonvanishingOpen_intValue_pow ψ' hf hV' j') hV2).trans
    (Stacks.AlgebraicGeometry.ProjChartIntMulMapPullback.intDivTop_intPullSection j L
      (intValue ψ (j' * d) p) n (le_nonvanishingOpen_intValue_pow ψ hf hV j')
      ((intPowReindex L he.symm).hom.app ⊤ (intValue ψ e ⟨x, hx⟩)) hVV' hV2)

/-- **The chart-level comparison of the pulled-back datum is the pullback of that of `ψ`**, in
every integer degree and with no representative in the statement.

Both maps are defined by choice and computed by *any* representative
(`…ProjChartGradedDivision.intChartSection_mk`), so one representative of `y`, which
`…ProjChartGradedDivision.exists_int_rep` supplies, reduces the claim to
`intChartSectionOf_pullback`. -/
theorem intChartSection_pullback (hd : 0 < d) (n : ℤ)
    (y : gradedPiece 𝒜 (integerGrading (S := A) 𝒜) f n) :
    intChartSection ψ' hf hV' hd n y
      = intPullSectionOn j L (intCompare j L) n hVV' (intChartSection ψ hf hV hd n y) := by
  obtain ⟨j', e, he, x, hx, hy⟩ := exists_int_rep hf hd n y
  rw [intChartSection_mk ψ' hf hV' hd n y j' e he x hx hy,
    intChartSection_mk ψ hf hV hd n y j' e he x hx hy,
    intChartSectionOf_pullback j L ψ ψ' hψ hf hV hVV' hV' n j' e he hx]

end Stacks.AlgebraicGeometry.ProjChartGradedIntThetaSchemeFunctoriality

end
