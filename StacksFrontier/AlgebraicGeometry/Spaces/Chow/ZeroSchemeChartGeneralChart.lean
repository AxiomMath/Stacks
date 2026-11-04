module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.InvertibleAffineOpenChartGenerator
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ZeroSchemeChartAffineOpenGerm
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ZeroSchemeChartFiniteLength
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ZeroSchemePreimageModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartIdealSheafPreimage
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stacks 0EQL on an arbitrary good algebraic space

In Situation 0EDT let `X/B` be a good algebraic space, let `ℒ` be an invertible `𝒪_X`-module, let
`s ∈ Γ(X, ℒ)` be a **regular** section and assume `dim_δ(X) ≤ k + 1`.  Writing
`[X]_{k+1} = ∑ n_i [X_i]` over the irreducible components `X_i` of `X` of δ-dimension `k + 1` and
`s_i = s|_{X_i}`, Stacks 0EQL asserts

`[Z(s)]_k = ∑ n_i [Z(s_i)]_k`

as `k`-cycles on `X`.  That is equation 82.18.3.1, Stacks 0EQM.  This file proves it.

The proof reads the identity on a surjective étale scheme chart `V` of `X`, which every
algebraic space has (`AlgebraicGeometry.Space.exists_isSurjectiveChart`), and applies the
scheme-side Stacks 0EPI there.  The chart is not assumed affine and need not trivialise `ℒ`.

## Main results

* `AlgebraicGeometry.Space.ker_componentVanishingLocusChartImmersion_of_isInvertible`: on an
  arbitrary chart, the chart of `Z(s|_W)` is cut out by the equations of `W` and those of `Z(s)`.
* `cycleCoeffOfClosedSubspace_eq_cycleAssociatedToClosedSubscheme_chart_ker`:
  the left-hand side of Stacks 0EQL read on the kernel of the chart base change.
* `cycleCoeffOfClosedSubspace_eq_componentZeroCycleSumCoeff_chart_of_affineOpen`:
  the identity at one chart point, from the local data of Stacks 0EPI on an affine open of the
  chart.
* `AlgebraicGeometry.Space.cycleCoeffOfClosedSubspace_zeroScheme_eq_componentZeroCycleSumCoeff`:
  Stacks 0EQL.

## Implementation notes

Three inputs of Stacks 0EPI are read locally on the chart:

1. the local equation of `Z(s)`, which lives on an affine open around each chart point, by
   `exists_affineOpen_isRegular_ideal_ker_closedSubspaceBaseChangeChartProj_zeroScheme_eq_span`;
2. the bound `dim_δ(Z(s)) ≤ k`, which follows from a nonzerodivisor around each point of the
   support, by `Stacks.Chow.schemeDeltaDimension_subschemeι_le_of_forall_exists_affineOpen`;
3. the identification of the chart of `Z(s|_{X_i})` with the closed subscheme cut out by the
   equations of `X_i` together with those of `Z(s)`.  Here `Z(s|_W)` is the inverse image of
   `Z(s)` along `W → X` (`AlgebraicGeometry.Space.zeroScheme_modulePullback_eq_preimage`), inverse
   images of chart ideal sheaves are compatible by
   `AlgebraicGeometry.Space.comap_idealSheafDataOfChart_of_hom`, and the kernel of the composite of
   the two base-change projections is computed by
   `AlgebraicGeometry.Scheme.ker_comp_eq_sup_of_ker_eq_comap`.

The chart is taken surjective because `AlgebraicGeometry.Space.chartChowSituation` is built from a
dimension function on the chart, and
`AlgebraicGeometry.Space.exists_dimensionFunction_comp_chart` produces one for a surjective chart.

## References

* [Stacks Project, Tag 0EQL](https://stacks.math.columbia.edu/tag/0EQL)
* [Stacks Project, Tag 0EQM](https://stacks.math.columbia.edu/tag/0EQM)
* [Stacks Project, Tag 0EPI](https://stacks.math.columbia.edu/tag/0EPI)
* [Stacks Project, Tag 0845](https://stacks.math.columbia.edu/tag/0845)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The kernel of the projection of the chart base change of a closed subspace is the ideal sheaf
that its defining ideal sheaf induces on the chart. -/
theorem ker_closedSubspaceBaseChangeChartProj_eq_idealSheafDataOfChart
    (X : AlgebraicSpaces B S hS) (Z : ClosedSubspaces B S hS X.1)
    (V : SmallEtale B S hS X.1) :
    (closedSubspaceBaseChangeChartProj B S hS X.2 Z.1 Z.2 V).ker =
      idealSheafDataOfChart B S hS X (definingIdealSheaf B S hS X Z)
        (definingIdealSheaf_isCartesianOnAffineCharts B S hS X Z) V :=
  ker_rep_snd_eq_idealSheafDataOfChart B S hS X Z V

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (L : Modules.{u, u} D.site D.base D.base_mem X hX.1) (s : L.sections)

/-- The chart of `Z(s|_W)` is cut out of an arbitrary chart of `X` by the equations of `W` and
the equations of `Z(s)`.  Let `ℒ` be an invertible `𝒪_X`-module with a global section `s`, let
`W ⊆ X` be an integral closed subspace and let `V` be an étale scheme chart of `X`, **not**
assumed affine.  Then the kernel of the closed immersion `(V ×_X W) ×_W Z(s|_W) ⟶ V` is the sum
of the kernel of `V ×_X W ⟶ V` and the kernel of `V ×_X Z(s) ⟶ V`. -/
@[sga "6 XIII 7.5" "partial"]
theorem ker_componentVanishingLocusChartImmersion_of_isInvertible
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible
      (structureCommRings D.site D.base D.base_mem ⟨X, hX.1⟩)
      (structureRingSheaf D.site D.base D.base_mem ⟨X, hX.1⟩).property L)
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (V : SmallEtale D.site D.base D.base_mem X) :
    (componentVanishingLocusChartImmersion D sX hX L s W V).ker =
      (closedSubspaceBaseChangeChartProj D.site D.base D.base_mem hX.1 W.subspace
          W.isClosedSubspace V).ker ⊔
        (closedSubspaceBaseChangeChartProj D.site D.base D.base_mem hX.1
          (zeroScheme D.site D.base D.base_mem ⟨X, hX.1⟩ L s).1
          (zeroScheme D.site D.base D.base_mem ⟨X, hX.1⟩ L s).2 V).ker := by
  have hci₁ := isClosedImmersion_closedSubspaceBaseChangeChartProj D.site D.base D.base_mem
    hX.1 W.subspace W.isClosedSubspace V
  have hci₂ := isClosedImmersion_closedSubspaceBaseChangeChartProj D.site D.base D.base_mem
    W.isClosedSubspace.1 (componentVanishingLocus D sX hX L s W).1
    (componentVanishingLocus D sX hX L s W).2
    (closedSubspaceBaseChangeChart D.site D.base D.base_mem hX.1 W.subspace
      W.isClosedSubspace V)
  refine AlgebraicGeometry.Scheme.ker_comp_eq_sup_of_ker_eq_comap _ _ _ ?_
  have hcVL : componentVanishingLocus D sX hX L s W =
      preimageClosedSubspace
        (closedSubspaceHom D.site D.base D.base_mem hX.1 W.subspace W.isClosedSubspace)
        (zeroScheme D.site D.base D.base_mem ⟨X, hX.1⟩ L s) :=
    zeroScheme_modulePullback_eq_preimage D.site D.base D.base_mem
      (closedSubspaceHom D.site D.base D.base_mem hX.1 W.subspace W.isClosedSubspace) L s hL
  have key := comap_idealSheafDataOfChart_of_hom
    (closedSubspaceHom D.site D.base D.base_mem hX.1 W.subspace W.isClosedSubspace)
    (zeroScheme D.site D.base D.base_mem ⟨X, hX.1⟩ L s)
    (closedSubspaceBaseChangeChart D.site D.base D.base_mem hX.1 W.subspace
      W.isClosedSubspace V) V
    (closedSubspaceBaseChangeChartDiagram D.site D.base D.base_mem hX.1 W.subspace
      W.isClosedSubspace V).g
    (closedSubspaceBaseChangeChartDiagram D.site D.base D.base_mem hX.1 W.subspace
      W.isClosedSubspace V).comm.symm
  rw [← hcVL] at key
  rw [ker_closedSubspaceBaseChangeChartProj_eq_idealSheafDataOfChart,
    ker_closedSubspaceBaseChangeChartProj_eq_idealSheafDataOfChart]
  exact key.symm

/-! ### The left-hand side of Stacks 0EQL on an arbitrary chart -/

/-- The coefficient of `[Y]_k` read on the ideal-sheaf presentation of the chart base change.  At
a point `v` of a surjective étale scheme chart `V` of `X` over the generic point of an integral
closed subspace `Z ⊆ X`, the coefficient of `Z` in the cycle `[Y]_k` of Stacks 0EE9 of a closed
subspace `Y ⊆ X` is the coefficient of `v` in the cycle of Stacks 02QU of the closed subscheme of
`V` cut out by the kernel of `V ×_X Y ⟶ V`. -/
theorem cycleCoeffOfClosedSubspace_eq_cycleAssociatedToClosedSubscheme_chart_ker
    (Y : Subfunctor X) (hY : IsClosedSubspace D.site D.base D.base_mem Y)
    (hYgood : D.IsGood (Y.ι ≫ sX))
    (V : SmallEtale D.site D.base D.base_mem X)
    (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme D.site D.base D.base_mem))) V.obj.hom)
    (k : ℤ)
    (γ : points D.site D.base D.base_mem Y.toFunctor →
      GeometricPoint D.site D.base D.base_mem Y.toFunctor)
    (hγ : ∀ y, (γ y).image = y)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) (v : chartScheme V)
    (hv : chartSchemeToPoints D.site D.base D.base_mem X V v =
      Z.ambientGenericPoint D.site D.base D.base_mem) :
    haveI hft := locallyOfFiniteType_id_chartChowSituation D sX hX V hs
    cycleCoeffOfClosedSubspace D sX hX Y hY k γ Z =
      (Stacks.Chow.cycleAssociatedToClosedSubscheme (chartChowSituation D sX hX V hs)
        (𝟙 (chartScheme V))
        (closedSubspaceBaseChangeChartProj D.site D.base D.base_mem hX.1 Y hY V).ker.subschemeι
        k).1 v := by
  have hft := locallyOfFiniteType_id_chartChowSituation D sX hX V hs
  have hci := isClosedImmersion_closedSubspaceBaseChangeChartProj D.site D.base D.base_mem
    hX.1 Y hY V
  rw [cycleCoeffOfClosedSubspace_eq_cycleAssociatedToClosedSubscheme_chart D sX hX Y hY hYgood
      V hs k γ hγ Z v hv,
    Stacks.Chow.cycleAssociatedToClosedSubscheme_eq_ker_subschemeι
      (chartChowSituation D sX hX V hs) (𝟙 (chartScheme V))
      (closedSubspaceBaseChangeChartProj D.site D.base D.base_mem hX.1 Y hY V) k]

/-! ### The identity of Stacks 0EQL at a chart point -/

/-- A surjective étale scheme chart is surjective on points of the scheme. -/
private theorem surjective_chartSchemeToPoints_of_surjective_chart
    (hX : D.IsGood sX) (V : SmallEtale D.site D.base D.base_mem X)
    (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme D.site D.base D.base_mem))) V.obj.hom) :
    Function.Surjective (chartSchemeToPoints D.site D.base D.base_mem X V) :=
  surjective_chartSchemeToPoints D.site D.base D.base_mem X V
    ((surjective_iff_surjective_pointsMap D.site D.base D.base_mem X hX.1 V.obj.left
      V.obj.hom).mp hs)

/-- The identity of Stacks 0EQL at a chart point, on an arbitrary surjective chart.  In Situation
0EDT let `X/B` be good, let `ℒ` be an invertible `𝒪_X`-module with a global section `s`, and let
`V` be a surjective étale scheme chart of `X`, not assumed affine and not assumed to trivialise
`ℒ`.  Write `Dz` for the kernel of `V ×_X Z(s) ⟶ V`.  Assume the local hypotheses of
Stacks 0EPI at a point `v` of the chart over the generic point of an integral closed subspace
`Z ⊆ X`: an affine open `U ∋ v` carrying a function `a` whose germ generates the stalk of `Dz`, is
a nonzerodivisor and is not a unit, of finite colength.  Then the coefficient of `Z` in `[Z(s)]_k`
equals the coefficient of `Z` in `∑ n_i [Z(s|_{X_i})]_k`. -/
theorem cycleCoeffOfClosedSubspace_eq_componentZeroCycleSumCoeff_chart_of_affineOpen
    (k : ℤ) (hL : IsInvertibleSheaf D sX hX L)
    (hEgood : D.IsGood ((vanishingLocus D sX hX L s).1.ι ≫ sX))
    (hVLgood : ∀ W : ComponentsOfDeltaDimension D sX hX (k + 1),
      D.IsGood ((componentVanishingLocus D sX hX L s W.1).1.ι ≫ W.1.subspace.ι ≫ sX))
    (V : SmallEtale D.site D.base D.base_mem X)
    (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme D.site D.base D.base_mem))) V.obj.hom)
    (γ : points D.site D.base D.base_mem X → GeometricPoint D.site D.base D.base_mem X)
    (hγ : ∀ x, (γ x).image = x)
    (γW : ComponentGeometricRepresentatives D sX hX L s k)
    (hγW : ∀ (W : ComponentsOfDeltaDimension D sX hX (k + 1)) y, (γW W y).image = y)
    (γZ : points D.site D.base D.base_mem (vanishingLocus D sX hX L s).1.toFunctor →
      GeometricPoint D.site D.base D.base_mem (vanishingLocus D sX hX L s).1.toFunctor)
    (hγZ : ∀ y, (γZ y).image = y)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) (v : chartScheme V)
    (hv : chartSchemeToPoints D.site D.base D.base_mem X V v =
      Z.ambientGenericPoint D.site D.base D.base_mem)
    (hvD : v ∈ (closedSubspaceBaseChangeChartProj D.site D.base D.base_mem hX.1
      (vanishingLocus D sX hX L s).1 (vanishingLocus D sX hX L s).2 V).ker.support)
    (U : (chartScheme V).affineOpens) (hvU : v ∈ U.1) (a : Γ(chartScheme V, U.1))
    (haD : AlgebraicGeometry.IdealSheafData.stalk
        (closedSubspaceBaseChangeChartProj D.site D.base D.base_mem hX.1
          (vanishingLocus D sX hX L s).1 (vanishingLocus D sX hX L s).2 V).ker v =
      Ideal.span {((chartScheme V).presheaf.germ U.1 v hvU).hom a})
    (ha : IsSMulRegular ((chartScheme V).presheaf.stalk v)
      (((chartScheme V).presheaf.germ U.1 v hvU).hom a))
    (ham : ((chartScheme V).presheaf.germ U.1 v hvU).hom a ∈
      IsLocalRing.maximalIdeal ((chartScheme V).presheaf.stalk v))
    (hfinite : Module.length ((chartScheme V).presheaf.stalk v)
      ((chartScheme V).presheaf.stalk v ⧸
        Ideal.span {((chartScheme V).presheaf.germ U.1 v hvU).hom a}) ≠ ⊤) :
    haveI hft := locallyOfFiniteType_id_chartChowSituation D sX hX V hs
    haveI hftD := locallyOfFiniteType_subschemeι_comp_id_chartChowSituation D sX hX V hs
      (closedSubspaceBaseChangeChartProj D.site D.base D.base_mem hX.1
        (vanishingLocus D sX hX L s).1 (vanishingLocus D sX hX L s).2 V).ker
    Stacks.Chow.schemeDeltaDimension (chartChowSituation D sX hX V hs)
        (𝟙 (chartScheme V)) ≤ (k + 1 : EInt) →
    Stacks.Chow.schemeDeltaDimension (chartChowSituation D sX hX V hs)
        ((closedSubspaceBaseChangeChartProj D.site D.base D.base_mem hX.1
          (vanishingLocus D sX hX L s).1 (vanishingLocus D sX hX L s).2 V).ker.subschemeι ≫
            𝟙 (chartScheme V)) ≤ (k : EInt) →
    Stacks.Chow.relativeDimension (chartChowSituation D sX hX V hs).dimensionFunction
        (𝟙 (chartScheme V)) v = k →
    cycleCoeffOfClosedSubspace D sX hX (vanishingLocus D sX hX L s).1
        (vanishingLocus D sX hX L s).2 k γZ Z =
      componentZeroCycleSumCoeff D sX hX L s k γ γW Z := by
  have hft := locallyOfFiniteType_id_chartChowSituation D sX hX V hs
  intro hYdim hDdim hvdim
  classical
  have hsurjpt : Function.Surjective (chartSchemeToPoints D.site D.base D.base_mem X V) :=
    surjective_chartSchemeToPoints_of_surjective_chart D sX hX V hs
  choose wpt hwpt using fun Xi : ComponentsOfDeltaDimension D sX hX (k + 1) =>
    hsurjpt (Xi.1.ambientGenericPoint D.site D.base D.base_mem)
  rw [cycleCoeffOfClosedSubspace_eq_cycleAssociatedToClosedSubscheme_chart_ker D sX hX
      (vanishingLocus D sX hX L s).1 (vanishingLocus D sX hX L s).2 hEgood V hs k γZ hγZ Z v hv,
    cycleAssociatedToClosedSubscheme_eq_finsum_componentsOfDeltaDimension D sX hX V hs k γ hγ
      wpt hwpt (closedSubspaceBaseChangeChartProj D.site D.base D.base_mem hX.1
        (vanishingLocus D sX hX L s).1 (vanishingLocus D sX hX L s).2 V).ker
      v hvD U hvU a haD ha ham hfinite hYdim hDdim hvdim,
    componentZeroCycleSumCoeff_eq_finsum_cycleAssociatedToClosedSubscheme_chart
      D sX hX L s k γ hγ γW hγW hVLgood V hs wpt hwpt Z v hv]
  refine finsum_congr fun Xi => congrArg (fun z : ℤ => _ * z) ?_
  have hci := isClosedImmersion_componentVanishingLocusChartImmersion D sX hX L s Xi.1 V
  rw [Stacks.Chow.cycleAssociatedToClosedSubscheme_eq_ker_subschemeι
      (chartChowSituation D sX hX V hs) (𝟙 (chartScheme V))
      (componentVanishingLocusChartImmersion D sX hX L s Xi.1 V) k,
    ker_componentVanishingLocusChartImmersion_of_isInvertible D sX hX L s hL Xi.1 V]

/-! ### Stacks 0EQL -/

/-- **Stacks 0EQL.**  In Situation 0EDT let `X/B` be good, let `ℒ` be an invertible `𝒪_X`-module,
let `s ∈ Γ(X, ℒ)` be a **regular** section and assume `dim_δ(X) ≤ k + 1`.  Write
`[X]_{k+1} = ∑ n_i [X_i]` with `X_i` the irreducible components of `X` of δ-dimension `k + 1`, and
`s_i = s|_{X_i}`.  Then

`[Z(s)]_k = ∑ n_i [Z(s_i)]_k`

as `k`-cycles on `X`.  This is equation 82.18.3.1, Stacks 0EQM.

The two sides are the coefficient families of
`AlgebraicGeometry.Space.cycleCoeffOfClosedSubspace` at the zero scheme `Z(s)` of Stacks 0845 and
of `AlgebraicGeometry.Space.componentZeroCycleSumCoeff`; the geometric representatives `γ`, `γW`,
`γZ` of the generic points are parameters throughout this library, Lemma 0EE1 being absent from
it, and the equality holds for every choice of them. -/
@[stacks 0EQL "equation 82.18.3.1, which is Stacks 0EQM, is the conclusion: the coefficient family
of [Z(s)]_k of Stacks 0EE9 equals componentZeroCycleSumCoeff, the sum over the irreducible
components X_i of X of δ-dimension k+1 of the pushforward along X_i → X of [Z(s|_{X_i})]_k
weighted by the coefficient n_i of X_i in [X]_{k+1}.  The geometric representatives of the generic
points are the parameters γ, γW, γZ, as throughout this library, Lemma 0EE1 being absent from it;
the equality holds for every choice of them.  The definition of the right-hand side is
componentZeroCycleSumCoeff (StacksFrontier/AlgebraicGeometry/Spaces/Chow/FirstChernClassCap.lean)"]
theorem cycleCoeffOfClosedSubspace_zeroScheme_eq_componentZeroCycleSumCoeff
    (k : ℤ) (hL : IsInvertibleSheaf D sX hX L)
    (hsreg : AlgebraicGeometry.IsRegularSection
      (structureCommRings D.site D.base D.base_mem ⟨X, hX.1⟩)
      (structureRingSheaf D.site D.base D.base_mem ⟨X, hX.1⟩).property s)
    (hdim : deltaDimensionClosed D sX hX Set.univ isClosed_univ ≤ ((k + 1 : ℤ) : EInt))
    (γ : points D.site D.base D.base_mem X → GeometricPoint D.site D.base D.base_mem X)
    (hγ : ∀ x, (γ x).image = x)
    (γW : ComponentGeometricRepresentatives D sX hX L s k)
    (hγW : ∀ (W : ComponentsOfDeltaDimension D sX hX (k + 1)) y, (γW W y).image = y)
    (γZ : points D.site D.base D.base_mem (vanishingLocus D sX hX L s).1.toFunctor →
      GeometricPoint D.site D.base D.base_mem (vanishingLocus D sX hX L s).1.toFunctor)
    (hγZ : ∀ y, (γZ y).image = y) :
    cycleCoeffOfClosedSubspace D sX hX (vanishingLocus D sX hX L s).1
        (vanishingLocus D sX hX L s).2 k γZ =
      componentZeroCycleSumCoeff D sX hX L s k γ γW := by
  classical
  obtain ⟨V, hs⟩ := exists_isSurjectiveChart D.site D.base D.base_mem ⟨X, hX.1⟩
  have hft := locallyOfFiniteType_id_chartChowSituation D sX hX V hs
  have hftD := locallyOfFiniteType_subschemeι_comp_id_chartChowSituation D sX hX V hs
    (closedSubspaceBaseChangeChartProj D.site D.base D.base_mem hX.1
      (vanishingLocus D sX hX L s).1 (vanishingLocus D sX hX L s).2 V).ker
  have hEgood : D.IsGood ((vanishingLocus D sX hX L s).1.ι ≫ sX) :=
    isGood_closedSubspace D sX hX (vanishingLocus D sX hX L s)
  have hVLgood : ∀ W : ComponentsOfDeltaDimension D sX hX (k + 1),
      D.IsGood ((componentVanishingLocus D sX hX L s W.1).1.ι ≫ W.1.subspace.ι ≫ sX) :=
    fun W => isGood_closedSubspace D (W.1.subspace.ι ≫ sX)
      (isGood_integralClosedSubspace D sX hX W.1) (componentVanishingLocus D sX hX L s W.1)
  have hsurjpt : Function.Surjective (chartSchemeToPoints D.site D.base D.base_mem X V) :=
    surjective_chartSchemeToPoints_of_surjective_chart D sX hX V hs
  have hYdim : Stacks.Chow.schemeDeltaDimension (chartChowSituation D sX hX V hs)
      (𝟙 (chartScheme V)) ≤ (((k + 1 : ℤ) : ℤ) : EInt) :=
    schemeDeltaDimension_id_chartChowSituation_le D sX hX V hs (k + 1) hdim
  have hloc : ∀ w : chartScheme V, ∃ (O : (chartScheme V).affineOpens) (_ : w ∈ O.1)
      (a : Γ(chartScheme V, O.1)), a ∈ nonZeroDivisors Γ(chartScheme V, O.1) ∧
        (closedSubspaceBaseChangeChartProj D.site D.base D.base_mem hX.1
          (vanishingLocus D sX hX L s).1 (vanishingLocus D sX hX L s).2 V).ker.ideal O =
          Ideal.span {a} := by
    intro w
    obtain ⟨O, hwO, a, hareg, haspan⟩ :=
      exists_affineOpen_isRegular_ideal_ker_closedSubspaceBaseChangeChartProj_zeroScheme_eq_span
        D.site D.base D.base_mem ⟨X, hX.1⟩ L hL s hsreg V w
    exact ⟨O, hwO, a, mem_nonZeroDivisors_iff_right.2 fun z hz => hareg.left
      (show a * z = a * 0 by rw [mul_zero, mul_comm]; exact hz), haspan⟩
  have hDdim : Stacks.Chow.schemeDeltaDimension (chartChowSituation D sX hX V hs)
      ((closedSubspaceBaseChangeChartProj D.site D.base D.base_mem hX.1
        (vanishingLocus D sX hX L s).1 (vanishingLocus D sX hX L s).2 V).ker.subschemeι ≫
          𝟙 (chartScheme V)) ≤ (k : EInt) := by
    refine Stacks.Chow.schemeDeltaDimension_subschemeι_le_of_forall_exists_affineOpen
      (chartChowSituation D sX hX V hs) (𝟙 (chartScheme V)) _ hYdim fun w _ => ?_
    obtain ⟨O, hwO, a, hanzd, haspan⟩ := hloc w
    exact ⟨O, hwO, a, hanzd, haspan ▸ Ideal.mem_span_singleton_self a⟩
  funext Z
  by_cases hZk : deltaDimension D sX Z = k
  · obtain ⟨v, hv⟩ := hsurjpt (Z.ambientGenericPoint D.site D.base D.base_mem)
    have hvdim : Stacks.Chow.relativeDimension (chartChowSituation D sX hX V hs).dimensionFunction
        (𝟙 (chartScheme V)) v = k :=
      (deltaDimension_eq_relativeDimension_id_chartChowSituation D sX hX V hs Z v hv).symm.trans
        hZk
    by_cases hvD : v ∈ (closedSubspaceBaseChangeChartProj D.site D.base D.base_mem hX.1
        (vanishingLocus D sX hX L s).1 (vanishingLocus D sX hX L s).2 V).ker.support
    · obtain ⟨O, hvO, a, hanzd, haspan⟩ := hloc v
      have ha := AlgebraicGeometry.Scheme.germ_isSMulRegular_stalk O hanzd v hvO
      exact cycleCoeffOfClosedSubspace_eq_componentZeroCycleSumCoeff_chart_of_affineOpen
        D sX hX L s k hL hEgood hVLgood V hs γ hγ γW hγW γZ hγZ Z v hv hvD O hvO a
        (AlgebraicGeometry.IdealSheafData.stalk_eq_span_germ_of_ideal_eq_span hvO haspan)
        ha
        (AlgebraicGeometry.Scheme.germ_mem_maximalIdeal_of_mem_support _ O
          (haspan ▸ Ideal.mem_span_singleton_self a) v hvO hvD)
        (Stacks.Chow.length_quotient_span_germ_stalk_ne_top (chartChowSituation D sX hX V hs)
          (𝟙 (chartScheme V)) hYdim v hvdim O hvO a ha)
        hYdim hDdim hvdim
    · have hLHS : cycleCoeffOfClosedSubspace D sX hX (vanishingLocus D sX hX L s).1
          (vanishingLocus D sX hX L s).2 k γZ Z = 0 := by
        rw [cycleCoeffOfClosedSubspace_eq_cycleAssociatedToClosedSubscheme_chart_ker D sX hX
          (vanishingLocus D sX hX L s).1 (vanishingLocus D sX hX L s).2 hEgood V hs k γZ hγZ
          Z v hv]
        exact Stacks.Chow.cycleAssociatedToClosedSubscheme_apply_eq_zero_of_notMem_range _ _ _
          k (by rwa [Scheme.IdealSheafData.range_subschemeι])
      have hRHS : componentZeroCycleSumCoeff D sX hX L s k γ γW Z = 0 := by
        choose wpt hwpt using fun Xi : ComponentsOfDeltaDimension D sX hX (k + 1) =>
          hsurjpt (Xi.1.ambientGenericPoint D.site D.base D.base_mem)
        rw [componentZeroCycleSumCoeff_eq_finsum_cycleAssociatedToClosedSubscheme_chart
          D sX hX L s k γ hγ γW hγW hVLgood V hs wpt hwpt Z v hv]
        refine finsum_eq_zero_of_forall_eq_zero fun W => mul_eq_zero_of_right _ ?_
        have hci := isClosedImmersion_componentVanishingLocusChartImmersion D sX hX L s W.1 V
        refine Stacks.Chow.cycleAssociatedToClosedSubscheme_apply_eq_zero_of_notMem_range _ _ _
          k fun hmem => ?_
        have h1 : v ∈ (componentVanishingLocusChartImmersion D sX hX L s W.1 V).ker.support := by
          show v ∈ (((componentVanishingLocusChartImmersion D sX hX L s W.1 V).ker.support :
            _) : Set (chartScheme V))
          rw [Scheme.Hom.support_ker]
          exact subset_closure hmem
        rw [ker_componentVanishingLocusChartImmersion_of_isInvertible D sX hX L s hL W.1 V,
          Scheme.IdealSheafData.support_sup] at h1
        exact hvD h1.2
      rw [hLHS, hRHS]
  · rw [cycleCoeffOfClosedSubspace, ite_eq_right hZk,
      componentZeroCycleSumCoeff_eq_zero_of_deltaDimension_ne D sX hX L s k γ γW hZk]

end AlgebraicGeometry.Space

end
