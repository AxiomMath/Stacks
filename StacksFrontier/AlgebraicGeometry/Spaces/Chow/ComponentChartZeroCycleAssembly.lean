module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ComponentChartZeroCycleGrouping
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ComponentZeroCycleChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ChartZeroSchemeSubschemeComparison
public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapPushforward.Finiteness
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stacks 0EQL on a chart: the scheme case regrouped over the components of the space

Let `X/B` be a good algebraic space in Situation 0EDT and let `V` be a surjective étale scheme
chart of `X`. Each irreducible component `W` of the scheme `V` lies over one irreducible component
of `X`, the closure of the image of the generic point of `W`, and several components of `V` can lie
over the same component of `X`. The scheme case Stacks 0EPI on `V` writes the coefficient at a
chart point `v` of the `k`-cycle of a closed subscheme of `V` as a sum over the irreducible
components of `V` of δ-dimension `k + 1`. Grouping its terms by the component of `X` under each
component of `V` rewrites it as a sum over the irreducible components `X_i ⊆ X` of δ-dimension
`k + 1`, the index set of Stacks 0EQL. Reading both sides of Stacks 0EQL on the chart then gives
its local identity at a chart point, given that two closed subschemes of `V` have the same
`k`-cycle.

## Main definitions

* `AlgebraicGeometry.Space.ambientComponentOfChartComponent`: the irreducible component of `|X|`
  under an irreducible component of the chart scheme.
* `AlgebraicGeometry.Space.integralComponentOfChartComponent`: the same component of `X`, as an
  integral closed subspace.

## Main results

* `Stacks.Chow.finsum_eq_finsum_finsum_subtype_fiber`: a finitely supported sum regrouped over the
  fibres of a map, with the fibres as subtypes.
* `AlgebraicGeometry.finite_irreducibleComponents_mem_of_isLocallyNoetherian`: a point of a
  locally Noetherian scheme lies on finitely many irreducible components.
* `AlgebraicGeometry.Space.integralComponentOfChartComponent_eq_iff_subset_preimage`: a component
  of the chart lies over an irreducible component `Z` of `X` exactly when `Z` is the component
  attached to it.
* `AlgebraicGeometry.Space.cycleAssociatedToClosedSubscheme_eq_finsum_componentsOfDeltaDimension`:
  the scheme case Stacks 0EPI on the chart, regrouped over the components of `X`.
* `AlgebraicGeometry.Space.cycleCoeffOfClosedSubspace_eq_componentZeroCycleSumCoeff_chart`: the
  local identity of Stacks 0EQL at a chart point, given the identification `hident` of two closed
  subschemes of the chart.

## References

* [Stacks Project, Tag 00ET](https://stacks.math.columbia.edu/tag/00ET)
* [Stacks Project, Tag 02QU](https://stacks.math.columbia.edu/tag/02QU)
* [Stacks Project, Tag 0845](https://stacks.math.columbia.edu/tag/0845)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EE8](https://stacks.math.columbia.edu/tag/0EE8)
* [Stacks Project, Tag 0EE9](https://stacks.math.columbia.edu/tag/0EE9)
* [Stacks Project, Tag 0ENF](https://stacks.math.columbia.edu/tag/0ENF)
* [Stacks Project, Tag 0EPI](https://stacks.math.columbia.edu/tag/0EPI)
* [Stacks Project, Tag 0EPZ](https://stacks.math.columbia.edu/tag/0EPZ)
* [Stacks Project, Tag 0EQL](https://stacks.math.columbia.edu/tag/0EQL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-- **A finitely supported sum is the sum over the fibres of any map out of its index type.**
The inner sums are indexed by the fibre as a subtype; the version with the fibre as a subset is
`Stacks.Chow.finsum_finsum_mem_fiber`. -/
theorem finsum_eq_finsum_finsum_subtype_fiber {α β M : Type*} [AddCommMonoid M]
    (f : α → β) (G : α → M) (hG : (Function.support G).Finite) :
    (∑ᶠ a : α, G a) = ∑ᶠ b : β, ∑ᶠ a : {a : α // f a = b}, G a.1 :=
  ((finsum_congr fun b => finsum_set_coe_eq_finsum_mem (f ⁻¹' {b})).trans
    (finsum_finsum_mem_fiber f G hG)).symm

end Stacks.Chow

namespace AlgebraicGeometry

/-- **The irreducible components of a locally Noetherian scheme through a point are finite in
number.** -/
@[ega "0 14.2.6" "(i), special case", ega "IV 13.2.6" "more general"]
theorem finite_irreducibleComponents_mem_of_isLocallyNoetherian {Y : Scheme.{u}}
    [IsLocallyNoetherian Y] (x : Y) :
    {C : irreducibleComponents Y | x ∈ (C : Set Y)}.Finite := by
  have _ : IsNoetherianRing (Y.presheaf.stalk x) := inferInstance
  have _ : Finite (minimalPrimes (Y.presheaf.stalk x)) :=
    (minimalPrimes.finite_of_isNoetherianRing (Y.presheaf.stalk x)).to_subtype
  have _ : Finite {p : PrimeSpectrum (Y.presheaf.stalk x) //
      p.asIdeal ∈ minimalPrimes (Y.presheaf.stalk x)} :=
    Finite.of_injective
      (fun p => (⟨p.1.asIdeal, p.2⟩ : (minimalPrimes (Y.presheaf.stalk x) : Set _)))
      fun p q h => Subtype.ext (PrimeSpectrum.ext (congrArg Subtype.val h))
  exact Set.finite_coe_iff.mp
    (Finite.of_equiv _ (irreducibleComponentsEquivMinimalPrimes x).symm)

end AlgebraicGeometry

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- **The inclusion of a closed subscheme of a chart, followed by the identity, is locally of
finite type for the base situation `AlgebraicGeometry.Space.chartChowSituation` on the chart.** -/
theorem locallyOfFiniteType_subschemeι_comp_id_chartChowSituation
    (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (V : SmallEtale D.site D.base D.base_mem X)
    (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme D.site D.base D.base_mem))) V.obj.hom)
    (E : (chartScheme V).IdealSheafData) :
    haveI := locallyOfFiniteType_id_chartChowSituation D sX hX V hs
    @LocallyOfFiniteType _ (chartChowSituation D sX hX V hs).S
      (E.subschemeι ≫ 𝟙 (chartScheme V)) :=
  have := locallyOfFiniteType_id_chartChowSituation D sX hX V hs
  inferInstanceAs (LocallyOfFiniteType (E.subschemeι ≫ 𝟙 (chartScheme V)))

/-! ### The component of the space under a component of a chart -/

/-- A component of the chart lies over a component `T` of `|X|` iff `T` is the closure of the image
of its generic point, for a good space. -/
private theorem subset_preimage_iff_closure_singleton_of_isGood
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (V : SmallEtale D.site D.base D.base_mem X)
    (W : irreducibleComponents (chartScheme V)) {T : Set (points D.site D.base D.base_mem X)}
    (hT : T ∈ irreducibleComponents (points D.site D.base D.base_mem X)) :
    (W.1 : Set (chartScheme V)) ⊆ chartSchemeToPoints D.site D.base D.base_mem X V ⁻¹' T ↔
      closure
        ({chartSchemeToPoints D.site D.base D.base_mem X V (genericPoints.ofComponent W).1} :
          Set (points D.site D.base D.base_mem X)) = T :=
  subset_preimage_iff_closure_singleton_chartSchemeToPoints_eq D.site D.base D.base_mem hX.1
    (D.isDecentSpace_of_isGood sX hX) V W hT

/-- **The generic point of a component of the chart lying over an integral closed subspace whose
point set is an irreducible component of `|X|` lies over the generic point of that subspace.** -/
theorem chartSchemeToPoints_ofComponent_eq_ambientGenericPoint
    (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hZcomp : subspacePointSet D.site D.base D.base_mem X Z.subspace ∈
      irreducibleComponents (points D.site D.base D.base_mem X))
    (V : SmallEtale D.site D.base D.base_mem X)
    (W : irreducibleComponents (chartScheme V))
    (hW : (W.1 : Set (chartScheme V)) ⊆ chartSchemeToPoints D.site D.base D.base_mem X V ⁻¹'
      subspacePointSet D.site D.base D.base_mem X Z.subspace) :
    chartSchemeToPoints D.site D.base D.base_mem X V (genericPoints.ofComponent W).1 =
      Z.ambientGenericPoint D.site D.base D.base_mem := by
  have hdec : IsDecentSpace D.site D.base D.base_mem X := D.isDecentSpace_of_isGood sX hX
  have _ : T0Space (points D.site D.base D.base_mem X) :=
    t0Space_points_of_isDecentSpace D.site D.base D.base_mem hX.1 hdec
  exact (show IsGenericPoint (chartSchemeToPoints D.site D.base D.base_mem X V
        (genericPoints.ofComponent W).1)
        (subspacePointSet D.site D.base D.base_mem X Z.subspace) from
      (subset_preimage_iff_closure_singleton_of_isGood D sX hX V W hZcomp).mp hW).eq
    (Z.isGenericPoint_ambientGenericPoint D.site D.base D.base_mem hX.1)

/-- The irreducible component of `|X|` under an irreducible component of the scheme of an étale
chart: the closure of the image of its generic point. -/
def ambientComponentOfChartComponent (V : SmallEtale D.site D.base D.base_mem X)
    (W : irreducibleComponents (chartScheme V)) :
    IrreducibleCloseds (points D.site D.base D.base_mem X) where
  carrier := closure
    ({chartSchemeToPoints D.site D.base D.base_mem X V (genericPoints.ofComponent W).1} :
      Set (points D.site D.base D.base_mem X))
  isIrreducible' := isIrreducible_singleton.closure
  isClosed' := isClosed_closure

/-- The set of points attached to a component of the chart is an irreducible component of
`|X|`. -/
theorem mem_irreducibleComponents_ambientComponentOfChartComponent
    (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (V : SmallEtale D.site D.base D.base_mem X)
    (W : irreducibleComponents (chartScheme V)) :
    (ambientComponentOfChartComponent D V W :
        Set (points D.site D.base D.base_mem X)) ∈
      irreducibleComponents (points D.site D.base D.base_mem X) :=
  mem_irreducibleComponents_closure_singleton_chartSchemeToPoints D.site D.base D.base_mem
    hX.1 (D.isDecentSpace_of_isGood sX hX) V W

/-- The irreducible component of `X`, as an integral closed subspace, under an irreducible
component of the scheme of an étale chart. -/
def integralComponentOfChartComponent (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (V : SmallEtale D.site D.base D.base_mem X)
    (W : irreducibleComponents (chartScheme V)) :
    IntegralClosedSubspace D.site D.base D.base_mem X :=
  integralClosedSubspaceOfPoints D.site D.base D.base_mem hX.1
    (D.isDecentSpace_of_isGood sX hX) (ambientComponentOfChartComponent D V W)

/-- The set of points of the component of `X` attached to a component `W` of the chart is the
closure of the image of the generic point of `W`. -/
@[simp]
theorem subspacePointSet_integralComponentOfChartComponent
    (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (V : SmallEtale D.site D.base D.base_mem X)
    (W : irreducibleComponents (chartScheme V)) :
    subspacePointSet D.site D.base D.base_mem X
        (integralComponentOfChartComponent D sX hX V W).subspace =
      closure
        ({chartSchemeToPoints D.site D.base D.base_mem X V (genericPoints.ofComponent W).1} :
          Set (points D.site D.base D.base_mem X)) :=
  subspacePointSet_integralClosedSubspaceOfPoints D.site D.base D.base_mem hX.1
    (D.isDecentSpace_of_isGood sX hX) (ambientComponentOfChartComponent D V W)

/-- **The subspace attached to a component of the chart is an irreducible component of `X`** in
the sense of Stacks 0EE8: an integral closed subspace whose set of points is an irreducible
component of `|X|`. -/
theorem isIrreducibleComponent_integralComponentOfChartComponent
    (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (V : SmallEtale D.site D.base D.base_mem X)
    (W : irreducibleComponents (chartScheme V)) :
    IsIrreducibleComponent D.site D.base D.base_mem hX.1
      (integralComponentOfChartComponent D sX hX V W).subspace := by
  have hpts : subspacePointSet D.site D.base D.base_mem X
      (integralComponentOfChartComponent D sX hX V W).subspace ∈
      irreducibleComponents (points D.site D.base D.base_mem X) := by
    rw [subspacePointSet_integralComponentOfChartComponent D sX hX V W]
    exact mem_irreducibleComponents_ambientComponentOfChartComponent D sX hX V W
  exact ⟨(integralComponentOfChartComponent D sX hX V W).isClosedSubspace,
    (integralComponentOfChartComponent D sX hX V W).isIntegralSpace, hpts⟩

/-- A component of the chart lies over the component of `X` attached to it. -/
theorem subset_preimage_integralComponentOfChartComponent
    (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (V : SmallEtale D.site D.base D.base_mem X)
    (W : irreducibleComponents (chartScheme V)) :
    (W.1 : Set (chartScheme V)) ⊆ chartSchemeToPoints D.site D.base D.base_mem X V ⁻¹'
      subspacePointSet D.site D.base D.base_mem X
        (integralComponentOfChartComponent D sX hX V W).subspace :=
  (subset_preimage_iff_closure_singleton_of_isGood D sX hX V W
      ((subspacePointSet_integralComponentOfChartComponent D sX hX V W) ▸
        mem_irreducibleComponents_ambientComponentOfChartComponent D sX hX V W)).mpr
    (subspacePointSet_integralComponentOfChartComponent D sX hX V W).symm

/-- **A component of the chart lies over an irreducible component `Z` of `X` exactly when `Z` is
the component attached to it.** That is, the components of the chart lying over `Z` form the
fibre of `AlgebraicGeometry.Space.integralComponentOfChartComponent` over `Z`. -/
theorem integralComponentOfChartComponent_eq_iff_subset_preimage
    (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (V : SmallEtale D.site D.base D.base_mem X)
    (W : irreducibleComponents (chartScheme V))
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hZcomp : subspacePointSet D.site D.base D.base_mem X Z.subspace ∈
      irreducibleComponents (points D.site D.base D.base_mem X)) :
    integralComponentOfChartComponent D sX hX V W = Z ↔
      (W.1 : Set (chartScheme V)) ⊆ chartSchemeToPoints D.site D.base D.base_mem X V ⁻¹'
        subspacePointSet D.site D.base D.base_mem X Z.subspace := by
  refine ⟨fun h => h ▸ subset_preimage_integralComponentOfChartComponent D sX hX V W,
    fun hsub => ?_⟩
  refine (eq_integralClosedSubspaceOfPoints D.site D.base D.base_mem hX.1
    (D.isDecentSpace_of_isGood sX hX) Z (ambientComponentOfChartComponent D V W) ?_).symm
  exact ((subset_preimage_iff_closure_singleton_of_isGood D sX hX V W hZcomp).mp hsub).symm

/-! ### The outer regrouping -/

/-- **The scheme case Stacks 0EPI on a chart, regrouped over the irreducible components of the
space.** Let `X/B` be a good algebraic space, let `V` be a surjective étale scheme chart of `X`
of δ-dimension at most `k + 1`, and let `Dz` be an ideal sheaf on the chart scheme cutting out a
closed subscheme of δ-dimension at most `k` which is generated at a point `v` of relative
dimension `k` by a nonzerodivisor of finite colength. Then the coefficient at `v` of the
`k`-cycle of Stacks 02QU of `Dz` is the sum, over the irreducible components `X_i ⊆ X` of
δ-dimension `k + 1`, of the multiplicity of `X_i` in `[X]_{k+1}` — read on the chart at a point
`wpt X_i` over the generic point of `X_i` — times the coefficient at `v` of the `k`-cycle of the
closed subscheme `(V ×_X X_i) ∩ Dz` of the chart. -/
theorem cycleAssociatedToClosedSubscheme_eq_finsum_componentsOfDeltaDimension
    (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (V : SmallEtale D.site D.base D.base_mem X)
    (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme D.site D.base D.base_mem))) V.obj.hom)
    (k : ℤ)
    (γ : points D.site D.base D.base_mem X → GeometricPoint D.site D.base D.base_mem X)
    (hγ : ∀ x, (γ x).image = x)
    (wpt : ComponentsOfDeltaDimension D sX hX (k + 1) → chartScheme V)
    (hwpt : ∀ W, chartSchemeToPoints D.site D.base D.base_mem X V (wpt W) =
      W.1.ambientGenericPoint D.site D.base D.base_mem)
    (Dz : (chartScheme V).IdealSheafData) (v : chartScheme V)
    (hvD : v ∈ Dz.support)
    (U : (chartScheme V).affineOpens) (hvU : v ∈ U.1) (a : Γ(chartScheme V, U.1))
    (haD : AlgebraicGeometry.IdealSheafData.stalk Dz v =
      Ideal.span {((chartScheme V).presheaf.germ U.1 v hvU).hom a})
    (ha : IsSMulRegular ((chartScheme V).presheaf.stalk v)
      (((chartScheme V).presheaf.germ U.1 v hvU).hom a))
    (ham : ((chartScheme V).presheaf.germ U.1 v hvU).hom a ∈
      IsLocalRing.maximalIdeal ((chartScheme V).presheaf.stalk v))
    (hfinite : Module.length ((chartScheme V).presheaf.stalk v)
      ((chartScheme V).presheaf.stalk v ⧸
        Ideal.span {((chartScheme V).presheaf.germ U.1 v hvU).hom a}) ≠ ⊤) :
    haveI := locallyOfFiniteType_id_chartChowSituation D sX hX V hs
    haveI : @LocallyOfFiniteType _ (chartChowSituation D sX hX V hs).S
        (Dz.subschemeι ≫ 𝟙 (chartScheme V)) :=
      inferInstanceAs (LocallyOfFiniteType (Dz.subschemeι ≫ 𝟙 (chartScheme V)))
    Stacks.Chow.schemeDeltaDimension (chartChowSituation D sX hX V hs)
        (𝟙 (chartScheme V)) ≤ (k + 1 : EInt) →
    Stacks.Chow.schemeDeltaDimension (chartChowSituation D sX hX V hs)
        (Dz.subschemeι ≫ 𝟙 (chartScheme V)) ≤ (k : EInt) →
    Stacks.Chow.relativeDimension (chartChowSituation D sX hX V hs).dimensionFunction
        (𝟙 (chartScheme V)) v = k →
    (Stacks.Chow.cycleAssociatedToClosedSubscheme (chartChowSituation D sX hX V hs)
        (𝟙 (chartScheme V)) Dz.subschemeι k).1 v =
      ∑ᶠ Xi : ComponentsOfDeltaDimension D sX hX (k + 1),
        (Stacks.Chow.cycleAssociatedToClosedSubscheme (chartChowSituation D sX hX V hs)
            (𝟙 (chartScheme V)) (𝟙 (chartScheme V)) (k + 1)).1 (wpt Xi) *
          (Stacks.Chow.cycleAssociatedToClosedSubscheme (chartChowSituation D sX hX V hs)
            (𝟙 (chartScheme V))
            (((closedSubspaceBaseChangeChartProj D.site D.base D.base_mem hX.1 Xi.1.subspace
              Xi.1.isClosedSubspace V).ker ⊔ Dz).subschemeι) k).1 v := by
  have hft := locallyOfFiniteType_id_chartChowSituation D sX hX V hs
  have hftD := locallyOfFiniteType_subschemeι_comp_id_chartChowSituation D sX hX V hs Dz
  intro hYdim hDdim hvdim
  classical
  have hLN : IsLocallyNoetherian (chartScheme V) :=
    isLocallyNoetherian_chartScheme_of_isGood D sX hX V
  have hdimA : ∀ W : irreducibleComponents (chartScheme V),
      Stacks.Chow.deltaDimension (chartChowSituation D sX hX V hs) (𝟙 (chartScheme V))
          ⟨W.1, W.2.1, isClosed_of_mem_irreducibleComponents W.1 W.2⟩ = k + 1 →
        deltaDimension D sX (integralComponentOfChartComponent D sX hX V W) = k + 1 :=
    fun W hW => (deltaDimension_eq_of_subset_preimage_subspacePointSet D sX hX
      (integralComponentOfChartComponent D sX hX V W)
      (isIrreducibleComponent_integralComponentOfChartComponent D sX hX V W).2.2 V hs W
      (subset_preimage_integralComponentOfChartComponent D sX hX V W)).symm.trans hW
  have hdimS : ∀ (Xi : ComponentsOfDeltaDimension D sX hX (k + 1))
      (W : irreducibleComponents (chartScheme V)),
      (W.1 : Set (chartScheme V)) ⊆ chartSchemeToPoints D.site D.base D.base_mem X V ⁻¹'
          subspacePointSet D.site D.base D.base_mem X Xi.1.subspace →
        Stacks.Chow.deltaDimension (chartChowSituation D sX hX V hs) (𝟙 (chartScheme V))
          ⟨W.1, W.2.1, isClosed_of_mem_irreducibleComponents W.1 W.2⟩ = k + 1 :=
    fun Xi W hW => (deltaDimension_eq_of_subset_preimage_subspacePointSet D sX hX Xi.1
      Xi.2.1.2.2 V hs W hW).trans Xi.2.2
  have hvanish : ∀ W : irreducibleComponents (chartScheme V), v ∉ (W.1 : Set (chartScheme V)) →
      (Stacks.Chow.cycleAssociatedToClosedSubscheme (chartChowSituation D sX hX V hs)
        (𝟙 (chartScheme V))
        ((Scheme.IdealSheafData.vanishingIdeal
          ⟨W.1, isClosed_of_mem_irreducibleComponents W.1 W.2⟩ ⊔ Dz).subschemeι) k).1 v = 0 := by
    intro W hvW
    refine Stacks.Chow.cycleAssociatedToClosedSubscheme_apply_eq_zero _ _ _ _ _ ?_
    rintro ⟨ξ, hξ, -⟩
    refine hvW ?_
    have hx : v ∈ (Scheme.IdealSheafData.vanishingIdeal
        ⟨W.1, isClosed_of_mem_irreducibleComponents W.1 W.2⟩ ⊔ Dz).support := by
      show v ∈ (_ : Set (chartScheme V))
      rw [← Scheme.IdealSheafData.range_subschemeι]
      exact ⟨ξ.1, hξ⟩
    rw [Scheme.IdealSheafData.support_sup] at hx
    have hxI : v ∈ (_ : Set (chartScheme V)) := hx.1
    rwa [Scheme.IdealSheafData.coe_support_vanishingIdeal] at hxI
  have hmult : ∀ (Xi : ComponentsOfDeltaDimension D sX hX (k + 1))
      (W : irreducibleComponents (chartScheme V)),
      (W.1 : Set (chartScheme V)) ⊆ chartSchemeToPoints D.site D.base D.base_mem X V ⁻¹'
          subspacePointSet D.site D.base D.base_mem X Xi.1.subspace →
        (Stacks.Chow.cycleAssociatedToClosedSubscheme (chartChowSituation D sX hX V hs)
            (𝟙 (chartScheme V)) (𝟙 (chartScheme V)) (k + 1)).1
              (genericPoints.ofComponent W).1 =
          (Stacks.Chow.cycleAssociatedToClosedSubscheme (chartChowSituation D sX hX V hs)
            (𝟙 (chartScheme V)) (𝟙 (chartScheme V)) (k + 1)).1 (wpt Xi) := by
    intro Xi W hW
    have h1 := fundamentalCycleCoeff_eq_cycleAssociatedToClosedSubscheme_id_chart D sX hX V hs
      (k + 1) γ hγ Xi.1 (wpt Xi) (hwpt Xi)
    have h2 := fundamentalCycleCoeff_eq_cycleAssociatedToClosedSubscheme_id_chart D sX hX V hs
      (k + 1) γ hγ Xi.1 (genericPoints.ofComponent W).1
      (chartSchemeToPoints_ofComponent_eq_ambientGenericPoint D sX hX Xi.1 Xi.2.1.2.2 V W hW)
    exact h2.symm.trans h1
  rw [Stacks.Chow.cycleAssociatedToClosedSubscheme_apply_eq_length_quotient_idealStalk
      (chartChowSituation D sX hX V hs) (𝟙 (chartScheme V)) Dz hDdim v hvD hvdim, haD,
    Stacks.Chow.length_quotient_eq_sum_components (chartChowSituation D sX hX V hs)
      (𝟙 (chartScheme V)) Dz k hYdim hDdim v hvD hvdim U hvU a haD ha ham hfinite]
  refine Eq.trans (Stacks.Chow.finsum_eq_finsum_finsum_subtype_fiber
    (fun W : {W : irreducibleComponents (chartScheme V) //
        Stacks.Chow.deltaDimension (chartChowSituation D sX hX V hs) (𝟙 (chartScheme V))
          ⟨W.1, W.2.1, isClosed_of_mem_irreducibleComponents W.1 W.2⟩ = k + 1} =>
      (⟨integralComponentOfChartComponent D sX hX V W.1,
        isIrreducibleComponent_integralComponentOfChartComponent D sX hX V W.1,
        hdimA W.1 W.2⟩ : ComponentsOfDeltaDimension D sX hX (k + 1)))
    (fun W => (Stacks.Chow.cycleAssociatedToClosedSubscheme (chartChowSituation D sX hX V hs)
          (𝟙 (chartScheme V)) (𝟙 (chartScheme V)) (k + 1)).1 W.1.2.1.genericPoint *
        (Stacks.Chow.cycleAssociatedToClosedSubscheme (chartChowSituation D sX hX V hs)
          (𝟙 (chartScheme V))
          ((Scheme.IdealSheafData.vanishingIdeal
            ⟨W.1.1, isClosed_of_mem_irreducibleComponents W.1.1 W.1.2⟩ ⊔ Dz).subschemeι) k).1 v)
    ?_) ?_
  · refine Set.Finite.subset (Set.Finite.preimage (f := fun W : {W : irreducibleComponents
        (chartScheme V) // Stacks.Chow.deltaDimension (chartChowSituation D sX hX V hs)
          (𝟙 (chartScheme V)) ⟨W.1, W.2.1, isClosed_of_mem_irreducibleComponents W.1 W.2⟩ =
            k + 1} => W.1)
      (Subtype.val_injective.injOn)
      (finite_irreducibleComponents_mem_of_isLocallyNoetherian v)) ?_
    intro W hW
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    by_contra hvW
    exact Function.mem_support.1 hW (mul_eq_zero_of_right _ (hvanish W.1 hvW))
  refine finsum_congr fun Xi => ?_
  rw [cycleAssociatedToClosedSubscheme_componentChart_sup_eq_finsum D sX hX Xi.1 Xi.2.1.2.2 V hs
      Dz k v hvD U hvU a haD ha ham hfinite hYdim hDdim hvdim,
    mul_finsum]
  refine finsum_eq_of_bijective (fun W =>
    (⟨W.1.1, (integralComponentOfChartComponent_eq_iff_subset_preimage
      D sX hX V W.1.1 Xi.1 Xi.2.1.2.2).mp (congrArg Subtype.val W.2)⟩ :
      {W : irreducibleComponents (chartScheme V) //
        (W.1 : Set (chartScheme V)) ⊆ chartSchemeToPoints D.site D.base D.base_mem X V ⁻¹'
          subspacePointSet D.site D.base D.base_mem X Xi.1.subspace}))
    ⟨?_, ?_⟩ ?_
  · intro W W' h
    have h1 := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext h1)
  · intro W
    exact ⟨⟨⟨W.1, hdimS Xi W.1 W.2⟩, Subtype.ext
      ((integralComponentOfChartComponent_eq_iff_subset_preimage D sX hX V W.1 Xi.1
        Xi.2.1.2.2).mpr W.2)⟩, Subtype.ext rfl⟩
  · intro W
    exact congrArg (fun z : ℤ => z * _) (hmult Xi W.1.1
      ((integralComponentOfChartComponent_eq_iff_subset_preimage D sX hX V W.1.1 Xi.1
        Xi.2.1.2.2).mp (congrArg Subtype.val W.2)))

/-! ### The local identity of Stacks 0EQL on a chart -/

/-- **The local identity of Stacks 0EQL at a chart point, modulo one identification of closed
subschemes of the chart.** In Situation 0EDT let `X/B` be good, let `ℒ` be an invertible
`𝒪_X`-module with a global section `s`, let `V` be a surjective affine étale scheme chart of `X`,
let `Z ⊆ X` be an integral closed subspace and let `v` be a point of the chart over the generic
point of `Z`. Assume the local hypotheses of Stacks 0EPI at `v` for the closed subscheme of `V`
cut out by the evaluation ideal of `s`, and assume `hident`: for every irreducible component
`X_i ⊆ X` of δ-dimension `k + 1`, the chart `(V ×_X X_i) ×_{X_i} Z(s|_{X_i})` of `Z(s|_{X_i})`,
read as a closed subscheme of `V` through
`AlgebraicGeometry.Space.componentVanishingLocusChartImmersion`, has the same coefficient at `v` in
its `k`-cycle as the closed subscheme of `V` cut out by the sum of the ideal sheaf of `V ×_X X_i`
and the evaluation ideal of `s`. Then the coefficient of `Z` in the `k`-cycle `[Z(s)]_k` of Stacks
0EE9 equals the coefficient of `Z` in `∑ n_i [Z(s|_{X_i})]_k`, which is the identity of Stacks 0EQL
at `Z`. -/
theorem cycleCoeffOfClosedSubspace_eq_componentZeroCycleSumCoeff_chart
    (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (L : Modules.{u, u} D.site D.base D.base_mem X hX.1) (s : L.sections) (k : ℤ)
    (hL : IsInvertibleSheaf D sX hX L)
    (hEgood : D.IsGood ((vanishingLocus D sX hX L s).1.ι ≫ sX))
    (hVLgood : ∀ W : ComponentsOfDeltaDimension D sX hX (k + 1),
      D.IsGood ((componentVanishingLocus D sX hX L s W.1).1.ι ≫ W.1.subspace.ι ≫ sX))
    (V : SmallEtale D.site D.base D.base_mem X) [IsAffine (chartScheme V)]
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
    (hvD : v ∈ (Scheme.IdealSheafData.ofIdealTop
      (sectionEvaluationIdealAt D.site D.base D.base_mem ⟨X, hX.1⟩ L s V)).support)
    (U : (chartScheme V).affineOpens) (hvU : v ∈ U.1) (a : Γ(chartScheme V, U.1))
    (haD : AlgebraicGeometry.IdealSheafData.stalk (Scheme.IdealSheafData.ofIdealTop
        (sectionEvaluationIdealAt D.site D.base D.base_mem ⟨X, hX.1⟩ L s V)) v =
      Ideal.span {((chartScheme V).presheaf.germ U.1 v hvU).hom a})
    (ha : IsSMulRegular ((chartScheme V).presheaf.stalk v)
      (((chartScheme V).presheaf.germ U.1 v hvU).hom a))
    (ham : ((chartScheme V).presheaf.germ U.1 v hvU).hom a ∈
      IsLocalRing.maximalIdeal ((chartScheme V).presheaf.stalk v))
    (hfinite : Module.length ((chartScheme V).presheaf.stalk v)
      ((chartScheme V).presheaf.stalk v ⧸
        Ideal.span {((chartScheme V).presheaf.germ U.1 v hvU).hom a}) ≠ ⊤)
    (hident : ∀ Xi : ComponentsOfDeltaDimension D sX hX (k + 1),
      haveI := locallyOfFiniteType_id_chartChowSituation D sX hX V hs
      haveI := isClosedImmersion_componentVanishingLocusChartImmersion D sX hX L s Xi.1 V
      (Stacks.Chow.cycleAssociatedToClosedSubscheme (chartChowSituation D sX hX V hs)
            (𝟙 (chartScheme V))
            (componentVanishingLocusChartImmersion D sX hX L s Xi.1 V) k).1 v =
        (Stacks.Chow.cycleAssociatedToClosedSubscheme (chartChowSituation D sX hX V hs)
          (𝟙 (chartScheme V))
          (((closedSubspaceBaseChangeChartProj D.site D.base D.base_mem hX.1 Xi.1.subspace
              Xi.1.isClosedSubspace V).ker ⊔ Scheme.IdealSheafData.ofIdealTop
                (sectionEvaluationIdealAt D.site D.base D.base_mem ⟨X, hX.1⟩ L s V)).subschemeι)
          k).1 v) :
    haveI := locallyOfFiniteType_id_chartChowSituation D sX hX V hs
    haveI := locallyOfFiniteType_subschemeι_comp_id_chartChowSituation D sX hX V hs
      (Scheme.IdealSheafData.ofIdealTop
        (sectionEvaluationIdealAt D.site D.base D.base_mem ⟨X, hX.1⟩ L s V))
    Stacks.Chow.schemeDeltaDimension (chartChowSituation D sX hX V hs)
        (𝟙 (chartScheme V)) ≤ (k + 1 : EInt) →
    Stacks.Chow.schemeDeltaDimension (chartChowSituation D sX hX V hs)
        ((Scheme.IdealSheafData.ofIdealTop (sectionEvaluationIdealAt D.site D.base D.base_mem
          ⟨X, hX.1⟩ L s V)).subschemeι ≫ 𝟙 (chartScheme V)) ≤ (k : EInt) →
    Stacks.Chow.relativeDimension (chartChowSituation D sX hX V hs).dimensionFunction
        (𝟙 (chartScheme V)) v = k →
    cycleCoeffOfClosedSubspace D sX hX (vanishingLocus D sX hX L s).1
        (vanishingLocus D sX hX L s).2 k γZ Z =
      componentZeroCycleSumCoeff D sX hX L s k γ γW Z := by
  have hft := locallyOfFiniteType_id_chartChowSituation D sX hX V hs
  have hftD := locallyOfFiniteType_subschemeι_comp_id_chartChowSituation D sX hX V hs
    (Scheme.IdealSheafData.ofIdealTop
      (sectionEvaluationIdealAt D.site D.base D.base_mem ⟨X, hX.1⟩ L s V))
  intro hYdim hDdim hvdim
  have hsurjpt : Function.Surjective (chartSchemeToPoints D.site D.base D.base_mem X V) :=
    surjective_chartSchemeToPoints D.site D.base D.base_mem X V
      ((surjective_iff_surjective_pointsMap D.site D.base D.base_mem X hX.1 V.obj.left
        V.obj.hom).mp hs)
  choose wpt hwpt using fun Xi : ComponentsOfDeltaDimension D sX hX (k + 1) =>
    hsurjpt (Xi.1.ambientGenericPoint D.site D.base D.base_mem)
  rw [cycleCoeffOfClosedSubspace_zeroScheme_eq_cycleAssociatedToClosedSubscheme_chart
      D sX hX L hL s hEgood V hs k γZ hγZ Z v hv,
    cycleAssociatedToClosedSubscheme_eq_finsum_componentsOfDeltaDimension
      D sX hX V hs k γ hγ wpt hwpt (Scheme.IdealSheafData.ofIdealTop
        (sectionEvaluationIdealAt D.site D.base D.base_mem ⟨X, hX.1⟩ L s V))
      v hvD U hvU a haD ha ham hfinite hYdim hDdim hvdim,
    componentZeroCycleSumCoeff_eq_finsum_cycleAssociatedToClosedSubscheme_chart
      D sX hX L s k γ hγ γW hγW hVLgood V hs wpt hwpt Z v hv]
  exact finsum_congr fun Xi => congrArg (fun z : ℤ => _ * z) (hident Xi).symm

end AlgebraicGeometry.Space

end
