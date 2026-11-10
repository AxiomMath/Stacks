module

public import StacksFrontier.Algebra.Module.LiftBaseChangeRingEquivSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartOpenSectionsRingTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionSectionsUnit

/-!
# Base change of chart sections, in the `openChart` spelling of the charts

`StacksFrontier/AlgebraicGeometry/Spaces/ChartOpenSectionsRingTransport.lean` carries bijectivity of
the base-change comparison of the sections of an `𝒪_F`-module from the chart rings of the small
étale site to the rings of regular functions of the chart schemes.  It is written over
`AlgebraicGeometry.Space.chartOpens` and `AlgebraicGeometry.Space.chartOpensRestrictLE`.

Every section computation for the inverse-image comparison of the chart restrictions — the ones
of `StacksFrontier/AlgebraicGeometry/Spaces/ChartModuleRestrictionComparisonSections.lean` and
`StacksFrontier/AlgebraicGeometry/Spaces/ChartSchemeRestrictionSectionsUnit.lean` — is instead
written over `AlgebraicGeometry.Space.openChart` and the chart morphism
`openChartHomOfLE V hle ≫ openChartRestrict g O`.  The two readings of a Zariski open as an étale
chart are equal only propositionally, by
`AlgebraicGeometry.Space.chartOpens_obj_eq_openChart`, which is not `rfl`.  This file is the
transport restated in the second spelling, so that the two meet with no transport along that
equality.

## Main definitions

* `AlgebraicGeometry.Space.openChartRingEquiv` is the isomorphism
  `Γ(chartScheme U, O) ≃+* 𝒪_F(openChart U O)`, bundled as a `RingEquiv`.  It is
  `AlgebraicGeometry.Scheme.Opens.topIso` at `O`, inverted — the same map the tree already has
  unbundled, in the other direction, as `AlgebraicGeometry.Space.openChartTopRingHom`.

## Main results

* `AlgebraicGeometry.Space.chartSchemeMap_openChartHomOfLE_comp_openChartRestrict`: the morphism
  of schemes underlying `openChartHomOfLE V hle ≫ openChartRestrict g O` is
  `AlgebraicGeometry.Scheme.Hom.resLE` of the chart morphism, definitionally.
* `AlgebraicGeometry.Space.openChartRingEquiv_appLE`: **the square commutes.**
* `AlgebraicGeometry.Space.bijective_liftBaseChange_iff_sectionsBaseChange_openChart`: **the
  transport.**  The base-change comparison written over the two rings of regular functions is
  bijective exactly when `AlgebraicGeometry.Space.sectionsBaseChange` at
  `openChartHomOfLE V hle ≫ openChartRestrict g O` is.
* `AlgebraicGeometry.Space.bijective_liftBaseChange_of_isQuasicoherentOnSite_openChart`: **the
  consequence for a quasi-coherent module.**

## Implementation notes

**Why a restatement and not a transport.**  Composing
`AlgebraicGeometry.Space.bijective_liftBaseChange_iff_sectionsBaseChange` with the section
computations would need an `eqToHom` along
`AlgebraicGeometry.Space.chartOpens_obj_eq_openChart`, which is the design debt this tree avoids;
and the equality is between *objects of the small étale site*, so the transport would appear
inside `M.val.obj (op ·)` and inside the module instances, where it cannot be rewritten away.
Restating is strictly cheaper: the geometric input is the same single square
`AlgebraicGeometry.resLE_appTop_comp_topIso_hom`, and the only thing that changes is which
morphism of charts the restriction map is taken along.

**The statement of the original is untouched.**  The declarations here are siblings of those in
`StacksFrontier/AlgebraicGeometry/Spaces/ChartOpenSectionsRingTransport.lean` under new names, not
edits of them; the `chartOpens` spelling has its own consumers.

**The two factors of the chart morphism.**  The underlying morphism of schemes of
`openChartHomOfLE V hle` is `AlgebraicGeometry.Scheme.homOfLE` by
`AlgebraicGeometry.Space.toScheme_map_toOver_map_openChartHomOfLE`, and that of
`openChartRestrict g O` is `AlgebraicGeometry.morphismRestrict`, both definitionally; and
`AlgebraicGeometry.Space.chartSchemeMap_comp` is `rfl`.  Since
`AlgebraicGeometry.Scheme.Hom.resLE` is itself `homOfLE` followed by `morphismRestrict`, the
underlying morphism of the composite is `resLE` by `rfl`, which is what makes the square of
`AlgebraicGeometry.resLE_appTop_comp_topIso_hom` — stated for a general open inside the preimage,
not only for the preimage itself — applicable here without any further geometry.

**The module structures over the scheme rings are hypotheses, not instances**, for the reason the
implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartOpenSectionsRingTransport.lean` give: the sections of
an `𝒪_F`-module over a chart are a module over the chart ring and carry no
`Γ(chartScheme U, O)`-action as an instance.

**No `stacks` attribute is claimed.**  The content is a change of spelling of the charts one
comparison is written over.  The comparison itself is the cartesianness of Descent,
Proposition 03DX, which is registered elsewhere — for the small étale site of an algebraic space
as `AlgebraicGeometry.Space.bijective_sectionsBaseChange_of_isQuasicoherentOnSite_anyUniverse`.
Nothing here asserts invertibility of
`AlgebraicGeometry.Space.restrictToChartSchemePullbackComparison`.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03LY](https://stacks.math.columbia.edu/tag/03LY)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u m

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-! ### The two rings of functions on a Zariski open of a chart -/

/-- **The regular functions on a Zariski open of a chart scheme are the chart ring of the étale
chart that open cuts out.**  It is `AlgebraicGeometry.Scheme.Opens.topIso` at `O`, inverted: the
scheme underlying the étale chart `openChart U O` is the open subscheme `O` itself, so the source
is the global functions on it.

The same map in the other direction, unbundled, is
`AlgebraicGeometry.Space.openChartTopRingHom`; it is bundled here because
`Stacks.BaseChange.bijective_liftBaseChange_iff` consumes a `RingEquiv`. -/
noncomputable def openChartRingEquiv (U : SmallEtale B S hS F) (O : (chartScheme U).Opens) :
    Γ(chartScheme U, O) ≃+* chartRing B S hS F hF (openChart B S hS F U O) :=
  O.topIso.commRingCatIsoToRingEquiv.symm

/-! ### The square over a morphism of charts -/

/-- The morphism of schemes underlying `openChartHomOfLE V hle ≫ openChartRestrict g O` is
`AlgebraicGeometry.Scheme.Hom.resLE` of the chart morphism: both are `homOfLE` followed by
`AlgebraicGeometry.morphismRestrict`. -/
theorem chartSchemeMap_openChartHomOfLE_comp_openChartRestrict
    {U V : SmallEtale B S hS F} (g : V ⟶ U)
    {O : (chartScheme U).Opens} {O' : (chartScheme V).Opens}
    (hle : O' ≤ chartSchemeMap g ⁻¹ᵁ O) :
    chartSchemeMap (openChartHomOfLE B S hS F V hle ≫ openChartRestrict B S hS F g O) =
      (chartSchemeMap g).resLE O O' hle :=
  rfl

/-- **The square of `AlgebraicGeometry.Space.openChartRingEquiv`.**  Restricting regular
functions from `O` to `O'` and then passing to the chart ring is passing to the chart ring and
then restricting along the morphism of étale charts
`openChartHomOfLE V hle ≫ openChartRestrict g O`.

This is `AlgebraicGeometry.resLE_appTop_comp_topIso_hom` conjugated by the comparison
isomorphism; the identification of the chart-level restriction map with the one of
`AlgebraicGeometry.Scheme.Hom.resLE` is
`AlgebraicGeometry.Space.chartSchemeMap_openChartHomOfLE_comp_openChartRestrict`. -/
theorem openChartRingEquiv_appLE {U V : SmallEtale B S hS F} (g : V ⟶ U)
    {O : (chartScheme U).Opens} {O' : (chartScheme V).Opens}
    (hle : O' ≤ chartSchemeMap g ⁻¹ᵁ O) (r : Γ(chartScheme U, O)) :
    openChartRingEquiv B S hS F hF V O' ((chartSchemeMap g).appLE O O' hle r) =
      chartRestrict (hF := hF)
          (openChartHomOfLE B S hS F V hle ≫ openChartRestrict B S hS F g O)
        (openChartRingEquiv B S hS F hF U O r) := by
  have e : O'.topIso.hom
        (((chartSchemeMap g).resLE O O' hle).appTop (O.topIso.inv r)) =
      (chartSchemeMap g).appLE O O' hle (O.topIso.hom (O.topIso.inv r)) :=
    ConcreteCategory.congr_hom
      (resLE_appTop_comp_topIso_hom (chartSchemeMap g) hle) _
  apply (ConcreteCategory.bijective_of_isIso O'.topIso.hom).1
  change O'.topIso.hom (O'.topIso.inv ((chartSchemeMap g).appLE O O' hle r)) =
    O'.topIso.hom (((chartSchemeMap g).resLE O O' hle).appTop (O.topIso.inv r))
  rw [e, O.topIso.inv_hom_id_apply, O'.topIso.inv_hom_id_apply]

/-! ### The transport of base-change bijectivity -/

/-- **The base-change comparison of the sections of an `𝒪_F`-module over a pair of Zariski opens
of two charts, written over the rings of regular functions, is bijective exactly when
`AlgebraicGeometry.Space.sectionsBaseChange` at the morphism of étale charts
`openChartHomOfLE V hle ≫ openChartRestrict g O` is.**

This is `AlgebraicGeometry.Space.bijective_liftBaseChange_iff_sectionsBaseChange` in the
`AlgebraicGeometry.Space.openChart` spelling of the two charts, which is the one the section
computations for `AlgebraicGeometry.Space.restrictToChartSchemePullbackComparison` produce; see
the implementation notes.

The actions over the two rings of regular functions, and the algebra structure relating them,
are hypotheses rather than instances, and the restriction map appears twice — once over each base
ring — with `hf` saying the two are the same function. -/
theorem bijective_liftBaseChange_iff_sectionsBaseChange_openChart
    (M : Modules.{u, m} B S hS F hF) {U V : SmallEtale B S hS F} (g : V ⟶ U)
    {O : (chartScheme U).Opens} {O' : (chartScheme V).Opens}
    (hle : O' ≤ chartSchemeMap g ⁻¹ᵁ O)
    [Algebra Γ(chartScheme U, O) Γ(chartScheme V, O')]
    [Module Γ(chartScheme U, O)
      (M.val.obj (op (openChart B S hS F U O)) : Type m)]
    [Module Γ(chartScheme U, O)
      (M.val.obj (op (openChart B S hS F V O')) : Type m)]
    [Module Γ(chartScheme V, O')
      (M.val.obj (op (openChart B S hS F V O')) : Type m)]
    [IsScalarTower Γ(chartScheme U, O) Γ(chartScheme V, O')
      (M.val.obj (op (openChart B S hS F V O')) : Type m)]
    (halg : ∀ r : Γ(chartScheme U, O),
      algebraMap Γ(chartScheme U, O) Γ(chartScheme V, O') r =
        (chartSchemeMap g).appLE O O' hle r)
    (hMod : ∀ (r : Γ(chartScheme U, O))
        (x : (M.val.obj (op (openChart B S hS F U O)) : Type m)),
      r • x = openChartRingEquiv B S hS F hF U O r • x)
    (hN : ∀ (a : Γ(chartScheme V, O'))
        (n : (M.val.obj (op (openChart B S hS F V O')) : Type m)),
      a • n = openChartRingEquiv B S hS F hF V O' a • n)
    (f₁ : (M.val.obj (op (openChart B S hS F U O)) : Type m) →ₗ[Γ(chartScheme U, O)]
      (M.val.obj (op (openChart B S hS F V O')) : Type m))
    (hf : ∀ x, f₁ x = M.val.map
      (openChartHomOfLE B S hS F V hle ≫ openChartRestrict B S hS F g O).op x) :
    Function.Bijective (f₁.liftBaseChange Γ(chartScheme V, O')) ↔
      Function.Bijective (sectionsBaseChange M
        (openChartHomOfLE B S hS F V hle ≫ openChartRestrict B S hS F g O)) := by
  let := chartAlgebra (hF := hF)
    (openChartHomOfLE B S hS F V hle ≫ openChartRestrict B S hS F g O)
  let := chartSectionsModule M
    (openChartHomOfLE B S hS F V hle ≫ openChartRestrict B S hS F g O)
  have := chartSections_isScalarTower M
    (openChartHomOfLE B S hS F V hle ≫ openChartRestrict B S hS F g O)
  exact Stacks.BaseChange.bijective_liftBaseChange_iff
    (openChartRingEquiv B S hS F hF U O) (openChartRingEquiv B S hS F hF V O')
    hMod
    (fun r => by
      rw [halg r]
      exact openChartRingEquiv_appLE B S hS F hF g hle r)
    hN f₁ (chartRestrictLinear M
      (openChartHomOfLE B S hS F V hle ≫ openChartRestrict B S hS F g O)) hf

/-- **A quasi-coherent `𝒪_F`-module is cartesian over a pair of affine Zariski opens of two
charts, read over the rings of regular functions on those opens, in the
`AlgebraicGeometry.Space.openChart` spelling of the charts.**  This is
`AlgebraicGeometry.Space.bijective_sectionsBaseChange_of_isQuasicoherentOnSite_anyUniverse`
carried across `AlgebraicGeometry.Space.openChartRingEquiv` by
`AlgebraicGeometry.Space.bijective_liftBaseChange_iff_sectionsBaseChange_openChart`.

It is **not** invertibility of
`AlgebraicGeometry.Space.restrictToChartSchemePullbackComparison`: identifying that comparison
with this base change over an affine pair is a separate step. -/
theorem bijective_liftBaseChange_of_isQuasicoherentOnSite_openChart
    (M : Modules.{u, m} B S hS F hF) (hM : M.IsQuasicoherentOnSite)
    {U V : SmallEtale B S hS F} (g : V ⟶ U)
    {O : (chartScheme U).Opens} {O' : (chartScheme V).Opens}
    (hle : O' ≤ chartSchemeMap g ⁻¹ᵁ O)
    (hO : IsAffine (chartScheme (openChart B S hS F U O)))
    (hO' : IsAffine (chartScheme (openChart B S hS F V O')))
    [Algebra Γ(chartScheme U, O) Γ(chartScheme V, O')]
    [Module Γ(chartScheme U, O)
      (M.val.obj (op (openChart B S hS F U O)) : Type m)]
    [Module Γ(chartScheme U, O)
      (M.val.obj (op (openChart B S hS F V O')) : Type m)]
    [Module Γ(chartScheme V, O')
      (M.val.obj (op (openChart B S hS F V O')) : Type m)]
    [IsScalarTower Γ(chartScheme U, O) Γ(chartScheme V, O')
      (M.val.obj (op (openChart B S hS F V O')) : Type m)]
    (halg : ∀ r : Γ(chartScheme U, O),
      algebraMap Γ(chartScheme U, O) Γ(chartScheme V, O') r =
        (chartSchemeMap g).appLE O O' hle r)
    (hMod : ∀ (r : Γ(chartScheme U, O))
        (x : (M.val.obj (op (openChart B S hS F U O)) : Type m)),
      r • x = openChartRingEquiv B S hS F hF U O r • x)
    (hN : ∀ (a : Γ(chartScheme V, O'))
        (n : (M.val.obj (op (openChart B S hS F V O')) : Type m)),
      a • n = openChartRingEquiv B S hS F hF V O' a • n)
    (f₁ : (M.val.obj (op (openChart B S hS F U O)) : Type m) →ₗ[Γ(chartScheme U, O)]
      (M.val.obj (op (openChart B S hS F V O')) : Type m))
    (hf : ∀ x, f₁ x = M.val.map
      (openChartHomOfLE B S hS F V hle ≫ openChartRestrict B S hS F g O).op x) :
    Function.Bijective (f₁.liftBaseChange Γ(chartScheme V, O')) :=
  (bijective_liftBaseChange_iff_sectionsBaseChange_openChart B S hS F hF M g hle halg hMod hN
      f₁ hf).2
    (bijective_sectionsBaseChange_of_isQuasicoherentOnSite_anyUniverse B S hS F hF M hM
      (U := openChart B S hS F U O) (V := openChart B S hS F V O') hO hO'
      (openChartHomOfLE B S hS F V hle ≫ openChartRestrict B S hS F g O))

end AlgebraicGeometry.Space

end
