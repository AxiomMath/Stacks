module

public import StacksFrontier.Algebra.Module.LiftBaseChangeRingEquivSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraSheafChartCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealSheafDataFromCartesian

/-!
# Base change of chart sections, read over the regular functions on a Zariski open

A Zariski open `O` of the scheme `chartScheme U` underlying an étale chart `U` of an algebraic
space `F` is itself an étale chart of `F`, by `AlgebraicGeometry.Space.chartOpens`.  So there are
two rings of functions on `O`: the chart ring `𝒪_F((chartOpens U).obj O)` of the small étale
site, which is what `AlgebraicGeometry.Space.sectionsBaseChange` and the cartesianness of
Descent, Proposition 03DX are written over, and the regular functions `Γ(chartScheme U, O)` of
the scheme, which is what the affine comparison
`AlgebraicGeometry.affinePullbackSectionsBaseChangeIso` is written over.  The two are isomorphic
but not equal, and this file carries bijectivity of the base-change comparison from the first
spelling to the second.

This is the step recorded as the one thing still missing from the third item of the
implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/AlgebraSheafChartCartesian.lean`, and in the same words at
the end of the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartModuleRestrictionComparisonSections.lean`: "carrying
the bijectivity of `AlgebraicGeometry.Space.sectionsBaseChange` over to the rings of regular
functions on the two affine opens, which are isomorphic to the chart rings it is stated over but
not equal to them".

## Main definitions

* `AlgebraicGeometry.Space.chartOpensRingEquiv` is the isomorphism, bundled as a `RingEquiv`:
  `Γ(chartScheme U, O) ≃+* 𝒪_F((chartOpens U).obj O)`.  It is
  `AlgebraicGeometry.Scheme.Opens.topIso` at `O`, inverted — the same map the tree already has
  unbundled, in the other direction, as `AlgebraicGeometry.Space.openChartTopRingHom`.

## Main results

* `AlgebraicGeometry.Space.chartOpensRingEquiv_appLE`: **the square commutes.**  For a morphism
  `g : V ⟶ U` of étale charts and a Zariski open `O'` of `chartScheme V` inside the preimage of a
  Zariski open `O` of `chartScheme U`, the restriction map of regular functions
  `Γ(chartScheme U, O) ⟶ Γ(chartScheme V, O')` followed by the isomorphism at `O'` is the
  isomorphism at `O` followed by restriction along the chart morphism
  `AlgebraicGeometry.Space.chartOpensRestrictLE`.
* `AlgebraicGeometry.Space.bijective_liftBaseChange_iff_sectionsBaseChange`: **the transport.**
  The base-change comparison of the sections of an `𝒪_F`-module written over the two rings of
  regular functions is bijective exactly when
  `AlgebraicGeometry.Space.sectionsBaseChange` at
  `AlgebraicGeometry.Space.chartOpensRestrictLE` is.
* `AlgebraicGeometry.Space.bijective_liftBaseChange_of_isQuasicoherentOnSite`: **the consequence
  for a quasi-coherent module.**  Over a pair of affine opens the comparison written over the
  rings of regular functions is bijective.

## Implementation notes

**Nothing geometric is proved here; the square is already in the tree.**
`AlgebraicGeometry.resLE_appTop_comp_topIso_hom` is exactly the commuting square, for a general
open `O'` inside the preimage and not only for the preimage itself, and
`AlgebraicGeometry.Space.chartOpensRingEquiv_appLE` is that lemma conjugated by the comparison
isomorphism and read in the vocabulary of étale charts.  The one thing it adds is the
identification of `AlgebraicGeometry.Space.chartRestrict` along
`AlgebraicGeometry.Space.chartOpensRestrictLE` with the map on global functions of
`AlgebraicGeometry.Scheme.Hom.resLE`, which is
`AlgebraicGeometry.Space.chartSchemeMap_chartOpensRestrictLE` and holds by `rfl`:
`AlgebraicGeometry.Scheme.Hom.resLE` is by definition `homOfLE` followed by
`AlgebraicGeometry.morphismRestrict`, and that is how
`AlgebraicGeometry.Space.chartOpensRestrictLE` is assembled.  The comparison isomorphism itself
is not new either: `AlgebraicGeometry.Space.chartOpensRingEquiv` is
`AlgebraicGeometry.Scheme.Opens.topIso` inverted, which the tree already uses unbundled as
`AlgebraicGeometry.Space.openChartTopRingHom`, with its bijectivity as
`AlgebraicGeometry.Space.bijective_openChartTopRingHom` and its components identified with the
change-of-scalars map of the chart restriction by
`AlgebraicGeometry.Space.chartRestrictionRingHom_app_apply` together with
`AlgebraicGeometry.Space.chartRestrictionRingHom_eq`.  It is bundled here only because
`Stacks.BaseChange.bijective_liftBaseChange_iff` consumes a `RingEquiv`.

**The content of the file is therefore the transport, and the transport is the whole content.**
`Stacks.BaseChange.bijective_liftBaseChange_iff` had no consumer before this file; what it needs
is the two ring isomorphisms, the commutativity of the square they sit in, and the two pairs of
corresponding scalar actions, and supplying those at the chart rings and the rings of regular
functions is what is done below.

**The module structures over the scheme rings are hypotheses, not instances.**  The sections of
an `𝒪_F`-module over a chart are a module over the chart ring; they carry no
`Γ(chartScheme U, O)`-action as an instance, and the action a caller has is whatever its own
construction produced.  So, exactly as in
`StacksFrontier/AlgebraicGeometry/AffineOpenSectionsBaseChange/Basic.lean`, the actions and the
algebra structure are taken as instance-implicit arguments together with the equations pinning
them to the geometry, and the restriction map appears twice, once over each base ring, with the
hypothesis that the two are the same function.  Bundling them instead would produce a statement
no call site could apply.

**What is *not* checked here is that the intended caller can discharge those hypotheses.**  The
action the chart restriction supplies is restriction of scalars along
`AlgebraicGeometry.Space.chartSchemeRestrictionRingHom`, whose carrier is the chart sections
themselves, so the pinning equations ought to be `rfl`; but that action is a
`Module ((chartScheme U).ringCatSheaf.obj.obj (op O))` and the hypotheses here ask for a
`Module Γ(chartScheme U, O)`, and the two are separated by the `CommRingCat`/`RingCat` boundary
that the implementation notes of
`StacksFrontier/AlgebraicGeometry/Topologies/AssociatedModuleAffineBaseChange.lean` record as
exhausting the default recursion depth at these concrete sheaf-section types.  Reading the one
as the other was tried and does not go through at the kernel.  Supplying the instances on one
side of that boundary, so that a consumer coming from the chart restriction can apply the
transport below, is therefore still owed; it is the same choice-of-side that the implementation
notes of `StacksFrontier/AlgebraicGeometry/Spaces/ChartModuleRestrictionPullbackIso.lean` describe,
and it is not made here.

**No `stacks` attribute is claimed.**  The content is a change of spelling of the base rings of
one comparison.  The comparison itself is the cartesianness of Descent, Proposition 03DX, which
is registered elsewhere — for the small étale site of an algebraic space as
`AlgebraicGeometry.Space.bijective_sectionsBaseChange_of_isQuasicoherentOnSite_anyUniverse`, and
for a sheaf of algebras as
`AlgebraicGeometry.Space.AlgebraSheaf.isQuasicoherent_iff_isCartesianOnAffineCharts`.  Nothing
here asserts invertibility of
`AlgebraicGeometry.Space.restrictToChartSchemePullbackComparison`, which needs this transport
*and* the identification of that comparison with a base change over an affine pair; see the
implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartModuleRestrictionPullbackIso.lean`.

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

/-- **The regular functions on a Zariski open of a chart scheme are the chart ring of that open
read as an étale chart.**  It is `AlgebraicGeometry.Scheme.Opens.topIso` at `O`, inverted: the
scheme underlying the étale chart `(chartOpens U).obj O` is the open subscheme `O` itself, so the
target is the global functions on it.

The same map in the other direction, unbundled, is
`AlgebraicGeometry.Space.openChartTopRingHom`; it is bundled here because
`Stacks.BaseChange.bijective_liftBaseChange_iff` consumes a `RingEquiv`.  It is stated for an
unbundled algebraic space and at the chart `(chartOpens U).obj O`;
`AlgebraicGeometry.Space.chartOpenRingEquiv` is the analogue at
`AlgebraicGeometry.Space.openChart` for a bundled `X : AlgebraicSpaces B S hS`. -/
noncomputable def chartOpensRingEquiv (U : SmallEtale B S hS F) (O : (chartScheme U).Opens) :
    Γ(chartScheme U, O) ≃+* chartRing B S hS F hF ((chartOpens B S hS U).obj O) :=
  O.topIso.commRingCatIsoToRingEquiv.symm

/-! ### The square over a morphism of charts -/

/-- The morphism of schemes underlying `AlgebraicGeometry.Space.chartOpensRestrictLE` is
`AlgebraicGeometry.Scheme.Hom.resLE` of the chart morphism: both are `homOfLE` followed by
`AlgebraicGeometry.morphismRestrict`. -/
theorem chartSchemeMap_chartOpensRestrictLE {U V : SmallEtale B S hS F} (g : V ⟶ U)
    {O : (chartScheme U).Opens} {O' : (chartScheme V).Opens}
    (hle : O' ≤ chartSchemeMap g ⁻¹ᵁ O) :
    chartSchemeMap (chartOpensRestrictLE g hle) = (chartSchemeMap g).resLE O O' hle :=
  rfl

/-- **The square of `AlgebraicGeometry.Space.chartOpensRingEquiv`.**  Restricting regular
functions from `O` to `O'` and then passing to the chart ring is passing to the chart ring and
then restricting along the chart morphism `AlgebraicGeometry.Space.chartOpensRestrictLE`.

This is `AlgebraicGeometry.resLE_appTop_comp_topIso_hom` conjugated by the comparison
isomorphism; the identification of the chart-level restriction map with the one of
`AlgebraicGeometry.Scheme.Hom.resLE` is
`AlgebraicGeometry.Space.chartSchemeMap_chartOpensRestrictLE`. -/
theorem chartOpensRingEquiv_appLE {U V : SmallEtale B S hS F} (g : V ⟶ U)
    {O : (chartScheme U).Opens} {O' : (chartScheme V).Opens}
    (hle : O' ≤ chartSchemeMap g ⁻¹ᵁ O) (r : Γ(chartScheme U, O)) :
    chartOpensRingEquiv B S hS F hF V O' ((chartSchemeMap g).appLE O O' hle r) =
      chartRestrict (hF := hF) (chartOpensRestrictLE g hle)
        (chartOpensRingEquiv B S hS F hF U O r) := by
  have e : O'.topIso.hom
        (((chartSchemeMap g).resLE O O' hle).appTop (O.topIso.inv r)) =
      (chartSchemeMap g).appLE O O' hle (O.topIso.hom (O.topIso.inv r)) :=
    ConcreteCategory.congr_hom
      (resLE_appTop_comp_topIso_hom (chartSchemeMap g) hle) _
  apply (ConcreteCategory.bijective_of_isIso O'.topIso.hom).1
  show O'.topIso.hom (O'.topIso.inv ((chartSchemeMap g).appLE O O' hle r)) =
    O'.topIso.hom (((chartSchemeMap g).resLE O O' hle).appTop (O.topIso.inv r))
  rw [e, O.topIso.inv_hom_id_apply, O'.topIso.inv_hom_id_apply]

/-! ### The transport of base-change bijectivity -/

/-- **The base-change comparison of the sections of an `𝒪_F`-module over a pair of Zariski opens
of two charts, written over the rings of regular functions, is bijective exactly when
`AlgebraicGeometry.Space.sectionsBaseChange` at the corresponding chart morphism is.**

This is the transport the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/AlgebraSheafChartCartesian.lean` and of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartModuleRestrictionComparisonSections.lean` ask for:
cartesianness of Descent, Proposition 03DX is available over the chart rings
`𝒪_F((chartOpens U).obj O)` and `𝒪_F((chartOpens V).obj O')`, and the affine comparison
`AlgebraicGeometry.affinePullbackSectionsBaseChangeIso` is written over `Γ(chartScheme U, O)` and
`Γ(chartScheme V, O')`, the two pairs being isomorphic by
`AlgebraicGeometry.Space.chartOpensRingEquiv` and not equal.

The actions over the two rings of regular functions, and the algebra structure relating them,
are hypotheses rather than instances, and the restriction map appears twice — once over each base
ring — with `hf` saying the two are the same function; see the implementation notes. -/
theorem bijective_liftBaseChange_iff_sectionsBaseChange
    (M : Modules.{u, m} B S hS F hF) {U V : SmallEtale B S hS F} (g : V ⟶ U)
    {O : (chartScheme U).Opens} {O' : (chartScheme V).Opens}
    (hle : O' ≤ chartSchemeMap g ⁻¹ᵁ O)
    [Algebra Γ(chartScheme U, O) Γ(chartScheme V, O')]
    [Module Γ(chartScheme U, O)
      (M.val.obj (op ((chartOpens B S hS U).obj O)) : Type m)]
    [Module Γ(chartScheme U, O)
      (M.val.obj (op ((chartOpens B S hS V).obj O')) : Type m)]
    [Module Γ(chartScheme V, O')
      (M.val.obj (op ((chartOpens B S hS V).obj O')) : Type m)]
    [IsScalarTower Γ(chartScheme U, O) Γ(chartScheme V, O')
      (M.val.obj (op ((chartOpens B S hS V).obj O')) : Type m)]
    (halg : ∀ r : Γ(chartScheme U, O),
      algebraMap Γ(chartScheme U, O) Γ(chartScheme V, O') r =
        (chartSchemeMap g).appLE O O' hle r)
    (hMod : ∀ (r : Γ(chartScheme U, O))
        (x : (M.val.obj (op ((chartOpens B S hS U).obj O)) : Type m)),
      r • x = chartOpensRingEquiv B S hS F hF U O r • x)
    (hN : ∀ (a : Γ(chartScheme V, O'))
        (n : (M.val.obj (op ((chartOpens B S hS V).obj O')) : Type m)),
      a • n = chartOpensRingEquiv B S hS F hF V O' a • n)
    (f₁ : (M.val.obj (op ((chartOpens B S hS U).obj O)) : Type m) →ₗ[Γ(chartScheme U, O)]
      (M.val.obj (op ((chartOpens B S hS V).obj O')) : Type m))
    (hf : ∀ x, f₁ x = M.val.map (chartOpensRestrictLE g hle).op x) :
    Function.Bijective (f₁.liftBaseChange Γ(chartScheme V, O')) ↔
      Function.Bijective (sectionsBaseChange M (chartOpensRestrictLE g hle)) := by
  let := chartAlgebra (hF := hF) (chartOpensRestrictLE g hle)
  let := chartSectionsModule M (chartOpensRestrictLE g hle)
  have := chartSections_isScalarTower M (chartOpensRestrictLE g hle)
  exact Stacks.BaseChange.bijective_liftBaseChange_iff
    (chartOpensRingEquiv B S hS F hF U O) (chartOpensRingEquiv B S hS F hF V O')
    hMod
    (fun r => by
      rw [halg r]
      exact chartOpensRingEquiv_appLE B S hS F hF g hle r)
    hN f₁ (chartRestrictLinear M (chartOpensRestrictLE g hle)) hf

/-- **A quasi-coherent `𝒪_F`-module is cartesian over a pair of affine Zariski opens of two
charts, read over the rings of regular functions on those opens.**  This is
`AlgebraicGeometry.Space.bijective_sectionsBaseChange_of_isQuasicoherentOnSite_anyUniverse`
carried across `AlgebraicGeometry.Space.chartOpensRingEquiv` by
`AlgebraicGeometry.Space.bijective_liftBaseChange_iff_sectionsBaseChange`.

The affine opens for which this applies cover the smaller chart scheme, by
`AlgebraicGeometry.Space.exists_isAffine_le_preimage`, so this is the local statement of
cartesianness at the spelling of the base rings that the affine comparison
`AlgebraicGeometry.affinePullbackSectionsBaseChangeIso` uses.  It is **not** invertibility of
`AlgebraicGeometry.Space.restrictToChartSchemePullbackComparison`: identifying that comparison
with this base change over an affine pair is a separate step, recorded as open in the
implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartModuleRestrictionPullbackIso.lean`. -/
theorem bijective_liftBaseChange_of_isQuasicoherentOnSite
    (M : Modules.{u, m} B S hS F hF) (hM : M.IsQuasicoherentOnSite)
    {U V : SmallEtale B S hS F} (g : V ⟶ U)
    {O : (chartScheme U).Opens} {O' : (chartScheme V).Opens}
    (hle : O' ≤ chartSchemeMap g ⁻¹ᵁ O)
    (hO : IsAffine (chartScheme ((chartOpens B S hS U).obj O)))
    (hO' : IsAffine (chartScheme ((chartOpens B S hS V).obj O')))
    [Algebra Γ(chartScheme U, O) Γ(chartScheme V, O')]
    [Module Γ(chartScheme U, O)
      (M.val.obj (op ((chartOpens B S hS U).obj O)) : Type m)]
    [Module Γ(chartScheme U, O)
      (M.val.obj (op ((chartOpens B S hS V).obj O')) : Type m)]
    [Module Γ(chartScheme V, O')
      (M.val.obj (op ((chartOpens B S hS V).obj O')) : Type m)]
    [IsScalarTower Γ(chartScheme U, O) Γ(chartScheme V, O')
      (M.val.obj (op ((chartOpens B S hS V).obj O')) : Type m)]
    (halg : ∀ r : Γ(chartScheme U, O),
      algebraMap Γ(chartScheme U, O) Γ(chartScheme V, O') r =
        (chartSchemeMap g).appLE O O' hle r)
    (hMod : ∀ (r : Γ(chartScheme U, O))
        (x : (M.val.obj (op ((chartOpens B S hS U).obj O)) : Type m)),
      r • x = chartOpensRingEquiv B S hS F hF U O r • x)
    (hN : ∀ (a : Γ(chartScheme V, O'))
        (n : (M.val.obj (op ((chartOpens B S hS V).obj O')) : Type m)),
      a • n = chartOpensRingEquiv B S hS F hF V O' a • n)
    (f₁ : (M.val.obj (op ((chartOpens B S hS U).obj O)) : Type m) →ₗ[Γ(chartScheme U, O)]
      (M.val.obj (op ((chartOpens B S hS V).obj O')) : Type m))
    (hf : ∀ x, f₁ x = M.val.map (chartOpensRestrictLE g hle).op x) :
    Function.Bijective (f₁.liftBaseChange Γ(chartScheme V, O')) :=
  (bijective_liftBaseChange_iff_sectionsBaseChange B S hS F hF M g hle halg hMod hN
      f₁ hf).2
    (bijective_sectionsBaseChange_of_isQuasicoherentOnSite_anyUniverse B S hS F hF M hM
      (U := (chartOpens B S hS U).obj O) (V := (chartOpens B S hS V).obj O') hO hO'
      (chartOpensRestrictLE g hle))

end AlgebraicGeometry.Space

end
