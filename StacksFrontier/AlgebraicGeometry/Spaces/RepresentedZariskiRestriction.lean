module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionFunctorial
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtalePostcomp
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedTFAE

/-!
# Modules on a represented algebraic space, read on the representing scheme

Let `U` be an object of the big fppf site over `S`, with underlying scheme `T`, and let
`h_U = yoneda.obj U` be the algebraic space it represents. The identity of `h_U` is an étale
chart of `h_U` whose underlying scheme is `T`, so the restriction of modules to an étale scheme
chart specialises to a comparison functor from the `𝒪_{h_U}`-modules of the small étale site to
the `𝒪_T`-modules of the Zariski site of `T`.

That comparison is what matches the weakly associated points of the two sides: a point of `h_U`
is weakly associated to an `𝒪_{h_U}`-module exactly when the corresponding point of `T` is
weakly associated, in the Zariski sense of Stacks 056L, to the restricted `𝒪_T`-module. Both
directions are unconditional: the comparison `𝒪_{T, t} → 𝒪_{h_U, x̄}` of Stacks 05VP is a strict
henselization by Stacks 04KF, and Stacks 0CTU descends weak association along one.

## Main definitions

* `AlgebraicGeometry.Space.selfChart` is the identity of a represented presheaf, read as an
  étale chart of it, and `AlgebraicGeometry.Space.selfNeighborhood` is that chart with the
  canonical lift of a geometric point, a small étale neighbourhood of the point.
* `AlgebraicGeometry.Space.representedZariskiRestriction` and
  `AlgebraicGeometry.Space.representedZariskiRestrictionFunctor` are the comparison: the
  restriction of an `𝒪_{h_U}`-module to the Zariski site of the representing scheme, as a map
  on objects and as a functor.
* `AlgebraicGeometry.Space.etaleHomChart` is an étale morphism `g : U ⟶ U'` of the big fppf
  site, read as an étale chart of `h_{U'}`; its underlying scheme is the one underlying `U`.

## Main results

* `AlgebraicGeometry.Space.chartPoint_selfNeighborhood`: the point of the representing scheme
  cut out by the canonical neighbourhood of a geometric point is the image of that point under
  the comparison `AlgebraicGeometry.Space.pointsToScheme` of Stacks 03BV.
* `AlgebraicGeometry.Space.isWeaklyAssociatedPoint_of_isWeaklyAssociatedPoint_zariski`: one
  direction of the comparison of the two weak assassins.
* `AlgebraicGeometry.Space.isWeaklyAssociatedPoint_zariski_of_isWeaklyAssociatedPoint`: the
  converse.
* `AlgebraicGeometry.Space.isWeaklyAssociatedPoint_iff_isWeaklyAssociatedPoint_zariski` and
  `AlgebraicGeometry.Space.weaklyAssociatedPoints_eq_preimage_zariski`: the two together, at a
  point and as an equality of sets of points.
* `AlgebraicGeometry.Space.isEtale_schemeSpaceMap`: the morphism of represented algebraic spaces
  induced by an étale morphism of the big fppf site is étale.
* `AlgebraicGeometry.Space.chartOpens_selfChart_comp_smallEtalePostcomp` and
  `AlgebraicGeometry.Space.chartRestrictionRingHom_selfChart_eq_etaleHomChart`: the index and the
  coefficients of the restriction to the identity chart of `h_U` are, along an étale
  `g : U ⟶ U'`, those of the restriction to the chart `AlgebraicGeometry.Space.etaleHomChart`.
  Both hold on the nose.

## Implementation notes

The étale chart is `CategoryTheory.CostructuredArrow.mk (𝟙 (yoneda.obj U))`, whose underlying
object of the big fppf site is `U` itself, so the scheme underlying the chart is `T` on the
nose: `AlgebraicGeometry.Space.etaleChartScheme_selfChart` holds by `rfl`, and the restriction
`AlgebraicGeometry.Space.restrictToChart` to it therefore lands in
`AlgebraicGeometry.Scheme.Modules` of `T` with no transport. Étaleness of the chart is
étaleness of an identity, which `AlgebraicGeometry.Space.presheaf_yoneda_map_etale_iff` reduces
to étaleness of the identity of `T`.

A geometric point of a represented presheaf is, by the Yoneda lemma, a morphism from a field
spectrum of the site to `U`; that morphism *is* the lift of the point to the identity chart, so
`AlgebraicGeometry.Space.selfNeighborhood` needs nothing beyond the point itself, and its
`point_comp` holds by `rfl`. The point of `T` it selects is the image of the closed point of
the field spectrum, which is exactly `AlgebraicGeometry.Space.schemePoint`; that is why
`AlgebraicGeometry.Space.chartPoint_selfNeighborhood` is a `rfl`.

The weak-association statements are the chart conditions of Stacks 0CTW, which
`StacksFrontier/AlgebraicGeometry/Spaces/WeaklyAssociatedTFAE.lean` proves for an arbitrary étale
scheme chart of an arbitrary algebraic space, instantiated at this chart. Their content here is
therefore the instantiation and the identification of the chart point, not the transfer itself.

What is *not* here is any comparison of this restriction with the associated-module functor
`AlgebraicGeometry.Space.representedAssociatedModule` of
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedModuleComparison.lean`, which runs in the
opposite direction, nor with the composite of
`AlgebraicGeometry.Space.representedModuleRestriction` with
`AlgebraicGeometry.SmallEtale.restrictModule`, which lands in the same place by a different
route. No adjunction between the two directions is claimed and neither composite is identified
with an identity.

That gap is about *this* restriction, the chart restriction along the identity chart, and nothing
more.  Stacks 03DX (2) at `τ = étale` **is** available.  The implementation notes of
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleEssentialImage.lean` describe
only what is missing in that file, which is upstream of the proof.  The counit of the
associated-module adjunction of the small étale site of a scheme is an isomorphism at every
quasi-coherent module with no hypothesis
(`AlgebraicGeometry.SmallEtale.isIso_counit'`, with the named isomorphism
`AlgebraicGeometry.SmallEtale.associatedModuleRestrictModuleIso`), essential surjectivity and the
equivalence are unconditional
(`AlgebraicGeometry.SmallEtale.quasicoherentIsEssImageAssociatedModule`,
`AlgebraicGeometry.SmallEtale.associatedModuleEquivalence'`), and the tag is registered.  What is
absent is the comparison of those statements, which are about
`AlgebraicGeometry.SmallEtale.restrictModule`, with the chart restriction below, which is a
different functor.

The last section is about the behaviour of the comparison along a morphism `g : U ⟶ U'` of the
big fppf site. What one wants there is the identification
`(g^*M)|_{h_U} ≅ (T_g)^*(M|_{h_{U'}})` of the restriction of a pullback with the pullback of a
restriction, `T_g` being the morphism of representing schemes; it is the represented case of the
hypothesis `hsquare` of
`AlgebraicGeometry.Space.isLocallyProjective_restrictToChartScheme_modulePullback` and of
`AlgebraicGeometry.Space.ChartRestrictionBaseChange`.  It is not proved in this file, but it
**is** proved, for a quasi-coherent `M` and an arbitrary `g`, as
`AlgebraicGeometry.Space.representedZariskiRestrictionBaseChangeIso` of
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedZariskiRestrictionBaseChange.lean`; that file
reads the general chart statement below at the two identity charts.

No adjoint-uniqueness argument produces it: `AlgebraicGeometry.Space.modulePullback` is a tensor
product formed on the small étale topos, while the restriction to the identity chart restricts
sections along the inclusion of the Zariski opens, which is the shape of the right adjoint
`AlgebraicGeometry.SmallEtale.restrictModule` of the associated-module adjunction rather than of
a left adjoint, so the two sides are not two left adjoints of one functor.  For a
*quasi-coherent* module it is nevertheless available, along an arbitrary `g`, by the route the
source takes: the counit of the associated-module adjunction is an isomorphism there, so the
module is the associated module of its own restriction and the associated module commutes with
pullback.  That is
`AlgebraicGeometry.Space.nonempty_restrictToChartScheme_baseChange_of_isQuasicoherent` of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartSchemeRestrictionBaseChange.lean`, and
`AlgebraicGeometry.Space.restrictToChartBaseChangeIso` of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartRestrictionBaseChange.lean` carries it over to
`AlgebraicGeometry.Space.restrictToChart`; what quasi-coherence buys is exactly the clause of
Descent, Proposition Stacks 03DX (2) which
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleEssentialImage.lean` records
as available only over an essential surjectivity it does not have in general.

What the last section does supply is the two halves of the comparison for an *étale* `g`, where
`AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback` of Stacks 03LW replaces the
pullback by plain restriction along `AlgebraicGeometry.Space.smallEtalePostcomp` and the question
becomes the identification of the restriction to the identity chart of `h_U` with the restriction
to the chart `AlgebraicGeometry.Space.etaleHomChart`. The two halves below are the index functor
and the change of scalars of those two restrictions, and both agree on the nose. Assembling them
into an identification of the restrictions themselves is
`AlgebraicGeometry.Space.restrictToChart_etaleModulePullback_selfChart` of
`StacksFrontier/AlgebraicGeometry/Spaces/EtaleRestrictionPullback.lean`, an equality of the two
sheaves of modules and not merely an isomorphism; the one further step it needs is the
commutation of the universe lift of the sections with restriction along a functor of sites, which
is `Stacks.SheafOfModules.pushforward_ulift_pushforward_id` stated for bare data. What is still
not available, there or here, is the identification of the restriction to the chart
`AlgebraicGeometry.Space.etaleHomChart` with the Zariski pullback along the morphism of
representing schemes of the restriction to the identity chart of `h_{U'}`: that is the chartwise
comparison `AlgebraicGeometry.Space.restrictToChartSchemePullbackComparison`, which is only a
morphism, and the conditions of Stacks 03M0 which make it an isomorphism are stated for
`AlgebraicGeometry.Space.restrictToChartScheme`, a construction not definitionally equal to
`AlgebraicGeometry.Space.restrictToChart`. So the represented case of
`AlgebraicGeometry.Space.ChartRestrictionBaseChange` does not follow even for an étale `g`.

Nothing here is tagged. The comparison is a functor with no inverse, so it is neither clause of
Stacks 03DX; the equivalence of sites of Stacks 04M0 is already carried by
`AlgebraicGeometry.Space.smallEtaleEquivalenceOverChart`; and the weak-association results
below are the already-tagged chart conditions of Stacks 0CTW, from
`StacksFrontier/AlgebraicGeometry/Spaces/WeaklyAssociatedTFAE.lean`, read at one particular chart
and with an extra hypothesis in one direction, so they assert less than that tag does.

## References

* [Stacks Project, Lemma 71.2.1 (Tag 0CTW)](https://stacks.math.columbia.edu/tag/0CTW)
* [Stacks Project, Tag 056L](https://stacks.math.columbia.edu/tag/056L)
* [Stacks Project, Tag 03BV](https://stacks.math.columbia.edu/tag/03BV)
* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED)
* [Stacks Project, Tag 05VP](https://stacks.math.columbia.edu/tag/05VP)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)

/-! ### The identity chart of a represented presheaf -/

/-- The identity of a represented presheaf is an étale chart of it: the étale-chart condition
on a costructured arrow is the étale-chart condition on its underlying morphism of presheaves,
which for an identity is `AlgebraicGeometry.Space.presheaf_etale_id`. -/
theorem isEtaleChart_id_yoneda :
    IsEtaleChart B S hS (yoneda.obj U) (CostructuredArrow.mk (𝟙 (yoneda.obj U))) :=
  presheaf_etale_id B S hS U

/-- The identity chart of a represented presheaf: the object of the small étale site of
`yoneda.obj U` given by the identity, whose underlying scheme is the scheme underlying `U`. -/
def selfChart : SmallEtale B S hS (yoneda.obj U) :=
  ⟨CostructuredArrow.mk (𝟙 (yoneda.obj U)), isEtaleChart_id_yoneda B S hS U⟩

/-- The scheme underlying the identity chart of `yoneda.obj U` is the scheme underlying `U`. -/
theorem etaleChartScheme_selfChart :
    etaleChartScheme B S hS (selfChart B S hS U) = (BigFppfOver.toScheme B S hS).obj U :=
  rfl

/-! ### Restricting a module to the representing scheme -/

/-- **The comparison of the modules of a represented algebraic space with the modules of the
representing scheme.** An `𝒪`-module on the small étale site of `yoneda.obj U` restricts, along
the identity chart, to a sheaf of modules on the Zariski site of the scheme underlying `U`. -/
noncomputable def representedZariskiRestrictionFunctor
    (hU : IsAlgebraicSpace B S hS (yoneda.obj U)) :
    Modules.{u, u} B S hS (yoneda.obj U) hU ⥤
      ((BigFppfOver.toScheme B S hS).obj U).Modules :=
  restrictToChartFunctor B S hS hU (selfChart B S hS U)

/-- The comparison of `AlgebraicGeometry.Space.representedZariskiRestrictionFunctor` on a single
module: the restriction of an `𝒪`-module on the small étale site of `yoneda.obj U` to the
Zariski site of the scheme underlying `U`. -/
noncomputable def representedZariskiRestriction
    (hU : IsAlgebraicSpace B S hS (yoneda.obj U))
    (M : Modules.{u, u} B S hS (yoneda.obj U) hU) :
    ((BigFppfOver.toScheme B S hS).obj U).Modules :=
  restrictToChart B S hS hU M (selfChart B S hS U)

/-- The comparison functor agrees on objects with
`AlgebraicGeometry.Space.representedZariskiRestriction`. -/
theorem representedZariskiRestrictionFunctor_obj
    (hU : IsAlgebraicSpace B S hS (yoneda.obj U))
    (M : Modules.{u, u} B S hS (yoneda.obj U) hU) :
    (representedZariskiRestrictionFunctor B S hS U hU).obj M =
      representedZariskiRestriction B S hS U hU M :=
  rfl

/-- An isomorphism of `𝒪`-modules on a represented algebraic space restricts to an isomorphism
of sheaves of modules on the representing scheme. -/
noncomputable def representedZariskiRestrictionIso
    (hU : IsAlgebraicSpace B S hS (yoneda.obj U))
    {M N : Modules.{u, u} B S hS (yoneda.obj U) hU} (e : M ≅ N) :
    representedZariskiRestriction B S hS U hU M ≅
      representedZariskiRestriction B S hS U hU N :=
  (representedZariskiRestrictionFunctor B S hS U hU).mapIso e

/-! ### The canonical neighbourhood of a geometric point -/

/-- The identity chart of a represented presheaf, with the canonical lift of a geometric point:
a geometric point of `yoneda.obj U` *is* a morphism from a field spectrum of the site to `U`,
and that morphism is its lift to the identity chart. -/
def selfNeighborhood (x : GeometricPoint B S hS (yoneda.obj U)) :
    SmallEtaleNeighborhood x where
  chart := selfChart B S hS U
  point := x.val.value
  point_comp := rfl

/-- **The point of the representing scheme selected by the canonical neighbourhood of a
geometric point** is the image of that geometric point under the comparison of Stacks 03BV: both
are the image of the closed point of the field spectrum along the section. -/
theorem chartPoint_selfNeighborhood (x : GeometricPoint B S hS (yoneda.obj U)) :
    chartPoint B S hS (yoneda.obj U) (selfNeighborhood B S hS U x) =
      pointsToScheme B S hS U x.image :=
  rfl

/-! ### Weakly associated points -/

/-- **The weak assassin of a represented algebraic space contains the Zariski weak assassin of
the representing scheme.** Let `M` be a quasi-coherent `𝒪`-module on the algebraic space
represented by `U` and let `x̄` be a geometric point of it. If the point of the representing
scheme below `x̄` is weakly associated, in the Zariski sense of Stacks 056L, to the restriction
of `M`, then the point of the algebraic space below `x̄` is weakly associated to `M`. -/
theorem isWeaklyAssociatedPoint_of_isWeaklyAssociatedPoint_zariski
    (hU : IsAlgebraicSpace B S hS (yoneda.obj U))
    (M : Modules.{u, u} B S hS (yoneda.obj U) hU) [M.IsQuasicoherentOnSite]
    (x : GeometricPoint B S hS (yoneda.obj U))
    (h : Stacks.Divisors.IsWeaklyAssociatedPoint
      (representedZariskiRestriction B S hS U hU M) (pointsToScheme B S hS U x.image)) :
    IsWeaklyAssociatedPoint B S hS ⟨yoneda.obj U, hU⟩ M x.image :=
  isWeaklyAssociatedPoint_of_isWeaklyAssociatedPoint_restrictToChart B S hS
    ⟨yoneda.obj U, hU⟩ M x.image rfl (selfNeighborhood B S hS U x) h

/-- **The weak assassin of a represented algebraic space is contained in the Zariski weak
assassin of the representing scheme.** If a point of the algebraic space represented by `U` is
weakly associated to a quasi-coherent `𝒪`-module `M`, then the corresponding point of the
representing scheme is weakly associated, in the Zariski sense of Stacks 056L, to the
restriction of `M`.

This is the direction (3) ⟹ (1) of Stacks 0CTW at the identity chart, which descends weak
association along the strict henselization of Stacks 04KF by Stacks 0CTU, so it asks nothing of
the representing scheme. -/
theorem isWeaklyAssociatedPoint_zariski_of_isWeaklyAssociatedPoint
    (hU : IsAlgebraicSpace B S hS (yoneda.obj U))
    (M : Modules.{u, u} B S hS (yoneda.obj U) hU) [M.IsQuasicoherentOnSite]
    (z : points B S hS (yoneda.obj U))
    (h : IsWeaklyAssociatedPoint B S hS ⟨yoneda.obj U, hU⟩ M z) :
    Stacks.Divisors.IsWeaklyAssociatedPoint (representedZariskiRestriction B S hS U hU M)
      (pointsToScheme B S hS U z) := by
  obtain ⟨xbar, hxbar, hstalk⟩ := h
  have hchart := isWeaklyAssociatedPoint_restrictToChart_of_isWeaklyAssociatedPrime B S hS
    ⟨yoneda.obj U, hU⟩ (selfNeighborhood B S hS U xbar) M hstalk
  rw [chartPoint_selfNeighborhood B S hS U xbar, hxbar] at hchart
  exact hchart

/-- **The weak assassin of a represented algebraic space is the Zariski weak assassin of the
representing scheme.** A point of the algebraic space represented by `U` is weakly associated
to a quasi-coherent `𝒪`-module `M` exactly when the corresponding point of the representing
scheme is weakly associated, in the Zariski sense of Stacks 056L, to the restriction of `M`. -/
theorem isWeaklyAssociatedPoint_iff_isWeaklyAssociatedPoint_zariski
    (hU : IsAlgebraicSpace B S hS (yoneda.obj U))
    (M : Modules.{u, u} B S hS (yoneda.obj U) hU) [M.IsQuasicoherentOnSite]
    (z : points B S hS (yoneda.obj U)) :
    IsWeaklyAssociatedPoint B S hS ⟨yoneda.obj U, hU⟩ M z ↔
      Stacks.Divisors.IsWeaklyAssociatedPoint (representedZariskiRestriction B S hS U hU M)
        (pointsToScheme B S hS U z) := by
  refine ⟨isWeaklyAssociatedPoint_zariski_of_isWeaklyAssociatedPoint B S hS U hU M z,
    fun h => ?_⟩
  obtain ⟨x, rfl⟩ := exists_geometricRepresentative B S hS (yoneda.obj U) z
  exact isWeaklyAssociatedPoint_of_isWeaklyAssociatedPoint_zariski B S hS U hU M x h

/-- **The weak assassin of a represented algebraic space is the Zariski weak assassin of the
representing scheme, as an equality of sets of points.** The weakly associated points of a
quasi-coherent `𝒪`-module on the algebraic space represented by `U` are the preimage, under the
comparison of Stacks 03BV, of the Zariski weakly associated points of its restriction to the
representing scheme. -/
theorem weaklyAssociatedPoints_eq_preimage_zariski
    (hU : IsAlgebraicSpace B S hS (yoneda.obj U))
    (M : Modules.{u, u} B S hS (yoneda.obj U) hU) [M.IsQuasicoherentOnSite] :
    weaklyAssociatedPoints B S hS ⟨yoneda.obj U, hU⟩ M =
      pointsToScheme B S hS U ⁻¹'
        Stacks.Divisors.weaklyAssociatedPoints (representedZariskiRestriction B S hS U hU M) :=
  Set.ext fun z =>
    isWeaklyAssociatedPoint_iff_isWeaklyAssociatedPoint_zariski B S hS U hU M z

/-! ### Charts coming from an étale morphism of the site -/

section EtaleHom

variable {U' : BigFppfOver B S hS}

/-- An étale morphism `g : U ⟶ U'` of the big fppf site, read as an étale chart of
`yoneda.obj U'`: the chart condition for `yoneda.map g` is étaleness of the morphism of schemes
underlying `g`. The scheme underlying the chart is the scheme underlying `U`. -/
def etaleHomChart (g : U ⟶ U')
    (hg : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map g)) :
    SmallEtale B S hS (yoneda.obj U') :=
  ⟨CostructuredArrow.mk (yoneda.map g), (presheaf_yoneda_map_etale_iff B S hS g).2 hg⟩

/-- The scheme underlying `AlgebraicGeometry.Space.etaleHomChart` is the scheme underlying the
source of the morphism, so the restriction of a module to that chart lands in
`AlgebraicGeometry.Scheme.Modules` of the same scheme as the restriction to
`AlgebraicGeometry.Space.selfChart` of the source. -/
theorem etaleChartScheme_etaleHomChart (g : U ⟶ U')
    (hg : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map g)) :
    etaleChartScheme B S hS (etaleHomChart B S hS U g hg) =
      (BigFppfOver.toScheme B S hS).obj U :=
  rfl

/-- The morphism of represented algebraic spaces induced by an étale morphism of the big fppf
site is étale, so the pullback of modules along it is étale restriction. -/
theorem isEtale_schemeSpaceMap (g : U ⟶ U')
    (hg : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map g)) :
    IsEtale B S hS (schemeSpaceMap g).hom :=
  (isEtale_iff_presheaf_of_yoneda B S hS (yoneda.map g)).2
    ((presheaf_yoneda_map_etale_iff B S hS g).2 hg)

/-- **The Zariski opens of the representing scheme are the same étale charts on either side of
an étale morphism of the site.** Reading a Zariski open of the scheme underlying `U` as an étale
chart of `yoneda.obj U` and then composing with `yoneda.map g` is reading it as an étale chart of
`yoneda.obj U'` through `g`; the two agree as functors of the open, on the nose.

This is the index half of the comparison of the restriction of an étale pullback to the identity
chart of its source with the restriction to the chart `g`; see the implementation notes. -/
theorem chartOpens_selfChart_comp_smallEtalePostcomp (g : U ⟶ U')
    (hg : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map g)) :
    chartOpens B S hS (selfChart B S hS U) ⋙
        smallEtalePostcomp B S hS (schemeSpaceMap g)
          (isEtale_schemeSpaceMap B S hS U g hg) =
      chartOpens B S hS (etaleHomChart B S hS U g hg) :=
  rfl

/-- **The change of scalars of the two chart restrictions agree.** The comparison of the sheaf
of functions on the scheme underlying `U` with the functions on its opens read as étale charts
is the same whether those opens are read as charts of `yoneda.obj U` or, through an étale
`g : U ⟶ U'`, as charts of `yoneda.obj U'`.

This is the coefficient half of the comparison of the restriction of an étale pullback to the
identity chart of its source with the restriction to the chart `g`; see the implementation
notes. -/
theorem chartRestrictionRingHom_selfChart_eq_etaleHomChart (g : U ⟶ U')
    (hg : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map g))
    (hU : IsAlgebraicSpace B S hS (yoneda.obj U))
    (hU' : IsAlgebraicSpace B S hS (yoneda.obj U')) :
    chartRestrictionRingHom B S hS hU (selfChart B S hS U) =
      chartRestrictionRingHom B S hS hU' (etaleHomChart B S hS U g hg) :=
  rfl

end EtaleHom

end AlgebraicGeometry.Space

end
