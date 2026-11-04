module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModuleComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Stacks.RestrictionComparisonAlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentModuleUniverse
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentSiteEquivalence

/-!
# The chart-local identification of restrictions (Stacks 0GQC, Remark 0GQA)

Let `𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids representable by an algebraic space
`F`. The proof of Stacks 0GQC rests on the displayed equality
`ℱ|_{U_étale} = (ℱ|_{F_étale})|_{U_étale}` for a scheme `U` étale over `F`, which the source
calls clear and refers to Remark 0GQA for. The two sides live on two different sites of this
library: the left on the small étale site `AlgebraicGeometry.SmallEtale` of the *scheme* `U`,
which local quasi-coherence (Stacks 06WJ) is stated on, and the right on the slice at the chart
of the small étale site `AlgebraicGeometry.Space.SmallEtale` of the algebraic space `F`.

This file builds the *site* half of that identification, unconditionally: the equivalence of
those two sites, continuous and a dense subsite in both directions, together with the equality
of the two structure sheaves across it. With those in hand, Stacks 0GQC is proved from the
module-level half of the identification alone, which is the single hypothesis `hiso` of
`AlgebraicGeometry.Space.isQuasicoherentOnSite_of_chartLocalModuleIdentification`; that half is
proved in `StacksFrontier/AlgebraicGeometry/Stacks/ChartRestrictionModuleIdentification.lean`.

## Main definitions

* `AlgebraicGeometry.Space.restrictionChartObject` and
  `AlgebraicGeometry.Space.restrictionChartModule`: the object of `𝒳` attached to an étale chart
  of `F`, and the restriction of Stacks 06WJ at it.
* `AlgebraicGeometry.Space.transportSmallEtale`: an equivalence out of the small étale site of a
  scheme, transported along an equality of schemes.
* `AlgebraicGeometry.Space.chartSchemeEquivalence`: the small étale site of the scheme underlying
  an étale chart `W` of `F` is the slice at `W` of the small étale site of `F`.
* `AlgebraicGeometry.Space.chartLocalSiteEquivalence`: the same equivalence, typed at the scheme
  below the object `u_F W` of `𝒳`, which is where local quasi-coherence lives, and
  `AlgebraicGeometry.Space.chartLocalSiteEquivalenceOver` the same again in the ringed-site
  reading.

## Main results

* `AlgebraicGeometry.Space.isQuasicoherentOnSite_of_forall_chart`: quasi-coherence of an
  `𝒪_F`-module follows from quasi-coherence of its restriction to the slice at every étale
  chart. This is the clause of Stacks 03DN for the covering family of *all* charts.
* `AlgebraicGeometry.Space.chartSchemeEquivalence_ringSheaf` and
  `AlgebraicGeometry.Space.chartLocalSiteEquivalence_ringSheaf`: **the two structure sheaves
  agree**, an equality and not merely an isomorphism. The first holds by `rfl`.
* `AlgebraicGeometry.Space.isContinuous_chartLocalSiteEquivalence_functor`,
  `AlgebraicGeometry.Space.isContinuous_chartLocalSiteEquivalence_inverse` and
  `AlgebraicGeometry.Space.isDenseSubsite_chartLocalSiteEquivalence_inverse`: the equivalence
  matches the two topologies.
* `AlgebraicGeometry.Space.isDenseSubsite_inverse_of_isContinuous`: an equivalence of categories
  continuous in both directions is a dense subsite inclusion in both directions.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_of_chartLocalModuleIdentification`:
  **Stacks 0GQC granted the module-level half of the chart-local identification**, and nothing
  else.

## Implementation notes

The equivalence of sites is the composite of
`AlgebraicGeometry.Space.representedSmallEtaleEquivalence` — the small étale site of the
algebraic space represented by a scheme is the small étale site of that scheme — with
`AlgebraicGeometry.Space.SmallEtale.chartLocalizationEquivalence`, Stacks 04M0. Both halves
carry their topology comparison, and both halves identify the two structure sheaves on the
nose: `AlgebraicGeometry.Space.reindexRing_chartLocalizationEquivalence` for the second, and for
the first the fact that `AlgebraicGeometry.Space.representedStructureMapInverse` is the identity.
The composite comparison is therefore again an equality, by `rfl`.

A transport intervenes. The functor `u_F : F_étale ⥤ 𝒳` of Stacks 073M lies over the base only
*propositionally*, `AlgebraicGeometry.Space.restrictionFunctor_comp` being proved from the
equality field of the chosen equivalence over the site; so the scheme below `u_F W` is only
propositionally the scheme underlying the chart `W`, while the composite equivalence above is
typed at the latter. `AlgebraicGeometry.Space.transportSmallEtale` moves the equivalence across
that equality, and each property of it is moved across by its own lemma, proved by substituting
the equality — the transport along an equality of schemes is the identity site, so nothing is
lost and the `rfl` comparisons survive.

The big étale site is taken to be `AlgebraicGeometry.associatedBigEtaleSite` of the big fppf
site, whose size cutoff is that of the big fppf site by `rfl`. That is the canonical choice of
the auxiliary étale site which local quasi-coherence needs and which the source does not make.

## The module-level half

The source's displayed equality has a second half which this file assumes rather than proves,
and it is not a formality; it is proved by `AlgebraicGeometry.Space.chartRestriction_iso`.
Restriction to the small étale site of the scheme below an object
`x` of `𝒳` — Stacks 06W1, `AlgebraicGeometry.Stack.restrictToSmallEtale`, which local
quasi-coherence is stated with — evaluates the module at
`(CategoryTheory.Over.post (p ⋙ CategoryTheory.Over.forget _)).inv.obj …`, a chosen
quasi-inverse of the localization equivalence of Stacks 06W0. Restriction along `u_F` —
equation 075K, `AlgebraicGeometry.Space.etaleRestrictedModuleInverseImage` — evaluates it at
`(AlgebraicGeometry.Space.restrictionFunctor …).obj …`, built from the chosen inverse of the
equivalence over the site. Those two objects of `𝒳` are isomorphic, by uniqueness of lifts in a
category fibred in groupoids, but they are *not* definitionally equal, and the comparison also
has to be shown semilinear for the two structure-sheaf identifications
`AlgebraicGeometry.Stack.localStructurePresheafIso` and
`AlgebraicGeometry.Space.etaleChartStructureHom`, which are built along the two different
routes. That is the content of Remark 0GQA at the module level.

## References

* [Stacks Project, Tag 0GQC](https://stacks.math.columbia.edu/tag/0GQC)
* [Stacks Project, Tag 0GQA](https://stacks.math.columbia.edu/tag/0GQA)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 073M](https://stacks.math.columbia.edu/tag/073M)
* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite

namespace AlgebraicGeometry.Space

universe u v w u₁ v₁ m

/-! ### Transport of the small étale site of a scheme along an equality of schemes -/

section Transport

variable (E : BigEtaleSite.{u})

/-- An equivalence out of the small étale site of a scheme `T'`, read as an equivalence out of
the small étale site of a scheme `T` equal to it. The two sites are the same site, so this is
the identity; it is spelled as a transport because the equality of the two schemes is not an
equality of syntactic terms. -/
noncomputable def transportSmallEtale {T T' : Scheme.{u}} (h : T = T')
    (hT : E.Contains T) (hT' : E.Contains T')
    {D : Type u₁} [Category.{v₁} D] (eqv : _root_.AlgebraicGeometry.SmallEtale E T' hT' ≌ D) :
    _root_.AlgebraicGeometry.SmallEtale E T hT ≌ D := by
  subst h
  exact eqv

/-- The transported equivalence has a continuous functor as soon as the original one does. -/
theorem isContinuous_transportSmallEtale_functor {T T' : Scheme.{u}} (h : T = T')
    (hT : E.Contains T) (hT' : E.Contains T')
    {D : Type u₁} [Category.{v₁} D] (JD : GrothendieckTopology D)
    (eqv : _root_.AlgebraicGeometry.SmallEtale E T' hT' ≌ D)
    (hcont : eqv.functor.IsContinuous (_root_.AlgebraicGeometry.SmallEtale.topology E T' hT') JD) :
    (transportSmallEtale E h hT hT' eqv).functor.IsContinuous
      (_root_.AlgebraicGeometry.SmallEtale.topology E T hT) JD := by
  subst h
  exact hcont

/-- The transported equivalence has a continuous inverse as soon as the original one does. -/
theorem isContinuous_transportSmallEtale_inverse {T T' : Scheme.{u}} (h : T = T')
    (hT : E.Contains T) (hT' : E.Contains T')
    {D : Type u₁} [Category.{v₁} D] (JD : GrothendieckTopology D)
    (eqv : _root_.AlgebraicGeometry.SmallEtale E T' hT' ≌ D)
    (hcont : eqv.inverse.IsContinuous JD (_root_.AlgebraicGeometry.SmallEtale.topology E T' hT')) :
    (transportSmallEtale E h hT hT' eqv).inverse.IsContinuous JD
      (_root_.AlgebraicGeometry.SmallEtale.topology E T hT) := by
  subst h
  exact hcont

/-- The structure sheaf comparison of an equivalence out of the small étale site of a scheme is
carried along the transport. -/
theorem reindexRing_transportSmallEtale {T T' : Scheme.{u}} (h : T = T')
    (hT : E.Contains T) (hT' : E.Contains T')
    {D : Type (u + 1)} [Category.{u} D] (JD : GrothendieckTopology D)
    (eqv : _root_.AlgebraicGeometry.SmallEtale E T' hT' ≌ D) (R : Sheaf JD RingCat.{u})
    (hcont : eqv.functor.IsContinuous (_root_.AlgebraicGeometry.SmallEtale.topology E T' hT') JD)
    (hR : @Stacks.SheafOfModules.reindexRing _ _ _ _ _
        (_root_.AlgebraicGeometry.SmallEtale.topology E T' hT') eqv hcont R =
      _root_.AlgebraicGeometry.SmallEtale.structureSheaf E T' hT') :
    @Stacks.SheafOfModules.reindexRing _ _ _ _ _
        (_root_.AlgebraicGeometry.SmallEtale.topology E T hT)
        (transportSmallEtale E h hT hT' eqv)
        (isContinuous_transportSmallEtale_functor E h hT hT' JD eqv hcont) R =
      _root_.AlgebraicGeometry.SmallEtale.structureSheaf E T hT := by
  subst h
  exact hR

end Transport

/-! ### An equivalence of sites from continuity in both directions -/

/-- For an equivalence of categories which is continuous in both directions, the inverse is a
dense subsite inclusion. Continuity is cover preservation, cover preservation of each functor is
cocontinuity of the other through the adjunction the equivalence provides, and an equivalence
cocontinuous in both directions is a dense subsite in both directions. -/
theorem isDenseSubsite_inverse_of_isContinuous {C : Type u₁} [Category.{v₁} C]
    {D : Type u} [Category.{v} D] (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (eqv : C ≌ D) (hF : eqv.functor.IsContinuous J K) (hG : eqv.inverse.IsContinuous K J) :
    eqv.inverse.IsDenseSubsite K J :=
  let hFcov : CoverPreserving J K eqv.functor :=
    (Functor.isContinuous_iff_coverPreserving (F := eqv.functor) (J := J) (K := K)).1 hF
  let hGcov : CoverPreserving K J eqv.inverse :=
    (Functor.isContinuous_iff_coverPreserving (F := eqv.inverse) (J := K) (K := J)).1 hG
  let _h1 : eqv.functor.IsCocontinuous J K :=
    (eqv.toAdjunction.isCocontinuous_iff_coverPreserving J K).2 hGcov
  let _h2 : eqv.inverse.IsCocontinuous K J :=
    (eqv.symm.toAdjunction.isCocontinuous_iff_coverPreserving K J).2 hFcov
  Equivalence.isDenseSubsite_inverse_of_isCocontinuous J K eqv

/-! ### The chart-local data of Stacks 06WJ

The restriction of Stacks 06WJ at the object of `𝒳` attached to an étale chart, the locality of
quasi-coherence over the family of all charts, and the transport of quasi-coherence along an
equality of coefficient sheaves. These are the ingredients of the chart-by-chart proof of
Stacks 0GQC, and they are independent of the identification of sites built below. -/

section ChartData

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (hE : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S) (U : AlgebraicSpaces B S hS)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)

/-- **The clause of Stacks 03DN for quasi-coherence, at the family of all étale charts.** An
`𝒪_F`-module on the small étale site of an algebraic space is quasi-coherent as soon as its
restriction to the slice at every étale chart is quasi-coherent.

Every object of the site is a member of the family, so this is
`Stacks.SheafOfModules.isQuasicoherentOnSite_of_forall_over`, which is the locality of
quasi-coherence with the universe of the module sections independent of the universe of the
sections of the structure sheaf. -/
theorem isQuasicoherentOnSite_of_forall_chart (hF : IsAlgebraicSpace B S hS U.1)
    (M : Modules.{u, m} B S hS U.1 hF)
    (h : ∀ W : (smallEtaleRingedSite B S hS U.1 hF).C, (M.over W).IsQuasicoherentOnSite) :
    M.IsQuasicoherentOnSite :=
  Stacks.SheafOfModules.isQuasicoherentOnSite_of_forall_over M h

/-- The object of `𝒳` attached to an étale chart of the algebraic space `U` representing `𝒳`:
the value at that chart of the functor `u_U : U_étale ⥤ 𝒳` of Stacks 073M. -/
noncomputable abbrev restrictionChartObject
    (e : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (U.1 ⋙ typeToCat)).p)
    (W : SmallEtale B S hS U.1) : 𝒳 :=
  (restrictionFunctor B S hS U.1 p e).obj W

/-- The restriction `ℱ|_{U_étale}` of Stacks 06WJ at the object of `𝒳` attached to an étale
chart, as a sheaf of modules on the small étale site of the scheme below that object. The sheaf
condition is the one local quasi-coherence asserts. -/
noncomputable def restrictionChartModule (hp : p.IsFiberedInGroupoids)
    (e : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (U.1 ⋙ typeToCat)).p)
    (ℱ : inheritedEtaleModules B S hS p hp)
    (hℱ : Stack.IsLocallyQuasicoherent B E hE S hS p hp ℱ.val)
    (W : SmallEtale B S hS U.1) :
    SheafOfModules.{m} (_root_.AlgebraicGeometry.SmallEtale.structureSheaf E
      (p.obj (restrictionChartObject B S hS U p e W)).left.1
      (Stack.contains_base B E hE S hS p (restrictionChartObject B S hS U p e W))) :=
  ⟨Stack.restrictModuleToSmallEtale B E hE S hS p hp (restrictionChartObject B S hS U p e W)
    (etaleTopology B) (Stack.etaleTopology_le_topology B) ℱ.val,
    (hℱ.2 (restrictionChartObject B S hS U p e W)).choose⟩

/-- Local quasi-coherence says exactly that `AlgebraicGeometry.Space.restrictionChartModule` is
quasi-coherent at every étale chart. -/
theorem isQuasicoherentOnSite_restrictionChartModule (hp : p.IsFiberedInGroupoids)
    (e : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (U.1 ⋙ typeToCat)).p)
    (ℱ : inheritedEtaleModules B S hS p hp)
    (hℱ : Stack.IsLocallyQuasicoherent B E hE S hS p hp ℱ.val)
    (W : SmallEtale B S hS U.1) :
    (restrictionChartModule B E hE S hS U p hp e ℱ hℱ W).IsQuasicoherentOnSite :=
  (hℱ.2 (restrictionChartObject B S hS U p e W)).choose_spec

end ChartData

/-- Quasi-coherence travels along an equality of the sheaf of rings of coefficients. -/
private theorem isQuasicoherentOnSite_cast {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {R R' : Sheaf J RingCat.{w}} (h : R = R')
    (M : SheafOfModules.{m} R) (hM : M.IsQuasicoherentOnSite) :
    (h ▸ M).IsQuasicoherentOnSite := by
  subst h
  exact hM

/-! ### The chart-local equivalence of sites -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (U : AlgebraicSpaces B S hS)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)

/-- The object of the big fppf site of `S` underlying an étale chart of the algebraic space
`U`. -/
noncomputable abbrev chartOverObject (W : SmallEtale B S hS U.1) : BigFppfOver B S hS :=
  (SmallEtale.toOver B S hS U.1).obj W

/-- The small étale site of the scheme underlying an étale chart `W` of `U`, taken in the big
étale site associated with the big fppf site. -/
noncomputable abbrev chartSchemeSite (W : SmallEtale B S hS U.1) :=
  _root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B S hS).obj (chartOverObject B S hS U W))
    (chartOverObject B S hS U W).left.property

/-- The small étale topology on `AlgebraicGeometry.Space.chartSchemeSite`. -/
noncomputable abbrev chartSchemeTopology (W : SmallEtale B S hS U.1) :
    GrothendieckTopology (chartSchemeSite B S hS U W) :=
  _root_.AlgebraicGeometry.SmallEtale.topology (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B S hS).obj (chartOverObject B S hS U W))
    (chartOverObject B S hS U W).left.property

/-- **Stacks 04M0 after Stacks 03ED.** The small étale site of the scheme underlying an étale
chart `W` of the algebraic space `U` is the slice at `W` of the small étale site of `U`: the
small étale site of the scheme is the small étale site of the algebraic space it represents
(`AlgebraicGeometry.Space.representedSmallEtaleEquivalence`), and that is the slice at the chart
(Stacks 04M0). -/
noncomputable def chartSchemeEquivalence (W : SmallEtale B S hS U.1) :
    chartSchemeSite B S hS U W ≌ Over W :=
  (representedSmallEtaleEquivalence B S hS (chartOverObject B S hS U W)).symm.trans
    (SmallEtale.chartLocalizationEquivalence B S hS U.1 W)

/-- The functor of `AlgebraicGeometry.Space.chartSchemeEquivalence` is continuous. -/
instance isContinuous_chartSchemeEquivalence_functor (W : SmallEtale B S hS U.1) :
    (chartSchemeEquivalence B S hS U W).functor.IsContinuous
      (chartSchemeTopology B S hS U W) ((SmallEtale.topology B S hS U.1).over W) :=
  Functor.isContinuous_comp
    (representedSmallEtaleEquivalence B S hS (chartOverObject B S hS U W)).inverse
    (SmallEtale.chartLocalizationEquivalence B S hS U.1 W).functor
    (chartSchemeTopology B S hS U W)
    (SmallEtale.topology B S hS (yoneda.obj (chartOverObject B S hS U W)))
    ((SmallEtale.topology B S hS U.1).over W)

/-- The inverse of the comparison equivalence of Stacks 04M0 is continuous: it is a dense
subsite inclusion. -/
instance isContinuous_chartLocalizationEquivalence_inverse' (W : SmallEtale B S hS U.1) :
    (SmallEtale.chartLocalizationEquivalence B S hS U.1 W).inverse.IsContinuous
      ((SmallEtale.topology B S hS U.1).over W)
      (SmallEtale.topology B S hS (yoneda.obj (chartOverObject B S hS U W))) :=
  @Functor.IsDenseSubsite.instIsContinuous _ _ _ _ _ _ _
    (isDenseSubsite_chartLocalizationEquivalence_inverse B S hS U W)

/-- The inverse of `AlgebraicGeometry.Space.chartSchemeEquivalence` is continuous. -/
instance isContinuous_chartSchemeEquivalence_inverse (W : SmallEtale B S hS U.1) :
    (chartSchemeEquivalence B S hS U W).inverse.IsContinuous
      ((SmallEtale.topology B S hS U.1).over W) (chartSchemeTopology B S hS U W) :=
  Functor.isContinuous_comp
    (SmallEtale.chartLocalizationEquivalence B S hS U.1 W).inverse
    (representedSmallEtaleEquivalence B S hS (chartOverObject B S hS U W)).functor
    ((SmallEtale.topology B S hS U.1).over W)
    (SmallEtale.topology B S hS (yoneda.obj (chartOverObject B S hS U W)))
    (chartSchemeTopology B S hS U W)

/-- **The two structure sheaves of the chart-local identification agree.** The structure sheaf
of the slice at an étale chart `W` of the small étale site of `U`, transported along
`AlgebraicGeometry.Space.chartSchemeEquivalence`, is the structure sheaf of the small étale site
of the scheme underlying `W`.

Both sides send an object to the ring of global regular functions on the same scheme, neither
half of the equivalence changing that scheme; so the comparison is an equality, which is what
makes the transport of quasi-coherence possible at all. -/
theorem chartSchemeEquivalence_ringSheaf (W : SmallEtale B S hS U.1) :
    @Stacks.SheafOfModules.reindexRing _ _ _ _ _ (chartSchemeTopology B S hS U W)
        (chartSchemeEquivalence B S hS U W)
        (isContinuous_chartSchemeEquivalence_functor B S hS U W)
        (((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS U.1 U.2).O)).over W) =
      _root_.AlgebraicGeometry.SmallEtale.structureSheaf (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj (chartOverObject B S hS U W))
        (chartOverObject B S hS U W).left.property :=
  rfl

/-! ### The chart-local equivalence at the object of `𝒳` attached to a chart -/

variable (e : StacksRepresentableCFG.EquivalenceOver p
  (presheafOfCategories (U.1 ⋙ typeToCat)).p)

/-- The scheme below the object of `𝒳` attached to an étale chart `W` of `U` is the scheme
underlying `W`: the functor `u_U : U_étale ⥤ 𝒳` of Stacks 073M is over the base. -/
theorem restrictionChartObject_base_eq (W : SmallEtale B S hS U.1) :
    (p.obj (restrictionChartObject B S hS U p e W)).left.1 =
      (BigFppfOver.toScheme B S hS).obj (chartOverObject B S hS U W) :=
  congrArg (fun V : BigFppfOver B S hS => V.left.1)
    (Functor.congr_obj (restrictionFunctor_comp B S hS U.1 p e) W)

/-- **The chart-local identification of sites.** The small étale site of the scheme below the
object of `𝒳` attached to an étale chart `W` of `U` is the slice at `W` of the small étale site
of `U`.

This is `AlgebraicGeometry.Space.chartSchemeEquivalence` transported along
`AlgebraicGeometry.Space.restrictionChartObject_base_eq`, which identifies that scheme with the
scheme underlying the chart. -/
noncomputable def chartLocalSiteEquivalence (W : SmallEtale B S hS U.1) :
    _root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B)
        (p.obj (restrictionChartObject B S hS U p e W)).left.1
        (Stack.contains_base B (associatedBigEtaleSite B) rfl S hS p
          (restrictionChartObject B S hS U p e W)) ≌ Over W :=
  transportSmallEtale (associatedBigEtaleSite B)
    (restrictionChartObject_base_eq B S hS U p e W) _
    (chartOverObject B S hS U W).left.property (chartSchemeEquivalence B S hS U W)

/-- The functor of the chart-local identification of sites is continuous. -/
instance isContinuous_chartLocalSiteEquivalence_functor (W : SmallEtale B S hS U.1) :
    (chartLocalSiteEquivalence B S hS U p e W).functor.IsContinuous
      (_root_.AlgebraicGeometry.SmallEtale.topology (associatedBigEtaleSite B)
        (p.obj (restrictionChartObject B S hS U p e W)).left.1
        (Stack.contains_base B (associatedBigEtaleSite B) rfl S hS p
          (restrictionChartObject B S hS U p e W)))
      ((SmallEtale.topology B S hS U.1).over W) :=
  isContinuous_transportSmallEtale_functor (associatedBigEtaleSite B)
    (restrictionChartObject_base_eq B S hS U p e W) _
    (chartOverObject B S hS U W).left.property _ (chartSchemeEquivalence B S hS U W)
    (isContinuous_chartSchemeEquivalence_functor B S hS U W)

/-- The inverse of the chart-local identification of sites is continuous. -/
instance isContinuous_chartLocalSiteEquivalence_inverse (W : SmallEtale B S hS U.1) :
    (chartLocalSiteEquivalence B S hS U p e W).inverse.IsContinuous
      ((SmallEtale.topology B S hS U.1).over W)
      (_root_.AlgebraicGeometry.SmallEtale.topology (associatedBigEtaleSite B)
        (p.obj (restrictionChartObject B S hS U p e W)).left.1
        (Stack.contains_base B (associatedBigEtaleSite B) rfl S hS p
          (restrictionChartObject B S hS U p e W))) :=
  isContinuous_transportSmallEtale_inverse (associatedBigEtaleSite B)
    (restrictionChartObject_base_eq B S hS U p e W) _
    (chartOverObject B S hS U W).left.property _ (chartSchemeEquivalence B S hS U W)
    (isContinuous_chartSchemeEquivalence_inverse B S hS U W)

/-- The inverse of the chart-local identification of sites is a dense subsite inclusion, which
is the form in which quasi-coherence is transported. -/
instance isDenseSubsite_chartLocalSiteEquivalence_inverse (W : SmallEtale B S hS U.1) :
    (chartLocalSiteEquivalence B S hS U p e W).inverse.IsDenseSubsite
      ((SmallEtale.topology B S hS U.1).over W)
      (_root_.AlgebraicGeometry.SmallEtale.topology (associatedBigEtaleSite B)
        (p.obj (restrictionChartObject B S hS U p e W)).left.1
        (Stack.contains_base B (associatedBigEtaleSite B) rfl S hS p
          (restrictionChartObject B S hS U p e W))) :=
  isDenseSubsite_inverse_of_isContinuous _ _ (chartLocalSiteEquivalence B S hS U p e W)
    (isContinuous_chartLocalSiteEquivalence_functor B S hS U p e W)
    (isContinuous_chartLocalSiteEquivalence_inverse B S hS U p e W)

/-- **The two structure sheaves of the chart-local identification agree, at the object of `𝒳`
attached to a chart.** This is
`AlgebraicGeometry.Space.chartSchemeEquivalence_ringSheaf` transported along
`AlgebraicGeometry.Space.restrictionChartObject_base_eq`. -/
theorem chartLocalSiteEquivalence_ringSheaf (W : SmallEtale B S hS U.1) :
    @Stacks.SheafOfModules.reindexRing _ _ _ _ _
        (_root_.AlgebraicGeometry.SmallEtale.topology (associatedBigEtaleSite B)
          (p.obj (restrictionChartObject B S hS U p e W)).left.1
          (Stack.contains_base B (associatedBigEtaleSite B) rfl S hS p
            (restrictionChartObject B S hS U p e W)))
        (chartLocalSiteEquivalence B S hS U p e W)
        (isContinuous_chartLocalSiteEquivalence_functor B S hS U p e W)
        (((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS U.1 U.2).O)).over W) =
      _root_.AlgebraicGeometry.SmallEtale.structureSheaf (associatedBigEtaleSite B)
        (p.obj (restrictionChartObject B S hS U p e W)).left.1
        (Stack.contains_base B (associatedBigEtaleSite B) rfl S hS p
          (restrictionChartObject B S hS U p e W)) :=
  reindexRing_transportSmallEtale (associatedBigEtaleSite B)
    (restrictionChartObject_base_eq B S hS U p e W) _
    (chartOverObject B S hS U W).left.property _ (chartSchemeEquivalence B S hS U W) _
    (isContinuous_chartSchemeEquivalence_functor B S hS U W)
    (chartSchemeEquivalence_ringSheaf B S hS U W)

/-! ### The same data in the ringed-site reading, and Stacks 0GQC with one hypothesis left -/

/-- `AlgebraicGeometry.Space.chartLocalSiteEquivalence`, read for an object of
`(AlgebraicGeometry.Space.smallEtaleRingedSite ‹_›).C` rather than of
`AlgebraicGeometry.Space.SmallEtale`, to which it is definitionally equal.

The two readings carry different `CategoryTheory.Category` instance terms on the same category,
hence different `CategoryTheory.Over` slices; the sheaves-of-modules API indexes an `𝒪_U`-module
over the ringed site's sheaf of rings, so it is the ringed reading that appears in the statement
of Stacks 0GQC. This is the same restatement that
`AlgebraicGeometry.Space.smallEtaleRingedSite_hasWeakSheafify_over` makes for sheafification. -/
noncomputable abbrev chartLocalSiteEquivalenceOver
    (W : (smallEtaleRingedSite B S hS U.1 U.2).C) :
    _root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B)
        (p.obj (restrictionChartObject B S hS U p e W)).left.1
        (Stack.contains_base B (associatedBigEtaleSite B) rfl S hS p
          (restrictionChartObject B S hS U p e W)) ≌ Over W :=
  chartLocalSiteEquivalence B S hS U p e W

/-- Continuity of the functor of `AlgebraicGeometry.Space.chartLocalSiteEquivalenceOver`, for
the topology of the ringed site. -/
instance isContinuous_chartLocalSiteEquivalenceOver_functor
    (W : (smallEtaleRingedSite B S hS U.1 U.2).C) :
    (chartLocalSiteEquivalenceOver B S hS U p e W).functor.IsContinuous
      (_root_.AlgebraicGeometry.SmallEtale.topology (associatedBigEtaleSite B)
        (p.obj (restrictionChartObject B S hS U p e W)).left.1
        (Stack.contains_base B (associatedBigEtaleSite B) rfl S hS p
          (restrictionChartObject B S hS U p e W)))
      ((smallEtaleRingedSite B S hS U.1 U.2).J.over W) :=
  isContinuous_chartLocalSiteEquivalence_functor B S hS U p e W

/-- `AlgebraicGeometry.Space.chartLocalSiteEquivalence_ringSheaf` in the ringed-site reading:
**the two structure sheaves of the chart-local identification agree.** -/
theorem chartLocalSiteEquivalenceOver_ringSheaf
    (W : (smallEtaleRingedSite B S hS U.1 U.2).C) :
    Stacks.SheafOfModules.reindexRing
        (_root_.AlgebraicGeometry.SmallEtale.topology (associatedBigEtaleSite B)
          (p.obj (restrictionChartObject B S hS U p e W)).left.1
          (Stack.contains_base B (associatedBigEtaleSite B) rfl S hS p
            (restrictionChartObject B S hS U p e W)))
        (chartLocalSiteEquivalenceOver B S hS U p e W)
        (((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS U.1 U.2).O)).over W) =
      _root_.AlgebraicGeometry.SmallEtale.structureSheaf (associatedBigEtaleSite B)
        (p.obj (restrictionChartObject B S hS U p e W)).left.1
        (Stack.contains_base B (associatedBigEtaleSite B) rfl S hS p
          (restrictionChartObject B S hS U p e W)) :=
  chartLocalSiteEquivalence_ringSheaf B S hS U p e W

variable (hp : p.IsFiberedInGroupoids)

/-- **Stacks 0GQC, with the chart-local identification of restrictions reduced to its
module-level half.** Let `𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids representable by
the algebraic space `U`, through a chosen equivalence over the site as in Stacks 073M. If `ℱ` is
a locally quasi-coherent `𝒪_𝒳`-module (Stacks 06WJ) then its restriction `ℱ|_{U_étale}`
(equation 075K) is quasi-coherent, granted `hiso` alone.

The hypothesis `hiso` is an extra hypothesis beyond the source's, so this is weaker than
Stacks 0GQC. What it supplies is the *site* half of the source's
displayed equality `ℱ|_{U_étale} = (ℱ|_{F_étale})|_{U_étale}` — the equivalence of sites, its
continuity, its dense-subsite property and the equality of the two structure sheaves. What
remains assumed is exactly the module-level half: that the restriction of `ℱ|_{U_étale}` to the
chart, transported across the equivalence of sites, is the restriction `ℱ|_{W_étale}` of
Stacks 06WJ at the object `u_U W` of `𝒳`. That half is proved by
`AlgebraicGeometry.Space.chartRestriction_iso`, which discharges `hiso` and leaves Stacks 0GQC
with the source's hypotheses and no others.

That half is not a formality, and the implementation notes of this file record why: the two
modules are sections of `ℱ` at two objects of `𝒳` which are *not* definitionally equal, one
produced by the chosen quasi-inverse of the localization equivalence of Stacks 06W0 and the
other by the chosen inverse of the equivalence over the site of Stacks 073M. -/
theorem isQuasicoherentOnSite_of_chartLocalModuleIdentification
    (ℱ : inheritedEtaleModules B S hS p hp)
    (hℱ : Stack.IsLocallyQuasicoherent B (associatedBigEtaleSite B) rfl S hS p hp ℱ.val)
    (hiso : ∀ W : (smallEtaleRingedSite B S hS U.1 U.2).C,
      (SheafOfModules.pushforward.{m} (𝟙 (Stacks.SheafOfModules.reindexRing
          (_root_.AlgebraicGeometry.SmallEtale.topology (associatedBigEtaleSite B)
            (p.obj (restrictionChartObject B S hS U p e W)).left.1
            (Stack.contains_base B (associatedBigEtaleSite B) rfl S hS p
              (restrictionChartObject B S hS U p e W)))
          (chartLocalSiteEquivalenceOver B S hS U p e W)
          (((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS U.1 U.2).O)).over W)))).obj
        ((etaleRestrictedModuleInverseImage B S hS p p hp hp e (𝟭 𝒳)
          (Functor.IsFibredOneMorphism.id p) ℱ).over W) ≅
      (chartLocalSiteEquivalenceOver_ringSheaf B S hS U p e W).symm ▸
        restrictionChartModule B (associatedBigEtaleSite B) rfl S hS U p hp e ℱ hℱ W) :
    (etaleRestrictedModuleInverseImage B S hS p p hp hp e (𝟭 𝒳)
      (Functor.IsFibredOneMorphism.id p) ℱ).IsQuasicoherentOnSite := by
  refine isQuasicoherentOnSite_of_forall_chart B S hS U U.2 _ fun W => ?_
  have hq := isQuasicoherentOnSite_cast
    (chartLocalSiteEquivalenceOver_ringSheaf B S hS U p e W).symm
    (restrictionChartModule B (associatedBigEtaleSite B) rfl S hS U p hp e ℱ hℱ W)
    (isQuasicoherentOnSite_restrictionChartModule B (associatedBigEtaleSite B) rfl S hS U p hp
      e ℱ hℱ W)
  have : (chartLocalSiteEquivalenceOver B S hS U p e W).inverse.IsDenseSubsite
      ((smallEtaleRingedSite B S hS U.1 U.2).J.over W)
      (_root_.AlgebraicGeometry.SmallEtale.topology (associatedBigEtaleSite B)
        (p.obj (restrictionChartObject B S hS U p e W)).left.1
        (Stack.contains_base B (associatedBigEtaleSite B) rfl S hS p
          (restrictionChartObject B S hS U p e W))) :=
    isDenseSubsite_chartLocalSiteEquivalence_inverse B S hS U p e W
  exact Stacks.SheafOfModules.isQuasicoherentOnSite_of_reindex'
    (chartLocalSiteEquivalenceOver B S hS U p e W) _ _
    (SheafOfModules.IsQuasicoherentOnSite.of_iso (hiso W).symm hq)

end AlgebraicGeometry.Space

end
