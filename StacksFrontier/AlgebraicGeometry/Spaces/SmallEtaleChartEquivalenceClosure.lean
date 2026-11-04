module

public import StacksFrontier.AlgebraicGeometry.Spaces.RingedSite
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartGlueing
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRestrictionInverseImage
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Restriction to the charts is restriction to the slices

Stacks 03LS describes a sheaf on the small étale site of an algebraic space `X` by its
restrictions to the étale scheme charts of `X` together with the comparison isomorphisms between
successive restrictions, and asserts that the description is an equivalence of categories.
`StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartGlueing` supplies the two ends of that
assertion — the glueing equivalence of Stacks 0GWK at the small étale site, whose data are
indexed by the *slices* `X_étale/U`, and the category
`AlgebraicGeometry.Space.ChartGlueingData`, whose data are indexed by the small étale sites of
the *charts* — and records that two inputs are missing.  This file supplies the first of them:
the two indexings of restriction agree.

Concretely, restriction to a chart and the chartwise inverse image of Stacks 03G2, part (3), are
restriction to a slice and the slice pullback, read through the comparison equivalence of
Stacks 04M0.  The proof needs the identification of Stacks 04M0 as a statement about the *named*
comparison functor rather than inside the existential quantifier of
`AlgebraicGeometry.Space.smallEtaleEquivalenceOverChart`, so that clause is reproved here as
`AlgebraicGeometry.Space.SmallEtale.chartLocalization_inducedTopology`.

## Main definitions

* `AlgebraicGeometry.Space.chartSliceSheafEquiv`: sheaves of sets on the localization of the
  small étale site of `X` at an étale scheme chart are sheaves of sets on the small étale site of
  that chart.
* `AlgebraicGeometry.Space.chartSliceSheafEquivOfCoefficients`: the same equivalence with the
  universe of the coefficients left free, which is what the small étale ringed topos needs.
* `AlgebraicGeometry.Space.chartLocalizationPostcompIso`: through the comparison functors of
  Stacks 04M0, postcomposition with the morphism of algebraic spaces represented by a morphism of
  charts is the slice functor `CategoryTheory.Over.map`.

## Main results

* `AlgebraicGeometry.Space.SmallEtale.chartLocalization_inducedTopology`: the small étale
  topology of a chart is induced along `AlgebraicGeometry.Space.SmallEtale.chartLocalization`
  from the localization of the small étale topology of `X` at the chart.  This is the first
  clause of Stacks 04M0, de-existentialised.
* `AlgebraicGeometry.Space.SmallEtale.chartLocalization_op_comp_structurePresheaf`,
  `AlgebraicGeometry.Space.SmallEtale.structureSheaf'_eq_chartLocalization_pushforward` and
  `AlgebraicGeometry.Space.SmallEtale.ringSheaf_eq_chartLocalization_pushforward`: the
  comparison functor of Stacks 04M0 matches the two structure sheaves, so a module on the
  localization of the small étale site of `X` at a chart is a module on the small étale site of
  that chart.
* `AlgebraicGeometry.Space.isEtale_chartToSpace` and
  `AlgebraicGeometry.Space.isEtale_chartMap`: the structure morphism of a chart and the morphism
  of algebraic spaces represented by a morphism of charts are étale, so that Stacks 03LQ applies
  to both.
* `AlgebraicGeometry.Space.chartRestriction_overPullbackIso` and
  `AlgebraicGeometry.Space.chartInverseImage_overMapPullbackIso`: restriction to a chart is
  restriction to the slice, and the chartwise inverse image is the slice pullback.

## Implementation notes

The topology clause of Stacks 04M0 is reproved rather than extracted: the tagged statement
`AlgebraicGeometry.Space.smallEtaleEquivalenceOverChart` asserts the existence of an equivalence
with that property, so the property is not available as a lemma about
`AlgebraicGeometry.Space.SmallEtale.chartLocalizationEquivalence`, which is what
`CategoryTheory.Equivalence.sheafCongr` needs.  The proof here is the one in that file, with the
equivalence fixed; nothing in it uses the algebraicity hypothesis of the tagged statement, which
is why it can be dropped.  No new `@[stacks 04M0]` site is added: the tag's parts are already
covered.

The structure-sheaf clause needs no reproof.  The structure presheaf is the underlying object of
the big fppf site of `S`, followed by global regular functions, so the clause of Stacks 04M0
asserting that the comparison preserves that underlying object —
`AlgebraicGeometry.Space.SmallEtale.chartLocalization_comp_forget_comp_toOver`, which is already
stated for the named comparison functor — gives it by `congrArg`.  Passing from the presheaf to
the sheaf of commutative rings, and from there to the sheaf of rings over which modules are
taken, is `CategoryTheory.ObjectProperty.FullSubcategory.ext` and a second `congrArg`, since a
sheaf is its presheaf together with a proof.

With the topology identified, `CategoryTheory.Equivalence.sheafCongr` is applied to the *inverse*
of the equivalence of Stacks 04M0, because its hypothesis is a dense-subsite property of the
quasi-inverse of the equivalence it is given, and what Stacks 04M0 provides is the property of
`AlgebraicGeometry.Space.SmallEtale.chartLocalization` itself.

Both comparisons are then instances of `CategoryTheory.Functor.sheafPushforwardContinuousComp'`,
because Stacks 03LQ rewrites the inverse image of an étale morphism as restriction along
postcomposition: the chartwise inverse image and the slice pullback become restrictions along two
isomorphic composites of functors of sites.  For the structure morphism of a chart the two
composites are even equal, which is `AlgebraicGeometry.Space.chartLocalization_comp_forget`.

The continuity instances of `AlgebraicGeometry.Space.SmallEtale.chartLocalization` are passed to
`CategoryTheory.Functor.sheafPushforwardContinuousComp'` explicitly.  They are instances, and
they are found by `infer_instance` when the goal is stated on its own, but not when the same goal
arises as a subgoal of that definition — not even with the instance in the local context.  The
two chart-shaped instances
`AlgebraicGeometry.Space.isDenseSubsite_chartLocalization_chartSpace` and
`AlgebraicGeometry.Space.isContinuous_chartLocalization_chartSpace` exist for the same reason:
instance search does not unfold `AlgebraicGeometry.Space.chartOver`, so a statement about
`AlgebraicGeometry.Space.chartSpace` is not matched by one about the represented presheaf.  The
two instances
`AlgebraicGeometry.Space.SmallEtale.isDenseSubsite_chartLocalizationEquivalence_functor` and
`AlgebraicGeometry.Space.SmallEtale.isContinuous_chartLocalizationEquivalence_functor` are the
same restatement one step further out: the comparison *equivalence* is a definition, so instance
search does not reduce its `CategoryTheory.Equivalence.functor` projection to the comparison
functor either, and a result phrased in terms of the equivalence — which is the phrasing every
transport along it uses — sees no instance at all without them.

## What Stacks 03LS needed beyond this file

The second missing input is untouched here: that the canonical chartwise datum of a sheaf
satisfies the cocycle condition `AlgebraicGeometry.Space.ChartGlueingData.transition_comp`.  That
condition is stated through `AlgebraicGeometry.Space.chartInverseImageComp`, which is an
`CategoryTheory.Adjunction.leftAdjointUniq`, so it is the adjoint mate of an associativity
statement about `AlgebraicGeometry.Space.smallToposMorphism_comp`.  That associativity is now
`AlgebraicGeometry.Space.smallToposMorphism_comp_inverseImage_assoc`, and the cocycle itself is
`AlgebraicGeometry.Space.chartRestrictionComp_cocycle`, proved from it in
`StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartCanonicalGlueing`.

With both inputs in hand the equivalence is still not reached, and the reason is a third
statement that neither supplies — now
`AlgebraicGeometry.Space.chartInverseImage_overMapPullbackIso_comp` and
`AlgebraicGeometry.Space.chartRestriction_overPullbackIso_comp`, from which
`AlgebraicGeometry.Space.chartGlueingEquivalence` is built.  Transporting a chartwise glueing
datum — or a morphism of chartwise data — to the slice-indexed
`CategoryTheory.SiteGlueing.GlueingData` requires knowing that the two comparisons proved here
carry `AlgebraicGeometry.Space.chartRestrictionComp` and
`AlgebraicGeometry.Space.chartInverseImageComp` to `CategoryTheory.Sheaf.pushforwardOverMapIso`
and `CategoryTheory.GrothendieckTopology.overMapPullbackComp`.  This is a compatibility of the
chart-to-slice dictionary with the composition isomorphisms on both sides, not an associativity
statement about either side: `AlgebraicGeometry.Space.smallToposMorphism_inverseImageIso`, out of
which both comparisons here are built, is itself an
`CategoryTheory.Adjunction.leftAdjointUniq` conjugated by the comparison equivalences of
Stacks 03G1, so the compatibility is a statement relating the composition comparisons of two
different adjunction systems, of the kind
`AlgebraicGeometry.Space.smallToposMorphism_comp_inverseImage_eq_lComp` is for one of them.

What the comparisons here *do* give unconditionally is faithfulness of the chartwise
description, `AlgebraicGeometry.Space.chartGlueingFunctor_faithful`, which needs only the
object-level dictionary and not its compatibility with composition.

## References

* [Stacks Project, Tag 03LS](https://stacks.math.columbia.edu/tag/03LS)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 03LQ](https://stacks.math.columbia.edu/tag/03LQ)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry.Space.SmallEtale

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- The topology of the small étale site of the presheaf represented by the source of an étale
chart `X` of `F` is the topology induced from the localization of the small étale topology of `F`
at `X` along `AlgebraicGeometry.Space.SmallEtale.chartLocalization`.

This is the first clause of `AlgebraicGeometry.Space.smallEtaleEquivalenceOverChart`
(Stacks 04M0), stated for the named equivalence rather than inside its existential quantifier,
which is what makes it usable as the hypothesis of
`CategoryTheory.Equivalence.sheafCongr`. -/
theorem chartLocalization_inducedTopology (X : SmallEtale B S hS F) :
    (chartLocalization B S hS F X).inducedTopology ((topology B S hS F).over X) =
      topology B S hS (yoneda.obj ((toOver B S hS F).obj X)) := by
  let U := (toOver B S hS F).obj X
  let e := chartLocalizationEquivalence B S hS F X
  let Φ := e.functor
  let Ψ := e.inverse
  let PF := precoverage B S hS F
  let Psrc := precoverage B S hS (yoneda.obj U)
  let Q := PF.comap (Over.forget X)
  let K := Psrc.toGrothendieck
  let L := Q.toGrothendieck
  have hΦcov : CoverPreserving K L Φ := by
    refine coverPreserving_of_generators Φ Psrc L ?_
    intro A R hR
    obtain ⟨E, rfl, hE⟩ := (mem_precoverage_iff B S hS (yoneda.obj U)).mp hR
    rw [← Sieve.generate_map_eq_functorPushforward]
    refine Precoverage.generate_mem_toGrothendieck ?_
    show Presieve.map (Over.forget X) (Presieve.map Φ E.presieve₀) ∈
      PF ((Over.forget X).obj (Φ.obj A))
    refine (mem_precoverage_iff B S hS F).2 ⟨E.map (Φ ⋙ Over.forget X), ?_, ?_⟩
    · simp [PreZeroHypercover.presieve₀_map]
    · exact hE
  have hΨcov : CoverPreserving L K Ψ := by
    refine coverPreserving_of_generators Ψ Q K ?_
    intro A R hR
    change R.map (Over.forget X) ∈ PF ((Over.forget X).obj A) at hR
    obtain ⟨E, hEeq, hE⟩ := (mem_precoverage_iff B S hS F
      (X := (Over.forget X).obj A) (R := R.map (Over.forget X))).mp hR
    let E' : PreZeroHypercover.{u + 1} A :=
      { I₀ := E.I₀
        X i := Over.mk (E.f i ≫ A.hom)
        f i := Over.homMk (E.f i) (by simp) }
    have hsub : E'.presieve₀ ≤ R := by
      intro Z f hf
      obtain ⟨i⟩ := hf
      have hi : (R.map (Over.forget X)) (E.f i) := by
        rw [hEeq]; exact E.presieve₀_f i
      obtain ⟨T, hT, g, hg, hfac⟩ := Presieve.map_iff.mp hi
      obtain ⟨T₀, tHom, rfl⟩ := T.mk_surjective
      obtain rfl : T₀ = E.X i := by simpa using hT
      have hglef : g.left = E.f i := by simpa using hfac
      obtain rfl : tHom = E.f i ≫ A.hom := by
        have hw := Over.w g
        simpa [hglef] using hw.symm
      have hgf : g = E'.f i := Over.OverMorphism.ext hglef
      simpa [hgf] using hg
    have hE' : (E'.map Ψ).presieve₀ ∈ Psrc (Ψ.obj A) := by
      refine (mem_precoverage_iff B S hS (yoneda.obj U)
        (X := Ψ.obj A) (R := (E'.map Ψ).presieve₀)).2 ⟨E'.map Ψ, rfl, ?_⟩
      exact hE
    have hle : Sieve.generate (E'.presieve₀.map Ψ) ≤ Sieve.generate (R.map Ψ) := by
      rw [Sieve.generate_map_eq_functorPushforward, Sieve.generate_map_eq_functorPushforward]
      exact Sieve.functorPushforward_monotone Ψ A (Sieve.generate_mono hsub)
    rw [← Sieve.generate_map_eq_functorPushforward]
    refine K.superset_covering hle ?_
    simpa [PreZeroHypercover.presieve₀_map] using (Precoverage.generate_mem_toGrothendieck hE')
  have hΨcocont : Ψ.IsCocontinuous L K :=
    (e.symm.toAdjunction.isCocontinuous_iff_coverPreserving L K).2 hΦcov
  have hΦcocont : Φ.IsCocontinuous K L :=
    (e.toAdjunction.isCocontinuous_iff_coverPreserving K L).2 hΨcov
  have hΦcont : Φ.IsContinuous K L := Functor.isContinuous_iff_coverPreserving.2 hΦcov
  have hDense : Φ.IsDenseSubsite K L := Equivalence.isDenseSubsite_functor_of_isCocontinuous K L e
  have hrestricted : Φ.restrictedTopology L = K := by
    ext A R
    rw [Functor.mem_restrictedTopology_iff]
    exact hDense.functorPushforward_mem_iff
  have hLeq : (topology B S hS F).over X = L := over_topology_eq B S hS F X
  rw [hLeq]
  exact Φ.restrictedTopology_eq_inducedTopology_of_isContinuous hrestricted

/-- The comparison functor of Stacks 04M0 is an equivalence of categories. -/
instance isEquivalence_chartLocalization (X : SmallEtale B S hS F) :
    (chartLocalization B S hS F X).IsEquivalence :=
  (chartLocalizationEquivalence B S hS F X).isEquivalence_functor

/-- The comparison functor of Stacks 04M0 is a dense subsite inclusion for the small étale
topology of the chart and the localization of the small étale topology of `F` at the chart. -/
instance isDenseSubsite_chartLocalization (X : SmallEtale B S hS F) :
    (chartLocalization B S hS F X).IsDenseSubsite
      (topology B S hS (yoneda.obj ((toOver B S hS F).obj X)))
      ((topology B S hS F).over X) := by
  rw [← chartLocalization_inducedTopology B S hS F X]
  infer_instance

/-- The comparison functor of Stacks 04M0 is continuous for the small étale topology of the
chart and the localization of the small étale topology of `F` at the chart, so restriction of
sections along it carries sheaves to sheaves.

This is an immediate consequence of
`AlgebraicGeometry.Space.SmallEtale.isDenseSubsite_chartLocalization`, but the implication is
applied here by hand: searching for the dense-subsite hypothesis as a subgoal of Mathlib's
`CategoryTheory.Functor.IsDenseSubsite.instIsContinuous` does not find that instance. -/
instance isContinuous_chartLocalization (X : SmallEtale B S hS F) :
    (chartLocalization B S hS F X).IsContinuous
      (topology B S hS (yoneda.obj ((toOver B S hS F).obj X)))
      ((topology B S hS F).over X) :=
  @Functor.IsDenseSubsite.instIsContinuous _ _ _ _ _ _ _
    (isDenseSubsite_chartLocalization B S hS F X)

/-- `AlgebraicGeometry.Space.SmallEtale.isDenseSubsite_chartLocalization`, phrased for the
functor of the comparison *equivalence* of Stacks 04M0, which is the form typeclass search can
use: the two statements are definitionally equal, but
`AlgebraicGeometry.Space.SmallEtale.chartLocalizationEquivalence` is a definition and instance
search does not unfold its `CategoryTheory.Equivalence.functor` projection. -/
instance isDenseSubsite_chartLocalizationEquivalence_functor (X : SmallEtale B S hS F) :
    (chartLocalizationEquivalence B S hS F X).functor.IsDenseSubsite
      (topology B S hS (yoneda.obj ((toOver B S hS F).obj X)))
      ((topology B S hS F).over X) :=
  isDenseSubsite_chartLocalization B S hS F X

/-- `AlgebraicGeometry.Space.SmallEtale.isContinuous_chartLocalization`, phrased for the functor
of the comparison *equivalence* of Stacks 04M0, which is the form typeclass search can use.  This
is what lets a sheaf on the localization of the small étale site of `F` at the chart be restricted
along the equivalence rather than along the bare functor. -/
instance isContinuous_chartLocalizationEquivalence_functor (X : SmallEtale B S hS F) :
    (chartLocalizationEquivalence B S hS F X).functor.IsContinuous
      (topology B S hS (yoneda.obj ((toOver B S hS F).obj X)))
      ((topology B S hS F).over X) :=
  isContinuous_chartLocalization B S hS F X

/-! ### Stacks 04M0 on structure sheaves -/

/-- The structure presheaf of the small étale site of the presheaf represented by the source of
an étale chart `X` of `F` is the structure presheaf of `F` restricted along the comparison
functor of Stacks 04M0 and the slice projection: both send an étale chart of the chart to the
ring of global regular functions on its underlying scheme.

This is the second clause of `AlgebraicGeometry.Space.smallEtaleEquivalenceOverChart`
(Stacks 04M0) read through global functions, stated for the named comparison functor. -/
theorem chartLocalization_op_comp_structurePresheaf (X : SmallEtale B S hS F) :
    (chartLocalization B S hS F X).op ⋙ (Over.forget X).op ⋙ structurePresheaf B S hS F =
      structurePresheaf B S hS (yoneda.obj ((toOver B S hS F).obj X)) :=
  congrArg (fun H : SmallEtale B S hS (yoneda.obj ((toOver B S hS F).obj X)) ⥤
      BigFppfOver B S hS => (H ⋙ BigFppfOver.toScheme B S hS).op ⋙ Scheme.Γ)
    (chartLocalization_comp_forget_comp_toOver B S hS F X)

/-- **The comparison of Stacks 04M0 matches the structure sheaves of commutative rings.** The
structure sheaf of the small étale site of the presheaf represented by the source of an étale
chart `X` of `F` is the restriction, along the comparison functor of Stacks 04M0, of the
structure sheaf of `F` localized at `X`. -/
theorem structureSheaf'_eq_chartLocalization_pushforward (X : SmallEtale B S hS F) :
    structureSheaf' B S hS (yoneda.obj ((toOver B S hS F).obj X)) =
      ((chartLocalization B S hS F X).sheafPushforwardContinuous CommRingCat.{u}
        (topology B S hS (yoneda.obj ((toOver B S hS F).obj X)))
        ((topology B S hS F).over X)).obj ((structureSheaf' B S hS F).over X) :=
  ObjectProperty.FullSubcategory.ext
    (chartLocalization_op_comp_structurePresheaf B S hS F X).symm

/-- **The comparison of Stacks 04M0 matches the structure sheaves of the ringed sites.** The
sheaf of rings over which the modules on the small étale site of an étale scheme chart `X` of an
algebraic space `F` are taken is the restriction, along the comparison functor of Stacks 04M0,
of the sheaf of rings of `F` localized at `X`.

This is what transports a sheaf of modules, and hence any property of one, across the
equivalence of sites of Stacks 04M0: the two sides of the equivalence carry the same structure
sheaf, so no change of scalars intervenes. -/
theorem ringSheaf_eq_chartLocalization_pushforward (hF : IsAlgebraicSpace B S hS F)
    (X : SmallEtale B S hS F) :
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS (yoneda.obj ((toOver B S hS F).obj X))
        (isAlgebraicSpace_yoneda B S hS ((toOver B S hS F).obj X))).O) =
      ((chartLocalization B S hS F X).sheafPushforwardContinuous RingCat.{u}
        (topology B S hS (yoneda.obj ((toOver B S hS F).obj X)))
        ((topology B S hS F).over X)).obj
          (((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS F hF).O)).over X) :=
  ObjectProperty.FullSubcategory.ext
    (congrArg (fun P : (SmallEtale B S hS (yoneda.obj ((toOver B S hS F).obj X)))ᵒᵖ ⥤
        CommRingCat.{u} => P ⋙ forget₂ CommRingCat.{u} RingCat.{u})
      (chartLocalization_op_comp_structurePresheaf B S hS F X).symm)

end AlgebraicGeometry.Space.SmallEtale

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-- `AlgebraicGeometry.Space.SmallEtale.isDenseSubsite_chartLocalization` phrased for the
algebraic space `AlgebraicGeometry.Space.chartSpace` represented by the chart, which is the form
typeclass search can use: the two statements are definitionally equal, but the passage from
`chartSpace B S hS X U` to the represented presheaf unfolds
`AlgebraicGeometry.Space.chartOver`, which instance search does not do. -/
instance isDenseSubsite_chartLocalization_chartSpace (U : SmallEtale B S hS X.1) :
    (SmallEtale.chartLocalization B S hS X.1 U).IsDenseSubsite
      (SmallEtale.topology B S hS (chartSpace B S hS X U).1)
      ((SmallEtale.topology B S hS X.1).over U) :=
  SmallEtale.isDenseSubsite_chartLocalization B S hS X.1 U

/-- Continuity of the comparison functor of Stacks 04M0, in the form typeclass search can use.
It is an immediate consequence of
`AlgebraicGeometry.Space.isDenseSubsite_chartLocalization_chartSpace`, but the implication is
applied here by hand: searching for the dense-subsite hypothesis as a subgoal of Mathlib's
`CategoryTheory.Functor.IsDenseSubsite.instIsContinuous` does not find that instance, whereas
the same goal stated on its own is discharged by `infer_instance`. -/
instance isContinuous_chartLocalization_chartSpace (U : SmallEtale B S hS X.1) :
    (SmallEtale.chartLocalization B S hS X.1 U).IsContinuous
      (SmallEtale.topology B S hS (chartSpace B S hS X U).1)
      ((SmallEtale.topology B S hS X.1).over U) :=
  @Functor.IsDenseSubsite.instIsContinuous _ _ _ _ _ _ _
    (isDenseSubsite_chartLocalization_chartSpace B S hS X U)

/-- The structure morphism of an étale scheme chart is an étale morphism of algebraic spaces:
that is the defining property of the object of the spaces-étale site it becomes under the
comparison functor of Stacks 03G1. -/
theorem isEtale_chartToSpace (U : SmallEtale B S hS X.1) :
    IsEtale B S hS (chartToSpace B S hS X U).hom :=
  ((comparisonFunctor B S hS X).obj U).2

/-- The morphism of algebraic spaces represented by a morphism of étale scheme charts is étale:
it is the Yoneda morphism of a morphism of the big fppf site factoring one étale chart of `X`
through another, which is étale by cancellation between two étale charts. -/
theorem isEtale_chartMap {V U : SmallEtale B S hS X.1} (f : V ⟶ U) :
    IsEtale B S hS (chartMap B S hS X f).hom :=
  isEtale_of_presheaf_etale B S hS
    (SmallEtale.presheaf_etale_yoneda_map B S hS ((SmallEtale.toOver B S hS X.1).map f)
      V.property U.property (CostructuredArrow.w f.hom))

/-- **Stacks 04M0 on sheaves.** Sheaves of sets on the localization of the small étale site of
`X` at an étale scheme chart `U` are the same as sheaves of sets on the small étale site of the
chart.

This is `CategoryTheory.Equivalence.sheafCongr` for the equivalence of sites of Stacks 04M0,
whose hypothesis is
`AlgebraicGeometry.Space.SmallEtale.chartLocalization_inducedTopology`.

The coefficients are the sheaves of sets of the spaces-étale site, in `Type (u + 1)`, which is
the universe the glueing description of Stacks 03LS works at.  For the same equivalence at an
arbitrary coefficient universe — `Type u` for the small étale ringed topos of
`AlgebraicGeometry.Space.smallEtaleRingedTopos`, whose sheaves of sets take values there — see
`AlgebraicGeometry.Space.chartSliceSheafEquivOfCoefficients`. -/
noncomputable def chartSliceSheafEquiv (U : SmallEtale B S hS X.1) :
    Sheaf ((SmallEtale.topology B S hS X.1).over U) (Type (u + 1)) ≌
      Sheaf (SmallEtale.topology B S hS (chartSpace B S hS X U).1) (Type (u + 1)) :=
  haveI : (SmallEtale.chartLocalizationEquivalence B S hS X.1 U).symm.inverse.IsDenseSubsite
      (SmallEtale.topology B S hS (chartSpace B S hS X U).1)
      ((SmallEtale.topology B S hS X.1).over U) :=
    SmallEtale.isDenseSubsite_chartLocalization B S hS X.1 U
  Equivalence.sheafCongr ((SmallEtale.topology B S hS X.1).over U)
    (SmallEtale.topology B S hS (chartSpace B S hS X U).1)
    (SmallEtale.chartLocalizationEquivalence B S hS X.1 U).symm (Type (u + 1))

/-- **Stacks 04M0 on sheaves, at an arbitrary coefficient universe.** Sheaves on the
localization of the small étale site of `X` at an étale scheme chart `U`, with values in an
arbitrary `Type w`, are the same as sheaves on the small étale site of the chart with values
there.

This is `AlgebraicGeometry.Space.chartSliceSheafEquiv` with the universe of the coefficients
left free.  That universe is `u + 1` for the glueing description of Stacks 03LS, where the
sheaves are those of the spaces-étale site, and `u` for the small étale ringed topos of
`AlgebraicGeometry.Space.smallEtaleRingedTopos`, whose sheaves of sets take values in
`Type u`. -/
noncomputable def chartSliceSheafEquivOfCoefficients (U : SmallEtale B S hS X.1) :
    Sheaf ((SmallEtale.topology B S hS X.1).over U) (Type w) ≌
      Sheaf (SmallEtale.topology B S hS (chartSpace B S hS X U).1) (Type w) :=
  haveI : (SmallEtale.chartLocalizationEquivalence B S hS X.1 U).symm.inverse.IsDenseSubsite
      (SmallEtale.topology B S hS (chartSpace B S hS X U).1)
      ((SmallEtale.topology B S hS X.1).over U) :=
    SmallEtale.isDenseSubsite_chartLocalization B S hS X.1 U
  Equivalence.sheafCongr ((SmallEtale.topology B S hS X.1).over U)
    (SmallEtale.topology B S hS (chartSpace B S hS X U).1)
    (SmallEtale.chartLocalizationEquivalence B S hS X.1 U).symm (Type w)

/-- The comparison equivalences of Stacks 04M0 at two étale scheme charts `V ⟶ U` of `X` turn
postcomposition with the represented morphism of charts into the slice functor `Over.map`: an
étale chart of the chart `V`, read as an étale chart of `X` over `V` and then pushed to a chart
over `U`, is the same as its postcomposition with `V ⟶ U` read as a chart over `U`.

The underlying objects of the big fppf site of `S` are the same on both sides; what differs is
the structure morphism to `X`, where the two readings differ by the commuting triangle
`CostructuredArrow.w` of `f`. -/
noncomputable def chartLocalizationPostcompIso {V U : SmallEtale B S hS X.1} (f : V ⟶ U) :
    smallEtalePostcomp B S hS (chartMap B S hS X f) (isEtale_chartMap B S hS X f) ⋙
        SmallEtale.chartLocalization B S hS X.1 U ≅
      SmallEtale.chartLocalization B S hS X.1 V ⋙ Over.map f := by
  refine NatIso.ofComponents (fun A => ?_) ?_
  · refine Over.isoMk (ObjectProperty.isoMk (P := IsEtaleChart B S hS X.1)
      (CostructuredArrow.isoMk (Iso.refl _) ?_)) ?_
    · exact ((Category.assoc A.obj.hom
        (yoneda.map ((SmallEtale.toOver B S hS X.1).map f)) U.obj.hom).trans
        (congrArg (fun t => A.obj.hom ≫ t) (CostructuredArrow.w f.hom))).symm
    · refine ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ ?_)
      rfl
  · intro A A' m
    rfl

/-- The functor of `AlgebraicGeometry.Space.chartSliceSheafEquiv` is restriction along the
comparison functor of Stacks 04M0. -/
theorem chartSliceSheafEquiv_functor (U : SmallEtale B S hS X.1) :
    (chartSliceSheafEquiv B S hS X U).functor =
      (SmallEtale.chartLocalization B S hS X.1 U).sheafPushforwardContinuous (Type (u + 1))
        (SmallEtale.topology B S hS (chartSpace B S hS X U).1)
        ((SmallEtale.topology B S hS X.1).over U) := rfl

/-- The functor of `AlgebraicGeometry.Space.chartSliceSheafEquivOfCoefficients` is restriction
along the comparison functor of Stacks 04M0, at an arbitrary coefficient universe. -/
theorem chartSliceSheafEquivOfCoefficients_functor (U : SmallEtale B S hS X.1) :
    (chartSliceSheafEquivOfCoefficients.{w} B S hS X U).functor =
      (SmallEtale.chartLocalization B S hS X.1 U).sheafPushforwardContinuous (Type w)
        (SmallEtale.topology B S hS (chartSpace B S hS X U).1)
        ((SmallEtale.topology B S hS X.1).over U) := rfl

/-- The comparison functor of Stacks 04M0 at a chart `U`, followed by the slice projection, is
postcomposition with the structure morphism of the chart: both send an étale chart of `U` to the
étale chart of `X` obtained by composing with `U ⟶ X`. -/
theorem chartLocalization_comp_forget (U : SmallEtale B S hS X.1) :
    SmallEtale.chartLocalization B S hS X.1 U ⋙ Over.forget U =
      smallEtalePostcomp B S hS (chartToSpace B S hS X U)
        (isEtale_chartToSpace B S hS X U) := rfl

/-- **The first input owed by Stacks 03LS**, for the structure morphism of a chart: restriction
of a sheaf on the small étale site of `X` to an étale scheme chart `U` — the inverse image of
Stacks 03G2, part (3), along the structure morphism of the chart — is restriction to the slice
`X_étale/U`, read through the comparison equivalence of Stacks 04M0.

By Stacks 03LQ the chart restriction is restriction along postcomposition with the structure
morphism of the chart, which by `AlgebraicGeometry.Space.chartLocalization_comp_forget` is the
comparison functor of Stacks 04M0 followed by the slice projection. -/
@[sga "4 VII 1.6" "more general"]
noncomputable def chartRestriction_overPullbackIso (U : SmallEtale B S hS X.1) :
    chartRestriction B S hS X U ≅
      (SmallEtale.topology B S hS X.1).overPullback (Type (u + 1)) U ⋙
        (chartSliceSheafEquiv B S hS X U).functor := by
  have hu := isContinuous_chartLocalization_chartSpace B S hS X U
  have hfg : (SmallEtale.chartLocalization B S hS X.1 U ⋙ Over.forget U).IsContinuous
      (SmallEtale.topology B S hS (chartSpace B S hS X U).1) (SmallEtale.topology B S hS X.1) :=
    smallEtalePostcomp_isContinuous B S hS (chartToSpace B S hS X U)
      (isEtale_chartToSpace B S hS X U)
  have e₀ : chartRestriction B S hS X U ≅
      (smallEtalePostcomp B S hS (chartToSpace B S hS X U)
          (isEtale_chartToSpace B S hS X U)).sheafPushforwardContinuous (Type (u + 1))
        (SmallEtale.topology B S hS (chartSpace B S hS X U).1)
        (SmallEtale.topology B S hS X.1) :=
    smallToposMorphism_inverseImageIso B S hS (chartToSpace B S hS X U)
      (isEtale_chartToSpace B S hS X U)
  have e₁ : (SmallEtale.topology B S hS X.1).overPullback (Type (u + 1)) U ⋙
        (chartSliceSheafEquiv B S hS X U).functor ≅
      (smallEtalePostcomp B S hS (chartToSpace B S hS X U)
          (isEtale_chartToSpace B S hS X U)).sheafPushforwardContinuous (Type (u + 1))
        (SmallEtale.topology B S hS (chartSpace B S hS X U).1)
        (SmallEtale.topology B S hS X.1) :=
    @Functor.sheafPushforwardContinuousComp' _ _ _ _ _ _ _ _ _
      (Iso.refl (SmallEtale.chartLocalization B S hS X.1 U ⋙ Over.forget U)) (Type (u + 1)) _
      (SmallEtale.topology B S hS (chartSpace B S hS X U).1)
      ((SmallEtale.topology B S hS X.1).over U) (SmallEtale.topology B S hS X.1) hu _ hfg
  exact e₀ ≪≫ e₁.symm

/-- **The first input owed by Stacks 03LS**, for a morphism of charts: the chartwise inverse
image of Stacks 03G2, part (3), along a morphism `f : V ⟶ U` of étale scheme charts of `X` is
the slice pullback `CategoryTheory.GrothendieckTopology.overMapPullback` along `f`, read through
the comparison equivalences of Stacks 04M0 at the two charts.

By Stacks 03LQ the chartwise inverse image is restriction along postcomposition with the
represented morphism of charts, and
`AlgebraicGeometry.Space.chartLocalizationPostcompIso` identifies that postcomposition with
`CategoryTheory.Over.map f` through the two comparison functors; both sides are therefore
restriction along one of two isomorphic composites of functors of sites. -/
noncomputable def chartInverseImage_overMapPullbackIso {V U : SmallEtale B S hS X.1}
    (f : V ⟶ U) :
    (chartSliceSheafEquiv B S hS X U).functor ⋙ chartInverseImage B S hS X f ≅
      (SmallEtale.topology B S hS X.1).overMapPullback (Type (u + 1)) f ⋙
        (chartSliceSheafEquiv B S hS X V).functor := by
  have hu := isContinuous_chartLocalization_chartSpace B S hS X U
  have hv := isContinuous_chartLocalization_chartSpace B S hS X V
  have hfg : (SmallEtale.chartLocalization B S hS X.1 V ⋙ Over.map f).IsContinuous
      (SmallEtale.topology B S hS (chartSpace B S hS X V).1)
      ((SmallEtale.topology B S hS X.1).over U) :=
    Functor.isContinuous_comp _ _ _ ((SmallEtale.topology B S hS X.1).over V) _
  have e₀ : (chartSliceSheafEquiv B S hS X U).functor ⋙ chartInverseImage B S hS X f ≅
      (chartSliceSheafEquiv B S hS X U).functor ⋙
        (smallEtalePostcomp B S hS (chartMap B S hS X f)
          (isEtale_chartMap B S hS X f)).sheafPushforwardContinuous (Type (u + 1))
            (SmallEtale.topology B S hS (chartSpace B S hS X V).1)
            (SmallEtale.topology B S hS (chartSpace B S hS X U).1) :=
    Functor.isoWhiskerLeft (chartSliceSheafEquiv B S hS X U).functor
      (smallToposMorphism_inverseImageIso B S hS (chartMap B S hS X f)
        (isEtale_chartMap B S hS X f))
  have e₁ : (chartSliceSheafEquiv B S hS X U).functor ⋙
        (smallEtalePostcomp B S hS (chartMap B S hS X f)
          (isEtale_chartMap B S hS X f)).sheafPushforwardContinuous (Type (u + 1))
            (SmallEtale.topology B S hS (chartSpace B S hS X V).1)
            (SmallEtale.topology B S hS (chartSpace B S hS X U).1) ≅
      (SmallEtale.chartLocalization B S hS X.1 V ⋙
          Over.map f).sheafPushforwardContinuous (Type (u + 1))
        (SmallEtale.topology B S hS (chartSpace B S hS X V).1)
        ((SmallEtale.topology B S hS X.1).over U) :=
    @Functor.sheafPushforwardContinuousComp' _ _ _ _ _ _ _ _ _
      (chartLocalizationPostcompIso B S hS X f) (Type (u + 1)) _
      (SmallEtale.topology B S hS (chartSpace B S hS X V).1)
      (SmallEtale.topology B S hS (chartSpace B S hS X U).1)
      ((SmallEtale.topology B S hS X.1).over U) _ hu hfg
  have e₂ : (SmallEtale.topology B S hS X.1).overMapPullback (Type (u + 1)) f ⋙
        (chartSliceSheafEquiv B S hS X V).functor ≅
      (SmallEtale.chartLocalization B S hS X.1 V ⋙
          Over.map f).sheafPushforwardContinuous (Type (u + 1))
        (SmallEtale.topology B S hS (chartSpace B S hS X V).1)
        ((SmallEtale.topology B S hS X.1).over U) :=
    @Functor.sheafPushforwardContinuousComp' _ _ _ _ _ _ _ _ _
      (Iso.refl (SmallEtale.chartLocalization B S hS X.1 V ⋙ Over.map f)) (Type (u + 1)) _
      (SmallEtale.topology B S hS (chartSpace B S hS X V).1)
      ((SmallEtale.topology B S hS X.1).over V)
      ((SmallEtale.topology B S hS X.1).over U) hv _ hfg
  exact e₀ ≪≫ e₁ ≪≫ e₂.symm

end AlgebraicGeometry.Space

end
