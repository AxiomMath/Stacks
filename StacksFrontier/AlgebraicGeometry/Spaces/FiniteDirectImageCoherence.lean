module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Noetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHigherPushforwardVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentPushforwardReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts

/-!
# The direct images of a coherent module along a finite morphism of algebraic spaces

Let `f : X ⟶ Y` be a finite morphism of algebraic spaces over a scheme `S` with `Y` locally
Noetherian, and let `F` be a coherent `𝒪_X`-module.  Stacks 07UH asserts that `R^p f_*F = 0`
for `p > 0` and that `f_*F` is coherent.  Both assertions are proved here, each from one named
hypothesis holding the case of an étale chart of `Y`, which is the step the source's proof
delegates to the case of schemes (Cohomology of Schemes, Lemma 01Y6) across Stacks 03DW.

The coherence criterion that the direct image is measured against is proved here without any
hypothesis: on a locally Noetherian algebraic space a module is coherent exactly when it is
quasi-coherent and of finite type, which is Stacks 07UB (1) ⇔ (2).

## Main results

* `AlgebraicGeometry.Space.isCoherent_iff_isQuasicoherentOnSite_and_isFiniteType`: **Stacks
  07UB, conditions (1) and (2)** — a module on a locally Noetherian algebraic space is coherent
  if and only if it is quasi-coherent and of finite type.
* `AlgebraicGeometry.Space.isLocallyNoetherian_chart` and
  `AlgebraicGeometry.Space.hasEtaleLocalProperty_isLocallyNoetherian_chart`: **Stacks 03E8 at
  local Noetherianity** — every étale chart of a locally Noetherian algebraic space is locally
  Noetherian, as a scheme and as an algebraic space.
* `AlgebraicGeometry.Space.isZero_rightDerived_modulePushforward_of_isFinite`: **the vanishing
  assertion of Stacks 07UH** — the higher direct images of a module along a finite morphism
  vanish, granted the chart case `h03DW`.
* `AlgebraicGeometry.Space.isCoherent_modulePushforward_of_isFinite`: **the coherence assertion
  of Stacks 07UH** — the direct image of a coherent module along a finite morphism onto a
  locally Noetherian algebraic space is coherent, granted the chart case `hchart` at one étale
  chart of `Y` surjective on points, which the caller chooses.

## Implementation notes

**The coherence criterion is unconditional.**  `AlgebraicGeometry.Space.CoherentNoetherian`
proves Stacks 07UB (1) ⇔ (2) over the hypothesis
`AlgebraicGeometry.Space.IsCartesianOnAffineCharts`, which is Descent, Proposition 03DX (2) for
the charts of the space, and records that the tree does not have it.  It does:
`AlgebraicGeometry.Space.isCartesianOnAffineCharts_of_isQuasicoherentOnSite` carries
`@[stacks 03DX "quasi-coherent implies cartesian"]`, and in the reverse direction of the
criterion quasi-coherence is a hypothesis, so the base change property is free there.  The
module universe is the universe `u` of the structure rings, which is where that input lives.

**The chart of the coherence assertion is the caller's.**  Local Noetherianity of an *arbitrary*
étale chart is Stacks 03E8, which needs the étale locality of the property; that is
`AlgebraicGeometry.isLocallyNoetherian_isLocal_etale`, so the chart over which coherence is
tested need not be the atlas that the hypothesis on `Y` supplies and may in particular be taken
affine, which is what discharging the chart case would want.

**What the two chart hypotheses are, and why they are the same mathematics.**  For the
vanishing assertion the hypothesis is
`AlgebraicGeometry.Space.ChartwiseIsZeroHigherDirectImage`: the higher direct images of the
chart base changes of `f` vanish.  For the coherence assertion it is `hchart`: coherence of the
localized direct image of Stacks 04CF at one étale chart of `Y` surjective on points.  Both are
the étale-site form of Stacks 01Y6, whose Zariski form is proved — the vanishing half as
`Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.isZero_higherDirectImage_of_isFinite` and
the coherence half as
`Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.isCoherent_pushforward_of_isFinite` — for
`AlgebraicGeometry.Scheme.Modules`, that is on the Zariski site.  Passing to the small étale
site is Stacks 03DW, which is carried nowhere in this development, and the comparison of
`AlgebraicGeometry.Scheme.Modules` with `AlgebraicGeometry.Space.Modules` of a represented
algebraic space that would transport it does not exist either.  So one tag, 03DW, is what both
hypotheses are owed from, and each attribute below names it.

**Neither assertion needs all of the source's hypotheses.**  The vanishing reduction uses
finiteness of `f` only through affineness, and uses neither local Noetherianity of `Y`, nor
coherence of `F`, nor `p > 0`; the degree runs over `ℕ` in the injective-resolution convention
of `CategoryTheory.Functor.rightDerived`, as in Stacks 071Z.  The coherence reduction consumes
no property of `F` at all.  Both statements are therefore more general than the clause they
carry, and the source's clause is the special case.

**The two local priority raises** are the ones
`StacksFrontier/AlgebraicGeometry/Spaces/AffineHigherPushforwardVanishing.lean` documents: with the
module-universe-`max u v r w` instances of
`StacksFrontier/CategoryTheory/Sites/Cohomology/Modules/CohomologyOfModules.lean` in the import
closure, search for `Abelian` and `EnoughInjectives` on the modules at module universe `u`
commits to them and then fails on the universe constraint.

## References

* [Stacks Project, Tag 07UH](https://stacks.math.columbia.edu/tag/07UH)
* [Stacks Project, Tag 07UB](https://stacks.math.columbia.edu/tag/07UB)
* [Stacks Project, Tag 01Y6](https://stacks.math.columbia.edu/tag/01Y6)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 073H](https://stacks.math.columbia.edu/tag/073H)
* [Stacks Project, Tag 04CF](https://stacks.math.columbia.edu/tag/04CF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 5000] CategoryTheory.IsGrothendieckAbelian.enoughInjectives

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The coherence criterion on a locally Noetherian algebraic space -/

variable (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- **Stacks 07UB, conditions (1) and (2).**  A module on a locally Noetherian algebraic space
is coherent if and only if it is quasi-coherent and of finite type.

The base change property of the sections over the affine charts, which the conditional form in
`StacksFrontier.AlgebraicGeometry.Spaces.CoherentNoetherian` carries, is Descent, Proposition
03DX (2) and follows from quasi-coherence, which is a hypothesis in the direction that needs
it. -/
@[stacks 07UB "conditions (1) and (2)"]
theorem isCoherent_iff_isQuasicoherentOnSite_and_isFiniteType
    [Fact (HasEtaleLocalProperty B S hS F (fun V : Scheme.{u} => IsLocallyNoetherian V))]
    (M : Modules.{u, u} B S hS F hF) :
    IsCoherent B S hS F hF M ↔
      (M.IsQuasicoherentOnSite ∧
        PresheafOfModules.IsFiniteType (smallEtaleRingedSite B S hS F hF).J M.val) := by
  refine ⟨fun h => ⟨h.toIsQuasicoherentOnSite, h.toIsCoherentOnSite.isFiniteType⟩, fun h => ?_⟩
  exact (isCoherent_iff_isQuasicoherent_and_isFiniteType_of_isCartesian_of_isLocallyNoetherian
    B S hS F hF M
    (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS F hF M h.1)).2 h

/-! ### The higher direct images along a finite morphism -/

variable {X Y : AlgebraicSpaces B S hS}

/-- **The vanishing assertion of Stacks 07UH, granted the chart case `h03DW`.**  Let
`f : X ⟶ Y` be a finite morphism of algebraic spaces over `S` whose chart base changes have
vanishing degree-`n` higher direct images.  Then `R^n f_*𝓕 = 0`.

A finite morphism is affine, `AlgebraicGeometry.Space.IsFinite.isAffineHom`, so this is
`AlgebraicGeometry.Space.isZero_rightDerived_modulePushforward_of_isAffineHom`, the reduction of
Stacks 073H through Equation 69.3.0.1 of Stacks 071Z.  The source's hypotheses that `Y` be
locally Noetherian, that `𝓕` be coherent and that `n > 0` are not used; `h03DW` is the
étale-site form of Stacks 01Y6, that is Stacks 03DW, which this development does not carry. -/
@[stacks 07UH "vanishing of the higher direct images, granted the étale-affine case h03DW \
of Stacks 03DW"]
theorem isZero_rightDerived_modulePushforward_of_isFinite (f : X ⟶ Y)
    (hf : IsFinite B S hS f.hom) (G : Modules.{u, u} B S hS X.obj X.property) (n : ℕ)
    (h03DW : ChartwiseIsZeroHigherDirectImage B S hS f
      (relativelyRepresentable_of_isAffineHom B S hS f hf.isAffineHom)
      G n) :
    have := hasInjectiveResolutions_modules B S hS X.obj X.property
    IsZero (((modulePushforward B S hS f).rightDerived n).obj G) :=
  isZero_rightDerived_modulePushforward_of_isAffineHom B S hS f
    hf.isAffineHom G n h03DW

/-! ### Local Noetherianity of an arbitrary étale chart -/

/-- **Stacks 03E8 at local Noetherianity.**  Every étale chart of a locally Noetherian
algebraic space has locally Noetherian underlying scheme.

Local Noetherianity is étale-local by `AlgebraicGeometry.isLocallyNoetherian_isLocal_etale`, so
`AlgebraicGeometry.Space.exists_atlas_iff_forall_etale` upgrades the atlas condition of
Stacks 03E6 to a statement about every étale chart. -/
theorem isLocallyNoetherian_chart
    (hY : HasEtaleLocalProperty B S hS Y.1 (fun T : Scheme.{u} ↦ IsLocallyNoetherian T))
    (V : SmallEtale B S hS Y.1) :
    IsLocallyNoetherian
      ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj V)) :=
  (exists_atlas_iff_forall_etale B S hS Y.1 (fun T : Scheme.{u} ↦ IsLocallyNoetherian T)
    Y.2).1 hY V.1.left V.1.hom V.2

/-- The algebraic space of an étale chart of a locally Noetherian algebraic space is locally
Noetherian.  This is `AlgebraicGeometry.Space.isLocallyNoetherian_chart` read through
`AlgebraicGeometry.Space.hasEtaleLocalProperty_chart`. -/
theorem hasEtaleLocalProperty_isLocallyNoetherian_chart
    (hY : HasEtaleLocalProperty B S hS Y.1 (fun T : Scheme.{u} ↦ IsLocallyNoetherian T))
    (V : SmallEtale B S hS Y.1) :
    HasEtaleLocalProperty B S hS
      ((SpacesEtale.toSpaces B S hS Y).obj ((comparisonFunctor B S hS Y).obj V)).1
      (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) :=
  hasEtaleLocalProperty_chart B S hS _ V (isLocallyNoetherian_chart B S hS hY V)

/-! ### The coherence of the direct image along a finite morphism -/

/-- **The coherence assertion of Stacks 07UH, granted the chart case `hchart`.**  Let
`f : X ⟶ Y` be a finite morphism of algebraic spaces over `S` with `Y` locally Noetherian, let
`𝓕` be a coherent `𝒪_X`-module, and let `V` be an étale scheme chart of `Y` surjective on
points.  Then `f_*𝓕` is coherent.

Coherence is tested on `V` by Stacks 07UB (1) and (5) and over `V` the direct image is the
localized direct image of Stacks 04CF, by
`AlgebraicGeometry.Space.isCoherentOnSite_modulePushforward_of_over_of_isSurjective`.  The two
geometric premises of `hchart` are discharged: the base change of `f` along `V` is finite by
Stacks 03ZS, and `V` is locally Noetherian by Stacks 03E8.  So `hchart` is the étale-site form
of Stacks 01Y6, that is Stacks 03DW, which this development does not carry.

Unlike `AlgebraicGeometry.Space.isCoherent_modulePushforward_of_isFinite_of_chartCase` the chart
is the caller's, not the atlas that `hY` supplies, which is what lets `hchart` be met at an
*affine* chart; that is possible here because local Noetherianity of an arbitrary chart is
available, by `AlgebraicGeometry.Space.isLocallyNoetherian_chart`. -/
@[stacks 07UH "coherence of the direct image, granted the chart case hchart of Stacks 03DW"]
theorem isCoherent_modulePushforward_of_isFinite (f : X ⟶ Y) (hf : IsFinite B S hS f.hom)
    (hY : HasEtaleLocalProperty B S hS Y.1 (fun T : Scheme.{u} ↦ IsLocallyNoetherian T))
    (G : Modules.{u, u} B S hS X.1 X.2) (hG : IsCoherent B S hS X.1 X.2 G)
    (V : SmallEtale B S hS Y.1) (hsurj : IsSurjective B S hS V.1.hom)
    (hchart : IsFinite B S hS (chartBaseChangeProjection B S hS f V).hom →
      HasEtaleLocalProperty B S hS
        ((SpacesEtale.toSpaces B S hS Y).obj ((comparisonFunctor B S hS Y).obj V)).1
        (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) →
      IsCoherent B S hS X.1 X.2 G →
      ((chartLocalizedModulePushforward B S hS f V).obj
        ((moduleChartBaseChangeRestriction B S hS f V).obj G)).IsCoherentOnSite) :
    IsCoherent B S hS Y.1 Y.2 ((modulePushforward B S hS f).obj G) := by
  have : ((modulePushforward B S hS f).obj G).IsCoherentOnSite :=
    isCoherentOnSite_modulePushforward_of_over_of_isSurjective B S hS f G V hsurj
      (hchart (isFinite_chartBaseChangeProjection B S hS f V hf)
        (hasEtaleLocalProperty_isLocallyNoetherian_chart B S hS hY V) hG)
  exact isCoherent_of_isCoherentOnSite B S hS Y.1 Y.2 _

end AlgebraicGeometry.Space

end
