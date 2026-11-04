module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftChartDifferenceCompatible
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftChartPairDifference
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftChartPairTransport

/-!
# The chart-free difference of two lifts, as a candidate difference family

Let `Z ⊂ X'` be a first-order thickening of algebraic spaces over a scheme `S` contained in a big
fppf site `C`, let `q : Y ⟶ Bb` be a morphism and let `a : Z ⟶ Y` be a morphism over `Bb`.

`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftChartPairDifference` produces the
difference of two lifts over an arbitrary étale chart `U'` of `X'`, with no chart presentation
and no hypothesis beyond the thickening, as a global section of the acting sheaf of the
*restricted* problem; and
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftChartPairTransport` identifies that home
with the sections of `AlgebraicGeometry.Space.liftActionSheafTransport` over `U'`.

Composing the two gives a `AlgebraicGeometry.Space.LiftDifferenceFamily`: the *shape* that
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftChartDifferenceCompatible` asks for,
constructed unconditionally.

## Main definitions

* `AlgebraicGeometry.Space.chartLiftDifferenceFamily`: **the chart-free difference of two lifts,
  as a `AlgebraicGeometry.Space.LiftDifferenceFamily`.**

## What is not done here

**The two properties are not proved.**  A family of the right shape is not yet a difference:
`AlgebraicGeometry.Space.isChartTranslationCompatible_of_liftDifference` consumes a family
together with `AlgebraicGeometry.Space.IsLiftDifferenceOfTranslate` and
`AlgebraicGeometry.Space.IsLiftDifferenceRestrictionNatural`, and neither is established for
this family.  Each is a *value* computation, and what each needs is recorded here so the next
step is not re-derived:

* `AlgebraicGeometry.Space.IsLiftDifferenceOfTranslate` asks for the value of the family at a
  pair of translates of one chart presentation, read through
  `AlgebraicGeometry.Space.ChartLiftPresentation.transportActionSectionEquiv`.  By
  `AlgebraicGeometry.Space.isLiftDifferenceOfTranslate_of_chartSubtraction` it is enough to show
  that value is the subtraction of the two acting sections.

  **Both value lemmas are available.**  The chart half,
  `AlgebraicGeometry.Space.ChartLiftPresentation.actionSectionEquiv`, has
  `AlgebraicGeometry.Space.ChartLiftPresentation.actionSectionEquiv_apply`
  (`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftActionSheafActionSectionValue`); the
  sheaf half, `AlgebraicGeometry.Space.liftPairGlobalSectionOfCompEq` behind
  `AlgebraicGeometry.Space.chartLiftPairGlobalSection`, has
  `AlgebraicGeometry.Space.definingIdealHomOfDerivation_transpose_app_d` and the
  characterisation `AlgebraicGeometry.Space.eq_definingIdealHomOfDerivation_of_transpose_app_d`
  (`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftPairActionSectionValue`), which read the
  *forward* composite off the inverse instead of computing it — `Equiv.apply_symm_apply` followed
  by `AlgebraicGeometry.Space.differentialsHomEquiv_symm_app_d`.

  **What is actually missing is a third statement, about neither bijection**: that the source
  comparison `AlgebraicGeometry.Space.ChartLiftPresentation.chartSourceIso` carries the
  small-étale universal differential `d_{Y/Bb}` to the Zariski universal differential
  `Stacks.Smooth.pullbackD` of the chart square.  The sheaf half's value lemma is stated at the
  local sections of `𝒪_Y` on the small étale site, the chart half's at
  `Stacks.Smooth.pullbackD`, and nothing identifies the two.  That comparison is the composite
  of [Stacks Project, Tag 03LU], [Stacks Project, Tag 04CU], [Stacks Project, Tag 04CS],
  `AlgebraicGeometry.Space.representedAssociatedModulePullbackIso` and
  `AlgebraicGeometry.Scheme.Hom.cotangentSheafIso`.

  **Four of those five factors already have their derivation compatibility**, so the comparison
  is not blocked on new mathematics:
  `AlgebraicGeometry.Space.universalDerivationHom_comp_modulePullbackCompIso_inv_app_comp` for
  03LU; `AlgebraicGeometry.Space.postcomp_representedAssociatedDifferentialsIso` and
  `AlgebraicGeometry.Space.pullbackUnitDerivation_postcomp_representedAssociatedDifferentialsIso`
  for 04CS; `AlgebraicGeometry.Space.representedAssociatedModuleHomEquivLinearMap_pullbackSection`
  for `representedAssociatedModulePullbackIso` — which is the right form, because
  `Stacks.Smooth.pullbackD_eq_pullbackSection` says `Stacks.Smooth.pullbackD` *is* a
  `AlgebraicGeometry.Scheme.Modules.pullbackSection` of the Zariski universal differential, by
  `Eq.refl`; and
  `AlgebraicGeometry.Scheme.Hom.universalRelativeDerivation_postcomp_cotangentSheafIso_hom` with
  its inverse for `cotangentSheafIso`.  The consumer of the last of these is
  `AlgebraicGeometry.Space.representedAssociatedModuleHomEquivLinearMap_map`, the characterising
  equation of the bijection whose `Function.surjInv` the chart half's value lemma deliberately
  does not compute.

  **The fifth factor, 04CU, had no lemma of any kind and now does**:
  `AlgebraicGeometry.Space.universalDerivation_sheafOfDifferentialsEtaleLocalizationIso`
  (`StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsEtaleLocalizationDerivation`), so
  each of the five factors does now carry a derivation compatibility of its own.

  **But their composition is not all that is left, and the count of five is misleading.**  The
  five compatibilities are stated in three mutually incompatible idioms, and between the two ends
  of the chain sits a *sixth* link that none of them supplies.

  The small étale end is settled.  04CU and 04CS do compose, and their composite is formalized as
  `AlgebraicGeometry.Space.universalDerivation_chartSquareDifferentialsAssociatedIso`
  (`StacksFrontier.AlgebraicGeometry.Spaces.ChartSquareDifferentialsDerivation`): the chart-square
  comparison carries `d_{Y/Bb}`, read through
  `AlgebraicGeometry.Space.derivationEtalePullbackEquiv`, to the associated derivation
  `AlgebraicGeometry.Space.transportedAssociatedDerivation`, which is `d^a` of
  [Stacks Project, Tag 04CS].

  The other two factors live at the opposite end, on *Zariski global sections*:
  `AlgebraicGeometry.Space.representedAssociatedModuleHomEquivLinearMap_pullbackSection` speaks
  of `AlgebraicGeometry.Scheme.Modules.pullbackSection` of an element of `Γ(M, ⊤)`, and
  `AlgebraicGeometry.Scheme.Hom.universalRelativeDerivation_postcomp_cotangentSheafIso_hom` of
  `AlgebraicGeometry.Scheme.Hom.universalRelativeDerivation`.  To join the two ends the chain
  needs the element of `Γ(Ω_{W/V}, ⊤)` whose image in the associated module is `d^a` — and **no
  lemma in the repository states the value of
  `AlgebraicGeometry.Space.transportedAssociatedDerivation` in terms of
  `AlgebraicGeometry.Scheme.Hom.universalRelativeDerivation`.**  That is the sixth link, and it is
  the real blocker; it is not obtainable by composing the five.

  Its ingredients all exist, so what it needs is a transport and not new mathematics:
  `AlgebraicGeometry.SmallEtale.postcomp_differentialsIso_inv` down to the étale-site
  `AlgebraicGeometry.SmallEtale.etaleAssociatedDerivation`, then
  `AlgebraicGeometry.SmallEtale.associatedSectionsDerivation_d` and
  `AlgebraicGeometry.etaleAssociatedDerivation_apply` — both `rfl` — to the scheme-level `d^a`,
  and finally `AlgebraicGeometry.pullbackSectionHom_universalRelativeDerivation`, with its
  derivation-level packaging
  `AlgebraicGeometry.SmallEtale.universalRelativeDerivation_postcomp_sectionsUnit`.  That last
  one is the only statement in the repository equating a `d^a` value to a Zariski universal
  differential.  It is stated for `AlgebraicGeometry.SmallEtale.associatedModule` of a *scheme*
  and only at the Zariski-open objects of the small étale site, reached by
  `AlgebraicGeometry.SmallEtale.zariskiRestriction`; so the work owed is its transport across
  `AlgebraicGeometry.Space.representedSmallEtaleModuleEquivalence` to
  `AlgebraicGeometry.Space.representedAssociatedModule`, together with
  `AlgebraicGeometry.SmallEtale.sectionsUnit`.

  Three measurements govern how to write the composition itself.  First, assembling such a
  composite in one declaration exhausts the 200 000-heartbeat **kernel** budget while the
  elaborator succeeds in 50 to 90 seconds; the cost is neither the statement nor the
  delta-reduction of the composite isomorphism — each of those is cheap in isolation — but
  **projecting `.hom` and `.inv` out of isomorphisms built as structure literals**, whose
  `CategoryTheory.Iso.hom_inv_id` and `CategoryTheory.Iso.inv_hom_id` fields are large derivation
  computations that whnf drags in at every projection.  The four isomorphisms of this chain now
  have their equations and projections in
  `StacksFrontier.AlgebraicGeometry.Spaces.ChartSquareDifferentialsChartPullbackEquations`, and
  `AlgebraicGeometry.Space.ChartLiftPresentation.chartSourceIso_eq` carries them to the
  presentation.  Second, naming a projection is not by itself enough: three of those eight
  projections still timed out in the kernel until `CategoryTheory.Iso.trans_hom` and
  `CategoryTheory.Iso.trans_inv` were supplied as explicit *proofs* instead of being left to
  definitional unfolding, which took the file from 4.7 minutes to 2.4 seconds.  So `.symm`,
  `CategoryTheory.eqToIso` and `CategoryTheory.Functor.mapIso` are left unreduced in those
  statements on purpose.  Third, `rw` is unusable on these goals even when its own pattern is
  present: the small étale site index is spelled two definitionally-equal but syntactically
  different ways, so the rewrite motive will not typecheck, while the same chain in term mode
  with `congrArg` checks in a fraction of a second.
* `AlgebraicGeometry.Space.IsLiftDifferenceRestrictionNatural` asks for naturality in the chart,
  which is naturality of `AlgebraicGeometry.Space.liftActionSheafChartSectionsEquiv` in `U'`
  together with naturality of `AlgebraicGeometry.Space.chartLiftPairGlobalSection`.  Neither is
  stated; the five links of the former are each natural, but the restricted lifting *problem*
  changes with the chart, so the naturality square is between two different problems' acting
  sheaves and has to be set up before it can be proved.

Both are genuinely open, and nothing here assumes either: this file constructs the family and
claims nothing about it.

No `@[stacks]` attribute is claimed, and in particular none for [Stacks Project, Tag 04AM] —
item (c) of its chain is not closed until the two properties above are proved, and the
hypothesis it carries stays where it is.

## References

* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
* [Stacks Project, Tag 061C](https://stacks.math.columbia.edu/tag/061C)
* [Stacks Project, Tag 061D](https://stacks.math.columbia.edu/tag/061D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
  {Bb X' Y : AlgebraicSpaces C S hS}

/-- **The chart-free difference of two lifts, as a candidate difference family.**  At an étale
chart `U'` of `X'` the value is the difference of the two lifts over `U'`
(`AlgebraicGeometry.Space.chartLiftPairGlobalSection`), carried to the sections of the
transported acting sheaf over `U'` by
`AlgebraicGeometry.Space.liftActionSheafChartSectionsEquiv`.

The hypothesis that the restricted problem's morphism is `a` precomposed with the projection of
the restricted thickening — which is what the identification needs — is
`AlgebraicGeometry.Space.inclusion_comp_chartLiftHom`, the second clause of
`AlgebraicGeometry.Space.IsChartLift` for the second lift.

Nothing is assumed beyond `Z ⊂ X'` being a first-order thickening: no chart presentation, no
affine chart square of `q`, no étale hypothesis on the charts of `q`.  **This is the shape
only**; see "What is not done here" in the module documentation for the two properties that are
still owed. -/
def chartLiftDifferenceFamily (p : X' ⟶ Bb) (q : Y ⟶ Bb) (Z : ClosedSubspaces C S hS X'.1)
    (hG : IsThickening C S hS X' Z.1) (hX : IsFirstOrderThickening C S hS X' Z.1)
    (aZ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS) ⟶ Y) :
    LiftDifferenceFamily C S hS p Z hG q aZ :=
  fun U' β γ =>
    liftActionSheafChartSectionsEquiv C S hS Z hG q aZ U'
      (IsThickening.inclusion C S hS
          (isThickening_preimage C S hS Z.1 (chartToSpace C S hS X' U') hG) ≫
        chartLiftHom C S hS p q aZ.hom U' γ)
      (ObjectProperty.hom_ext _
        (inclusion_comp_chartLiftHom C S hS p q aZ.hom hG U' γ))
      (chartLiftPairGlobalSection C S hS p q aZ.hom hG hX U' β γ)

end AlgebraicGeometry.Space

end
