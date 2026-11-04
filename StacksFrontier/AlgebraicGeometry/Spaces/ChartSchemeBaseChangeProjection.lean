module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeBaseChangeStructureMap

/-!
# The chart base-change square read on the cartesian projections

The square of `AlgebraicGeometry.Space.chartSchemeEquivalenceBaseChangeIso` compares two
descriptions of the same object: the base change `W ×_Y X` of an étale chart `W` of the chart
scheme of `V` along `f`, and the fibre product `W ×_{V} U` of `W` with `U = V ×_Y X` over the
chart scheme of `V`.  The comparison is an isomorphism of charts of `X`, and the content of the
square -- the only part that is not bookkeeping -- is that it is compatible with the two
projections to `W`: on the left `AlgebraicGeometry.Space.chartProjectionRepresentable`'s second
projection, on the right the cartesian projection `CategoryTheory.Limits.pullback.fst`.

This file collects the pieces of that comparison, each read on underlying morphisms of the
bounded category of schemes, where the structure map of the square is read:

* the five `rfl`-level identifications that strip the chart-scheme identification
  `AlgebraicGeometry.Space.chartReprEquivalence` and the chart localization
  `AlgebraicGeometry.Space.SmallEtale.chartLocalizationEquivalence` from a morphism, an
  identification that is available because both equivalences are built from
  `CategoryTheory.yonedaCostructuredArrowOverEquiv` and `CategoryTheory.Over.iteratedSliceEquiv`,
  whose unit and counit are `CategoryTheory.Iso.refl` on underlying objects;
* the three compatibilities with the projections, stated at the level of schemes and with
  `CategoryTheory.reassoc` variants, which are the three rewrites the square's component goal
  needs;
* `AlgebraicGeometry.Space.chartSchemeEquivSharp`, the structure comparison of the chart-scheme
  identification, which is the identity and is the pair of identity edges of the square.

## Implementation notes

The three compatibilities are the scheme-level forms of
`AlgebraicGeometry.Space.chartLocalizationBaseChangeObjIso_hom_comp_snd'`,
`AlgebraicGeometry.Space.smallBaseChange_map_snd` and `CategoryTheory.Limits.pullback.lift_fst`.
They are stated here rather than used directly because the first two live in the big fppf
category over `S` and the projection they must meet lives in the bounded category of schemes;
`CategoryTheory.Over.comp_left` is what crosses between the two, and it has to be applied
before the compatibility fires, not after.

## References

* [Stacks Project, Tag 04CF](https://stacks.math.columbia.edu/tag/04CF)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

section Sharp

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (U : AlgebraicSpaces B S hS) (W : (smallEtaleRingedSite B S hS U.1 U.2).C)

/-- **The structure comparison of the chart-scheme identification**: the identity, the two
structure sheaves being equal by
`AlgebraicGeometry.Space.chartSchemeEquivalence_ringSheaf`.

This is the pair of identity edges of the square of
`AlgebraicGeometry.Space.chartSchemeEquivalenceBaseChangeIso`. -/
noncomputable abbrev chartSchemeEquivSharp :
    chartSchemeSiteStructureSheaf B S hS U W ⟶
      (@Functor.sheafPushforwardContinuous (chartSchemeSite B S hS U W) _
        ((smallEtaleRingedSite B S hS U.1 U.2).over W).C _
        (chartSchemeIdentification B S hS U W).functor RingCat.{u} _
        (chartSchemeTopology B S hS U W)
        ((smallEtaleRingedSite B S hS U.1 U.2).over W).J
        (isContinuous_chartSchemeIdentification_functor B S hS U W)).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf ((smallEtaleRingedSite B S hS U.1 U.2).over W).O) :=
  𝟙 _

end Sharp

section Telescope

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {Z : AlgebraicSpaces B S hS} (A : SmallEtale B S hS Z.1)

/-- The chart-scheme identification carries a morphism of étale schemes over the chart scheme to
a morphism of charts with the same underlying morphism of schemes. -/
theorem chartReprEquivalence_inverse_map_left {M M' : chartSchemeSite B S hS Z A} (m : M ⟶ M') :
    ((chartReprEquivalence B S hS A).inverse.map m).hom.left.left = m.hom.left := rfl

/-- The counit of the chart-scheme identification is the identity on underlying schemes. -/
theorem chartReprEquivalence_counit_app_left (M : chartSchemeSite B S hS Z A) :
    ((chartReprEquivalence B S hS A).counit.app M).hom.left = 𝟙 _ := rfl

/-- The inverse counit of the chart-scheme identification is the identity on underlying
schemes. -/
theorem chartReprEquivalence_counitInv_app_left (M : chartSchemeSite B S hS Z A) :
    ((chartReprEquivalence B S hS A).counitInv.app M).hom.left = 𝟙 _ := rfl

/-- The unit of the chart-scheme identification is the identity on underlying schemes. -/
theorem chartReprEquivalence_unit_app_left
    (M : SmallEtale B S hS (yoneda.obj (chartOverObject B S hS Z A))) :
    ((chartReprEquivalence B S hS A).unit.app M).hom.left.left = 𝟙 _ := rfl

/-- The inverse unit of the chart-scheme identification is the identity on underlying
schemes. -/
theorem chartReprEquivalence_unitInv_app_left
    (M : SmallEtale B S hS (yoneda.obj (chartOverObject B S hS Z A))) :
    ((chartReprEquivalence B S hS A).unitInv.app M).hom.left.left = 𝟙 _ := rfl

/-- The chart localization of Stacks 04CF carries a morphism of charts of the chart to a
morphism of charts with the same underlying morphism of the big fppf category over `S`. -/
theorem chartLocalizationEquivalence_functor_map_left
    {M M' : SmallEtale B S hS (yoneda.obj (chartOverObject B S hS Z A))} (m : M ⟶ M') :
    ((SmallEtale.chartLocalizationEquivalence B S hS Z.1 A).functor.map m).left.hom.left =
      m.hom.left := rfl

end Telescope

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
  (hrep : yoneda.relativelyRepresentable f.hom) (V : SmallEtale B S hS Y.1)

attribute [local implicit_reducible] smallEtaleRingedSite smallBaseChange

/-- **The content of the square, at a chart.**  `AlgebraicGeometry.Space.
chartLocalizationBaseChangeObjIso` is compatible with the projections to the chart, read on
underlying morphisms of the bounded category of schemes. -/
@[reassoc]
theorem chartLocalizationBaseChangeObjIso_hom_left_comp_snd
    (A : SmallEtale B S hS (yoneda.obj ((SmallEtale.toOver B S hS Y.1).obj V))) :
    (chartLocalizationBaseChangeObjIso B S hS f hrep V A).hom.left ≫
        ((chartProjectionRepresentable B S hS f hrep V).snd A.1.hom).left =
      (hrep.snd (A.1.hom ≫ V.1.hom)).left := by
  rw [← Over.comp_left, chartLocalizationBaseChangeObjIso_hom_comp_snd']

/-- Base change of charts along `f` is compatible with the projections to the charts of `Y`,
read on underlying morphisms of the bounded category of schemes. -/
@[reassoc]
theorem smallBaseChange_map_left_comp_snd {A A' : SmallEtale B S hS Y.1} (k : A ⟶ A') :
    ((smallBaseChange B S hS f hrep).map k).hom.left.left ≫ (hrep.snd A'.1.hom).left =
      (hrep.snd A.1.hom).left ≫ k.hom.left.left := by
  rw [← Over.comp_left, smallBaseChange_map_snd, Over.comp_left]

/-- Base change of the small étale sites of the two chart schemes is compatible with the
cartesian projections to the charts of the chart scheme of `V`. -/
@[reassoc]
theorem chartSchemeBaseChange_map_left_comp_fst
    {A A' : chartSchemeSite B S hS Y V} (k : A ⟶ A') :
    ((chartSchemeBaseChange B S hS f hrep V).map k).hom.left ≫
        pullback.fst A'.obj.hom (baseChangeChartHom B S hS f hrep V).left =
      pullback.fst A.obj.hom (baseChangeChartHom B S hS f hrep V).left ≫ k.hom.left :=
  pullback.lift_fst _ _ _


/-! ### The remaining step: the ring half of the square

What is still missing for Stacks 0610 in the form that goes through the chart-scheme
identification is the compatibility of the two structure maps of
`AlgebraicGeometry.Space.ChartSchemeBaseChangeStructureMap` around the square of
`AlgebraicGeometry.Space.chartSchemeEquivalenceBaseChangeIso`, i.e. that

```
SheafOfModules.comparisonComp (chartSchemeBaseChangeSharp B S hS f hrep V)
    (chartSchemeEquivSharp B S hS X (baseChangeChart B S hS f hrep V)) ≫
  (Functor.sheafPushforwardContinuousNatTrans
      (chartSchemeEquivalenceBaseChangeIso B S hS f hrep V).hom RingCat …).app
    ((smallEtaleRingedSite B S hS X.1 X.2).over (baseChangeChart B S hS f hrep V)).ringSheaf =
  SheafOfModules.comparisonComp (chartSchemeEquivSharp B S hS Y V)
    (chartLocalizedSharp B S hS f hrep V)
```

with `chartSchemeEquivSharp` the identity (the two structure sheaves of a chart agree by
`AlgebraicGeometry.Space.chartSchemeEquivalence_ringSheaf`) and the bottom edge pinned by
`CategoryTheory.Over.post` of `AlgebraicGeometry.Space.smallBaseChange`.  That statement
elaborates with no instance errors provided every one of `C`, `D`, `E` and its `Category`
instance is given explicitly -- the instances are `((smallEtaleRingedSite …).over W).category`,
never `_`.  Mind the spelling asymmetry: on the `Y` side `(chartSchemeEquivalence … Y V).functor`
synthesises `Category (Over V)` while `(chartSchemeIdentification … Y V).functor` fails for
`V : SmallEtale B S hS Y.1`; on the `X` side, where the chart is `baseChangeChart` and already
carries the `(smallEtaleRingedSite …).C` spelling, `chartSchemeIdentification` is the one that
works.  Every composite and every whiskering has to be written out: inferred grouping makes the
elaborator unify two long functor composites and exhausts the heartbeat budget.

After `ObjectProperty.hom_ext` and `NatTrans.ext` the square reduces to its component, which is
the compatibility of the comparison with the projection to the chart:

```
((chartSchemeEquivalenceBaseChangeIso B S hS f hrep V).hom.app W).left.hom.left.left ≫
    pullback.fst W.obj.hom (baseChangeChartHom B S hS f hrep V).left =
  (hrep.snd (((chartSchemeEquivalence B S hS Y V).functor.obj W).left.obj.hom)).left
```

Unfolding `chartSchemeEquivalenceBaseChangeIso`, `chartSchemeBaseChangeIso` and
`chartSchemeBaseChangeInnerIso` and then the structural simp lemmas for `Iso.trans`,
`CategoryTheory.Functor.isoWhiskerLeft`, `CategoryTheory.Equivalence.invFunIdAssoc`,
`CategoryTheory.Equivalence.funInvIdAssoc` and `CategoryTheory.Functor.associator` drives that
component to a composite of exactly seven factors in the slice
`Over ((smallBaseChange B S hS f hrep).obj V)`, in this order:

1. `Over.post (smallBaseChange f hrep)` of the chart localization of
   `(chartReprEquivalence V).inverse.map ((chartReprEquivalence V).counitInv.app W)`;
2. the same of `(chartReprEquivalence V).unitInv.app ((chartReprEquivalence V).inverse.obj W)`;
3. `(chartLocalizationBaseChangeIso B S hS f hrep V).hom.app` at
   `(chartReprEquivalence V).inverse.obj W`
   -- underlying morphism `chartLocalizationBaseChangeObjIso`, the input of
   `chartLocalizationBaseChangeObjIso_hom_left_comp_snd` above;
4. the chart localization of `(chartReprEquivalence (baseChangeChart …)).unit`;
5. the chart localization of `(chartReprEquivalence (baseChangeChart …)).inverse.map` of
   `(representedSmallEtaleBaseChangeIso … (baseChangeChartHom …)
   (chartProjectionRepresentable …)).hom.app`
   -- underlying morphism `IsPullback.isoIsPullback`, the input of
   `CategoryTheory.IsPullback.isoIsPullback_hom_fst`;
6. `𝟙 _`, from `Functor.associator_hom_app`;
7. the chart localization of `(chartReprEquivalence (baseChangeChart …)).inverse.map` of
   `(chartSchemeBaseChange f hrep V).map ((chartReprEquivalence V).counit.app W)`
   -- underlying morphism `(Over.pullback _).map`, the input of
   `chartSchemeBaseChange_map_left_comp_fst` above.

The mathematics is then the chain: push `pullback.fst` leftwards through factor 7 by
`chartSchemeBaseChange_map_left_comp_fst`, fire `IsPullback.isoIsPullback_hom_fst` at factor 5,
fire `chartLocalizationBaseChangeObjIso_hom_left_comp_snd` at factor 3, and move the resulting
`hrep.snd` out through factors 2 and 1 by `smallBaseChange_map_left_comp_snd`, factors 4 and 6
and the two unit/counit factors telescoping away.  That telescoping is sound and definitional;
the five `rfl` lemmas of the `Telescope` section above are exactly it, and
`CategoryTheory.Category.id_comp` and `CategoryTheory.Category.assoc` are themselves `rfl` both
in `SmallEtale B S hS Y.1` and in `B.Schemes`, so none of the bookkeeping is content.

What blocks the chain is not the mathematics but transparency, and the obstruction is sharper
than it looks:

* The seven-factor composite is a composite in one category, but the projection
  `pullback.fst W.obj.hom (baseChangeChartHom …).left` it must meet is a bare morphism of
  schemes.  The implicit middle object of the outermost `≫` is therefore recorded at the
  spelling the *statement* elaborated it at -- the long chart-localization chain -- while the
  seventh factor's target is recorded at `((chartSchemeBaseChange …).obj W).obj.left`.  The two
  are definitionally equal and syntactically different, so `CategoryTheory.Category.assoc`
  cannot fire at that junction: `rw [Category.assoc]` reports that it did not find the pattern
  and `simp only [Category.assoc]` silently leaves the junction left-associated while
  right-associating everything inside it.  `refine (Category.assoc _ _ _).trans ?_` *does* go
  through, because `refine` unifies at default transparency; but it only reaches the root, and
  each further step of the chain needs the same treatment one level deeper.
* `attribute [local implicit_reducible]` on `smallEtaleRingedSite`, `smallBaseChange` and
  `AlgebraicGeometry.smallEtaleBaseChange` does not repair this (`ObjectProperty.lift` and
  `Over.pullback` already carry it).  The spellings that have to be reconciled run through
  `SmallEtale.chartLocalizationEquivalence` and `representedSmallEtaleEquivalence`, which are
  built by tactic blocks ending in `Equivalence.congrFullSubcategory`; marking those
  `implicit_reducible` as well changes nothing.
* Restating the component with `show`, at a spelling chosen so that the junction matches, times
  out at `whnf`: the defeq check has to unfold `chartSchemeEquivalenceBaseChangeIso` through
  `Equivalence.invFunIdAssoc` and `congrFullSubcategory`, which costs more than the heartbeat
  budget even when the simp unfolding is done first and the association and factor count are
  left untouched.
* Applying the five telescoping `rfl` lemmas first makes matters worse rather than better: once
  they have fired the goal is no longer type-correct at `implicit` transparency -- the unit of
  `chartReprEquivalence (baseChangeChart …)` then sits at type
  `((chartReprBaseChange …).obj A).obj.left ⟶ …` where
  `((SmallEtale.chartLocalizationEquivalence … X.1
  ((smallBaseChange …).obj V)).functor.obj …).left.obj.left` is expected -- and `simp`
  refuses to enter the subterm at all, reporting only `simp made no progress`.
  `with_unfolding_all` in front of `simp only` does not help, since
  the refusal is a type-correctness check and not a unification failure.

So the remaining step wants either the chain written as nested root-level `refine`s with every
intermediate equation stated by hand at the spelling the previous step produced, or -- better --
a reformulation in which the cartesian projection never has to meet a composite whose middle
object is spelled through the chart localization.  Ruled out, with the evidence above: plain
`simp` and `simp only` in any lemma set; `rw` of either content lemma; `show`; and
`implicit_reducible` on any of the definitions named above.

`AlgebraicGeometry.Space.chartSchemeEquivalenceBaseChangeIso` itself is proved, and so is every piece the assembly of Stacks 0610 needs on top of this square:
`AlgebraicGeometry.Space.over_smallBaseChangeModulePushforward_obj` (Stacks 04CF),
`AlgebraicGeometry.Space.isFinitePresentation_chartSchemeModule_iff`,
`AlgebraicGeometry.Space.restrictModulePushforwardIso`,
`AlgebraicGeometry.Space.isFinitePresentation_restrictModule_iff` and
`AlgebraicGeometry.Space.isFinitePresentation_iff_pushforward_isFinitePresentation`
(Stacks 05B4), the last fed by `AlgebraicGeometry.Space.isFinite_baseChangeChartHom`,
`AlgebraicGeometry.Space.finitePresentation_baseChangeChartHom` and
`AlgebraicGeometry.Space.isQuasicoherent_restrictModule`.  The tag of Stacks 0610 is registered
on `isFinitePresentation_iff_smallBaseChangePushforward_of_isQuasicoherentOnSite` in
`StacksFrontier/AlgebraicGeometry/Spaces/ChartSchemeFinitePresentationDescent.lean`.
-/

end AlgebraicGeometry.Space

end
