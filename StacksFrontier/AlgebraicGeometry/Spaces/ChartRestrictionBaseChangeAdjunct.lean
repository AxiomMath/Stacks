module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionPushforwardComparison

/-!
# The adjunct of the chart base-change isomorphism, reduced to two factors

`AlgebraicGeometry.Space.restrictToChartBaseChangeIso` is the base change of the chart
restriction of a quasi-coherent module along a square of étale scheme charts: an isomorphism
`g^*(G|_V) ≅ (a^*G)|_W` of sheaves of modules on the chart scheme of `W`.  Its adjunct along the
Zariski pullback–pushforward adjunction is a morphism of sheaves of modules
`G|_V ⟶ g_*((a^*G)|_W)`, and the morphism it ought to be compared with is
`AlgebraicGeometry.Space.restrictToChartPushforwardHom` of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartRestrictionPushforwardComparison.lean`, which was
built for that comparison and has a value-on-sections description.

**This file does not make that comparison.  It reduces the adjunct to two factors and says which
one of them is the obstruction.**  The isomorphism is a five-fold composite; the adjunct of a
composite whose first factor is an image of the pullback functor costs nothing on that factor, by
naturality of the unit, and costs nothing on any factor after the first either, those being
pushed into the direct image.  What is left is one factor whose adjunct is not formal.

## Main definitions

* `AlgebraicGeometry.Space.restrictToChartBaseChangeEtaleTail` is the composite of the last three
  factors of `AlgebraicGeometry.Space.restrictToChartBaseChangeIso`: the chart restriction's own
  base-change comparison `AlgebraicGeometry.Space.chartSmallEtaleRestrictionBaseChangeIso`,
  followed by the two readings of the chart restriction run backwards.
* `AlgebraicGeometry.Space.restrictToChartBaseChangeTail` is that preceded by the inverse of the
  represented base-change isomorphism
  `AlgebraicGeometry.Space.restrictToChartSchemeBaseChangeIso`, that is, the whole composite
  after its one pullback-image factor.

## Main results

* `AlgebraicGeometry.Space.restrictToChartBaseChangeIso_eq`: the isomorphism is the image under
  the Zariski pullback of the two readings of the chart restriction, followed by
  `AlgebraicGeometry.Space.restrictToChartBaseChangeTail`.  This is its definition, regrouped.
* `AlgebraicGeometry.Space.homEquiv_restrictToChartBaseChangeIso_hom`: **the reduction.**  The
  adjunct of `AlgebraicGeometry.Space.restrictToChartBaseChangeIso` is

  the two readings of the chart restriction, then the adjunct of the *inverse of the represented*
  base-change isomorphism `AlgebraicGeometry.Space.restrictToChartSchemeBaseChangeIso`, then the
  direct image of `AlgebraicGeometry.Space.restrictToChartBaseChangeEtaleTail`.

  So of the five factors, four cost nothing: the first is discharged by
  `CategoryTheory.Adjunction.homEquiv_naturality_left`, the last three by
  `CategoryTheory.Adjunction.homEquiv_naturality_right`.

## Implementation notes

### Where the comparison still stops

Two things remain in the reduced form, and they are of different kinds.

*The adjunct of the represented base-change isomorphism.*  This is the half that is formal.
`AlgebraicGeometry.Space.restrictToChartSchemeBaseChangeIso` is taken `.symm` inside the
composite, so what occurs is its **inverse**, and in that inverse both adjunction maps appear
forward — the unit `AlgebraicGeometry.SmallEtale.unitIsoOnQuasicoherent` and the counit
`AlgebraicGeometry.SmallEtale.isIso_counit` — as the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartRestrictionBaseChange.lean` record.  Its two
pullback-image factors peel the same way as the one peeled here, and the associated-module unit
it passes through is absorbed by `CategoryTheory.Adjunction.comp_unit_app` into the unit of the
composite adjunction, exactly as
`AlgebraicGeometry.SmallEtale.zariskiRouteAdjunction` of
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleMorphismBaseChange.lean` is
built; `AlgebraicGeometry.Space.representedAssociatedModulePullbackIso`, the one comparison of
left adjoints inside it, has its adjunct square outright in
`AlgebraicGeometry.Space.unit_comp_representedModulePullbackIso_inv` and
`AlgebraicGeometry.SmallEtale.unit_comp_associatedModuleObjBaseChangeIso`.  **It is carried
out**, in
`StacksFrontier/AlgebraicGeometry/Spaces/ChartSchemeRestrictionBaseChangeAdjunct.lean`: the factors
of that isomorphism are the named declarations
`AlgebraicGeometry.Space.associatedModuleRestrictModuleIsoSelf`,
`AlgebraicGeometry.Space.restrictModuleAssociatedModuleIsoSelf` and
`AlgebraicGeometry.Space.restrictToChartSchemeBaseChangeIsoHead`, and the adjunct of the inverse
is `AlgebraicGeometry.Space.homEquiv_restrictToChartSchemeBaseChangeIso_inv`.  Peeling needs
that construction's components named, and naming them is the
whole of the work; the peel itself is one
`CategoryTheory.Adjunction.homEquiv_naturality_left`.

*The direct image of the étale tail — this is the obstruction.*  The adjunct has to be compared
with `AlgebraicGeometry.Space.restrictToChartPushforwardHom`, whose components are the chart
components `AlgebraicGeometry.Space.modulePullbackChartSection` of the unit of the Stacks 03D7
adjunction **at `a`**.  Nothing in the represented half knows about `a`: it is a statement about
the represented morphism `AlgebraicGeometry.Space.representedSpaceMap` of `g` alone.  The passage
from the represented morphism to `a` happens in exactly one place, the factor
`AlgebraicGeometry.Space.chartSmallEtaleRestrictionBaseChangeIso` inside
`AlgebraicGeometry.Space.restrictToChartBaseChangeEtaleTail`, which is
`AlgebraicGeometry.Space.chartModuleRestrictionBaseChangeIso` — that is
`AlgebraicGeometry.Space.modulePullbackCommSquareIso`, two instances of the composition
comparison `AlgebraicGeometry.Space.modulePullbackCompIso` of Stacks 03LU.  So the comparison
needs the value of that comparison on the chart component of the unit of Stacks 03D7.

Its *adjunct square* is not what is missing: that is
`AlgebraicGeometry.Space.unit_comp_whiskerRight_modulePullbackCompIso_hom` in
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePullbackComp.lean`, together with
`AlgebraicGeometry.Space.modulePullbackCompIso_hom_comp_counit`, and those two characterize the
comparison.  What the passage from that square to a *chart* component asks for is the comparison
`AlgebraicGeometry.Space.modulePushforwardCompIso` of the direct images on underlying sheaves of
sets, and **that is proved**, as
`AlgebraicGeometry.Space.moduleSheafFunctor_map_modulePushforwardCompIso_hom_app` in
`StacksFrontier/AlgebraicGeometry/Spaces/ModulePushforwardCompIsoSheafTransfer.lean`, by reading
the comparison on a single local section.  So is the chart component itself:

* `AlgebraicGeometry.Space.modulePullbackCompIso_hom_val_app_modulePullbackUnitSection` in
  `StacksFrontier/AlgebraicGeometry/Spaces/ModulePullbackCompIsoChartSection.lean` is Stacks 03LU
  carrying a chart section of a chart section to the chart section of the composite, with no
  étaleness on either factor, which is the **mixed** instance this reduction needs and the one
  the both-étale `AlgebraicGeometry.Space.modulePullbackCompIsoEtaleRestriction` does not give.

That statement is **not** proved by assembling the four `eqToHom`-laden factors in
`SmallEtaleModulePullbackComp.lean`: that assembly diverges, over six spellings.  It is proved
by never composing in the category of sheaves of
modules — on a section the two sides are two elements of one type, the `eqToHom` is crossed once
by a lemma stated at variable functors, and `CategoryTheory.Sheaf.hom_ext_sections` reassembles
the equation of sheaf morphisms.  No refactor of
`AlgebraicGeometry.Space.pushforwardModules_eq_modulePushforward` — 142 references across 25
files — is needed for it, and the component-wise natural isomorphism such a refactor would
produce exists already, beside the equality rather than in place of it, as
`AlgebraicGeometry.Space.pushforwardModulesIsoModulePushforward`.

**The other half the reduction below names** is the adjunct of the
*represented* base-change isomorphism
`AlgebraicGeometry.Space.restrictToChartSchemeBaseChangeIso`.  That half is formal, as described
above, and **it is carried out**, in
`StacksFrontier/AlgebraicGeometry/Spaces/ChartSchemeRestrictionBaseChangeAdjunct.lean`, which also
substitutes it into the reduction below:
`AlgebraicGeometry.Space.homEquiv_restrictToChartBaseChangeIso_hom_peeled` is the adjunct of
`AlgebraicGeometry.Space.restrictToChartBaseChangeIso` with every factor discharged except the
direct image of `AlgebraicGeometry.Space.restrictToChartBaseChangeEtaleTail`.  So the chart
comparison of Stacks 07SI is short of exactly one thing, and it is the mixed instance of the
compatibility recorded below — not two.

### The tail's value description: one factor supplied, and the next obstruction

The tail's factors have almost no value description — searching by name and by statement
shape for
`AlgebraicGeometry.Space.chartSmallEtaleRestrictionBaseChangeIso`,
`AlgebraicGeometry.Space.restrictToChartSchemeIsoIdEtaleChart`,
`AlgebraicGeometry.Space.restrictToChartIsoRestrictToChartScheme`,
`AlgebraicGeometry.Space.chartModuleRestrictionIsoChartSmallEtaleRestriction` and
`AlgebraicGeometry.Space.restrictToChartSchemeIdEtaleChartIso`: **only the fourth has one.**
In the namespace `AlgebraicGeometry.Space`,
`chartModuleRestrictionIsoChartSmallEtaleRestriction_hom_val_app_modulePullbackUnitSection`
in `StacksFrontier/AlgebraicGeometry/Spaces/ChartModuleRestrictionChartSection.lean` reads that
factor on a chart section, in one application of
`AlgebraicGeometry.Space.modulePushforwardCounitApp_map`.

*Why that one was cheap, and what that says about the others.*  The factor is
`AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback` at one object, and that general
construction **already** has its value pinned on a section, by
`AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback_unit_app` and by
`AlgebraicGeometry.Space.etaleModulePullbackAdjunction_unit_app`, which holds by `Eq.refl`.  So
"no factor has a value lemma" and "no factor's value is *available*" are different claims, and
only the first is true of the remaining four.  The same question is worth asking of them before
writing anything for them: of their own building blocks,
`Stacks.PresheafOfModules.pushforwardIsoOfIndexIso`, `SheafOfModules.pushforwardCongr₂` and
`SheafOfModules.pushforwardComp` all have value lemmas
(`pushforwardIsoOfIndexIso_hom_app_app_apply`, `pushforwardCongr₂_hom_app_val_app`,
`pushforwardComp_hom_app_val_app`, the last being Mathlib's and the iso being `Iso.refl`), and
`PresheafOfModules.sheafification` has one only in unit-mediated form, which is what the value
lemmas of `AlgebraicGeometry.Space.restrictToChartIsoRestrictToChartScheme` and
`AlgebraicGeometry.Space.restrictToChartSchemeIdEtaleChartIso` will have to be stated on.

*The next obstruction is the assembly, not a missing lemma.*  The
factor that carries the passage from the represented morphism to `a` is
`AlgebraicGeometry.Space.chartSmallEtaleRestrictionBaseChangeIso`, whose middle is
`AlgebraicGeometry.Space.chartModuleRestrictionBaseChangeIso`, that is
`AlgebraicGeometry.Space.modulePullbackCommSquareIso` — the composite of
`modulePullbackCompIso γ cZ`, `eqToIso (congrArg modulePullback hsq)` and
`(modulePullbackCompIso cX a).symm`.
Its value on an iterated chart section needs exactly three reductions, and **each one compiles**:

* the mixed instance of Stacks 03LU on a chart section, which is
  `AlgebraicGeometry.Space.modulePullbackCompIso_hom_val_app_modulePullbackUnitSection` and is
  already in the library;
* its inverse form, which follows from it by `CategoryTheory.Iso.hom_inv_id_app` read on the
  section;
* the crossing of the middle `eqToIso`, which goes through by `subst` on the square and then
  `rfl` **provided the two morphisms it compares are free variables** — stated at
  `{k₁ k₂ : Y ⟶ W} (h : k₁ = k₂)` with the chart diagram bundled, it is three lines.

What does not go through is their *composition*.  Regrouping at the iso level is free, as
elsewhere in this file (`CategoryTheory.Iso.trans_hom` and `CategoryTheory.NatTrans.comp_app`
cost nothing), and peeling the resulting threefold composite off the section is free too through
a lemma whose every object is a variable.  But joining the first reduction to the next — by
`congrArg` over the remaining two factors, with the binder's type ascribed to
`((modulePullback (γ ≫ cZ)).obj G).val.obj (op U)` — exhausts the heartbeat limit, and the
variant that states the whole chain as one `show` between written-out sides elaborates and then
**exceeds the kernel's budget**.  Both failures have the same cause as the one recorded below for
`≫` at the iso level: the middle object of the composite is an inverse image of modules, so
`whnf` on it descends into a sheafification left adjoint.  `rw` with fully-applied lemmas, which
is what works elsewhere here, does not apply: the printed pattern and the printed target are
character-for-character identical and still do not match, the two `≫`s reaching the category of
sheaves of modules by different instance paths, so only `isDefEq` can join them and that is the
operation which is too expensive.

So the remaining obstruction at this factor is *not* the mixed compatibility — that is proved —
and not any of the three reductions above.  It is that a chain of three reductions through an
inverse image of modules cannot presently be joined inside one declaration.  The natural route
is the one that works for the represented half: give each joint its own
declaration with the data a free variable, so that no single kernel check sees two of the three
at once.

**The records this joins are three.**
The "What is not proved" section of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartBaseChangeEtaleSquareComparison.lean` names the
compatibility in exactly these words — "the compatibility of the comparisons of Stacks 03LU and
03LW with the chart component of the unit of Stacks 03D7" — and carries the
split that matters: the compatibility has a *both-factors-étale* instance and a *mixed* instance,
and only the mixed one is missing.  The both-étale instance,
`AlgebraicGeometry.Space.QuasiCoherentDescent.ModulePullbackCompIsoEtaleRestriction`, is **proved
unconditionally** as `AlgebraicGeometry.Space.modulePullbackCompIsoEtaleRestriction`; the
hypothesis survives on the declaration
`fullyFaithfulEtaleCanonicalDescentFunctorOfIsZariskiCovering` of the namespace
`AlgebraicGeometry.Space.QuasiCoherentDescent` only because that module does not import the
proof, and its one consumer discharges it.  What remains recorded as missing is the mixed
instance, in `StacksFrontier/AlgebraicGeometry/Spaces/ConormalAlgebraEtaleRestriction.lean` and
`StacksFrontier/AlgebraicGeometry/Spaces/ModuleChartCorrespondenceComp.lean`.

The reduction below is the measurement that puts the chart comparison of Stacks 07SI on that
same list rather than on a list of its own: it is not blocked by the seventeen isomorphisms of
`AlgebraicGeometry.Space.restrictToChartBaseChangeIso`, nor by anything inverted on the route it
takes, but by that one compatibility.  And the instance it needs is the **mixed** one: the two
instances of `AlgebraicGeometry.Space.modulePullbackCompIso` inside
`AlgebraicGeometry.Space.chartModuleRestrictionBaseChangeIso` are taken at
`(AlgebraicGeometry.Space.chartSpaceMapOver g, AlgebraicGeometry.Space.chartToSpace Z V)` and at
`(AlgebraicGeometry.Space.chartToSpace X W, a)`, and in neither pair are both factors étale.  The
structure morphism of a chart is, by
`AlgebraicGeometry.Space.isEtale_chartToSpace`; `a` is arbitrary by hypothesis, and for
`AlgebraicGeometry.Space.chartSpaceMapOver` of a morphism of charts over an arbitrary `a` the
development has no étaleness lemma and none is expected, the two charts of a square being chosen
independently.  So the proved both-étale instance discharges neither factor.

What the same file supplies and what it does not is worth keeping in view.
`AlgebraicGeometry.Space.modulePullbackEtaleSquareComparison` *is* a base-change comparison of
exactly this shape which carries the chart component of the unit at one morphism to the chart
component at another, by construction
(`AlgebraicGeometry.Space.modulePullbackEtaleSquareComparison_chartSection`); what is missing is
only that it agrees with the comparison built from Stacks 03LU, which is the same identification
read the other way round.

### Elaboration

*The isomorphism is regrouped at the level of isomorphisms, never of morphisms.*  Stating the
composite with `≫` instead of `≪≫` — writing out even one factor as
`(Scheme.Modules.pullback _).map _ ≫ _` — exhausts the recursion depth, because the middle object
has to be unified at two spellings, `AlgebraicGeometry.Space.etaleChartScheme` of the chart and
`AlgebraicGeometry.BigFppfOver.toScheme` of its underlying object, and the categories of modules
over them are then compared.  With `≪≫` the regrouping is `rfl` and costs nothing, and the
morphism-level form is reached only inside a goal that is already elaborated.

*The adjunct is written with `CategoryTheory.Adjunction.homEquiv` and not as
`unit ≫ pushforward.map`.*  The two are equal by `CategoryTheory.Adjunction.homEquiv_unit`, but
the two naturality lemmas the reduction is are stated for `homEquiv`, and applying them to the
unit form needs a rewrite inside the direct image, which is where the recursion depth goes.

Nothing here raises a compiler limit or disables a linter.

## References

* [Stacks Project, Tag 03M0](https://stacks.math.columbia.edu/tag/03M0)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 07SI](https://stacks.math.columbia.edu/tag/07SI)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Z : AlgebraicSpaces B S hS} (a : X ⟶ Z)
    (V : SmallEtale B S hS Z.1) (W : SmallEtale B S hS X.1)
    (g : (SmallEtale.toOver B S hS X.1).obj W ⟶ (SmallEtale.toOver B S hS Z.1).obj V)
    (hg : yoneda.map g ≫ V.obj.hom = W.obj.hom ≫ a.hom)
    (G : Modules.{u, u} B S hS Z.1 Z.2) (hG : G.IsQuasicoherentOnSite)

/-! ### The composite after the pullback-image factor -/

/-- **The last three factors of `AlgebraicGeometry.Space.restrictToChartBaseChangeIso`**: the
base-change comparison `AlgebraicGeometry.Space.chartSmallEtaleRestrictionBaseChangeIso` of the
small étale reading of the chart restriction, read on the scheme of the identity chart, followed
by the two readings of the chart restriction run backwards.

This is the factor which carries the passage from the represented morphism of `g` to `a`, and so
the one whose action on the chart component of the unit of Stacks 03D7 the comparison of
`AlgebraicGeometry.Space.restrictToChartPushforwardHom` with the adjunct still needs; see this
file's implementation notes. -/
def restrictToChartBaseChangeEtaleTail :
    (restrictToChartSchemeFunctor B S hS (yoneda.obj (chartFppfObject B S hS X W))
          (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS (chartFppfObject B S hS X W))
          (idEtaleChart B S hS (chartFppfObject B S hS X W))).obj
        ((modulePullback B S hS (representedSpaceMap B S hS g)).obj
          (chartSmallEtaleRestriction B S hS Z G V)) ≅
      restrictToChart B S hS X.2 ((modulePullback B S hS a).obj G) W :=
  (restrictToChartSchemeFunctor B S hS (yoneda.obj (chartFppfObject B S hS X W))
        (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS (chartFppfObject B S hS X W))
        (idEtaleChart B S hS (chartFppfObject B S hS X W))).mapIso
      (chartSmallEtaleRestrictionBaseChangeIso B S hS a G V W g hg) ≪≫
    (restrictToChartSchemeIsoIdEtaleChart B S hS X ((modulePullback B S hS a).obj G)
        (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS a G hG) W).symm ≪≫
    (restrictToChartIsoRestrictToChartScheme B S hS X.2
        ((modulePullback B S hS a).obj G) W).symm

/-- **Everything in `AlgebraicGeometry.Space.restrictToChartBaseChangeIso` after its one
pullback-image factor**: the inverse of the represented base-change isomorphism
`AlgebraicGeometry.Space.restrictToChartSchemeBaseChangeIso`, followed by
`AlgebraicGeometry.Space.restrictToChartBaseChangeEtaleTail`. -/
def restrictToChartBaseChangeTail :
    (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map g)).obj
        (restrictToChartScheme B S hS (yoneda.obj (chartFppfObject B S hS Z V))
          (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS (chartFppfObject B S hS Z V))
          (chartSmallEtaleRestriction B S hS Z G V)
          (idEtaleChart B S hS (chartFppfObject B S hS Z V))) ≅
      restrictToChart B S hS X.2 ((modulePullback B S hS a).obj G) W :=
  (restrictToChartSchemeBaseChangeIso g (chartSmallEtaleRestriction B S hS Z G V)
      (isQuasicoherentOnSite_chartSmallEtaleRestriction B S hS Z G hG V)).symm ≪≫
    restrictToChartBaseChangeEtaleTail B S hS a V W g hg G hG

/-- **The base-change isomorphism of the chart restriction, regrouped**: the Zariski pullback of
the two readings of the chart restriction, followed by
`AlgebraicGeometry.Space.restrictToChartBaseChangeTail`.

This is its definition and nothing else, written so that the adjunct can be taken: the one factor
which is an image of the pullback functor stands alone in front. -/
theorem restrictToChartBaseChangeIso_eq :
    restrictToChartBaseChangeIso B S hS a G hG V W g hg =
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map g)).mapIso
          (restrictToChartIsoRestrictToChartScheme B S hS Z.2 G V ≪≫
            restrictToChartSchemeIsoIdEtaleChart B S hS Z G hG V) ≪≫
        restrictToChartBaseChangeTail B S hS a V W g hg G hG :=
  rfl

/-! ### The adjunct -/

/-- **The adjunct of `AlgebraicGeometry.Space.restrictToChartBaseChangeIso`, reduced.**  Along
the Zariski pullback–pushforward adjunction of the morphism of chart schemes, the adjunct of the
base change of the chart restriction is the two readings of the chart restriction, then the
adjunct of the **inverse of the represented** base-change isomorphism
`AlgebraicGeometry.Space.restrictToChartSchemeBaseChangeIso`, then the direct image of
`AlgebraicGeometry.Space.restrictToChartBaseChangeEtaleTail`.

Four of the five factors therefore cost nothing: the pullback-image factor is discharged by
`CategoryTheory.Adjunction.homEquiv_naturality_left` and the three after the represented
base change by `CategoryTheory.Adjunction.homEquiv_naturality_right`.

The represented adjunct this leaves standing is itself discharged by
`AlgebraicGeometry.Space.homEquiv_restrictToChartSchemeBaseChangeIso_inv`, and
`AlgebraicGeometry.Space.homEquiv_restrictToChartBaseChangeIso_hom_peeled` is this statement with
that substitution made; both are in
`StacksFrontier/AlgebraicGeometry/Spaces/ChartSchemeRestrictionBaseChangeAdjunct.lean`.  What the
comparison of the adjunct with `AlgebraicGeometry.Space.restrictToChartPushforwardHom` still
needs is therefore one thing and not two: the action of the étale tail on the chart component of
the unit of Stacks 03D7.  See this file's implementation notes. -/
theorem homEquiv_restrictToChartBaseChangeIso_hom :
    (Scheme.Modules.pullbackPushforwardAdjunction
          ((BigFppfOver.toScheme B S hS).map g)).homEquiv _ _
        (restrictToChartBaseChangeIso B S hS a G hG V W g hg).hom =
      (restrictToChartIsoRestrictToChartScheme B S hS Z.2 G V ≪≫
          restrictToChartSchemeIsoIdEtaleChart B S hS Z G hG V).hom ≫
        ((Scheme.Modules.pullbackPushforwardAdjunction
              ((BigFppfOver.toScheme B S hS).map g)).homEquiv _ _
            (restrictToChartSchemeBaseChangeIso g (chartSmallEtaleRestriction B S hS Z G V)
              (isQuasicoherentOnSite_chartSmallEtaleRestriction B S hS Z G hG V)).inv ≫
          (Scheme.Modules.pushforward ((BigFppfOver.toScheme B S hS).map g)).map
            (restrictToChartBaseChangeEtaleTail B S hS a V W g hg G hG).hom) := by
  refine Eq.trans (congrArg (fun e ↦
    (Scheme.Modules.pullbackPushforwardAdjunction
          ((BigFppfOver.toScheme B S hS).map g)).homEquiv _ _ (Iso.hom e))
    (restrictToChartBaseChangeIso_eq B S hS a V W g hg G hG)) ?_
  refine Eq.trans (Adjunction.homEquiv_naturality_left _ _ _) ?_
  exact congrArg (fun k ↦ (restrictToChartIsoRestrictToChartScheme B S hS Z.2 G V ≪≫
      restrictToChartSchemeIsoIdEtaleChart B S hS Z G hG V).hom ≫ k)
    (Adjunction.homEquiv_naturality_right _ _ _)

end AlgebraicGeometry.Space

end
