module

public import StacksFrontier.AlgebraicGeometry.ChartTransNonNested.Model
public import StacksFrontier.AlgebraicGeometry.ProjInclusionTwist.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeProjMapDomain.Open

/-!
# Tag 01NO's twist comparison on sections, for the charts of a relative projective spectrum

`StacksFrontier/AlgebraicGeometry/ChartTransNonNested/Model.lean` asks, for a chart family on a
scheme `X`, for a local model over each member of a refinement together with an identification
`cmp` of each chart module with it and a transition `modelTrans` between the models of two
members. For the twists on a relative projective spectrum the intended instance has `X` the
relative Proj, the chart over an affine open `U` of the base carrying
`twistingSheaf (A.grading U) n`, and the refinement the inverse images of the affine opens of the
base.

This file builds the comparison itself. For **nested** affine opens `W ⊆ U` of the base it
produces, for every open `V` of the relative Proj inside the inverse image of `W`, an isomorphism
of `𝒪(V)`-modules between the sections over `V` of the two pushed-forward twists, compatible with
every restriction map:
`Stacks.AlgebraicGeometry.ChartTransRelativeProj.cmpNested`.

## Main definitions

* `Stacks.AlgebraicGeometry.ChartTransRelativeProj.pushNested`: Tag 01NO's twist comparison as a
  **morphism of sheaves of modules on the relative Proj**, from the direct image of the twist on
  the chart of `U` to the direct image of the twist on the chart of `W`.
* `Stacks.AlgebraicGeometry.ChartTransRelativeProj.cmpNested`: that morphism read as a
  `TopCat.Sheaf.LocalModuleEquiv` over the inverse image of `W`.
* `Stacks.AlgebraicGeometry.ChartTransRelativeProj.IsComposite` and `AgreeOn`: the composition law
  for three local isomorphisms and the agreement of two, as **named generic predicates**. Every
  statement below is an application of one of them; see the implementation notes for why that is
  forced here and not a matter of taste.
* `Stacks.AlgebraicGeometry.ChartTransRelativeProj.tailIso`: **the three pushforward factors of
  the comparison as a named generic isomorphism**, with every ingredient a variable.
  `pushNestedTail` is an instantiation of it rather than an anonymous `CategoryTheory.Iso.trans`,
  which is what makes the comparison computable on sections at all; see the implementation notes.
* `Stacks.AlgebraicGeometry.ChartTransRelativeProj.IsNestedCocycle`: **the one statement still
  owed**, stated, in a single integer degree. See below.
* `Stacks.AlgebraicGeometry.ChartTransRelativeProj.meetLoc`: the comparison over the inverse image
  of an affine open of the base below two given opens — the family the comparison for a pair with
  nested *inverse images* is glued over.
* `Stacks.AlgebraicGeometry.ChartTransRelativeProj.cmpGen`: **the comparison for a pair of affine
  opens of the base whose inverse images are nested.** This, and not `cmpNested`, is the field
  `Stacks.AlgebraicGeometry.ChartTransNonNested.ModelData.cmp` and `modelTrans` ask for.
* `Stacks.AlgebraicGeometry.ChartTransRelativeProj.modelData`: **the `ModelData` for the twists on
  a relative projective spectrum**, in a fixed integer degree, on the single hypothesis
  `IsNestedCocycle`; `gluedTwist`, the glued sheaf of `𝒪`-modules it produces; and `chartIso`,
  the identification of the restriction of that sheaf along a chart with the absolute twist the
  chart carried.

## Main results

* `Stacks.AlgebraicGeometry.ChartTransRelativeProj.isIso_app_pushNested`: the comparison is an
  isomorphism on the sections over every open inside the inverse image of `W`, and
  `bijective_pushNested` is the same fact as bijectivity.
* `Stacks.AlgebraicGeometry.ChartTransRelativeProj.tailIso_hom_val_app` and
  `pushNestedTail_hom_val_app`: **the action of the tail on a section**, generically and at this
  instance. The three pushforward factors contribute one restriction map, after which the tail is
  Tag 01NO's chart-level comparison read over the preimage of the open in the chart of `W`. This
  discharges the hypothesis of
  `Stacks.AlgebraicGeometry.NestedCocycleReduction.pushNested_app_val_of`, which cannot be
  discharged from inside that file.
* `Stacks.AlgebraicGeometry.ChartTransRelativeProj.image_preimage_chart`: the geometric input —
  over an open inside the inverse image of `W`, the transition morphism of the charts carries the
  preimage in the chart of `W` onto the preimage in the chart of `U`.
* `Stacks.AlgebraicGeometry.ChartTransRelativeProj.meetLoc_agreeOn_of_le` and `meetLoc_agreeOn`:
  the comparisons over two members of the family agree. The first consumes `IsNestedCocycle`
  twice and is the only place it is used; the second is the first plus the sheaf axiom.
* `Stacks.AlgebraicGeometry.ChartTransRelativeProj.cmpGen_comp`: **the cocycle for `cmpGen`**,
  which is `ModelData.cmp_modelTrans` at this refinement. It follows from `IsNestedCocycle` with
  no further input: over the inverse image of an affine open below all three, all three glued
  comparisons factor through that open's own chart, and comparisons through one model compose for
  free.
* `Stacks.AlgebraicGeometry.ChartTransRelativeProj.le_iSup_preimage_affine_le`,
  `le_iSup_preimage_meetIndex`, `le_iSup_preimage_inf` and `le_iSup_preimage_inf₃`: the covering
  statements the glueing steps need.

## The route, and why the comparison is built at the level of sheaves of modules

Tag 01NO's comparison is already an **isomorphism of sheaves of modules**,
`Stacks.AlgebraicGeometry.ProjInclusionTwist.projInclusionTwistIso`, on the *pullback* of the
twist along the transition morphism. Three steps carry it to the statement about sections:

* `AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` replaces the pullback by the
  **restriction** along the transition morphism, whose sections over an open of the smaller chart
  are by definition the sections of the twist on the larger chart over the *image* of that open
  (`AlgebraicGeometry.Scheme.Modules.restrictAppIso` is the identity isomorphism);
* the unit of `AlgebraicGeometry.Scheme.Modules.restrictAdjunction` turns that into a morphism
  out of the twist on the larger chart. Its component over an open `T` is the restriction map
  along `transition ''ᵁ transition ⁻¹ᵁ T ≤ T`, which is an **equality** of opens exactly when `T`
  is the preimage of an open inside the inverse image of `W` — that is
  `image_preimage_preimage_chart`, and it is where the geometry enters;
* pseudofunctoriality of the pushforward and
  `Stacks.AlgebraicGeometry.RelativeProj.RelativeProjData.chart_transition` move everything
  to the relative Proj.

Composing those in the category of sheaves of modules on the relative Proj, rather than on
sections, is what makes the `𝒪(V)`-linearity and the compatibility with restriction **free**:
they are the naturality of a single morphism. The only thing proved by hand is that one of the
four factors — the unit — is invertible on the sections in question, and that is a restriction map
between two opens which are equal.

## What is not done here, precisely

`Stacks.AlgebraicGeometry.ChartTransRelativeProj.IsNestedCocycle` is **not proved**, and it is
now the *only* thing this file is conditional on: `cmpGen`, `cmpGen_comp`, `modelData` and
`gluedTwist` all take it as a hypothesis and nothing else is owed. It is the cocycle for a nested
chain `W ⊆ W' ⊆ U`, which is `ModelData`'s `cmp_modelTrans` at a **base**-nested triple.

It is stated **in one integer degree**, which is the degreewise split the previous round recorded
as reduction 3 below; so the twist `𝒪(1)` is conditional on the cocycle in the degree `n = 1`
alone, and not on it in degrees no consumer uses.

No functoriality of Tag 01MY's twist map in the graded ring map exists in the development, so the
route to it is a rigidity statement applied to one leg composed with the inverse of the other:
that is an endomorphism family of the twists on the chart of `W`, and rigidity asks it to fix the
restricted homogeneous global sections and — in the general statements — to be multiplicative.

**The multiplicativity half is not needed in degree one.**

* `Stacks.AlgebraicGeometry.TwistRigidity.IsMultiplicative` for the composite is **not** needed:
  `Stacks.AlgebraicGeometry.TwistRigidityDegreeOne.eq_id_res` is relative rigidity in degree one
  with **no multiplicativity hypothesis at all**. In place of it that statement asks only that the
  graded ring of sections over the smaller affine open have, at every point of its `Proj`, a
  nonvanishing element of degree one — which holds for `Sym(E)`, a symmetric algebra being
  generated in degree one. The mechanism is that `α 1` is a morphism of sheaves of `𝒪`-modules,
  hence `𝒪`-linear for free, and that Tag 01MS trivializes `𝒪(1)` over `D₊(g)` by multiplication
  by the very global section `degreeSection 𝒜 1 g`
  (`Stacks.AlgebraicGeometry.ProjDegreeOneTriv.bijective_smul_degreeOneSection`), so every local
  section there is a multiple of that generator and no product of two twist sections occurs.
  `Stacks.AlgebraicGeometry.TwistRigidityDS.eq_id_res` weakens the hypothesis instead of removing
  it, and is the statement to use in degrees other than one.
* So the claim that Tag 01MY's multiplicativity had to be **transported** through the four factors
  of `pushNested` — the adjunction unit, `pushforwardComp`, `pushforwardCongr` and
  `restrictTwistIso` — is withdrawn for `n = 1`. (The input it referred to does exist, as
  `Stacks.AlgebraicGeometry.ProjMapCard.twistPushforwardMap_twistMultiplicationMap` with the
  clause `twistMap_comp_pullbackTwistMultiplication` carrying
  `@[stacks 01MY "graded-algebra multiplication"]`; the earlier claim that it was "proved nowhere"
  was also false. It is simply not needed here.)

**What is owed, stated exactly.** One section computation, and nothing else:

> for affine opens `W ⊆ U` of the base, a degree `k`, and a homogeneous `c` of degree `k` of the
> graded ring of sections over `U`, the component of `cmpNested A W U h hW hU k` on the sections
> over `toBase ⁻¹ᵁ W` carries the restriction of the direct image of
> `degreeSection (A.grading U) k c` to the direct image of
> `degreeSection (A.grading W) k ⟨A.res h c, _⟩`.

With it, `IsNestedCocycle A 1` follows: the composite of the three legs, read through the chart of
`W` by `Stacks.AlgebraicGeometry.TwistExistence.restrictLocalEquiv` and
`isoOfLocalEquiv` exactly as `Stacks.AlgebraicGeometry.TwistExistence.overlapEndo` does, satisfies
`Stacks.AlgebraicGeometry.RelativeTwistRigidity.FixesResDegreeSections (A.res hWU)`, so
`TwistRigidityDegreeOne.eq_id_res` makes it the identity, and the passage from `V = toBase ⁻¹ᵁ W`
to an arbitrary `V` inside it is the image/preimage transport of
`Stacks.AlgebraicGeometry.TwistExistence.cmp_agreeOn_nested`. Nothing in that chain is new
mathematics; the section computation is.

The ingredients for the section computation, all in the library, in the order they compose. Because
`FixesResDegreeSections` is a statement about sections over `⊤` of `Proj Γ(W, A)`, and
`chart W ''ᵁ ⊤ = toBase ⁻¹ᵁ W`, **only the component over `⊤` is needed** — which is the one
degree of freedom the six-factor computation already has.

* `Stacks.AlgebraicGeometry.ProjInclusionDegreeSection.composite_degreeSection`: the six-factor
  pullback comparison on a pulled-back homogeneous global section over `⊤`, landing on exactly
  `degreeSection (A.grading W) k ⟨A.res h c, _⟩`. Its statement spells the composite out rather
  than naming `projInclusionTwistMap`; the reassociation joining the two is
  `Stacks.AlgebraicGeometry.ProjInclusionTwist.projInclusionTwistMap_eq_split`, and the named
  comparison on a degree-`k` section is
  `Stacks.AlgebraicGeometry.ProjInclusionDegreeSection.projInclusionTwistMap_degreeSection`.
* `AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` and
  `Stacks.AlgebraicGeometry.ProjTwistTheta.restrictUnit_comp_map_restrictFunctorIsoPullback`: the
  bridge identifying the restriction unit followed by that isomorphism with the **pullback**
  adjunction unit, which is what `pullbackSection` in `composite_degreeSection` is built from.
  This is what connects `pushNestedUnit` and `restrictTwistIso` to the pullback-side statement.
* The two structural factors `pushforwardComp` and `pushforwardCongr` are components of natural
  isomorphisms; reassociating them past the other two is the remaining bookkeeping.

The **second** gap recorded by the previous round is now closed. `ModelData.cmp k i` is required
for every pair with `L k ≤ U i`, and for the intended refinement that reads
`toBase ⁻¹ᵁ W ≤ toBase ⁻¹ᵁ U`, **not** `W ≤ U`: the structure morphism of a relative Proj need
not be surjective, so the first is strictly weaker than the second and `cmpNested` does not
supply the field. `cmpGen` closes it by glueing — `toBase ⁻¹ᵁ W` is covered by the inverse images
of the affine opens of the base below both (`le_iSup_preimage_meetIndex`), over each of which
`meetLoc` is a comparison built from two nested ones, and those agree on overlaps by
`meetLoc_agreeOn`.

What is still absent beyond the cocycle: no `Stacks.AlgebraicGeometry.RelativeProjTwists.ChartData`
and no `TwistData`. `modelData`, `gluedTwist` and `chartIso` give one sheaf of modules per integer
degree together with its chart identifications; a `ChartData` asks for the chart identifications
of a **single graded algebra** on the relative Proj, and neither the multiplication nor the unit
of that algebra is constructed anywhere, in this file or elsewhere. Nor is the quasi-coherence of
the glued pieces, nor the homogeneous-section map `ψ` with its three compatibilities, all of which
a `TwistData` also asks for.

No `stacks` attribute is attached to any declaration in this file. Nothing here is a complete
covering set for any label: Tag 01NO's twist-isomorphism assertion is already carried by
`Stacks.AlgebraicGeometry.ProjInclusionTwist.isIso_projInclusionTwistMap`, and Tag 01NR's
existence assertion is **not** earned — it asks for a `TwistData`, every declaration here is
conditional on an unproved hypothesis, and neither would be acceptable alone.

## Implementation notes

The elaboration budget at this instance is the binding constraint, and the facts below explain
the shape of the file.

* `Scheme.Modules.restrict` takes the module before the morphism with the target scheme implicit,
  so applying it to `twistingSheaf (A.grading U) n` leaves that scheme a metavariable which
  unification cannot solve. Everything below therefore goes through
  `Scheme.Modules.restrictFunctor`, whose source and target are fixed by the morphism.
* `rw` is never used on a goal mentioning a pushforward of a twist: it exhausts the recursion
  limit. `pushNested_app` is an *application* of
  `AlgebraicGeometry.Scheme.Modules.Hom.comp_app`, and the naturality of `cmpNested` is obtained
  by instantiating `localModuleEquivOfBijective`, a definition in which every ingredient is a
  variable, rather than by proving the same statement here.
* The naturality of `cmpNested`, written out at this instance, exhausts the recursion
  limit with `rw`, with a term-mode `Eq.trans` chain, and by instantiating a generic naturality
  *lemma* at the concrete morphism — but not when the whole `TopCat.Sheaf.LocalModuleEquiv` is
  produced by one generic definition.

More precisely:

* **The wall is an `app` applied to a composite, not `rfl` and not matching a composite head.**
  `rfl` *is* usable at this instance, at the level of the local isomorphisms:
  `meetLoc_eq`, which states `meetLoc = modelPair (cmpNested _) (cmpNested _)` with the two
  containments supplied freely, is proved by `rfl` and elaborates. What does not elaborate is
  `(modelPair _ _).app V hV s` **written out** at this instance: identifying the two isomorphisms
  underneath an `app` sends the elaborator through `cmpNested`'s body into `pushNested`. So the
  identification is made once, at the level of the isomorphisms, and transported into the
  predicate by `congrArg` (`isComposite_meetLoc`).
* **A concretely written equation cannot be matched against a generically produced one.** This is
  the decisive fact. `hcoc W W' U … s` elaborates fine on its own, and discarding the
  result compiles; what fails with `maxRecDepth` is matching its type against the *same* equation
  written out in a theorem statement at this instance. That is why `IsNestedCocycle`'s conclusion
  is spelled with `IsComposite`, and why every hypothesis and conclusion in the glueing is an
  application of `IsComposite` or `AgreeOn`: both sides of every match are then generic bodies
  instantiated, and those agree on the nose.
* **The kernel is a separate budget.** `modelData`'s `cmp_modelTrans` field, given as
  `cmpGen_comp … V hV (hV.trans hkk') s`, is accepted by the elaborator and then exceeds the
  **kernel's** deterministic timeout. Supplying the field one argument shorter — stopping at the
  `IsComposite` and letting the structure's own binder take `s` — compiles. The two terms differ
  only in one eta step.

## References

* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 00AN](https://stacks.math.columbia.edu/tag/00AN)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ChartTransNonNested
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj

namespace Stacks.AlgebraicGeometry.ChartTransRelativeProj

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj
attribute [local instance_reducible] ProjectiveSpectrum.top

universe u

/-! ### Two general facts -/

/-- **A restriction map between two opens that happen to be equal is an isomorphism.** The two
inclusions are not assumed related: morphisms between opens are unique, so a morphism between
equal opens is `eqToHom` whatever it is. -/
public theorem isIso_presheaf_map_of_eq {X : Scheme.{u}} (M : X.Modules) {P Q : X.Opens}
    (hPQ : P = Q) (i : P ⟶ Q) : IsIso (M.presheaf.map i.op) :=
  have : IsIso i :=
    { out := ⟨eqToHom hPQ.symm, Subsingleton.elim _ _, Subsingleton.elim _ _⟩ }
  inferInstance

/-- A morphism of sheaves of modules on a scheme whose component on the sections over an open is
an isomorphism is bijective there. -/
public theorem bijective_val_app_of_isIso {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N)
    (V : X.Opens) [IsIso (φ.app V)] : Function.Bijective (φ.val.app (op V)).hom :=
  ConcreteCategory.bijective_of_isIso (φ.app V)

/-- **A morphism of presheaves of modules which is bijective on the sections over every open
contained in a given open is a local isomorphism there.**

Stated and proved where every ingredient is a variable — no scheme, no `Proj`, no graded ring.
That is not economy: at the concrete instance below, every spelling of this proof
exhausts the recursion limit, whether written with `rw`, with a term-mode `Eq.trans` chain, or by
instantiating a generic naturality lemma at the concrete morphism. Instantiating *this*
definition is a single application and asks for no reduction at all. -/
public def localModuleEquivOfBijective {X : TopCat.{u}} {𝒪 : (Opens X)ᵒᵖ ⥤ RingCat.{u}}
    {M N : PresheafOfModules.{u} 𝒪} (φ : M ⟶ N) (W₀ : Opens X)
    (hb : ∀ V : Opens X, V ≤ W₀ → Function.Bijective (φ.app (op V)).hom) :
    TopCat.Sheaf.LocalModuleEquiv M N W₀ where
  app V hV := LinearEquiv.ofBijective _ (hb V hV)
  naturality hV hWV s := by
    rw [LinearEquiv.ofBijective_apply, LinearEquiv.ofBijective_apply]
    exact PresheafOfModules.app_resLE φ hWV s

/-- The local isomorphism `localModuleEquivOfBijective φ W₀ hb` acts on sections as `φ`. -/
@[simp]
public theorem localModuleEquivOfBijective_app {X : TopCat.{u}}
    {𝒪 : (Opens X)ᵒᵖ ⥤ RingCat.{u}} {M N : PresheafOfModules.{u} 𝒪} (φ : M ⟶ N) (W₀ : Opens X)
    (hb : ∀ V : Opens X, V ≤ W₀ → Function.Bijective (φ.app (op V)).hom)
    (V : Opens X) (hV : V ≤ W₀) (s : M.obj (op V)) :
    (localModuleEquivOfBijective φ W₀ hb).app V hV s = φ.app (op V) s :=
  rfl

/-- **Two local isomorphisms with a common target, cancelled against each other.** This is the
shape every comparison below has: each chart module is identified with the module on a third,
smaller chart, and the comparison of the two is the first identification followed by the inverse
of the second.

It exists as a named generic definition for the same reason as
`Stacks.AlgebraicGeometry.ChartTransRelativeProj.localModuleEquivOfBijective`: at the concrete
instance, matching a statement against `TopCat.Sheaf.LocalModuleEquiv.trans` composed with
`symm` exhausts the recursion limit, while matching it against one named head symbol does not. -/
public def modelPair {X : TopCat.{u}} {𝒪 : (Opens X)ᵒᵖ ⥤ RingCat.{u}}
    {M N Q : PresheafOfModules.{u} 𝒪} {W₀ : Opens X}
    (a : TopCat.Sheaf.LocalModuleEquiv M Q W₀) (b : TopCat.Sheaf.LocalModuleEquiv N Q W₀) :
    TopCat.Sheaf.LocalModuleEquiv M N W₀ :=
  a.trans b.symm

/-- On sections, `modelPair a b` is `a` followed by the inverse of `b`. -/
public theorem modelPair_app {X : TopCat.{u}} {𝒪 : (Opens X)ᵒᵖ ⥤ RingCat.{u}}
    {M N Q : PresheafOfModules.{u} 𝒪} {W₀ : Opens X}
    (a : TopCat.Sheaf.LocalModuleEquiv M Q W₀) (b : TopCat.Sheaf.LocalModuleEquiv N Q W₀)
    (V : Opens X) (hV : V ≤ W₀) (s : M.obj (op V)) :
    (modelPair a b).app V hV s = ((b.app V hV).symm) (a.app V hV s) :=
  TopCat.Sheaf.LocalModuleEquiv.trans_app a b.symm V hV s

/-- **The cocycle for three comparisons through one common model is free.** The middle
identification cancels against its own inverse. -/
public theorem modelPair_comp {X : TopCat.{u}} {𝒪 : (Opens X)ᵒᵖ ⥤ RingCat.{u}}
    {M N P Q : PresheafOfModules.{u} 𝒪} {W₀ : Opens X}
    (a : TopCat.Sheaf.LocalModuleEquiv M Q W₀) (b : TopCat.Sheaf.LocalModuleEquiv N Q W₀)
    (c : TopCat.Sheaf.LocalModuleEquiv P Q W₀)
    (V : Opens X) (hV : V ≤ W₀) (s : M.obj (op V)) :
    (modelPair b c).app V hV ((modelPair a b).app V hV s) = (modelPair a c).app V hV s :=
  (modelPair_app b c V hV _).trans
    ((congrArg (fun z => ((c.app V hV).symm) z)
        ((congrArg (b.app V hV) (modelPair_app a b V hV s)).trans
          (LinearEquiv.apply_symm_apply (b.app V hV) (a.app V hV s)))).trans
      (modelPair_app a c V hV s).symm)

/-- Congruence for the argument of a local isomorphism, at the level of variables. -/
public theorem app_congr_arg {X : TopCat.{u}} {𝒪 : (Opens X)ᵒᵖ ⥤ RingCat.{u}}
    {M N : PresheafOfModules.{u} 𝒪} {W₀ V : Opens X}
    (e : TopCat.Sheaf.LocalModuleEquiv M N W₀) (hV : V ≤ W₀) {x y : M.obj (op V)} (hxy : x = y) :
    e.app V hV x = e.app V hV y :=
  congrArg (e.app V hV) hxy

/-! ### Composition laws and agreement, as named predicates -/

/-- **The composition law for three local isomorphisms, on the sections over one open.** Read
`IsComposite e₀ e₁ e₂ V hV₀ hV₁` as: over `V`, following `e₀` by `e₁` is `e₂`.

This is a named generic predicate rather than an equation written out, and it is the single
structural decision the rest of the file turns on. An equation
`e₁.app V _ (e₀.app V _ s) = e₂.app V _ s` **written out at the concrete instance** cannot be
identified with the same equation obtained by instantiating a generic statement — the two
elaborations reach the module structure on the sections by different routes, and reconciling them
drives the elaborator through `cmpNested` into the pushforward of the twist, which exhausts the
recursion limit. Every hypothesis and every conclusion below is an application of this predicate
or of `AgreeOn`, so that both sides of every match are generic, where they agree on the nose. -/
public def IsComposite {X : TopCat.{u}} {𝒪 : (Opens X)ᵒᵖ ⥤ RingCat.{u}}
    {M N P : PresheafOfModules.{u} 𝒪} {W₀ W₁ : Opens X}
    (e₀ : TopCat.Sheaf.LocalModuleEquiv M N W₁) (e₁ : TopCat.Sheaf.LocalModuleEquiv N P W₀)
    (e₂ : TopCat.Sheaf.LocalModuleEquiv M P W₀) (V : Opens X) (hV₀ : V ≤ W₀) (hV₁ : V ≤ W₁) :
    Prop :=
  ∀ s : M.obj (op V), e₁.app V hV₀ (e₀.app V hV₁ s) = e₂.app V hV₀ s

/-- **Two local isomorphisms of the same pair of modules agree on the sections over one open.**
The two may be defined on two different opens, both containing `V`. -/
public def AgreeOn {X : TopCat.{u}} {𝒪 : (Opens X)ᵒᵖ ⥤ RingCat.{u}}
    {M N : PresheafOfModules.{u} 𝒪} {W₀ W₁ : Opens X}
    (e₀ : TopCat.Sheaf.LocalModuleEquiv M N W₀) (e₁ : TopCat.Sheaf.LocalModuleEquiv M N W₁)
    (V : Opens X) (hV₀ : V ≤ W₀) (hV₁ : V ≤ W₁) : Prop :=
  ∀ s : M.obj (op V), e₀.app V hV₀ s = e₁.app V hV₁ s

/-- **The second identification undoes `modelPair`.** -/
public theorem isComposite_modelPair {X : TopCat.{u}} {𝒪 : (Opens X)ᵒᵖ ⥤ RingCat.{u}}
    {M N Q : PresheafOfModules.{u} 𝒪} {W₀ : Opens X}
    (a : TopCat.Sheaf.LocalModuleEquiv M Q W₀) (b : TopCat.Sheaf.LocalModuleEquiv N Q W₀)
    (V : Opens X) (hV : V ≤ W₀) : IsComposite (modelPair a b) b a V hV hV :=
  fun s => (app_congr_arg b hV (modelPair_app a b V hV s)).trans
    (LinearEquiv.apply_symm_apply (b.app V hV) (a.app V hV s))

/-- **Replacing a local isomorphism by one it agrees with preserves a composition law.** -/
public theorem isComposite_of_agreeOn {X : TopCat.{u}} {𝒪 : (Opens X)ᵒᵖ ⥤ RingCat.{u}}
    {M N P : PresheafOfModules.{u} 𝒪} {W₀ W₁ W₂ : Opens X}
    (e₀ : TopCat.Sheaf.LocalModuleEquiv M N W₁) (e₀' : TopCat.Sheaf.LocalModuleEquiv M N W₂)
    (e₁ : TopCat.Sheaf.LocalModuleEquiv N P W₀) (e₂ : TopCat.Sheaf.LocalModuleEquiv M P W₀)
    (V : Opens X) (hV₀ : V ≤ W₀) (hV₁ : V ≤ W₁) (hV₂ : V ≤ W₂)
    (h : AgreeOn e₀ e₀' V hV₁ hV₂) (hc : IsComposite e₀' e₁ e₂ V hV₀ hV₂) :
    IsComposite e₀ e₁ e₂ V hV₀ hV₁ :=
  fun s => (app_congr_arg e₁ hV₀ (h s)).trans (hc s)

/-- **Two comparisons of one pair of modules, each factoring through its own model, agree where
the two models are themselves compared.** The four hypotheses are: each comparison undoes into its
own pair, and the transition between the models carries each leg of the second pair to the
corresponding leg of the first. That last pair is the nested cocycle, used once on each side. -/
public theorem agreeOn_of_model {X : TopCat.{u}} {𝒪 : (Opens X)ᵒᵖ ⥤ RingCat.{u}}
    {M N Q₀ Q₁ : PresheafOfModules.{u} 𝒪} {W₀ W₁ : Opens X}
    (e₀ : TopCat.Sheaf.LocalModuleEquiv M N W₀) (e₁ : TopCat.Sheaf.LocalModuleEquiv M N W₁)
    (a₀ : TopCat.Sheaf.LocalModuleEquiv M Q₀ W₀) (b₀ : TopCat.Sheaf.LocalModuleEquiv N Q₀ W₀)
    (a₁ : TopCat.Sheaf.LocalModuleEquiv M Q₁ W₁) (b₁ : TopCat.Sheaf.LocalModuleEquiv N Q₁ W₁)
    (t : TopCat.Sheaf.LocalModuleEquiv Q₁ Q₀ W₀)
    (V : Opens X) (hV₀ : V ≤ W₀) (hV₁ : V ≤ W₁)
    (h₀ : IsComposite e₀ b₀ a₀ V hV₀ hV₀) (h₁ : IsComposite e₁ b₁ a₁ V hV₁ hV₁)
    (hα : IsComposite a₁ t a₀ V hV₀ hV₁) (hβ : IsComposite b₁ t b₀ V hV₀ hV₁) :
    AgreeOn e₁ e₀ V hV₁ hV₀ :=
  fun s => (b₀.app V hV₀).injective
    (((hβ (e₁.app V hV₁ s)).symm.trans (app_congr_arg t hV₀ (h₁ s))).trans
      ((hα s).trans (h₀ s).symm))

/-- **Three comparisons that factor through one common model compose.** The middle identification
cancels against itself. -/
public theorem isComposite_of_model {X : TopCat.{u}} {𝒪 : (Opens X)ᵒᵖ ⥤ RingCat.{u}}
    {M N P Q : PresheafOfModules.{u} 𝒪} {W₀ W₁ W₂ : Opens X}
    (e₀ : TopCat.Sheaf.LocalModuleEquiv M N W₁) (e₁ : TopCat.Sheaf.LocalModuleEquiv N P W₀)
    (e₂ : TopCat.Sheaf.LocalModuleEquiv M P W₀)
    (a : TopCat.Sheaf.LocalModuleEquiv M Q W₂) (b : TopCat.Sheaf.LocalModuleEquiv N Q W₂)
    (c : TopCat.Sheaf.LocalModuleEquiv P Q W₂)
    (V : Opens X) (hV₀ : V ≤ W₀) (hV₁ : V ≤ W₁) (hV₂ : V ≤ W₂)
    (h₀ : IsComposite e₀ b a V hV₂ hV₁) (h₁ : IsComposite e₁ c b V hV₂ hV₀)
    (h₂ : IsComposite e₂ c a V hV₂ hV₀) :
    IsComposite e₀ e₁ e₂ V hV₀ hV₁ :=
  fun s => (c.app V hV₂).injective ((h₁ (e₀.app V hV₁ s)).trans ((h₀ s).trans (h₂ s).symm))

/-- **Agreement is local**: two local isomorphisms agreeing over every open inside a member of a
covering family agree. The separation half of the sheaf axiom. -/
public theorem agreeOn_of_cover {X : TopCat.{u}} {𝒪 : (Opens X)ᵒᵖ ⥤ RingCat.{u}}
    {M N : PresheafOfModules.{u} 𝒪}
    (hN : CategoryTheory.Presheaf.IsSheaf (Opens.grothendieckTopology X) N.presheaf)
    {W₀ W₁ : Opens X} (e₀ : TopCat.Sheaf.LocalModuleEquiv M N W₀)
    (e₁ : TopCat.Sheaf.LocalModuleEquiv M N W₁) {ρ : Type u} (R : ρ → Opens X)
    (h : ∀ (r : ρ) (V : Opens X) (hV₀ : V ≤ W₀) (hV₁ : V ≤ W₁), V ≤ R r →
      AgreeOn e₀ e₁ V hV₀ hV₁)
    (V : Opens X) (hV₀ : V ≤ W₀) (hV₁ : V ≤ W₁) (hcov : V ≤ ⨆ r, R r) :
    AgreeOn e₀ e₁ V hV₀ hV₁ := by
  intro s
  refine TopCat.Sheaf.eq_of_locally_eq_of_isSheafPresheaf hN (fun r => V ⊓ R r)
    (fun _ => inf_le_left) (TopCat.Sheaf.le_iSup_inf_of_le hcov) fun r => ?_
  refine Eq.trans (e₀.naturality hV₀ inf_le_left s).symm ?_
  refine Eq.trans ?_ (e₁.naturality hV₁ inf_le_left s)
  exact h r (V ⊓ R r) (inf_le_left.trans hV₀) (inf_le_left.trans hV₁) inf_le_right _

/-- **The composition law is local**: three local isomorphisms composing over every open inside a
member of a covering family compose. -/
public theorem isComposite_of_cover {X : TopCat.{u}} {𝒪 : (Opens X)ᵒᵖ ⥤ RingCat.{u}}
    {M N P : PresheafOfModules.{u} 𝒪}
    (hP : CategoryTheory.Presheaf.IsSheaf (Opens.grothendieckTopology X) P.presheaf)
    {W₀ W₁ : Opens X} (e₀ : TopCat.Sheaf.LocalModuleEquiv M N W₁)
    (e₁ : TopCat.Sheaf.LocalModuleEquiv N P W₀) (e₂ : TopCat.Sheaf.LocalModuleEquiv M P W₀)
    {ρ : Type u} (R : ρ → Opens X)
    (h : ∀ (r : ρ) (V : Opens X) (hV₀ : V ≤ W₀) (hV₁ : V ≤ W₁), V ≤ R r →
      IsComposite e₀ e₁ e₂ V hV₀ hV₁)
    (V : Opens X) (hV₀ : V ≤ W₀) (hV₁ : V ≤ W₁) (hcov : V ≤ ⨆ r, R r) :
    IsComposite e₀ e₁ e₂ V hV₀ hV₁ := by
  intro s
  refine TopCat.Sheaf.eq_of_locally_eq_of_isSheafPresheaf hP (fun r => V ⊓ R r)
    (fun _ => inf_le_left) (TopCat.Sheaf.le_iSup_inf_of_le hcov) fun r => ?_
  refine Eq.trans (e₁.naturality hV₀ inf_le_left (e₀.app V hV₁ s)).symm ?_
  refine Eq.trans (app_congr_arg e₁ (inf_le_left.trans hV₀)
    (e₀.naturality hV₁ (inf_le_left : V ⊓ R r ≤ V) s).symm) ?_
  refine Eq.trans ?_ (e₂.naturality hV₀ inf_le_left s)
  exact h r (V ⊓ R r) (inf_le_left.trans hV₀) (inf_le_left.trans hV₁) inf_le_right _

/-! ### The tail of the comparison, as a named generic isomorphism -/

/-- **The three pushforward factors of the comparison, as a named generic isomorphism.**
Pseudofunctoriality of the pushforward along two morphisms composing to a third, the congruence
for that composition, and the functor image of an isomorphism of modules on the source.

It exists as a named definition with every ingredient a variable for the same reason as
`Stacks.AlgebraicGeometry.ChartTransRelativeProj.modelPair`, and the measurement behind it is
sharper: as an anonymous `CategoryTheory.Iso.trans`, the identification of this composite with
its three factors underneath a `val.app` is unreachable, because matching a metavariable's
`CategoryTheory.Iso.hom` projection against a composite is not a first-order problem. Written
this way the identification is the instantiation of
`Stacks.AlgebraicGeometry.ChartTransRelativeProj.tailIso_hom_val_app`, which substitutes for
variables and asks for no reduction at all. -/
public def tailIso {X Y Z : Scheme.{u}} (g : Y ⟶ Z) (c : Z ⟶ X) (d : Y ⟶ X) (hcd : g ≫ c = d)
    {R N : Y.Modules} (e : R ≅ N) :
    (Scheme.Modules.pushforward c).obj ((Scheme.Modules.pushforward g).obj R) ≅
      (Scheme.Modules.pushforward d).obj N :=
  (Scheme.Modules.pushforwardComp g c).app R ≪≫
    (Scheme.Modules.pushforwardCongr hcd).app R ≪≫
    (Scheme.Modules.pushforward d).mapIso e

/-- **The action of `Stacks.AlgebraicGeometry.ChartTransRelativeProj.tailIso` on a section.**
Pseudofunctoriality of the pushforward is the identity, the congruence is a transport of opens,
and the functor image of `e` is `e` read at the preimage. The whole composite therefore acts as a
single restriction map followed by `e`. -/
public theorem tailIso_hom_val_app {X Y Z : Scheme.{u}} (g : Y ⟶ Z) (c : Z ⟶ X) (d : Y ⟶ X)
    (hcd : g ≫ c = d) {R N : Y.Modules} (e : R ≅ N) (V : X.Opens)
    (y : ((Scheme.Modules.pushforward c).obj
      ((Scheme.Modules.pushforward g).obj R)).val.obj (op V)) :
    (tailIso g c d hcd e).hom.val.app (op V) y =
      e.hom.val.app (op (d ⁻¹ᵁ V))
        (R.val.map (eqToHom (show d ⁻¹ᵁ V = g ⁻¹ᵁ (c ⁻¹ᵁ V) from hcd ▸ rfl)).op y) :=
  rfl

/-- The same with the inclusion of opens a **variable**: morphisms between opens are unique, so
the transport the congruence factor contributes never has to be exhibited. -/
public theorem tailIso_hom_val_app_of {X Y Z : Scheme.{u}} (g : Y ⟶ Z) (c : Z ⟶ X) (d : Y ⟶ X)
    (hcd : g ≫ c = d) {R N : Y.Modules} (e : R ≅ N) (V : X.Opens)
    (i : d ⁻¹ᵁ V ⟶ g ⁻¹ᵁ (c ⁻¹ᵁ V))
    (y : ((Scheme.Modules.pushforward c).obj
      ((Scheme.Modules.pushforward g).obj R)).val.obj (op V)) :
    (tailIso g c d hcd e).hom.val.app (op V) y =
      e.hom.val.app (op (d ⁻¹ᵁ V)) (R.val.map i.op y) :=
  (tailIso_hom_val_app g c d hcd e V y).trans
    (congrArg (e.hom.val.app (op (d ⁻¹ᵁ V)))
      (by obtain rfl : i = eqToHom (show d ⁻¹ᵁ V = g ⁻¹ᵁ (c ⁻¹ᵁ V) from hcd ▸ rfl) :=
            Subsingleton.elim _ _
          rfl))

/-- **The action on a section of any isomorphism identified with the tail by an equation of
isomorphisms.** The subject is a *variable* `T`, so instantiating this asks the kernel for no
conversion at all: the identification is discharged once, at the level of isomorphisms, where it
is a single delta step, and transported underneath the `val.app` by `congrArg`.

This is the shape that survives at the concrete instance. Supplying
`Stacks.AlgebraicGeometry.ChartTransRelativeProj.tailIso_hom_val_app_of` directly for the tail —
which differs from this only in letting the kernel perform that one delta step *underneath* the
`val.app` rather than above it — exceeds the kernel's deterministic timeout. -/
public theorem tailIso_hom_val_app_eq {X Y Z : Scheme.{u}} (g : Y ⟶ Z) (c : Z ⟶ X) (d : Y ⟶ X)
    (hcd : g ≫ c = d) {R N : Y.Modules} (e : R ≅ N)
    (T : (Scheme.Modules.pushforward c).obj ((Scheme.Modules.pushforward g).obj R) ≅
      (Scheme.Modules.pushforward d).obj N)
    (hT : T = tailIso g c d hcd e) (V : X.Opens) (i : d ⁻¹ᵁ V ⟶ g ⁻¹ᵁ (c ⁻¹ᵁ V))
    (y : ((Scheme.Modules.pushforward c).obj
      ((Scheme.Modules.pushforward g).obj R)).val.obj (op V)) :
    T.hom.val.app (op V) y = e.hom.val.app (op (d ⁻¹ᵁ V)) (R.val.map i.op y) :=
  (congrArg (fun E : (Scheme.Modules.pushforward c).obj
        ((Scheme.Modules.pushforward g).obj R) ≅ (Scheme.Modules.pushforward d).obj N =>
      E.hom.val.app (op V) y) hT).trans (tailIso_hom_val_app_of g c d hcd e V i y)


variable {S : Scheme.{u}} (A : SheafGradedAlgebra S)

section Nested

variable (W U : S.Opens) (h : W ≤ U) (hW : IsAffineOpen W) (hU : IsAffineOpen U)

/-- The preimage in the smaller chart of an open of the relative Proj is the preimage under the
transition morphism of its preimage in the larger chart. -/
private theorem chart_preimage_eq_preimage_transition (V : (relativeProj A).scheme.Opens) :
    (relativeProj A).chart W hW ⁻¹ᵁ V
      = projInclusionMap A W U h hW hU ⁻¹ᵁ ((relativeProj A).chart U hU ⁻¹ᵁ V) := by
  rw [← Scheme.Hom.comp_preimage, (relativeProj A).chart_transition W U h hW hU]

/-- Over an open of the relative Proj lying in the inverse image of the smaller affine open, the
image under the transition morphism of the preimage in the smaller chart is the preimage in the
larger chart. -/
public theorem image_preimage_chart (V : (relativeProj A).scheme.Opens)
    (hV : V ≤ (relativeProj A).toBase ⁻¹ᵁ W) :
    projInclusionMap A W U h hW hU ''ᵁ ((relativeProj A).chart W hW ⁻¹ᵁ V)
      = (relativeProj A).chart U hU ⁻¹ᵁ V := by
  have hrange : (relativeProj A).chart U hU ⁻¹ᵁ V
      ≤ (projInclusionMap A W U h hW hU).opensRange := by
    rw [RelativeProjMapDomain.opensRange_projInclusionMap]
    intro x hx
    have hx2 : (relativeProj A).toBase ((relativeProj A).chart U hU x) ∈ W := hV hx
    rwa [RelativeProjMapDomain.toBase_chart_apply] at hx2
  rw [chart_preimage_eq_preimage_transition A W U h hW hU V,
    Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.mpr hrange]

/-- The same statement with the preimage taken in the larger chart: the transition morphism does
not shrink the preimage of an open lying in the inverse image of the smaller affine open. This is
the form the unit of the restriction--pushforward adjunction is read at. -/
public theorem image_preimage_preimage_chart (V : (relativeProj A).scheme.Opens)
    (hV : V ≤ (relativeProj A).toBase ⁻¹ᵁ W) :
    projInclusionMap A W U h hW hU ''ᵁ (projInclusionMap A W U h hW hU ⁻¹ᵁ
        ((relativeProj A).chart U hU ⁻¹ᵁ V))
      = (relativeProj A).chart U hU ⁻¹ᵁ V := by
  rw [← chart_preimage_eq_preimage_transition A W U h hW hU V]
  exact image_preimage_chart A W U h hW hU V hV

/-- Tag 01NO's twist comparison, read on the restriction along the transition morphism instead of
on its pullback. -/
public def restrictTwistIso (n : ℤ) :
    (Scheme.Modules.restrictFunctor (projInclusionMap A W U h hW hU)).obj
        (twistingSheaf (A.grading U) n) ≅
      twistingSheaf (A.grading W) n :=
  (Scheme.Modules.restrictFunctorIsoPullback (projInclusionMap A W U h hW hU)).app
      (twistingSheaf (A.grading U) n) ≪≫
    ProjInclusionTwist.projInclusionTwistIso A W U h hW hU n

/-- The restriction of the twist on the larger chart along the transition morphism, as a sheaf of
modules on the smaller chart. -/
public abbrev restrictedTwist (n : ℤ) :=
  (Scheme.Modules.restrictFunctor (projInclusionMap A W U h hW hU)).obj
    (twistingSheaf (A.grading U) n)

/-- The unit of the restriction--pushforward adjunction at the twist on the larger chart, pushed
forward along that chart. This is the **only** factor of the comparison which is not an
isomorphism of sheaves of modules: over an open lying in the inverse image of the smaller affine
open it becomes one, and nowhere else need it. -/
public def pushNestedUnit (n : ℤ) :
    (Scheme.Modules.pushforward ((relativeProj A).chart U hU)).obj
        (twistingSheaf (A.grading U) n) ⟶
      (Scheme.Modules.pushforward ((relativeProj A).chart U hU)).obj
        ((Scheme.Modules.pushforward (projInclusionMap A W U h hW hU)).obj
          (restrictedTwist A W U h hW hU n)) :=
  (Scheme.Modules.pushforward ((relativeProj A).chart U hU)).map
    ((Scheme.Modules.restrictAdjunction (projInclusionMap A W U h hW hU)).unit.app
      (twistingSheaf (A.grading U) n))

/-- The three remaining factors of the comparison, all isomorphisms: pseudofunctoriality of the
pushforward, the chart compatibility of the transition morphism, and Tag 01NO's twist
isomorphism.

It is an instantiation of `Stacks.AlgebraicGeometry.ChartTransRelativeProj.tailIso`, not an
anonymous `CategoryTheory.Iso.trans` of the three factors written out — although the two terms
are definitionally equal by one delta step. That is the one structural decision this definition
carries, and it is what makes
`Stacks.AlgebraicGeometry.ChartTransRelativeProj.pushNestedTail_hom_val_app` reachable. -/
public def pushNestedTail (n : ℤ) :
    (Scheme.Modules.pushforward ((relativeProj A).chart U hU)).obj
        ((Scheme.Modules.pushforward (projInclusionMap A W U h hW hU)).obj
          (restrictedTwist A W U h hW hU n)) ≅
      (Scheme.Modules.pushforward ((relativeProj A).chart W hW)).obj
        (twistingSheaf (A.grading W) n) :=
  tailIso (projInclusionMap A W U h hW hU) ((relativeProj A).chart U hU)
    ((relativeProj A).chart W hW) ((relativeProj A).chart_transition W U h hW hU)
    (restrictTwistIso A W U h hW hU n)

/-- **The action of the tail on a section**, which is the hypothesis of
`Stacks.AlgebraicGeometry.NestedCocycleReduction.pushNested_app_val_of`, discharged.

The three pushforward factors contribute a single restriction map, after which the tail acts as
Tag 01NO's chart-level comparison read over the preimage of the open in the chart of the smaller
affine open. The inclusion of opens is a free argument.

The proof instantiates
`Stacks.AlgebraicGeometry.ChartTransRelativeProj.tailIso_hom_val_app_eq`, whose subject is a
variable, at `pushNestedTail`. No conversion is requested underneath the `val.app`: the
identification is discharged one level up, where it is a single delta step. -/
public theorem pushNestedTail_hom_val_app (n : ℤ) (V : (relativeProj A).scheme.Opens)
    (i : (relativeProj A).chart W hW ⁻¹ᵁ V ⟶
      projInclusionMap A W U h hW hU ⁻¹ᵁ ((relativeProj A).chart U hU ⁻¹ᵁ V))
    (y : ((Scheme.Modules.pushforward ((relativeProj A).chart U hU)).obj
      ((Scheme.Modules.pushforward (projInclusionMap A W U h hW hU)).obj
        (restrictedTwist A W U h hW hU n))).val.obj (op V)) :
    (pushNestedTail A W U h hW hU n).hom.val.app (op V) y =
      (restrictTwistIso A W U h hW hU n).hom.val.app
          (op ((relativeProj A).chart W hW ⁻¹ᵁ V))
        ((restrictedTwist A W U h hW hU n).val.map i.op y) :=
  tailIso_hom_val_app_eq (projInclusionMap A W U h hW hU) ((relativeProj A).chart U hU)
    ((relativeProj A).chart W hW) ((relativeProj A).chart_transition W U h hW hU)
    (restrictTwistIso A W U h hW hU n) (pushNestedTail A W U h hW hU n) rfl V i y

/-- **The nested twist comparison, pushed forward to the relative Proj.** A morphism of sheaves of
`𝒪`-modules on the relative Proj from the direct image of the twist on the larger chart to the
direct image of the twist on the smaller one. Being a morphism in the category of sheaves of
modules on the relative Proj, every component of it is automatically linear over the sections of
the structure sheaf there — which is the whole reason the comparison is built at this level rather
than section by section. -/
public def pushNested (n : ℤ) :
    (Scheme.Modules.pushforward ((relativeProj A).chart U hU)).obj
        (twistingSheaf (A.grading U) n) ⟶
      (Scheme.Modules.pushforward ((relativeProj A).chart W hW)).obj
        (twistingSheaf (A.grading W) n) :=
  pushNestedUnit A W U h hW hU n ≫ (pushNestedTail A W U h hW hU n).hom

/-- **Over an open lying in the inverse image of the smaller affine open, the unit factor is an
isomorphism.** Its component there is the restriction map between the preimage of the open in the
larger chart and the image of its preimage in the smaller one, and
`Stacks.AlgebraicGeometry.ChartTransRelativeProj.image_preimage_preimage_chart` says those two
opens are equal. -/
public theorem isIso_app_pushNestedUnit (n : ℤ) (V : (relativeProj A).scheme.Opens)
    (hV : V ≤ (relativeProj A).toBase ⁻¹ᵁ W) :
    IsIso ((pushNestedUnit A W U h hW hU n).app V) :=
  isIso_presheaf_map_of_eq (X := AlgebraicGeometry.Proj (A.grading U))
    (twistingSheaf (A.grading U) n)
    (image_preimage_preimage_chart A W U h hW hU V hV) _

/-- The comparison on sections, factored. Proved by *applying*
`AlgebraicGeometry.Scheme.Modules.Hom.comp_app`, never by `rfl` at this instance: `rfl` here
exhausts the recursion budget on the pushforward terms, while instantiating the general lemma
substitutes for its variables and demands no reduction. -/
public theorem pushNested_app (n : ℤ) (V : (relativeProj A).scheme.Opens) :
    (pushNested A W U h hW hU n).app V
      = (pushNestedUnit A W U h hW hU n).app V
        ≫ (pushNestedTail A W U h hW hU n).hom.app V :=
  Scheme.Modules.Hom.comp_app _ _

/-- **The comparison is an isomorphism on the sections over any open lying in the inverse image of
the smaller affine open.** The three tail factors are isomorphisms of sheaves of modules
outright; the unit factor becomes one exactly there. -/
public theorem isIso_app_pushNested (n : ℤ) (V : (relativeProj A).scheme.Opens)
    (hV : V ≤ (relativeProj A).toBase ⁻¹ᵁ W) :
    IsIso ((pushNested A W U h hW hU n).app V) := by
  have := isIso_app_pushNestedUnit A W U h hW hU n V hV
  rw [pushNested_app]
  infer_instance

/-- The comparison is bijective on the sections over an open lying in the inverse image of the
smaller affine open. -/
public theorem bijective_pushNested (n : ℤ) (V : (relativeProj A).scheme.Opens)
    (hV : V ≤ (relativeProj A).toBase ⁻¹ᵁ W) :
    Function.Bijective ((pushNested A W U h hW hU n).val.app (op V)).hom :=
  have := isIso_app_pushNested A W U h hW hU n V hV
  bijective_val_app_of_isIso (pushNested A W U h hW hU n) V

/-- **Tag 01NO's twist comparison for a nested pair of affine opens, on sections.** For affine
opens `W ⊆ U` of the base and an integer `n`, an isomorphism of `𝒪(V)`-modules between the
sections over `V` of the direct image of the `n`-th twist on the chart of `U` and those of the
direct image of the `n`-th twist on the chart of `W`, for every open `V` of the relative Proj
contained in the inverse image of `W`, compatible with every restriction map.

This is the shape `Stacks.AlgebraicGeometry.ChartTransNonNested.ModelData.cmp` and
`modelTrans` ask for, at a **nested** pair. Linearity over the structure sheaf of the relative
Proj and compatibility with restriction are not proved by hand: the comparison is a morphism in
the category of sheaves of modules on the relative Proj, so both are its own naturality, and the
only thing proved by hand is that it is bijective on the sections in question. -/
public def cmpNested (n : ℤ) :
    TopCat.Sheaf.LocalModuleEquiv
      (pushforwardVal ((relativeProj A).chart U hU) (twistingSheaf (A.grading U) n))
      (pushforwardVal ((relativeProj A).chart W hW) (twistingSheaf (A.grading W) n))
      ((relativeProj A).toBase ⁻¹ᵁ W) :=
  localModuleEquivOfBijective (pushNested A W U h hW hU n).val
    ((relativeProj A).toBase ⁻¹ᵁ W) (bijective_pushNested A W U h hW hU n)

/-- On sections, the nested comparison `cmpNested` acts as the morphism `pushNested`. -/
@[simp]
public theorem cmpNested_app (n : ℤ) (V : (relativeProj A).scheme.Opens)
    (hV : V ≤ (relativeProj A).toBase ⁻¹ᵁ W)
    (s : (pushforwardVal ((relativeProj A).chart U hU)
      (twistingSheaf (A.grading U) n)).obj (op V)) :
    (cmpNested A W U h hW hU n).app V hV s = (pushNested A W U h hW hU n).val.app (op V) s :=
  localModuleEquivOfBijective_app _ _ _ V hV s

end Nested

/-! ### The remaining obligation: the nested cocycle -/

/-- **The nested cocycle for Tag 01NO's twist comparison, in one integer degree.** For affine
opens `W ⊆ W' ⊆ U` of the base, the comparison of the chart of `U` with the chart of `W` is the
comparison with the chart of `W'` followed by the comparison of the chart of `W'` with that of
`W`, on the sections over every open of the relative Proj lying in the inverse image of `W`.

The degree is a **parameter**, not quantified: everything built from this hypothesis below —
`cmpGen`, `cmpGen_comp`, `modelData`, `gluedTwist`, `chartIso` — is already per-degree, and the
twist `𝒪(1)` that Tag 01VM and the first condition of Tag 01W8 ask for needs the hypothesis in
the single degree `n = 1`. Quantifying over all degrees would make every one of those
constructions conditional on degrees it does not use.

This is the **one** mathematical statement the construction below is conditional on, and it is
not proved here. It is the identity which
`Stacks.AlgebraicGeometry.RelativeTwistRigidity.eq_id_res` is designed to deliver, applied to
the composite of one leg with the inverse of the other: that composite is an endomorphism family
of the twists on the chart of `W`, it fixes the restricted homogeneous global sections by
`Stacks.AlgebraicGeometry.ProjInclusionDegreeSection.composite_degreeSection`, and what is
missing is the remaining hypothesis of the rigidity theorem —
`Stacks.AlgebraicGeometry.TwistRigidity.IsMultiplicative` for that composite.

Every containment proof it mentions is a **free argument**, deliberately: a statement that
derived `W ≤ U` from `W ≤ W'` and `W' ≤ U` would be definitionally equal to this one by proof
irrelevance, but every use of it would make the elaborator check that equality underneath the
pushforward terms, and that is what exhausts the budget.

The conclusion is spelled with
`Stacks.AlgebraicGeometry.ChartTransRelativeProj.IsComposite`, which unfolds to exactly the
equation `(cmpNested A W W' ·).app V hV ((cmpNested A W' U ·).app V hV' s) = (cmpNested A W U
·).app V hV s`. That is not cosmetic: the equation written out at this instance
cannot be matched against the same equation produced by instantiating a generic lemma, so a
consumer of this hypothesis spelled the first way cannot use it at all. -/
public def IsNestedCocycle (n : ℤ) : Prop :=
  ∀ (W W' U : S.Opens) (hWW' : W ≤ W') (hW'U : W' ≤ U) (hWU : W ≤ U)
    (hW : IsAffineOpen W) (hW' : IsAffineOpen W') (hU : IsAffineOpen U)
    (V : (relativeProj A).scheme.Opens) (hV : V ≤ (relativeProj A).toBase ⁻¹ᵁ W)
    (hV' : V ≤ (relativeProj A).toBase ⁻¹ᵁ W'),
    IsComposite (cmpNested A W' U hW'U hW' hU n) (cmpNested A W W' hWW' hW hW' n)
      (cmpNested A W U hWU hW hU n) V hV hV'

/-! ### From nested pairs to pairs with nested inverse images -/

/-- The pushforward of a twist along a chart is a sheaf. -/
public theorem isSheaf_pushChart (W : S.Opens) (hW : IsAffineOpen W) (n : ℤ) :
    CategoryTheory.Presheaf.IsSheaf (Opens.grothendieckTopology (relativeProj A).scheme)
      (pushforwardVal ((relativeProj A).chart W hW)
        (twistingSheaf (A.grading W) n)).presheaf :=
  ((Scheme.Modules.pushforward ((relativeProj A).chart W hW)).obj
    (twistingSheaf (A.grading W) n)).isSheaf

/-- **The inverse image of an open of the base is covered by the inverse images of the affine
opens contained in it.** This is the only covering statement the glueing below uses, and it is
about the affine opens of the *base*: the inverse images of the affine opens are not a basis of
the topology of the relative Proj. -/
public theorem le_iSup_preimage_affine_le (T : S.Opens) :
    (relativeProj A).toBase ⁻¹ᵁ T
      ≤ ⨆ m : {m : S.affineOpens // (m.1 : S.Opens) ≤ T},
          (relativeProj A).toBase ⁻¹ᵁ (m.1.1 : S.Opens) := by
  intro x hx
  obtain ⟨m, hmmem, hxm, hmT⟩ :=
    Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens
      (show (relativeProj A).toBase x ∈ T from hx)
  exact Opens.mem_iSup.mpr ⟨⟨⟨m, hmmem⟩, fun _ hy => hmT hy⟩, hxm⟩

section Glue

variable (W U : S.Opens) (hW : IsAffineOpen W) (hU : IsAffineOpen U) (n : ℤ)

/-- The affine opens of the base contained in both of two opens: the index of the family the
comparison for a pair with nested inverse images is glued over. -/
public abbrev meetIndex : Type u := {m : S.affineOpens // (m.1 : S.Opens) ≤ W ⊓ U}

/-- The comparison over the inverse image of a member of that family: both charts are compared
with the member's own chart, which is a **nested** comparison on each side. -/
public def meetLoc (m : meetIndex W U) :
    TopCat.Sheaf.LocalModuleEquiv
      (pushforwardVal ((relativeProj A).chart U hU) (twistingSheaf (A.grading U) n))
      (pushforwardVal ((relativeProj A).chart W hW) (twistingSheaf (A.grading W) n))
      ((relativeProj A).toBase ⁻¹ᵁ (m.1.1 : S.Opens)) :=
  modelPair (cmpNested A (m.1.1 : S.Opens) U (m.2.trans inf_le_right) m.1.2 hU n)
    (cmpNested A (m.1.1 : S.Opens) W (m.2.trans inf_le_left) m.1.2 hW n)

/-- The members of the family cover the inverse image of the smaller open. This is where the
hypothesis that the two inverse images are nested is used — and the only place. -/
public theorem le_iSup_preimage_meetIndex
    (hpre : (relativeProj A).toBase ⁻¹ᵁ W ≤ (relativeProj A).toBase ⁻¹ᵁ U) :
    (relativeProj A).toBase ⁻¹ᵁ W
      ≤ ⨆ m : meetIndex W U, (relativeProj A).toBase ⁻¹ᵁ (m.1.1 : S.Opens) := by
  refine le_trans (fun x hx => ?_) (le_iSup_preimage_affine_le A (W ⊓ U))
  exact ⟨hx, hpre hx⟩

/-- **The affine opens of the base below two given opens cover any open inside both inverse
images.** -/
public theorem le_iSup_preimage_inf (P Q : S.Opens) (V : (relativeProj A).scheme.Opens)
    (hP : V ≤ (relativeProj A).toBase ⁻¹ᵁ P) (hQ : V ≤ (relativeProj A).toBase ⁻¹ᵁ Q) :
    V ≤ ⨆ r : {r : S.affineOpens // (r.1 : S.Opens) ≤ P ⊓ Q},
        (relativeProj A).toBase ⁻¹ᵁ (r.1.1 : S.Opens) := by
  refine le_trans (fun x hx => ?_) (le_iSup_preimage_affine_le A (P ⊓ Q))
  exact ⟨hP hx, hQ hx⟩

/-- The same for three opens of the base, which is what the cocycle for the glued comparison
needs. -/
public theorem le_iSup_preimage_inf₃ (P Q R : S.Opens) (V : (relativeProj A).scheme.Opens)
    (hP : V ≤ (relativeProj A).toBase ⁻¹ᵁ P) (hQ : V ≤ (relativeProj A).toBase ⁻¹ᵁ Q)
    (hR : V ≤ (relativeProj A).toBase ⁻¹ᵁ R) :
    V ≤ ⨆ r : {r : S.affineOpens // (r.1 : S.Opens) ≤ P ⊓ Q ⊓ R},
        (relativeProj A).toBase ⁻¹ᵁ (r.1.1 : S.Opens) := by
  refine le_trans (fun x hx => ?_) (le_iSup_preimage_affine_le A (P ⊓ Q ⊓ R))
  exact ⟨⟨hP hx, hQ hx⟩, hR hx⟩

/-- **`meetLoc` is the cancellation of two nested comparisons**, with the two containments in the
base supplied freely. This is the only statement in the file that identifies `meetLoc` with a
`modelPair`, and it is stated at the level of the local isomorphisms, never on sections: at the
level of the isomorphisms the identification is one delta step, while underneath an `app` it
drives the elaborator into the pushforward of the twist. -/
public theorem meetLoc_eq (m : meetIndex W U) (hmW : (m.1.1 : S.Opens) ≤ W)
    (hmU : (m.1.1 : S.Opens) ≤ U) :
    meetLoc A W U hW hU n m
      = modelPair (cmpNested A (m.1.1 : S.Opens) U hmU m.1.2 hU n)
          (cmpNested A (m.1.1 : S.Opens) W hmW m.1.2 hW n) :=
  rfl

/-- **The defining property of `meetLoc`:** following it with the member's comparison of the chart
of the smaller open recovers the member's comparison of the chart of the larger one, the member's
own chart cancelling. The equation of local isomorphisms is transported under `app` by `congrArg`,
which is why `meetLoc_eq` is stated where it is. -/
public theorem isComposite_meetLoc (m : meetIndex W U) (hmW : (m.1.1 : S.Opens) ≤ W)
    (hmU : (m.1.1 : S.Opens) ≤ U) (V : (relativeProj A).scheme.Opens)
    (hV : V ≤ (relativeProj A).toBase ⁻¹ᵁ (m.1.1 : S.Opens)) :
    IsComposite (meetLoc A W U hW hU n m) (cmpNested A (m.1.1 : S.Opens) W hmW m.1.2 hW n)
      (cmpNested A (m.1.1 : S.Opens) U hmU m.1.2 hU n) V hV hV :=
  cast (congrArg (fun e : TopCat.Sheaf.LocalModuleEquiv
          (pushforwardVal ((relativeProj A).chart U hU) (twistingSheaf (A.grading U) n))
          (pushforwardVal ((relativeProj A).chart W hW) (twistingSheaf (A.grading W) n))
          ((relativeProj A).toBase ⁻¹ᵁ (m.1.1 : S.Opens)) =>
        IsComposite e (cmpNested A (m.1.1 : S.Opens) W hmW m.1.2 hW n)
          (cmpNested A (m.1.1 : S.Opens) U hmU m.1.2 hU n) V hV hV)
      (meetLoc_eq A W U hW hU n m hmW hmU)).symm
    (isComposite_modelPair (cmpNested A (m.1.1 : S.Opens) U hmU m.1.2 hU n)
      (cmpNested A (m.1.1 : S.Opens) W hmW m.1.2 hW n) V hV)

/-- **Shrinking the member does not change the comparison**, over an open inside the inverse image
of the smaller member. This is the one place the nested cocycle is consumed, and it is consumed
twice: once along the chain `k ⊆ m ⊆ U` and once along `k ⊆ m ⊆ W`. -/
public theorem meetLoc_agreeOn_of_le (hcoc : IsNestedCocycle A n) (m k : meetIndex W U)
    (hmW : (m.1.1 : S.Opens) ≤ W) (hmU : (m.1.1 : S.Opens) ≤ U) (hkW : (k.1.1 : S.Opens) ≤ W)
    (hkU : (k.1.1 : S.Opens) ≤ U) (hkm : (k.1.1 : S.Opens) ≤ (m.1.1 : S.Opens))
    (V : (relativeProj A).scheme.Opens)
    (hVm : V ≤ (relativeProj A).toBase ⁻¹ᵁ (m.1.1 : S.Opens))
    (hVk : V ≤ (relativeProj A).toBase ⁻¹ᵁ (k.1.1 : S.Opens)) :
    AgreeOn (meetLoc A W U hW hU n m) (meetLoc A W U hW hU n k) V hVm hVk :=
  agreeOn_of_model (meetLoc A W U hW hU n k) (meetLoc A W U hW hU n m)
    (cmpNested A (k.1.1 : S.Opens) U hkU k.1.2 hU n)
    (cmpNested A (k.1.1 : S.Opens) W hkW k.1.2 hW n)
    (cmpNested A (m.1.1 : S.Opens) U hmU m.1.2 hU n)
    (cmpNested A (m.1.1 : S.Opens) W hmW m.1.2 hW n)
    (cmpNested A (k.1.1 : S.Opens) (m.1.1 : S.Opens) hkm k.1.2 m.1.2 n) V hVk hVm
    (isComposite_meetLoc A W U hW hU n k hkW hkU V hVk)
    (isComposite_meetLoc A W U hW hU n m hmW hmU V hVm)
    (hcoc (k.1.1 : S.Opens) (m.1.1 : S.Opens) U hkm hmU hkU k.1.2 m.1.2 hU V hVk hVm)
    (hcoc (k.1.1 : S.Opens) (m.1.1 : S.Opens) W hkm hmW hkW k.1.2 m.1.2 hW V hVk hVm)

/-- **The comparisons over two members of the family agree on any open inside both inverse
images.** The two members need not be nested, and their meet need not be affine; what is used is
that the affine opens of the base below the meet cover it, and that over the inverse image of such
an affine open both comparisons are that open's own comparison. -/
public theorem meetLoc_agreeOn (hcoc : IsNestedCocycle A n) (m m' : meetIndex W U)
    (V : (relativeProj A).scheme.Opens)
    (hVm : V ≤ (relativeProj A).toBase ⁻¹ᵁ (m.1.1 : S.Opens))
    (hVm' : V ≤ (relativeProj A).toBase ⁻¹ᵁ (m'.1.1 : S.Opens)) :
    AgreeOn (meetLoc A W U hW hU n m) (meetLoc A W U hW hU n m') V hVm hVm' := by
  have key : ∀ (q : meetIndex W U) (r : meetIndex W U) (hrq : (r.1.1 : S.Opens) ≤ q.1.1)
      (V' : (relativeProj A).scheme.Opens)
      (hV'q : V' ≤ (relativeProj A).toBase ⁻¹ᵁ (q.1.1 : S.Opens))
      (hV'r : V' ≤ (relativeProj A).toBase ⁻¹ᵁ (r.1.1 : S.Opens)),
      AgreeOn (meetLoc A W U hW hU n q) (meetLoc A W U hW hU n r) V' hV'q hV'r :=
    fun q r hrq V' hV'q hV'r =>
      meetLoc_agreeOn_of_le A W U hW hU n hcoc q r (q.2.trans inf_le_left)
        (q.2.trans inf_le_right) (hrq.trans (q.2.trans inf_le_left))
        (hrq.trans (q.2.trans inf_le_right)) hrq V' hV'q hV'r
  exact agreeOn_of_cover (isSheaf_pushChart A W hW n) (meetLoc A W U hW hU n m)
    (meetLoc A W U hW hU n m')
    (fun r : {r : S.affineOpens // (r.1 : S.Opens) ≤ (m.1.1 : S.Opens) ⊓ (m'.1.1 : S.Opens)} =>
      (relativeProj A).toBase ⁻¹ᵁ (r.1.1 : S.Opens))
    (fun r V' hV'm hV'm' hV'r s' =>
      (key m ⟨r.1, (r.2.trans inf_le_left).trans m.2⟩ (r.2.trans inf_le_left) V' hV'm hV'r s').trans
        (key m' ⟨r.1, (r.2.trans inf_le_left).trans m.2⟩ (r.2.trans inf_le_right) V' hV'm' hV'r
          s').symm)
    V hVm hVm' (le_iSup_preimage_inf A (m.1.1 : S.Opens) (m'.1.1 : S.Opens) V hVm hVm')

/-- **Tag 01NO's twist comparison for a pair of affine opens of the base whose inverse images are
nested, on sections.** This, and not `cmpNested`, is the field
`Stacks.AlgebraicGeometry.ChartTransNonNested.ModelData.cmp` asks for: the hypothesis available
there is `toBase ⁻¹ᵁ W ≤ toBase ⁻¹ᵁ U`, which is strictly weaker than `W ≤ U` because the
structure morphism of a relative Proj need not be surjective.

It is glued from `meetLoc` over the affine opens of the base below both, which cover the inverse
image of `W` exactly under that hypothesis. -/
public def cmpGen (hpre : (relativeProj A).toBase ⁻¹ᵁ W ≤ (relativeProj A).toBase ⁻¹ᵁ U)
    (hcoc : IsNestedCocycle A n) :
    TopCat.Sheaf.LocalModuleEquiv
      (pushforwardVal ((relativeProj A).chart U hU) (twistingSheaf (A.grading U) n))
      (pushforwardVal ((relativeProj A).chart W hW) (twistingSheaf (A.grading W) n))
      ((relativeProj A).toBase ⁻¹ᵁ W) :=
  TopCat.Sheaf.LocalModuleEquiv.glueLE (isSheaf_pushChart A U hU n)
    (isSheaf_pushChart A W hW n) (meetLoc A W U hW hU n)
    (meetLoc_agreeOn A W U hW hU n hcoc) (le_iSup_preimage_meetIndex A W U hpre)

/-- Over an open inside the inverse image of an affine open of the base below both, the glued
comparison is that open's own comparison. This is the only computational handle on `cmpGen`. -/
public theorem cmpGen_agreeOn_meetLoc
    (hpre : (relativeProj A).toBase ⁻¹ᵁ W ≤ (relativeProj A).toBase ⁻¹ᵁ U)
    (hcoc : IsNestedCocycle A n) (p : S.affineOpens) (hpW : (p.1 : S.Opens) ≤ W)
    (hpU : (p.1 : S.Opens) ≤ U) (V : (relativeProj A).scheme.Opens)
    (hVW : V ≤ (relativeProj A).toBase ⁻¹ᵁ W)
    (hVp : V ≤ (relativeProj A).toBase ⁻¹ᵁ (p.1 : S.Opens)) :
    AgreeOn (cmpGen A W U hW hU n hpre hcoc) (meetLoc A W U hW hU n ⟨p, le_inf hpW hpU⟩)
      V hVW hVp :=
  fun s => TopCat.Sheaf.LocalModuleEquiv.glueLE_app_of_le (isSheaf_pushChart A U hU n)
    (isSheaf_pushChart A W hW n) (meetLoc A W U hW hU n)
    (meetLoc_agreeOn A W U hW hU n hcoc) (le_iSup_preimage_meetIndex A W U hpre)
    (i := ⟨p, le_inf hpW hpU⟩) hVW hVp s

end Glue

/-! ### The cocycle for the glued comparison, and the chart data -/

/-- Over an open inside the inverse image of an affine open `p` of the base below both, the glued
comparison followed by the comparison of `p`'s chart with the target is the comparison of `p`'s
chart with the source. -/
private theorem isComposite_cmpGen (W U : S.Opens) (hW : IsAffineOpen W) (hU : IsAffineOpen U)
    (n : ℤ) (hpre : (relativeProj A).toBase ⁻¹ᵁ W ≤ (relativeProj A).toBase ⁻¹ᵁ U)
    (hcoc : IsNestedCocycle A n) (p : S.affineOpens) (hpW : (p.1 : S.Opens) ≤ W)
    (hpU : (p.1 : S.Opens) ≤ U) (V : (relativeProj A).scheme.Opens)
    (hVW : V ≤ (relativeProj A).toBase ⁻¹ᵁ W)
    (hVp : V ≤ (relativeProj A).toBase ⁻¹ᵁ (p.1 : S.Opens)) :
    IsComposite (cmpGen A W U hW hU n hpre hcoc) (cmpNested A (p.1 : S.Opens) W hpW p.2 hW n)
      (cmpNested A (p.1 : S.Opens) U hpU p.2 hU n) V hVp hVW :=
  isComposite_of_agreeOn _ (meetLoc A W U hW hU n ⟨p, le_inf hpW hpU⟩) _ _ V hVp hVW hVp
    (cmpGen_agreeOn_meetLoc A W U hW hU n hpre hcoc p hpW hpU V hVW hVp)
    (isComposite_meetLoc A W U hW hU n ⟨p, le_inf hpW hpU⟩ hpW hpU V hVp)

/-- **The glued comparisons compose along a chain of three affine opens of the base whose inverse
images are nested.** This is exactly
`Stacks.AlgebraicGeometry.ChartTransNonNested.ModelData.cmp_modelTrans` at the refinement by the
inverse images of the affine opens of the base, and it needs no hypothesis beyond
`IsNestedCocycle`.

Checked on a cover of the open by the inverse images of the affine opens of the base below all
three: over such a member each glued comparison is that member's own comparison through the
member's own chart, and three comparisons through one model compose for free. -/
public theorem cmpGen_comp (n : ℤ) (hcoc : IsNestedCocycle A n) (W W' U : S.Opens)
    (hW : IsAffineOpen W) (hW' : IsAffineOpen W') (hU : IsAffineOpen U)
    (hWW' : (relativeProj A).toBase ⁻¹ᵁ W ≤ (relativeProj A).toBase ⁻¹ᵁ W')
    (hW'U : (relativeProj A).toBase ⁻¹ᵁ W' ≤ (relativeProj A).toBase ⁻¹ᵁ U)
    (hWU : (relativeProj A).toBase ⁻¹ᵁ W ≤ (relativeProj A).toBase ⁻¹ᵁ U)
    (V : (relativeProj A).scheme.Opens) (hV : V ≤ (relativeProj A).toBase ⁻¹ᵁ W)
    (hV' : V ≤ (relativeProj A).toBase ⁻¹ᵁ W') :
    IsComposite (cmpGen A W' U hW' hU n hW'U hcoc) (cmpGen A W W' hW hW' n hWW' hcoc)
      (cmpGen A W U hW hU n hWU hcoc) V hV hV' := by
  refine isComposite_of_cover (isSheaf_pushChart A W hW n) (cmpGen A W' U hW' hU n hW'U hcoc)
    (cmpGen A W W' hW hW' n hWW' hcoc) (cmpGen A W U hW hU n hWU hcoc)
    (fun r : {r : S.affineOpens // (r.1 : S.Opens) ≤ W ⊓ W' ⊓ U} =>
      (relativeProj A).toBase ⁻¹ᵁ (r.1.1 : S.Opens))
    (fun r V₀ hV₀ hV₁ hV₀r => ?_) V hV hV'
    (le_iSup_preimage_inf₃ A W W' U V hV hV' (hV'.trans hW'U))
  have hrW : (r.1.1 : S.Opens) ≤ W := r.2.trans (inf_le_left.trans inf_le_left)
  have hrW' : (r.1.1 : S.Opens) ≤ W' := r.2.trans (inf_le_left.trans inf_le_right)
  have hrU : (r.1.1 : S.Opens) ≤ U := r.2.trans inf_le_right
  exact isComposite_of_model (cmpGen A W' U hW' hU n hW'U hcoc)
    (cmpGen A W W' hW hW' n hWW' hcoc) (cmpGen A W U hW hU n hWU hcoc)
    (cmpNested A (r.1.1 : S.Opens) U hrU r.1.2 hU n)
    (cmpNested A (r.1.1 : S.Opens) W' hrW' r.1.2 hW' n)
    (cmpNested A (r.1.1 : S.Opens) W hrW r.1.2 hW n) V₀ hV₀ hV₁ hV₀r
    (isComposite_cmpGen A W' U hW' hU n hW'U hcoc r.1 hrW' hrU V₀ hV₁ hV₀r)
    (isComposite_cmpGen A W W' hW hW' n hWW' hcoc r.1 hrW hrW' V₀ hV₀ hV₀r)
    (isComposite_cmpGen A W U hW hU n hWU hcoc r.1 hrW hrU V₀ hV₀ hV₀r)


/-- **The chart data of a relative projective spectrum, presented by local models**, in a fixed
integer degree and conditional on the nested cocycle.

The charts are the projective spectra of the graded rings of sections over the affine opens of the
base, each carrying its absolute twist; the refinement is the family of inverse images of those
affine opens, which refines every chart open and every pairwise meet of its own members
(`Stacks.AlgebraicGeometry.ChartTransNonNested.isRefinedBy_preimage_affineOpens`); the model over
a member is the pushforward of that member's own twist; the identification of a chart module with
the model is `cmpGen`, and the model transition is `cmpGen` again. The only field with
mathematical content, `cmp_modelTrans`, is `cmpGen_comp`.

`Stacks.AlgebraicGeometry.ChartTransNonNested.ModelData.toChartGlueData` then produces the glueing
datum, so the glued sheaf of modules and the chart identification exist as soon as
`IsNestedCocycle` does. -/
public def modelData (n : ℤ) (hcoc : IsNestedCocycle A n) :
    ModelData (relativeProj A).scheme
      (fun i : S.affineOpens => (relativeProj A).toBase ⁻¹ᵁ (i.1 : S.Opens)) where
  chart i := AlgebraicGeometry.Proj (A.grading (i.1 : S.Opens))
  hom i := (relativeProj A).chart (i.1 : S.Opens) i.2
  sheaf i := twistingSheaf (A.grading (i.1 : S.Opens)) n
  κ := S.affineOpens
  L k := (relativeProj A).toBase ⁻¹ᵁ (k.1 : S.Opens)
  isRefinedBy_chartOpen i :=
    isRefinedBy_preimage_affineOpens (relativeProj A).toBase (i.1 : S.Opens)
  isRefinedBy_inf k k' := isRefinedBy_inf_preimage_affineOpens (relativeProj A).toBase k k'
  model k := pushforwardVal ((relativeProj A).chart (k.1 : S.Opens) k.2)
    (twistingSheaf (A.grading (k.1 : S.Opens)) n)
  cmp k i hi := cmpGen A (k.1 : S.Opens) (i.1 : S.Opens) k.2 i.2 n hi hcoc
  modelTrans k k' hkk' := cmpGen A (k.1 : S.Opens) (k'.1 : S.Opens) k.2 k'.2 n hkk' hcoc
  cmp_modelTrans k k' hkk' i hi V hV :=
    cmpGen_comp A n hcoc (k.1 : S.Opens) (k'.1 : S.Opens) (i.1 : S.Opens) k.2 k'.2 i.2 hkk' hi
      (hkk'.trans hi) V hV (hV.trans hkk')

/-- **The glued twist on the relative projective spectrum**, in a fixed integer degree,
conditional on the nested cocycle. -/
public def gluedTwist (n : ℤ) (hcoc : IsNestedCocycle A n) : (relativeProj A).scheme.Modules :=
  (modelData A n hcoc).glued

/-- **The chart identification of the glued twist.** The restriction of the glued twist along the
chart over an affine open of the base is isomorphic, as a sheaf of modules on that chart, to the
absolute twist the chart carried.

This is what `Stacks.AlgebraicGeometry.RelativeProjTwists.ChartData.chartIso` asserts in degree
`n`. It is **not** a `ChartData`: that asks for the chart identifications of a single graded
algebra on the relative Proj, and neither the multiplication nor the unit of that algebra is
constructed here.

Both the source and the target are spelled through `modelData`'s own fields rather than through
`gluedTwist` and `twistingSheaf`: with the latter spelling the kernel rejects the `hi` argument,
which is the same phenomenon as the `cmp_modelTrans` measurement in the implementation notes. -/
public def chartIso (n : ℤ) (hcoc : IsNestedCocycle A n) (i : S.affineOpens)
    [hchart : IsOpenImmersion ((modelData A n hcoc).hom i)] :
    Scheme.Modules.restrict (modelData A n hcoc).glued ((modelData A n hcoc).hom i)
      ≅ (modelData A n hcoc).sheaf i :=
  ModelData.chartIso (modelData A n hcoc) i (hom_isOpenImmersion := hchart)
    (RelativeProjTwistGlue.chart_image_top (relativeProj A) (i.1 : S.Opens) i.2).le

end Stacks.AlgebraicGeometry.ChartTransRelativeProj

end
