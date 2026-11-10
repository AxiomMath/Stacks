module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposTwoMorphismModules
public import StacksFrontier.AlgebraicGeometry.Stacks.MorphismSpaceInduced
public import StacksFrontier.AlgebraicGeometry.Stacks.RestrictionCommutationRingedTopoi
public import StacksFrontier.AlgebraicGeometry.Stacks.RestrictionDirectImageComparisonIso
public import StacksFrontier.AlgebraicGeometry.Stacks.RestrictionProjectionExactness
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.Composition
public import
StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.CompositionOfToposHomUnconditional

/-!
# The derived direct image of a morphism representable by algebraic spaces, restricted

Let `S` be a scheme in a big fppf site and let `f : 𝒳 ⥤ 𝒴` be a 1-morphism of categories fibred
in groupoids over `(Sch/S)_{fppf}`, with `𝒳` representable by an algebraic space `F` and `𝒴` by
an algebraic space `G`, and write `f : F ⟶ G` for the induced morphism of algebraic spaces.
Stacks 075N asserts, for a complex `ℱ` of `𝒪_𝒳`-modules, the identity

`(Rf_*ℱ)|_{G_étale} = Rf_{small,*}(ℱ|_{F_étale})`

in `D(𝒪_G)`, where `(-)|_{F_étale}` and `(-)|_{G_étale}` are the restrictions to the small étale
sites of Stacks 073M. This file states and proves it, from the square of Stacks 073N and the
composition law for total direct images of Stacks 0D6E, in the forms in which this development
has them.

The argument is the source's. The square of Stacks 073N says that `π_G ∘ f` and `f_small ∘ π_F`
are 2-isomorphic morphisms of ringed topoi; Stacks 0D6E factors the total direct image of each
composite through its two factors; so `Rf_* ⋙ Rπ_{G,*}` and `Rπ_{F,*} ⋙ Rf_{small,*}` are right
derived functors of one and the same degreewise functor, hence isomorphic. The restrictions
`π_{F,*}` and `π_{G,*}` are exact, so their total right derived functors are the degreewise
ones, and the display above is what the isomorphism says.

## Main definitions

* `AlgebraicGeometry.RingedToposHom.PreservesKInjectiveModules`: Stacks 093Y as a property of a
  morphism of ringed topoi — degreewise direct image preserves K-injectivity.
* `AlgebraicGeometry.RingedToposHom.PushforwardComputesDerived`: the weaker condition that the
  composition criterion below actually consumes — the unit of `Rg` is invertible at the
  degreewise direct image along `f` of every K-injective complex.
* `AlgebraicGeometry.RingedToposHom.derivedPushforwardOfExact` and
  `AlgebraicGeometry.RingedToposHom.derivedPushforwardOfExactUnit`: for an exact degreewise
  direct image, the functor it induces on unbounded derived categories, and the canonical
  isomorphism exhibiting it as a right derived functor.
* `AlgebraicGeometry.RingedToposHom.TwoIso.pushforwardToDerivedCategoryIso`: a 2-isomorphism of
  morphisms of ringed topoi induces an isomorphism of the degreewise direct images of complexes
  of modules, read into the derived category of the target.
* `AlgebraicGeometry.RingedToposHom.twoLegsComparison` and
  `AlgebraicGeometry.RingedToposHom.twoLegsIso`: the canonical comparison of the two derived
  composites of a 2-commutative square of ringed topoi, and the isomorphism it is.
* `AlgebraicGeometry.Space.inducedAlgebraicSpacesHom`: the source's "induced morphism of
  algebraic spaces" `F ⟶ G`, at the spelling the statement below needs — so that it is derived
  from the 1-morphism and the two presentations rather than carried as a parameter.
* `AlgebraicGeometry.Space.restrictionRingedSquareInducedAlgebraicSpaces`: **Stacks 073N** at
  the induced morphism of algebraic spaces, in the spelling the statement below needs.
* `AlgebraicGeometry.Space.restrictedDerivedDirectImageIso`: **Stacks 075N**, clause (2), the
  display above as an isomorphism of functors `D(𝒪_𝒳) ⥤ D(𝒪_G)`. The tag itself sits on
  `AlgebraicGeometry.Space.restrictedDerivedDirectImageIsoClauses`, which asserts this clause
  together with clause (1) for abelian sheaves.

## Main results

* `Stacks.Cohomology.UnboundedComplexes.isRightDerivedFunctor_comp_of_isIso`: a right derived
  functor of a functor is a right derived functor of any isomorphic functor.
* `AlgebraicGeometry.RingedToposHom.isRightDerivedFunctor_comp_of_isGrothendieckAbelian`:
  Stacks 0D6E's criterion for `Rf_* ⋙ Rg_*`, with Grothendieck abelianness of the two
  categories of modules given directly rather than deduced from `UnivLE` between the site and
  section universes.
* `AlgebraicGeometry.RingedToposHom.isRightDerivedFunctor_derivedPushforwardOfExactUnit`: an
  exact degreewise direct image is its own total right derived functor, and
  `AlgebraicGeometry.RingedToposHom.isIso_derivedPushforwardOfExactUnit`: its unit is an
  isomorphism.
* `AlgebraicGeometry.RingedToposHom.pushforwardComputesDerived_of_preservesKInjectiveModules`
  and `AlgebraicGeometry.RingedToposHom.pushforwardComputesDerived_of_isIso`: the two ways to
  supply the condition the criterion consumes — Stacks 093Y for the first morphism, or an
  invertible unit for the second, which asks nothing of the first.
* `AlgebraicGeometry.RingedToposHom.isIso_twoLegsComparison`: the comparison of the two derived
  composites of a 2-commutative square of ringed topoi is invertible.
* `AlgebraicGeometry.Space.isIso_restrictedDerivedDirectImageComparison`: the same for the two
  legs of the square of Stacks 073N, for arbitrary right derived functors of the two
  restrictions. This is *not* Stacks 075N — the source's restrictions are underived — and
  carries no tag; `restrictedDerivedDirectImageIso` is clause (2) of the tag.

## Implementation notes

**What is proved.** Nothing beyond the source's own data — `S`, the 1-morphism, the two
presentations and the complex, together with the right derived direct images the display
presupposes — is a hypothesis of `restrictedDerivedDirectImageIso`. The morphism of algebraic
spaces is not one either: it is induced, as the source has it, and the paragraph below says how.

The 2-isomorphism of the two legs of the square, Stacks 073N itself, is
`AlgebraicGeometry.Space.restrictionRingedSquareInducedAlgebraicSpaces`:
`AlgebraicGeometry.Space.restrictionRingedSquareInduced` builds it from invertibility of the
canonical comparison map of equation 075M alone, and that invertibility is
`AlgebraicGeometry.Space.isIso_restrictedDirectImageComparison`. The paragraph "The square of
Stacks 073N" below says how the three goals that construction once left open were settled.

The condition that the composition criterion consumes
at the second leg `f_small ∘ π_F` — that the unit of `Rf_{small,*}` is invertible at the
degreewise restriction of every K-injective complex — is
`AlgebraicGeometry.Space.pushforwardComputesDerived_smallEtaleRingedToposHom`, with **no
hypothesis on `π_F`**. The paragraph "How the second leg is discharged" below says how, and why
this is the only way it can be done: in the shape Stacks 093Y would supply it, at module
coefficients, the condition is the statement Stacks 075L records as *false*, by Stacks 0758.

**The morphism of algebraic spaces is induced, not given.** Stacks 075N gives `S`, the
1-morphism `fStack`, the two presentations `eF`, `eG` and the complex, and then says "denote
`f : F ⟶ G` the induced morphism of algebraic spaces". Accordingly `fSpace` is **not** a
parameter of the statement below: every binder that mentions it — the derived direct image
`RfSpace`, its unit `αfSpace`, and the square `sq` — is stated at
`AlgebraicGeometry.Space.inducedAlgebraicSpacesHom`, which is
`AlgebraicGeometry.Space.inducedSpacesHom` for the two presentations and the verticality
`hfStack.comp_eq`. `AlgebraicGeometry.Space.eq_inducedSpacesHom_iff_forall_sectionOfObj`
characterises that term — it is the unique morphism of algebraic spaces carrying the section of
`F` named by each object `z` of `𝒳` to the section of `G` named by `fStack z` — and
`AlgebraicGeometry.Stack.morphismSpaceEquiv_eq_inducedSpaceMap` certifies that this is the
morphism the bijection of Stacks 04SW produces. The universe-free
`inducedSpacesHom` is what makes this possible: `morphismSpaceEquiv` ties the hom-universes of
`𝒳` and `𝒴` to that of the site, which 075N leaves free.

**The square of Stacks 073N.** Because `fSpace` is induced, the type of the 2-isomorphism
relates the given data instead of two independent parameters, and a construction of it is well
posed. Measuring `AlgebraicGeometry.Space.restrictionRingedSquareOfIsIso` at the induced
morphism leaves exactly three goals, and all three are theorems; the assembly is
`restrictionRingedSquareInducedAlgebraicSpaces` below, which is
`AlgebraicGeometry.Space.restrictionRingedSquareOfInduced`.

* *The compatibility of the 1-morphism with the morphism of algebraic spaces* — the hypothesis
  `ha` that `AlgebraicGeometry.Space.restrictedDirectImageComparison` carries for a free
  `fSpace`, namely
  `schemeChartFunctor B S hS F p eF ⋙ fStack ≅ CostructuredArrow.map fSpace.hom ⋙
  schemeChartFunctor B S hS G q eG`. For the **induced** morphism this is
  `AlgebraicGeometry.Space.schemeChartPostcompIso`: it is
  `AlgebraicGeometry.Space.restrictionFunctorPostcompIso` read at *all* scheme charts instead
  of the small étale sites, and so, unlike that declaration, it carries **no** `IsEtale`
  hypothesis on the induced morphism — postcomposition of scheme charts needs none. This was
  the obstruction that no amount of 073N could remove while `fSpace` was free.
* *Invertibility of the comparison of the two direct images*, equation 075M:
  `IsIso (restrictedDirectImageComparison …)`. This is
  `AlgebraicGeometry.Space.isIso_restrictedDirectImageComparison`, and it is what the source's
  proof of Stacks 073N spends its length on. It is settled chartwise: injectivity of the
  comparison on sections over an étale scheme chart `V` of `G` comes from the pushforward
  formula of Stacks 06W6 together with the chart correspondence of Stacks 03G8, and
  surjectivity by gluing the compatible family of canonical restrictions to the diagrams of
  étale scheme charts over `V` and recognizing the result through the covering of Properties of
  Spaces 03H7. So neither the identification of the 2-fibre product
  `(Sch/V)_{fppf} ×_𝒴 𝒳` with the split category fibred in groupoids of `V ×_G F` nor the
  comparison of the equalizer presentations of Stacks 03H7 against Stacks 03G2 has to be
  carried out in the form the source gives them.
* *The structure-sheaf compatibility* `hsq`: the comparison, precomposed with the structure map
  of `π_G` and the direct image under `π_G` of the structure map of `fStack`, is the structure
  map of `f_{small}` followed by the direct image under `f_{small}` of the structure map of
  `π_F`. This is
  `AlgebraicGeometry.Space.restrictedDirectImageComparison_structureSheafCompatible`: the three
  structure-sheaf identifications of the square are computed on sections there, its verticality
  input being `AlgebraicGeometry.Space.isHomLift_schemeChartPostcompIso_hom_app`.

The three live in
`StacksFrontier/AlgebraicGeometry/Stacks/RestrictionDirectImageComparison.lean` and
`StacksFrontier/AlgebraicGeometry/Stacks/RestrictionDirectImageComparisonIso.lean`, the latter of
which this file imports.

**How the second leg is discharged.** The condition the composition criterion consumes at
`f_small ∘ π_F` is `AlgebraicGeometry.RingedToposHom.PushforwardComputesDerived π_F f_small`,
and `pushforwardComputesDerived_smallEtaleRingedToposHom` below supplies it from
`Stacks.Cohomology.DerivedPushforwardCompositionOfToposHom`
· `isIso_app_pushforwardMapHomotopy_of_isKInjective`, the **unconditional Stacks 0D6E for a
morphism of ringed topoi**. That is the source's own argument: `Rf_* ⋙ Rg_*` is a right adjoint
of `Lg^* ⋙ Lf^*` because each factor is (Stacks 07A6), that composite is `L(g ∘ f)^*`
(Stacks 0D6D), and `R(g ∘ f)_*` is a right adjoint of `L(g ∘ f)^*` as well, so the two agree by
uniqueness of right adjoints.

Two things had to be true for it to reach this leg, and both are recorded because neither was
available when this note was first written.

* *The geometric datum is a morphism of ringed topoi, not of ringed sites.*
  `isIso_derivedPushforwardComparison_unconditional`, in
  `Stacks.Cohomology.DerivedPushforwardCompositionOnTopoi`, is for an
  `AlgebraicGeometry.RingedToposSiteHom` and carries
  `CategoryTheory.Functor.IsMorphismOfSites` of the underlying functor of each morphism.
  `AlgebraicGeometry.Space.smallEtaleRingedToposHom` has no such functor: a morphism of
  algebraic spaces induces no functor between the small étale sites, the base change of an étale
  *scheme* chart along a non-representable morphism being an algebraic space and not a chart —
  `AlgebraicGeometry.Space.smallBaseChange`, the only functor there is, carries
  `CategoryTheory.Functor.relativelyRepresentable` of the morphism. So `f_small` is an
  `AlgebraicGeometry.RingedToposHom` and nothing more, and no relaxation of universe binders can
  change that: the continuous functor is a *field* of `RingedToposSiteHom`. The two pullbacks are
  different functors as well — Mathlib's `SheafOfModules.pullback` against the inverse image of
  Stacks 03D2 followed by extension of scalars — so the ringed-topoi statement is not a universe
  generalization of the ringed-site one. The same point is recorded, for the derived pullback, in
  the implementation notes of
  `StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPullback/DerivedPullbackOfToposHom.lean`.
* *The universes.* `π_F` is a `RingedToposHom.{w, v, u, u, u + 1, u}` and `f_small` a
  `RingedToposHom.{u, u + 1, u, u, u + 1, u}`, the small étale ringed topos of an algebraic space
  being `AlgebraicGeometry.RingedTopos.{u, u + 1, u}`; and the unconditional Stacks 0D6E consumes
  Stacks 07A6 and Stacks 0FPI at `π_F`, at `f_small` **and** at their composite, so all three
  need the Stacks 06YY datum with its target above the module universe. That datum is now free in
  both halves. Its *resolving* half always was: Stacks 06YS is
  `Stacks.SheafOfModules.KFlatResolution.exists_kFlatResolution_ofSize`, which resolves by flat
  modules at three independent universes rather than by a direct sum of extensions by zero
  indexed by sections over objects — the form
  `Stacks.SheafOfModules.KFlatResolution.exists_kFlatResolution` takes, whose index type is not
  `u`-small on a site with objects in `Type (u + 1)`. Its *exactness* half,
  `Stacks.Cohomology.DerivedPullbackOfToposHom.pullbackInvertsQuasiIso_isKFlat`, rested on
  Stacks 0G6R and through it on Stacks 05VD, and those were stated with the section universe of
  each side dominating its own site universes. They are now at three independent universes per
  ringed topos; what had pinned them was the `max v w` pairing of the two halves of Stacks 08FC
  (the free-universe pairing
  `Stacks.SheafOfModules.isFlat_iff_hasLocalSingleRelationFactorizations_freeUniverse` was
  already available), `Stacks.Sheaves.TypeSheaf.exists_covering_of_epi_sigmaDesc` at
  `Type (max u v)`, and the identification of extension of scalars with
  `Stacks.Sheaves.ChangeOfRings.changeOfRings`, whose ring universe is the *object* universe of
  the site. Stacks 05V4 itself (`Stacks.FlatChangeOfRings.isFlat_extendScalars`) was free all
  along.

What the criterion asks of the three sites in addition is `CategoryTheory.HasSheafify` for
`Type u`-valued sheaves. At a site whose objects live above the universe of the sections this is
not Mathlib's size-restricted instance but `CategoryTheory.hasSheafifyEssentiallySmallSite`, and
the three sites here are essentially small: the small étale site of an algebraic space outright,
and `𝒳` because it is representable, which is
`AlgebraicGeometry.Space.essentiallySmall_of_equivalenceOver` — the same step
`AlgebraicGeometry.Space.projectionRingedToposHom` itself takes. They are supplied inside the
proof, so no binder of Stacks 075N mentions them.

**Why the flat route was not the route, independently of the universes.** The other way to the
condition would have been Stacks 093Y as this development has it for a flat morphism,
`isKInjective_mapHomologicalComplex_pushforwardModules`, which asks
`PreservesFiniteLimits (pullbackModules π_F)` and nothing else. It is recorded as closed because
the flatness it asks for is false, so no amount of universe work would have opened it. Two
obstructions stood in the way and neither implies the other.

* *The universes.* Applying it to `π_F` asks that source and target be one
  `AlgebraicGeometry.RingedTopos` universe triple: the source is `RingedTopos.{w, v, u}` and
  the target `RingedTopos.{u, u + 1, u}`, so the application is rejected before any hypothesis
  is examined. The restriction is inherited, not essential — `rightAdjoint_preserves_isKInjective`
  (Stacks 070G) declares its two abelian categories over one pair of universe variables, as the
  implementation notes of `CompositionWithAFlatFirstMorphism.lean` in
  `StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPushforward/` already record — and a
  generalization of those binders would remove it.
* *The flatness, which is the real obstruction.* `PreservesFiniteLimits (pullbackModules π_F)`
  is not available and is not an oversight. `pullbackModules` is the topos inverse image
  followed by extension of scalars along the structure map, so its exactness is flatness of
  `RingedToposHom.fSharpInverseImage`, the *inverse-image* form `π_F^{-1}𝒪_F ⟶ 𝒪_𝒳` of the
  structure map — `pullbackModules_exact_of_isFlatMap` (Stacks 04JC) asks exactly that, and is
  the one such statement already general in the universes. Now `π_F`'s structure map is
  supplied in *direct-image* form, as `𝒪_F ⟶ π_{F,*}𝒪_𝒳`, and in that form it **is** an
  isomorphism: `inverseImage_structureSheaf_eq` makes the restriction of `𝒪_𝒳` along the
  functor of Stacks 073M equal to `𝒪_F` on the nose, and `restrictionCommRingIso` is an
  isomorphism. That does not transfer. By `fSharpInverseImage_forget` the inverse-image form is
  the image of the direct-image form under `π_F^{-1} = g_!` followed by the counit of
  `g_! ⊣ π_{F,*}`, so it is `g_!(𝒪_F) ⟶ 𝒪_𝒳`, and the only bridge the development has from an
  invertible `fSharp` to an invertible `fSharpInverseImage`, `isIso_fSharpInverseImage`, needs
  `π_{F,*}` to be an **equivalence**, which restriction along `F_étale ⥤ 𝒳` is not. Every
  flatness in the development is produced from `isFlatMap_of_isIso`, so with
  `fSharpInverseImage` not invertible there is no input at all; `π_F` is the only one of these
  morphisms whose structure map is given in direct-image form, and the sibling `i_F` — whose
  `fSharp` is built as the adjunct of an isomorphism — is the shape from which the flatness
  results do follow. This is the module-coefficient failure the source itself records: flatness
  of `π_F` would give Stacks 075L for sheaves of modules, which Stacks 0758 refutes. Stacks 075L
  for *abelian* sheaves is proved, `isKInjective_restrictionAbSheafFunctor_obj`, precisely
  because there the left adjoint of restriction is `g_!` itself, with no extension of scalars.

So the flat route needs flatness of `g_!(𝒪_F) ⟶ 𝒪_𝒳`, which is false; there is no route to the
condition through Stacks 093Y, and the unconditional Stacks 0D6E for a `RingedToposHom` recorded
above is the one taken.

**Stacks 093Y for degreewise `f_*` is no longer carried.** The first leg of the square is
`π_G ∘ f`, and the criterion `isRightDerivedFunctor_comp_of_isGrothendieckAbelian` uses
K-injectivity of `f_*I` only to know that the unit of the *second* derived functor is
invertible there. On this leg the second functor is `derivedPushforwardOfExact π_G`, whose
unit is invertible everywhere (`isIso_derivedPushforwardOfExactUnit`), so nothing is needed of
`f`. `PushforwardComputesDerived` is that weaker condition, isolated so that the three routes to
it can be stated: an invertible unit (`pushforwardComputesDerived_of_isIso`), which is the first
leg; Stacks 093Y for the first morphism
(`pushforwardComputesDerived_of_preservesKInjectiveModules`), which no leg of this square uses;
and the unconditional Stacks 0D6E, which is the second leg.

Exactness of the two module-level restrictions `π_{F,*}` and `π_{G,*}` — the source's own
closing sentence — used to be a third carried input, as a `PreservesFiniteColimits` instance
hypothesis on each. It is now **proved**:
`AlgebraicGeometry.Space.exactFunctor_pushforwardModules_projectionRingedToposHom`, in
`StacksFrontier/AlgebraicGeometry/Stacks/RestrictionProjectionExactness.lean`. The finite-limit
half is automatic for a right adjoint,
`AlgebraicGeometry.RingedToposHom.pushforwardModules_preservesFiniteLimits`; the finite-colimit
half comes from the functor
`F_étale ⥤ 𝒳` of Stacks 073M being **cocontinuous**, which makes restriction along it preserve
epimorphisms of sheaves of sets, hence homology of sheaves of modules, hence finite colimits.
That route avoids the identification `pullbackModules i_F ≅ pushforwardModules π_F` of equation
075K for module coefficients, which this development still does not have. Note that
Stacks 075L is **not** a route: it is false for sheaves of modules, by Stacks 0758.

Everything else is proved: the comparison of the two derived composites, the condition it
consumes at each of the two legs, the exactness of the two restrictions, the identification of
the derived restrictions with the degreewise ones from it, and the universe generalization
below.

**Why Stacks 0D6E is restated.** `derivedPushforwardComparison_isIso` reaches Grothendieck
abelianness of the two categories of modules through `UnivLE` between the site and the section
universes of the source and the middle ringed topos. For the leg `f_small ∘ π_F` the middle is
the small étale ringed topos of an algebraic space, which is
`AlgebraicGeometry.RingedTopos.{u, u + 1, u}` — site objects in `Type (u + 1)`, sections in
`Type u` — so that `UnivLE` is false and that statement cannot be instantiated at this
leg at all. `isRightDerivedFunctor_comp_of_isGrothendieckAbelian` is the
same statement with the same proof, taking `CategoryTheory.IsGrothendieckAbelian` as a
hypothesis instead; nothing is weakened, and the `UnivLE` route remains available to anyone who
has it.

**The Grothendieck abelianness hypotheses are satisfiable.** They are asked of the two fibred
ringed topoi and of the small étale ringed topos of `F`, at the universe of the structure
rings. For the last, that is exactly
`AlgebraicGeometry.Space.isGrothendieckAbelian_modules`, proved from essential smallness of the
small étale site. For the two fibred topoi, essential smallness is likewise available: `𝒳` is
essentially small because it is representable, which is
`AlgebraicGeometry.Space.essentiallySmall_of_equivalenceOver`, used for the same purpose inside
`AlgebraicGeometry.Space.projectionRingedToposHom`. They are hypotheses rather than instances
only because the instance that produces them from essential smallness must be stated at the
reduced spelling of the site, as recorded in
`StacksFrontier/AlgebraicGeometry/Spaces/DerivedModulePushforward.lean`.

**No hypothesis is asked of the target.** The small étale ringed topos of `G` carries no
Grothendieck abelianness hypothesis. The criterion behind Stacks 0D6E needs it for the source of
a composite — to know that every object of its derived category comes from a K-injective
complex — and for the middle, where the unit of the second derived direct image is evaluated;
the target of a composite only receives, so nothing is required of it. Both legs here have the
small étale ringed topos of `G` for target, and the two middles are `𝒴_étale` and the small
étale ringed topos of `F`, which is why exactly three of the four corners are constrained.

**Additivity is pinned, not synthesized.** `AlgebraicGeometry.RingedToposHom.pushforwardModules`
is additive for every morphism of ringed topoi,
`AlgebraicGeometry.RingedToposHom.pushforwardModules_additive`, and instance search finds that
where the two ringed topoi are variables. It does not find it at the concrete morphisms of this
file, although the instance applies there when named. `PreservesKInjectiveModules`,
`derivedPushforwardOfExact` and `derivedPushforwardOfExactUnit` therefore exist: each is a
definition made where the ringed topoi are still variables, so that the additivity instance
which `CategoryTheory.Functor.mapHomologicalComplex` and
`CategoryTheory.Functor.mapDerivedCategory` consume is resolved once. Both
`CategoryTheory.Functor.Additive` and `CategoryTheory.Limits.PreservesZeroMorphisms` are
`Prop`-valued, so pinning a particular proof of them loses nothing.
`derivedPushforwardOfExact` and `derivedPushforwardOfExactUnit` are additionally made
irreducible once their characterizing property is proved, which keeps the definitional unifier
out of the construction of the derived category while the statement of Stacks 075N is
elaborated.

**The statement is an isomorphism, not an invertibility claim.** Stacks 075N is an
identification of two functors, so `restrictedDerivedDirectImageIso` is the isomorphism itself.
It is not a chosen isomorphism between abstractly isomorphic functors: it is
`AlgebraicGeometry.RingedToposHom.twoLegsComparison`, the map induced by the universal property
of `Rf_* ⋙ Rπ_{G,*}` as a right derived functor, shown invertible by
`isIso_twoLegsComparison`.

## References

* [Stacks Project, Tag 075N](https://stacks.math.columbia.edu/tag/075N)
* [Stacks Project, Tag 073M](https://stacks.math.columbia.edu/tag/073M)
* [Stacks Project, Tag 073N](https://stacks.math.columbia.edu/tag/073N)
* [Stacks Project, Tag 075K](https://stacks.math.columbia.edu/tag/075K)
* [Stacks Project, Tag 075L](https://stacks.math.columbia.edu/tag/075L)
* [Stacks Project, Tag 076Q](https://stacks.math.columbia.edu/tag/076Q)
* [Stacks Project, Tag 0GQA](https://stacks.math.columbia.edu/tag/0GQA)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 03H7](https://stacks.math.columbia.edu/tag/03H7)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 0300](https://stacks.math.columbia.edu/tag/0300)
* [Stacks Project, Tag 0758](https://stacks.math.columbia.edu/tag/0758)
* [Stacks Project, Tag 093Y](https://stacks.math.columbia.edu/tag/093Y)
* [Stacks Project, Tag 0D6E](https://stacks.math.columbia.edu/tag/0D6E)
* [Stacks Project, Tag 07A5](https://stacks.math.columbia.edu/tag/07A5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Stacks.Cohomology.UnboundedComplexes

universe w v u v₂ u₂ v₃ u₃

variable {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{w} A]

/-- A right derived functor stays one after the functor it derives is replaced by an isomorphic
functor: if `RF` is a right derived functor of `F'` with unit `α`, and `e : F ≅ F'`, then `RF` is
a right derived functor of `F` with unit `e ≫ α`.

The criterion `isRightDerivedFunctor_of_isIso_app_isKInjective` only asks the unit to be
invertible at K-injective complexes, where `α` is invertible by
`isIso_app_of_isKInjective` and `e` is invertible everywhere. -/
theorem isRightDerivedFunctor_comp_of_isIso {H : Type u₂} [Category.{v₂} H]
    {F F' : HomotopyCategory A (ComplexShape.up ℤ) ⥤ H} (e : F ⟶ F') [IsIso e]
    {D : Type u₃} [Category.{v₃} D] (L : HomotopyCategory A (ComplexShape.up ℤ) ⥤ D)
    [L.IsLocalization (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))] (RF : D ⥤ H)
    (α : F' ⟶ L ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))] :
    RF.IsRightDerivedFunctor (e ≫ α) (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) := by
  refine isRightDerivedFunctor_of_isIso_app_isKInjective _ _ _ _ fun I hI ↦ ?_
  have := isIso_app_of_isKInjective F' L RF α I hI
  rw [NatTrans.comp_app]
  infer_instance

end Stacks.Cohomology.UnboundedComplexes

namespace AlgebraicGeometry.RingedToposHom

universe w w' w₂ w₃ v u v' u' v₂ u₂ v₃ u₃ dX dY dY₂ dZ

/-! ### Stacks 0D6E with Grothendieck abelianness supplied directly -/

section Composite

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  {Z : RingedTopos.{v₃, u₃, w₃}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [Z.J.HasSheafCompose (forget RingCat.{w₃})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w₃} RingCat.{w₃})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w₃})]
  [HasSheafify X.J AddCommGrpCat.{w}] [HasSheafify Y.J AddCommGrpCat.{w'}]
  [HasSheafify Z.J AddCommGrpCat.{w₃}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [Z.J.WEqualsLocallyBijective AddCommGrpCat.{w₃}]
  [HasDerivedCategory.{dX} X.Modules] [HasDerivedCategory.{dY} Y.Modules]
  [HasDerivedCategory.{dZ} Z.Modules]
  (f : RingedToposHom X Y) (g : RingedToposHom Y Z)
  (Rf : DerivedCategory X.Modules ⥤ DerivedCategory Y.Modules)
  (Rg : DerivedCategory Y.Modules ⥤ DerivedCategory Z.Modules)
  (αf : pushforwardToDerivedCategory f ⟶ DerivedCategory.Qh ⋙ Rf)
  (αg : pushforwardToDerivedCategory g ⟶ DerivedCategory.Qh ⋙ Rg)

/-- **Stacks 093Y as a property of a morphism of ringed topoi**: degreewise direct image of
complexes of sheaves of modules along `f` carries K-injective complexes of `𝒪_C`-modules to
K-injective complexes of `𝒪_D`-modules.

This is the hypothesis that
`AlgebraicGeometry.RingedToposHom.derivedPushforwardComparison_isIso` carries, named. Naming it
also pins the additivity instance that `CategoryTheory.Functor.mapHomologicalComplex` consumes:
`AlgebraicGeometry.RingedToposHom.pushforwardModules_additive` is found by instance search here,
where the two ringed topoi are variables, but not at every concrete pair of ringed topoi, and
`CategoryTheory.Functor.Additive` is a `Prop`, so pinning it loses nothing. -/
def PreservesKInjectiveModules (f : RingedToposHom X Y) : Prop :=
  ∀ I : CochainComplex X.Modules ℤ, I.IsKInjective →
    CochainComplex.IsKInjective
      (((pushforwardModules f).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)

/-- **The condition the composition criterion actually uses**: the unit of `Rg` is invertible
at the degreewise direct image along `f` of every K-injective complex of `𝒪_C`-modules.

`isRightDerivedFunctor_comp_of_isGrothendieckAbelian` consumes nothing else of its
K-injectivity input, and there are two ways to supply it:
`pushforwardComputesDerived_of_preservesKInjectiveModules`, which is Stacks 093Y for `f`, and
`pushforwardComputesDerived_of_isIso`, which asks nothing of `f` at all and applies whenever
the unit of `Rg` is an isomorphism — in particular when `g` has exact degreewise direct image
and `Rg` is `derivedPushforwardOfExact g`. Splitting the two off from the criterion is what
lets the second leg of a square with an exact second morphism carry no hypothesis on its
first. -/
def PushforwardComputesDerived (f : RingedToposHom X Y) (g : RingedToposHom Y Z)
    (Rg : DerivedCategory Y.Modules ⥤ DerivedCategory Z.Modules)
    (αg : pushforwardToDerivedCategory g ⟶ DerivedCategory.Qh ⋙ Rg) : Prop :=
  ∀ I : CochainComplex X.Modules ℤ, I.IsKInjective →
    IsIso (αg.app (((pushforwardModules f).mapHomotopyCategory (ComplexShape.up ℤ)).obj
      ((HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).obj I)))

omit [Z.J.HasSheafCompose (forget AddCommGrpCat.{w₃})] [HasDerivedCategory.{dX} X.Modules] in
/-- **Stacks 093Y for `f` supplies the condition.** If degreewise `f_*` preserves
K-injectivity, then the unit of any right derived functor `Rg` is invertible at the direct
image of a K-injective complex, by
`Stacks.Cohomology.UnboundedComplexes.isIso_app_of_isKInjective`. -/
theorem pushforwardComputesDerived_of_preservesKInjectiveModules
    [IsGrothendieckAbelian.{w'} Y.Modules]
    [Rg.IsRightDerivedFunctor αg (HomotopyCategory.quasiIso Y.Modules (ComplexShape.up ℤ))]
    (hf : PreservesKInjectiveModules f) :
    PushforwardComputesDerived f g Rg αg := fun I hI ↦
  Stacks.Cohomology.UnboundedComplexes.isIso_app_of_isKInjective
    (pushforwardToDerivedCategory g) DerivedCategory.Qh Rg αg _ (hf I hI)

omit [Z.J.HasSheafCompose (forget AddCommGrpCat.{w₃})] [HasDerivedCategory.{dX} X.Modules] in
/-- **An invertible unit supplies the condition, with no hypothesis on `f`.** This is the case
of an exact degreewise direct image along `g`, where
`isIso_derivedPushforwardOfExactUnit` makes the unit of `derivedPushforwardOfExact g` an
isomorphism everywhere, so in particular at the direct images of K-injective complexes. -/
theorem pushforwardComputesDerived_of_isIso [IsIso αg] :
    PushforwardComputesDerived f g Rg αg := fun _ _ ↦ inferInstance

/-- `isRightDerivedFunctor_derivedPushforwardCompUnit` with Grothendieck abelianness of the two
categories of modules supplied as a hypothesis instead of deduced from `UnivLE` between the site
and section universes.

The statement and the proof are those of
`AlgebraicGeometry.RingedToposHom.isRightDerivedFunctor_derivedPushforwardCompUnit`; only the
route to `CategoryTheory.IsGrothendieckAbelian` differs. That route matters here because the
small étale ringed topos of an algebraic space is
`AlgebraicGeometry.RingedTopos.{u, u + 1, u}` — site objects in `Type (u + 1)`, sections in
`Type u` — so `UnivLE` between its site and section universes is false, while its modules are
Grothendieck abelian all the same, by essential smallness of the site
(`AlgebraicGeometry.Space.isGrothendieckAbelian_modules`). -/
theorem isRightDerivedFunctor_comp_of_isGrothendieckAbelian
    [IsGrothendieckAbelian.{w} X.Modules] [IsGrothendieckAbelian.{w'} Y.Modules]
    [Rf.IsRightDerivedFunctor αf (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))]
    [Rg.IsRightDerivedFunctor αg (HomotopyCategory.quasiIso Y.Modules (ComplexShape.up ℤ))]
    (hf : PushforwardComputesDerived f g Rg αg) :
    (Rf ⋙ Rg).IsRightDerivedFunctor (derivedPushforwardCompUnit f g Rf Rg αf αg)
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) := by
  refine Stacks.Cohomology.UnboundedComplexes.isRightDerivedFunctor_of_isIso_app_isKInjective
    _ _ _ _ fun I hI ↦ ?_
  have h₂ : IsIso (αg.app (((pushforwardModules f).mapHomotopyCategory
      (ComplexShape.up ℤ)).obj
      ((HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).obj I))) := hf I hI
  have h₃ : IsIso (αf.app ((HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).obj I)) :=
    Stacks.Cohomology.UnboundedComplexes.isIso_app_of_isKInjective
      (pushforwardToDerivedCategory f) DerivedCategory.Qh Rf αf I hI
  simp only [derivedPushforwardCompUnit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app]
  infer_instance

/-- The functor on unbounded derived categories induced by an **exact** degreewise direct image
of sheaves of modules: `CategoryTheory.Functor.mapDerivedCategory` of
`AlgebraicGeometry.RingedToposHom.pushforwardModules`.

This is the functor the source writes `(-)|_{G_étale}` for when the restriction it restricts
along is exact — the derived category's image of the degreewise direct image, not a right
derived functor of it. That it *is* a right derived functor of it is
`isRightDerivedFunctor_derivedPushforwardOfExactUnit`.

A `def` rather than an `abbrev`: it exists so that the additivity instance that
`CategoryTheory.Functor.mapDerivedCategory` consumes is resolved here, where the two ringed
topoi are variables, rather than at each concrete pair of ringed topoi, where
`AlgebraicGeometry.RingedToposHom.pushforwardModules_additive` is not found by instance search.
See the implementation notes of this file. -/
def derivedPushforwardOfExact (f : RingedToposHom X Y)
    [PreservesFiniteColimits (pushforwardModules f)] :
    DerivedCategory X.Modules ⥤ DerivedCategory Y.Modules :=
  have := pushforwardModules_preservesFiniteLimits f
  (pushforwardModules f).mapDerivedCategory

/-- The canonical unit of `derivedPushforwardOfExact`: the factorization isomorphism of
`CategoryTheory.Functor.mapDerivedCategory` through the homotopy category, read as a
transformation out of the degreewise direct image. It is an isomorphism. -/
def derivedPushforwardOfExactUnit (f : RingedToposHom X Y)
    [PreservesFiniteColimits (pushforwardModules f)] :
    pushforwardToDerivedCategory f ⟶ DerivedCategory.Qh ⋙ derivedPushforwardOfExact f :=
  have := pushforwardModules_preservesFiniteLimits f
  (pushforwardModules f).mapDerivedCategoryFactorsh.inv

/-- The unit of an exact degreewise direct image is invertible: it is the inverse of the
factorization isomorphism of `mapDerivedCategory`. -/
private theorem isIso_derivedPushforwardOfExactUnit_aux (f : RingedToposHom X Y)
    [PreservesFiniteColimits (pushforwardModules f)] :
    IsIso (derivedPushforwardOfExactUnit f) :=
  have := pushforwardModules_preservesFiniteLimits f
  inferInstanceAs (IsIso (pushforwardModules f).mapDerivedCategoryFactorsh.inv)

/-- **An exact direct image is its own total right derived functor.** If degreewise direct image
of sheaves of modules along `f` is exact, then the functor it induces on unbounded derived
categories is a right derived functor of it, with the canonical factorization isomorphism for
unit.

This is the unbounded analogue of `Stacks.Cohomology.BaseChange.exactUnit_isIso`: the unit is an
isomorphism outright, hence an isomorphism at every K-injective complex, which by
`Stacks.Cohomology.UnboundedComplexes.isRightDerivedFunctor_of_isIso_app_isKInjective` is all
that has to be checked. It is what lets a right derived direct image along an exact morphism be
read as the degreewise one. -/
theorem isRightDerivedFunctor_derivedPushforwardOfExactUnit (f : RingedToposHom X Y)
    [IsGrothendieckAbelian.{w} X.Modules]
    [PreservesFiniteColimits (pushforwardModules f)] :
    (derivedPushforwardOfExact f).IsRightDerivedFunctor (derivedPushforwardOfExactUnit f)
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) :=
  have := isIso_derivedPushforwardOfExactUnit_aux f
  Stacks.Cohomology.UnboundedComplexes.isRightDerivedFunctor_of_isIso_app_isKInjective
    _ _ _ _ fun _ _ ↦ inferInstance

/-- **The canonical unit of an exact degreewise direct image is an isomorphism.** It is the
inverse of the factorization isomorphism of `CategoryTheory.Functor.mapDerivedCategory`.

Recorded before `derivedPushforwardOfExact` and `derivedPushforwardOfExactUnit` are made
irreducible, since after that the identification is no longer available to unification. It is
what `pushforwardComputesDerived_of_isIso` consumes. -/
theorem isIso_derivedPushforwardOfExactUnit (f : RingedToposHom X Y)
    [PreservesFiniteColimits (pushforwardModules f)] :
    IsIso (derivedPushforwardOfExactUnit f) :=
  isIso_derivedPushforwardOfExactUnit_aux f

attribute [instance] isIso_derivedPushforwardOfExactUnit

attribute [irreducible] derivedPushforwardOfExact derivedPushforwardOfExactUnit

end Composite

/-! ### Two factorizations of 2-isomorphic composites -/

section TwoLegs

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  {Y₂ : RingedTopos.{v₂, u₂, w₂}} {Z : RingedTopos.{v₃, u₃, w₃}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [Y₂.J.HasSheafCompose (forget RingCat.{w₂})] [Z.J.HasSheafCompose (forget RingCat.{w₃})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Y₂.J.HasSheafCompose (forget₂ CommRingCat.{w₂} RingCat.{w₂})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w₃} RingCat.{w₃})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [Y₂.J.HasSheafCompose (forget AddCommGrpCat.{w₂})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w₃})]
  [HasSheafify X.J AddCommGrpCat.{w}] [HasSheafify Y.J AddCommGrpCat.{w'}]
  [HasSheafify Y₂.J AddCommGrpCat.{w₂}] [HasSheafify Z.J AddCommGrpCat.{w₃}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [Y₂.J.WEqualsLocallyBijective AddCommGrpCat.{w₂}]
  [Z.J.WEqualsLocallyBijective AddCommGrpCat.{w₃}]
  [HasDerivedCategory.{dX} X.Modules] [HasDerivedCategory.{dY} Y.Modules]
  [HasDerivedCategory.{dY₂} Y₂.Modules] [HasDerivedCategory.{dZ} Z.Modules]

/-- Two 2-isomorphic morphisms of ringed topoi have isomorphic degreewise direct images of
complexes of modules on the unbounded homotopy category, followed by localization.

This is `AlgebraicGeometry.RingedToposHom.TwoIso.pushforwardModulesIso` carried along
`CategoryTheory.NatTrans.mapHomotopyCategory` and whiskered with the localization
`DerivedCategory.Qh`. -/
def TwoIso.pushforwardToDerivedCategoryIso {h h' : RingedToposHom X Z} (t : TwoIso h h') :
    pushforwardToDerivedCategory h ≅ pushforwardToDerivedCategory h' :=
  Functor.isoWhiskerRight
    { hom := NatTrans.mapHomotopyCategory t.pushforwardModulesIso.hom (ComplexShape.up ℤ)
      inv := NatTrans.mapHomotopyCategory t.pushforwardModulesIso.inv (ComplexShape.up ℤ)
      hom_inv_id := by
        rw [← NatTrans.mapHomotopyCategory_comp, t.pushforwardModulesIso.hom_inv_id,
          NatTrans.mapHomotopyCategory_id]
      inv_hom_id := by
        rw [← NatTrans.mapHomotopyCategory_comp, t.pushforwardModulesIso.inv_hom_id,
          NatTrans.mapHomotopyCategory_id] }
    DerivedCategory.Qh

variable (f : RingedToposHom X Y) (g : RingedToposHom Y Z)
  (f' : RingedToposHom X Y₂) (g' : RingedToposHom Y₂ Z)
  (Rf : DerivedCategory X.Modules ⥤ DerivedCategory Y.Modules)
  (Rg : DerivedCategory Y.Modules ⥤ DerivedCategory Z.Modules)
  (Rf' : DerivedCategory X.Modules ⥤ DerivedCategory Y₂.Modules)
  (Rg' : DerivedCategory Y₂.Modules ⥤ DerivedCategory Z.Modules)
  (αf : pushforwardToDerivedCategory f ⟶ DerivedCategory.Qh ⋙ Rf)
  (αg : pushforwardToDerivedCategory g ⟶ DerivedCategory.Qh ⋙ Rg)
  (αf' : pushforwardToDerivedCategory f' ⟶ DerivedCategory.Qh ⋙ Rf')
  (αg' : pushforwardToDerivedCategory g' ⟶ DerivedCategory.Qh ⋙ Rg')
  (t : TwoIso (g.comp f) (g'.comp f'))

/-- The unit of the second composite `Rf'_* ⋙ Rg'_*`, read as a transformation out of the
degreewise direct image along the *first* composite through the 2-isomorphism of the two
composites. -/
def twoLegsUnit :
    pushforwardToDerivedCategory (g.comp f) ⟶ DerivedCategory.Qh ⋙ (Rf' ⋙ Rg') :=
  t.pushforwardToDerivedCategoryIso.hom ≫ derivedPushforwardCompUnit f' g' Rf' Rg' αf' αg'

variable [IsGrothendieckAbelian.{w} X.Modules] [IsGrothendieckAbelian.{w'} Y.Modules]
  [IsGrothendieckAbelian.{w₂} Y₂.Modules]
  [Rf.IsRightDerivedFunctor αf (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))]
  [Rg.IsRightDerivedFunctor αg (HomotopyCategory.quasiIso Y.Modules (ComplexShape.up ℤ))]
  [Rf'.IsRightDerivedFunctor αf' (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))]
  [Rg'.IsRightDerivedFunctor αg' (HomotopyCategory.quasiIso Y₂.Modules (ComplexShape.up ℤ))]

/-- The canonical comparison `Rf_* ⋙ Rg_* ⟶ Rf'_* ⋙ Rg'_*` of the two derived composites of a
commutative square-shaped diagram of ringed topoi, induced by the universal property of the
first as a right derived functor of degreewise `(g ∘ f)_*`. The hypothesis is the one of
`isRightDerivedFunctor_comp_of_isGrothendieckAbelian`, namely `PushforwardComputesDerived`. -/
def twoLegsComparison (hf : PushforwardComputesDerived f g Rg αg) :
    (Rf ⋙ Rg) ⟶ (Rf' ⋙ Rg') :=
  haveI := isRightDerivedFunctor_comp_of_isGrothendieckAbelian
    f g Rf Rg αf αg hf
  (Rf ⋙ Rg).rightDerivedDesc (derivedPushforwardCompUnit f g Rf Rg αf αg)
    (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) (Rf' ⋙ Rg')
    (twoLegsUnit f g f' g' Rf' Rg' αf' αg' t)

/-- **The two derived composites of a 2-commutative square of ringed topoi agree.** If
`g ∘ f` and `g' ∘ f'` are 2-isomorphic morphisms of ringed topoi, and if the units of `Rg` and
`Rg'` are invertible at the direct images of K-injective complexes, then the canonical
comparison `Rf_* ⋙ Rg_* ⟶ Rf'_* ⋙ Rg'_*` is invertible. Either leg's hypothesis is supplied by
Stacks 093Y for its first morphism, through
`pushforwardComputesDerived_of_preservesKInjectiveModules`, or for free by
`pushforwardComputesDerived_of_isIso` when its second morphism has exact degreewise direct
image.

Both composites are right derived functors of degreewise direct image along their own
composite, by `isRightDerivedFunctor_comp_of_isGrothendieckAbelian`; the
2-isomorphism identifies the two degreewise direct images, so by
`Stacks.Cohomology.UnboundedComplexes.isRightDerivedFunctor_comp_of_isIso` they are right
derived functors of one and the same functor, and the comparison between two right derived
functors of one functor is invertible. -/
theorem isIso_twoLegsComparison
    (hf : PushforwardComputesDerived f g Rg αg)
    (hf' : PushforwardComputesDerived f' g' Rg' αg') :
    IsIso (twoLegsComparison f g f' g' Rf Rg Rf' Rg' αf αg αf' αg' t hf) := by
  have := isRightDerivedFunctor_comp_of_isGrothendieckAbelian
    f g Rf Rg αf αg hf
  have := isRightDerivedFunctor_comp_of_isGrothendieckAbelian
    f' g' Rf' Rg' αf' αg' hf'
  have := Stacks.Cohomology.UnboundedComplexes.isRightDerivedFunctor_comp_of_isIso
    t.pushforwardToDerivedCategoryIso.hom DerivedCategory.Qh (Rf' ⋙ Rg')
    (derivedPushforwardCompUnit f' g' Rf' Rg' αf' αg')
  exact (Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc (Rf ⋙ Rg)
    (derivedPushforwardCompUnit f g Rf Rg αf αg)
    (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) (Rf' ⋙ Rg')
    (twoLegsUnit f g f' g' Rf' Rg' αf' αg' t)).mp this

/-- **The two derived composites of a 2-commutative square of ringed topoi are isomorphic**,
by the invertible comparison `twoLegsComparison`. -/
def twoLegsIso (hf : PushforwardComputesDerived f g Rg αg)
    (hf' : PushforwardComputesDerived f' g' Rg' αg') :
    (Rf ⋙ Rg) ≅ (Rf' ⋙ Rg') :=
  have := isIso_twoLegsComparison f g f' g' Rf Rg Rf' Rg' αf αg αf' αg' t hf hf'
  asIso (twoLegsComparison f g f' g' Rf Rg Rf' Rg' αf αg αf' αg' t hf)

end TwoLegs

end AlgebraicGeometry.RingedToposHom

/-! ### Stacks 075N for sheaves of modules -/

namespace AlgebraicGeometry.Space

universe u v w v' w' dX dY dF dG

open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

attribute [local instance] hasSheafCompose_forget_ringCat
  Stacks.hasSheafCompose_forget₂_commRingCat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  {𝒳 : Type v} [Category.{w} 𝒳] {𝒴 : Type v'} [Category.{w'} 𝒴]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (q : 𝒴 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
  (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
  (eF : StacksRepresentableCFG.EquivalenceOver p
    (presheafOfCategories (F ⋙ typeToCat)).p)
  (eG : StacksRepresentableCFG.EquivalenceOver q
    (presheafOfCategories (G ⋙ typeToCat)).p)
  (fStack : 𝒳 ⥤ 𝒴) (hfStack : p.IsFibredOneMorphism q fStack)

/-- **The morphism of algebraic spaces induced by the 1-morphism**, at the spelling in which the
statement of Stacks 075N below needs it: `AlgebraicGeometry.Space.inducedSpacesHom` for the
algebraic spaces `⟨F, hF⟩` and `⟨G, hG⟩` and for a 1-morphism presented as a
`CategoryTheory.Functor.IsFibredOneMorphism`, of which only the verticality `hfStack.comp_eq`
enters.

This is the source's "denote `f : F ⟶ G` the induced morphism of algebraic spaces". It is
*derived* from `fStack` and the two presentations `eF`, `eG` and is therefore not a hypothesis:
Stacks 075N gives `S`, the 1-morphism, the two presentations and the complex, and nothing else.
That this term is the morphism Stacks 04SW attaches to `fStack` is
`AlgebraicGeometry.Space.eq_inducedSpacesHom_iff_forall_sectionOfObj`, which characterises it by
carrying the section of `F` named by each object `z` of `𝒳` to the section of `G` named by
`fStack z`, together with `AlgebraicGeometry.Stack.morphismSpaceEquiv_eq_inducedSpaceMap`, which
identifies that recipe with the bijection of Stacks 04SW.

It is named only so that the binders of the statement below — the derived direct image
`RfSpace`, its unit `αfSpace`, and the square `sq` — can be written through the name rather than
through the unfolded `ObjectProperty.homMk (natTransOfBasedFunctor …)`. -/
def inducedAlgebraicSpacesHom : (⟨F, hF⟩ : AlgebraicSpaces B S hS) ⟶ ⟨G, hG⟩ :=
  inducedSpacesHom B S hS (X := ⟨F, hF⟩) (Y := ⟨G, hG⟩) p q eF eG fStack hfStack.comp_eq

section TwoIso

variable [∀ P : 𝒳ᵒᵖ ⥤ Type u, fStack.op.HasPointwiseRightKanExtension P]

/-- **Stacks 073N at the induced morphism of algebraic spaces**, in the spelling the statement
of Stacks 075N below needs: the two legs `π_G ∘ f` and `f_{small} ∘ π_F` of the square are
2-isomorphic morphisms of ringed topoi, with the morphism of algebraic spaces taken to be
`AlgebraicGeometry.Space.inducedAlgebraicSpacesHom`.

This is `AlgebraicGeometry.Space.restrictionRingedSquareOfInduced`, read through that name for
the induced morphism. It is a *theorem* of this development and not a hypothesis: the
structure-sheaf compatibility of the square is
`AlgebraicGeometry.Space.restrictedDirectImageComparison_structureSheafCompatible`, whose
verticality input is `AlgebraicGeometry.Space.isHomLift_schemeChartPostcompIso_hom_app`, and
invertibility of the comparison map of equation 075M is
`AlgebraicGeometry.Space.isIso_restrictedDirectImageComparison`, proved chartwise from the
pushforward formula of Stacks 06W6, the chart correspondence of Stacks 03G8 and the covering
of Properties of Spaces 03H7. Its hypotheses are exactly those of Stacks 075N itself — `S`,
the 1-morphism and the two presentations — together with the right Kan extensions that compute
the direct image along the 1-morphism. -/
noncomputable def restrictionRingedSquareInducedAlgebraicSpaces :
    RingedToposHom.TwoIso
      (A := FibredSite.associatedRingedTopos B S hS p hp .etale)
      (B := smallEtaleRingedTopos B S hS ⟨G, hG⟩)
      (restrictionSquareFibredLeg B S hS G p q hp hq hG eG fStack hfStack)
      (restrictionSquareSpaceLeg B S hS F G p hp hF hG eF
        (inducedAlgebraicSpacesHom B S hS F G p q hF hG eF eG fStack hfStack)) :=
  restrictionRingedSquareOfInduced B S hS F G p q hp hq hF hG eF eG fStack hfStack

end TwoIso

variable [∀ P : 𝒳ᵒᵖ ⥤ Type u, fStack.op.HasPointwiseRightKanExtension P]
  [(FibredSite.associatedRingedTopos B S hS p hp .etale).J.HasSheafCompose
    (forget AddCommGrpCat.{u})]
  [(FibredSite.associatedRingedTopos B S hS q hq .etale).J.HasSheafCompose
    (forget AddCommGrpCat.{u})]
  [(smallEtaleRingedTopos B S hS ⟨F, hF⟩).J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [(smallEtaleRingedTopos B S hS ⟨G, hG⟩).J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify (FibredSite.associatedRingedTopos B S hS p hp .etale).J AddCommGrpCat.{u}]
  [HasSheafify (FibredSite.associatedRingedTopos B S hS q hq .etale).J AddCommGrpCat.{u}]
  [HasSheafify (smallEtaleRingedTopos B S hS ⟨F, hF⟩).J AddCommGrpCat.{u}]
  [HasSheafify (smallEtaleRingedTopos B S hS ⟨G, hG⟩).J AddCommGrpCat.{u}]
  [(FibredSite.associatedRingedTopos B S hS p hp .etale).J.WEqualsLocallyBijective
    AddCommGrpCat.{u}]
  [(FibredSite.associatedRingedTopos B S hS q hq .etale).J.WEqualsLocallyBijective
    AddCommGrpCat.{u}]
  [(smallEtaleRingedTopos B S hS ⟨F, hF⟩).J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(smallEtaleRingedTopos B S hS ⟨G, hG⟩).J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{dX} (FibredSite.associatedRingedTopos B S hS p hp .etale).Modules]
  [HasDerivedCategory.{dY} (FibredSite.associatedRingedTopos B S hS q hq .etale).Modules]
  [HasDerivedCategory.{dF} (smallEtaleRingedTopos B S hS ⟨F, hF⟩).Modules]
  [HasDerivedCategory.{dG} (smallEtaleRingedTopos B S hS ⟨G, hG⟩).Modules]
  [IsGrothendieckAbelian.{u} (FibredSite.associatedRingedTopos B S hS p hp .etale).Modules]
  [IsGrothendieckAbelian.{u} (FibredSite.associatedRingedTopos B S hS q hq .etale).Modules]
  [IsGrothendieckAbelian.{u} (smallEtaleRingedTopos B S hS ⟨F, hF⟩).Modules]
  (Rf : DerivedCategory (FibredSite.associatedRingedTopos B S hS p hp .etale).Modules ⥤
    DerivedCategory (FibredSite.associatedRingedTopos B S hS q hq .etale).Modules)
  (RprojG : DerivedCategory (FibredSite.associatedRingedTopos B S hS q hq .etale).Modules ⥤
    DerivedCategory (smallEtaleRingedTopos B S hS ⟨G, hG⟩).Modules)
  (RprojF : DerivedCategory (FibredSite.associatedRingedTopos B S hS p hp .etale).Modules ⥤
    DerivedCategory (smallEtaleRingedTopos B S hS ⟨F, hF⟩).Modules)
  (RfSpace : DerivedCategory (smallEtaleRingedTopos B S hS ⟨F, hF⟩).Modules ⥤
    DerivedCategory (smallEtaleRingedTopos B S hS ⟨G, hG⟩).Modules)
  (αf : RingedToposHom.pushforwardToDerivedCategory
      (FibredSite.ringedToposMorphism B S hS p q hp hq fStack hfStack .etale) ⟶
    DerivedCategory.Qh ⋙ Rf)
  (αprojG : RingedToposHom.pushforwardToDerivedCategory
      (projectionRingedToposHom B S hS G q hq hG eG) ⟶ DerivedCategory.Qh ⋙ RprojG)
  (αprojF : RingedToposHom.pushforwardToDerivedCategory
      (projectionRingedToposHom B S hS F p hp hF eF) ⟶ DerivedCategory.Qh ⋙ RprojF)
  (αfSpace : RingedToposHom.pushforwardToDerivedCategory
      (smallEtaleRingedToposHom B S hS
        (inducedAlgebraicSpacesHom B S hS F G p q hF hG eF eG fStack hfStack)) ⟶
    DerivedCategory.Qh ⋙ RfSpace)
  [Rf.IsRightDerivedFunctor αf (HomotopyCategory.quasiIso
    (FibredSite.associatedRingedTopos B S hS p hp .etale).Modules (ComplexShape.up ℤ))]
  [RprojG.IsRightDerivedFunctor αprojG (HomotopyCategory.quasiIso
    (FibredSite.associatedRingedTopos B S hS q hq .etale).Modules (ComplexShape.up ℤ))]
  [RprojF.IsRightDerivedFunctor αprojF (HomotopyCategory.quasiIso
    (FibredSite.associatedRingedTopos B S hS p hp .etale).Modules (ComplexShape.up ℤ))]
  [RfSpace.IsRightDerivedFunctor αfSpace (HomotopyCategory.quasiIso
    (smallEtaleRingedTopos B S hS ⟨F, hF⟩).Modules (ComplexShape.up ℤ))]

omit [∀ P : 𝒳ᵒᵖ ⥤ Type u, fStack.op.HasPointwiseRightKanExtension P]
  [HasDerivedCategory.{dX} (FibredSite.associatedRingedTopos B S hS p hp .etale).Modules] in
open Stacks.Cohomology.DerivedPushforwardCompositionOfToposHom
  (isIso_app_pushforwardMapHomotopy_of_isKInjective) in
/-- **The condition the composition criterion consumes, discharged at the second leg of the
square of Stacks 073N.** The unit of `Rf_{small,*}` is invertible at the degreewise restriction
`π_{F,*}I` of every K-injective complex `I` of `𝒪_𝒳`-modules, with **no hypothesis on `π_F`**.

This is the unconditional Stacks 0D6E for a morphism of ringed topoi,
`isIso_app_pushforwardMapHomotopy_of_isKInjective` in
`Stacks.Cohomology.DerivedPushforwardCompositionOfToposHom`, at the two morphisms of this leg. It
replaces Stacks 093Y for `π_F`, which at module coefficients is the statement Stacks 075L records
as false, by Stacks 0758.

Three sheafification instances are supplied by hand: the criterion asks `HasSheafify` for
`Type u`-valued sheaves on each of the three sites, which at a site whose objects live above
the universe of the sections is not Mathlib's size-restricted instance but
`CategoryTheory.hasSheafifyEssentiallySmallSite`. The small étale site of an algebraic space is
essentially small outright, and `𝒳` is essentially small because it is representable, which is
`AlgebraicGeometry.Space.essentiallySmall_of_equivalenceOver` — the same step
`AlgebraicGeometry.Space.projectionRingedToposHom` itself takes. -/
theorem pushforwardComputesDerived_smallEtaleRingedToposHom :
    RingedToposHom.PushforwardComputesDerived
      (projectionRingedToposHom B S hS F p hp hF eF)
      (smallEtaleRingedToposHom B S hS
        (inducedAlgebraicSpacesHom B S hS F G p q hF hG eF eG fStack hfStack))
      RfSpace αfSpace := by
  let : EssentiallySmall.{u} 𝒳 := essentiallySmall_of_equivalenceOver B S hS F p eF
  let : EssentiallySmall.{u} (FibredSite.associatedRingedTopos B S hS p hp .etale).C :=
    essentiallySmall_of_equivalenceOver B S hS F p eF
  let : HasSheafify (FibredSite.associatedRingedTopos B S hS p hp .etale).J (Type u) :=
    hasSheafifyEssentiallySmallSite.{_, _, _, _, u} _ _
  let : HasSheafify (smallEtaleRingedTopos B S hS ⟨F, hF⟩).J (Type u) :=
    hasSheafifyEssentiallySmallSite.{_, _, _, _, u} _ _
  let : HasSheafify (smallEtaleRingedTopos B S hS ⟨G, hG⟩).J (Type u) :=
    hasSheafifyEssentiallySmallSite.{_, _, _, _, u} _ _
  exact isIso_app_pushforwardMapHomotopy_of_isKInjective _ _ RfSpace αfSpace

/-- The comparison `Rf_* ⋙ Rπ_{G,*} ⟶ Rπ_{F,*} ⋙ Rf_{small,*}` of the two derived composites
around the square of Stacks 073N is an isomorphism.

This is `AlgebraicGeometry.RingedToposHom.isIso_twoLegsComparison` at the two legs
`AlgebraicGeometry.Space.restrictionSquareFibredLeg` and
`AlgebraicGeometry.Space.restrictionSquareSpaceLeg`. It is stated for *arbitrary* right derived
functors `RprojF`, `RprojG` of the two restriction functors, and so is not itself the statement
of Stacks 075N, which has the two restrictions appearing underived; that statement is
`isIso_restrictedDerivedDirectImageComparison_of_exact` below, the case in which the two
restrictions are exact and the general comparison can therefore be read with the degreewise
restrictions in place of their derived functors.

The square of the two legs is no longer a hypothesis: it is
`AlgebraicGeometry.Space.restrictionRingedSquareInducedAlgebraicSpaces`, Stacks 073N at the
induced morphism of algebraic spaces. The one hypothesis is `hf`, that degreewise `f_*`
preserves K-injectivity, which is Stacks 093Y for the first morphism of the first leg; it is a
hypothesis *of this statement only*, because the two restrictions appear derived here, so
neither leg's second derived functor is known to have an invertible unit, and `hf` is what
stands in for that on the first leg. It does not survive into
`restrictedDerivedDirectImageIso`, which has the restrictions underived — there the first leg's
condition is free and the second leg's is
`pushforwardComputesDerived_smallEtaleRingedToposHom`. See the implementation notes of this
file. -/
theorem isIso_restrictedDerivedDirectImageComparison
    (hf : RingedToposHom.PreservesKInjectiveModules
      (FibredSite.ringedToposMorphism B S hS p q hp hq fStack hfStack .etale)) :
    IsIso (RingedToposHom.twoLegsComparison
      (FibredSite.ringedToposMorphism B S hS p q hp hq fStack hfStack .etale)
      (projectionRingedToposHom B S hS G q hq hG eG)
      (projectionRingedToposHom B S hS F p hp hF eF)
      (smallEtaleRingedToposHom B S hS
        (inducedAlgebraicSpacesHom B S hS F G p q hF hG eF eG fStack hfStack))
      Rf RprojG RprojF RfSpace αf αprojG αprojF αfSpace
      (restrictionRingedSquareInducedAlgebraicSpaces B S hS F G p q hp hq hF hG eF eG
        fStack hfStack)
      (RingedToposHom.pushforwardComputesDerived_of_preservesKInjectiveModules _ _ _ _ hf)) :=
  RingedToposHom.isIso_twoLegsComparison _ _ _ _ Rf RprojG RprojF RfSpace
    αf αprojG αprojF αfSpace
    (restrictionRingedSquareInducedAlgebraicSpaces B S hS F G p q hp hq hF hG eF eG
      fStack hfStack)
    (RingedToposHom.pushforwardComputesDerived_of_preservesKInjectiveModules _ _ _ _ hf)
    (pushforwardComputesDerived_smallEtaleRingedToposHom B S hS F G p q hp hF hG eF eG
      fStack hfStack RfSpace αfSpace)

/-- **Stacks 075N, clause (2).** For a complex `ℱ` of `𝒪_𝒳`-modules, the restriction of `Rf_*ℱ`
to the small étale site of `G` is `Rf_{small,*}` of the restriction of `ℱ` to the small étale
site of `F`, in `D(𝒪_G)`.

The two restriction functors appear **underived**, as they do in the source: they are the
functors `AlgebraicGeometry.RingedToposHom.derivedPushforwardOfExact` induced on derived
categories by the degreewise restrictions `π_{G,*}` and `π_{F,*}`, which are their own right
derived functors because they are exact
(`AlgebraicGeometry.RingedToposHom.isRightDerivedFunctor_derivedPushforwardOfExactUnit`). This
is the source's closing step, "because the restriction functors `π_{F,*}` and `π_{G,*}` are
exact".

The isomorphism is the canonical comparison
`AlgebraicGeometry.RingedToposHom.twoLegsComparison` of the two derived composites around the
square of Stacks 073N, which `isIso_restrictedDerivedDirectImageComparison` shows invertible;
it is not a chosen isomorphism of abstractly isomorphic functors.

Nothing beyond the source's data is a hypothesis. Exactness of the two restrictions is
`AlgebraicGeometry.Space.exactFunctor_pushforwardModules_projectionRingedToposHom`, found by
instance search. Stacks 093Y for degreewise `f_*` is not needed, the unit of the exact `π_{G,*}`
being invertible. The condition at the second leg is
`pushforwardComputesDerived_smallEtaleRingedToposHom`, from the unconditional Stacks 0D6E for a
morphism of ringed topoi. The square of Stacks 073N is
`AlgebraicGeometry.Space.restrictionRingedSquareInducedAlgebraicSpaces`.

Clause (1), for abelian sheaves, is
`AlgebraicGeometry.Space.restrictedAbelianDerivedDirectImageIso`, and the two clauses together
are `AlgebraicGeometry.Space.restrictedDerivedDirectImageIsoClauses`, which carries the tag. -/
def restrictedDerivedDirectImageIso :
    Rf ⋙ RingedToposHom.derivedPushforwardOfExact
        (projectionRingedToposHom B S hS G q hq hG eG) ≅
      RingedToposHom.derivedPushforwardOfExact
        (projectionRingedToposHom B S hS F p hp hF eF) ⋙ RfSpace :=
  have := RingedToposHom.isRightDerivedFunctor_derivedPushforwardOfExactUnit
    (projectionRingedToposHom B S hS G q hq hG eG)
  have := RingedToposHom.isRightDerivedFunctor_derivedPushforwardOfExactUnit
    (projectionRingedToposHom B S hS F p hp hF eF)
  have := RingedToposHom.isIso_derivedPushforwardOfExactUnit
    (projectionRingedToposHom B S hS G q hq hG eG)
  RingedToposHom.twoLegsIso
    (FibredSite.ringedToposMorphism B S hS p q hp hq fStack hfStack .etale)
    (projectionRingedToposHom B S hS G q hq hG eG)
    (projectionRingedToposHom B S hS F p hp hF eF)
    (smallEtaleRingedToposHom B S hS
      (inducedAlgebraicSpacesHom B S hS F G p q hF hG eF eG fStack hfStack)) Rf
    (RingedToposHom.derivedPushforwardOfExact
      (projectionRingedToposHom B S hS G q hq hG eG))
    (RingedToposHom.derivedPushforwardOfExact
      (projectionRingedToposHom B S hS F p hp hF eF))
    RfSpace αf
    (RingedToposHom.derivedPushforwardOfExactUnit
      (projectionRingedToposHom B S hS G q hq hG eG))
    (RingedToposHom.derivedPushforwardOfExactUnit
      (projectionRingedToposHom B S hS F p hp hF eF))
    αfSpace
    (restrictionRingedSquareInducedAlgebraicSpaces B S hS F G p q hp hq hF hG eF eG
      fStack hfStack)
    (RingedToposHom.pushforwardComputesDerived_of_isIso _ _ _ _)
    (pushforwardComputesDerived_smallEtaleRingedToposHom B S hS F G p q hp hF hG eF eG
      fStack hfStack RfSpace αfSpace)

end AlgebraicGeometry.Space

end
