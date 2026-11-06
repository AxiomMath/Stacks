module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardEssentialImage
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModule
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentials
import StacksCore.Tactic.StacksAttribute

/-!
# The conormal sequence of an immersion of algebraic spaces

Let `B` be an algebraic space over a scheme `S` and let `i : Z ⟶ X` be an immersion of algebraic
spaces over `B`, with structure morphism `b : X ⟶ B`.  Stacks 05ZA attaches to it a canonical
exact sequence
```
  𝒞_{Z/X} ⟶ i^*Ω_{X/B} ⟶ Ω_{Z/B} ⟶ 0
```
of sheaves of `𝒪_Z`-modules on the small étale site of `Z`, whose first arrow is "induced by
`d_{X/B}`" and whose second arrow is the comparison map of Stacks 04CX.

The source does not define the first arrow on an immersion directly: it replaces `X` by an open
subspace to make `i` a closed immersion, and then reads `d_{X/B}` on the defining ideal sheaf
`𝓘 ⊆ 𝒪_X` of `Z`.  That is what is done here, for a closed subspace `Z` of `X`.  The arrow for an
arbitrary immersion is in
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceImmersionFirstMap.lean`, where no such
reduction is needed.

## The construction of the first arrow

The conormal module of a closed subspace is `𝒞_{Z/X} = i^*𝓘`
(`AlgebraicGeometry.Space.conormalModule`), so by the adjunction `i^* ⊣ i_*` of Stacks 03LU a
morphism `𝒞_{Z/X} ⟶ i^*Ω_{X/B}` is the same thing as a morphism of `𝒪_X`-modules
`𝓘 ⟶ i_*i^*Ω_{X/B}`.  The latter is built from `d_{X/B}` in one step, and this is the step that
makes the arrow exist globally:

* composing `d_{X/B}` with the unit `Ω_{X/B} ⟶ i_*i^*Ω_{X/B}` of the adjunction gives a
  `B`-derivation `D` of `𝒪_X` with values in `i_*i^*Ω_{X/B}`
  (`AlgebraicGeometry.Space.conormalSequenceUnitDerivation`);
* `D` is only a derivation, not `𝒪_X`-linear, but its *restriction to `𝓘`* is linear: by the
  Leibniz rule `D(ra) = r·D(a) + a·D(r)` for a section `a` of `𝓘`, and the second summand
  vanishes because a direct image along a closed immersion is annihilated by the defining ideal
  sheaf — Stacks 04CJ, part (3), available here as
  `AlgebraicGeometry.Space.definingIdealAt_smul_modulePushforward_eq_zero`.

So no quotient is formed.  The source passes through `𝓘/𝓘² ⟶ Ω_{X/S}/𝓘Ω_{X/S}` and then across
the equivalence of Stacks 04CJ between `𝒪_Z`-modules and `𝒪_X`-modules annihilated by `𝓘`; the
route above uses only the annihilation half of that equivalence, and produces the same arrow
because `i^*𝓘 = 𝓘/𝓘²` is how `𝒞_{Z/X}` is realized here (see the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModule.lean`).

**Both halves of that equivalence are available in this development**, so the restriction to the
annihilation half is one of what this route needs and not of what the library has: `i_*` is fully
faithful by `AlgebraicGeometry.Space.fullyFaithfulModulePushforward` of
`StacksFrontier/AlgebraicGeometry/Spaces/ClosedImmersionModulePushforward.lean:192`, and its
essential image is exactly the annihilated modules by
`AlgebraicGeometry.Space.essImage_modulePushforward_iff` of
`StacksFrontier/AlgebraicGeometry/Spaces/ClosedImmersionModuleEssentialImage.lean:331`, which
carries `@[stacks 08KS]` and is unconditional in `IsClosedImmersion`.

## Main definitions

* `AlgebraicGeometry.Space.submoduleDerivationHom` and
  `AlgebraicGeometry.Space.conormalSequenceIdealHom`: the restriction to a sheaf of ideals, and to
  the defining ideal sheaf of a closed subspace, of a derivation of `𝒪_X` whose values that ideal
  sheaf annihilates, as a morphism of `𝒪_X`-modules.  This is the one place where linearity is
  checked.
* `AlgebraicGeometry.Space.pullbackUnitDerivation`: `d_{X/B}` followed by the unit of
  `f^* ⊣ f_*`, for a morphism `f` of algebraic spaces left as a variable.  Its implementation
  notes say why the variable matters.
* `AlgebraicGeometry.Space.conormalSequenceUnitDerivation`: the `B`-derivation `D` above, which
  is the previous one at the inclusion of `Z`.
* `AlgebraicGeometry.Space.conormalSequenceIdealDifferential`: the adjoint form of the first
  arrow, the morphism of `𝒪_X`-modules `𝓘 ⟶ i_*i^*Ω_{X/B}` obtained by restricting `D` to `𝓘`.
* `AlgebraicGeometry.Space.submoduleTranspose`: the transposition along `f^* ⊣ f_*` of a
  morphism out of a subsheaf of the structure sheaf, named so that a consumer of the first arrow
  need not write it out.
* `AlgebraicGeometry.Space.conormalSequenceIdealPullbackMap` and
  `AlgebraicGeometry.Space.conormalSequenceFirstMap`: **Stacks 05ZA**, the first arrow
  `𝒞_{Z/X} ⟶ i^*Ω_{X/B}`, the transpose of the previous one.  The two differ only in how the
  source is written: `i^*𝓘` and `𝒞_{Z/X}`, which are equal by
  `AlgebraicGeometry.Space.conormalModule_eq`.

## Main results

* `AlgebraicGeometry.Space.conormalSequenceIdealDifferential_val_app_apply`: **Stacks 05ZA**, the
  sense in which the first arrow is induced by `d_{X/B}`.  The first arrow is by definition the
  transpose of `conormalSequenceIdealDifferential`, and that morphism carries a section `a` of
  `𝓘` to `D(a)`, that is, to `d_{X/B}(a)` followed by the unit.  Since the transposition is a
  bijection, this determines the arrow.
* `AlgebraicGeometry.Space.definingIdealAt_smul_modulePushforward_eq_zero`: the annihilation
  statement of Stacks 04CJ, part (3), in the form the linearity check consumes.
* `AlgebraicGeometry.Space.homEquiv_submoduleTranspose`: transposing
  `AlgebraicGeometry.Space.submoduleTranspose` back recovers the morphism out of the sheaf of
  ideals, so that a consumer may read the first arrow through its adjoint form.

The second arrow is not constructed here and not imported here: Stacks 05ZA does not construct
it either, it is the comparison map of Stacks 04CX for the square over the identity of `B`, which
`AlgebraicGeometry.Space.pullbackDifferentialsMap` already is.  It is registered under this tag
in `StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceSecondMap.lean`, a module that exists
only to carry that registration.

That module's implementation notes say the construction of the first arrow and the module
defining the second arrow cannot be loaded into one Lean process together.  **The two import
surfaces do compose.**  `ConormalSequenceDerivationVanishing.lean` imports this module together
with `StacksFrontier/AlgebraicGeometry/Spaces/RelativeDifferentialsTriangle.lean`, where the second
arrow is defined, and compiles — as its own implementation notes record at `:80-85`.  The 2.8 GB
measurement behind the separate module was taken against an import surface containing
`StacksFrontier/AlgebraicGeometry/Spaces/ClosedImmersionModulePushforward.lean`, which this module
does not have, for the reason the implementation notes below give.  So a statement mentioning both
arrows has a home one import away, and
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceComplex.lean` is where the one that exists
lives.

## Implementation notes

**One adjunction, and it is the one both arrows live in.**  The first arrow is built as a
transpose along `AlgebraicGeometry.Space.modulePullbackAdjunction`, the adjunction `i^* ⊣ i_*`
with `AlgebraicGeometry.Space.modulePushforward` as right adjoint.  That is where the
annihilation statement of Stacks 04CJ applies — it is about
`AlgebraicGeometry.Space.modulePushforward` — and it is also the adjunction through which
Stacks 04CX's characterizing property `AlgebraicGeometry.Space.IsSheafOfDifferentialsMap` is
stated, so the second arrow, the comparison map
`AlgebraicGeometry.Space.sheafOfDifferentialsMap` of
`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsMap.lean`, is transposed along the same
adjunction.  No comparison of two forms of the direct image of modules occurs anywhere in the
sequence.

**The import surface is kept small on purpose.**  The environment these statements need is itself
most of the memory a single Lean process is given, so this file imports the lemma that
Stacks 04CJ, part (3) is proved from —
`Stacks.Sheaves.PushforwardEssentialImage.smul_restrictScalars_eq_zero` — rather than
`StacksFrontier/AlgebraicGeometry/Spaces/ClosedImmersionModulePushforward.lean`, which
carries that part of 04CJ but drags in the coherent and quasi-coherent module theory with it.
With that module imported the file needs more than about 2.8 GB; without it the same
declarations compile.  This is why the second arrow's registration is in its own module; it does
*not* mean the second arrow cannot be imported here (see the paragraph on the second arrow above).

**Why the statements are made at `i^*𝓘` and not at `𝒞_{Z/X}`.**  Every statement about the first
arrow applies the transposition to it, and the transposition expects its argument to be a morphism
out of `i^*𝓘`.  At the `𝒞_{Z/X}` reading of the source each such application re-checks the
equality of the two sheaves of modules, and that check does not fit in the default heartbeat
budget, so the statements are made at the `i^*𝓘` reading and
`AlgebraicGeometry.Space.conormalSequenceFirstMap` is the same morphism with its source written
the other way.

**How the annihilation hypotheses get the scalar action.**  The `ModuleCat` index of
`N.val.obj U` comes from `AlgebraicGeometry.Space.Modules` and so carries
`(smallEtaleRingedSite B S hS X.1 X.2).J`, whereas
`AlgebraicGeometry.Space.structureRingSheaf B S hS X` is
`Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O` read over
`AlgebraicGeometry.Space.SmallEtale.topology B S hS X.1`, and that constructor is a plain
definition, so instance search — which runs at `instances` transparency and does not unfold it —
finds no `SMul` for `a • m` when the scalar is written at the `structureRingSheaf` spelling; the
membership `a ∈ definingIdealAt B S hS X Z U` still elaborates, because unification there runs at
default transparency.  There are therefore two ways the statements below supply the action, and
both are in use.

`AlgebraicGeometry.Space.conormalSequenceIdealHom`,
`AlgebraicGeometry.Space.conormalSequenceIdealHom_val_app_apply` and
`AlgebraicGeometry.Space.definingIdealAt_smul_modulePushforward_eq_zero` write the scalar at
`Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O` itself, which
records the topology the way the module's index does, so search succeeds and nothing has to be
seated.  The statements that write it at the `structureRingSheaf` spelling instead — starting with
`AlgebraicGeometry.Space.submoduleDerivationHom` — name the section module's own canonical
structure `CategoryTheory.ModuleCat.isModule` in a `letI`.  The bound value is term-identical to
the canonical instance, so no second module structure exists, and `letI` zeta-reduces, so the
proposition is the same one; this is the device
`AlgebraicGeometry.Space.AnnihilatedByKerIdeal` of
`StacksFrontier/AlgebraicGeometry/Spaces/ClosedImmersionModulePushforward.lean` already uses for the
same statement.  In the proof of `AlgebraicGeometry.Space.submoduleDerivationHom` the scalar
instead arrives from the `homMk` goal, so the Leibniz step is taken with
`congrArg (HAdd.hAdd _)`, which reuses the summand the derivation's own `d_mul` produced rather
than writing `r • d(a)` out a second time.

**The universes** are those of the small étale site, `RingedSite.{u + 1, u, u}` with modules
`Modules.{u, u}`, as everywhere in this part of the development.

## What is not proved

* **What this file establishes is the *construction* of the first arrow and the sense in which
  `d_{X/B}` induces it.**  The two other clauses of the displayed sequence are proved, but
  elsewhere, and neither is proved here.
  * *Exactness at the right term* — that the second arrow is an epimorphism — is
    `AlgebraicGeometry.Space.epi_pullbackDifferentialsMap_of_isLocallySurjective` of
    `StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceDifferentialsEpi.lean`; it needs the
    comparison map and the transposition of derivations, and not the conormal module, so it is a
    separate module.
  * *The composite of the two arrows is zero* is
    `AlgebraicGeometry.Space.conormalSequenceFirstMap_comp_pullbackDifferentialsMap` of
    `StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceComplex.lean`, unconditionally.  It is
    not in this file because it mentions the second arrow, which this file does not import — not
    because it could not; and the three steps of its reduction are cut into separate named
    lemmas there, because
    at these concrete small étale ringed topoi none of them fits the default heartbeat budget
    when it is left to unification — the identification of
    `AlgebraicGeometry.Space.conormalSequenceUnitDerivation` with the universal derivation
    followed by the unit of the adjunction (`PresheafOfModulesOfCommRing.Derivation.postcomp_d_apply`), the
    naturality `CategoryTheory.Adjunction.homEquiv_naturality_right_symm` of the transposition,
    and the identification of `AlgebraicGeometry.Space.conormalSequenceFirstMap` with
    `AlgebraicGeometry.Space.conormalSequenceIdealPullbackMap`.  Delta-reducing the two
    definitions syntactically and applying each step at explicit arguments keeps every one of
    them inside the budget, so no compiler option is raised.
* **Exactness at the middle term is proved, unconditionally for a closed subspace**, and
  **it cannot be registered in this module**: the clause has to be stated of the short complex
  built from the two arrows, whose vanishing composite is
  `AlgebraicGeometry.Space.conormalSequenceFirstMap_comp_pullbackDifferentialsMap`
  of `StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceComplex.lean`, and that module imports
  `StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceDerivationVanishing.lean`, which imports
  this one.  Its home is therefore `ConormalSequenceComplex.lean` or a module above it, and that
  is where it lives: `AlgebraicGeometry.Space.exact_conormalSequence` of
  `StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceThickeningDescent.lean`, which carries
  the `@[stacks 05ZA]` attribute for the middle clause.  The consumers of the clause used to
  carry it as `h05ZA` — two binders in `ConormalSequenceUnramifiedPair.lean`, one in
  `ConormalSequenceFormallyUnramified.lean` and three in
  `ConormalSequenceFormallySmoothSplitting.lean` — and **none of them does any more**, through
  `AlgebraicGeometry.Space.exact_conormalSequence_universalThickening`.  The source gets the
  clause by étale localization to the scheme case, Morphisms, Lemma 01UZ, through Stacks 04CU and
  04CO; that route is **not** the one taken, and the record of what it would need is kept below
  because it is also what a comparison of the first arrows would serve:
  * the scheme case with the conormal sheaf itself at the left-hand end is
    `Stacks.ConormalSequenceRight.conormalShortComplex_exact` of
    `StacksFrontier/AlgebraicGeometry/ConormalSequenceRight/SchemeShortExact.lean`, unconditional in
    `IsImmersion`, for the first arrow `Stacks.ConormalSequenceRight.conormalDifferential` of
    `StacksFrontier/AlgebraicGeometry/ConormalSequenceRight/Basic.lean`.  (The equation-presented
    `Stacks.ConormalSequenceRight.equationDifferentialsComplexOver_exact` of
    `ConormalSequenceRight/Middle.lean` has the free module on a family of equations as its
    left-hand term, and that file's implementation notes still say no morphism
    `𝒞_{Z/X} ⟶ i^*Ω_{X/S}` exists at the scheme level; both statements are stale.)
  * the comparison of `Ω_{X/Y}` read on the small étale site with the Zariski sheaf of
    differentials of a morphism of schemes of the site is
    `AlgebraicGeometry.Space.sheafOfDifferentialsSchemeComparison` of
    `StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsSchemeTransport.lean`, registered
    there under Stacks 04CS and under Stacks 04CU, with the chart form
    `AlgebraicGeometry.Space.modulePullbackSheafOfDifferentialsChartIso`.

  What is missing is the *comparison of the first arrows*: no declaration identifies
  `AlgebraicGeometry.Space.conormalSequenceFirstMap` restricted to an affine étale chart with
  `Stacks.ConormalSequenceRight.conormalDifferential` of that chart.  The comparison of the
  left-hand *objects* is not missing: `AlgebraicGeometry.Space.conormalModule` restricted to an
  étale scheme chart is the scheme conormal sheaf of the base change of the inclusion along that
  chart, by `AlgebraicGeometry.Space.modulePullbackConormalModuleChartConormalSheafIso` of
  `StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleChartConormalSheaf.lean:600`.

  The last step of the reduction is proved —
  `AlgebraicGeometry.Space.exact_of_exact_modulePullback_schemeChart` of
  `StacksFrontier/AlgebraicGeometry/Spaces/ModulePullbackSchemeChartExactness.lean:150` descends
  exactness of a short complex of modules along a surjective étale scheme chart.

  **How much of that comparison exactness needs.**  Identifying the three *objects* is
  not enough, and neither is identifying them together with the right-hand square.  Isomorphisms
  `α₁, α₂, α₃` of the three terms and a commuting right-hand square give, from the
  composite-is-zero clause alone, only one containment: the image of the transported first arrow
  lands in the kernel of the scheme-level second arrow, which is the scheme-level first arrow's
  image.  The reverse containment does not follow — in `Ab`, `ℤ --0--> ℤ --0--> 0` and
  `ℤ --𝟙--> ℤ --0--> 0` have isomorphic terms and the same right-hand square, the second is exact
  at the middle and the first is not.  What *does* suffice is strictly weaker than identifying
  the canonical map: the one remaining containment of images, that
  `Stacks.ConormalSequenceRight.conormalDifferential` of the chart factors through `α₂` composed
  with the chart inverse image of `AlgebraicGeometry.Space.conormalSequenceFirstMap`.  Equality
  of the two canonical maps — whose proof needs
  `Stacks.Immersion.IsInducedConormalSheafMap` of
  `StacksFrontier/AlgebraicGeometry/Thickenings/UniversalConormalGenerators.lean:403` and
  `Stacks.Immersion.immersionConormalSheafMap_unique` of
  `StacksFrontier/AlgebraicGeometry/Conormal/SquareMap.lean:319`, because `ε^*` of a monomorphism is
  not preserved by `i^*` along a closed immersion and the mono-cancellation handle therefore does
  not survive the inverse image — is not needed for exactness.

  **That containment is no longer blocked at the left-hand object.**  It needs a morphism
  between the two left-hand terms, and one exists, at exactly the generality of the statements
  below: `AlgebraicGeometry.Space.modulePullbackConormalModuleChartConormalSheafIso` of
  `StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleChartConormalSheaf.lean:600` identifies
  the inverse image of `𝒞_{Z/X}` along an étale scheme chart of `X` with `ε^*` of the scheme
  conormal sheaf `Stacks.ClosedImmersion.conormalSheaf` of the base change of the inclusion
  along that chart, which is a closed immersion of schemes.  For an arbitrary immersion the
  same identification is Stacks 04CO,
  `AlgebraicGeometry.Space.conormalModuleSchemeEtaleRestriction` of
  `StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleSchemeEtaleRestriction.lean:245`, with
  `AlgebraicGeometry.Space.isIso_conormalModuleSchemeEtaleRestriction` at `:154` of that file
  for the invertibility; the closed case read against `Stacks.Conormal.conormalSheaf` on the
  small étale site is part (1) of Stacks 04G2,
  `AlgebraicGeometry.Space.conormalModuleClosedSubspaceRangeIso` of
  `StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleSchemeAgreement.lean:425`.  The chart
  comparison for the *ideal sheaf* is a separate statement and also available:
  `AlgebraicGeometry.Space.chartModulePullbackDefiningIdealSheafIso` of
  `StacksFrontier/AlgebraicGeometry/Spaces/RepresentedIdealModuleComparison.lean:262` identifies the
  inverse image of `𝓘` along an étale chart of `X` with the represented reading of the Zariski
  ideal sheaf of the chart, unconditionally and with no surjectivity hypothesis.  The
  re-anchoring of the subspace along
  `CategoryTheory.Subfunctor.range (yoneda.map j) ≅ yoneda.obj R` is what
  `AlgebraicGeometry.Space.rangeSpaceIso` of
  `StacksFrontier/AlgebraicGeometry/Spaces/RepresentedClosedSubspaceIdeal.lean:101` performs inside
  the 04G2 comparison.  So the blockage of this route is at the comparison of the first arrows
  above, not at the left-hand object, not at the right-hand square and not at a canonical-map
  characterisation.
  The scheme-level input is `Stacks.ConormalSequenceRight.conormalShortComplex_exact` of
  `StacksFrontier/AlgebraicGeometry/ConormalSequenceRight/SchemeShortExact.lean:389` as recorded
  above; `Stacks.Thickenings.transitivityConormalShortComplex_exact` of
  `StacksFrontier/AlgebraicGeometry/Thickenings/TransitivityConormal.lean:669` is **not** an
  alternative to it — that is 06AE, part (2), whose sequence is `i^*𝒞_{Y/X} ⟶ 𝒞_{Z/X} ⟶ 𝒞_{Z/Y}`
  and has a conormal module, not a sheaf of differentials, in its right-hand term.
* **A second route to exactness at the middle term exists, and bottoms out elsewhere.**  Together
  with exactness at the right term, exactness at the middle says exactly that the second arrow is
  a *cokernel* of the first; exactness at the right term is proved
  (`AlgebraicGeometry.Space.epi_pullbackDifferentialsMap_of_isLocallySurjective` of
  `ConormalSequenceDifferentialsEpi.lean`), so the uniqueness half of that colimit is free and
  only the factorization has to be produced: every morphism `h : i^*Ω_{X/B} ⟶ M` of
  `𝒪_Z`-modules killed by the first arrow factors through the second.  Transposing along
  `i^* ⊣ i_*` and applying `AlgebraicGeometry.Space.universalDerivation_isUniversal` at both ends,
  with `AlgebraicGeometry.Space.IsSheafOfDifferentialsMap` pinning the second arrow and
  `conormalSequenceIdealDifferential_val_app_apply` above pinning the first, turns that into one
  statement about derivations: *for every `𝒪_Z`-module `M`, precomposition with `i♯` carries the
  `B`-derivations of `𝒪_Z` with values in `M` bijectively onto the `B`-derivations of `𝒪_X` with
  values in `i_*M` which vanish on `𝓘`.*  The equivalence of Stacks 04CJ does not give this, both
  halves notwithstanding: a derivation is not a morphism of modules, and descending one along the
  locally surjective `i♯` needs `𝒪_X ⟶ i_*𝒪_Z` to be a cokernel of `𝓘 ⟶ 𝒪_X` in sheaves of
  *abelian groups*, whereas the cokernel in `Modules` is
  `AlgebraicGeometry.Space.isColimitCokernelCofork` of
  `StacksFrontier/AlgebraicGeometry/Spaces/ConormalAlgebraDegreeZero.lean:216`, over
  `AlgebraicGeometry.Space.ker_structureProjection` and
  `AlgebraicGeometry.Space.epi_structureProjection`.

  **That cokernel in sheaves of abelian groups is now proved**, so this route no longer bottoms
  out there: `AlgebraicGeometry.Space.isColimitAbelianCokernelCofork` of
  `StacksFrontier/AlgebraicGeometry/Spaces/DefiningIdealAbelianCokernel.lean`, over the short
  exactness `AlgebraicGeometry.Space.definingIdealAbelianShortComplex_shortExact` there, with
  `AlgebraicGeometry.Space.abelianDesc` as the factorization a consumer calls.  **The bridge
  `PreservesFiniteColimits (SheafOfModules.toSheaf _)` is not what that needs**, and the record
  that it is was wrong: Mathlib proves the *limits* half, the inclusion of the ideal is a kernel of
  the structure projection on the nose, and
  `Stacks.SheafOfModules.EpiMono.epi_toSheaf_map` of
  `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/EpiLocallySurjective.lean:168` supplies the
  epimorphism, so short exactness — hence the cokernel — follows for this one sequence without it.
  That general bridge is indeed still carried as a hypothesis at
  `StacksFrontier/Homology/DerivedCategory/InverseSystem/ModuleInverseLimitGlobalSections.lean:705`,
  and Mathlib does not supply it: `Mathlib/Algebra/Category/ModuleCat/Sheaf/Limits.lean` has
  `PreservesFiniteLimits (SheafOfModules.toSheaf R)` and
  `Mathlib/Algebra/Category/ModuleCat/Sheaf/Colimits.lean` has no preservation statement at all,
  the only other instances on that functor being `Faithful` and `Additive`.  It is simply not
  needed here.

  **What this route still needs.**  Having the additive factorization, the step left is
  to read it as a derivation of `𝒪_Z`, and that is a transport of derivations along the direct
  image.

  **The transport itself is now proved, and the whole reduction with it.**  The direct image
  `f_*D ∘ f♯` of an arbitrary derivation is
  `AlgebraicGeometry.Space.pushforwardDerivation` of
  `StacksFrontier/AlgebraicGeometry/Spaces/PushforwardDerivation.lean`, which also proves that
  **precomposition with the second arrow is that transport** —
  `AlgebraicGeometry.Space.derivationDirectImageEquiv_sheafOfDifferentialsMap_comp` — and
  `AlgebraicGeometry.Space.exact_conormalSequence_of_exists_pushforwardDerivation` of
  `StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceMiddleExactness.lean` assembles the
  cokernel from it.  So the clause reduced to **exactly one statement**, the `hdesc`
  of that theorem: *for every `𝒪_Z`-module `M`, every `B`-derivation of `𝒪_X` with values in
  `i_*M` which vanishes on every local section of `𝓘` is the direct image of a `B`-derivation of
  `𝒪_Z` with values in `M`.*  The *injectivity* half of the bijection this paragraph used to
  demand is not needed: it is the epimorphism at the right, which is proved — and, for a closed
  subspace, unconditionally, by
  `AlgebraicGeometry.Space.epi_pullbackDifferentialsMap_subspaceInclusion` in that module.

  **And `hdesc` is now discharged, unconditionally for a closed subspace**, which closes this
  route: `AlgebraicGeometry.Space.exists_conormalPushforwardDerivation_eq` of
  `StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceThickeningDescent.lean` is `hdesc`, and
  `AlgebraicGeometry.Space.exact_conormalSequence` there is the clause.  The one step of the
  derivation data that uses anything about the inclusion is
  `AlgebraicGeometry.Space.inverseImageDerivationFun_eq_zero_of_app_eq_zero` of
  `ConormalSequenceThickeningKernelVanishing.lean`, the vanishing of the transpose of the
  derivation on the sections killed by `i^♯` in inverse-image form, and what it uses is that `i`
  is a closed immersion: `𝓘` is presented as the fibre of `i^♯` over the zero section of sheaves
  of sets by `AlgebraicGeometry.Space.isPullback_definingIdealSheaf` of
  `StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceDefiningIdealFibreSquare.lean`, carried
  through `i^{-1}` by left exactness, and the counit `i^{-1}i_*𝒪_Z ⟶ 𝒪_Z` — invertible for a
  closed immersion by Stacks 04E5, part (1) — identifies the two kernels.  Every other step of
  the route is proved for an arbitrary morphism of algebraic spaces.

  Two corrections to what this paragraph said before.  Equation 0619,
  `AlgebraicGeometry.Space.derivationDirectImageEquiv`, *already* supplies the bijection
  `Hom(i^*Ω_{X/B}, M) ≃ Der_B(𝒪_X, i_*M)`, so what was owed was never a transport bijection but
  only the surjectivity above.  And
  `Stacks.Sheaves.Differentials.directImageDerivationEquiv` of
  `StacksFrontier/CategoryTheory/Sites/Modules/DifferentialsInverseImage.lean:442` is not merely
  "the bijection for the *inverse-image* ring sheaf": it asks for
  `[CategoryTheory.SmallCategory C]` and `[CategoryTheory.SmallCategory D]`, and the small étale
  site has its objects in `Type (u + 1)` and its morphisms in `Type u` (verified by
  elaboration), so it does not apply at these sites at all, whichever ring sheaf it is stated
  for.

  **What `hdesc` needs.**  A section of `𝒪_Z` over an object `V` of the small étale
  site of `Z` is not in the image of any structure map in general, so the derivation of `𝒪_Z`
  has to be glued from the data on the base-changed objects; the full faithfulness that would
  make that possible is available at *any* coefficients,
  `AlgebraicGeometry.Space.fullyFaithfulSmallEtaleRestriction` of
  `StacksFrontier/AlgebraicGeometry/Spaces/SmallEtalePushforwardFullyFaithful.lean:166`, and at
  abelian coefficients it carries `@[stacks 04E5 "part (2)"]` —
  `AlgebraicGeometry.Space.fullyFaithfulSmallEtaleAbelianPushforwardOfIsClosedImmersion` of
  `StacksFrontier/AlgebraicGeometry/Spaces/ClosedImmersionChartBaseChangeDense.lean:388`, at a
  *free* coefficient universe and conditional only on `IsClosedImmersion`, with its counit
  isomorphism at `:409`; the module-level Stacks 04CJ is derived from the sets-valued form of
  the same statement at `:354`.  But that direct image is *restriction along the chart
  base-change functor*, and the one in the sequence is
  `AlgebraicGeometry.Space.modulePushforward`, built from the right Kan extension
  `AlgebraicGeometry.Space.smallEtaleDirectImageRan`.  The comparison of the two exists at
  sheaves of modules — `AlgebraicGeometry.Space.modulePushforwardChartIso` of
  `StacksFrontier/AlgebraicGeometry/Spaces/ModulePushforwardChartComparison.lean:518`, with
  `AlgebraicGeometry.Space.modulePushforwardIsoChartDirectImage` at `:545` for a closed
  immersion and `AlgebraicGeometry.Space.isIso_chartRanApp` at `:322` for the sections — and at
  sheaves of sets and of commutative rings
  (`AlgebraicGeometry.Space.smallEtaleRingedToposHom_representable` and
  `AlgebraicGeometry.Space.smallEtaleRingedToposHom_representableRing` of
  `StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleRingedToposHom.lean`).  **It now exists at
  sheaves of abelian groups as well**, which is the one category 04E5, part (2) is stated in:
  `AlgebraicGeometry.Space.abelianPushforwardChartIso` of
  `StacksFrontier/AlgebraicGeometry/Spaces/ModulePushforwardAbelianChartComparison.lean:114`, with
  `AlgebraicGeometry.Space.abelianPushforwardChartIso_hom_app` at `:134` reading it as the
  module-level comparison forgotten (by `rfl`), and 04E5, part (2) read through it as
  `AlgebraicGeometry.Space.abelianPushforwardPreimage` at `:157` — for a closed immersion every
  morphism `i_*M ⟶ i_*N` of sheaves of abelian groups is the direct image of a unique morphism
  `M ⟶ N` of abelian sheaves.  So the two inputs this bullet recorded as unconnected are
  connected; what the pair delivers, over the additive factorization through `𝒪_X ⟶ i_*𝒪_Z`
  (`AlgebraicGeometry.Space.abelianDesc` of
  `StacksFrontier/AlgebraicGeometry/Spaces/DefiningIdealAbelianCokernel.lean`), is an additive
  morphism `χ : 𝒪_Z ⟶ M` of abelian sheaves and nothing more.  Leibniz for that descended map is
  still owed, and it is a separatedness argument of the shape
  `AlgebraicGeometry.Space.epi_pullbackDifferentialsMap_of_isLocallySurjective` already makes,
  not a gluing one; the *What is not proved* section of
  `StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceMiddleExactness.lean` states what is left
  in the shape that module's reduction wants it, with the declarations that would do it.
* **The reduction of an immersion to a closed immersion is not performed here**, so every
  statement below is for a closed subspace.  This is the restriction that
  `StacksFrontier/AlgebraicGeometry/Spaces/ConormalModule.lean` records for Stacks 04CN — and that
  file records it as *not* for want of the open subspace, because both the open subspace
  `X ∖ ∂Z` and the factorization through it exist in this development:
  `AlgebraicGeometry.Space.boundaryComplement` of
  `StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/Immersions.lean:387` carries Stacks 06EC and
  `AlgebraicGeometry.Space.exists_isClosedImmersion_comp_ι_boundaryComplement` at `:767` of the
  same file carries Stacks 04CE, with the choice-free form
  `AlgebraicGeometry.Space.immersionClosedFactorization` into
  `AlgebraicGeometry.Space.immersionAmbient` at
  `StacksFrontier/AlgebraicGeometry/Spaces/ConormalAlgebra.lean:309` and `:301`.  What keeps the
  statements below closed is instead that `AlgebraicGeometry.Space.conormalModule` — hence the
  source of the first arrow — is defined only for a closed subspace; the immersion-level object
  is `AlgebraicGeometry.Space.conormalModuleOfImmersion` at `ConormalAlgebra.lean:428`.  This is
  also the case the source itself reduces to before explaining what "induced by `d_{X/B}`"
  means.
* **Elsewhere the clauses are proved for an arbitrary immersion**, where the reduction absent
  here is performed, together with a second form of the composite.  Each of these carries nothing
  beyond the immersion.
  * *The composite is zero*, in the form consumed by the immersion route:
    `AlgebraicGeometry.Space.conormalSequenceFirstMap_comp_pullbackDifferentialsMap_eq_zero` of
    `StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceCompositeZero.lean`.
  * *Exactness at the right term*:
    `AlgebraicGeometry.Space.epi_pullbackDifferentialsMap_of_isImmersion` of
    `StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceEpiImmersion.lean`.
  * *The first arrow for an arbitrary immersion*, and the vanishing of its composite:
    `AlgebraicGeometry.Space.conormalSequenceFirstMapOfImmersion` of
    `StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceImmersionFirstMap.lean`.  The reduction
    of an immersion to a closed immersion is not performed there; it is not needed, since the
    arrow is built from the kernel ideal sheaf of an arbitrary morphism in
    `StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceKernelIdeal.lean` and the source is
    identified with the conormal module by Stacks 09RR, inside which the reduction of Stacks 04CE
    is carried out.
  * *Exactness at the middle term for an arbitrary immersion*:
    `AlgebraicGeometry.Space.conormalSequenceOfImmersion_exact` of
    `StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceImmersionKernelExactness.lean`, which
    performs the open-subspace reduction of Stacks 04CE; for a closed subspace the clause is also
    stated at `AlgebraicGeometry.Space.conormalSequenceFirstMap` as
    `AlgebraicGeometry.Space.conormalSequence_exact` of
    `StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceMiddleExactnessAt.lean`.

## References

* [Stacks Project, Tag 05ZA](https://stacks.math.columbia.edu/tag/05ZA)
* [Stacks Project, Tag 04CN](https://stacks.math.columbia.edu/tag/04CN), the conormal module.
* [Stacks Project, Tag 04CJ](https://stacks.math.columbia.edu/tag/04CJ), direct image along a
  closed immersion and annihilation by the defining ideal.
* [Stacks Project, Tag 04CX](https://stacks.math.columbia.edu/tag/04CX), the comparison map of a
  commutative square.
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB), the defining ideal sheaf
  of a closed subspace.
* [Stacks Project, Tag 01UZ](https://stacks.math.columbia.edu/tag/01UZ), the scheme case.
-/

@[expose] public section

open CategoryTheory Opposite
open Stacks.Sheaves.RingedToposModules

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Ideal

variable {X : AlgebraicSpaces B S hS}

/-- **The restriction of a derivation to a sheaf of ideals that annihilates its values.**  Let
`𝓘 ⊆ 𝒪_X` be a subsheaf of the structure sheaf of an algebraic space `X` and let `D` be a
derivation of `𝒪_X` with values in an `𝒪_X`-module `N` which `𝓘` annihilates.  Then `D`
restricted to `𝓘` is a morphism of `𝒪_X`-modules `𝓘 ⟶ N`.

A derivation is additive and commutes with restriction, so the only thing to check is linearity,
and the Leibniz rule gives `D(ra) = r·D(a) + a·D(r)` with the second summand killed by the
annihilation hypothesis.  This is the one step in the construction of the first arrow of
Stacks 05ZA at which the ideal is used. -/
noncomputable def submoduleDerivationHom
    (I : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    {A : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u}}
    {φ : A ⟶ (smallEtaleRingedTopos B S hS X).O}
    (N : Modules.{u, u} B S hS X.1 X.2) (D : PresheafOfModulesOfCommRing.Derivation' N.val φ.hom)
    (hann : ∀ (U : (SmallEtale B S hS X.1)ᵒᵖ)
      (a : ToType ((structureRingSheaf B S hS X).obj.obj U)),
      a ∈ I.obj U →
        letI : Module ((structureRingSheaf B S hS X).obj.obj U) (N.val.obj U) :=
          (N.val.obj U).isModule
        ∀ m : N.val.obj U, a • m = 0) :
    I.toSheafOfModules ⟶ N where
  val := PresheafOfModules.homMk
    { app := fun U ↦ AddCommGrpCat.ofHom (D.d.comp ((I.obj U).subtype.toAddMonoidHom))
      naturality := by
        intro U V g
        ext x
        exact D.d_map g x.1 }
    (by
      intro U r m
      refine (D.d_mul r m.1).trans (Eq.trans
        (congrArg (HAdd.hAdd _) (hann U m.1 m.2 (D.d r))) (add_zero _)))

/-- **The restriction of a derivation to a defining ideal sheaf.**  Let `Z` be a closed subspace
of an algebraic space `X` with defining ideal sheaf `𝓘 ⊆ 𝒪_X`, and let `D` be a derivation of
`𝒪_X` with values in an `𝒪_X`-module `N` which `𝓘` annihilates.  Then `D` restricted to `𝓘` is a
morphism of `𝒪_X`-modules `𝓘 ⟶ N`.

A derivation is additive and commutes with restriction, so the only thing to check is linearity,
and the Leibniz rule gives `D(ra) = r·D(a) + a·D(r)` with the second summand killed by the
annihilation hypothesis.  This is the one step in the construction of the first arrow of
Stacks 05ZA at which the ideal is used. -/
noncomputable def conormalSequenceIdealHom (Z : ClosedSubspaces B S hS X.1)
    {A : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u}}
    {φ : A ⟶ (smallEtaleRingedTopos B S hS X).O}
    (N : Modules.{u, u} B S hS X.1 X.2) (D : PresheafOfModulesOfCommRing.Derivation' N.val φ.hom)
    (hann : ∀ (U : (SmallEtale B S hS X.1)ᵒᵖ)
      (a : (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O).obj.obj U),
      a ∈ definingIdealAt B S hS X Z U → ∀ m : N.val.obj U, a • m = 0) :
    (definingIdealSheaf B S hS X Z).toSheafOfModules ⟶ N :=
  submoduleDerivationHom B S hS (definingIdealSheaf B S hS X Z) N D hann

/-- The value of `AlgebraicGeometry.Space.conormalSequenceIdealHom` on a section of the defining
ideal sheaf is the value of the derivation on that section, read in `𝒪_X`. -/
theorem conormalSequenceIdealHom_val_app_apply (Z : ClosedSubspaces B S hS X.1)
    {A : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u}}
    {φ : A ⟶ (smallEtaleRingedTopos B S hS X).O}
    (N : Modules.{u, u} B S hS X.1 X.2) (D : PresheafOfModulesOfCommRing.Derivation' N.val φ.hom)
    (hann : ∀ (U : (SmallEtale B S hS X.1)ᵒᵖ)
      (a : (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O).obj.obj U),
      a ∈ definingIdealAt B S hS X Z U → ∀ m : N.val.obj U, a • m = 0)
    (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (x : (definingIdealSheaf B S hS X Z).toSheafOfModules.val.obj U) :
    ((conormalSequenceIdealHom B S hS Z N D hann).val.app U).hom x = D.d x.1 :=
  rfl

/-- **Stacks 04CJ, part (3), in the form the first arrow of Stacks 05ZA consumes.**  A section of
the defining ideal sheaf of a closed subspace `Z ⊆ X` annihilates every section of a direct image
along the inclusion of `Z`.

The direct image of modules is the Stacks 03D1 direct image followed by restriction of scalars
along the structure map of the inclusion (`AlgebraicGeometry.Space.modulePushforward_eq`), so a
section of `𝒪_X` acts on it through that structure map; and the defining ideal sheaf is exactly
the kernel of that map, by `AlgebraicGeometry.Space.mem_definingIdealAt_iff`.  This is the same
statement as `AlgebraicGeometry.Space.annihilatedByKerIdeal_modulePushforward`, with the same
one-line proof, restated here against the ideal sheaf rather than
`CategoryTheory.SheafOfModules.kerIdeal`: that declaration's module cannot be imported here, for
the reason the implementation notes of this file record. -/
theorem definingIdealAt_smul_modulePushforward_eq_zero (Z : ClosedSubspaces B S hS X.1)
    (G : Modules.{u, u} B S hS Z.1.toFunctor Z.2.1) (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (a : (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X.1 X.2).O).obj.obj U)
    (ha : a ∈ definingIdealAt B S hS X Z U)
    (m : ((modulePushforward B S hS (subspaceInclusion B S hS X Z)).obj G).val.obj U) :
    a • m = 0 :=
  Stacks.Sheaves.PushforwardEssentialImage.smul_restrictScalars_eq_zero
    (structureSharp B S hS (subspaceInclusion B S hS X Z))
    ((moduleDirectImage B S hS (subspaceInclusion B S hS X Z)).obj G) U a
    ((mem_definingIdealAt_iff B S hS X Z U a).1 ha) m

end Ideal

section Transpose

variable {X X' : AlgebraicSpaces B S hS}

/-- **The transpose along `f^* ⊣ f_*` of a morphism out of a sheaf of ideals.**  For a morphism
`f : X' ⟶ X` of algebraic spaces, a subsheaf `𝓘 ⊆ 𝒪_X` of the structure sheaf and an
`𝒪_{X'}`-module `M`, a morphism of `𝒪_X`-modules `𝓘 ⟶ f_*M` transposes to a morphism of
`𝒪_{X'}`-modules `f^*𝓘 ⟶ M` across the adjunction of Stacks 03LU.

This is the transposition the first arrow of Stacks 05ZA is built by, named rather than written
out, and that is what it is for: a consumer that writes the transposition out instead must
compare its own elaboration of it with the one inside the definition of the arrow, and at the
concrete small étale ringed topoi that comparison does not fit in the default heartbeat budget
(it needs more than twenty times that budget).  Through this definition the comparison is
of two applications of one constant, with the ambient module categories never entered. -/
noncomputable def submoduleTranspose (f : X' ⟶ X)
    (I : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    (M : Modules.{u, u} B S hS X'.1 X'.2)
    (u : I.toSheafOfModules ⟶ (modulePushforward B S hS f).obj M) :
    (modulePullback B S hS f).obj I.toSheafOfModules ⟶ M :=
  ((modulePullbackAdjunction B S hS f).homEquiv I.toSheafOfModules M).symm u

/-- The transposition of `AlgebraicGeometry.Space.submoduleTranspose` is a bijection: transposing
back along `f^* ⊣ f_*` returns the morphism out of the sheaf of ideals. -/
theorem homEquiv_submoduleTranspose (f : X' ⟶ X)
    (I : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    (M : Modules.{u, u} B S hS X'.1 X'.2)
    (u : I.toSheafOfModules ⟶ (modulePushforward B S hS f).obj M) :
    ((modulePullbackAdjunction B S hS f).homEquiv I.toSheafOfModules M)
        (submoduleTranspose B S hS f I M u) = u :=
  ((modulePullbackAdjunction B S hS f).homEquiv I.toSheafOfModules M).apply_symm_apply u

/-- **`d_{X/B}` followed by the unit of `f^* ⊣ f_*`.**  For a morphism `f : X' ⟶ X` of algebraic
spaces and a structure morphism `g : X ⟶ B`, this is the universal `B`-derivation `d_{X/B}` of
`𝒪_X` composed with the unit `Ω_{X/B} ⟶ f_*f^*Ω_{X/B}` of the adjunction of Stacks 03LU.

**This definition exists so that the morphism of algebraic spaces stays a variable.**  Every
statement about this derivation — the identification of its value on a local section with the
unit applied to a universal differential, which is
`PresheafOfModulesOfCommRing.Derivation.postcomp_d_apply` — elaborates at the default heartbeat budget while
`f` is a variable and does *not* elaborate once `f` is a concrete inclusion of a closed subspace,
because the coefficient module must then be compared with the one the adjunction writes through
the composite functor `f^* ⋙ f_*`, which unfolds the construction of the small étale ringed topos.
A consumer at a concrete `f` therefore names this constant instead of writing the composite out:
the comparison it is then left with is of two applications of one constant, and `rfl` decides it.
This is the same device, for the same reason, as
`AlgebraicGeometry.Space.submoduleTranspose` above. -/
noncomputable def pullbackUnitDerivation {Bb : AlgebraicSpaces B S hS} (f : X' ⟶ X)
    (g : X ⟶ Bb) :
    PresheafOfModulesOfCommRing.Derivation' ((modulePushforward B S hS f).obj
      ((modulePullback B S hS f).obj (sheafOfDifferentials B S hS g))).val
      (structureSharpInverseImage B S hS g).hom :=
  (universalDerivation B S hS g).postcomp
    ((modulePullbackAdjunction B S hS f).unit.app (sheafOfDifferentials B S hS g)).val

end Transpose

section FirstMap

variable {X Bb : AlgebraicSpaces B S hS}

/-- **The `B`-derivation that induces the first arrow of Stacks 05ZA.**  For a closed subspace
`Z ⊆ X` with inclusion `i` and a morphism `b : X ⟶ B`, this is the universal `B`-derivation
`d_{X/B}` of `𝒪_X` followed by the unit `Ω_{X/B} ⟶ i_*i^*Ω_{X/B}` of the adjunction `i^* ⊣ i_*`
of Stacks 03LU, that is, `AlgebraicGeometry.Space.pullbackUnitDerivation` at `i`.

It is a derivation and not a morphism of `𝒪_X`-modules; what makes the first arrow exist is that
its restriction to the defining ideal sheaf *is* a morphism of `𝒪_X`-modules, by
`AlgebraicGeometry.Space.conormalSequenceIdealHom`. -/
noncomputable def conormalSequenceUnitDerivation (Z : ClosedSubspaces B S hS X.1) (b : X ⟶ Bb) :
    PresheafOfModulesOfCommRing.Derivation'
      ((modulePushforward B S hS (subspaceInclusion B S hS X Z)).obj
        ((modulePullback B S hS (subspaceInclusion B S hS X Z)).obj
          (sheafOfDifferentials B S hS b))).val
      (structureSharpInverseImage B S hS b).hom :=
  pullbackUnitDerivation B S hS (subspaceInclusion B S hS X Z) b

/-- **The adjoint form of the first arrow of Stacks 05ZA**: the morphism of `𝒪_X`-modules
`𝓘 ⟶ i_*i^*Ω_{X/B}` obtained by restricting
`AlgebraicGeometry.Space.conormalSequenceUnitDerivation` to the defining ideal sheaf of `Z`. -/
noncomputable def conormalSequenceIdealDifferential (Z : ClosedSubspaces B S hS X.1)
    (b : X ⟶ Bb) :
    (definingIdealSheaf B S hS X Z).toSheafOfModules ⟶
      (modulePushforward B S hS (subspaceInclusion B S hS X Z)).obj
        ((modulePullback B S hS (subspaceInclusion B S hS X Z)).obj
          (sheafOfDifferentials B S hS b)) :=
  conormalSequenceIdealHom B S hS Z _ (conormalSequenceUnitDerivation B S hS Z b)
    (fun U a ha m ↦ definingIdealAt_smul_modulePushforward_eq_zero B S hS Z _ U a ha m)

/-- **Stacks 05ZA, "the first arrow is induced by `d_{X/B}`".**  The first arrow is by definition
the transpose across `i^* ⊣ i_*` of
`AlgebraicGeometry.Space.conormalSequenceIdealDifferential`, and that transpose carries a local
section `a` of the defining ideal sheaf of `Z` to `D(a)`, where `D` is `d_{X/B}` followed by the
unit of the adjunction — which is what
`AlgebraicGeometry.Space.conormalSequenceUnitDerivation` is, by its definition.  This equation is
the whole of the arrow's dependence on `d_{X/B}`; since the transposition is a bijection, it
determines the arrow. -/
@[stacks 05ZA "the first arrow is induced by `d_{X/B}`: the transpose of the first arrow across \
`i^* ⊣ i_*` carries a section of the defining ideal sheaf to the universal differential of that \
section, followed by the unit"]
theorem conormalSequenceIdealDifferential_val_app_apply (Z : ClosedSubspaces B S hS X.1)
    (b : X ⟶ Bb) (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (x : (definingIdealSheaf B S hS X Z).toSheafOfModules.val.obj U) :
    ((conormalSequenceIdealDifferential B S hS Z b).val.app U).hom x =
      (conormalSequenceUnitDerivation B S hS Z b).d x.1 :=
  rfl

/-- **The first arrow of Stacks 05ZA, written out of `i^*𝓘`.**  The transpose across the
adjunction `i^* ⊣ i_*` of Stacks 03LU of
`AlgebraicGeometry.Space.conormalSequenceIdealDifferential`.

This is the same morphism as `AlgebraicGeometry.Space.conormalSequenceFirstMap`, whose source is
written `𝒞_{Z/X}`; the two sources are equal by `AlgebraicGeometry.Space.conormalModule_eq`.  The
statements below are made at this reading of the source, because every one of them applies the
transposition to the arrow, and at the other reading each such application re-checks that equality
of sheaves of modules, which does not fit in the default heartbeat budget.

The transposition is taken through `AlgebraicGeometry.Space.submoduleTranspose`, which is that
transposition at an arbitrary sheaf of ideals; the implementation notes of that definition say
why it is named here rather than written out. -/
noncomputable def conormalSequenceIdealPullbackMap (Z : ClosedSubspaces B S hS X.1)
    (b : X ⟶ Bb) :
    (modulePullback B S hS (subspaceInclusion B S hS X Z)).obj
        (definingIdealSheaf B S hS X Z).toSheafOfModules ⟶
      (modulePullback B S hS (subspaceInclusion B S hS X Z)).obj
        (sheafOfDifferentials B S hS b) :=
  submoduleTranspose B S hS (subspaceInclusion B S hS X Z) (definingIdealSheaf B S hS X Z)
    ((modulePullback B S hS (subspaceInclusion B S hS X Z)).obj
      (sheafOfDifferentials B S hS b))
    (conormalSequenceIdealDifferential B S hS Z b)


/-- **Stacks 05ZA, the canonical first arrow.**  For a subspace `Z` of an algebraic space
`X` over `B`, with inclusion `i : Z ⟶ X`, the arrow
```
  𝒞_{Z/X} ⟶ i^*Ω_{X/B}
```
induced by `d_{X/B}`.  It is `AlgebraicGeometry.Space.conormalSequenceIdealPullbackMap` with its
source read as the conormal module, which it is by
`AlgebraicGeometry.Space.conormalModule_eq`. -/
@[stacks 05ZA "the canonical first arrow `𝒞_{Z/X} ⟶ i^*Ω_{X/B}` induced by `d_{X/B}`, at a \
subspace inclusion.  The same arrow at an arbitrary immersion is \
`conormalSequenceFirstMapOfImmersion`"]
noncomputable def conormalSequenceFirstMap (Z : ClosedSubspaces B S hS X.1) (b : X ⟶ Bb) :
    conormalModule B S hS X Z ⟶
      (modulePullback B S hS (subspaceInclusion B S hS X Z)).obj
        (sheafOfDifferentials B S hS b) :=
  conormalSequenceIdealPullbackMap B S hS Z b

end FirstMap

end AlgebraicGeometry.Space

end
