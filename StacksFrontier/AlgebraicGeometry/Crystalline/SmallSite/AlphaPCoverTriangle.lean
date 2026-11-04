module

public import StacksFrontier.AlgebraicGeometry.Crystalline.AlphaPCover
public import StacksFrontier.AlgebraicGeometry.Crystalline.AlphaPCoverCohomologyBound
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrisDirectImage
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrisGlobalSectionsIso
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LowerShriekAbelianExact
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ZariskiRingedComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.PushforwardInjectives
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.DerivedGlobalSectionsMap

/-!
# The terms of the triangle of [Stacks, Tag 07Q9], and the bound of [Stacks, Tag 07QA]

[Stacks, Tag 07Q9] asserts that for an iterated `α_p`-cover `f : X' ⟶ X` of schemes over `S₀` of
constant degree `q` and a crystal in quasi-coherent modules `ℱ` on `Cris(X/S)`, the third term `E`
of the distinguished triangle

`Ru_{X/S, *}ℱ ⟶ f_*Ru_{X'/S, *}ℱ' ⟶ E ⟶ Ru_{X/S, *}ℱ[1]`,  `ℱ' = f_cris^*ℱ`,

has cohomology sheaves annihilated by `q`, and [Stacks, Tag 07QA] deduces that
`f^* : H^i(Cris(X/S), ℱ) ⟶ H^i(Cris(X'/S), ℱ')` has kernel and cokernel annihilated by
`q^{i + 1}`.  This file assembles the *terms* of that triangle.  Three of the four are built
here; the fourth, `Ru_{X/S, *}`, is
`Crystalline.GlobalCrystallineSituation.SmallSite.derivedZariskiDirectImage` of
`SmallSite/ZariskiDirectImage.lean`.

As in `SmallSite/CrisDirectImage.lean`, the orientation of the variables is that `S` is the
*source* situation `X'/S` and `S'` the *target* situation `X/S`, so `fX : S.X ⟶ S'.X` is the
cover `f : X' ⟶ X` and `crisDirectImage S S' fS fX hf` is `f_{cris, *}`.

Everything is at abelian coefficients.  That is not a weakening: the module documentation of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/ZariskiRingedComparison.lean` shows that
`u_{X/S}` is not a morphism of ringed topoi over `𝒪_X`, so `Ru_{X/S, *}ℱ` is a complex of abelian
sheaves on `X_Zar` and nothing more, and the triangle of [Stacks, Tag 07Q9] is a statement in
`D(Ab(X_Zar))`.

## What this file adds

* **The Zariski direct image along `f`.**  `zariskiPushforward` is
  `f_{Zar, *} : Ab(X'_Zar) ⥤ Ab(X_Zar)`, the abelian companion of the set-valued
  `StacksZariskiSite.opensMapMorphismOfTopoi`, together with its left adjoint, its exactness
  properties, the fact that it preserves injectives, and the derived and graded derived functors
  `Rf_{Zar, *}` and `R^j f_{Zar, *}`.  All unconditional.
* **The inverse image along `f_cris`.**  `crisInverseImage` is
  `f_cris^{-1} : Ab(Cris(X/S)) ⥤ Ab(Cris(X'/S))`, the left adjoint of
  `crisDirectImage`, assembled from the left adjoints of its three factors; `crisPullback` is
  `ℱ' = f_cris^{-1}ℱ`, `crisUnit` the unit `ℱ ⟶ f_{cris, *}ℱ'` and `derivedCrisUnit` its derived
  form `ℱ[0] ⟶ Rf_{cris, *}ℱ'[0]`.  It is **exact**, hence `f_{cris, *}` preserves injective
  abelian sheaves.  All unconditional.
* **The comparison map, as far as it goes.**  `zariskiComparison` is the underived comparison
  `u_{X/S, *}ℱ ⟶ f_{Zar, *}u_{X'/S, *}ℱ'`, built from the unit above and a commutation of the
  square of topoi which has to be *supplied*; `HasFreeCrisZariskiCell` records the canonical
  2-cell that is free, which goes the *other* way.  `derivedZariskiSquare` and
  `derivedZariskiComparison` are the derived forms, each taking the commutation as an explicit
  argument, which `...SmallSite.crisZariskiSquare` supplies.
* **The Leray factorization for `f_cris` and the map `f^*` of [Stacks, Tag 07QA].**  Because
  `f_{cris, *}` preserves injective abelian sheaves,
  `derivedCrisGlobalSectionsIso` factors `RΓ(Cris(X'/S), -)` as `Rf_{cris, *}` followed by
  `RΓ(Cris(X/S), -)`, and `crisCohomologyMap` is the resulting
  `f^* : H^i(Cris(X/S), ℱ) ⟶ H^i(Cris(X'/S), ℱ')`.  These three take no datum: the underived
  `Γ(Cris(X/S), f_{cris, *} -) ≅ Γ(Cris(X'/S), -)` is proved, as
  `...SmallSite.crisGlobalSectionsIso` of `SmallSite/CrisGlobalSectionsIso.lean`.
* **The two bounds of [Stacks, Tag 07QA]**, `pow_smul_eq_zero_of_kernel_07QA` and
  `exists_comp_mor₁_eq_pow_smul_07QA`, proved unconditionally in `D(Ab(X_Zar))` from the
  lemmas of `Crystalline/AlphaPCoverCohomologyBound.lean`, with the exponent `q^{i + 1}` of the
  source in place.

## The direction of the square, and why the comparison map is not free

The map of [Stacks, Tag 07Q9] is the composite

`Ru_{X/S, *}ℱ ⟶ Ru_{X/S, *}Rf_{cris, *}ℱ' ≅ R(u_{X/S} ∘ f_cris)_*ℱ' ≅ R(f_{Zar} ∘ u_{X'/S})_*ℱ'`,

so it needs the commutation `u_{X/S, *} ∘ f_{cris, *} ≅ f_{Zar, *} ∘ u_{X'/S, *}` — or at least a
2-cell in the direction `u_{X/S, *} ∘ f_{cris, *} ⟶ f_{Zar, *} ∘ u_{X'/S, *}`.  That 2-cell is
**not** formal, and the one that is formal runs the opposite way.  Both composites are limits of
the same presheaf and can be read off:

* `(f_{Zar, *}u_{X'/S, *}H)(V)` is the limit of `H` over the objects `A'` of `Cris(X'/S)` whose
  open image in `X'` lies in `f^{-1}V`;
* `(u_{X/S, *}f_{cris, *}H)(V)` is the limit of `H` over the *pairs* `(A, A')` with `A` an object
  of `Cris(X/S)` whose open image lies in `V`, `A'` an object of `Cris(X'/S)`, and a morphism
  `A' ⟶ A` in `CRIS(X/S)` after change of base.

A pair gives `U_{A'} ⟶ U_A ⊆ V` over `X`, hence `U_{A'} ⊆ f^{-1}V`, so every index of the second
limit maps to an index of the first and the canonical 2-cell is
`f_{Zar, *} ∘ u_{X'/S, *} ⟶ u_{X/S, *} ∘ f_{cris, *}` — recorded as
`HasFreeCrisZariskiCell` below, in the shape in which the library can state it.  The converse
needs, for an object `A'` of `Cris(X'/S)`, an object of `Cris(X/S)` dominating it, i.e. an
embedding of the divided power thickening of `U_{A'}` into one of an open of `X`; no such thing
exists canonically, and this is the obstruction (★) of the module documentation of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/StructureMorphism.lean`, whose cofinality
route is recorded there as *false* in general.  So the commutation is genuine mathematics, not
assembly: the declarations here take it as explicit data, and it is constructed in
`SmallSite/CrisZariskiSquareIso.lean` as `...SmallSite.crisZariskiSquare`.

The obstruction (★) does **not** also keep `f_{cris, *}` from preserving injectives.
Preservation of injectives follows from exactness of `f_cris^{-1}`, whose only problematic factor
is the abelian lower shriek `i_{X, !}`; the exactness
`Crystalline.GlobalCrystallineSituation.CrystallineThickening.preservesFiniteLimits_lowerShriek`
is indeed for sheaves of *sets* only, and its terminal-object step is `coversTop_ι`, the clause
[Stacks, Tag 07IJ] omits in general — but at abelian coefficients that step is not needed, the
final object of a category of abelian sheaves being the zero object, which a left adjoint between
additive categories preserves.  What is left is [Stacks, Tag 00X4] for the shapes of
[Stacks, Tag 00X6], already in the library as
`Stacks.Sites.LowerShriek.gShriek_preservesFiniteLimits`.  So the abelian `i_{X, !}` is exact
(`...CrystallineThickening.preservesFiniteLimits_lowerShriekAb` of
`SmallSite/LowerShriekAbelianExact.lean`), `f_cris^{-1}` is exact
(`preservesFiniteLimits_crisInverseImage`) and `f_{cris, *}` preserves injective abelian sheaves
(`preservesInjectiveObjects_crisDirectImage`), all unconditionally.  The commutation of the
square is therefore the *only* datum `derivedZariskiSquare` carries.

## The commutation of the square, and why the obstruction (★) never blocked it

It is **proved**: `...SmallSite.crisZariskiSquare` of `SmallSite/CrisZariskiSquareIso.lean`
inhabits `CrisZariskiSquare` for every morphism of global crystalline situations.  What follows
is the route, which says which cofinality statement is false and why that does not matter.  The
two steps are in
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/CrisZariskiSquareCovering.lean`.

The counterexample of `SmallSite/StructureMorphism.lean` — `S = Spec ℤ_{(p)}` with divided power
ideal `(p)`, `X = ⨆_{n ≥ 1} Spec 𝔽_p`, `T = ⨆_{n ≥ 1} Spec ℤ/p^n` — shows that the comma category
of a *fixed* object of the big site over the inclusion can be empty, hence that `ι` is not a final
functor and that `CategoryTheory.RepresentablyFlat (ι S)` fails.  It does not refute the
comparison of the two limits displayed above, because that comparison is of limits of a *sheaf*:
as for `...SmallSite.smallRestrictionGlobalSectionsIso`, where the same comparison is false for
presheaves and true for sheaves, it is enough to *cover* each index of the first limit by indices
the projection hits, and one is free to shrink `A'` first.

The shrinking is the argument already given for `coversTop_ι`.  Restricting `A'` to the affine
opens of its ambient scheme, `...CrystallineThickening.restrictOpen`, and shrinking further so
that the part of `U'` maps into an affine open of `X` *inside `V`*, gives refinements of `A'` for
which `...exists_crystalline_hom_of_affine` — the pushout of [Stacks, Tag 07RT] — produces an
object `A` of `Cris(X/S)` whose open of `X` is that affine, with a morphism from the refinement of
`A'` to `ι A` after change of base.  That is exactly an index of the pair-limit, and those
refinements **cover** `A'`: `...SmallSite.dominatedSieve_mem`.  The companion step, that any two
such dominations of one `A'` are refined by a third — which is what makes a family on the pairs
compatible — is `...SmallSite.exists_cone_domination`, and it needs no new argument: the absolute
cofilteredness `...SmallSite.isCofilteredOrEmpty_structuredArrow_ι` is available and the
condition `U_A ⊆ V` descends to a common refinement by `...Thickening.mem_of_hom`.  In the sheaf
reading these two steps are the covering and the cofilteredness just named, not initiality and
connectedness of the comma categories of the projection, and neither is the cofinality statement
that `SmallSite/StructureMorphism.lean` refutes.

What remained after those two steps was not geometry: the flattening of the three nested right
Kan extensions computing `u_{X/S, *} ∘ f_{cris, *}` into a single limit over the pairs, so that
the canonical 2-cell becomes a `CategoryTheory.Limits.limit.pre`; separatedness of an abelian
sheaf at a covering sieve of an *object*, the relative form of what
`CategoryTheory.GrothendieckTopology.CoversTop.ext` does at the final object; and amalgamation of
the compatible family over that sieve.  `SmallSite/CrisZariskiSquareLimit.lean` and
`SmallSite/CrisZariskiSquareIso.lean` carry those out.  See the module documentation of
`SmallSite/CrisZariskiSquareCovering.lean`.

## Main definitions

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `zariskiPushforward`, `zariskiPullbackSheaf`, `zariskiPushforwardAdjunction` — `f_{Zar, *}`,
  `f_{Zar}^{-1}` and the adjunction between them on abelian sheaves.
* `derivedZariskiPushforwardFunctor`, `higherZariskiPushforward` — `Rf_{Zar, *}` and
  `R^j f_{Zar, *}`.
* `crisInverseImage`, `crisDirectImageAdjunction`, `crisPullback`, `crisUnit`, `derivedCrisUnit` —
  `f_cris^{-1}`, the adjunction `f_cris^{-1} ⊣ f_{cris, *}`, the pullback `ℱ'`, the unit
  `ℱ ⟶ f_{cris, *}ℱ'` and its derived form `ℱ[0] ⟶ Rf_{cris, *}ℱ'[0]`.
* `CrisGlobalSectionsComparison` — the type `Γ(Cris(X/S), f_{cris, *} -) ≅ Γ(Cris(X'/S), -)`.
  It is inhabited by
  `...SmallSite.crisGlobalSectionsIso` of `SmallSite/CrisGlobalSectionsIso.lean`.
* `derivedCrisGlobalSectionsIso` — the Leray factorization
  `RΓ(Cris(X'/S), -) ≅ Rf_{cris, *} ⋙ RΓ(Cris(X/S), -)`.
* `derivedCrisPullbackMap` and `crisCohomologyMap` — `f^*` on derived crystalline global sections
  and on the graded cohomology `H^i(Cris(X/S), -)`.
* `CrisZariskiSquare` — the type of the commutation datum
  `u_{X/S, *} ∘ f_{cris, *} ≅ f_{Zar, *} ∘ u_{X'/S, *}`, and `HasCrisZariskiSquare` the assertion
  that one exists.
* `HasFreeCrisZariskiCell` — the 2-cell in the free direction, as a proposition.
* `zariskiComparison` — the underived comparison `u_{X/S, *}ℱ ⟶ f_{Zar, *}u_{X'/S, *}ℱ'`.
* `derivedZariskiSquare` and `derivedZariskiComparison` — the derived square and the derived
  comparison, each from the data above.
* `Annihilation07Q9` — the conclusion of [Stacks, Tag 07Q9] for a given morphism of
  `D⁺(Ab(X_Zar))`, and `Statement07Q9` the full statement of [Stacks, Tag 07Q9] reduced to the
  data the previous paragraph names.

## Main results

* `preservesInjectiveObjects_zariskiPushforward` — `f_{Zar, *}` preserves injective abelian
  sheaves, its left adjoint being exact.
* `preservesFiniteLimits_crisInverseImage` and `preservesInjectiveObjects_crisDirectImage` —
  **`f_cris^{-1}` is exact and `f_{cris, *}` preserves injective abelian sheaves**,
  unconditionally.
* `zariskiPushforward_comp_topSections` — `Γ(X, f_{Zar, *}G) = Γ(X', G)`, by `rfl`.
* `pow_smul_eq_zero_of_kernel_07QA` and `exists_comp_mor₁_eq_pow_smul_07QA` — **the two bounds of
  [Stacks, Tag 07QA] with the exponent `q^{i + 1}`**, for a distinguished triangle in
  `D(Ab(X_Zar))` whose cohomology sheaves in the relevant range are annihilated by `q`.  The
  kernel bound needs only that the triangle's first term be concentrated in degrees `≥ 0`, which
  for the triangle of [Stacks, Tag 07Q9] is free.
* `exists_comp_mor₁_eq_pow_smul_07QA_of_mono` — the cokernel bound with the hypothesis the
  geometry supplies.  The concentration of the cone in degrees `≥ 0`, which is what buys the
  source's exponent `q^{i + 1}` in place of `q^{i + 2}`, is derived from injectivity of
  `ℋ^0(Ru_{X/S, *}ℱ) ⟶ ℋ^0(f_*Ru_{X'/S, *}ℱ')` instead of assumed.
* `smul_id_homologyFunctor_ι_obj₃_eq_zero` — `Annihilation07Q9`, the conclusion of
  [Stacks, Tag 07Q9], restated in the unbounded form the two bounds consume.  It holds by
  `rfl`: `DerivedCategory.Plus.homologyFunctor` *is* `DerivedCategory.Plus.ι` followed by
  `DerivedCategory.homologyFunctor`, so the apparent `D⁺`-versus-`D` mismatch between 07Q9's
  conclusion and 07QA's bounds costs nothing.  The real content between them is neither the
  commutation of the square of topoi, which is `...SmallSite.crisZariskiSquare`, nor the Leray
  coherence named in `crisCohomologyMap`'s docstring, which is
  `...SmallSite.crisZariskiLerayCoherence`: it is [Stacks, Proposition 07LG]
  (`...SmallSite.crystalPairDeRhamComplex_computesCohomology`), through [Stacks, Tag 07Q9],
  together with the monomorphism of `ℋ^0` that the cokernel half needs
  (`...SmallSite.mono_zariskiDirectImage_map_crisModuleUnit_of_isIteratedAlphaPCover`).

## What is and is not proved

What is proved, unconditionally: that `f_{Zar, *}` and `f_{Zar}^{-1}` exist on abelian sheaves and
are adjoint, that `f_{Zar}^{-1}` is exact and `f_{Zar, *}` additive, left exact and
injective-preserving, that `Rf_{Zar, *}` and `R^j f_{Zar, *}` therefore exist and that
`R^0 f_{Zar, *} = f_{Zar, *}`; that `f_cris^{-1}` exists on abelian sheaves, is adjoint to
`f_{cris, *}`, is additive and **exact**, and comes with its unit, so that `f_{cris, *}`
preserves injective abelian sheaves; and the two annihilation bounds of [Stacks, Tag 07QA] for an
abstract distinguished triangle in `D(Ab(X_Zar))`.

Where the tags are, and what this file contributes to them:

* **No tag attribute is placed in this file.**  [Stacks, Tag 07Q9] is
  `...SmallSite.annihilation07Q9_of_isIteratedAlphaPCover` of
  `SmallSite/AlphaPCover07Q9Main.lean`, whose conclusion is the proposition `Annihilation07Q9`
  defined here; [Stacks, Tag 07QA] is
  `...SmallSite.annihilated_ker_coker_crisModuleCohomologyMap_of_isIteratedAlphaPCover` of
  `SmallSite/CrisCohomologyBound07QAMain.lean`.  `Annihilation07Q9` and `Statement07Q9` are
  *definitions of propositions*: the first is the conclusion of [Stacks, Tag 07Q9] for a given
  morphism, the second the whole statement in the abelian vocabulary of this file; no declaration
  here asserts either.
* The commutation of the square of topoi is `...SmallSite.crisZariskiSquare` of
  `SmallSite/CrisZariskiSquareIso.lean`, with `...SmallSite.hasCrisZariskiSquare` for
  `HasCrisZariskiSquare`; so the declarations below that take a `CrisZariskiSquare` in their
  signature take a datum this library supplies, and nothing else.  The route ran through the
  three files `SmallSite/CrisZariskiSquare{Covering, Limit, Iso}.lean`: the covering
  `dominatedSieve_mem` and the cofilteredness `exists_cone_domination`; then the flattening of
  the three nested right Kan extensions computing `u_{X/S, *}f_{cris, *}` into one limit over the
  dominating pairs, which makes the free 2-cell a `CategoryTheory.Limits.limit.pre`; then the
  inversion of that comparison by the sheaf condition, and its promotion to an isomorphism of
  functors by recognising it as Mathlib's base change of a right Kan extension along a square of
  sites.
* The underived comparison of global sections along `f_cris` is
  `...SmallSite.crisGlobalSectionsIso` of `SmallSite/CrisGlobalSectionsIso.lean`, so
  `derivedCrisGlobalSectionsIso`, `derivedCrisPullbackMap` and `crisCohomologyMap` take **nothing**
  and `f^*` on crystalline cohomology is an unconditional declaration of this library.  No abelian
  lower shriek and no constant-sheaf computation are needed, only that the limit of a sheaf on
  `CRIS(X/S)` is computed over `Cris(X/S)`, which `...CrystallineThickening.coversTop_ι` gives
  directly.
* **The mathematical content of [Stacks, Tag 07Q9]** is [Stacks, Proposition 07LG], the
  computation of the cohomology of a crystal in quasi-coherent modules by the de Rham complex of
  the divided power envelope — `...SmallSite.crystalPairDeRhamComplex_computesCohomology` of
  `SmallSite/CrystalDeRhamComputesCohomology.lean` — together with [Stacks, Tag 07Q7] at `a = p`
  for the extension of [Stacks, Tag 07N1]: in Situation 07MD for the completed envelope this is
  `Crystalline.PthRootExtension.exists_homotopyInverse_completedPthRootExtension_situation` of
  `Differentials/PthRootCompletedSituation.lean`, and the splitness of `D ⟶ D'` as a map of
  `D`-modules is `Crystalline.PthRootExtension.completedPrimeRetraction_comp_completedToPrimeRing`
  and `Crystalline.PthRootExtension.injective_completedToPrimeRing`.  The proof of the tag uses
  them over the chain opens of `SmallSite/AlphaPCoverBasis07Q9.lean`, in
  `...SmallSite.chainConeAnnihilation_isChainOpen07Q9`.

  The propagation along the chain `X' = X_n ⟶ ⋯ ⟶ X_0 = X` is also available *in the terms of
  `Annihilation07Q9` itself*, both in the binary form `...SmallSite.annihilation07Q9_comp` of
  `SmallSite/CrisDirectImageComposition.lean` — the annihilators of `Annihilation07Q9` multiply
  along a composition of maps of `D⁺(Ab(X_Zar))` — and along the whole tower as
  `...SmallSite.annihilation07Q9_chainComp` of `SmallSite/AlphaPCoverTowerAnnihilation.lean`, with
  the exponent `a ^ n` for `n` stages, both unconditionally.  (The lemma
  `Stacks.Triangulated.pow_smul_id_eq_zero_of_chainComp` propagates the annihilation of the
  *cone*, whereas 07Q9's conclusion is the annihilation of the cone's *cohomology sheaves*, and
  neither implies the other.)  The composition functoriality of `derivedZariskiComparison` that
  this route needs — the comparison map of a composite cover is the composite of the comparison
  maps of its stages — is assembled from `changeBaseComp`, `changeBaseDirectImageComp`,
  `zariskiPushforwardComp` and `derivedZariskiPushforwardComp` of
  `SmallSite/CrisDirectImageComposition.lean`, `...SmallSite.hasCrisDirectImageComp` of
  `SmallSite/CrisDirectImageCompositionIso.lean`, `...SmallSite.crisInverseImageComp` of
  `SmallSite/CrisInverseImageComposition.lean` and `...SmallSite.crisZariskiCellComp` of
  `SmallSite/CrisZariskiCellCompositionProof.lean`, which give the underived form
  `...SmallSite.zariskiComparison_comp'`; the derived form is
  `...SmallSite.derivedZariskiComparison_comp'` of `SmallSite/DerivedCrisZariskiComposition.lean`,
  all with no hypotheses.
* **The bounds of [Stacks, Tag 07QA] as statements about `f^*`.**  The bounds *here* are stated
  for morphisms `P ⟶ A` out of an object `P` of `D(Ab(X_Zar))` concentrated in degrees `≤ i`,
  and the triangle they are applied to is the one of [Stacks, Tag 07Q9] in `D(Ab(X_Zar))`;
  `crisCohomologyMap` is built on the *crystalline* side, out of the derived unit and the Leray
  factorization.  Three inputs separate the two, and all three are in the library:

  1. the commutation `sq` of the square of topoi, `...SmallSite.crisZariskiSquare`;
  2. the annihilation of [Stacks, Tag 07Q9],
     `...SmallSite.annihilation07Q9_of_isIteratedAlphaPCover`;
  3. the identification of `crisCohomologyMap` with `H^i` of `derivedZariskiComparison sq`.
     This is not a consequence of 1 and 2.  The Leray factorization
     `RΓ(Cris(X/S), -) ≅ Ru_{X/S, *} ⋙ RΓ(X_Zar, -)` is
     `...SmallSite.derivedGlobalSectionsIsoDerivedZariskiDirectImage`, the Leray factorization
     `RΓ(X'_Zar, -) ≅ Rf_{Zar, *} ⋙ RΓ(X_Zar, -)` is assembled from
     `preservesInjectiveObjects_zariskiPushforward` and `zariskiPushforward_comp_topSections`
     above, and their *coherence* — that the square of those two factorizations, the crystalline
     one `derivedCrisGlobalSectionsIso` and the derived square `derivedZariskiSquare sq`
     commutes, a statement about four Leray comparisons that does not follow from `sq` — is
     `...SmallSite.crisZariskiLerayCoherence` of `SmallSite/UnderivedLerayCoherence.lean`, so
     `...SmallSite.derivedZariskiGlobalSections_map_derivedZariskiComparison_of_coherence` of
     `SmallSite/HypercohomologyBound07QA.lean` identifies `RΓ(X_Zar, -)` of the comparison with
     `derivedCrisPullbackMap`.  Reading the bounds in degree `i` uses
     `H^i(X_Zar, -) ≅ Hom(P, -⟦i⟧)` for `P` the constant sheaf `ℤ_X` placed in degree zero and
     shifted: `...SmallSite.derivedZariskiGlobalSectionsHomologyShiftAddEquiv` and its
     naturality in `K` (`SmallSite/ZariskiHypercohomology.lean`).

  No declaration in *this* file bounds `crisCohomologyMap`.
  `...SmallSite.pow_smul_eq_zero_of_crisCohomologyMap_eq_zero_07QA` and
  `...SmallSite.exists_crisCohomologyMap_eq_pow_smul_07QA` of
  `SmallSite/CrisCohomologyBound07QA.lean` do, for any morphism whose cone satisfies
  `Annihilation07Q9`, by conjugating the bounds of `SmallSite/HypercohomologyBound07QA.lean`
  along those two Leray isomorphisms; they are lemmas, stated for an arbitrary annihilator `q`.
  The tag itself, under the source's hypotheses, is the module-level form
  `...SmallSite.annihilated_ker_coker_crisModuleCohomologyMap_of_isIteratedAlphaPCover`, which
  feeds [Stacks, Tag 07Q9] into the same bounds.
* **No hypothesis is used to make any statement easier.**  `Annihilation07Q9` quantifies over
  *every* distinguished triangle on the given morphism, as the source's "the distinguished
  triangle" must be read; the exponent in the [Stacks, Tag 07QA] bounds is the source's `i + 1`
  and not the weaker `i + 2`.  For the kernel that costs nothing — the bound is a quotient of
  `H^{i - 1}(X, E)` and the degrees `-1, 0, …, i - 1` already number `i + 1` — and
  `pow_smul_eq_zero_of_kernel_07QA` accordingly asks only that the triangle's first term be
  concentrated in degrees `≥ 0`, which the triangle of [Stacks, Tag 07Q9] gives for free.  For
  the cokernel the count runs over `-1, 0, …, i` and would give `i + 2`, so the source's `i + 1`
  genuinely needs `ℋ^{-1}(E) = 0`.  That is **not** an erratum and **not** a hypothesis smuggled
  in: `ℋ^{-1}(E)` is the kernel of `ℋ^0(Ru_{X/S, *}ℱ) ⟶ ℋ^0(f_*Ru_{X'/S, *}ℱ')`, and that map is
  injective for an iterated `α_p`-cover because `D ⟶ D'` of [Stacks, Tag 07N1] is a split
  injection of `D`-modules and `u_{X/S, *}` is left exact.
  `exists_comp_mor₁_eq_pow_smul_07QA_of_mono` is the form that takes that injectivity as its
  hypothesis and derives the concentration, through
  `Stacks.Triangulated.isGE_obj₃_of_mono_homologyMap`; the injectivity itself for the
  crystalline unit of a crystal in quasi-coherent modules is local structure theory, done in
  `SmallSite/ModuleUnitMonoRings07QA.lean` as
  `...SmallSite.mono_zariskiDirectImage_map_crisModuleUnit_of_isIteratedAlphaPCover`.

## References

* [Stacks Project, Lemma 60.26.3, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
* [Stacks Project, Lemma 60.26.4, Tag 07QA](https://stacks.math.columbia.edu/tag/07QA)
* [Stacks Project, Lemma 60.25.1, Tag 07Q7](https://stacks.math.columbia.edu/tag/07Q7)
* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Tag 07IJ](https://stacks.math.columbia.edu/tag/07IJ)
* [Stacks Project, Tag 07IK](https://stacks.math.columbia.edu/tag/07IK)
* [Stacks Project, Tag 07IL](https://stacks.math.columbia.edu/tag/07IL)
* [Stacks Project, Tag 00X2](https://stacks.math.columbia.edu/tag/00X2)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
  TopologicalSpace Opposite

universe w w' u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable (S S' : GlobalCrystallineSituation.{u}) (fS : S.S ⟶ S'.S) (fX : S.X ⟶ S'.X)
  (hf : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap fS = fX ≫ S'.toClosedFiber)

/-! ### The Zariski direct image along `f : X' ⟶ X` -/

/-- **The abelian direct image `f_{Zar, *} : Ab(X'_Zar) ⥤ Ab(X_Zar)`** along the map of small
Zariski sites induced by `f : X' ⟶ X`.  It is restriction along the continuous functor
`Opens.map f` of [Stacks, Tag 00X2], at the coefficients `AddCommGrpCat.{u + 1}` of this chapter
instead of the `Type (u + 1)` of `StacksZariskiSite.opensMapMorphismOfTopoi`; on sections it is
`(f_{Zar, *}G)(V) = G(f^{-1}V)`.

This is the `f_*` of the triangle of [Stacks, Tag 07Q9]. -/
def zariskiPushforward :
    Sheaf (opensTopology S) AddCommGrpCat.{u + 1} ⥤
      Sheaf (opensTopology S') AddCommGrpCat.{u + 1} :=
  (Opens.map fX.base).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (opensTopology S') (opensTopology S)

/-- **The abelian inverse image `f_{Zar}^{-1} : Ab(X_Zar) ⥤ Ab(X'_Zar)`**, the chosen left adjoint
of `f_{Zar, *}`: the sheafification of the left Kan extension along `Opens.map f`. -/
def zariskiPullbackSheaf :
    Sheaf (opensTopology S') AddCommGrpCat.{u + 1} ⥤
      Sheaf (opensTopology S) AddCommGrpCat.{u + 1} :=
  (Opens.map fX.base).sheafPullback AddCommGrpCat.{u + 1}
    (opensTopology S') (opensTopology S)

/-- **The adjunction `f_{Zar}^{-1} ⊣ f_{Zar, *}`** on abelian sheaves, [Stacks, Tag 00X2] at
abelian coefficients. -/
def zariskiPushforwardAdjunction :
    zariskiPullbackSheaf S S' fX ⊣ zariskiPushforward S S' fX :=
  (Opens.map fX.base).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
    (opensTopology S') (opensTopology S)

/-- **`f_{Zar}^{-1}` is left exact** on abelian sheaves: it is the sheafification of the left Kan
extension along `Opens.map f`, the index categories of that extension are filtered because
`Opens.map f` is representably flat, and filtered colimits of abelian groups are exact.  This is
`Stacks.Topology.preservesFiniteLimits_sheafPullbackOpensMap` at the coefficient universe
`u + 1`. -/
instance preservesFiniteLimits_zariskiPullbackSheaf :
    PreservesFiniteLimits (zariskiPullbackSheaf S S' fX) :=
  haveI _hS : HasSheafify (Opens.grothendieckTopology S.X.carrier) AddCommGrpCat.{u + 1} :=
    instHasSheafifyOpensAddCommGrpCat S
  haveI _hS' : HasSheafify (Opens.grothendieckTopology S'.X.carrier) AddCommGrpCat.{u + 1} :=
    instHasSheafifyOpensAddCommGrpCat S'
  have h : PreservesFiniteLimits ((Opens.map fX.base).sheafPullback AddCommGrpCat.{u + 1}
      (Opens.grothendieckTopology S'.X.carrier) (Opens.grothendieckTopology S.X.carrier)) :=
    Stacks.Topology.preservesFiniteLimits_sheafPullbackOpensMap.{u + 1} fX.base
  h

/-- `f_{Zar}^{-1}` commutes with every colimit that exists, being a left adjoint; in particular it
is right exact. -/
instance preservesColimitsOfSize_zariskiPullbackSheaf :
    PreservesColimitsOfSize.{w, w'} (zariskiPullbackSheaf S S' fX) :=
  (zariskiPushforwardAdjunction S S' fX).leftAdjoint_preservesColimits

/-- `f_{Zar, *}` commutes with every limit that exists, being a right adjoint; in particular it
is left exact. -/
instance preservesLimitsOfSize_zariskiPushforward :
    PreservesLimitsOfSize.{w, w'} (zariskiPushforward S S' fX) :=
  (zariskiPushforwardAdjunction S S' fX).rightAdjoint_preservesLimits

/-- `f_{Zar, *}` is additive on abelian sheaves: on sections it is the identity, so it is additive
on the nose. -/
instance additive_zariskiPushforward : (zariskiPushforward S S' fX).Additive where
  map_add := by intros; rfl

/-- **`f_{Zar, *}` carries injective abelian sheaves to injective abelian sheaves.**  Its left
adjoint `f_{Zar}^{-1}` is exact, hence preserves monomorphisms, and a right adjoint with that
property preserves injective objects.  This is
`Stacks.Topology.preservesInjectiveObjects_sheafPushforwardOpensMap` at the coefficient universe
`u + 1`, and it is what would make `Rf_{Zar, *}` compose with other derived functors in the manner
of [Stacks, Tag 015M]. -/
instance preservesInjectiveObjects_zariskiPushforward :
    (zariskiPushforward S S' fX).PreservesInjectiveObjects :=
  haveI _hS : HasSheafify (Opens.grothendieckTopology S.X.carrier) AddCommGrpCat.{u + 1} :=
    instHasSheafifyOpensAddCommGrpCat S
  haveI _hS' : HasSheafify (Opens.grothendieckTopology S'.X.carrier) AddCommGrpCat.{u + 1} :=
    instHasSheafifyOpensAddCommGrpCat S'
  have h : ((Opens.map fX.base).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (Opens.grothendieckTopology S'.X.carrier)
      (Opens.grothendieckTopology S.X.carrier)).PreservesInjectiveObjects :=
    Stacks.Topology.preservesInjectiveObjects_sheafPushforwardOpensMap.{u + 1} fX.base
  h

/-- **`Γ(X, f_{Zar, *}G) = Γ(X', G)`**, by `rfl`: the sections of `f_{Zar, *}G` over the top open
of `X` are the sections of `G` over `f^{-1}(⊤) = ⊤`, and `TopologicalSpace.Opens.map_top` is a
definitional equality.  This is the underived input of a Leray factorization for `f_{Zar}`. -/
theorem zariskiPushforward_comp_topSections :
    zariskiPushforward S S' fX ⋙
        (sheafSections (opensTopology S') AddCommGrpCat.{u + 1}).obj (op ⊤) =
      (sheafSections (opensTopology S) AddCommGrpCat.{u + 1}).obj (op ⊤) :=
  rfl

section DerivedZariski

variable [HasDerivedCategory.{w} (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology S') AddCommGrpCat.{u + 1})]

/-- **The derived Zariski direct image `Rf_{Zar, *} : D⁺(Ab(X'_Zar)) ⥤ D⁺(Ab(X_Zar))`.**  It is
the right derived functor of `f_{Zar, *}`, which is additive and whose source has enough
injectives by
`Crystalline.GlobalCrystallineSituation.SmallSite.instEnoughInjectivesOpens`.  For an `f` whose
`f_{Zar, *}` is exact — as it is for the iterated `α_p`-covers of [Stacks, Tag 07Q9], which are
homeomorphisms on points — this agrees with `f_{Zar, *}` degreewise, so it is the `f_*` the source
writes; nothing below assumes that exactness. -/
def derivedZariskiPushforwardFunctor :
    DerivedCategory.Plus (Sheaf (opensTopology S) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory.Plus (Sheaf (opensTopology S') AddCommGrpCat.{u + 1}) :=
  (zariskiPushforward S S' fX).rightDerivedFunctorPlus

/-- **The graded higher direct image `R^j f_{Zar, *} : Ab(X'_Zar) ⥤ Ab(X_Zar)`**, the degree-`j`
cohomology sheaf of `Rf_{Zar, *}`. -/
def higherZariskiPushforward (j : ℤ) :
    Sheaf (opensTopology S) AddCommGrpCat.{u + 1} ⥤
      Sheaf (opensTopology S') AddCommGrpCat.{u + 1} :=
  (zariskiPushforward S S' fX).rightDerivedPlus j

/-- **`R^j f_{Zar, *} I = 0` for `j ≠ 0` and `I` an injective abelian sheaf**, so `Rf_{Zar, *}I` is
concentrated in degree zero. -/
theorem isZero_higherZariskiPushforward_of_injective
    (G : Sheaf (opensTopology S) AddCommGrpCat.{u + 1}) [Injective G] (j : ℤ) (hj : j ≠ 0) :
    IsZero ((higherZariskiPushforward S S' fX j).obj G) :=
  Functor.isZero_rightDerivedPlus_obj_injective (zariskiPushforward S S' fX) j hj G

/-- **`R^0 f_{Zar, *} ≅ f_{Zar, *}`.**  The Zariski direct image is left exact, being a right
adjoint, so nothing is lost in degree zero. -/
def higherZariskiPushforwardZeroIso :
    higherZariskiPushforward S S' fX 0 ≅ zariskiPushforward S S' fX :=
  haveI : PreservesFiniteLimits (zariskiPushforward S S' fX) := inferInstance
  (Stacks.DerivedIndexing.rightDerivedIso (zariskiPushforward S S' fX) 0).symm ≪≫
    (zariskiPushforward S S' fX).rightDerivedZeroIsoSelf

end DerivedZariski

/-! ### The inverse image along `f_cris` -/

section CrisInverse

include hf

/-- **The abelian inverse image `f_cris^{-1} : Ab(Cris(X/S)) ⥤ Ab(Cris(X'/S))`** along the
morphism of small crystalline topoi of [Stacks, Tag 07IK].

`f_cris` is the composite `π_X ∘ f_CRIS ∘ i_{X'}` of [Stacks, Tag 07IK], so its inverse image is
the composite of the three inverse images in the opposite order: the lower shriek `i_{X, !}` of
[Stacks, Tag 07IJ], the sheaf pullback along the cocontinuous change of divided power base of
[Stacks, Tag 07IC], and restriction `i_{X'}^{-1}` to the small crystalline site.  Each of the
three is the left adjoint named by the corresponding adjunction of
`SmallSite/CrisDirectImage.lean`, so this is the left adjoint of `crisDirectImage` and
nothing is chosen.

This is the `f_cris^*` of [Stacks, Tag 07Q9] at abelian coefficients, and the reading is faithful:
the inverse image of the structure sheaf along each stage of `f_cris` is the structure sheaf on the
nose, `changeBase_op_comp_crisRing` and `ι_op_comp_crisRing`, so the module pullback a crystal
would be given adds no tensor factor. -/
def crisInverseImage :
    Sheaf (smallTopology S') AddCommGrpCat.{u + 1} ⥤
      Sheaf (smallTopology S) AddCommGrpCat.{u + 1} :=
  (Functor.sheafPullbackConstruction.sheafPullback (CrystallineThickening.ι S')
      AddCommGrpCat.{u + 1} (smallTopology S') (topology S') ⋙
    (changeBase S S' fS fX hf).sheafPullbackCocontinuous AddCommGrpCat.{u + 1}
      (topology S) (topology S')) ⋙
    smallRestriction S

/-- **The adjunction `f_cris^{-1} ⊣ f_{cris, *}`** on abelian sheaves: the composite of the three
adjunctions out of which `crisDirectImage` is built. -/
def crisDirectImageAdjunction :
    crisInverseImage S S' fS fX hf ⊣ crisDirectImage S S' fS fX hf :=
  ((smallRestrictionAdjunction S').comp
      (changeBaseDirectImageAdjunction S S' fS fX hf)).comp (bigDirectImageAdjunction S)

/-- `f_cris^{-1}` commutes with every colimit that exists, being a left adjoint; in particular it
is right exact. -/
instance preservesColimitsOfSize_crisInverseImage :
    PreservesColimitsOfSize.{w, w'} (crisInverseImage S S' fS fX hf) :=
  (crisDirectImageAdjunction S S' fS fX hf).leftAdjoint_preservesColimits

/-- **`f_cris^{-1}` is left exact**, hence exact.  Each of its three factors is:

* the abelian lower shriek `i_{X, !}` is
  `...CrystallineThickening.preservesFiniteLimits_lowerShriekAb`
  — [Stacks, Tag 07IJ] clause (6) at abelian coefficients, where no covering argument is needed
  because the final object of a category of abelian sheaves is the zero object;
* the inverse image along the cocontinuous change of divided power base is
  `CategoryTheory.Functor.preservesFiniteLimits_sheafPullbackCocontinuous`, [Stacks, Tag 00XL];
* restriction `i_{X'}^{-1} = π_{X', *}` to the small crystalline site preserves all limits, being
  itself a right adjoint, `preservesLimitsOfSize_smallRestriction`. -/
instance preservesFiniteLimits_crisInverseImage :
    PreservesFiniteLimits (crisInverseImage S S' fS fX hf) :=
  haveI _h₁ : PreservesFiniteLimits
      (Functor.sheafPullbackConstruction.sheafPullback (CrystallineThickening.ι S')
        AddCommGrpCat.{u + 1} (smallTopology S') (topology S')) :=
    CrystallineThickening.preservesFiniteLimits_lowerShriekAb S'
  haveI _h₃ : PreservesFiniteLimits (smallRestriction S) := ⟨fun _ _ _ ↦ inferInstance⟩
  comp_preservesFiniteLimits _ _

/-- **`f_{cris, *}` carries injective abelian sheaves to injective abelian sheaves.**  Its left
adjoint `f_cris^{-1}` is exact by `preservesFiniteLimits_crisInverseImage`, hence preserves
monomorphisms, and a right adjoint with that property preserves injective objects
([Stacks, Tag 015Z]).

This is what makes `Rf_{cris, *}` compose with other derived functors in the manner of
[Stacks, Tag 015M].  The exactness of the abelian `i_{X, !}` it rests on is in
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/LowerShriekAbelianExact.lean`. -/
instance preservesInjectiveObjects_crisDirectImage :
    (crisDirectImage S S' fS fX hf).PreservesInjectiveObjects :=
  haveI := preservesFiniteLimits_crisInverseImage S S' fS fX hf
  haveI : (crisInverseImage S S' fS fX hf).PreservesMonomorphisms :=
    preservesMonomorphisms_of_preservesLimitsOfShape _
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (crisDirectImageAdjunction S S' fS fX hf)

/-- **`ℱ' = f_cris^{-1}ℱ`**, the abelian sheaf on `Cris(X'/S)` the triangle of
[Stacks, Tag 07Q9] is about. -/
abbrev crisPullback (F : Sheaf (smallTopology S') AddCommGrpCat.{u + 1}) :
    Sheaf (smallTopology S) AddCommGrpCat.{u + 1} :=
  (crisInverseImage S S' fS fX hf).obj F

/-- **The unit `ℱ ⟶ f_{cris, *}ℱ'`** of the adjunction `f_cris^{-1} ⊣ f_{cris, *}`.  This is the
first half of the comparison map of [Stacks, Tag 07Q9]: pushing it down along `u_{X/S}` and
transporting along a commutation of the square gives `zariskiComparison`. -/
def crisUnit (F : Sheaf (smallTopology S') AddCommGrpCat.{u + 1}) :
    F ⟶ (crisDirectImage S S' fS fX hf).obj (crisPullback S S' fS fX hf F) :=
  (crisDirectImageAdjunction S S' fS fX hf).unit.app F

end CrisInverse

/-! ### The square of topoi, and the comparison map -/

section Square

include hf

/-- **The commutation of the square of topoi of [Stacks, Tag 07Q9],
`u_{X/S, *} ∘ f_{cris, *} ≅ f_{Zar, *} ∘ u_{X'/S, *}`, as a type of data.**  This is the input the
comparison map of [Stacks, Tag 07Q9] needs; it is inhabited unconditionally by
`...SmallSite.crisZariskiSquare` of `SmallSite/CrisZariskiSquareIso.lean`, and the declarations
below take it as a parameter only so that they do not depend on that file.  See the module
documentation for the two limit formulas and for why the canonical 2-cell runs the other way. -/
abbrev CrisZariskiSquare :=
  crisDirectImage S S' fS fX hf ⋙ zariskiDirectImage S' ≅
    zariskiDirectImage S ⋙ zariskiPushforward S S' fX

/-- **The assertion that the square of topoi of [Stacks, Tag 07Q9] commutes.**  **Proved**, as
`...SmallSite.hasCrisZariskiSquare` of `SmallSite/CrisZariskiSquareIso.lean`; what follows
records why it took three files.  The canonical 2-cell between the two composites runs in the
direction
`f_{Zar, *} ∘ u_{X'/S, *} ⟶ u_{X/S, *} ∘ f_{cris, *}` (`HasFreeCrisZariskiCell`), and inverting it
asks, for an object `A'` of `Cris(X'/S)`, for an object of `Cris(X/S)` dominating `A'` after change
of base — an embedding of the divided power thickening of `U_{A'}` into a divided power thickening
of an open of `X`.  For a *fixed* `A'` no such thing exists: that is the obstruction (★) recorded
in the module documentation of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/StructureMorphism.lean`, whose cofinality
route is false in general.

Both composites are limits of a *sheaf*, however, so `A'` may be refined first, and the two
geometric facts that buys are proved:
`Crystalline.GlobalCrystallineSituation.SmallSite.dominatedSieve_mem` — the refinements which
*are* dominated cover `A'` — and
`Crystalline.GlobalCrystallineSituation.SmallSite.exists_cone_domination` — any two dominations
are refined by a third.  See `SmallSite/CrisZariskiSquareCovering.lean` for both, and
`SmallSite/CrisZariskiSquare{Limit, Iso}.lean` for the limit plumbing which turns them into a
term of `CrisZariskiSquare`. -/
def HasCrisZariskiSquare : Prop :=
  Nonempty (CrisZariskiSquare S S' fS fX hf)

/-- **The 2-cell of the square that is free**, as a proposition:
`f_{Zar, *} ∘ u_{X'/S, *} ⟶ u_{X/S, *} ∘ f_{cris, *}`.  Every index of the limit computing the
right-hand side at an open `V` of `X` — a pair of an object `A` of `Cris(X/S)` with open image in
`V`, an object `A'` of `Cris(X'/S)`, and a morphism between them over `f` — yields
`U_{A'} ⊆ f^{-1}V`, hence an index of the limit computing the left-hand side, so a cone and a map
in this direction.  Recorded as a proposition rather than built, since nothing below uses it and
it is the direction [Stacks, Tag 07Q9] does *not* need. -/
def HasFreeCrisZariskiCell : Prop :=
  Nonempty (zariskiDirectImage S ⋙ zariskiPushforward S S' fX ⟶
    crisDirectImage S S' fS fX hf ⋙ zariskiDirectImage S')

/-- **The underived comparison `u_{X/S, *}ℱ ⟶ f_{Zar, *}u_{X'/S, *}ℱ'`** of [Stacks, Tag 07Q9]:
push the unit `ℱ ⟶ f_{cris, *}ℱ'` down along `u_{X/S}` and transport along the given commutation
of the square. -/
def zariskiComparison (sq : CrisZariskiSquare S S' fS fX hf)
    (F : Sheaf (smallTopology S') AddCommGrpCat.{u + 1}) :
    (zariskiDirectImage S').obj F ⟶
      (zariskiPushforward S S' fX).obj
        ((zariskiDirectImage S).obj (crisPullback S S' fS fX hf F)) :=
  (zariskiDirectImage S').map (crisUnit S S' fS fX hf F) ≫
    sq.hom.app (crisPullback S S' fS fX hf F)

section Derived

variable [HasDerivedCategory.{w} (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w} (Sheaf (smallTopology S') AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology S') AddCommGrpCat.{u + 1})]

/-- **The derived square `Rf_{cris, *} ⋙ Ru_{X/S, *} ≅ Ru_{X'/S, *} ⋙ Rf_{Zar, *}`**, from the
underived commutation.  Two instances of [Stacks, Tag 015M] in the form
`CategoryTheory.Functor.rightDerivedFunctorPlusCompIso` are used: the one on the Zariski side
needs that `u_{X'/S, *}` preserve injectives, which is
`preservesInjectiveObjects_zariskiDirectImage`, and the one on the crystalline side needs that
`f_{cris, *}` preserve injectives, which is `preservesInjectiveObjects_crisDirectImage` above.
Only the commutation `sq` is taken as an argument. -/
def derivedZariskiSquare (sq : CrisZariskiSquare S S' fS fX hf) :
    derivedCrisDirectImageFunctor S S' fS fX hf ⋙ derivedZariskiDirectImageFunctor S' ≅
      derivedZariskiDirectImageFunctor S ⋙ derivedZariskiPushforwardFunctor S S' fX :=
  (Functor.rightDerivedFunctorPlusCompIso (crisDirectImage S S' fS fX hf)
      (zariskiDirectImage S')).symm ≪≫
    Functor.rightDerivedFunctorPlusNatIso sq ≪≫
    Functor.rightDerivedFunctorPlusCompIso (zariskiDirectImage S) (zariskiPushforward S S' fX)

/-- **The derived unit `ℱ[0] ⟶ Rf_{cris, *}ℱ'[0]`** in `D⁺(Ab(Cris(X/S)))`: the unit
`ℱ ⟶ f_{cris, *}ℱ'` of `crisUnit`, placed in degree zero, followed by the canonical comparison
`f_{cris, *}ℱ'[0] ⟶ Rf_{cris, *}(ℱ'[0])` of
`Stacks.Cohomology.singleRightDerivedUnit`, the unit of the bounded below right derived functor
read on a complex concentrated in degree zero.  Unconditional. -/
def derivedCrisUnit (F : Sheaf (smallTopology S') AddCommGrpCat.{u + 1}) :
    (DerivedCategory.Plus.singleFunctor
        (Sheaf (smallTopology S') AddCommGrpCat.{u + 1}) 0).obj F ⟶
      (derivedCrisDirectImageFunctor S S' fS fX hf).obj
        ((DerivedCategory.Plus.singleFunctor
          (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) 0).obj
            (crisPullback S S' fS fX hf F)) :=
  (DerivedCategory.Plus.singleFunctor
      (Sheaf (smallTopology S') AddCommGrpCat.{u + 1}) 0).map
        (crisUnit S S' fS fX hf F) ≫
    (Stacks.Cohomology.singleRightDerivedUnit (crisDirectImage S S' fS fX hf)).app
      (crisPullback S S' fS fX hf F)

/-- **The comparison map `Ru_{X/S, *}ℱ ⟶ Rf_{Zar, *}Ru_{X'/S, *}ℱ'`** of [Stacks, Tag 07Q9], the
first arrow of its distinguished triangle.  It is `Ru_{X/S, *}` applied to the derived unit
`derivedCrisUnit`, followed by the derived square.

The commutation `sq` of the square of topoi is an argument, and it is available:
`...SmallSite.crisZariskiSquare` of
`SmallSite/CrisZariskiSquareIso.lean` inhabits it for every morphism of global crystalline
situations — it is the term the bounds of `SmallSite/CrisCohomologyBound07QA.lean` pass.
Everything else — the unit `ℱ ⟶ f_{cris, *}ℱ'`, its derived form, the preservation of injectives
by `f_{cris, *}` and the derivation of the square — is proved. -/
def derivedZariskiComparison (sq : CrisZariskiSquare S S' fS fX hf)
    (F : Sheaf (smallTopology S') AddCommGrpCat.{u + 1}) :
    (derivedZariskiDirectImage S').obj F ⟶
      (derivedZariskiPushforwardFunctor S S' fX).obj
        ((derivedZariskiDirectImage S).obj (crisPullback S S' fS fX hf F)) :=
  (derivedZariskiDirectImageFunctor S').map (derivedCrisUnit S S' fS fX hf F) ≫
    (derivedZariskiSquare S S' fS fX hf sq).hom.app
      ((DerivedCategory.Plus.singleFunctor
        (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) 0).obj
          (crisPullback S S' fS fX hf F))

end Derived

end Square

/-! ### The Leray factorization for `f_cris`, and `f^*` on crystalline cohomology -/

section Leray

include hf

variable [HasDerivedCategory.{w} (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w} (Sheaf (smallTopology S') AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} AddCommGrpCat.{u + 1}]

/-- **The comparison of underived global sections along `f_cris`,
`Γ(Cris(X/S), f_{cris, *} -) ≅ Γ(Cris(X'/S), -)`, as a type.**

`...SmallSite.crisGlobalSectionsIso` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/CrisGlobalSectionsIso.lean` inhabits it for
every morphism of global crystalline situations, and the three declarations below use that term.

Two of the three factors of `f_{cris, *}` are formal: for the cocontinuous
`bigDirectImage` and `changeBaseDirectImage` the underlying presheaf of the direct image is a
right Kan extension and the limit of a right Kan extension is the limit of the functor extended,
`CategoryTheory.Functor.ranCompLimIso` — the argument of
`...SmallSite.zariskiGlobalSectionsDirectImageIso`.  The third factor is restriction
`i_X^{-1} = π_{X, *}` to the small crystalline site: read through
`CategoryTheory.Sheaf.ΓNatIsoLim` the factor is invertibility of the canonical
`CategoryTheory.Limits.limit.pre` along `i_X`, i.e. that the limit of a *sheaf* on `CRIS(X/S)` is
already computed over the full subcategory `Cris(X/S)`, and that follows from
`...CrystallineThickening.coversTop_ι` directly — separatedness by
`CategoryTheory.GrothendieckTopology.CoversTop.ext` and gluing by amalgamating the cone of limit
projections as a compatible family of elements. -/
abbrev CrisGlobalSectionsComparison :=
  crisDirectImage S S' fS fX hf ⋙ globalSections S' ≅ globalSections S

/-- **The Leray factorization of [Stacks, Tag 015M] for `f_cris`:**
`RΓ(Cris(X'/S), -) ≅ Rf_{cris, *} ⋙ RΓ(Cris(X/S), -)`.  **Unconditional.**

This is `...SmallSite.derivedGlobalSectionsFunctorIsoPushforward`, whose two inputs are
that the direct image preserve injective abelian sheaves and the underived comparison of global
sections.  The first is `preservesInjectiveObjects_crisDirectImage` above; the second is
`crisGlobalSectionsIso`.  Both are proved, so this factorization takes no datum. -/
def derivedCrisGlobalSectionsIso :
    derivedGlobalSectionsFunctor S ≅
      derivedCrisDirectImageFunctor S S' fS fX hf ⋙ derivedGlobalSectionsFunctor S' :=
  derivedGlobalSectionsFunctorIsoPushforward S S' (crisDirectImage S S' fS fX hf)
    (crisGlobalSectionsIso S S' fS fX hf)

/-- **`f^*` on derived crystalline global sections**,
`RΓ(Cris(X/S), ℱ) ⟶ RΓ(Cris(X'/S), ℱ')`: push the derived unit `ℱ[0] ⟶ Rf_{cris, *}ℱ'[0]` into
`RΓ(Cris(X/S), -)` and read the result through the Leray factorization.  **Unconditional.** -/
def derivedCrisPullbackMap
    (F : Sheaf (smallTopology S') AddCommGrpCat.{u + 1}) :
    (derivedGlobalSections S').obj F ⟶
      (derivedGlobalSections S).obj (crisPullback S S' fS fX hf F) :=
  (derivedGlobalSectionsFunctor S').map (derivedCrisUnit S S' fS fX hf F) ≫
    (derivedCrisGlobalSectionsIso S S' fS fX hf).inv.app
      ((DerivedCategory.Plus.singleFunctor
        (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) 0).obj
          (crisPullback S S' fS fX hf F))

/-- **`f^* : H^i(Cris(X/S), ℱ) ⟶ H^i(Cris(X'/S), ℱ')`**, the map of [Stacks, Tag 07QA], as a
morphism of `AddCommGrpCat.{u + 1}`.  It is `derivedCrisPullbackMap` read in degree `i` through
`...SmallSite.homologyDerivedGlobalSectionsIsoObj`, which identifies the cohomology of
`RΓ(Cris(X/S), -)` with the library's
`Crystalline.GlobalCrystallineSituation.SmallSite.cohomology`.

This is the map whose kernel and cokernel [Stacks, Tag 07QA] bounds, and it takes no datum
beyond the morphism of situations (the global-sections comparison it needs is
`crisGlobalSectionsIso`).  It is bounded, for any morphism whose cone satisfies
`Annihilation07Q9`, by `...SmallSite.pow_smul_eq_zero_of_crisCohomologyMap_eq_zero_07QA` and
`...SmallSite.exists_crisCohomologyMap_eq_pow_smul_07QA` of
`SmallSite/CrisCohomologyBound07QA.lean`, which take that annihilation and, for the cokernel half,
the monomorphism as inputs and place no tag.  [Stacks, Tag 07QA] itself is
`...SmallSite.annihilated_ker_coker_crisModuleCohomologyMap_of_isIteratedAlphaPCover` of
`SmallSite/CrisCohomologyBound07QAMain.lean`, for the module-level map
`...SmallSite.crisModuleCohomologyMap` (this map of the underlying abelian sheaf followed by the
comparison of the abelian inverse image with the module pullback), and it discharges both inputs.
The three inputs of the bound are:

The commutation `CrisZariskiSquare` of the square of topoi, which is
`...SmallSite.crisZariskiSquare` of `SmallSite/CrisZariskiSquareIso.lean`; and the coherence of
this map's Leray factorization with the Zariski one across that square, which is
`...SmallSite.crisZariskiLerayCoherence` of `SmallSite/UnderivedLerayCoherence.lean` — its five
edges are all declarations of this library and all unconditional, the fourth Leray factorization
among them, [Stacks, Tag 015M] for `f_{Zar}`, being
`...SmallSite.derivedZariskiGlobalSectionsIsoPushforward` of
`SmallSite/ZariskiPushforwardLeray.lean`.  With it,
`...SmallSite.derivedZariskiGlobalSections_map_derivedZariskiComparison_of_coherence` of
`SmallSite/HypercohomologyBound07QA.lean` identifies `derivedCrisPullbackMap` with
`RΓ(X_Zar, -)` applied to `derivedZariskiComparison`, with no further input; that is what
transports a bound from the Zariski comparison to this map.  Reading the bounds in a fixed
degree `i` additionally wants `H^i(X_Zar, K) ≅ Hom(P, K⟦i⟧)` for a complex `K` and a concrete
`P` — the constant sheaf `ℤ_X` placed in degree zero and shifted: the corepresentation
is `...SmallSite.derivedZariskiGlobalSectionsHomologyShiftAddEquiv` of
`SmallSite/ZariskiHypercohomology.lean`, and it is proved without `HasExt`, by recognising
`H^n(RΓ(X_Zar, -))` and `Hom(ℤ_X[0], (-)⟦n⟧)` as right derived functors of one and the same
functor on `K⁺`.

And the annihilation of the triangle of [Stacks, Tag 07Q9], which rests on
[Stacks, Proposition 07LG]: `SmallSite/HypercohomologyBound07QA.lean` states the two bounds on
cohomology groups for any annihilator of that triangle (and, for the cokernel half, the
monomorphism `ℋ^0` of the comparison), and the annihilation itself, for a crystal in
quasi-coherent modules, is `...SmallSite.annihilation07Q9_of_isIteratedAlphaPCover`. -/
def crisCohomologyMap
    (F : Sheaf (smallTopology S') AddCommGrpCat.{u + 1}) (i : ℕ) :
    (cohomologyFunctor S' i).obj F ⟶
      (cohomologyFunctor S i).obj (crisPullback S S' fS fX hf F) :=
  (homologyDerivedGlobalSectionsIsoObj S' F i).inv ≫
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} (i : ℤ)).map
      (derivedCrisPullbackMap S S' fS fX hf F) ≫
    (homologyDerivedGlobalSectionsIsoObj S (crisPullback S S' fS fX hf F) i).hom

end Leray

/-! ### The statement of [Stacks, Tag 07Q9] -/

section Statement

/-- **The conclusion of [Stacks, Tag 07Q9] for a given morphism `α` of `D⁺(Ab(X_Zar))`**: in every
distinguished triangle `A ⟶ B ⟶ E ⟶ A[1]` on `α`, the cohomology sheaves of `E` are annihilated
by `q`.

The quantification over *every* distinguished triangle is how the source's "the distinguished
triangle" is read: such a triangle is unique only up to isomorphism and the conclusion is
invariant under isomorphism.  This matches the idiom of
`Stacks.Triangulated.pow_smul_id_eq_zero_of_chainComp`. -/
def Annihilation07Q9 [HasDerivedCategory.{w'} (Sheaf (opensTopology S') AddCommGrpCat.{u + 1})]
    (q : ℕ) {A B : DerivedCategory.Plus (Sheaf (opensTopology S') AddCommGrpCat.{u + 1})}
    (α : A ⟶ B) : Prop :=
  ∀ (E : DerivedCategory.Plus (Sheaf (opensTopology S') AddCommGrpCat.{u + 1}))
    (v : B ⟶ E) (wE : E ⟶ A⟦(1 : ℤ)⟧),
    Triangle.mk α v wE ∈
        distTriang (DerivedCategory.Plus (Sheaf (opensTopology S') AddCommGrpCat.{u + 1})) →
      ∀ j : ℤ, (q : ℤ) • 𝟙 ((DerivedCategory.Plus.homologyFunctor
        (Sheaf (opensTopology S') AddCommGrpCat.{u + 1}) j).obj E) = 0

/-- **The conclusion of [Stacks, Tag 07Q9] feeds the bounds of [Stacks, Tag 07QA] with no
transfer.**  `Annihilation07Q9` is phrased in `D⁺(Ab(X_Zar))` and the two bounds below are
phrased in the unbounded `D(Ab(X_Zar))`; the gap between them is only apparent, because
`DerivedCategory.Plus.homologyFunctor` is by definition `DerivedCategory.Plus.ι` followed by
`DerivedCategory.homologyFunctor`.  So the annihilation hypothesis the bounds want is exactly
what `Annihilation07Q9` gives, and this lemma is its restatement in the form they consume.

What connects the two is therefore *not* boundedness, nor the commutation `CrisZariskiSquare`
of the square of topoi, which is `...SmallSite.crisZariskiSquare`.  It is the inputs named in the
docstring of `crisCohomologyMap`: [Stacks, Proposition 07LG] (through
`...SmallSite.annihilation07Q9_of_isIteratedAlphaPCover`), and the coherence of that map's Leray
factorization with the Zariski one across the square (`...SmallSite.crisZariskiLerayCoherence`).
-/
theorem smul_id_homologyFunctor_ι_obj₃_eq_zero
    [HasDerivedCategory.{w'} (Sheaf (opensTopology S') AddCommGrpCat.{u + 1})] (q : ℕ)
    {A B E : DerivedCategory.Plus (Sheaf (opensTopology S') AddCommGrpCat.{u + 1})} {α : A ⟶ B}
    (h : Annihilation07Q9 S' q α) (v : B ⟶ E) (wE : E ⟶ A⟦(1 : ℤ)⟧)
    (hT : Triangle.mk α v wE ∈
      distTriang (DerivedCategory.Plus (Sheaf (opensTopology S') AddCommGrpCat.{u + 1})))
    (j : ℤ) :
    (q : ℤ) • 𝟙 ((DerivedCategory.homologyFunctor
      (Sheaf (opensTopology S') AddCommGrpCat.{u + 1}) j).obj
        (DerivedCategory.Plus.ι.obj E)) = 0 :=
  h E v wE hT j

include hf

/-- **The statement of [Stacks, Tag 07Q9], reduced to the data its comparison map is missing.**
For `f : X' ⟶ X` an iterated `α_p`-cover of constant degree `q` and `ℱ` an abelian sheaf on
`Cris(X/S)`, the third term of every distinguished triangle on the comparison map
`Ru_{X/S, *}ℱ ⟶ Rf_{Zar, *}Ru_{X'/S, *}ℱ'` has cohomology sheaves annihilated by `q`.

The commutation `sq` of the square of topoi is quantified over; the canonical one is
`...SmallSite.crisZariskiSquare`.  The coefficients range over *every* abelian sheaf `ℱ`, so this
proposition is formally stronger than [Stacks, Tag 07Q9], which is stated for a crystal in
quasi-coherent modules — that restriction is where the proof lives, through
[Stacks, Proposition 07LG].

This is a proposition, not a theorem, and no declaration of the library proves it.  [Stacks,
Tag 07Q9] itself, for a crystal in quasi-coherent modules and the module comparison map, is
`...SmallSite.annihilation07Q9_of_isIteratedAlphaPCover` of `SmallSite/AlphaPCover07Q9Main.lean`.
-/
def Statement07Q9 [HasDerivedCategory.{w} (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})]
    [HasDerivedCategory.{w} (Sheaf (smallTopology S') AddCommGrpCat.{u + 1})]
    [HasDerivedCategory.{w'} (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})]
    [HasDerivedCategory.{w'} (Sheaf (opensTopology S') AddCommGrpCat.{u + 1})]
    (q : ℕ) : Prop :=
  IsIteratedAlphaPCover S'.p fX → HasConstantDegree fX q →
    ∀ (sq : CrisZariskiSquare S S' fS fX hf)
      (F : Sheaf (smallTopology S') AddCommGrpCat.{u + 1}),
      Annihilation07Q9 S' q (derivedZariskiComparison S S' fS fX hf sq F)

end Statement

/-! ### The bounds of [Stacks, Tag 07QA] -/

section Bounds

variable {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]

/-- **The kernel bound of [Stacks, Tag 07QA].**  Let `W ⟶ A ⟶ B ⟶ W⟦1⟧` be a distinguished
triangle in `D(𝒜)` with `W` concentrated in degrees `≥ 0` and every cohomology object of `W` in
degree `≤ i` annihilated by `q`, and let `P` be concentrated in degrees `≤ i`.  Then `q^{i + 1}`
annihilates every morphism `P ⟶ A` killed by `A ⟶ B`.

Applied to the inverse rotation `E⟦-1⟧ ⟶ A ⟶ B ⟶ E` of the triangle of [Stacks, Tag 07Q9] — so
that `W = E⟦-1⟧` is concentrated in degrees `≥ 0` exactly when `E` is concentrated in degrees
`≥ -1` — with `P` the unit object, this is the statement that `q^{i + 1}` annihilates the kernel of
`H^i(X, Ru_{X/S, *}ℱ) ⟶ H^i(X, f_*Ru_{X'/S, *}ℱ')`.

The hypothesis is the one [Stacks, Tag 07QA] has for free: `A` and `B` are direct images of
sheaves placed in degree zero, so both are concentrated in degrees `≥ 0` and its cone `E` is
concentrated in degrees `≥ -1` by `Stacks.Triangulated.isGE_obj₃_sub_one`.  No vanishing of
`ℋ^{-1}(E)` is needed: the kernel is a quotient of `H^{i - 1}(X, E)`, whose filtration runs over
the `i + 1` degrees `-1, 0, …, i - 1`, and the source's exponent `q^{i + 1}` is exactly that
count.  The cokernel is the half that needs more, and `exists_comp_mor₁_eq_pow_smul_07QA` below
is where the extra hypothesis appears. -/
theorem pow_smul_eq_zero_of_kernel_07QA (q i : ℕ) (T : Triangle (DerivedCategory 𝒜))
    (hT : T ∈ distTriang (DerivedCategory 𝒜)) [T.obj₁.IsGE 0]
    (hW : ∀ j : ℤ, j ≤ (i : ℤ) →
      (q : ℤ) • 𝟙 ((DerivedCategory.homologyFunctor 𝒜 j).obj T.obj₁) = 0)
    (P : DerivedCategory 𝒜) [P.IsLE (i : ℤ)] (g : P ⟶ T.obj₂) (hg : g ≫ T.mor₂ = 0) :
    ((q : ℤ) ^ (i + 1)) • g = 0 := by
  simpa using Stacks.Triangulated.pow_smul_eq_zero_of_comp_mor₂_eq_zero
    (𝒜 := 𝒜) (q : ℤ) 0 (i : ℤ) T hT hW P g hg

/-- **The cokernel bound of [Stacks, Tag 07QA].**  Let `A ⟶ B ⟶ E ⟶ A⟦1⟧` be a distinguished
triangle in `D(𝒜)` with `E` concentrated in degrees `≥ 0` and every cohomology object of `E` in
degree `≤ i` annihilated by `q`, and let `P` be concentrated in degrees `≤ i`.  Then `q^{i + 1}`
times any morphism `P ⟶ B` factors through `A ⟶ B`.

With `P` the unit object this is the statement that `q^{i + 1}` annihilates the cokernel of
`H^i(X, Ru_{X/S, *}ℱ) ⟶ H^i(X, f_*Ru_{X'/S, *}ℱ')`.  The hypothesis that `E` be concentrated in
degrees `≥ 0` is what makes the exponent `i + 1` rather than `i + 2`: [Stacks, Tag 07QA] observes
only that `E` has cohomology in degrees `-1` and up, and the filtration count over the degrees
`-1, 0, …, i` gives `i + 2`.  The vanishing of `ℋ^{-1}(E)`, equivalently the injectivity of
`ℋ^0(A) ⟶ ℋ^0(B)`, is therefore part of the hypothesis here and not derived. -/
theorem exists_comp_mor₁_eq_pow_smul_07QA (q i : ℕ) (T : Triangle (DerivedCategory 𝒜))
    (hT : T ∈ distTriang (DerivedCategory 𝒜)) [T.obj₃.IsGE 0]
    (hE : ∀ j : ℤ, j ≤ (i : ℤ) →
      (q : ℤ) • 𝟙 ((DerivedCategory.homologyFunctor 𝒜 j).obj T.obj₃) = 0)
    (P : DerivedCategory 𝒜) [P.IsLE (i : ℤ)] (g : P ⟶ T.obj₂) :
    ∃ h : P ⟶ T.obj₁, ((q : ℤ) ^ (i + 1)) • g = h ≫ T.mor₁ := by
  obtain ⟨h, hh⟩ := Stacks.Triangulated.exists_comp_mor₁_eq_pow_smul
    (𝒜 := 𝒜) (q : ℤ) 0 (i : ℤ) T hT hE P g
  exact ⟨h, by simpa using hh⟩

/-- **The cokernel bound of [Stacks, Tag 07QA], with the hypothesis the geometry supplies.**  Let
`A ⟶ B ⟶ E ⟶ A⟦1⟧` be a distinguished triangle in `D(𝒜)` with `A` and `B` concentrated in
degrees `≥ 0`, with `ℋ^0(A) ⟶ ℋ^0(B)` a monomorphism, and with every cohomology object of `E` in
degree `≤ i` annihilated by `q`.  Then for `P` concentrated in degrees `≤ i` the scalar
`q^{i + 1}` times any morphism `P ⟶ B` factors through `A ⟶ B`.

This is `exists_comp_mor₁_eq_pow_smul_07QA` with its concentration hypothesis replaced by what
the triangle of [Stacks, Tag 07Q9] actually offers.  There `A = Ru_{X/S, *}ℱ` and
`B = f_*Ru_{X'/S, *}ℱ'` are direct images of sheaves placed in degree zero, so both are
concentrated in degrees `≥ 0` with no argument, and `ℋ^0(A) ⟶ ℋ^0(B)` is
`u_{X/S, *}` applied to the adjunction unit `ℱ ⟶ f_{cris, *}f_cris^*ℱ`, which is injective for an
iterated `α_p`-cover because the completed divided power envelope `D ⟶ D'` of
[Stacks, Tag 07N1] is a split injection of `D`-modules; `u_{X/S, *}` is left exact and so
preserves that monomorphism.  The concentration of `E` in degrees `≥ 0` — equivalently the
vanishing of `ℋ^{-1}(E)`, which is what forces the source's exponent `q^{i + 1}` rather than
`q^{i + 2}` — is then the conclusion of
`Stacks.Triangulated.isGE_obj₃_of_mono_homologyMap` rather than an assumption. -/
theorem exists_comp_mor₁_eq_pow_smul_07QA_of_mono (q i : ℕ) (T : Triangle (DerivedCategory 𝒜))
    (hT : T ∈ distTriang (DerivedCategory 𝒜)) [T.obj₁.IsGE 0] [T.obj₂.IsGE 0]
    (hmono : Mono ((DerivedCategory.homologyFunctor 𝒜 0).map T.mor₁))
    (hE : ∀ j : ℤ, j ≤ (i : ℤ) →
      (q : ℤ) • 𝟙 ((DerivedCategory.homologyFunctor 𝒜 j).obj T.obj₃) = 0)
    (P : DerivedCategory 𝒜) [P.IsLE (i : ℤ)] (g : P ⟶ T.obj₂) :
    ∃ h : P ⟶ T.obj₁, ((q : ℤ) ^ (i + 1)) • g = h ≫ T.mor₁ :=
  have : T.obj₃.IsGE (0 - 1) := Stacks.Triangulated.isGE_obj₃_sub_one T hT 0
  have : T.obj₃.IsGE 0 := Stacks.Triangulated.isGE_obj₃_of_mono_homologyMap T hT 0 hmono
  exists_comp_mor₁_eq_pow_smul_07QA q i T hT hE P g

end Bounds

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
