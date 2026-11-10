module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.CohomologicalGysinMap
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.CounitCompatibleGeometric
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinMapDeRham
public import
  StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.SupportedEndoForgetDegreewise
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.BottomHomologyEdge
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.CounitGysinEdgeExact
public import
  StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.UnderlyingAbelianSheafCohomology
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.AbelianGysinEdge

/-!
# Stacks 0G8B: the cohomological Gysin maps and the de Rham differentials

Let `π : X ⟶ S` be a morphism of schemes, let `f₁, …, f_c ∈ Γ(X, 𝒪_X)` with `c = c' + 1` and let
`i : Z ⟶ X` be the closed subscheme they cut out.  [Stacks, Tag 0G8A] attaches to the Gysin map
`γ^p_{f₁, …, f_c}` of [Stacks, Tag 0G83] the maps on cohomology

`γ^{p, q} : H^q(X, i_*Ω^p_{Z/S}) ⟶ H^{q + c}(X, Ω^{p + c}_{X/S})`,

and [Stacks, Tag 0G8B] says that they are compatible with the de Rham differentials on
`Ω^•_{X/S}` and `Ω^•_{Z/S}`.  The source's proof is the sheaf-level statement
[Stacks, Tag 0G85] — or its glued form [Stacks, Tag 0G87] — together with functoriality of
cohomology.

**The de Rham differential is not `𝒪_X`-linear**, so it is not a morphism of `X.Modules` and the
cohomology functor `Hfunctor` of [Stacks, Tag 01E3] does not act on it.  The arrow it induces on
the cohomology groups `Hgroup` is built here: cohomology of a sheaf of modules over an open is
the cohomology of its underlying abelian sheaf, by [Stacks, Tag 0D5Y] part (1), and an arbitrary
morphism of abelian sheaves acts on the latter.  That is `abelianHgroupMap`, and it is
constructed, not assumed; `abelianDerivedMap_map` checks that on an `𝒪_X`-linear morphism it is
the functorial action.  This is the cohomological counterpart of
`AlgebraicGeometry.Scheme.Hom.gysinTargetDeRhamMap`, which does the same for the local cohomology
sheaf using [Stacks, Tag 0G74] part (2).

## Main definitions

* `globalSectionsForgetIso`: **forgetting the module structure does not change derived global
  sections**, [Stacks, Tag 0D5Y] part (1) at the open `⊤`, as a named isomorphism of the functor
  `derivedGlobalSections` of `StacksFrontier.AlgebraicGeometry.DeRham.Gysin.CohomologicalGysinMap`
  with the derived global sections of the underlying abelian sheaf.
* `forgetSingleMap`: a morphism of underlying abelian sheaves, placed in a single degree of the
  derived category of abelian sheaves and read on the forgetful image of the module placed in that
  degree.
* `abelianDerivedMap` and `abelianHgroupMap`: **the action of a morphism of underlying abelian
  sheaves on derived global sections, resp. on the cohomology groups `Hgroup`.**  This is the
  arrow the de Rham differential induces on Hodge cohomology.
* `SupportVanishing` and `supportedLocalCohomology`: the vanishing hypothesis of
  [Stacks, Tag 0G8A] and the target `i_*ℋ ᶜ_Z(ℱ)` of the sheaf-level Gysin map, named for
  legibility.
* `EdgeCommutesWithAbelian`: the Gysin edge morphism `supportedGysinEdge` of
  [Stacks, Tag 0G8A] is natural in the ambient module for morphisms of the *underlying abelian
  sheaves*, the local cohomology sheaf acting on such a morphism by [Stacks, Tag 0G74] part (2).
  It says nothing about a differential, and it is **proved**, as `edgeCommutesWithAbelian`.
* `forgetEdgeSourceCompare` and `forgetLocalCohomologyComparison`: the comparison between the
  sources of the two Gysin edge morphisms, and its degree-`c` content.
* `forgetComparisonAsIso`: the auxiliary out of which `globalSectionsForgetIso` is read; the
  implementation notes say why it exists.

## Main results

* `cohomologyMapOfSingleHom_abelianHgroupMap`: **a commuting square of the derived category of
  abelian sheaves gives a commuting square on cohomology groups**, for the map
  `cohomologyMapOfSingleHom` that [Stacks, Tag 0G8A] is built out of.  This is the cohomological
  half of the argument and it is proved here.
* `gysinCohomologyMap_comm`: the same for `gysinCohomologyMap`, the cohomological Gysin map of
  [Stacks, Tag 0G8A], from the sheaf-level square and the compatibility of the Gysin edge
  morphism.
* `abelianDerivedMap_map`, `abelianDerivedMap_id`, `abelianDerivedMap_comp`,
  `abelianHgroupMap_id` and `abelianHgroupMap_comp`: **the abelian action extends the
  `𝒪_X`-linear one and is functorial.**  The first is what pins `abelianDerivedMap` down as the
  right notion rather than merely a map of the right type.
* `forgetSingleMap_comp_left` and `forgetSingleMap_comp_right`: an `𝒪_X`-linear morphism placed
  in the same degree is absorbed into the morphism of abelian sheaves.  These are the naturality
  of `forgetSingle` and they are what paste the sheaf-level square into the derived square.
* `gysinCohomologyMap_congr`: transport of `gysinCohomologyMap` along an equality of the ambient
  module, which carries the degree bookkeeping `p + 1 + c = p + c + 1`.
* `gysinTargetReindex_eq_eqToHom`: the degree transport of the square of [Stacks, Tag 0G85] is
  the transport `gysinCohomologyMap_congr` consumes.
* `edge_deRham`: `EdgeCommutesWithAbelian` at the two terms of the de Rham complex and at the
  differential between them.
* `equationGysinHodgeMap_eq`: the tagged [Stacks, Tag 0G8A] map on `H^q(Z, Ω^p_{Z/S})` is the
  one used here preceded by the affine-pushforward comparison of [Stacks, Tag 089W].
* `gysinCohomologyMap_comm_deRham` and `gysinCohomologyMap_reindex_eq`: the square with the
  degree transport folded into the Gysin map, and the unfolding of that transport.
* `forgetSingleMap_map`: forgetting the module structure, applied to an `𝒪_X`-linear morphism
  placed in a single degree, is `forgetSingleMap` at its underlying morphism of abelian sheaves.
* `supportedGysinEdge_naturality`: **the Gysin edge morphism of [Stacks, Tag 0G8A] is natural in
  the coefficient complex**, which is the one statement about that morphism the library did not
  have.  The comparison `ℋ ᶜ_Z(K)[-c] ⟶ Rℋ_Z(K)` it is built from is natural by
  `Stacks.BottomHomologyEdge.naturality`.
* `supportedGysinEdge_eq_edge`: **the Gysin edge morphism is `Stacks.CounitGysinEdge.edge` at the
  module data**, by `rfl`, so that it and the abelian-side edge morphism
  `Stacks.Cohomology.AbelianSupportedCounit.abelianSupportedGysinEdge` are the same construction
  at different data.
* `edgeCommutesWithAbelian_map`: **`EdgeCommutesWithAbelian` holds for the underlying morphism of
  abelian sheaves of an `𝒪_X`-linear morphism.**  That is *not* the case it is wanted in; see the
  implementation notes.
* `edgeCommutesWithAbelian`: **`EdgeCommutesWithAbelian` holds**, so nothing of the square is
  carried.  `derivedForget_supportedGysinEdge_square` reduces it to the square
  `edgeSourceCompare_square` on the sources of the two edge morphisms, which is
  `forgetLocalCohomologyComparison_natural` placed in degree `c`.
* `equationGysinCohomologyMap_comm_deRham`: **the square of [Stacks, Tag 0G8B] for the Gysin maps
  `γ^{p,q}` of the equation-chart Gysin map of [Stacks, Tag 0G83]**, with the vanishing of
  [Stacks, Tag 0G8A] assumed.  The tag itself sits on
  `Stacks.DeRham.GysinCohomologyDeRhamKoszul.koszulGysinCohomologyMap_comm_deRham`, where the
  square is at the glued Gysin map of [Stacks, Tag 0G86] and the vanishing is derived from
  smoothness and Koszul-regularity rather than assumed; this statement is one of its inputs.

## Implementation notes

**What is proved.**  The passage from the sheaf-level square of [Stacks, Tag 0G85] to the square
on cohomology groups: the sheaf-level square is pushed into the derived category of abelian
sheaves by the single functor, pasted with the compatibility of the Gysin edge morphism, carried
through derived global sections by the naturality of `globalSectionsForgetIso`, and read on the
cohomology groups through `cohomologyDerivedSingleIso`, whose four occurrences cancel in pairs.
The sheaf-level input is `AlgebraicGeometry.Scheme.Hom.gysinMapCommutesWithDeRham`, which is
[Stacks, Tag 0G85] itself and is proved unconditionally.

**Nothing is carried.**  `EdgeCommutesWithAbelian` — that forgetting the module structure carries
the Gysin edge morphism `i_*ℋ ᶜ_Z(ℱ)[-c] ⟶ ℱ` of [Stacks, Tag 0G8A] to the corresponding morphism
for the underlying abelian sheaves — is proved here, as `edgeCommutesWithAbelian`.  It is
[Stacks, Tag 0G74] **part (2)** — the source's part (1) is `RΓ_Z(X, K) ⟶ RΓ_Z(X, K_ab)`, and the
sheafy `Rℋ_Z(K) ⟶ Rℋ_Z(K_ab)` is part (2) — together with the compatibility of the counit of
[Stacks, Tag 0A3B] with the same forgetting, and the proof is in three steps:

* `Stacks.CounitGysinEdge.mapDerivedCategory_edge` says that an exact functor carries the generic
  edge morphism to the generic edge morphism, granted
  `Stacks.CounitGysinEdge.CounitCompatible`.  That hypothesis at the geometric data is
  `Stacks.DeRham.CounitCompatibleGeometric.counitCompatible`; the two edge morphisms are the
  generic construction by `supportedGysinEdge_eq_edge` and
  `Stacks.Cohomology.AbelianSupportedCounit.abelianSupportedGysinEdge_eq_edge`.
* `Stacks.CounitGysinEdge.mapDerivedCategory_edge_square` adds the naturality of the abelian edge
  morphism and so reduces the square to a square between the **sources**, which mentions no edge
  morphism and no counit.  At the geometric data that reduction is
  `derivedForget_supportedGysinEdge_square`.
* that square is `edgeSourceCompare_square`, which is
  `forgetLocalCohomologyComparison_natural` placed in degree `c`.  The degree-`c` statement
  identifies the comparison `forgetLocalCohomologyComparison` — the unbounded reading of
  [Stacks, Tag 0G74] part (2) for the Gysin map's target — with the classical-model reading
  `Stacks.Perfect.AbelianSupportedEndoModelBridge.pushIsoApp`, by
  `forgetLocalCohomologyComparison_comp`, which is
  `Stacks.Perfect.SupportedEndoForgetDegreewise.derivedForgetIdentity` and
  `Stacks.Perfect.SupportedEndoForgetDegreewise.pushHomologySingle_pushIsoApp_eq_endoForgetIsoApp`;
  the action of `i_*ℋ ᶜ_Z` on a
  morphism of the underlying abelian sheaves is a conjugation on both sides, and what remains is
  the naturality of the abelian model bridge `modelBeta`.

**Where the spelling had to be settled.**  The instantiation of `CounitCompatible` at the
geometric data is the crux, and what stood in the way was not mathematics but three instances;
the implementation notes of
`StacksFrontier.AlgebraicGeometry.DeRham.Gysin.CounitCompatibleGeometric` record them.  In short:
the category of abelian sheaves on the closed subspace has two definitionally equal spellings,
and `HasDerivedCategory` is found only at the one `derivedAbelianSupportedSectionsOnClosed` uses,
while `Additive`, `PreservesFiniteLimits` and `PreservesFiniteColimits` of the forgetful functor
are then no longer found at that spelling and have to be named.

**The `𝒪_X`-linear case, kept.**  `supportedGysinEdge_naturality` is the square for a morphism of
`D(𝒪_X)`, and `edgeCommutesWithAbelian_map` reads it as `EdgeCommutesWithAbelian`'s square at the
underlying morphism of abelian sheaves of a morphism of `X.Modules`.  A de Rham differential is
the forgetful image of no such morphism, so that special case is not what the tag needs; it is
kept because it checks the two vertical arrows of the square against one another independently of
the derived-category chase, and it is the counterpart one level down of
`Stacks.Perfect.GysinAbelianSquare.cokernelLastDifToSupport_abelian_square_mapPresheaf`.

**The vanishing hypothesis is the source's own.**  `hvan` is [Stacks, Tag 0G8A]'s own assumption
that `ℋ^j_Z(Ω^{p+c}_{X/S}) = 0` for `j < c`, without which `γ^{p,q}` does not exist.  The
sufficient condition the source offers for it, [Stacks, Tag 0G7P], is not available: this
library's 0G7P, `Stacks.Perfect.LocalCohomologyDegrees`
`.isZero_homology_derivedSupportedSections_of_locallyKoszulRegular`, proves only the
complementary vanishing in degrees `j > c` and says so in its own attribute.  Smoothness of `π`
and Koszul regularity of `i` are therefore **not consumed**; they are carried because
[Stacks, Tag 0G8B] states them, and the module of
`StacksFrontier.AlgebraicGeometry.DeRham.Gysin.CohomologicalGysinMap` records the same situation for
[Stacks, Tag 0G8A].

**Cohomology is taken on `X`.**  The source of `γ^{p,q}` is written `H^q(X, i_*Ω^p_{Z/S})`, which
is the convention `gysinCohomologyMap` is stated in and the shape the Gysin map of
[Stacks, Tag 0G83] has its source in; `equationGysinHodgeMap_eq` records that the source's own
`H^q(Z, Ω^p_{Z/S})` differs from it by the affine-pushforward comparison of [Stacks, Tag 089W],
which is what the tagged [Stacks, Tag 0G8A] composes with.  Rewriting the square in that shape
would need the compatibility of that comparison with `abelianHgroupMap`, which the library does
not have, so the square is stated on `X`, exactly as this development's [Stacks, Tag 0G8D] is.

**Why `globalSectionsForgetIso` goes through a helper.**  `derivedGlobalSections X` and
`Stacks.Cohomology.OpenSubspace.derivedSectionsOnOpen (structureSheafRing X) ⊤` are the same
functor, but the two spellings carry different `HasRightDerivedFunctor` instance terms; ascribing
the result type while asking for `IsIso` of the comparison makes instance search look for the
instance at the ascribed spelling and fail.  `forgetComparisonAsIso` is therefore stated without
an ascription and `globalSectionsForgetIso` is the same term read at the spelling the rest of the
file uses.  No compiler option is raised anywhere here.

**Why the assembly is split and why one transport is carried as a parameter.**  The last step —
reading the folded square `gysinCohomologyMap_comm_deRham` in the shape of the tag — is a single
rewrite along `gysinTargetReindex_eq_eqToHom`, but written that way the kernel does not finish:
the rewrite builds a motive over the whole `gysinCohomologyMap` application and then has to
re-check it against the degree identification `p + 1 + c = p + c + 1`, and it exceeds the
deterministic timeout.  So `gysinCohomologyMap_congr` takes the transport as a parameter `τ`
together with the equation `hτ` pinning it to the canonical one, which turns the rewrite into an
application; `edge_deRham` likewise unfolds the carried hypothesis once, in a statement that
mentions nothing else.  With that the whole file elaborates and is checked in a few seconds at
the default limits.

**One naturality is not available and is not claimed.**  `cohomologyDerivedSingleIso`, the
identification of the degree-`m` cohomology of the derived global sections of a module placed in
degree `a` with `H^{m-a}(X, -)`, is
`Stacks.DerivedFunctor.homologyTotalRightDerivedSingleShiftIso`,
which is built from a chosen injective resolution and comes with no naturality.  So
`abelianHgroupMap` cannot be identified with `Hfunctor.map` on an `𝒪_X`-linear morphism, and that
is not asserted: `abelianDerivedMap_map` is the corresponding statement one level down, on derived
global sections, where it is true and proved.  The same gap is recorded for `pullbackHgroup` in
`StacksFrontier.AlgebraicGeometry.DeRham.Gysin.CohomologicalBaseChange`.

## References

* [Stacks Project, Tag 0G8B](https://stacks.math.columbia.edu/tag/0G8B)
* [Stacks Project, Tag 0G8A](https://stacks.math.columbia.edu/tag/0G8A)
* [Stacks Project, Tag 0G85](https://stacks.math.columbia.edu/tag/0G85)
* [Stacks Project, Tag 0G83](https://stacks.math.columbia.edu/tag/0G83)
* [Stacks Project, Tag 0G87](https://stacks.math.columbia.edu/tag/0G87)
* [Stacks Project, Tag 0G8D](https://stacks.math.columbia.edu/tag/0G8D)
* [Stacks Project, Lemma 20.34.8 (Tag 0G74)](https://stacks.math.columbia.edu/tag/0G74)
* [Stacks Project, Lemma 20.32.7 (Tag 0D5Y)](https://stacks.math.columbia.edu/tag/0D5Y)
* [Stacks Project, Tag 0A3B](https://stacks.math.columbia.edu/tag/0A3B)
* [Stacks Project, Lemma 20.34.6 (Tag 0G72)](https://stacks.math.columbia.edu/tag/0G72)
* [Stacks Project, Tag 0G7P](https://stacks.math.columbia.edu/tag/0G7P)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
* [Stacks Project, Tag 01E3](https://stacks.math.columbia.edu/tag/01E3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.SupportedComplexes
open Stacks.Cohomology.UnderlyingAbelianSheaf
open Stacks.DeRham.CohomologicalGysin

namespace Stacks.DeRham.GysinCohomologyDeRham

universe u

open DerivedCategory

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.Topology.RingedSpaceSheafifyOpens.opensHasSheafifyAddCommGrpCat
  Stacks.Topology.RingedSpaceSheafifyOpens.opensWEqualsLocallyBijectiveAddCommGrpCat

-- Sheaves of modules on a ringed space have a derived category.  The choice
-- `HasDerivedCategory.standard _` pins the universes, so it is made once, in
-- `CohomologicalGysinMap`, and only the instance attribute is re-attached here.
attribute [local instance] Stacks.DeRham.CohomologicalGysin.moduleSheavesHasDerivedCategory

/-! ### Cohomology of the underlying abelian sheaf -/

/-- Sheaves of abelian groups on the space underlying a ringed space. -/
abbrev AbSheaves (X : RingedSpace.{u, u}) : Type (u + 1) :=
  Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}

/-- **Forgetting the `𝒪_X`-module structure.**  For a scheme this is
`Stacks.Perfect.AbelianFraction.abelianSheaf`, in which the abelian constructions of
[Stacks, Tag 0G85] are stated. -/
abbrev forgetModules (X : RingedSpace.{u, u}) : RModules X ⥤ AbSheaves X :=
  SheafOfModules.toSheaf.{u} (structureSheafRing X)

/-- Forgetting the `𝒪_X`-module structure on the unbounded derived category.  The forgetful
functor is exact, so it acts on derived categories without being derived. -/
abbrev derivedForget (X : RingedSpace.{u, u}) :
    DerivedCategory (RModules X) ⥤ DerivedCategory (AbSheaves X) :=
  underlyingDerivedSheaf (structureSheafRing X)

/-- Unbounded derived global sections of sheaves of abelian groups. -/
abbrev derivedAbelianGlobalSections (X : RingedSpace.{u, u}) :
    DerivedCategory (AbSheaves X) ⥤ DerivedCategory AddCommGrpCat.{u} :=
  derivedAbelianSectionsOnOpen X.carrier ⊤

/-- The comparison of [Stacks, Tag 0D5Y] part (1) at the open `⊤`, as an isomorphism.  It is
stated without ascribing the type of the two functors; see the implementation notes.  It is an
auxiliary of `globalSectionsForgetIso`, which is the same term at the spelling of
`derivedGlobalSections`. -/
def forgetComparisonAsIso (X : RingedSpace.{u, u}) :=
  letI : IsIso (sectionsForgetComparison (structureSheafRing X) (⊤ : Opens X.carrier)) :=
    sectionsForgetComparison_isIso (structureSheafRing X) (⊤ : Opens X.carrier)
  asIso (sectionsForgetComparison (structureSheafRing X) (⊤ : Opens X.carrier))

/-- **Forgetting the module structure does not change derived global sections**, [Stacks, Tag
0D5Y] part (1): the canonical comparison `RΓ(X, K) ⟶ RΓ(X, K_ab)` is an isomorphism, naturally
in `K`.  The source is `derivedGlobalSections`, the functor the cohomological Gysin map of
[Stacks, Tag 0G8A] is built with. -/
def globalSectionsForgetIso (X : RingedSpace.{u, u}) :
    derivedGlobalSections X ≅ derivedForget X ⋙ derivedAbelianGlobalSections X :=
  forgetComparisonAsIso X

/-- Placing a module in a single degree commutes with forgetting its module structure: the
forgetful functor is exact, so this is `CategoryTheory.Functor.mapDerivedCategorySingleFunctor`. -/
abbrev forgetSingle (X : RingedSpace.{u, u}) (a : ℤ) :
    DerivedCategory.singleFunctor (RModules X) a ⋙ derivedForget X ≅
      forgetModules X ⋙ DerivedCategory.singleFunctor (AbSheaves X) a :=
  (forgetModules X).mapDerivedCategorySingleFunctor a

/-- **A morphism `ψ : ℱ_ab ⟶ 𝒢_ab` of underlying abelian sheaves, placed in degree `a`**: the
morphism `ℱ_ab[-a] ⟶ 𝒢_ab[-a]` of the derived category of abelian sheaves, read as a morphism
between the forgetful images of `ℱ[-a]` and `𝒢[-a]` through `forgetSingle`.  The morphism `ψ` is
**not** required to be `𝒪_X`-linear, which is what a de Rham differential is not. -/
def forgetSingleMap (X : RingedSpace.{u, u}) (a : ℤ) {A B : RModules X}
    (ψ : (forgetModules X).obj A ⟶ (forgetModules X).obj B) :
    (derivedForget X).obj ((DerivedCategory.singleFunctor (RModules X) a).obj A) ⟶
      (derivedForget X).obj ((DerivedCategory.singleFunctor (RModules X) a).obj B) :=
  (forgetSingle X a).hom.app A ≫
    (DerivedCategory.singleFunctor (AbSheaves X) a).map ψ ≫ (forgetSingle X a).inv.app B

/-- `forgetSingleMap` at the underlying abelian morphism of `φ` is the forgetful image of `φ`. -/
private theorem forgetSingleMap_forget_map (X : RingedSpace.{u, u}) (a : ℤ) {A B : RModules X}
    (φ : A ⟶ B) :
    forgetSingleMap X a ((forgetModules X).map φ) =
      (derivedForget X).map ((DerivedCategory.singleFunctor (RModules X) a).map φ) := by
  have h := (forgetSingle X a).hom.naturality φ
  simp only [Functor.comp_map] at h
  rw [forgetSingleMap, ← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id_app,
    Category.comp_id]

/-- Precomposing `forgetSingleMap` with an `𝒪_X`-linear morphism placed in the same degree
absorbs it into the morphism of abelian sheaves.  This is the naturality of `forgetSingle`. -/
theorem forgetSingleMap_comp_left (X : RingedSpace.{u, u}) (a : ℤ) {A A₁ B : RModules X}
    (φ : A ⟶ A₁) (ψ : (forgetModules X).obj A₁ ⟶ (forgetModules X).obj B) :
    (derivedForget X).map ((DerivedCategory.singleFunctor (RModules X) a).map φ) ≫
        forgetSingleMap X a ψ =
      forgetSingleMap X a ((forgetModules X).map φ ≫ ψ) := by
  have h := (forgetSingle X a).hom.naturality φ
  simp only [Functor.comp_map] at h
  simp only [forgetSingleMap, Functor.map_comp, Category.assoc]
  rw [← Category.assoc, h, Category.assoc]

/-- Postcomposing `forgetSingleMap` with an `𝒪_X`-linear morphism placed in the same degree
absorbs it into the morphism of abelian sheaves.  This is the naturality of `forgetSingle`. -/
theorem forgetSingleMap_comp_right (X : RingedSpace.{u, u}) (a : ℤ) {A B B₁ : RModules X}
    (ψ : (forgetModules X).obj A ⟶ (forgetModules X).obj B₁) (φ : B₁ ⟶ B) :
    forgetSingleMap X a ψ ≫
        (derivedForget X).map ((DerivedCategory.singleFunctor (RModules X) a).map φ) =
      forgetSingleMap X a (ψ ≫ (forgetModules X).map φ) := by
  have h := (forgetSingle X a).inv.naturality φ
  simp only [Functor.comp_map] at h
  simp only [forgetSingleMap, Functor.map_comp, Category.assoc]
  rw [← h]

/-- **The action on derived global sections of a morphism of underlying abelian sheaves**, for
modules placed in degree `a`: pass to the derived global sections of the abelian sheaves by
`globalSectionsForgetIso`, act there, and come back. -/
def abelianDerivedMap (X : RingedSpace.{u, u}) (a : ℤ) {A B : RModules X}
    (ψ : (forgetModules X).obj A ⟶ (forgetModules X).obj B) :
    (derivedGlobalSections X).obj ((DerivedCategory.singleFunctor (RModules X) a).obj A) ⟶
      (derivedGlobalSections X).obj ((DerivedCategory.singleFunctor (RModules X) a).obj B) :=
  (globalSectionsForgetIso X).hom.app _ ≫
    (derivedAbelianGlobalSections X).map (forgetSingleMap X a ψ) ≫
      (globalSectionsForgetIso X).inv.app _

/-- **The abelian action extends the `𝒪_X`-linear one.**  On the underlying morphism of abelian
sheaves of a morphism `φ` of `𝒪_X`-modules, `abelianDerivedMap` is the derived global sections of
`φ` placed in degree `a`.  This is the naturality of `forgetSingle` and of
`globalSectionsForgetIso`, and nothing else; it is what pins `abelianDerivedMap` down as the right
notion rather than merely a map of the right type. -/
theorem abelianDerivedMap_map (X : RingedSpace.{u, u}) (a : ℤ) {A B : RModules X} (φ : A ⟶ B) :
    abelianDerivedMap X a ((forgetModules X).map φ) =
      (derivedGlobalSections X).map ((DerivedCategory.singleFunctor (RModules X) a).map φ) := by
  have hnat := (globalSectionsForgetIso X).hom.naturality
    ((DerivedCategory.singleFunctor (RModules X) a).map φ)
  simp only [Functor.comp_map] at hnat
  rw [abelianDerivedMap, forgetSingleMap_forget_map, ← Category.assoc, ← hnat, Category.assoc,
    Iso.hom_inv_id_app, Category.comp_id]

/-- The abelian action on derived global sections sends the identity to the identity. -/
theorem abelianDerivedMap_id (X : RingedSpace.{u, u}) (a : ℤ) (A : RModules X) :
    abelianDerivedMap X a (𝟙 ((forgetModules X).obj A)) = 𝟙 _ := by
  rw [← CategoryTheory.Functor.map_id (forgetModules X) A, abelianDerivedMap_map]
  simp

/-- The abelian action on derived global sections is compatible with composition. -/
theorem abelianDerivedMap_comp (X : RingedSpace.{u, u}) (a : ℤ) {A B C : RModules X}
    (ψ : (forgetModules X).obj A ⟶ (forgetModules X).obj B)
    (ψ' : (forgetModules X).obj B ⟶ (forgetModules X).obj C) :
    abelianDerivedMap X a (ψ ≫ ψ') = abelianDerivedMap X a ψ ≫ abelianDerivedMap X a ψ' := by
  simp only [abelianDerivedMap, forgetSingleMap, Functor.map_comp, Category.assoc,
    Iso.inv_hom_id_app_assoc]
  simp

/-- **The action on the cohomology groups of a morphism of underlying abelian sheaves.**  For
`n = m - a`, this is the map `H^n(X, ℱ) ⟶ H^n(X, 𝒢)` induced by a morphism `ℱ_ab ⟶ 𝒢_ab` which
need not be `𝒪_X`-linear: `abelianDerivedMap` in degree `m`, read on the cohomology groups
through `cohomologyDerivedSingleIso`.

**This is the arrow a de Rham differential induces on Hodge cohomology**, and it is the vertical
arrow of the square of [Stacks, Tag 0G8B].  The degree `a` in which the module is placed is free
because the square needs it at `a = c` on the source side and at `a = 0` on the target side,
exactly as for `Stacks.DeRham.GysinCohomologyBaseChange.pullbackHgroup`. -/
def abelianHgroupMap (X : RingedSpace.{u, u}) (a m : ℤ) (n : ℕ) (hn : m - a = n)
    {A B : RModules X} (ψ : (forgetModules X).obj A ⟶ (forgetModules X).obj B) :
    Hgroup (structureSheafRing X) ⊤ n A ⟶ Hgroup (structureSheafRing X) ⊤ n B :=
  (cohomologyDerivedSingleIso X A a m n hn).inv ≫
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u} m).map (abelianDerivedMap X a ψ) ≫
      (cohomologyDerivedSingleIso X B a m n hn).hom

/-- The abelian action on cohomology groups sends the identity to the identity. -/
theorem abelianHgroupMap_id (X : RingedSpace.{u, u}) (a m : ℤ) (n : ℕ) (hn : m - a = n)
    (A : RModules X) :
    abelianHgroupMap X a m n hn (𝟙 ((forgetModules X).obj A)) = 𝟙 _ := by
  rw [abelianHgroupMap, abelianDerivedMap_id]
  simp

/-- The abelian action on cohomology groups is compatible with composition. -/
theorem abelianHgroupMap_comp (X : RingedSpace.{u, u}) (a m : ℤ) (n : ℕ) (hn : m - a = n)
    {A B C : RModules X} (ψ : (forgetModules X).obj A ⟶ (forgetModules X).obj B)
    (ψ' : (forgetModules X).obj B ⟶ (forgetModules X).obj C) :
    abelianHgroupMap X a m n hn (ψ ≫ ψ') =
      abelianHgroupMap X a m n hn ψ ≫ abelianHgroupMap X a m n hn ψ' := by
  simp only [abelianHgroupMap, abelianDerivedMap_comp, Functor.map_comp, Category.assoc,
    Iso.hom_inv_id_assoc]

/-! ### A derived square gives a square on cohomology -/

/-- **A commuting square of the derived category of abelian sheaves gives a commuting square on
cohomology groups.**  For `Φ : 𝒜[-c] ⟶ ℱ` and `Φ' : 𝒜'[-c] ⟶ ℱ'` in `D(𝒪_X)` whose forgetful
images are compatible with two morphisms `ψ_𝒜`, `ψ_ℱ` of underlying abelian sheaves, the maps
`cohomologyMapOfSingleHom` they induce commute with the abelian actions on cohomology.

Derived global sections carry the square to a square by the naturality of
`globalSectionsForgetIso`, and the identifications `cohomologyDerivedSingleIso` of the four
cohomology groups cancel in pairs.  This is the abelian counterpart of
`Stacks.DeRham.GysinCohomologyBaseChange.cohomologyMapOfSingleHom_pullbackHgroup`. -/
theorem cohomologyMapOfSingleHom_abelianHgroupMap (X : RingedSpace.{u, u}) (c q : ℕ)
    {A F A' F' : RModules X}
    (ψA : (forgetModules X).obj A ⟶ (forgetModules X).obj A')
    (ψF : (forgetModules X).obj F ⟶ (forgetModules X).obj F')
    (Φ : (DerivedCategory.singleFunctor (RModules X) (c : ℤ)).obj A ⟶
      (DerivedCategory.singleFunctor (RModules X) (0 : ℤ)).obj F)
    (Φ' : (DerivedCategory.singleFunctor (RModules X) (c : ℤ)).obj A' ⟶
      (DerivedCategory.singleFunctor (RModules X) (0 : ℤ)).obj F')
    (hsq : (derivedForget X).map Φ ≫ forgetSingleMap X (0 : ℤ) ψF =
      forgetSingleMap X (c : ℤ) ψA ≫ (derivedForget X).map Φ') :
    cohomologyMapOfSingleHom X A F c q Φ ≫
        abelianHgroupMap X (0 : ℤ) ((q : ℤ) + (c : ℤ)) (q + c) (by omega) ψF =
      abelianHgroupMap X (c : ℤ) ((q : ℤ) + (c : ℤ)) q (by omega) ψA ≫
        cohomologyMapOfSingleHom X A' F' c q Φ' := by
  have hnat : ∀ {K L : DerivedCategory (RModules X)} (u : K ⟶ L),
      (derivedGlobalSections X).map u =
        (globalSectionsForgetIso X).hom.app _ ≫
          (derivedAbelianGlobalSections X).map ((derivedForget X).map u) ≫
            (globalSectionsForgetIso X).inv.app _ :=
    fun u => (NatIso.naturality_2 (globalSectionsForgetIso X) u).symm
  have key : (derivedGlobalSections X).map Φ ≫ abelianDerivedMap X (0 : ℤ) ψF =
      abelianDerivedMap X (c : ℤ) ψA ≫ (derivedGlobalSections X).map Φ' := by
    rw [hnat Φ, hnat Φ', abelianDerivedMap, abelianDerivedMap]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc, ← Functor.map_comp_assoc]
    rw [hsq]
  have hH := congrArg (DerivedCategory.homologyFunctor AddCommGrpCat.{u}
    ((q : ℤ) + (c : ℤ))).map key
  simp only [Functor.map_comp] at hH
  simp only [cohomologyMapOfSingleHom, abelianHgroupMap, Category.assoc, Iso.hom_inv_id_assoc]
  rw [reassoc_of% hH]

/-! ### The cohomological Gysin map and a morphism of underlying abelian sheaves -/

/-- **The vanishing hypothesis of [Stacks, Tag 0G8A]**: the local cohomology sheaves
`ℋ ^i_Z(ℱ)` vanish in the degrees `i < c`.  Without it the cohomological Gysin map does not
exist. -/
abbrev SupportVanishing (X : RingedSpace.{u, u}) (Z : Set X.carrier) (hZ : IsClosed Z) (c : ℕ)
    (F : RModules X) : Prop :=
  ∀ i : ℤ, i < (c : ℤ) → IsZero (localCohomologySheafOfComplex X Z hZ i
    ((DerivedCategory.singleFunctor (RModules X) (0 : ℤ)).obj F))

/-- **The sheaf `i_*ℋ ᶜ_Z(ℱ)`, read on `X`**: the target of the sheaf-level Gysin map, in the
shape the construction of [Stacks, Tag 0G8A] consumes. -/
abbrev supportedLocalCohomology (X : RingedSpace.{u, u}) (Z : Set X.carrier) (hZ : IsClosed Z)
    (c : ℕ) (F : RModules X) : RModules X :=
  (modulePushforward (closedSubsetInclusion X Z)).obj
    (localCohomologySheafOfComplex X Z hZ (c : ℤ)
      ((DerivedCategory.singleFunctor (RModules X) (0 : ℤ)).obj F))

/-- **Forgetting the module structure, applied to an `𝒪_X`-linear morphism placed in degree
`a`, is `forgetSingleMap` at its underlying morphism of abelian sheaves.**  This is the
naturality of `forgetSingle`; it is the step inside `abelianDerivedMap_map` that identifies the
abelian action with the functorial one, named here because the square of [Stacks, Tag 0G8B] needs
it one level up, in the derived category rather than on derived global sections. -/
theorem forgetSingleMap_map (X : RingedSpace.{u, u}) (a : ℤ) {A B : RModules X} (φ : A ⟶ B) :
    forgetSingleMap X a ((forgetModules X).map φ) =
      (derivedForget X).map ((DerivedCategory.singleFunctor (RModules X) a).map φ) :=
  forgetSingleMap_forget_map X a φ

/-- **The Gysin edge morphism of [Stacks, Tag 0G8A] is natural in the coefficient complex.**  For
`g : K ⟶ K'` a morphism of `D(𝒪_X)` whose source and target both satisfy the vanishing hypothesis
of that tag, the square formed by the two edge morphisms `i_*ℋ ᶜ_Z(-)[-c] ⟶ -`, by `g` and by
`i_*ℋ ᶜ_Z(g)` placed in degree `c` commutes.

Three naturalities and nothing else: that of `CategoryTheory.Functor`
`.mapDerivedCategorySingleFunctor` at the direct image, that of the comparison
`ℋ ᶜ_Z(K)[-c] ⟶ Rℋ_Z(K)` — which is
`Stacks.BottomHomologyEdge.naturality`, the edge morphism out of the bottom cohomology object
having no naturality of its own, being built from `CategoryTheory.inv` of a component of the
truncation projection — and that of the counit of [Stacks, Tag 0A3B]. -/
theorem supportedGysinEdge_naturality (X : RingedSpace.{u, u}) (Z : Set X.carrier)
    (hZ : IsClosed Z) (c : ℤ) {K K' : DerivedCategory (RModules X)}
    (hvan : ∀ i : ℤ, i < c → IsZero (localCohomologySheafOfComplex X Z hZ i K))
    (hvan' : ∀ i : ℤ, i < c → IsZero (localCohomologySheafOfComplex X Z hZ i K'))
    (g : K ⟶ K') :
    (DerivedCategory.singleFunctor (RModules X) c).map
          ((modulePushforward (closedSubsetInclusion X Z)).map
            ((DerivedCategory.homologyFunctor (SupportedModules X Z) c).map
              ((derivedSupportedSectionsOnClosed X Z hZ).map g))) ≫
        supportedGysinEdge Z hZ c K' hvan' =
      supportedGysinEdge Z hZ c K hvan ≫ g := by
  let := pushforward_preservesFiniteLimits X Z
  let := pushforward_preservesFiniteColimits X Z hZ
  have : ((derivedSupportedSectionsOnClosed X Z hZ).obj K).IsGE c :=
    (DerivedCategory.isGE_iff _ c).2 hvan
  have : ((derivedSupportedSectionsOnClosed X Z hZ).obj K').IsGE c :=
    (DerivedCategory.isGE_iff _ c).2 hvan'
  have hsingle := ((modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategorySingleFunctor
    c).inv.naturality ((DerivedCategory.homologyFunctor (SupportedModules X Z) c).map
      ((derivedSupportedSectionsOnClosed X Z hZ).map g))
  simp only [Functor.comp_map] at hsingle
  have hedge : (DerivedCategory.singleFunctor (SupportedModules X Z) c).map
          ((DerivedCategory.homologyFunctor (SupportedModules X Z) c).map
            ((derivedSupportedSectionsOnClosed X Z hZ).map g)) ≫
        localCohomologySingleToDerived Z hZ c K' hvan' =
      localCohomologySingleToDerived Z hZ c K hvan ≫
        (derivedSupportedSectionsOnClosed X Z hZ).map g :=
    Stacks.BottomHomologyEdge.naturality c ((derivedSupportedSectionsOnClosed X Z hZ).map g)
  have hcounit := (derivedPushforwardAdjunction X Z hZ).counit.naturality g
  simp only [Functor.comp_map, Functor.id_map] at hcounit
  dsimp only [supportedGysinEdge]
  rw [← Category.assoc, hsingle, Category.assoc, Category.assoc, ← Functor.map_comp_assoc,
    hedge, Functor.map_comp, Category.assoc, hcounit, Category.assoc]

/-- **The Gysin edge morphism of [Stacks, Tag 0G8A] is `Stacks.CounitGysinEdge.edge` at the module
data**, by `rfl`: the derived supported sections on the closed subset, the direct image along its
inclusion, and the counit of the adjunction of [Stacks, Tag 0A3B].

The abelian counterpart is
`Stacks.Cohomology.AbelianSupportedCounit.abelianSupportedGysinEdge_eq_edge`, so the two edge
morphisms are the same construction at different data. -/
theorem supportedGysinEdge_eq_edge (X : RingedSpace.{u, u}) (Z : Set X.carrier)
    (hZ : IsClosed Z) (c : ℤ) (K : DerivedCategory (RModules X))
    (hvan : ∀ i : ℤ, i < c → IsZero (localCohomologySheafOfComplex X Z hZ i K)) :
    letI := pushforward_preservesFiniteLimits X Z
    letI := pushforward_preservesFiniteColimits X Z hZ
    haveI : ((derivedSupportedSectionsOnClosed X Z hZ).obj K).IsGE c :=
      (DerivedCategory.isGE_iff _ c).2 hvan
    supportedGysinEdge Z hZ c K hvan =
      Stacks.CounitGysinEdge.edge (derivedSupportedSectionsOnClosed X Z hZ)
        (modulePushforward (closedSubsetInclusion X Z))
        (derivedPushforwardAdjunction X Z hZ).counit c K :=
  rfl

/-! ### The Gysin edge morphism against an arbitrary morphism of abelian sheaves -/

section EdgeSquare

open Stacks.Cohomology.AbelianSupportedCounit
open Stacks.Cohomology.ModulePushforwardComparison
open Stacks.DeRham.CounitCompatibleGeometric

attribute [local instance] Stacks.DeRham.CounitCompatibleGeometric.toSheaf_preservesFiniteColimits
attribute [local instance] Stacks.DeRham.CounitCompatibleGeometric.forgetClosed_additive
  Stacks.DeRham.CounitCompatibleGeometric.forgetClosed_preservesFiniteLimits
  Stacks.DeRham.CounitCompatibleGeometric.forgetClosed_preservesFiniteColimits

variable (X : RingedSpace.{u, u}) (Z : Set X.carrier) (hZ : IsClosed Z)

/-- **The comparison between the sources of the two Gysin edge morphisms**, at the geometric data:
`Stacks.CounitGysinEdge.edgeSourceCompare` at the two forgetful functors, the two direct images
and the comparison of [Stacks, Tag 0G74] part (2).  It identifies the forgetful image of
`i_*ℋ ᶜ_Z(K)[-c]` with `i_*^{ab}ℋ ᶜ_Z(K_ab)[-c]`. -/
def forgetEdgeSourceCompare (c : ℤ) (K : DerivedCategory (RModules X)) :
    letI := pushforward_preservesFiniteLimits X Z
    letI := pushforward_preservesFiniteColimits X Z hZ
    letI := abelianClosedPushforward_preservesFiniteLimits X Z hZ
    letI := abelianClosedPushforward_preservesFiniteColimits X Z hZ
    (derivedForget X).obj ((DerivedCategory.singleFunctor (RModules X) c).obj
        ((modulePushforward (closedSubsetInclusion X Z)).obj
          ((DerivedCategory.homologyFunctor (SupportedModules X Z) c).obj
            ((derivedSupportedSectionsOnClosed X Z hZ).obj K)))) ⟶
      (DerivedCategory.singleFunctor (AbSheaves X) c).obj
        ((abelianClosedPushforward Z).obj
          ((DerivedCategory.homologyFunctor
              (Sheaf (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat.{u}) c).obj
            ((derivedAbelianSupportedSectionsOnClosed X Z hZ).obj
              ((derivedForget X).obj K)))) :=
  letI := pushforward_preservesFiniteLimits X Z
  letI := pushforward_preservesFiniteColimits X Z hZ
  letI := abelianClosedPushforward_preservesFiniteLimits X Z hZ
  letI := abelianClosedPushforward_preservesFiniteColimits X Z hZ
  Stacks.CounitGysinEdge.edgeSourceCompare
    (modulePushforward (closedSubsetInclusion X Z))
    (_root_.SheafOfModules.toSheaf.{u} (structureSheafRing X))
    (forgetClosed X Z)
    (abelianClosedPushforward Z)
    (modulePushforwardCompToSheafIso (closedSubsetInclusion X Z))
    (derivedSupportedSectionsOnClosed X Z hZ)
    (derivedAbelianSupportedSectionsOnClosed X Z hZ)
    (forgetLocalCohomologyIso X Z hZ) c K


/-- **The forgetful image of the Gysin edge morphism of [Stacks, Tag 0G8A] is natural along an
arbitrary morphism `g` of the derived category of abelian sheaves**, as soon as the corresponding
arrow `t` on the sources makes the square `ht` commute against `forgetEdgeSourceCompare`.

This is `Stacks.CounitGysinEdge.mapDerivedCategory_edge_square` at the geometric data, with its
one hypothesis supplied by `Stacks.DeRham.CounitCompatibleGeometric.counitCompatible`; the edge
morphism is recognised as the generic construction by `supportedGysinEdge_eq_edge`.  Note that `g`
is **not** required to be the image of a morphism of `D(𝒪_X)`, which is the whole point: a de Rham
differential is the forgetful image of no morphism of `X.Modules`. -/
theorem derivedForget_supportedGysinEdge_square (c : ℤ) {K K' : DerivedCategory (RModules X)}
    (hvan : ∀ i : ℤ, i < c → IsZero (localCohomologySheafOfComplex X Z hZ i K))
    (hvan' : ∀ i : ℤ, i < c → IsZero (localCohomologySheafOfComplex X Z hZ i K'))
    (g : (derivedForget X).obj K ⟶ (derivedForget X).obj K')
    (t : (derivedForget X).obj ((DerivedCategory.singleFunctor (RModules X) c).obj
          ((modulePushforward (closedSubsetInclusion X Z)).obj
            ((DerivedCategory.homologyFunctor (SupportedModules X Z) c).obj
              ((derivedSupportedSectionsOnClosed X Z hZ).obj K)))) ⟶
        (derivedForget X).obj ((DerivedCategory.singleFunctor (RModules X) c).obj
          ((modulePushforward (closedSubsetInclusion X Z)).obj
            ((DerivedCategory.homologyFunctor (SupportedModules X Z) c).obj
              ((derivedSupportedSectionsOnClosed X Z hZ).obj K')))))
    (ht : t ≫ forgetEdgeSourceCompare X Z hZ c K' =
      forgetEdgeSourceCompare X Z hZ c K ≫ (DerivedCategory.singleFunctor (AbSheaves X) c).map
        ((abelianClosedPushforward Z).map
          ((DerivedCategory.homologyFunctor
              (Sheaf (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat.{u}) c).map
            ((derivedAbelianSupportedSectionsOnClosed X Z hZ).map g)))) :
    (derivedForget X).map (supportedGysinEdge Z hZ c K hvan) ≫ g =
      t ≫ (derivedForget X).map (supportedGysinEdge Z hZ c K' hvan') := by
  let := pushforward_preservesFiniteLimits X Z
  let := pushforward_preservesFiniteColimits X Z hZ
  let := abelianClosedPushforward_preservesFiniteLimits X Z hZ
  let := abelianClosedPushforward_preservesFiniteColimits X Z hZ
  have : ((derivedSupportedSectionsOnClosed X Z hZ).obj K).IsGE c :=
    (DerivedCategory.isGE_iff _ c).2 hvan
  have : ((derivedSupportedSectionsOnClosed X Z hZ).obj K').IsGE c :=
    (DerivedCategory.isGE_iff _ c).2 hvan'
  rw [supportedGysinEdge_eq_edge X Z hZ c K hvan, supportedGysinEdge_eq_edge X Z hZ c K' hvan']
  exact Stacks.CounitGysinEdge.mapDerivedCategory_edge_square
    (modulePushforward (closedSubsetInclusion X Z))
    (_root_.SheafOfModules.toSheaf.{u} (structureSheafRing X))
    (forgetClosed X Z)
    (abelianClosedPushforward Z)
    (modulePushforwardCompToSheafIso (closedSubsetInclusion X Z))
    (derivedSupportedSectionsOnClosed X Z hZ)
    (derivedAbelianSupportedSectionsOnClosed X Z hZ)
    (forgetLocalCohomologyIso X Z hZ)
    (derivedPushforwardAdjunction X Z hZ).counit
    (abelianSupportPushCounit X Z hZ)
    (counitCompatible X Z hZ) c K K' g t ht

end EdgeSquare

/-- **The cohomological Gysin map of [Stacks, Tag 0G8A] commutes with the actions of two
morphisms of underlying abelian sheaves**, granted the sheaf-level square `hsheaf` for the Gysin
maps and the compatibility `hedge` of the Gysin edge morphism.

The sheaf-level square is pushed into the derived category of abelian sheaves by
`forgetSingleMap_comp_left` and `forgetSingleMap_comp_right`, pasted with `hedge`, and fed to
`cohomologyMapOfSingleHom_abelianHgroupMap`.  Nothing about a differential appears: `ψA`, `ψF` and
`ψT` are arbitrary morphisms of abelian sheaves. -/
theorem gysinCohomologyMap_comm (X : RingedSpace.{u, u}) (Z : Set X.carrier) (hZ : IsClosed Z)
    (c q : ℕ) {A F A' F' : RModules X}
    (hvan : SupportVanishing X Z hZ c F) (hvan' : SupportVanishing X Z hZ c F')
    (γ : A ⟶ supportedLocalCohomology X Z hZ c F)
    (γ' : A' ⟶ supportedLocalCohomology X Z hZ c F')
    (ψA : (forgetModules X).obj A ⟶ (forgetModules X).obj A')
    (ψF : (forgetModules X).obj F ⟶ (forgetModules X).obj F')
    (ψT : (forgetModules X).obj (supportedLocalCohomology X Z hZ c F) ⟶
      (forgetModules X).obj (supportedLocalCohomology X Z hZ c F'))
    (hsheaf : (forgetModules X).map γ ≫ ψT = ψA ≫ (forgetModules X).map γ')
    (hedge : (derivedForget X).map
          (supportedGysinEdge Z hZ (c : ℤ)
            ((DerivedCategory.singleFunctor (RModules X) (0 : ℤ)).obj F) hvan) ≫
        forgetSingleMap X (0 : ℤ) ψF =
      forgetSingleMap X (c : ℤ) ψT ≫ (derivedForget X).map
        (supportedGysinEdge Z hZ (c : ℤ)
          ((DerivedCategory.singleFunctor (RModules X) (0 : ℤ)).obj F') hvan')) :
    gysinCohomologyMap Z hZ c A F hvan γ q ≫
        abelianHgroupMap X (0 : ℤ) ((q : ℤ) + (c : ℤ)) (q + c) (by omega) ψF =
      abelianHgroupMap X (c : ℤ) ((q : ℤ) + (c : ℤ)) q (by omega) ψA ≫
        gysinCohomologyMap Z hZ c A' F' hvan' γ' q := by
  refine cohomologyMapOfSingleHom_abelianHgroupMap X c q ψA ψF _ _ ?_
  rw [Functor.map_comp, Category.assoc, hedge, ← Category.assoc, forgetSingleMap_comp_left,
    hsheaf, ← forgetSingleMap_comp_right, Category.assoc, ← Functor.map_comp]

/-- **Transport of the cohomological Gysin map along an equality of the ambient module.**  It is
what carries the degree bookkeeping of the square of [Stacks, Tag 0G8B]: the Gysin map in degree
`p` lands in `Ω^{p+c}_{X/S}`, so the differential following it lands in `Ω^{p+c+1}_{X/S}`, whereas
the Gysin map in degree `p + 1` lands in `Ω^{p+1+c}_{X/S}`, and those two terms of the de Rham
complex are equal but not definitionally equal for variable `p` and `c`. -/
theorem gysinCohomologyMap_congr (X : RingedSpace.{u, u}) (Z : Set X.carrier) (hZ : IsClosed Z)
    (c q : ℕ) {A F F₁ : RModules X} (h : F = F₁)
    (hvan : SupportVanishing X Z hZ c F) (hvan₁ : SupportVanishing X Z hZ c F₁)
    (γ : A ⟶ supportedLocalCohomology X Z hZ c F)
    (τ : supportedLocalCohomology X Z hZ c F ⟶ supportedLocalCohomology X Z hZ c F₁)
    (hτ : τ = eqToHom (congrArg (supportedLocalCohomology X Z hZ c) h)) :
    gysinCohomologyMap Z hZ c A F hvan γ q ≫
        eqToHom (congrArg (Hgroup (structureSheafRing X) ⊤ (q + c)) h) =
      gysinCohomologyMap Z hZ c A F₁ hvan₁ (γ ≫ τ) q := by
  subst h
  subst hτ
  simp

/-! ### Stacks 0G8B for the Gysin map of a family of equations -/

section DeRham

open AlgebraicGeometry.Scheme.Hom
open Stacks.Perfect.CechDerivedSupport (equationsClosedSet isClosed_equationsClosedSet)

variable {Z X S : Scheme.{u}}

attribute [local instance] isQuasicoherent_relativeDifferentialForms

/-- **The Gysin edge morphism is natural for morphisms of the underlying abelian sheaves.**
For `𝒪_X`-modules `ℱ`, `𝒢` satisfying the vanishing hypothesis of
[Stacks, Tag 0G8A] and an arbitrary — in particular not `𝒪_X`-linear — morphism
`ψ : ℱ_ab ⟶ 𝒢_ab`, the square formed by the two Gysin edge morphisms
`i_*ℋ ᶜ_Z(-)[-c] ⟶ -` of `supportedGysinEdge`, by `ψ` placed in degree `0` and by the action of
`i_*ℋ ᶜ_Z` on `ψ` supplied by [Stacks, Tag 0G74] part (2), commutes in the derived category of
abelian sheaves on `X`.

Mathematically this is [Stacks, Tag 0G74] part (2) together with the compatibility of the counit
of the adjunction of [Stacks, Tag 0A3B] with forgetting the module structure.  It **holds**:
`edgeCommutesWithAbelian` proves it, and the implementation notes say from what.  It is kept as a
named proposition because `edge_deRham` and `gysinCohomologyMap_comm_deRham` consume it one
unfolding at a time, for the elaboration reason recorded in the implementation notes.
`edgeCommutesWithAbelian_map` is the special case of `ψ` the forgetful image of an `𝒪_X`-linear
morphism, proved directly.
**It says nothing about a de Rham differential**, `ψ` being arbitrary.

It is stated for an arbitrary closed subset `T ⊆ X` and an arbitrary degree `c`, which is the
generality every ingredient of its proof already had: the two cases it is used in are the common
zero locus of a global family of equations, where it feeds
`equationGysinCohomologyMap_comm_deRham`, and the image `Set.range i.base` of a closed immersion,
where it feeds the glued [Stacks, Tag 0G8B] of
`StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinCohomologyDeRhamConormal`. -/
def EdgeCommutesWithAbelian {T : Set X} (hT : IsClosed T) (c : ℕ) : Prop :=
  ∀ (F G : X.Modules)
    (hF : SupportVanishing X.toRingedSpace T hT c F)
    (hG : SupportVanishing X.toRingedSpace T hT c G)
    (ψ : (forgetModules X.toRingedSpace).obj F ⟶ (forgetModules X.toRingedSpace).obj G),
    (derivedForget X.toRingedSpace).map
          (supportedGysinEdge T hT (c : ℤ)
            ((DerivedCategory.singleFunctor (RModules X.toRingedSpace) (0 : ℤ)).obj F) hF) ≫
        forgetSingleMap X.toRingedSpace (0 : ℤ) ψ =
      forgetSingleMap X.toRingedSpace (c : ℤ)
          (Stacks.Perfect.GysinAbelianSquare.pushforwardLocalCohomologyAbelianMap hT c ψ) ≫
        (derivedForget X.toRingedSpace).map
          (supportedGysinEdge T hT (c : ℤ)
            ((DerivedCategory.singleFunctor (RModules X.toRingedSpace) (0 : ℤ)).obj G) hG)

/-- **`EdgeCommutesWithAbelian` holds for the underlying morphism of abelian sheaves of an
`𝒪_X`-linear morphism.**  For `ψ` the forgetful image of a morphism `φ : ℱ ⟶ 𝒢` of `X.Modules`
the square is the forgetful image of `supportedGysinEdge_naturality` at `φ` placed in degree `0`:
the left-hand vertical becomes `φ` placed in degree `0` by `forgetSingleMap_map`, and the
right-hand one becomes the functorial action of `i_*ℋ ᶜ_Z` by
`Stacks.Perfect.GysinAbelianSquare.pushforwardLocalCohomologyAbelianMap_map`.

This is **not** the case `EdgeCommutesWithAbelian` is wanted in — a de Rham differential is
`f⁻¹𝒪_S`-linear and is the forgetful image of no morphism of `X.Modules` — exactly as
`Stacks.Perfect.GysinAbelianSquare.cokernelLastDifToSupport_abelian_square_mapPresheaf` is not the
case [Stacks, Tag 0G85] needs.  Its purpose is the same: it checks that the two vertical arrows of
the square are matched to one another, so that what remains open is isolated in the
non-`𝒪_X`-linearity and nowhere else. -/
theorem edgeCommutesWithAbelian_map {T : Set X} (hT : IsClosed T) (c : ℕ) {F G : X.Modules}
    (hF : SupportVanishing X.toRingedSpace T hT c F)
    (hG : SupportVanishing X.toRingedSpace T hT c G)
    (φ : F ⟶ G) :
    (derivedForget X.toRingedSpace).map
          (supportedGysinEdge T hT
            (c : ℤ)
            ((DerivedCategory.singleFunctor (RModules X.toRingedSpace) (0 : ℤ)).obj F) hF) ≫
        forgetSingleMap X.toRingedSpace (0 : ℤ) ((forgetModules X.toRingedSpace).map φ) =
      forgetSingleMap X.toRingedSpace (c : ℤ)
          (Stacks.Perfect.GysinAbelianSquare.pushforwardLocalCohomologyAbelianMap hT c
            ((forgetModules X.toRingedSpace).map φ)) ≫
        (derivedForget X.toRingedSpace).map
          (supportedGysinEdge T hT
            (c : ℤ)
            ((DerivedCategory.singleFunctor (RModules X.toRingedSpace) (0 : ℤ)).obj G) hG) := by
  have e1 := (congrArg (forgetSingleMap X.toRingedSpace (c : ℤ))
    (Stacks.Perfect.GysinAbelianSquare.pushforwardLocalCohomologyAbelianMap_map hT c φ)).trans
    (forgetSingleMap_map X.toRingedSpace (c : ℤ) _)
  refine (congrArg _ (forgetSingleMap_map X.toRingedSpace (0 : ℤ) (A := F) (B := G) φ)).trans ?_
  refine Eq.trans ?_ (congrArg (· ≫ _) e1).symm
  exact (((derivedForget X.toRingedSpace).map_comp _ _).symm.trans
    (congrArg (derivedForget X.toRingedSpace).map
      (supportedGysinEdge_naturality X.toRingedSpace T hT (c : ℤ) hF hG _).symm)).trans
    ((derivedForget X.toRingedSpace).map_comp _ _)

section AbelianEdge

open Stacks.Cohomology.AbelianSupportedCounit
open Stacks.Cohomology.ModulePushforwardComparison
open Stacks.DeRham.CounitCompatibleGeometric
open Stacks.Perfect.AbelianFraction (abelianSheaf)
open Stacks.Perfect.AbelianSupportedEndoModelBridge (pushIsoApp)
open Stacks.Perfect.AbelianSupportedEndoModelFactors
open Stacks.Perfect.GysinAbelianSquare (abelianClosedPushforward
  abelianLocalCohomologyPushforward pushforwardLocalCohomologyAbelianMap
  pushforwardLocalCohomologyForgetIso)
open Stacks.Perfect.SupportedEndoForgetDegreewise (derivedForgetIdentity
  pushHomologySingle_pushIsoApp_eq_endoForgetIsoApp)

attribute [local instance] Stacks.DeRham.CounitCompatibleGeometric.toSheaf_preservesFiniteColimits
attribute [local instance] Stacks.DeRham.CounitCompatibleGeometric.forgetClosed_additive
  Stacks.DeRham.CounitCompatibleGeometric.forgetClosed_preservesFiniteLimits
  Stacks.DeRham.CounitCompatibleGeometric.forgetClosed_preservesFiniteColimits

variable {T : Set X} (hT : IsClosed T) (c : ℕ)

/-- **The degreewise comparison of [Stacks, Tag 0G74] part (2) for the Gysin map's target**: the
underlying abelian sheaf of `i_*ℋ ᶜ_Z(ℱ)`, with the local cohomology sheaf taken in the unbounded
derived category, compared with `i_*^{ab}ℋ ᶜ_Z(ℱ_ab)` in the unbounded abelian model.  It is
`Stacks.Cohomology.ModulePushforwardComparison.modulePushforwardCompToSheafIso` followed by the
direct image of the comparison on the closed subset, which is what `edgeSourceCompare` of
`Stacks.CounitGysinEdge` is built from; `forgetEdgeSourceCompare_eq` records that. -/
def forgetLocalCohomologyComparison (H : X.Modules) :
    (forgetModules X.toRingedSpace).obj
        ((modulePushforward (closedSubsetInclusion X.toRingedSpace T)).obj
          ((localCohomologySheafOfComplexFunctor X.toRingedSpace T
            hT (c : ℤ)).obj H)) ⟶
      (abelianClosedPushforward X.toRingedSpace T).obj
        ((DerivedCategory.homologyFunctor
            (Sheaf (Opens.grothendieckTopology (TopCat.of T))
              AddCommGrpCat.{u}) (c : ℤ)).obj
          ((derivedAbelianSupportedSectionsOnClosed X.toRingedSpace T
              hT).obj
            ((derivedForget X.toRingedSpace).obj
              ((DerivedCategory.singleFunctor (RModules X.toRingedSpace) 0).obj H)))) :=
  (modulePushforwardCompToSheafIso
        (closedSubsetInclusion X.toRingedSpace T)).hom.app
      ((localCohomologySheafOfComplexFunctor X.toRingedSpace T
        hT (c : ℤ)).obj H) ≫
    (abelianClosedPushforward X.toRingedSpace T).map
      ((modelForgetHomology X.toRingedSpace T hT c H).hom ≫
        (DerivedCategory.homologyFunctor
            (Sheaf (Opens.grothendieckTopology (TopCat.of T))
              AddCommGrpCat.{u}) (c : ℤ)).map
          ((forgetLocalCohomologyIso X.toRingedSpace T
              hT).hom.app
            ((DerivedCategory.singleFunctor (RModules X.toRingedSpace) 0).obj H)))

private lemma key_formal {V : Type*} [Category* V] {a b m k d e : V}
    (p : a ⟶ b) (pinv : b ⟶ a) (nu : b ⟶ k) (pz : k ⟶ m) (q : m ⟶ e)
    (pzq : k ⟶ e) (tl : e ⟶ d) (Th : a ⟶ e) (pia : b ⟶ d) (endo : a ⟶ d)
    (hp : pinv ≫ p = 𝟙 b) (hmc : pzq = pz ≫ q)
    (hDFI : p ≫ nu ≫ pzq = Th) (hEF : endo = Th ≫ tl) (hFIA : p ≫ pia = endo) :
    (nu ≫ pz) ≫ q ≫ tl = pia := by
  have := IsSplitEpi.mk' ⟨pinv, hp⟩
  refine (cancel_epi p).1 ?_
  rw [hFIA, hEF, ← hDFI, hmc]
  simp only [Category.assoc]

/-- **The degreewise comparison lands on the classical model**: `forgetLocalCohomologyComparison`
followed by the single-degree bridge and the abelian model bridge is the classical-model reading
`Stacks.Perfect.AbelianSupportedEndoModelBridge.pushIsoApp` of [Stacks, Tag 0G74] part (2).

This is `Stacks.Perfect.SupportedEndoForgetDegreewise.derivedForgetIdentity` — the degree-`c`
agreement of the two readings of that comparison — together with
`Stacks.Perfect.SupportedEndoForgetDegreewise.pushHomologySingle_pushIsoApp_eq_endoForgetIsoApp`,
which carries it across the comparison of the two places at which the degree-`c` cohomology sheaf
is taken. -/
theorem forgetLocalCohomologyComparison_comp (H : X.Modules) :
    forgetLocalCohomologyComparison hT c H ≫
        (abelianClosedPushforward X.toRingedSpace T).map
            ((DerivedCategory.homologyFunctor
                (Sheaf (Opens.grothendieckTopology (TopCat.of T))
                  AddCommGrpCat.{u}) (c : ℤ)).map
              ((derivedAbelianSupportedSectionsOnClosed X.toRingedSpace T
                  hT).map
                (singleForgetMathlib X.toRingedSpace H).hom)) ≫
          abelianModelTail hT c H =
      (pushIsoApp hT c H).hom :=
  key_formal _ ((abelianSheaf X).mapIso
      (pushHomologySingle hT c H)).inv
    _ _ _ _ _ _ _ _
    ((abelianSheaf X).mapIso
      (pushHomologySingle hT c H)).inv_hom_id
    ((abelianClosedPushforward X.toRingedSpace T).map_comp _ _)
    (derivedForgetIdentity hT c H)
    (endoForgetIsoApp_hom hT c H)
    (pushHomologySingle_pushIsoApp_eq_endoForgetIsoApp hT c H)

/-- **The abelian model bridge on the closed subset**: the degree-`c` cohomology of
`R𝓗^{ab}_Z(-[0])` is the classical `ℕ`-indexed right derived functor `ℋ ᶜ_Z`, naturally.  This is
the isomorphism `Stacks.Perfect.AbelianSupportedEndoModelFactors.abelianModelTail` is the direct
image of; it is named here so that the chase elaborates within the default limits. -/
abbrev modelBeta :=
  Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
    (abelianSupportedSectionsOnClosed X.toRingedSpace T
      hT)
    (derivedAbelianSupportedSectionsOnClosed X.toRingedSpace T
      hT)
    (derivedAbelianSupportedSectionsOnClosedUnit X.toRingedSpace T
      hT)
    Stacks.Cohomology.Localization.enoughKInjectives c

private lemma star_formal {V : Type*} [Category* V] {a b b' c' d e k m : V}
    (lamF : a ⟶ b) (qF : b ⟶ b') (tF : b' ⟶ m) (piaF : a ⟶ m)
    (lamG : c' ⟶ d) (qG : d ⟶ e) (tG : e ⟶ k) (piaG : c' ⟶ k) (piaGi : k ⟶ c')
    (chi : a ⟶ c') (aps : m ⟶ k) (pg : b ⟶ d) (pps : b' ⟶ e)
    (qGi : e ⟶ d) (tGi : k ⟶ e)
    (hKF : lamF ≫ qF ≫ tF = piaF) (hKG : lamG ≫ qG ≫ tG = piaG)
    (hchi : chi = piaF ≫ aps ≫ piaGi) (hpg : pg ≫ qG = qF ≫ pps)
    (hbeta : tF ≫ aps = pps ≫ tG) (hinv : piaGi ≫ piaG = 𝟙 k)
    (hqg : qG ≫ qGi = 𝟙 d) (htg : tG ≫ tGi = 𝟙 e) :
    chi ≫ lamG = lamF ≫ pg := by
  have hr : (qG ≫ tG) ≫ tGi ≫ qGi = 𝟙 d := by
    rw [Category.assoc, ← Category.assoc tG tGi qGi, htg, Category.id_comp, hqg]
  have hL : (chi ≫ lamG) ≫ qG ≫ tG = piaF ≫ aps := by
    rw [Category.assoc, hKG, hchi, Category.assoc, Category.assoc, hinv, Category.comp_id]
  have hR : (lamF ≫ pg) ≫ qG ≫ tG = piaF ≫ aps := by
    rw [Category.assoc, ← Category.assoc pg qG tG, hpg, Category.assoc, ← hbeta,
      ← Category.assoc qF tF aps, ← Category.assoc lamF (qF ≫ tF) aps, hKF]
  have := IsSplitMono.mk' ⟨tGi ≫ qGi, hr⟩
  exact (cancel_mono (qG ≫ tG)).1 (hL.trans hR.symm)

private lemma map_nat {A₀ B₀ : Type*} [Category* A₀] [Category* B₀] (W' : A₀ ⥤ B₀)
    {x y z w : A₀} (a : x ⟶ y) (b : y ⟶ w) (c : x ⟶ z) (d : z ⟶ w) (h : a ≫ b = c ≫ d) :
    W'.map c ≫ W'.map d = W'.map a ≫ W'.map b := by
  rw [← W'.map_comp, ← W'.map_comp, h]

private lemma map3_nat {A₀ B₀ C₀ D₀ : Type*} [Category* A₀] [Category* B₀] [Category* C₀]
    [Category* D₀] (R : A₀ ⥤ B₀) (Hf : B₀ ⥤ C₀) (P : C₀ ⥤ D₀)
    {x y z w : A₀} (a : x ⟶ y) (b : y ⟶ w) (c : x ⟶ z) (d : z ⟶ w) (h : a ≫ b = c ≫ d) :
    P.map (Hf.map (R.map a)) ≫ P.map (Hf.map (R.map b)) =
      P.map (Hf.map (R.map c)) ≫ P.map (Hf.map (R.map d)) := by
  rw [← P.map_comp, ← Hf.map_comp, ← R.map_comp, h, R.map_comp, Hf.map_comp, P.map_comp]

private lemma comp_cancel_inv {V : Type*} [Category* V] {x y z w : V}
    (a : x ⟶ y) (b : y ⟶ z) (ci : z ⟶ w) (c : w ⟶ z) (h : ci ≫ c = 𝟙 z) :
    (a ≫ b ≫ ci) ≫ c = a ≫ b := by
  rw [Category.assoc, Category.assoc, h, Category.comp_id]

/-- Following the action of a morphism of underlying abelian sheaves placed in degree `0` by the
comparison `Φᴰ(𝒢[0]) ≅ (𝒢_ab)[0]` absorbs that comparison: the comparison at `ℱ` followed by the
morphism placed in degree `0`.  This is the definition of `forgetSingleMap` with the inverse
comparison cancelled. -/
theorem forgetSingleMap_comp_singleForget {F G : X.Modules}
    (ψ : (forgetModules X.toRingedSpace).obj F ⟶ (forgetModules X.toRingedSpace).obj G) :
    forgetSingleMap X.toRingedSpace 0 ψ ≫ (singleForgetMathlib X.toRingedSpace G).hom =
      (singleForgetMathlib X.toRingedSpace F).hom ≫
        (DerivedCategory.singleFunctor (AbSheaves X.toRingedSpace) 0).map ψ :=
  comp_cancel_inv _ _ _ _
    (Iso.inv_hom_id_app
      ((forgetModules X.toRingedSpace).mapDerivedCategorySingleFunctor 0) G)

/-- The classical-model comparison at a module is the component of the natural isomorphism it is
read from.  Stated so that the chase below never has to unfold the isomorphism itself. -/
theorem pushIsoApp_hom_eq (H : X.Modules) :
    (pushIsoApp hT c H).hom =
      (Stacks.Perfect.GysinAbelianSquare.pushforwardLocalCohomologyForgetIso
        hT c).hom.app H :=
  rfl

/-- The inverse of the classical-model comparison at a module, as a component. -/
theorem pushIsoApp_inv_eq (H : X.Modules) :
    (pushIsoApp hT c H).inv =
      (Stacks.Perfect.GysinAbelianSquare.pushforwardLocalCohomologyForgetIso
        hT c).inv.app H :=
  rfl

/-- **The abelian action on the Gysin map's target is a conjugation**, spelled with the components
of the natural isomorphism.  This holds by definition. -/
theorem pushforwardLocalCohomologyAbelianMap_eq' {F G : X.Modules}
    (ψ : (forgetModules X.toRingedSpace).obj F ⟶ (forgetModules X.toRingedSpace).obj G) :
    pushforwardLocalCohomologyAbelianMap hT c ψ =
      (Stacks.Perfect.GysinAbelianSquare.pushforwardLocalCohomologyForgetIso
          hT c).hom.app F ≫
        (abelianLocalCohomologyPushforward X.toRingedSpace T
            hT c).map ψ ≫
          (Stacks.Perfect.GysinAbelianSquare.pushforwardLocalCohomologyForgetIso
            hT c).inv.app G :=
  rfl

/-- **The abelian action on the Gysin map's target is a conjugation by the classical-model
comparison**, in the spelling `forgetLocalCohomologyComparison_comp` delivers. -/
theorem pushforwardLocalCohomologyAbelianMap_eq {F G : X.Modules}
    (ψ : (forgetModules X.toRingedSpace).obj F ⟶ (forgetModules X.toRingedSpace).obj G) :
    pushforwardLocalCohomologyAbelianMap hT c ψ =
      (pushIsoApp hT c F).hom ≫
        (abelianLocalCohomologyPushforward X.toRingedSpace T
            hT c).map ψ ≫
          (pushIsoApp hT c G).inv := by
  rw [pushIsoApp_hom_eq, pushIsoApp_inv_eq]
  exact pushforwardLocalCohomologyAbelianMap_eq' hT c ψ

/-- **The degreewise comparison is natural in an arbitrary morphism of the underlying abelian
sheaves.**  The action
`Stacks.Perfect.GysinAbelianSquare.pushforwardLocalCohomologyAbelianMap` on the classical-model
side and the unbounded abelian model's own functoriality are carried to one another by
`forgetLocalCohomologyComparison`.

Both actions are conjugations: the first by the classical-model comparison, by
`pushforwardLocalCohomologyAbelianMap_eq`, and the second by
`forgetLocalCohomologyComparison_comp`, so the two agree once the model bridge
`Stacks.Perfect.AbelianSupportedEndoModelFactors.abelianModelTail` is
seen to be natural — which is the naturality of `modelBeta` — and the single-degree bridge is
moved across by `forgetSingleMap_comp_singleForget`. -/
theorem forgetLocalCohomologyComparison_natural {F G : X.Modules}
    (ψ : (forgetModules X.toRingedSpace).obj F ⟶ (forgetModules X.toRingedSpace).obj G) :
    pushforwardLocalCohomologyAbelianMap hT c ψ ≫ forgetLocalCohomologyComparison hT c G =
      forgetLocalCohomologyComparison hT c F ≫
        (abelianClosedPushforward X.toRingedSpace T).map
          ((DerivedCategory.homologyFunctor
              (Sheaf (Opens.grothendieckTopology (TopCat.of T))
                AddCommGrpCat.{u}) (c : ℤ)).map
            ((derivedAbelianSupportedSectionsOnClosed X.toRingedSpace T
                hT).map
              (forgetSingleMap X.toRingedSpace 0 ψ))) :=
  star_formal _ _ _ _ _ _ _ _ _ _ _ _ _
    ((derivedAbelianSupportedSectionsOnClosed X.toRingedSpace T
        hT ⋙
      DerivedCategory.homologyFunctor
          (Sheaf (Opens.grothendieckTopology (TopCat.of T))
            AddCommGrpCat.{u}) (c : ℤ) ⋙
        abelianClosedPushforward X.toRingedSpace T).map
      (singleForgetMathlib X.toRingedSpace G).inv)
    ((abelianClosedPushforward X.toRingedSpace T).map
      ((modelBeta hT c).inv.app
        ((abelianSheaf X).obj G)))
    (forgetLocalCohomologyComparison_comp hT c F) (forgetLocalCohomologyComparison_comp hT c G)
    (pushforwardLocalCohomologyAbelianMap_eq hT c ψ)
    (map3_nat
      (derivedAbelianSupportedSectionsOnClosed X.toRingedSpace T
        hT)
      (DerivedCategory.homologyFunctor
        (Sheaf (Opens.grothendieckTopology (TopCat.of T))
          AddCommGrpCat.{u}) (c : ℤ))
      (abelianClosedPushforward X.toRingedSpace T)
      _ _ _ _ (forgetSingleMap_comp_singleForget ψ))
    (map_nat (abelianClosedPushforward X.toRingedSpace T) _ _ _ _
      ((modelBeta hT c).hom.naturality ψ))
    ((pushIsoApp hT c G).inv_hom_id)
    (((derivedAbelianSupportedSectionsOnClosed X.toRingedSpace T
        hT ⋙
      DerivedCategory.homologyFunctor
          (Sheaf (Opens.grothendieckTopology (TopCat.of T))
            AddCommGrpCat.{u}) (c : ℤ) ⋙
        abelianClosedPushforward X.toRingedSpace T).mapIso
      (singleForgetMathlib X.toRingedSpace G)).hom_inv_id)
    (((abelianClosedPushforward X.toRingedSpace T).mapIso
      ((modelBeta hT c).app
        ((abelianSheaf X).obj G))).hom_inv_id)


private lemma assoc_map_comp {V : Type*} [Category* V] {a b d e : V}
    (m : a ⟶ b) (x : b ⟶ d) (y : d ⟶ e) (z : b ⟶ e) (h : x ≫ y = z) :
    (m ≫ x) ≫ y = m ≫ z := by
  rw [Category.assoc, h]

/-- **The source comparison of the Gysin edge morphisms is the degreewise comparison placed in
degree `c`**, after the comparison `Φᴰ(ℳ[-c]) ≅ (Φℳ)[-c]`.  This is
`Stacks.CounitGysinEdge.edgeSourceCompare_eq` with the last two of its three factors collapsed. -/
theorem forgetEdgeSourceCompare_eq (H : X.Modules) :
    forgetEdgeSourceCompare X.toRingedSpace T hT
        (c : ℤ) ((DerivedCategory.singleFunctor (RModules X.toRingedSpace) 0).obj H) =
      ((forgetModules X.toRingedSpace).mapDerivedCategorySingleFunctor
            (c : ℤ)).hom.app
          ((modulePushforward (closedSubsetInclusion X.toRingedSpace T)).obj
            ((localCohomologySheafOfComplexFunctor X.toRingedSpace T
              hT (c : ℤ)).obj H)) ≫
        (DerivedCategory.singleFunctor (AbSheaves X.toRingedSpace) (c : ℤ)).map
          (forgetLocalCohomologyComparison hT c H) :=
  assoc_map_comp _ _ _ _
    ((DerivedCategory.singleFunctor (AbSheaves X.toRingedSpace) (c : ℤ)).map_comp
      _ _).symm

private lemma final_formal {V : Type*} [Category* V] {a p q b e d : V}
    (mF : a ⟶ p) (sx : p ⟶ q) (mGi : q ⟶ b) (mG : b ⟶ q) (slG : q ⟶ d)
    (slF : p ⟶ e) (sg : e ⟶ d) (eG : b ⟶ d) (eF : a ⟶ e)
    (hmg : mGi ≫ mG = 𝟙 q) (heG : eG = mG ≫ slG) (heF : eF = mF ≫ slF)
    (hsq : sx ≫ slG = slF ≫ sg) :
    (mF ≫ sx ≫ mGi) ≫ eG = eF ≫ sg := by
  rw [heG, heF, Category.assoc, Category.assoc, ← Category.assoc mGi mG slG, hmg,
    Category.id_comp, hsq, Category.assoc]

/-- **The square on the sources of the two Gysin edge morphisms**, which is what
`Stacks.CounitGysinEdge.mapDerivedCategory_edge_square` asks for: the action of `i_*ℋ ᶜ_Z` on a
morphism of the underlying abelian sheaves, placed in degree `c`, commutes with the source
comparison and with the abelian model's own functoriality.  This is
`forgetLocalCohomologyComparison_natural` placed in degree `c`. -/
theorem edgeSourceCompare_square {F G : X.Modules}
    (ψ : (forgetModules X.toRingedSpace).obj F ⟶ (forgetModules X.toRingedSpace).obj G) :
    forgetSingleMap X.toRingedSpace (c : ℤ) (pushforwardLocalCohomologyAbelianMap hT c ψ) ≫
        forgetEdgeSourceCompare X.toRingedSpace T hT
          (c : ℤ)
          ((DerivedCategory.singleFunctor (RModules X.toRingedSpace) 0).obj G) =
      forgetEdgeSourceCompare X.toRingedSpace T hT
          (c : ℤ)
          ((DerivedCategory.singleFunctor (RModules X.toRingedSpace) 0).obj F) ≫
        (DerivedCategory.singleFunctor (AbSheaves X.toRingedSpace) (c : ℤ)).map
          ((abelianClosedPushforward X.toRingedSpace T).map
            ((DerivedCategory.homologyFunctor
                (Sheaf (Opens.grothendieckTopology (TopCat.of T))
                  AddCommGrpCat.{u}) (c : ℤ)).map
              ((derivedAbelianSupportedSectionsOnClosed X.toRingedSpace T
                  hT).map
                (forgetSingleMap X.toRingedSpace 0 ψ)))) :=
  final_formal _ _ _ _ _ _ _ _ _
    (Iso.inv_hom_id_app
      ((forgetModules X.toRingedSpace).mapDerivedCategorySingleFunctor (c : ℤ)) _)
    (forgetEdgeSourceCompare_eq hT c G) (forgetEdgeSourceCompare_eq hT c F)
    ((((DerivedCategory.singleFunctor (AbSheaves X.toRingedSpace)
              (c : ℤ)).map_comp _ _).symm.trans
        (congrArg
          (DerivedCategory.singleFunctor (AbSheaves X.toRingedSpace) (c : ℤ)).map
          (forgetLocalCohomologyComparison_natural hT c ψ))).trans
      ((DerivedCategory.singleFunctor (AbSheaves X.toRingedSpace)
        (c : ℤ)).map_comp _ _))

/-- **`EdgeCommutesWithAbelian` holds.**  Forgetting the module structure carries the Gysin edge
morphism of [Stacks, Tag 0G8A] to the one for the underlying abelian sheaves, so the edge morphism
is natural along an arbitrary — in particular not `𝒪_X`-linear — morphism `ψ` of the underlying
abelian sheaves, the local cohomology sheaf acting on `ψ` by
`Stacks.Perfect.GysinAbelianSquare.pushforwardLocalCohomologyAbelianMap`.

`derivedForget_supportedGysinEdge_square` reduces this to the square on the sources, and that is
`edgeSourceCompare_square`.  The only hypotheses are the vanishing of [Stacks, Tag 0G8A]. -/
theorem edgeCommutesWithAbelian : EdgeCommutesWithAbelian hT c := fun _ _ hF hG ψ =>
  derivedForget_supportedGysinEdge_square X.toRingedSpace T
    hT
    (c : ℤ) hF hG (forgetSingleMap X.toRingedSpace 0 ψ)
    (forgetSingleMap X.toRingedSpace (c : ℤ) (pushforwardLocalCohomologyAbelianMap hT c ψ))
    (edgeSourceCompare_square hT c ψ)

end AbelianEdge

/-- `EdgeCommutesWithAbelian` at the two terms of the de Rham complex the square of
[Stacks, Tag 0G8B] relates and at the de Rham differential between them.  The right-hand vertical
arrow becomes `AlgebraicGeometry.Scheme.Hom.gysinTargetDeRhamMap`, which is by definition the
action of `i_*ℋ ᶜ_Z` on that differential.  It is a separate declaration so that the general
hypothesis is unfolded once, in a statement that mentions nothing else. -/
theorem edge_deRham (π : X ⟶ S) {c : ℕ} (f : Fin (c + 1) → Γ(X, ⊤)) (p : ℕ)
    (hvan : SupportVanishing X.toRingedSpace (equationsClosedSet f)
      (isClosed_equationsClosedSet f) (c + 1)
      (relativeDifferentialForms π ((p : ℤ) + ((c + 1 : ℕ) : ℤ))))
    (hvan' : SupportVanishing X.toRingedSpace (equationsClosedSet f)
      (isClosed_equationsClosedSet f) (c + 1)
      (relativeDifferentialForms π ((p + (c + 1) + 1 : ℕ) : ℤ)))
    (hedge : EdgeCommutesWithAbelian (isClosed_equationsClosedSet f) (c + 1)) :
    (derivedForget X.toRingedSpace).map
          (supportedGysinEdge (equationsClosedSet f) (isClosed_equationsClosedSet f)
            ((c + 1 : ℕ) : ℤ)
            ((DerivedCategory.singleFunctor (RModules X.toRingedSpace) (0 : ℤ)).obj
              (relativeDifferentialForms π ((p : ℤ) + ((c + 1 : ℕ) : ℤ)))) hvan) ≫
        forgetSingleMap X.toRingedSpace (0 : ℤ) (deRhamDifferentialAbHom π (p + (c + 1))) =
      forgetSingleMap X.toRingedSpace ((c + 1 : ℕ) : ℤ)
          (gysinTargetDeRhamMap π f (p + (c + 1))) ≫
        (derivedForget X.toRingedSpace).map
          (supportedGysinEdge (equationsClosedSet f) (isClosed_equationsClosedSet f)
            ((c + 1 : ℕ) : ℤ)
            ((DerivedCategory.singleFunctor (RModules X.toRingedSpace) (0 : ℤ)).obj
              (relativeDifferentialForms π ((p + (c + 1) + 1 : ℕ) : ℤ))) hvan') :=
  hedge _ _ hvan hvan' (deRhamDifferentialAbHom π (p + (c + 1)))

/-- The degree transport `AlgebraicGeometry.Scheme.Hom.gysinTargetReindex` of the square of
[Stacks, Tag 0G85] is the transport along the equality of the two terms of the de Rham complex
that `gysinCohomologyMap_congr` consumes.  Both are the action of `i_*ℋ ᶜ_Z` on the canonical
identification of two terms of equal degree; this is
`CategoryTheory.eqToHom_map` and proof irrelevance. -/
theorem gysinTargetReindex_eq_eqToHom (π : X ⟶ S) {c : ℕ} (f : Fin (c + 1) → Γ(X, ⊤)) (p : ℕ) :
    gysinTargetReindex π f (gysinTargetDegree_eq (c := c) p) =
      eqToHom (congrArg (supportedLocalCohomology X.toRingedSpace (equationsClosedSet f)
        (isClosed_equationsClosedSet f) (c + 1))
        (congrArg (relativeDifferentialForms π) (gysinTargetDegree_eq (c := c) p))) := by
  rw [gysinTargetReindex, eqToHom_map]
  rfl

/-- The cohomological Gysin map `γ^{p,q}` of [Stacks, Tag 0G8A] attached to the Gysin map
`γ^p_{f₁, …, f_c}` of [Stacks, Tag 0G83], with the source read on `X`, is
`equationGysinCohomologyMap` at the kernel description that `hcut` provides; the source's own
`H^q(Z, Ω^p_{Z/S})` form is `equationGysinHodgeMap`, which is that map preceded by the
affine-pushforward comparison of [Stacks, Tag 089W]. -/
theorem equationGysinHodgeMap_eq (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) {c : ℕ}
    (f : Fin (c + 1) → Γ(X, ⊤)) (p : ℕ) (hcut : Stacks.Gysin.IsCutOutByEquations i f)
    (hvan : SupportVanishing X.toRingedSpace (equationsClosedSet f)
      (isClosed_equationsClosedSet f) (c + 1)
      (relativeDifferentialForms π ((p : ℤ) + ((c + 1 : ℕ) : ℤ))))
    (q : ℕ) :
    equationGysinHodgeMap i π f p hcut hvan q =
      ((Stacks.AffineCohomologyResolution.cohomologyPushforwardIso i q).app
          ⟨relativeDifferentialForms (i ≫ π) (p : ℤ),
            isQuasicoherent_relativeDifferentialForms (i ≫ π) p⟩).hom ≫
        equationGysinCohomologyMap i π f p
          (formKernelGeneratedByEquations_of_isCutOutByEquations i π hcut p) hvan q := rfl

/-- **The square of [Stacks, Tag 0G8B] with the degree transport folded into the Gysin map**,
which is the shape the sheaf-level square of [Stacks, Tag 0G85] is stated in: the right-hand
horizontal arrow is the cohomological Gysin map attached to `γ^{p+1}` followed by
`AlgebraicGeometry.Scheme.Hom.gysinTargetReindex`.

This is `gysinCohomologyMap_comm` at the Gysin map of [Stacks, Tag 0G83], with the sheaf-level
square supplied by `AlgebraicGeometry.Scheme.Hom.gysinMapCommutesWithDeRham` and the edge
compatibility by `hedge`, which `edge_deRham` supplies from `edgeCommutesWithAbelian`.
`gysinCohomologyMap_reindex_eq` unfolds the transport, which is what
turns this into the tagged form `equationGysinCohomologyMap_comm_deRham`. -/
theorem gysinCohomologyMap_comm_deRham (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) {c : ℕ}
    (f : Fin (c + 1) → Γ(X, ⊤)) (p q : ℕ) (hcut : Stacks.Gysin.IsCutOutByEquations i f)
    (hvan : SupportVanishing X.toRingedSpace (equationsClosedSet f)
      (isClosed_equationsClosedSet f) (c + 1)
      (relativeDifferentialForms π ((p : ℤ) + ((c + 1 : ℕ) : ℤ))))
    (hvan' : SupportVanishing X.toRingedSpace (equationsClosedSet f)
      (isClosed_equationsClosedSet f) (c + 1)
      (relativeDifferentialForms π ((p + (c + 1) + 1 : ℕ) : ℤ)))
    (hedge : (derivedForget X.toRingedSpace).map
          (supportedGysinEdge (equationsClosedSet f) (isClosed_equationsClosedSet f)
            ((c + 1 : ℕ) : ℤ)
            ((DerivedCategory.singleFunctor (RModules X.toRingedSpace) (0 : ℤ)).obj
              (relativeDifferentialForms π ((p : ℤ) + ((c + 1 : ℕ) : ℤ)))) hvan) ≫
        forgetSingleMap X.toRingedSpace (0 : ℤ) (deRhamDifferentialAbHom π (p + (c + 1))) =
      forgetSingleMap X.toRingedSpace ((c + 1 : ℕ) : ℤ)
          (gysinTargetDeRhamMap π f (p + (c + 1))) ≫
        (derivedForget X.toRingedSpace).map
          (supportedGysinEdge (equationsClosedSet f) (isClosed_equationsClosedSet f)
            ((c + 1 : ℕ) : ℤ)
            ((DerivedCategory.singleFunctor (RModules X.toRingedSpace) (0 : ℤ)).obj
              (relativeDifferentialForms π ((p + (c + 1) + 1 : ℕ) : ℤ))) hvan')) :
    gysinCohomologyMap (equationsClosedSet f) (isClosed_equationsClosedSet f) (c + 1)
          ((Scheme.Modules.pushforward i).obj (relativeDifferentialForms (i ≫ π) (p : ℤ)))
          (relativeDifferentialForms π ((p : ℤ) + ((c + 1 : ℕ) : ℤ))) hvan
          (gysinMap i π f p hcut) q ≫
        abelianHgroupMap X.toRingedSpace (0 : ℤ) ((q : ℤ) + ((c + 1 : ℕ) : ℤ)) (q + (c + 1))
          (by omega) (deRhamDifferentialAbHom π (p + (c + 1))) =
      abelianHgroupMap X.toRingedSpace ((c + 1 : ℕ) : ℤ) ((q : ℤ) + ((c + 1 : ℕ) : ℤ)) q
          (by omega) (pushforwardDeRhamDifferentialAbHom i π p) ≫
        gysinCohomologyMap (equationsClosedSet f) (isClosed_equationsClosedSet f) (c + 1)
          ((Scheme.Modules.pushforward i).obj
            (relativeDifferentialForms (i ≫ π) ((p + 1 : ℕ) : ℤ)))
          (relativeDifferentialForms π ((p + (c + 1) + 1 : ℕ) : ℤ)) hvan'
          (gysinMap i π f (p + 1) hcut ≫
            gysinTargetReindex π f (gysinTargetDegree_eq (c := c) p)) q :=
  gysinCohomologyMap_comm X.toRingedSpace (equationsClosedSet f)
    (isClosed_equationsClosedSet f) (c + 1) q hvan hvan' (gysinMap i π f p hcut)
    (gysinMap i π f (p + 1) hcut ≫ gysinTargetReindex π f (gysinTargetDegree_eq (c := c) p))
    (pushforwardDeRhamDifferentialAbHom i π p) (deRhamDifferentialAbHom π (p + (c + 1)))
    (gysinTargetDeRhamMap π f (p + (c + 1)))
    (gysinMapCommutesWithDeRham i π f p hcut) hedge

/-- **Unfolding the degree transport.**  The cohomological Gysin map attached to `γ^{p+1}`
followed by `AlgebraicGeometry.Scheme.Hom.gysinTargetReindex` is `γ^{p+1,q}` itself, that is
`equationGysinCohomologyMap` in degree `p + 1`, followed by the identification of the two
cohomology groups of the two equal degrees `p + 1 + c` and `p + c + 1`.  This is
`gysinTargetReindex_eq_eqToHom` and `gysinCohomologyMap_congr`. -/
theorem gysinCohomologyMap_reindex_eq (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) {c : ℕ}
    (f : Fin (c + 1) → Γ(X, ⊤)) (p q : ℕ) (hcut : Stacks.Gysin.IsCutOutByEquations i f)
    (hvan₁ : SupportVanishing X.toRingedSpace (equationsClosedSet f)
      (isClosed_equationsClosedSet f) (c + 1)
      (relativeDifferentialForms π (((p + 1 : ℕ) : ℤ) + ((c + 1 : ℕ) : ℤ))))
    (hvan' : SupportVanishing X.toRingedSpace (equationsClosedSet f)
      (isClosed_equationsClosedSet f) (c + 1)
      (relativeDifferentialForms π ((p + (c + 1) + 1 : ℕ) : ℤ))) :
    gysinCohomologyMap (equationsClosedSet f) (isClosed_equationsClosedSet f) (c + 1)
          ((Scheme.Modules.pushforward i).obj
            (relativeDifferentialForms (i ≫ π) ((p + 1 : ℕ) : ℤ)))
          (relativeDifferentialForms π ((p + (c + 1) + 1 : ℕ) : ℤ)) hvan'
          (gysinMap i π f (p + 1) hcut ≫
            gysinTargetReindex π f (gysinTargetDegree_eq (c := c) p)) q =
      equationGysinCohomologyMap i π f (p + 1)
          (formKernelGeneratedByEquations_of_isCutOutByEquations i π hcut (p + 1)) hvan₁ q ≫
        eqToHom (congrArg (Hgroup X.ringCatSheaf ⊤ (q + (c + 1)))
          (congrArg (relativeDifferentialForms π) (gysinTargetDegree_eq (c := c) p))) :=
  (gysinCohomologyMap_congr X.toRingedSpace (equationsClosedSet f)
    (isClosed_equationsClosedSet f) (c + 1) q
    (congrArg (relativeDifferentialForms π) (gysinTargetDegree_eq (c := c) p)) hvan₁ hvan'
    (gysinMap i π f (p + 1) hcut) _ (gysinTargetReindex_eq_eqToHom π f p)).symm

/-- **The square of [Stacks, Tag 0G8B] for the Gysin maps of a global family of equations.**  Let
`π : X ⟶ S` be a morphism of schemes, let `f₁, …, f_c ∈ Γ(X, 𝒪_X)` with `c = c' + 1` and let
`i : Z ⟶ X` be the closed subscheme they cut out.  The cohomological Gysin maps `γ^{p,q}` of
[Stacks, Tag 0G8A] are compatible with the de Rham differentials on `Ω^•_{X/S}` and
`Ω^•_{Z/S}`: the square

```
H^q(X, i_*Ω^p_{Z/S}) ----γ^{p,q}----→ H^{q+c}(X, Ω^{p+c}_{X/S})
        ↓ d                                   ↓ d
H^q(X, i_*Ω^{p+1}_{Z/S}) --γ^{p+1,q}→ H^{q+c}(X, Ω^{p+c+1}_{X/S})
```

commutes, the verticals being the arrows the de Rham differentials induce on cohomology through
`abelianHgroupMap` and the final `eqToHom` the degree identification `p + 1 + c = p + c + 1`.

The sheaf-level square is `AlgebraicGeometry.Scheme.Hom.gysinMapCommutesWithDeRham`, that is
[Stacks, Tag 0G85] itself; the compatibility of the Gysin edge morphism with forgetting the module
structure is `edgeCommutesWithAbelian`.  Smoothness of `π` and Koszul regularity of `i` are the
source's hypotheses and are not consumed here: the vanishing `hvan` they provide by
[Stacks, Tag 0G7P] is assumed instead.  Deriving it is
`Stacks.DeRham.GysinCohomologyDeRhamKoszul.supportVanishing_relativeDifferentialForms`, and the
tag sits on `Stacks.DeRham.GysinCohomologyDeRhamKoszul.koszulGysinCohomologyMap_comm_deRham`,
which states the square at the glued Gysin map of [Stacks, Tag 0G86] with the vanishing
discharged; this statement, the global-equations case, is one of its inputs. -/
theorem equationGysinCohomologyMap_comm_deRham (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S)
    [Smooth π] (_hkoszul : Stacks.AlgebraicGeometry.RegularIdealSheaf.IsKoszulRegularImmersion i)
    {c : ℕ} (f : Fin (c + 1) → Γ(X, ⊤)) (p q : ℕ)
    (hcut : Stacks.Gysin.IsCutOutByEquations i f)
    (hvan : SupportVanishing X.toRingedSpace (equationsClosedSet f)
      (isClosed_equationsClosedSet f) (c + 1)
      (relativeDifferentialForms π ((p : ℤ) + ((c + 1 : ℕ) : ℤ))))
    (hvan₁ : SupportVanishing X.toRingedSpace (equationsClosedSet f)
      (isClosed_equationsClosedSet f) (c + 1)
      (relativeDifferentialForms π (((p + 1 : ℕ) : ℤ) + ((c + 1 : ℕ) : ℤ)))) :
    equationGysinCohomologyMap i π f p
          (formKernelGeneratedByEquations_of_isCutOutByEquations i π hcut p) hvan q ≫
        abelianHgroupMap X.toRingedSpace (0 : ℤ) ((q : ℤ) + ((c + 1 : ℕ) : ℤ)) (q + (c + 1))
          (by omega) (deRhamDifferentialAbHom π (p + (c + 1))) =
      abelianHgroupMap X.toRingedSpace ((c + 1 : ℕ) : ℤ) ((q : ℤ) + ((c + 1 : ℕ) : ℤ)) q
          (by omega) (pushforwardDeRhamDifferentialAbHom i π p) ≫
        equationGysinCohomologyMap i π f (p + 1)
            (formKernelGeneratedByEquations_of_isCutOutByEquations i π hcut (p + 1)) hvan₁ q ≫
          eqToHom (congrArg (Hgroup X.ringCatSheaf ⊤ (q + (c + 1)))
            (congrArg (relativeDifferentialForms π) (gysinTargetDegree_eq (c := c) p))) := by
  have hvan' : SupportVanishing X.toRingedSpace (equationsClosedSet f)
      (isClosed_equationsClosedSet f) (c + 1)
      (relativeDifferentialForms π ((p + (c + 1) + 1 : ℕ) : ℤ)) := by
    rw [← gysinTargetDegree_eq (c := c) p]
    exact hvan₁
  refine (gysinCohomologyMap_comm_deRham i π f p q hcut hvan hvan'
    (edge_deRham π f p hvan hvan'
      (edgeCommutesWithAbelian (isClosed_equationsClosedSet f) (c + 1)))).trans ?_
  rw [gysinCohomologyMap_reindex_eq i π f p q hcut hvan₁ hvan']
  rfl

end DeRham

end Stacks.DeRham.GysinCohomologyDeRham

end
