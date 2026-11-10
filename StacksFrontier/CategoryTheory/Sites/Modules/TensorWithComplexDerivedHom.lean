module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DGFunctorHomComplexCohomology
public import StacksFrontier.Algebra.DifferentialGraded.Module.HomComplexExtGeneral
public import StacksFrontier.Algebra.DifferentialGraded.Module.PropertyPDerivedModel
public import StacksFrontier.CategoryTheory.DifferentialGraded.HomComplex
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomShift
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexDerived
import StacksCore.Tactic.StacksAttribute

/-!
# Derived hom and tensoring with a complex of modules on a ringed site

Let `(C, O)` be a ringed site, let `K` be a complex of `O`-modules and let
`(E, d) = Hom_{Comp^dg(O)}(K, K)` be its endomorphism differential graded algebra. Tensoring with
`K` is a functor `- ⊗_E K : Mod^dg_(E, d) ⥤ Comp^dg(O)` of differential graded categories
(Tag 09LV), so it acts on the differential graded Hom complexes: for differential graded
`E`-modules `M` and `N` it gives a map of complexes of abelian groups

`Hom^•_{Mod^dg_(E, d)}(M, N) ⟶ Hom^•_{Comp^dg(O)}(M ⊗_E K, N ⊗_E K)`.

The target is the complex of global sections of the internal Hom complex (Tag 0A8Z) and
therefore maps canonically to the global derived hom `RHom_O(M ⊗_E K, N ⊗_E K)` of Tag 0B6E.
Composing gives the canonical map of Tag 0CS6. The maps built here are read in `D(ℤ)`; the
source's `D(R)`-valued ones, which carry the registrations of the tag, are in
`StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexDerivedHomModulesOver` and forget to
these. See the implementation notes on the base ring.

## Main definitions

* `AlgebraicGeometry.RingedSite.tensorWithComplexHomComplexMap`: the map of differential graded
  Hom complexes induced by tensoring with `K`.
* `AlgebraicGeometry.RingedSite.tensorWithComplexDerivedHomMap`: the canonical map
  `Hom^•_{Mod^dg_(E, d)}(M, N) ⟶ RHom_O(M ⊗_E K, N ⊗_E K)` of Tag 0CS6, in `D(ℤ)`.
* `AlgebraicGeometry.RingedSite.tensorWithComplexDerivedPropertyPIso`: on a differential graded
  module with property (P) the derived tensor product `M ⊗_E^𝐋 K` is the ordinary one `M ⊗_E K`.
* `AlgebraicGeometry.RingedSite.tensorWithComplexDerivedRepIso`: the derived tensor product of an
  *arbitrary* object of `D(E, d)` is the ordinary tensor product of its chosen property-(P)
  representative.
* `AlgebraicGeometry.RingedSite.tensorWithComplexDerivedHomMapDerived`: the same canonical map
  with its target moved to the global derived hom of the *derived* tensor products,
  `RHom(M, N) ⟶ RHom_O(M ⊗_E^𝐋 K, N ⊗_E^𝐋 K)`, for every `M`, `N` in `D(E, d)`.
* `AlgebraicGeometry.RingedSite.tensorWithComplexDerivedHomSourceExtEquiv`: the source of the
  canonical map is `RHom(M, N)`, read on cohomology: its degree-`n` cohomology is
  `Ext^n_{D(E, d)}(M, N)`, for every `M`, `N` in `D(E, d)`.
* `AlgebraicGeometry.RingedSite.tensorWithComplexDerivedHomTargetExtEquiv`: the target of the
  canonical map read on cohomology: its degree-`n` cohomology is
  `Ext^n_{D(O)}(M ⊗_E^𝐋 K, N ⊗_E^𝐋 K)`, for every `M`, `N` in `D(E, d)`.

## Main results

* `AlgebraicGeometry.RingedSite.tensorWithComplexHomComplexMap_homology`: Tag 09LC is natural
  under the differential graded functor of Tag 09LV — the degree-`n` cohomology of the first leg
  of the canonical map is the action of `- ⊗_E K` on homotopy-category morphism groups. This is
  one of the three inputs of the central clause of Tag 0CS6; see the implementation notes.

## Implementation notes

*No hypothesis beyond the source's.* The source's statement is quantified over **every** `M`,
`N` in `D(E, d)`; the modules "with property (P)" of its proof are a device of that proof, which
the source introduces with "we may assume". Accordingly nothing tagged below assumes property
(P). The reduction is carried out instead by the chosen representative
`DifferentialGradedModule.propertyPModel` of
`StacksFrontier.Algebra.DifferentialGraded.Module.PropertyPDerivedModel`, which exists for every
object of `D(E, d)` by Tag 09KP and has property (P) by construction; the statements below are
read at those representatives and transported to `M` and `N` along
`DifferentialGradedModule.propertyPModelIso`. Note that the property-(P) hypothesis cannot
simply be deleted from a statement about the Hom complex of `M` and `N` themselves: the
degree-`n` cohomology of `Hom^•_{Mod^dg_(E, d)}(M, N)` is `Hom_{K(E, d)}(M, N[n])`, which is the
`Ext`-group only for an `M` orthogonal on the left to the acyclic modules. It is the change of
source object, not the removal of a binder, that discharges the hypothesis.

Nor is anything assumed about the site: the five typeclass hypotheses under which the degree-`n`
reading of the global derived hom is stated in
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomShift` —
`HasSheafify`, `WEqualsLocallyBijective`, the additivity of the sheaf tensor product in each
variable, and the existence of its bifunctor maps on complexes — are all inferable for an
arbitrary `AlgebraicGeometry.RingedSite.{u, u, u}`, so they are not carried here.

*The base ring is the source's, on both sides.* The source fixes a ring `R` and a sheaf `O` of
commutative `R`-algebras, and asserts that the canonical map lives in `D(R)`; that carries two
things, that the objects the clauses quantify over are formed over `R`, and that the map between
them is `R`-linear. The first is carried here: `R` is a variable of this file, with an
`R`-linear structure on the sheaves of `O`-modules and an
`AlgebraicGeometry.RingedSite.ScalarSections` instance, so `E` is a differential graded
`R`-algebra, `D(E, d)` is its derived category of differential graded modules, `- ⊗_E^𝐋 K` is
defined on it and the `Ext`-groups are `R`-modules. The second is carried too, but not by the
maps in *this* file: those are read in `D(ℤ) = D(Ab)`, that is, with the scalars of their source
and target forgotten. The `D(R)`-valued maps are
`AlgebraicGeometry.RingedSite.tensorWithComplexDerivedHomMapModulesOver` and
`AlgebraicGeometry.RingedSite.tensorWithComplexDerivedHomMapDerivedModulesOver` of
`StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexDerivedHomModulesOver`, each proved
to forget to the corresponding map below; the registrations of Tag 0CS6 sit there and on the
cohomology clause of
`StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexDerivedExtClauseOver`. The maps below
are therefore those maps with their scalars forgotten, and nothing here is registered.

Tags 09LV–09LX are formed over an arbitrary base ring in
`StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplex`,
`StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexHomotopy` and
`StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexDerived`: there
`AlgebraicGeometry.RingedSite.Rep` takes a commutative ring `R` with an `R`-linear structure on
the sheaves of `O`-modules and an `AlgebraicGeometry.RingedSite.ScalarSections` instance, and
produces a differential graded `R`-algebra and an `R`-linear differential graded tensor functor.
At `R = ℤ` every one of those constructions is definitionally the one the files downstream use,
with `AlgebraicGeometry.RingedSite.scalarSectionsInt` supplying the instance.

Nor does it lie in the hypothesis. That pair of data is the source's own: by
`AlgebraicGeometry.RingedSite.ScalarSections.toGlobalSections` of
`StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexBaseRing` the sections by which a
scalar multiplies form a global section of `O` and the assignment is a ring map
`R ⟶ Γ(C, O)`, so the instance *is* a sheaf of commutative `R`-algebras
(`AlgebraicGeometry.RingedSite.ScalarSections.algebraSheaf`) and the linear structure is that
map's restriction of scalars. In particular `Γ(C, O)` is the universal base ring: every `R` of
the source factors through it, and a statement in `D(Γ(C, O))` gives the statement in `D(R)` by
restricting scalars along that map.

What is read in `D(ℤ)` in this file is the canonical map itself. Its source is
`DGCategory.homComplex`, valued in `AddCommGrpCat`, rather than the `R`-module-valued
`DGCategory.homComplexModules`, and its target is the global derived hom with its scalars
forgotten, for which the whole family of files around
`AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHom` is stated in `D(ℤ)`; only
`AlgebraicGeometry.RingedSite.globalDerivedHomModules` itself is module-valued, and over
`Γ(C, O)` rather than over `R`. Reading the clause in `D(R)` meant carrying that family to the
module level over `Γ(C, O)` and then restricting scalars, and that is what
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomModuleRestrict` and
`StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexDerivedHomModulesOver` do.

What that move consists of, leg by leg —
`AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHom` is a composite of three.
Its third leg, `(derivedModuleGlobalSections X).map (sheafHomComplexUnit X F G)`, is free at the
module level: `sheafHomComplexUnit` is a morphism of `D(O)` and
`AlgebraicGeometry.RingedSite.derivedGlobalSectionsModules` may be applied to it instead. Its
second, `AlgebraicGeometry.RingedSite.globalSectionsDerivedUnit`, is a transcription: every
ingredient of it — the two comparisons of the localization with
`Functor.mapHomologicalComplex`, and the unit of the derived functor — already has a
module-valued counterpart in
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHom`,
`AlgebraicGeometry.RingedSite.derivedGlobalSectionsModulesUnit` among them. Its first leg is the
identification `Hom^•_{Comp^dg(O)}(F, G) = Γ(C, SheafHom^•(F, G))` of Tag 0A8Z, and that is the
leg that needed new mathematics, because the identification was available only as one of
complexes of abelian groups. It is `Γ(C, O)`-linear in every degree, which is
`AlgebraicGeometry.RingedSite.globalSectionsCochainEquiv`, and it is an isomorphism of
*complexes* of `Γ(C, O)`-modules, which is
`AlgebraicGeometry.RingedSite.globalSectionsHomComplexModulesIso`, both of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomModuleSections`. The
comparison of the `dite` differential of `DGCategory.homComplexModules` with that of the Hom
complex, which had exhausted one declaration's heartbeat budget, is paid for once and at an
abstract base category by
`CochainComplex.dgCategoryLinear_homComplexModules_d_apply`.

*The canonical map over `Γ(C, O)` therefore exists*, as
`AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHomModules` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomModuleMap`, and since
every base ring of the source maps to `Γ(C, O)` it is the source's map for every `R`.

*And it forgets to the `D(ℤ)`-valued map below.* Forgetting the `Γ(C, O)`-action of the
module-valued canonical map, and identifying its source with the class of the Hom complex and
its target with the `D(ℤ)`-valued global derived hom, returns
`AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHom`; that is
`AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHomModules_forget` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomModuleForget`. Leg by
leg the first is
`AlgebraicGeometry.RingedSite.homComplexModulesDerivedForgetIso_inv_comp`, the second
`AlgebraicGeometry.RingedSite.globalSectionsModulesDerivedUnit_forget` and the third the
naturality `AlgebraicGeometry.RingedSite.derivedGlobalSectionsModulesForget_naturality`. The two
canonical maps are therefore one map read over two base rings, so a statement about either is a
statement about both, and the derived-hom side of this tag no longer restricts it to `R = ℤ`.

*The other side of the canonical map is over `R` too.* The differential graded module side —
`E`, the homotopy and derived categories of `E`-modules, the derived tensor product
`- ⊗_E^𝐋 K`, its counit, the property-(P) resolutions and the `Ext` readings of Tags 09LC and
09KY — used to be taken at `R = ℤ` and is now taken at `R`, so the objects the clauses below
quantify over are the source's. That was a re-parametrisation of the whole family and not a
lemma, and the only mathematical input it needed was to state the descent of a differential
graded functor to the homotopy categories over an arbitrary base ring rather than over `ℤ`:
`StacksFrontier.Algebra.DifferentialGraded.Module.DGFunctorToComplexes` and its two companions,
whose target is now `CochainComplex.dgCategoryLinear B R`. The property-(P) machinery of
`StacksFrontier.Algebra.DifferentialGraded.Module.PropertyPDerivedModel` was already stated at
three independent universes, so a base ring in the section universe of the site was already
admissible.

*And the clauses have moved.* Reading the map in `D(R)` and not only in `D(ℤ)` meant replacing
`DGCategory.homComplex` by `DGCategory.homComplexModules` on the source side and
`AlgebraicGeometry.RingedSite.globalDerivedHom` by
`AlgebraicGeometry.RingedSite.globalDerivedHomModules` restricted along
`AlgebraicGeometry.RingedSite.ScalarSections.toGlobalSections` on the target side. Three things
were owed, and all three are now in place.

The restriction of scalars from `Γ(C, O)` to a general `R` is
`AlgebraicGeometry.RingedSite.homComplexModulesRestrictIso` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomModuleRestrict`; its
content is `AlgebraicGeometry.RingedSite.ScalarSections.smul_eq_globalSections_smul` read on
cochains, the module structure on Mathlib's cochains being pointwise, so the comparison is the
degreewise identity.

The transport of the target along
`AlgebraicGeometry.RingedSite.tensorWithComplexDerivedRepIso` at the module level is
`AlgebraicGeometry.RingedSite.tensorWithComplexDerivedHomMapDerivedModulesOver`, and costs
nothing: that comparison is a morphism of `D(O)`, so the module-valued global derived hom eats
it exactly as the `D(ℤ)`-valued one does below.

The assembly of the two forget legs is
`AlgebraicGeometry.RingedSite.tensorWithComplexDerivedHomMapModulesOver_forget`: the first leg
is `DGCategory.DGFunctor.homComplexModulesMap_forget`, read against Mathlib's Hom complex in
`AlgebraicGeometry.RingedSite.complexFirstLeg`, which holds degreewise on the nose; the second
is `AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHomModulesOver_forget`. That the
transported map forgets too is the naturality of the forgetful comparison of the global derived
hom in each variable.

The seven registrations of Tag 0CS6 are placed consistently.
Five of them are on the `D(R)`-valued declarations — the two maps in
`StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexDerivedHomModulesOver` and the two
`Ext` readings and the cohomology clause in
`StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexDerivedExtClauseOver` — and the
remaining two, on
`AlgebraicGeometry.RingedSite.tensorWithComplexDerivedExtMap` and
`AlgebraicGeometry.RingedSite.tensorWithComplexDerivedExtMap_q` of
`StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexDerived`, name the map on `Ext`
induced by `- ⊗_E^𝐋 K` and are formed over the source's `R`.

The target is accordingly the global
derived hom of Tag 0B6E with its `Γ(C, O)`-action forgotten,
`AlgebraicGeometry.RingedSite.globalDerivedHom`, which
`AlgebraicGeometry.RingedSite.globalDerivedHomForget` identifies with the `D(Γ(C, O))`-valued
`AlgebraicGeometry.RingedSite.globalDerivedHomModules` of Tag 0B6E.

The source is the differential graded Hom complex `Hom^•_{Mod^dg_(E, d)}(M, N)` of Tag 09LC,
taken at differential graded modules rather than at objects of `D(E, d)`: it computes
`RHom(M, N)` of Section 22.31 when `M` has property (P), which is Tag 0BYW, and the value on an
object of `D(E, d)` does not depend on the property-(P) representative, which is Tag 0BYV.

*That the source is `RHom(M, N)`* is recorded here, on cohomology and for every `M`, `N` in
`D(E, d)`, by `AlgebraicGeometry.RingedSite.tensorWithComplexDerivedHomSourceExtEquiv`: the
degree-`n` cohomology of the source is `Ext^n_{D(E, d)}(M, N)`.
It is not obtained from Tags 0BYV and 0BYW
as they are formalized in this library, which cannot apply here: those two exist only at a
*single* universe parameter, `DifferentialGraded.Bimodule.derivedPrecomp` and
`DifferentialGradedModule.DerivedHomData.isIso_comparison_of_propertyP` both requiring a base
ring `R : Type u₁` together with `DifferentialGradedAlgebra.{u₁, u₁} R` and
`DifferentialGradedModule.{u₁, u₁, u₁}`. The endomorphism differential graded algebra of a
complex of sheaves is an algebra over the base ring `R`, whose universe is independent of the
section universe of the site in which its carrier lies; the diagonal is therefore not
satisfiable. The obstruction is not only the universes: those statements are also built on the
single-universe morphism property `DifferentialGradedModule.quasiIsomorphisms'` and the
`DerivedHomData` localization attached to it, whereas `- ⊗_E^𝐋 K` is defined on the
universe-polymorphic `DifferentialGradedModule.derivedCategory`; the `Naming` section of
`StacksFrontier.Algebra.DGA.QuasiIsomorphisms` records that the two families cannot yet be merged,
because the identification of the two classes of distinguished triangles is Tag 09KH, which is
not formalized.

What is used instead, in
`StacksFrontier.Algebra.DifferentialGraded.Module.HomComplexExtGeneral`, is the composite those two
tags produce for `Ext` out of a *module*, built directly and at independent universes: Tag 09LC
identifies the degree-`n` cohomology of `Hom^•_{Mod^dg_(E, d)}(M, N)` with `Hom_{K(E, d)}(M, N[n])`
(`DifferentialGradedModule.General.homComplexHomologyEquiv`), and the localization
`K(E, d) ⥤ D(E, d)` is bijective on the morphisms out of a module orthogonal on the left to the
acyclic ones (`DifferentialGradedModule.General.bijective_q_map_of_leftOrthogonal`, the mechanism
of Tag 09KY), which a module with property (P) is by Tag 09KM. That route goes through no derived
functor and no bimodule, so it needs neither the `DerivedHomData` localization nor the primed
quasi-isomorphisms, and every ingredient of it was already universe polymorphic. It does not
replace Tags 0BYV and 0BYW in general — nothing below asserts the functorial statement on all of
`D(E, d)`, only the cohomology identification the present clause of Tag 0CS6 consumes.

The target, on the other hand, is moved: `tensorWithComplexDerivedHomMap` lands in the global
derived hom of the *ordinary* tensor products `M ⊗_E K`, and
`AlgebraicGeometry.RingedSite.tensorWithComplexDerivedPropertyPIso` identifies those with the
derived tensor products `M ⊗_E^𝐋 K` whenever `M` has property (P), by the invertibility of the
comparison of Tag 09LX at a left-orthogonal object
(`AlgebraicGeometry.RingedSite.isIso_tensorWithComplexDerivedCounit_app_of_propertyP`). At an
arbitrary object of `D(E, d)` the same identification, read at the chosen property-(P)
representative, is `AlgebraicGeometry.RingedSite.tensorWithComplexDerivedRepIso`, and
`AlgebraicGeometry.RingedSite.tensorWithComplexDerivedHomMapDerived` is the resulting map into
`RHom_O(M ⊗_E^𝐋 K, N ⊗_E^𝐋 K)`. Composing with the comparison of Tag 09LX alone would not
suffice even at a property-(P) module: the global derived hom is contravariant in its first
argument, so the comparison moves that argument unconditionally, but in the covariant argument it
points the wrong way and has to be inverted — which is why an invertibility statement, and hence
a representative at which the comparison is invertible, is needed rather than the comparison
itself.

*The central clause, which is now proved.* It is the assertion that `H^n` of the canonical map is
the map on `Ext` induced by `- ⊗_E^𝐋 K`
(`AlgebraicGeometry.RingedSite.tensorWithComplexDerivedExtMap`), and it is
`AlgebraicGeometry.RingedSite.tensorWithComplexDerivedHomMapDerived_homology` of
`StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexDerivedExtClause`, whose reading over
the source's base ring,
`AlgebraicGeometry.RingedSite.tensorWithComplexDerivedHomMapDerivedModulesOver_homology` of
`StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexDerivedExtClauseOver`, is where the
registration for it sits. Both *sides* of it are identified as `Ext`-groups in every degree: the
`D(E, d)`-side by
`AlgebraicGeometry.RingedSite.tensorWithComplexDerivedHomSourceExtEquiv` above, and the
`D(O)`-side by `AlgebraicGeometry.RingedSite.tensorWithComplexDerivedHomTargetExtEquiv`, which
is `AlgebraicGeometry.RingedSite.globalDerivedHomDegreeEquiv` at the derived tensor products —
the degree-`n` form of
`AlgebraicGeometry.RingedSite.globalDerivedHomModulesDegreeZeroEquiv`, obtained by moving the
degree into the covariant variable along the commutation of the derived internal hom with the
translation,
`AlgebraicGeometry.RingedSite.derivedSheafHomTargetShiftIso`, an identification which is now
also known to be natural in both variables. The identification of the **map** needed three
inputs, and the last of them to arrive was the degree-`n` reading of the canonical map of
Tag 0A8Z into the global derived hom for arbitrary complexes,
`AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHom_homology_degree`; the composition of
the three is carried out in the file named above. See "The assembly" below.

*Available.* The naturality of Tag 0A94 globally, for morphisms of complexes in each variable, is
`AlgebraicGeometry.RingedSite.sheafHomGlobalHomologyEquivDerivedCategoryHom_naturality` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalHomNaturality`.

*Partly available, first.* The degree-`n` reading of the canonical map
`Hom^•(F, G) ⟶ RHom_O(F, G)` of
`AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHom` as the localization functor on
morphism groups. At representatives this is a cancellation and not a computation: for a
K-injective `I` the comparison `AlgebraicGeometry.RingedSite.sheafHomComplexUnit` is the inverse
of `AlgebraicGeometry.RingedSite.derivedSheafHomComparison`
(`AlgebraicGeometry.RingedSite.sheafHomComplexUnit_eq_derivedSheafHomComparison_inv`), and when
`SheafHom(A, I)` is K-injective as well — which for a K-flat `A` is Tag 0A96 — the unit
`AlgebraicGeometry.RingedSite.globalSectionsDerivedUnit` is
`Stacks.Cohomology.ModuleSections.globalSectionsKInjectiveIso`
(`AlgebraicGeometry.RingedSite.globalSectionsDerivedUnit_eq_globalSectionsKInjectiveIso`), so
composing with
`AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquivOfKInjectiveHom` leaves only
the universe-lift bookkeeping of Tag 0A8Z. That case is now **proved**, in degree zero, as
`AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHom_homology_zero` and
`AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHom_homology_zero_of_isKFlat` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomLocalization`.

For the complexes this clause is about, namely the
tensor products `M ⊗_E K` and `N ⊗_E K`, neither hypothesis is available, so the chosen K-flat
and K-injective models have to be passed to; and `AlgebraicGeometry.RingedSite.kFlatModelIso`
and `AlgebraicGeometry.RingedSite.kInjectiveModelIso` are isomorphisms of `D(O)`, not classes of
morphisms of complexes. At the class of a complex each of them *is* a composite of the class of
a morphism of complexes with the inverse of such a class — the target of `kInjectiveModelIso` is
K-injective, so `AlgebraicGeometry.RingedSite.exists_Q_map_eq_of_isKInjective` applies. That
decomposition is now available too, as
`AlgebraicGeometry.RingedSite.exists_Q_map_eq_comp_kInjectiveModelIso`,
`AlgebraicGeometry.RingedSite.exists_Q_map_eq_kInjectiveModelIso_inv` and
`AlgebraicGeometry.RingedSite.kFlatModelIso_hom_comp` of the same file; and the naturality of
`AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquivOfKInjectiveHom` in each
variable along a morphism of complexes is
`AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquivOfKInjectiveHom_naturality` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomTransport`, proved from
the naturality above together with the naturality of
`Stacks.Cohomology.ModuleSections.globalSectionsKInjectiveIso`
(`AlgebraicGeometry.RingedSite.globalSectionsKInjectiveIso_hom_naturality`, which is free: the
comparison is the component of a natural transformation) and
`AlgebraicGeometry.RingedSite.derivedSheafHomComparison_naturality`.

*Where the contravariant variable stops being a problem.* The section "What this file does not
contain" of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSectionsOnDerivedObjects` says
that moving the contravariant variable along an arbitrary morphism of `D(O)` needs a
*two-variable* localization argument. It does not. One variable at a time suffices, because the
calculus of right fractions in the derived category — `CategoryTheory.DerivedCategory.right_fac`
of Mathlib, which is available since `HomotopyCategory.quasiIso` is the morphism property of an
acyclic triangulated subcategory — writes any `θ : Q A ⟶ Q A'` as `inv (Q s) ≫ Q g` with
`s : Y ⟶ A` a quasi-isomorphism, and a K-flat resolution of `Y` (Tag 06YS) makes the auxiliary
complex K-flat, where Tag 0A96 restores the K-injectivity of the internal Hom complex and the
naturality above applies. That is
`AlgebraicGeometry.RingedSite.exists_kFlat_common_refinement`.

*The model-independence of Tag 08JA, which this needed, is now proved.*
`AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv_naturality` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomModelIndependence` is
the naturality of the degree-zero identification of Tag 08JA in both variables for **arbitrary**
morphisms of `D(O)`, so that identification does not depend on the chosen models.

*The commutation with the translation is natural, and so is the degree-`n` identification; both
are now proved.* The commutation of the derived internal Hom with the translation in its
covariant variable, `AlgebraicGeometry.RingedSite.derivedSheafHomTargetShiftIso` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomShift`, is natural in
both variables for **arbitrary** morphisms of `D(O)`:
`AlgebraicGeometry.RingedSite.derivedSheafHomTargetShiftIso_hom_naturality` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomShiftNaturality`. At
K-injective representatives
(`AlgebraicGeometry.RingedSite.derivedSheafHomTargetShiftIsoOfKInjective_hom_naturality`) that is
`AlgebraicGeometry.RingedSite.derivedSheafHomComparison_naturality` together with
`AlgebraicGeometry.RingedSite.sheafHomTargetShiftIso_hom_naturality` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.HomComplexShift` and the commutation of
the localization functor with the translation; and the transport to arbitrary objects needs no
K-flat refinement, because the model used in *both* variables there is the K-injective one, so
both comparisons are already classes of morphisms of complexes. Consequently
`AlgebraicGeometry.RingedSite.globalDerivedHomDegreeEquiv` is natural in both variables as well,
`AlgebraicGeometry.RingedSite.globalDerivedHomDegreeEquiv_naturality` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomDegreeNaturality`,
proved from that, from the model-independence above, and from the naturality of the shift
sequence of the homology functors and of the commutation of derived global sections with the
translation.

*And the degree-zero reading is now off its representative pair.*
`AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv_eq_ofKFlat` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomRepresentativePair`
identifies Tag 08JA at arbitrary objects, read at `(Q A, Q I)` for a K-flat `A` and a K-injective
`I`, with Tag 08JA at the pair `(A, I)` itself. This does *not* follow from the
model-independence above, which compares the chosen models of two different pairs of objects and
says nothing about a representative the construction did not choose; it is the same refinement
argument run once more against the given pair. Composed with
`AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHom_homology_zero_of_isKFlat` it gives the
degree-zero reading of the canonical map against
`AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv`, which is the form
`AlgebraicGeometry.RingedSite.globalDerivedHomDegreeEquiv` is built on.

*And this input is now complete.* What it needed was the compatibility of the canonical map
`AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHom` itself with the translation in its
covariant variable — the square comparing it at `(F, G)` with it at `(F, G[n])`, through the
shift of the Hom complex on the left and through
`AlgebraicGeometry.RingedSite.derivedSheafHomTargetShiftIso` on the right. That square is
`AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHom_shift` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomShiftSquare`, stated at
a K-injective `G`. With it the degree-`n` reading follows from the degree-zero one by the
naturality above, since for a K-flat `F` and a K-injective `G` the pair `(F, G[n])` is a
representative pair along with `(F, G)`: `G[n]` is K-injective and Tag 0A96 applies again. That
last assembly — taking degree-zero homology of the square and reading the result through
`AlgebraicGeometry.RingedSite.globalDerivedHomDegreeEquiv` — is
`AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHom_homology_of_isKFlat`, and is **proved**;
see the paragraphs below and "What remains".

The square is a compatibility with the shift of each factor of
`AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHom`, and those are collected in
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomShiftCompatibility`.
All four are **proved** there.
`AlgebraicGeometry.RingedSite.sheafHomComplexUnit_derivedSheafHomTargetShiftIsoOfKInjective`
is the comparison with the derived internal Hom, which costs nothing: on a K-injective target
that comparison is the inverse of
`AlgebraicGeometry.RingedSite.derivedSheafHomComparison`
(`AlgebraicGeometry.RingedSite.sheafHomComplexUnit_eq_derivedSheafHomComparison_inv`), out of
which `AlgebraicGeometry.RingedSite.derivedSheafHomTargetShiftIsoOfKInjective` is built, so the
compatibility is a cancellation. `AlgebraicGeometry.RingedSite.uliftComplexSelfIso_shift` and
`AlgebraicGeometry.RingedSite.globalSectionsComplexShiftIso` are the universe lift and the
complex of global sections, both degreewise the identity, the latter being Mathlib's commutation
of `CategoryTheory.Functor.mapHomologicalComplex` with the translation.
`AlgebraicGeometry.RingedSite.globalSectionsDerivedUnit_shift` is the unit of derived global
sections, which is the composite of four whiskerings each compatible with the shift — the two
comparisons `CategoryTheory.DerivedCategory.quotientCompQhIso` and
`CategoryTheory.Functor.mapHomotopyCategoryFactors` by Mathlib's instances, and the derived
functor's unit by Mathlib's
`CategoryTheory.Functor.RightDerivedCommShift.natTrans_commShift`. That one could not be
*inferred* from those four instances: `CategoryTheory.Functor.CommShift` is a class of data, and
the functor through which two consecutive whiskerings compose receives two different instances
depending on the bracketing, so `CategoryTheory.NatTrans.CommShift.comp` does not apply to the
composite; stating
`CategoryTheory.NatTrans.CommShiftCore` by hand pins the canonical instances and the four
compatibilities chain, which is
`AlgebraicGeometry.RingedSite.commShiftCore_globalSectionsDerivedUnitNatTrans`.

*And one gap that was not on the list.* The degree-`n` form
`AlgebraicGeometry.RingedSite.globalDerivedHomDegreeEquiv` is built from
`AlgebraicGeometry.RingedSite.derivedSheafHomTargetShiftIso` at the **chosen** K-injective
models, whereas the degree-zero reading of the canonical map lives at the pair `(F, G[n])`; so
the assembly needs that identification read at a representative pair, exactly as it needs
`AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv_eq_ofKFlat` for Tag 08JA. That
is `AlgebraicGeometry.RingedSite.derivedSheafHomTargetShiftIso_eq_ofKInjective`, and unlike the
Tag 08JA statement it needs no K-flat refinement: the comparison of the covariant variable is a
class of a morphism of complexes because the chosen model is K-injective, and so is the
comparison of the contravariant variable, because there the chosen model is the *target* of the
morphism needed, so
`AlgebraicGeometry.RingedSite.exists_Q_map_eq_of_isKInjective` applies to both and step one's
naturality
`AlgebraicGeometry.RingedSite.derivedSheafHomTargetShiftIsoOfKInjective_hom_naturality`
applies directly.

*The fourth factor, which was the last one absent, is now proved.* It is the global description
of Tag 0A8Z itself, `AlgebraicGeometry.RingedSite.SheafHomComplex.globalSectionsIso`, against
`AlgebraicGeometry.RingedSite.sheafHomTargetShiftIso` on the sheaf side and the target shift of
the Hom complex on the module side:
`AlgebraicGeometry.RingedSite.globalSectionsIso_sheafHomTargetShiftIso`. It was the only factor
with a sign-bearing identification on either side, and both signs are in fact absent, so the
compatibility is an identity of homogeneous components rather than a sign computation.
`AlgebraicGeometry.RingedSite.sectionsEquiv_sheafHomTargetShiftIso_hom` describes the sheaf-side
shift by `AlgebraicGeometry.RingedSite.cochainTargetShift`, which is Mathlib's
`CochainComplex.HomComplex.Cochain.rightShift` conjugated by the identification of the
restriction of a shifted complex with the shift of the restriction, and is sign-free; the module
side is `CochainComplex.HomComplex.homComplexTargetShiftIso` of
`StacksFrontier.Homology.HomComplex.TargetShiftIso`, which is that same `rightShift`, built from
`CochainComplex.HomComplex.Cochain.rightShiftAddEquiv` — the equivalence on which
`CochainComplex.HomComplex.CohomologyClass.homAddEquiv` is built through
`CochainComplex.HomComplex.Cocycle.equivHomShift`, so the module side already speaks the
conventions step two below needs, namely those of
`CochainComplex.HomComplex.homComplexHomologyAddEquiv`. The sections description computed
against is `AlgebraicGeometry.RingedSite.sheafHomComplex_globalSectionsIso_v_app`, the
global-sections companion of
`AlgebraicGeometry.RingedSite.globalSectionsIso_homMap_v` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalHomNaturality`.

*And the degree-`n` reading of the canonical map is now proved, at a representative pair.*
`AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHom_homology_of_isKFlat` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomDegreeReading`: for a
K-flat `F` and a K-injective `G` the degree-`n` cohomology of
`AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHom`, read through
`AlgebraicGeometry.RingedSite.globalDerivedHomDegreeEquiv` on the target and Tag 0A8Z in degree
`n` on the source, is the localization functor `K(O) ⥤ D(O)` on morphism groups. It is the square
above read on degree-zero homology, and it did need **both** representative-pair
identifications — `AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv_eq_ofKFlat`
for Tag 08JA and `AlgebraicGeometry.RingedSite.derivedSheafHomTargetShiftIso_eq_ofKInjective` for
the target shift, the second being the gap described above, which the first does not cover —
together with `AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv_naturality` to
absorb the transport of the covariant variable from `(Q G)[n]` to `Q (G[n])`. The degree moves by
the shift sequence of the homology functors of `D(Ab)`, `CategoryTheory.Functor.isoShift`, and
no transport of `CochainComplex.HomComplex.CohomologyClass.homAddEquiv` along
`CategoryTheory.shiftFunctorZero` had to be built: the degree-zero reading already states its
answer in exactly that shape, at `(F, (G[n])[0])`, so reading it at the pair `(F, G[n])` produces
the shape the clause wants with no further bookkeeping. Note that the identification is stated
against `(DerivedCategory.Q.commShiftIso n).app G` rather than absorbing it, because
`globalDerivedHomDegreeEquiv` lands in `Hom(Q F, (Q G)[n])` while Tag 0A8Z in degree `n` lands in
`Hom(Q F, Q (G[n]))`; absorbing it would read as if the localization functor commuted with the
translation on the nose.

*And the naturality the transport runs against is now proved.*
`AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHom_naturality` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomCanonicalNaturality`:
the canonical map is natural in both complexes for morphisms of complexes, **with no hypothesis
on any of the four**. Only one of its three factors was missing,
`AlgebraicGeometry.RingedSite.sheafHomComplexUnit_naturality`, and the shortcut that made the
*shift* compatibility of `sheafHomComplexUnit` free — passing to Tag 0A97 at a K-injective target
— is **not** what works for naturality, because
`AlgebraicGeometry.RingedSite.derivedSheafHomComparison_naturality` assumes both targets
K-injective and the transport needs the arbitrary case. What works instead is to pass to the
comparison with the chosen *resolution*:
`AlgebraicGeometry.RingedSite.derivedSheafHomResolutionComparison_naturality` carries no
hypothesis at all, being the naturality of the lifting datum of the descent, and what is left
after it is the naturality of `AlgebraicGeometry.RingedSite.kInjectiveAugmentation`, which is
free.

*And the degree-`n` reading is now off the representative pair, and the degree-shift bookkeeping
is now present.* The first of the three inputs of the clause is therefore **complete**:
`AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHom_homology_degree` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomDegreeTransport` reads
the degree-`n` cohomology of the canonical map as the localization functor `K(O) ⥤ D(O)` on
morphism groups for **arbitrary** complexes `A`, `B`, with the source class read by Tag 0A5X in
degree `n` (`CochainComplex.HomComplex.homComplexHomologyAddEquiv`) and the target by
`AlgebraicGeometry.RingedSite.globalDerivedHomDegreeEquiv`. Three things went into it.

*The degree-shift bookkeeping, which was the one genuinely absent input, is proved.* The
degree-`n` reading at a representative pair states its answer in the degree-**zero** shape at
the pair `(F, G[n])`, whereas
`AlgebraicGeometry.RingedSite.tensorWithComplexHomComplexMap_homology`, the third input of the
clause, speaks the degree-`n` identification. The lemma matching them is
`CochainComplex.HomComplex.homComplexHomologyAddEquiv_degreeShift_Q` of
`StacksFrontier.Homology.HomComplex.TargetShiftDegree`, together with its plain form
`CochainComplex.HomComplex.homComplexHomologyAddEquiv_degreeShift`; the comparison they run
through is `CochainComplex.HomComplex.homComplexDegreeShift`, the shift sequence of the homology
functors of cochain complexes followed by `homComplexTargetShiftIso`. Two auxiliary facts had to
be proved for it: that the `isoZero` of the shift sequence of the homology functor of the derived
category is the identity
(`CochainComplex.HomComplex.derivedCategoryIsoShiftZero_hom`, which
`CategoryTheory.Functor.isoShift` carries and which Mathlib evaluates only at objects in the
image of the localization functor),
and that the comparison `H^n(Q D) ⟶ H^0(D[n])` of the derived category is the one of cochain
complexes (`CochainComplex.HomComplex.derivedCategoryIsoShift_inv_app_Q_obj`, which is Mathlib's
`CategoryTheory.DerivedCategory.shiftMap_homologyFunctor_map_Q` at an identity morphism, run in
the inverse direction).

*The reading restated in degree `n`.*
`AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHom_homology_degree_of_isKFlat` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomDegreeSource` is the
degree-`n` reading at a representative pair with its degree-zero source shape replaced by the
degree-`n` identification. Doing this **before** the transport removes an input the earlier plan
for the transport listed: the naturality of
`CochainComplex.HomComplex.homComplexTargetShiftIso` under
`CochainComplex.HomComplex.homComplexConj` is not needed, because once the reading is stated in
degree `n` the target shift no longer occurs in it. What is needed on the source side is only
`CochainComplex.HomComplex.homComplexHomologyAddEquiv_conj` of the same file, which is
`homologyAddEquiv_conj` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.IntoAKInjectiveComplex` read through
`CochainComplex.HomComplex.toHom_cohomologyClassPrecomp` and `...Postcomp`.

That same file also names the map the transported statement has to be phrased with:
`AlgebraicGeometry.RingedSite.localizationHomAddHom`, the localization functor on morphism groups
`Hom_{K(O)}(A, B) →+ Hom_{D(O)}(A, B)` for arbitrary complexes. The reading at a representative
pair is stated against `AlgebraicGeometry.RingedSite.homotopyHomDerivedCategoryEquiv`, which is
an *isomorphism* and so exists only at a K-injective target; what survives the transport is the
underlying map, and
`AlgebraicGeometry.RingedSite.homotopyHomDerivedCategoryEquiv_eq` identifies the two where both
are defined.

*The transport itself.* `AlgebraicGeometry.RingedSite.exists_kFlat_common_refinement` at the
identity of `Q A` gives a K-flat `R` with `u : R ⟶ A` of invertible class, and
`AlgebraicGeometry.RingedSite.exists_Q_map_eq_kInjectiveModelIso_inv` gives
`h : B ⟶ kInjectiveModel (Q B)` of invertible class; no morphism of complexes
`R ⟶ A` is available from `AlgebraicGeometry.RingedSite.kFlatModelIso` directly — the chosen
K-flat model maps into the chosen K-INJECTIVE one, which is why
`AlgebraicGeometry.RingedSite.kFlatModelIso_hom_comp` is phrased as it is — so the contravariant
variable goes through the refinement and not through the chosen model. The degree-`n` homology of
`AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHom_naturality` at `(u, h)` is then read
on the target by `AlgebraicGeometry.RingedSite.globalDerivedHomDegreeEquiv_naturality` at
`(Q u, Q h)` and on the source by the conjugation naturality above, and `Q u` and the class of
`h[n]` cancel, the latter being invertible because the quasi-isomorphisms are stable under the
translation.

*The assembly.* **Nothing remains: the clause is proved.** Its statement is

`tensorWithComplexDerivedHomTargetExtEquiv X R K M N n`
`  (H^n(tensorWithComplexDerivedHomMapDerived X R K M N) η) =`
`    tensorWithComplexDerivedExtMap X R K n`
`      (tensorWithComplexDerivedHomSourceExtEquiv X R K M N n η)`

for arbitrary `M`, `N` in `D(E, d)` and every `n`, which is exactly the source's second assertion
with both sides already identified as the `Ext`-groups it compares; it is
`AlgebraicGeometry.RingedSite.tensorWithComplexDerivedHomMapDerived_homology` of
`StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexDerivedExtClause`. The three inputs
are `AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHom_homology_degree` for the second leg
of the canonical map, `AlgebraicGeometry.RingedSite.tensorWithComplexHomComplexMap_homology` for
the first, and `AlgebraicGeometry.RingedSite.tensorWithComplexDerivedExtMap_q` for the passage
from `K(E, d)` to `D(E, d)`; the glue between them has four parts, carried out there in this order.

*(i)* The first leg. `H^n` of `DerivedCategory.Q.map (tensorWithComplexHomComplexMap X R K M N)`
has to be turned into `HomologicalComplex.homologyMap` of that morphism by the naturality of
`CategoryTheory.DerivedCategory.homologyFunctorFactors` in degree `n`, which is what
`AlgebraicGeometry.RingedSite.tensorWithComplexHomComplexMap_homology` is stated against; this is
one application of `NatTrans.naturality` and is the shape
`AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHom_homology_degree` already consumes on
its own source side.

*(ii)* The two transports along `AlgebraicGeometry.RingedSite.tensorWithComplexDerivedRepIso` that
`AlgebraicGeometry.RingedSite.tensorWithComplexDerivedHomMapDerived` carries come off the target
side by `AlgebraicGeometry.RingedSite.globalDerivedHomDegreeEquiv_naturality`, exactly as the
transport above used it at `(Q u, Q h)`.

*(iii)* The comparison of the two localizations.
The sheaf side speaks `AlgebraicGeometry.RingedSite.localizationHomAddHom`, built on
`CategoryTheory.DerivedCategory.Qh`, while
`AlgebraicGeometry.RingedSite.tensorWithComplexDerivedExtMap_q` speaks
`(DifferentialGradedModule.quasiIsomorphisms _).Q` on the differential graded side and
`AlgebraicGeometry.RingedSite.tensorWithComplexToDerivedCategory` between them, and that functor
*is* `AlgebraicGeometry.RingedSite.tensorWithComplexHomotopy ⋙ CategoryTheory.DerivedCategory.Qh`
by definition — so `CategoryTheory.Functor.commShiftIso_comp_hom_app` splits its commutation with
the translation into the two factors, and `localizationHomAddHom` conjugates `Qh` by
`CategoryTheory.DerivedCategory.quotientCompQhIso`, whose `hom` is a
`CategoryTheory.NatTrans.CommShift` in Mathlib, which is what carries the remaining factor to
`DerivedCategory.Q.commShiftIso`. Three inputs are needed, and all three are
proved in `StacksFrontier.Algebra.DifferentialGraded.Module.DGFunctorHomotopyCommShift`:
`DifferentialGradedModule.dgFunctorToHomotopyCategory_commShiftIso_hom_app`, which identifies the
commutation of `K(E, d) ⥤ K(O)` with the translation as
`DifferentialGradedModule.dgFunctorToComplexesShiftIso` conjugated by the two quotient functors
(a `private` equivalent exists in
`StacksFrontier.Algebra.DifferentialGraded.Module.DGFunctorToComplexes`, hence is not importable,
and it is reproved there without the `set_option backward.*` that file carries), and
`DifferentialGradedModule.General.homAddEquivOfEq_apply` together with
`DifferentialGradedModule.General.homAddEquivOfEq_comp_commShiftIso_inv`, which cancel the
transport along the equality of objects that Tag 09LC's identification produces against the
commutation of `DifferentialGradedModule.toHomotopyCategory` with the translation (whose
`eqToHom` spelling is the already public
`DifferentialGradedModule.quotientShiftIso_inv_eq_eqToHom`).

That chase is
`AlgebraicGeometry.RingedSite.localizationHomAddHom_tensorWithComplexHomotopy` of the file named
above: for a morphism `c : [P_M] ⟶ [P_N[n]]` of `K(E, d)`,

`localizationHomAddHom X (P_M ⊗_E K) ((P_N ⊗_E K)[n]) (tensorWithComplexHomotopy.map c ≫
quotient.map (dgFunctorToComplexesShiftIso _ P_N n).hom) ≫ (Q.commShiftIso n).hom.app
(P_N ⊗_E K) = (quotientCompQhIso _).inv.app (P_M ⊗_E K) ≫ tensorWithComplexToDerivedCategoryExtMap
X R K n (homAddEquivOfEq (toHomotopyCategory_obj_shift _ P_N n) c) ≫
((quotientCompQhIso _).hom.app (P_N ⊗_E K))[n]`.

*(iv)* The source identification unfolded.
`AlgebraicGeometry.RingedSite.tensorWithComplexDerivedHomSourceExtEquiv` is
`CategoryTheory.DerivedCategory.homologyFunctorFactors` followed by
`DifferentialGradedModule.propertyPModelExtEquiv`, and that is
`DifferentialGradedModule.General.homComplexExtEquiv` at the chosen property-(P) representatives
conjugated by `DifferentialGradedModule.propertyPModelIso`; `homComplexExtEquiv` is in turn
`DifferentialGradedModule.General.homComplexHomologyEquiv` followed by the localization. The third
input `tensorWithComplexHomComplexMap_homology` is stated at a class presented as
`(General.homScHomologyEquiv _ _ _ n).symm (QuotientAddGroup.mk f)` for a closed degree-`n`
homogeneous `f`, and `General.homScHomologyEquiv` is an isomorphism and
`QuotientAddGroup.mk` is surjective, so every class is of that form; that surjectivity is how the
input gets applied to an arbitrary `η`.

*The trailing comparison cancels.* `AlgebraicGeometry.RingedSite.tensorWithComplexDerivedRepIso`
ends in `CategoryTheory.DerivedCategory.quotientCompQhIso`, and that is the same comparison
`AlgebraicGeometry.RingedSite.localizationHomAddHom` carries as its inverse, so in the assembly
the two cancel rather than accumulate; this is what makes step (ii) shorter than it reads. It
also means no inverse of the comparison of Tag 09LX is needed: on the covariant side the counit
cancels it forwards, which is how
`AlgebraicGeometry.RingedSite.counit_comp_quotientCompQhIso_hom_comp_repIso_inv` is phrased.

**The tag for the clause sits on the composed statement only** — on
`AlgebraicGeometry.RingedSite.tensorWithComplexDerivedHomMapDerivedModulesOver_homology` of
`StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexDerivedExtClauseOver`, the reading of
that clause over the source's base ring, and on nothing else, since a registration on anything
less than the composed statement would overstate it.


*Available, second.* The naturality of Tag 09LC under a differential graded functor: the first
leg of the canonical map is `AlgebraicGeometry.RingedSite.tensorWithComplexHomComplexMap`, the
action of the functor of Tag 09LV on the differential graded Hom complexes, and the clause needs
its effect on cohomology to be the action of that functor on the morphism groups of the homotopy
categories, under `DifferentialGradedModule.General.homComplexHomologyEquiv` on one side and
Tag 0A8Z on the other. That compatibility is
`AlgebraicGeometry.RingedSite.tensorWithComplexHomComplexMap_homology` below, which is
`DifferentialGradedModule.homAddEquiv_homologyAddEquiv_homologyMap` of
`StacksFrontier.Algebra.DifferentialGraded.Module.DGFunctorHomComplexCohomology` read at the
differential graded functor of Tag 09LV. The passage from the homotopy category to `D(E, d)` is
then `AlgebraicGeometry.RingedSite.tensorWithComplexDerivedExtMap_q`, which already compares the
map on `Ext` induced by `- ⊗_E^𝐋 K` with the map induced by the functor of Tag 09LV read on
homotopy categories.

The shift is carried there by
`DifferentialGradedModule.dgFunctorToComplexesShiftIso` rather than by the commutation of the
homotopy-category functor with the translation, because the target of Tag 0A8Z is the group of
morphisms into `(HomotopyCategory.quotient _ _).obj ((N ⊗_E K)⟦n⟧)`, whose identification with
the `n`-shift of the homotopy class of `N ⊗_E K` is an equality of objects and not a
definitional one; the two differ by that transport only.

The universes are the diagonal ones: the derived internal Hom and derived global sections of a
ringed site force the site universes and the module universe together — see the implementation
notes of `StacksDraft.Ch21.Sec34.DerivedInternalHomOnASite` — so the section universes of `K` and
the carriers of the differential graded modules are taken in the same universe as the site. That
is what makes the diagonal the *common* setting for the two halves of Tag 0CS6 rather than one
choice among several: `AlgebraicGeometry.RingedSite.globalDerivedHom` exists only for
`X : RingedSite.{u, u, u}` with modules in `SheafOfModules.{u}`, whereas the derived tensor
product and the maps it induces on `Ext`, in
`StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexDerived`, are polymorphic in
`{u, v, w, t, s}` and therefore specialise here; a common setting with the site universes kept
apart does not exist, since the ambient module category of the tensor products is
`SheafOfModules.{max u v w t s}`, which the global derived hom requires to be `SheafOfModules.{u}`.

## References

* [Stacks Project, Tag 0CS6](https://stacks.math.columbia.edu/tag/0CS6)
* [Stacks Project, Tag 0B6E](https://stacks.math.columbia.edu/tag/0B6E)
* [Stacks Project, Tag 09LV](https://stacks.math.columbia.edu/tag/09LV)
* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry

namespace AlgebraicGeometry.RingedSite

universe u o

attribute [local instance] HasDerivedCategory.standard

variable (X : AlgebraicGeometry.RingedSite.{u, u, u})
  (R : Type o) [CommRing R] [Linear R (TensorModO.{u, u, u, u, u} X)]
  [ScalarSections.{u, u, u, u, u, o} X R]
  (K : CochainComplex (ModO.{u, u, u, u} X) ℤ)

/-- The map of differential graded Hom complexes induced by tensoring with `K`: the action of
the differential graded functor of Tag 09LV on homogeneous morphisms, read into the Hom complex
of complexes of `O`-modules.

This is `DifferentialGradedModule.dgFunctorHomComplexMap` at the differential graded functor of
Tag 09LV, which is what makes the naturality of Tag 09LC under a differential graded functor
available here as
`AlgebraicGeometry.RingedSite.tensorWithComplexHomComplexMap_homology`. -/
def tensorWithComplexHomComplexMap
    (M N : (DifferentialGradedModule.dgCategory.{_, _, u}
      (Rep.{u, u, u, u, u, o} X R K).algebra).Obj) :
    (DifferentialGradedModule.dgCategory.{_, _, u}
        (Rep.{u, u, u, u, u, o} X R K).algebra).homComplex M N ⟶
      ((tensorWithComplexDG.{u, u, u, u, u, o} X R K).functor.obj M).HomComplex
        ((tensorWithComplexDG.{u, u, u, u, u, o} X R K).functor.obj N) :=
  DifferentialGradedModule.dgFunctorHomComplexMap
    (tensorWithComplexDG.{u, u, u, u, u, o} X R K).functor M N

/-- **Stacks 09LC, naturality under the differential graded functor of Tag 09LV.** The degree-`n`
cohomology of `AlgebraicGeometry.RingedSite.tensorWithComplexHomComplexMap` is the action of the
functor `- ⊗_E K` on homotopy-category morphism groups: the cohomology class of the Hom complex
`Hom^•_{Mod^dg_(E, d)}(M, N)` attached to a closed degree-`n` homogeneous morphism `f` goes to
the homotopy class of `f ⊗_E K`, read into `(M ⊗_E K) ⟶ (N ⊗_E K)[n]` along the comparison
`(N[n]) ⊗_E K ≅ (N ⊗_E K)[n]`.

This is `DifferentialGradedModule.homAddEquiv_homologyAddEquiv_homologyMap` at the differential
graded functor of Tag 09LV; it is the third of the three inputs the central clause of Tag 0CS6
needs — see the implementation notes. -/
theorem tensorWithComplexHomComplexMap_homology
    (M N : (DifferentialGradedModule.dgCategory.{_, _, u}
      (Rep.{u, u, u, u, u, o} X R K).algebra).Obj) (n : ℤ)
    (f : ↥(AddCommGrpCat.Hom.hom
      (DifferentialGradedModule.General.homSc (Rep.{u, u, u, u, u, o} X R K).algebra M N n).g).ker)
        :
    CochainComplex.HomComplex.CohomologyClass.homAddEquiv
        (CochainComplex.HomComplex.homologyAddEquiv
          ((tensorWithComplexDG.{u, u, u, u, u, o} X R K).functor.obj M)
          ((tensorWithComplexDG.{u, u, u, u, u, o} X R K).functor.obj N) n
          (HomologicalComplex.homologyMap (tensorWithComplexHomComplexMap.{u, o} X R K M N) n
            ((DifferentialGradedModule.General.homScHomologyEquiv
              (Rep.{u, u, u, u, u, o} X R K).algebra M N n).symm (QuotientAddGroup.mk f)))) =
      (tensorWithComplexHomotopy.{u, u, u, u, u, o} X R K).map
          (DifferentialGradedModule.General.closedToHomotopy
            (Rep.{u, u, u, u, u, o} X R K).algebra M N n f) ≫
        (HomotopyCategory.quotient (TensorModO.{u, u, u, u, u} X) (ComplexShape.up ℤ)).map
          (DifferentialGradedModule.dgFunctorToComplexesShiftIso
            (tensorWithComplexDG.{u, u, u, u, u, o} X R K).functor N n).hom :=
  DifferentialGradedModule.homAddEquiv_homologyAddEquiv_homologyMap
    (tensorWithComplexDG.{u, u, u, u, u, o} X R K).functor f

/-- **Stacks 0CS6**, the canonical map at the level of differential graded modules. *For every
`M`, `N` there is a canonical map* `RHom(M, N) ⟶ RHom_O(M ⊗_E K^•, N ⊗_E K^•)` *in `D(R)`.* The
differential graded functor of Tag 09LV acts on the differential graded Hom complexes, and the
Hom complex of two complexes of `O`-modules maps canonically to their global derived hom of
Tag 0B6E; the composite is the map below.

Its source is the differential graded Hom complex `Hom^•_{Mod^dg_(E, d)}(M, N)` of two
differential graded modules, not `RHom(M, N)` for two objects of `D(E, d)`; the two agree when
`M` has property (P), by Tag 0BYW, but that identification is not available at these universes —
see the implementation notes.

The endomorphism differential graded algebra `E`, and with it the objects `M` and `N` below, are
taken over the source's base ring `R`. The map itself is read in `D(ℤ) = D(Ab)`, with the
scalars of its source and target forgotten, rather than in the source's `D(R)`; the
`D(R)`-valued map is
`AlgebraicGeometry.RingedSite.tensorWithComplexDerivedHomMapModulesOver` of
`StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexDerivedHomModulesOver`, which carries
the registration of Tag 0CS6 and which
`AlgebraicGeometry.RingedSite.tensorWithComplexDerivedHomMapModulesOver_forget` identifies with
the map below. The two are one map read over two base rings. -/
def tensorWithComplexDerivedHomMap
    (M N : (DifferentialGradedModule.dgCategory.{_, _, u}
      (Rep.{u, u, u, u, u, o} X R K).algebra).Obj) :
    DerivedCategory.Q.obj
        ((DifferentialGradedModule.dgCategory.{_, _, u}
          (Rep.{u, u, u, u, u, o} X R K).algebra).homComplex M N) ⟶
      ((globalDerivedHom X).obj (op (DerivedCategory.Q.obj
            ((tensorWithComplexDG.{u, u, u, u, u, o} X R K).functor.obj M)))).obj
        (DerivedCategory.Q.obj
          ((tensorWithComplexDG.{u, u, u, u, u, o} X R K).functor.obj N)) :=
  DerivedCategory.Q.map (tensorWithComplexHomComplexMap.{u, o} X R K M N) ≫
    homComplexToGlobalDerivedHom X _ _

/-! ### Moving the target to the derived tensor products -/

/-- **On a module with property (P) the derived tensor product with `K` is the ordinary one.**
The comparison of Tag 09LX is invertible at a differential graded module with property (P), by
`AlgebraicGeometry.RingedSite.isIso_tensorWithComplexDerivedCounit_app_of_propertyP`, and the
value of the functor being derived at such a module is the class of the ordinary tensor product
`M ⊗_E K` in `D(O)`. -/
def tensorWithComplexDerivedPropertyPIso
    {M : (DifferentialGradedModule.dgCategory.{_, _, u}
      (Rep.{u, u, u, u, u, o} X R K).algebra).Obj}
    (hM : Nonempty (DifferentialGradedModule.General.PropertyPFiltration M)) :
    (tensorWithComplexDerived.{u, u, u, u, u, o} X R K).obj
        ((DifferentialGradedModule.quasiIsomorphisms
            (Rep.{u, u, u, u, u, o} X R K).algebra).Q.obj
          ((DifferentialGradedModule.toHomotopyCategory
            (Rep.{u, u, u, u, u, o} X R K).algebra).obj M)) ≅
      DerivedCategory.Q.obj ((tensorWithComplexDG.{u, u, u, u, u, o} X R K).functor.obj M) :=
  have := isIso_tensorWithComplexDerivedCounit_app_of_propertyP.{u, u, u, u, u, o} X R K hM
  asIso ((tensorWithComplexDerivedCounit.{u, u, u, u, u, o} X R K).app
      ((DifferentialGradedModule.toHomotopyCategory
        (Rep.{u, u, u, u, u, o} X R K).algebra).obj M)) ≪≫
    (DerivedCategory.quotientCompQhIso _).app _

/-- **The derived tensor product of an arbitrary object of `D(E, d)` is the ordinary tensor
product of its chosen property-(P) representative.** Every object of `D(E, d)` is represented by
a differential graded module with property (P)
(`DifferentialGradedModule.propertyPModelIso`), and at such a module the comparison of Tag 09LX
is invertible, which is
`AlgebraicGeometry.RingedSite.tensorWithComplexDerivedPropertyPIso`.

This is the reduction the proof of Tag 0CS6 performs — "we may assume `M` and `N` are
differential graded `E`-modules with property (P)" — made into a construction, so that the
statements below can quantify over every object of `D(E, d)` as the source does. -/
def tensorWithComplexDerivedRepIso
    (M : DifferentialGradedModule.derivedCategory (Rep.{u, u, u, u, u, o} X R K).algebra) :
    (tensorWithComplexDerived.{u, u, u, u, u, o} X R K).obj M ≅
      DerivedCategory.Q.obj ((tensorWithComplexDG.{u, u, u, u, u, o} X R K).functor.obj
        (DifferentialGradedModule.propertyPModel.{o, u, 0}
          (Rep.{u, u, u, u, u, o} X R K).algebra M)) :=
  (tensorWithComplexDerived.{u, u, u, u, u, o} X R K).mapIso
      (DifferentialGradedModule.propertyPModelIso.{o, u, 0}
        (Rep.{u, u, u, u, u, o} X R K).algebra M).symm ≪≫
    tensorWithComplexDerivedPropertyPIso.{u, o} X R K
      (DifferentialGradedModule.propertyPFiltration_propertyPModel.{o, u, 0}
        (Rep.{u, u, u, u, u, o} X R K).algebra M)

/-- **Stacks 0CS6**, the canonical map with the target of the source's statement, *for every*
`M`, `N` *in* `D(E, d)`. The canonical map of
`AlgebraicGeometry.RingedSite.tensorWithComplexDerivedHomMap`, taken at the chosen property-(P)
representatives of `M` and `N`, is read into the global derived hom of the *derived* tensor
products,

`RHom(M, N) ⟶ RHom_O(M ⊗_E^𝐋 K^•, N ⊗_E^𝐋 K^•)`,

by transporting both arguments along
`AlgebraicGeometry.RingedSite.tensorWithComplexDerivedRepIso`. The global derived hom is
contravariant in the first argument, where that isomorphism is used as it stands, and covariant
in the second, where it is inverted.

There is no hypothesis on `M` or `N`: property (P) is a device of the source's proof, not part of
its statement, and it is discharged here by the choice of representative, whose existence is
Tag 09KP. The source object is the differential graded Hom complex of the two representatives,
which is `RHom(M, N)` read on cohomology by
`AlgebraicGeometry.RingedSite.tensorWithComplexDerivedHomSourceExtEquiv`.

As for `AlgebraicGeometry.RingedSite.tensorWithComplexDerivedHomMap`, the objects are over the
source's base ring `R` and the map is read in `D(ℤ)` and not in the source's `D(R)`. The
`D(R)`-valued map is
`AlgebraicGeometry.RingedSite.tensorWithComplexDerivedHomMapDerivedModulesOver` of
`StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexDerivedHomModulesOver`, which carries
the registration of Tag 0CS6 and forgets to this one by
`AlgebraicGeometry.RingedSite.tensorWithComplexDerivedHomMapDerivedModulesOver_forget`. -/
def tensorWithComplexDerivedHomMapDerived
    (M N : DifferentialGradedModule.derivedCategory (Rep.{u, u, u, u, u, o} X R K).algebra) :
    DerivedCategory.Q.obj
        ((DifferentialGradedModule.dgCategory.{_, _, u}
            (Rep.{u, u, u, u, u, o} X R K).algebra).homComplex
          (DifferentialGradedModule.propertyPModel.{o, u, 0}
            (Rep.{u, u, u, u, u, o} X R K).algebra M)
          (DifferentialGradedModule.propertyPModel.{o, u, 0}
            (Rep.{u, u, u, u, u, o} X R K).algebra N)) ⟶
      ((globalDerivedHom X).obj
          (op ((tensorWithComplexDerived.{u, u, u, u, u, o} X R K).obj M))).obj
        ((tensorWithComplexDerived.{u, u, u, u, u, o} X R K).obj N) :=
  tensorWithComplexDerivedHomMap.{u, o} X R K _ _ ≫
    ((globalDerivedHom X).map
        (op (tensorWithComplexDerivedRepIso.{u, o} X R K M).hom)).app _ ≫
      ((globalDerivedHom X).obj _).map (tensorWithComplexDerivedRepIso.{u, o} X R K N).inv

/-! ### The source of the canonical map is `RHom(M, N)` -/

/-- **Stacks 0CS6, the source of the canonical map**, *for every* `M`, `N` *in* `D(E, d)`. The
degree-`n` cohomology of the source of
`AlgebraicGeometry.RingedSite.tensorWithComplexDerivedHomMapDerived` is the `Ext`-group

`Ext^n_{D(E, d)}(M, N) = Hom_{D(E, d)}(M, N[n])`,

so that source really is `RHom(M, N)` read on cohomology.

This is `DifferentialGradedModule.propertyPModelExtEquiv`: on the chosen property-(P)
representatives it is `DifferentialGradedModule.General.homComplexExtEquivOfPropertyP`, the
composite of Tag 09LC in every degree with the mechanism of Tag 09KY, at the independent
universes of the endomorphism differential graded algebra of `K` — the base ring is the source's
`R` while the carrier lies in the section universe of the site, which the single-universe
Tags 0BYW and 0CS5 cannot reach, see the implementation notes — and the two isomorphisms of
`DifferentialGradedModule.propertyPModelIso` then carry the `Ext`-group from the representatives
to `M` and `N` themselves. The cohomology is read on the class of the Hom complex in `D(ℤ)` by
`CategoryTheory.DerivedCategory.homologyFunctorFactors`, so it is the cohomology of the actual
source of the canonical map.

There is no hypothesis on `M` or `N`. Note that the hypothesis cannot simply be dropped from a
statement about the Hom complex of `M` and `N` themselves: the degree-`n` cohomology of
`Hom^•_{Mod^dg_(E, d)}(M, N)` is `Hom_{K(E, d)}(M, N[n])`, which is *not* the `Ext`-group unless
`M` is orthogonal on the left to the acyclic modules. What removes the hypothesis is the change
of source object to the property-(P) representatives, which is the source's own reduction.

The cohomology is read here in `D(ℤ)`; the same reading for the `D(R)`-valued map is
`AlgebraicGeometry.RingedSite.tensorWithComplexDerivedHomSourceExtEquivOver` of
`StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexDerivedExtClauseOver`, which carries
the registration of Tag 0CS6 and is this equivalence read through the comparison of the two
cohomologies. -/
def tensorWithComplexDerivedHomSourceExtEquiv
    (M N : DifferentialGradedModule.derivedCategory (Rep.{u, u, u, u, u, o} X R K).algebra)
    (n : ℤ) :
    ↥((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
        (DerivedCategory.Q.obj
          ((DifferentialGradedModule.dgCategory.{_, _, u}
              (Rep.{u, u, u, u, u, o} X R K).algebra).homComplex
            (DifferentialGradedModule.propertyPModel.{o, u, 0}
              (Rep.{u, u, u, u, u, o} X R K).algebra M)
            (DifferentialGradedModule.propertyPModel.{o, u, 0}
              (Rep.{u, u, u, u, u, o} X R K).algebra N)))) ≃+ (M ⟶ N⟦n⟧) :=
  (((DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} n).app
      _).addCommGroupIsoToAddEquiv).trans
    (DifferentialGradedModule.propertyPModelExtEquiv.{o, u, 0}
      (Rep.{u, u, u, u, u, o} X R K).algebra M N n)

/-! ### The target of the canonical map is `RHom_O(M ⊗_E^𝐋 K, N ⊗_E^𝐋 K)` -/

/-- **Stacks 0CS6, the target of the canonical map**, *for every* `M`, `N` *in* `D(E, d)`. The
degree-`n` cohomology of the target of
`AlgebraicGeometry.RingedSite.tensorWithComplexDerivedHomMapDerived` is the `Ext`-group

`Ext^n_{D(O)}(M ⊗_E^𝐋 K^•, N ⊗_E^𝐋 K^•) = Hom_{D(O)}(M ⊗_E^𝐋 K^•, (N ⊗_E^𝐋 K^•)[n])`.

This is `AlgebraicGeometry.RingedSite.globalDerivedHomDegreeEquiv`, the degree-`n` cohomology of
the global derived hom of Tag 0B6E, at the derived tensor products; it is the companion of
`AlgebraicGeometry.RingedSite.tensorWithComplexDerivedHomSourceExtEquiv` on the other side of
the canonical map, and together the two exhibit both cohomology modules of the clause as the
`Ext`-groups the clause compares. That the *map* between them is the one induced by
`- ⊗_E^𝐋 K^•` is not asserted here; it is
`AlgebraicGeometry.RingedSite.tensorWithComplexDerivedHomMapDerived_homology` of
`StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexDerivedExtClause`.

The cohomology is read here in `D(ℤ)`; the same reading for the `D(R)`-valued map is
`AlgebraicGeometry.RingedSite.tensorWithComplexDerivedHomTargetExtEquivOver` of
`StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexDerivedExtClauseOver`, which carries
the registration of Tag 0CS6.

There is no hypothesis on `M` or `N`, and none on the site either: the five typeclass
assumptions under which the degree-`n` reading of the global derived hom is stated in
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomShift` are all
inferable for an arbitrary `AlgebraicGeometry.RingedSite.{u, u, u}`, so they are not carried
here. -/
def tensorWithComplexDerivedHomTargetExtEquiv
    (M N : DifferentialGradedModule.derivedCategory (Rep.{u, u, u, u, u, o} X R K).algebra)
    (n : ℤ) :
    letI := tensorModOHasBinaryBiproducts.{u, u, u, u, u} X
    ↥((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
        (((globalDerivedHom X).obj
            (op ((tensorWithComplexDerived.{u, u, u, u, u, o} X R K).obj M))).obj
          ((tensorWithComplexDerived.{u, u, u, u, u, o} X R K).obj N))) ≃+
      ((tensorWithComplexDerived.{u, u, u, u, u, o} X R K).obj M ⟶
        ((tensorWithComplexDerived.{u, u, u, u, u, o} X R K).obj N)⟦n⟧) :=
  have := tensorModOHasBinaryBiproducts.{u, u, u, u, u} X
  have : HasSheafify X.J AddCommGrpCat.{u} := inferInstance
  have : X.J.WEqualsLocallyBijective AddCommGrpCat.{u} := inferInstance
  @globalDerivedHomDegreeEquiv.{u} X inferInstance inferInstance
    (Stacks.SheafOfModules.Tensor.sheafTensor_additive.{u, u, u, u, u} X.O)
    (Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive.{u, u, u, u, u} X.O)
    (Stacks.SheafOfModules.Tensor.hasMapBifunctor_sheafTensor.{u, u, u, u, u} X.O)
    ((tensorWithComplexDerived.{u, u, u, u, u, o} X R K).obj M)
    ((tensorWithComplexDerived.{u, u, u, u, u, o} X R K).obj N) n

end AlgebraicGeometry.RingedSite

end
