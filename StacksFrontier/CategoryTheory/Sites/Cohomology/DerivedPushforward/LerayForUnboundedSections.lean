module

import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.KInjectivePredicateBridge
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.LeftTExactness
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.DerivedDirectImageAndRestriction

/-!
# Leray for unbounded derived sections along a morphism of ringed sites

Let `f : (C, O_C) ⟶ (D, O_D)` be a morphism of ringed sites given by the continuous functor
`u : D ⥤ C`, let `V` be an object of `D` and put `U = u(V)`. Stacks 0D6H asserts two things:
that `RΓ(D, -) ∘ Rf_* = RΓ(C, -)` as functors `D(O_C) ⟶ D(Γ(O_D))`, and that
`RΓ(V, -) ∘ Rf_* = RΓ(U, -)`. This file proves the second assertion for a **flat** `f`, and
isolates the single input on which it depends; the first assertion is proved from the same
input in the sibling module `LerayForUnboundedGlobalSections`.

That input is `ComputesSecond f_* (Γ(V, -))`: that `f_* I` computes `RΓ(V, -)` for every
K-injective complex `I` of `O_C`-modules. It is weaker than Stacks 093Y — that degreewise `f_*`
carries K-injective complexes to K-injective complexes — which is what discharges it for a flat
`f` and which, being a lemma about flat morphisms, is *false* in general; see the
`## Implementation notes`. Given the input, the argument is two lines of general nonsense. The
underived identity
`Γ(V, f_*M) = Γ(U, M)` holds *on the nose* — both sides are the sections of the underlying
presheaf of `M` at `op U`, since `f_*` is precomposition with `u.op` and restriction of scalars
does not move the underlying abelian group. So `RΓ(V, -) ∘ Rf_*` and `RΓ(U, -)` are right
derived functors of one and the same functor on the unbounded homotopy category of
`O_C`-modules: the comparison for `Rf_*` is invertible on a K-injective complex `I` with no
hypothesis at all (Stacks 07A5), and the comparison for `RΓ(V, -)` is invertible at `f_*I`
because `f_*I` is again K-injective. Uniqueness of right derived functors then identifies the
two.

**Why not the source's proof.** The source deduces both assertions from the composition law
`R(g ∘ f)_* = Rg_* ∘ Rf_*` of Stacks 0D6E, applied to `(C, O_C) → (D, O_D) → (pt, O_pt)` with
`pt` the punctual topos carrying `Γ(O_D)`.

*The composition law is not what is missing.* Stacks 0D6E holds in this library with nothing
left over, as
`Stacks.Cohomology.DerivedPushforwardCompositionOnTopoi.derivedPushforwardCompIsoUnconditional`
and — in the form that mentions no derived category, which is the one a proof of 0D6H would
quote — `quasiIso_mapHomotopyCategory_pushforward_of_isKInjective`
(`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPushforward/CompositionOnRingedTopoiUnconditional.lean:541` and `:445`). Neither
carries anything beyond the two `IsMorphismOfSites` witnesses that
`AlgebraicGeometry.RingedSite.Hom` already stores. Nor is the unbounded derived pullback they
rest on missing: it is
`Stacks.Cohomology.DerivedPullbackOnRingedTopoi.hasLeftDerivedFunctor_pullbackOnHomotopy`
(`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPullback/DerivedPullbackExistence.lean:130`), built from
`pullbackInvertsQuasiIso_isKFlat` (`:119`) for every morphism of ringed topoi that comes from a
morphism of sites.

*What is missing is the third morphism.* The library's Stacks 0D6E composes direct images along
morphisms of ringed topoi **presented by morphisms of sites**
(`AlgebraicGeometry.RingedToposSiteHom`), and neither sections functor is presented that way.
`Γ(V, -)` is the direct image along the functor `PUnit ⥤ D` picking `V`, and that functor is
continuous but not in general a morphism of sites:
`CategoryTheory.Functor.IsMorphismOfSites` (`StacksFrontier/CategoryTheory/Sites/MorphismOfSites.lean:58`)
demands that the sheaf pullback preserve finite limits, and it carries the one-point set to the
sheafification of the representable on `V`, which is terminal only when `V` is a final object of
the site. `Γ(D, -)` is worse: `Stacks.Cohomology.SiteModules.globalSectionsFunctor` is the limit
`M.sections` over the whole site, i.e. the direct image along the structure morphism to the
punctual topos, which is a morphism of *topoi* that no functor of sites presents unless the site
has a final object. On a ringed space the corresponding factorization is available — a continuous
map to the Sierpiński space classifies the open `V` — and it is exactly what makes the unbounded
statement Stacks 0D5W hold with no hypothesis on `f`:
`Stacks.Cohomology.DerivedSectionsLeray.isIso_lerayComparison`
(`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPushforward/LerayForDerivedSections.lean:456`),
whose geometric content is `isIso_derivedSectionsOverOpenUnit_app_pushforward` (`:365`), the
invertibility of the unit of `RΓ(V, -)` at `f_* I`. So the route through K-injectivity below is
not a stylistic preference, but the thing it stands in for is the punctual presentation of the
sections functors, not the derived pullback.

**The route that does not need the punctual topos, and what of it is built.** `Γ(V, -)` is
corepresented by `j_{V!} O_V`, so `ComputesSecond f_* (Γ(V, -))` unwinds into bijectivity of
`Hom_{K(O_D)}((j_{V!} O_V)[0], (f_* I)⟦n⟧) ⟶ Hom_{D(O_D)}((j_{V!} O_V)[0], (f_* I)⟦n⟧)`
for every `n`, which is a statement about morphisms out of a *sheaf of modules* and so one the
derived adjunction of Stacks 07A6 can act on: transpose to
`Hom_{D(O_C)}(Lf^*(j_{V!} O_V), I⟦n⟧)`, use `Lf^*(j_{V!} O_V) ≅ f^*(j_{V!} O_V)` — legitimate
because `j_{V!} O_V` is flat, Stacks 03EV, `sheafExtensionUnit_isFlat` in
`StacksFrontier/Algebra/Category/ModuleCat/Presheaf/FlatSliceExtension.lean:95` — and conclude from
K-injectivity of `I`, which makes `Hom_K(-, I⟦n⟧) = Hom_D(-, I⟦n⟧)`
(`CochainComplex.IsKInjective.Qh_map_bijective`, in this tree
`cohomologyClassRHomAddEquivOfIsKInjective`, `StacksFrontier/Homology/HomComplex/RHom.lean:243`).

The unwinding itself is now available:
`Stacks.Sites.ExtensionByZero.sectionsOverObjectHomologyAddEquiv`
(`StacksFrontier/CategoryTheory/Sites/Modules/SectionsOverObjectHomotopyCategory.lean:90`)
identifies `Hⁿ(Γ(U, M^•))` with `Hom_{K(O)}((j_{U!} O_U)[0], M^•⟦n⟧)`, out of Stacks 0G1V in
the additive form `coyonedaExtensionByZeroUnitIso`
(`StacksFrontier/CategoryTheory/Sites/Modules/SectionsOverObjectCorepresentable.lean:112`) and the generic
`CochainComplex.HomComplex.homComplexSingleIsoCoyonedaComplex`
(`StacksFrontier/Algebra/Homology/HomotopyCategory/HomComplexFromSingle.lean:70`). So is the
geometric step: `Stacks.Sites.ExtensionByZero.pullbackToposExtensionByZeroUnitIso`
(`StacksFrontier/CategoryTheory/Sites/Modules/PullbackOfExtensionByZeroUnit.lean:114`) is
`f^*(j_{V!} O_V) ≅ j_{U!} O_U`, both sides corepresenting `Γ(U, -)`, built over the additive
transposition `CategoryTheory.Adjunction.coyonedaAddIso` (`:65`).

**The chase is done.** `Stacks.Cohomology.DerivedPullbackOnRingedTopoi.`
`bijective_qh_map_pushforward_of_isKInjective`
(`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPushforward/HomotopyHomIntoPushforwardOfKInjective.lean:148`) is exactly the
displayed bijectivity, for any `P` at which the Stacks 06YY comparison `Lf^* ⟶ f^*` is
invertible — which `(j_{V!} O_V)[0]` is, being a bounded above complex of flat modules
(`Stacks.Cohomology.DerivedPullbackOnRingedTopoi.isIso_derivedPullbackComparison_app_boundedAbove`,
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPullback/DerivedPullbackExistence.lean:165`, with the flatness of `j_{V!} O_V` from
Stacks 03EV). The two identifications of both sides with `Hom(f^* P, I)` agree by
`derivedAdjunction_homEquiv_symm_qh_map` (`:89`), which is Stacks 0FPI
(`Stacks.Cohomology.DerivedPullbackOnRingedTopoi.derivedAdjunction_counit_fac`,
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPushforward/OrdinaryAndDerivedCounit.lean:141`) applied at `I`, preceded by the
naturality of the comparison at the morphism — so the inverse of the comparison is never
computed, it living on the *counit* side.

**And the clause is closed.** `Stacks.Cohomology.LerayUnbounded.`
`computesSecond_pushforwardTopos_sectionsOverObject`
(`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPushforward/LerayForUnboundedSectionsGeneral.lean:192`) discharges
`ComputesSecond f_* (Γ(V, -))` for every morphism of ringed sites, so
`derivedSectionsOverObjectPushforwardIsoGeneral` (`:235`) is this file's conclusion with no
flatness, and it is where the `@[stacks 0D6H]` tag for this clause lives. The three steps
between the chase and the clause are formal, and each is a declaration of its own:

1. the criterion turning `IsIso ((totalDerivedUnit (Γ(V, -))).app (f_* I))` into
   `QuasiIso (Γ(V, s))` for a K-injective resolution `s : f_* I ⟶ J` — the naturality square of
   the comparison at `s`, with `Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective`
   (`StacksFrontier/CategoryTheory/Sites/Cohomology/Localization/RestrictionOfModules.lean:154`) at `J` and
   `Stacks.Cohomology.Localization.enoughKInjectives` (`:150`) producing `s`;
2. `CochainComplex.HomComplex.homComplexSingleIsoCoyonedaComplex_naturality` and
   `isIso_homologyMap_coyonedaComplexMap`
   (`StacksFrontier/Algebra/Homology/HomotopyCategory/HomComplexFromSinglePostcomp.lean:58`
   and `:69`), which feed `Stacks.Injectives.isIso_homologyMap_homComplexPostcomp`
   (`StacksFrontier/Homology/Injectives/Ext/SpectralSequenceIntoFunctoriality.lean:131`);
3. the shift bookkeeping, `Stacks.Cohomology.DerivedPullbackOnRingedTopoi.pushforwardShiftIso`
   and `bijective_postcomp_quotient_shift_of_isKInjective`
   (`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPushforward/PostcompIntoPushforwardOfKInjective.lean:83` and `:112`).

The global-sections clause is covered by the same three steps, in
`LerayForUnboundedGlobalSectionsGeneral.lean`, with `Γ(D, -)` corepresented by the structure
sheaf itself: `derivedGlobalSectionsPushforwardIsoGeneral`.

**The route that does not need the punctual topos, and what of it is built.** `Γ(V, -)` is
corepresented by `j_{V!} O_V`, so `ComputesSecond f_* (Γ(V, -))` unwinds into bijectivity of
`Hom_{K(O_D)}((j_{V!} O_V)[0], (f_* I)⟦n⟧) ⟶ Hom_{D(O_D)}((j_{V!} O_V)[0], (f_* I)⟦n⟧)`
for every `n`, which is a statement about morphisms out of a *sheaf of modules* and so one the
derived adjunction of Stacks 07A6 can act on: transpose to
`Hom_{D(O_C)}(Lf^*(j_{V!} O_V), I⟦n⟧)`, use `Lf^*(j_{V!} O_V) ≅ f^*(j_{V!} O_V)` — legitimate
because `j_{V!} O_V` is flat, Stacks 03EV, `sheafExtensionUnit_isFlat` in
`StacksFrontier/Algebra/Category/ModuleCat/Presheaf/FlatSliceExtension.lean:95` — and conclude from
K-injectivity of `I`, which makes `Hom_K(-, I⟦n⟧) = Hom_D(-, I⟦n⟧)`
(`CochainComplex.IsKInjective.Qh_map_bijective`, in this tree
`cohomologyClassRHomAddEquivOfIsKInjective`, `StacksFrontier/Homology/HomComplex/RHom.lean:243`).

The unwinding itself is now available:
`Stacks.Sites.ExtensionByZero.sectionsOverObjectHomologyAddEquiv`
(`StacksFrontier/CategoryTheory/Sites/Modules/SectionsOverObjectHomotopyCategory.lean:90`)
identifies `Hⁿ(Γ(U, M^•))` with `Hom_{K(O)}((j_{U!} O_U)[0], M^•⟦n⟧)`, out of Stacks 0G1V in
the additive form `coyonedaExtensionByZeroUnitIso`
(`StacksFrontier/CategoryTheory/Sites/Modules/SectionsOverObjectCorepresentable.lean:112`) and the generic
`CochainComplex.HomComplex.homComplexSingleIsoCoyonedaComplex`
(`StacksFrontier/Algebra/Homology/HomotopyCategory/HomComplexFromSingle.lean:70`). So is the
geometric step: `Stacks.Sites.ExtensionByZero.pullbackToposExtensionByZeroUnitIso`
(`StacksFrontier/CategoryTheory/Sites/Modules/PullbackOfExtensionByZeroUnit.lean:114`) is
`f^*(j_{V!} O_V) ≅ j_{U!} O_U`, both sides corepresenting `Γ(U, -)`, built over the additive
transposition `CategoryTheory.Adjunction.coyonedaAddIso` (`:65`).

**The chase is done.** `Stacks.Cohomology.DerivedPullbackOnRingedTopoi.`
`bijective_qh_map_pushforward_of_isKInjective`
(`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPushforward/HomotopyHomIntoPushforwardOfKInjective.lean:148`) is exactly the
displayed bijectivity, for any `P` at which the Stacks 06YY comparison `Lf^* ⟶ f^*` is
invertible — which `(j_{V!} O_V)[0]` is, being a bounded above complex of flat modules
(`Stacks.Cohomology.DerivedPullbackOnRingedTopoi.isIso_derivedPullbackComparison_app_boundedAbove`,
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPullback/DerivedPullbackExistence.lean:165`, with the flatness of `j_{V!} O_V` from
Stacks 03EV). The two identifications of both sides with `Hom(f^* P, I)` agree by
`derivedAdjunction_homEquiv_symm_qh_map` (`:89`), which is Stacks 0FPI
(`Stacks.Cohomology.DerivedPullbackOnRingedTopoi.derivedAdjunction_counit_fac`,
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPushforward/OrdinaryAndDerivedCounit.lean:141`) applied at `I`, preceded by the
naturality of the comparison at the morphism — so the inverse of the comparison is never
computed, it living on the *counit* side.

**What the general clause still needs is plumbing, and it is enumerable.** Three steps, none of
them mathematical content:

1. The criterion turning `IsIso ((totalDerivedUnit (Γ(V, -))).app (f_* I))` into
   `QuasiIso (Γ(V, -) applied degreewise to a K-injective resolution s : f_* I ⟶ J)`. The
   generic form is `Stacks.SmallDerivedCategory.isIso_rightDerivedUnit_app_quotient_iff`
   (`StacksFrontier/AlgebraicGeometry/AffineVanishingUnbounded.lean:130`), whose `hA` is
   `Stacks.Cohomology.Localization.enoughKInjectives`
   (`StacksFrontier/CategoryTheory/Sites/Cohomology/Localization/RestrictionOfModules.lean:150`).
2. Naturality of `homComplexSingleIsoCoyonedaComplex` in the second variable, against
   `homComplexPostcomp` (`StacksFrontier/CategoryTheory/Sites/Cohomology/Cech/RightDerivedSheafToPresheaf.lean:89`). That
   feeds `isIso_homologyMap_homComplexPostcomp`
   (`StacksFrontier/Homology/Injectives/Ext/SpectralSequenceIntoFunctoriality.lean:131`), which
   already turns bijectivity of postcomposition in the homotopy category into invertibility of
   the homology map — i.e. into step 1's `QuasiIso`.
3. The shift bookkeeping `(f_* I)⟦n⟧ ≅ f_*(I⟦n⟧)`, so that the `n`-th instance of the
   bijectivity above is an instance of `bijective_qh_map_pushforward_of_isKInjective` at the
   K-injective `I⟦n⟧`. This is
   `(f_*.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso n`, whose components are
   identities (`Functor.mapHomologicalComplex_commShiftIso_hom_app_f`).

## Main results

All in the namespace `Stacks.Cohomology.LerayUnbounded`.

* `ComputesSecond` and `derivedCompIsoOfComputes`: the general brick, over the weakest
  hypothesis it admits. If `F ⋙ G ≅ H` and the comparison of `RG` is invertible at the
  degreewise image under `F` of every K-injective complex, then `RF ⋙ RG ≅ RH`.
* `derivedCompIso`: the same with `ComputesSecond` discharged from `F` carrying K-injective
  complexes to K-injective complexes, which is how `computesSecond_of_isKInjective` supplies it.
  Both results below are one application of these.
* `derivedSectionsOverObjectIsoSlice`: **Stacks 0D6F at the level of functors** — derived
  sections over `U` are derived sections on `C/U` of the derived restriction. The tag already
  sits on `Stacks.Cohomology.Localization.cohomologyOverObjectIsoRestriction`, which is this
  isomorphism whiskered with a homology functor.
* `pushforwardTopos_comp_sectionsOverObject`: the underived identity `Γ(V, f_*M) = Γ(U, M)`,
  as an equality of functors.
* `derivedSectionsOverObjectPushforwardIso`: `RΓ(V, -) ∘ Rf_* ≅ RΓ(U, -)`, over the weakest
  hypothesis there is — that `f_* I` computes `RΓ(V, -)` for K-injective `I`, which is the
  content of the clause itself and is true for every morphism of ringed sites — and
  `derivedSectionsOverObjectPushforwardIsoOfKInjective`, the same over the stronger named
  hypothesis `h093Y` that degreewise `f_*` preserves K-injectivity.
* `isKInjective_pushforwardTopos_of_exact_leftAdjoint` and
  `isKInjective_pushforwardTopos_of_flat`: that hypothesis for a morphism of ringed sites whose
  direct image has an exact left adjoint, and in particular for a flat one.
* `derivedSectionsOverObjectPushforwardIsoOfFlat`: the conclusion, unconditionally, for a flat
  morphism of ringed sites.

## Implementation notes

**What a general proof must supply, and what it must not be asked to supply.** The hypothesis
`h093Y` cannot be discharged for a general morphism of ringed sites: Stacks 093Y
(`sites-cohomology-lemma-K-injective-flat`) is a statement *about a flat
morphism* of ringed topoi, proved from the exactness of `f^*`, and it is false for a general
one — `f_* I` K-injective means `Hom_{K(O_C)}(f^*F, I) = 0` for every acyclic `F`, which for an
additive `f^*` forces `f^*` to be exact. So no amount of work discharges `h093Y` in general, and
the conditional statement over `h093Y` cannot reach the general case.

The hypothesis the statements below now carry is `ComputesSecond f_* (Γ(V, -))`: that `f_* I`
computes `RΓ(V, -)` for every K-injective `I`. That is strictly weaker than `h093Y`
(`computesSecond_of_isKInjective`), it is *exactly* the content of the clause, and it **is**
true in general — it is what the source's route through Stacks 0D6E delivers. The flat case
factors through `h093Y`; see `derivedSectionsOverObjectPushforwardIsoOfKInjective`.

The global-sections clause of Stacks 0D6H is proved in the sibling module
`StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.LerayForUnboundedGlobalSections`,
as `derivedGlobalSectionsPushforwardIso` and, with flatness discharging `h093Y`,
`derivedGlobalSectionsPushforwardIsoOfFlat`; its `ComputesSecond` hypothesis is discharged for
an arbitrary morphism of ringed sites in `LerayForUnboundedGlobalSectionsGeneral`, giving
`derivedGlobalSectionsPushforwardIsoGeneral`, which carries the tag for that clause. Note that
the two sides are modules over different
rings, so the comparison carries a restriction of scalars along `Γ(O_D) ⟶ Γ(O_C)` and is an
isomorphism rather than the `rfl` of `pushforwardTopos_comp_sectionsOverObject`; the derived half
is then one application of `derivedCompIso` with `G` taken to be global sections.

The module-valued global-sections functor
is `Stacks.Cohomology.SiteModules.globalSectionsFunctor` in
`CategoryTheory/Sites/Cohomology/Modules/CohomologyOfModules.lean:153`, and the ring map and the
whole underived comparison are proved, as
`Stacks.Cohomology.SiteModules.globalSectionsRingHom` and `globalSectionsPushforwardIso` in
`CategoryTheory/Sites/Cohomology/Modules/GlobalSectionsAndPushforward.lean:443` and `:579`. The
bridge between the two presentations of the pushforward --
`RingedToposHom` there, `RingedToposSiteHom.pushforwardTopos` here -- is
`AlgebraicGeometry.RingedSite.Hom.pushforwardModulesToposIso`
(`CategoryTheory/Sites/Modules/RingedToposModulesPullbackTopos.lean:158`); the two
presentations only have to be glued.

The three universes of the ringed sites are collapsed, as they are in
`AlgebraicGeometry.RingedSite.Hom` and throughout the derived development. The flat case also
asks for `HasWeakSheafify` and `WEqualsLocallyBijective` on the source site, because
`AlgebraicGeometry.RingedToposSiteHom.pullbackTopos` — the functor whose left exactness *is*
flatness, Stacks 03DJ — is only defined under them;
`isKInjective_pushforwardTopos_of_exact_leftAdjoint` is the form free of that side condition.

## References

* [Stacks Project, Tag 0D6H](https://stacks.math.columbia.edu/tag/0D6H)
* [Stacks Project, Tag 0D6F](https://stacks.math.columbia.edu/tag/0D6F)
* [Stacks Project, Tag 0D6G](https://stacks.math.columbia.edu/tag/0D6G)
* [Stacks Project, Tag 093Y](https://stacks.math.columbia.edu/tag/093Y)
* [Stacks Project, Tag 03DJ](https://stacks.math.columbia.edu/tag/03DJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.Cohomology.Localization

namespace Stacks.Cohomology.LerayUnbounded

universe u v w u₁ u₂ u₃ v₁ v₂ v₃ wA wB wC wGB

section General

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [IsGrothendieckAbelian.{w} A]
  [HasDerivedCategory.{wA} A] {B : Type u₂} [Category.{v₂} B] [Abelian B]
  [IsGrothendieckAbelian.{wGB} B] [HasDerivedCategory.{wB} B] {C : Type u₃} [Category.{v₃} C]
  [Abelian C] [HasDerivedCategory.{wC} C]

/-- The canonical comparison exhibiting `DerivedFunctor.totalRightDerived F` as a right derived
functor of degreewise `F` followed by localization. -/
noncomputable abbrev totalDerivedUnit (F : A ⥤ B) [F.Additive] :
    F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ DerivedFunctor.totalRightDerived F :=
  (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerivedUnit
    DerivedCategory.Qh (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))

/-- The canonical comparison from the two degreewise functors into `RF ⋙ RG`: the unit of `RG`
whiskered with degreewise `F`, after the unit of `RF` whiskered with `RG`. -/
noncomputable def derivedCompUnit (F : A ⥤ B) [F.Additive] (G : B ⥤ C) [G.Additive] :
    F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) ⟶
      DerivedCategory.Qh ⋙
        (DerivedFunctor.totalRightDerived F ⋙ DerivedFunctor.totalRightDerived G) :=
  Functor.whiskerLeft (F.mapHomotopyCategory (ComplexShape.up ℤ)) (totalDerivedUnit G) ≫
    Functor.whiskerRight (totalDerivedUnit F) (DerivedFunctor.totalRightDerived G)

/-- **`RG` is computed at `F I`** — the hypothesis `derivedCompIsoOfComputes` runs on. It says
that the comparison `G I' ⟶ RG I'` of the second functor is invertible at `I' = F I` for every
K-injective `I`, i.e. that the degreewise image of a K-injective complex under `F` computes `RG`.

This is strictly weaker than asking `F I` to be K-injective, and it is the hypothesis the
composite genuinely needs: the uniqueness argument only ever evaluates the comparison of `RG` at
complexes of the form `F I`. -/
abbrev ComputesSecond (F : A ⥤ B) [F.Additive] (G : B ⥤ C) [G.Additive] : Prop :=
  ∀ (I : CochainComplex A ℤ), I.IsKInjective →
    IsIso ((totalDerivedUnit G).app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)))

/-- Under `ComputesSecond F G`, the composite `RF ⋙ RG` is a right derived functor of the
composite of the two degreewise functors: the comparison for `RF` is invertible on a K-injective
complex `I` with no hypothesis, and the one for `RG` is invertible at `F I` by assumption. -/
theorem isRightDerivedFunctor_derivedCompUnit_of_computes (F : A ⥤ B) [F.Additive] (G : B ⥤ C)
    [G.Additive] (hG : ComputesSecond F G) :
    (DerivedFunctor.totalRightDerived F ⋙
        DerivedFunctor.totalRightDerived G).IsRightDerivedFunctor (derivedCompUnit F G)
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) :=
  isRightDerivedFunctor_comp_of_kInjectives _ _ _ _ _ _
    (fun I _ => Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective _ _ _ I)
    (fun I hI => hG I hI)

omit [IsGrothendieckAbelian.{w, v₁, u₁} A] [HasDerivedCategory A] in
/-- Preserving K-injectivity is one way to have `ComputesSecond F G`: the comparison of any right
derived functor is invertible on a K-injective complex. -/
theorem computesSecond_of_isKInjective (F : A ⥤ B) [F.Additive] (G : B ⥤ C) [G.Additive]
    (hF : ∀ (I : CochainComplex A ℤ), I.IsKInjective →
      CochainComplex.IsKInjective ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) :
    ComputesSecond F G := fun I hI => by
  have := hF I hI
  exact Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective _ _ _
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)

/-- If degreewise `F` preserves K-injectivity then `RF ⋙ RG` is a right derived functor of the
composite of the two degreewise functors. The comparison for `RF` is invertible on a K-injective
complex `I`, and the one for `RG` is invertible at `F I`, which is K-injective by hypothesis. -/
theorem isRightDerivedFunctor_derivedCompUnit (F : A ⥤ B) [F.Additive] (G : B ⥤ C) [G.Additive]
    (hF : ∀ (I : CochainComplex A ℤ), I.IsKInjective →
      CochainComplex.IsKInjective ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) :
    (DerivedFunctor.totalRightDerived F ⋙
        DerivedFunctor.totalRightDerived G).IsRightDerivedFunctor (derivedCompUnit F G)
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) :=
  isRightDerivedFunctor_derivedCompUnit_of_computes F G (computesSecond_of_isKInjective F G hF)

/-- **The brick, over the weakest hypothesis.** If `e : F ⋙ G ≅ H` and the comparison of `RG` is
invertible at the degreewise image under `F` of every K-injective complex, then the iterated
total right derived functor `RF ⋙ RG` is canonically isomorphic to `RH`. Both are right derived
functors of the same functor on the unbounded homotopy category, and a right derived functor is
unique up to a canonical isomorphism.

`derivedCompIso` is this with `ComputesSecond F G` discharged from preservation of
K-injectivity. The weaker form is what a general statement needs, because preservation of
K-injectivity by a direct image is Stacks 093Y, which is *false* without flatness, while
`ComputesSecond` is the conclusion content itself and holds in general. -/
noncomputable def derivedCompIsoOfComputes (F : A ⥤ B) [F.Additive] (G : B ⥤ C) [G.Additive]
    (H : A ⥤ C) [H.Additive] (e : F ⋙ G ≅ H) (hG : ComputesSecond F G) :
    DerivedFunctor.totalRightDerived F ⋙ DerivedFunctor.totalRightDerived G ≅
      DerivedFunctor.totalRightDerived H :=
  letI := isRightDerivedFunctor_derivedCompUnit_of_computes F G hG
  Functor.rightDerivedNatIso _ _ (derivedCompUnit F G) (totalDerivedUnit H)
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
    (Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)) DerivedCategory.Qh)

/-- **The brick.** If degreewise `F` carries K-injective complexes to K-injective complexes and
`e : F ⋙ G ≅ H`, then the iterated total right derived functor `RF ⋙ RG` is canonically
isomorphic to `RH`. Both are right derived functors of the same functor on the unbounded
homotopy category, and a right derived functor is unique up to a canonical isomorphism. -/
noncomputable def derivedCompIso (F : A ⥤ B) [F.Additive] (G : B ⥤ C) [G.Additive]
    (H : A ⥤ C) [H.Additive] (e : F ⋙ G ≅ H)
    (hF : ∀ (I : CochainComplex A ℤ), I.IsKInjective →
      CochainComplex.IsKInjective ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) :
    DerivedFunctor.totalRightDerived F ⋙ DerivedFunctor.totalRightDerived G ≅
      DerivedFunctor.totalRightDerived H :=
  derivedCompIsoOfComputes F G H e (computesSecond_of_isKInjective F G hF)

end General

section RingedSite

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

variable {X Y : RingedSite.{u, u, u}} (f : RingedSite.Hom X Y) (V : Y.C)

/-- **Stacks 0D6F, at the level of functors.** Unbounded derived sections over an object `U` of
a ringed site are the unbounded derived sections on the localized site `C/U` of the derived
restriction to `C/U`. Restriction is exact and carries K-injective complexes to K-injective
complexes (Stacks 08FI), and sections over `U` are global sections on `C/U` already before
deriving (`Stacks.Cohomology.Localization.sectionsRestrictionIso`).

`Stacks.Cohomology.Localization.cohomologyOverObjectIsoRestriction`, which carries the tag, is a
comparison of this shape whiskered with a homology functor: it constructs the functor-level
isomorphism inside its own proof and does not export it, which is why it is rebuilt here. -/
noncomputable def derivedSectionsOverObjectIsoSlice (Z : RingedSite.{u, u, u}) (U : Z.C) :
    derivedSectionsOverObject Z U ≅ derivedRestriction Z U ⋙ derivedSectionsOnSlice Z U :=
  (derivedCompIso (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) U)
    (sectionsOnSlice Z U)
    (sectionsOverObject Z U) (sectionsRestrictionIso Z U).symm
    (fun I hI =>
      @isKInjective_over _ _ Z.J (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) U I hI)).symm

attribute [local instance] AlgebraicGeometry.RingedSite.Hom.pushforwardTopos_additive

/-- Sections over `V` of the direct image along a morphism of ringed sites form an additive
functor. -/
local instance additive_pushforwardTopos_comp_sectionsOverObject :
    (f.toRingedToposSiteHom.pushforwardTopos ⋙ sectionsOverObject Y V).Additive where
  map_add := by intros; rfl

/-- **The underived identity behind Stacks 0D6H:** sections over `V` of the direct image of a
sheaf of modules along a morphism of ringed sites are the sections over `u(V)` of that sheaf.
As in the source this is an equality of functors, not merely an isomorphism: the direct image
is precomposition with `u.op`, and restricting the scalars along `f^♯` leaves the underlying
abelian group alone. -/
theorem pushforwardTopos_comp_sectionsOverObject :
    f.toRingedToposSiteHom.pushforwardTopos ⋙ sectionsOverObject Y V =
      sectionsOverObject X (f.u.obj V) := rfl

/-- **Stacks 0D6H, the clause on sections over an object, over the weakest hypothesis there is.**
For a morphism of ringed sites `f : (C, O_C) ⟶ (D, O_D)` given by the continuous functor
`u : D ⥤ C`, an object `V` of `D` and `U = u(V)`, the unbounded derived sections over `V` of the
unbounded derived direct image are the unbounded derived sections over `U`, as soon as `f_* I`
computes `RΓ(V, -)` for every K-injective complex `I` of `O_C`-modules.

That hypothesis — `ComputesSecond f_* (Γ(V, -))`, spelled out — is *exactly* the content of the
clause and nothing more, and it is **true for every morphism of ringed sites**: it is what the
source's route, Stacks 0D6E applied to `(C, O_C) → (D, O_D) → (pt, O_pt)`, delivers. It is
strictly weaker than the preservation of K-injectivity by `f_*`, which is Stacks 093Y and is a
lemma *about flat morphisms* — see `derivedSectionsOverObjectPushforwardIsoOfKInjective` for the
factorisation through it. Whoever supplies this hypothesis in general obtains the untagged,
unrestricted Stacks 0D6H by one application of this definition; the stronger hypothesis that `f_*`
preserves K-injectivity (Stacks 093Y) cannot be supplied in general, being false. -/
noncomputable def derivedSectionsOverObjectPushforwardIso
    (hcomputes :
      letI : @Functor.Additive (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
          AddCommGrpCat.{u} SheafOfModules.instCategory _ _ _ (sectionsOverObject Y V) :=
        additive_sectionsOverObject Y V
      ComputesSecond f.toRingedToposSiteHom.pushforwardTopos (sectionsOverObject Y V)) :
    derivedPushforward.{u} f.toRingedToposSiteHom ⋙ derivedSectionsOverObject Y V ≅
      derivedSectionsOverObject X (f.u.obj V) :=
  letI : @Functor.Additive (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      AddCommGrpCat.{u} SheafOfModules.instCategory _ _ _ (sectionsOverObject Y V) :=
    additive_sectionsOverObject Y V
  letI : @Functor.Additive (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      AddCommGrpCat.{u} SheafOfModules.instCategory _ _ _ (sectionsOverObject X (f.u.obj V)) :=
    additive_sectionsOverObject X (f.u.obj V)
  derivedCompIsoOfComputes f.toRingedToposSiteHom.pushforwardTopos (sectionsOverObject Y V)
    (sectionsOverObject X (f.u.obj V))
    (eqToIso (pushforwardTopos_comp_sectionsOverObject f V)) hcomputes

/-- The clause on sections over an object, over the stronger hypothesis `h093Y` that degreewise
direct image preserves K-injectivity.

No tag: `h093Y` is not a hypothesis of the source, which gets the same conclusion from the
composition law of Stacks 0D6E. See `derivedSectionsOverObjectPushforwardIsoOfFlat` for the
case in which `h093Y` is discharged, and `derivedSectionsOverObjectPushforwardIso` for the
weakest hypothesis under which the conclusion holds. -/
noncomputable def derivedSectionsOverObjectPushforwardIsoOfKInjective
    (h093Y : ∀ (I : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ), I.IsKInjective →
      CochainComplex.IsKInjective
        ((f.toRingedToposSiteHom.pushforwardTopos.mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I)) :
    derivedPushforward.{u} f.toRingedToposSiteHom ⋙ derivedSectionsOverObject Y V ≅
      derivedSectionsOverObject X (f.u.obj V) :=
  letI : @Functor.Additive (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      AddCommGrpCat.{u} SheafOfModules.instCategory _ _ _ (sectionsOverObject Y V) :=
    additive_sectionsOverObject Y V
  derivedSectionsOverObjectPushforwardIso f V
    (computesSecond_of_isKInjective f.toRingedToposSiteHom.pushforwardTopos
      (sectionsOverObject Y V) h093Y)

/-- **Stacks 093Y** for a morphism of ringed sites, from an exact left adjoint: if the direct
image of sheaves of modules along `f` has an exact left adjoint, then degreewise direct image
carries K-injective complexes of `O_C`-modules to K-injective complexes of `O_D`-modules. -/
theorem isKInjective_pushforwardTopos_of_exact_leftAdjoint
    (L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⥤
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    [L.Additive]
    (adj : L ⊣ f.toRingedToposSiteHom.pushforwardTopos)
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hI : I.IsKInjective) :
    CochainComplex.IsKInjective
      ((f.toRingedToposSiteHom.pushforwardTopos.mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I) :=
  (Stacks.Cohomology.isKInjectiveHomotopyCategory_iff_isKInjective _).mp
    (rightAdjoint_preserves_isKInjective f.toRingedToposSiteHom.pushforwardTopos L adj I
      ((Stacks.Cohomology.isKInjectiveHomotopyCategory_iff_isKInjective I).mpr hI))

/-- The inverse image of sheaves of modules along a morphism of ringed sites is additive, being
a left adjoint of the additive direct image. Instantiated here for the same reason as
`AlgebraicGeometry.RingedSite.Hom.pushforwardTopos_additive`. -/
local instance additive_pullbackTopos
    [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] :
    f.toRingedToposSiteHom.pullbackTopos.Additive :=
  Adjunction.left_adjoint_additive
    (RingedToposSiteHom.pullbackPushforwardAdjunctionTopos f.toRingedToposSiteHom)

/-- **Stacks 093Y** for a flat morphism of ringed sites: if `f^*` is left exact — that is, `f`
is flat in the sense of Stacks 03DJ, right exactness being automatic for a left adjoint — then
degreewise direct image preserves K-injectivity. -/
@[sga "4 V 4.9" "more general"]
theorem isKInjective_pushforwardTopos_of_flat
    [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [PreservesFiniteLimits f.toRingedToposSiteHom.pullbackTopos]
    (I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hI : I.IsKInjective) :
    CochainComplex.IsKInjective
      ((f.toRingedToposSiteHom.pushforwardTopos.mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I) :=
  have : PreservesColimitsOfSize.{0, 0} f.toRingedToposSiteHom.pullbackTopos :=
    (RingedToposSiteHom.pullbackPushforwardAdjunctionTopos
      f.toRingedToposSiteHom).leftAdjoint_preservesColimits
  isKInjective_pushforwardTopos_of_exact_leftAdjoint f _
    (RingedToposSiteHom.pullbackPushforwardAdjunctionTopos f.toRingedToposSiteHom) I hI

/-- **Stacks 0D6H for a flat morphism of ringed sites, the clause on sections over an object.**
Let `f : (C, O_C) ⟶ (D, O_D)` be a flat morphism of ringed sites given by the continuous functor
`u : D ⥤ C`, let `V` be an object of `D` and put `U = u(V)`. Then
`RΓ(V, -) ∘ Rf_* = RΓ(U, -)` as functors `D(O_C) ⟶ D(Ab)`.

Flatness is the hypothesis `PreservesFiniteLimits` on `f^*` of Stacks 03DJ, and it is a genuine
restriction: the source assumes no flatness, deducing the lemma instead from the composition
law of Stacks 0D6E applied to `(C, O_C) → (D, O_D) → (pt, O_pt)`. That composition law is
available unconditionally; what is not is the presentation of `Γ(V, -)` as a direct image along
a morphism of ringed *sites* to a punctual one, which is what the third morphism of the source's
chain would be — see `**Why not the source's proof**` in the module docstring above.

**No tag: this clause is now covered in general.** The flatness here is a genuine restriction
and the tag is carried by
`Stacks.Cohomology.LerayUnbounded.derivedSectionsOverObjectPushforwardIsoGeneral`
(`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPushforward/LerayForUnboundedSectionsGeneral.lean`), which is the same conclusion
for an arbitrary morphism of ringed sites. This flat form is kept because it is the one whose
hypothesis is an instance — `PreservesFiniteLimits` on `f^*` — and so the one instance search
finds without an argument. The source's other clause, the one about global sections into
`D(Γ(O_D))`, is
`Stacks.Cohomology.LerayUnbounded.derivedGlobalSectionsPushforwardIsoGeneral` in the sibling
module `LerayForUnboundedGlobalSectionsGeneral`. -/
noncomputable def derivedSectionsOverObjectPushforwardIsoOfFlat
    [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [PreservesFiniteLimits f.toRingedToposSiteHom.pullbackTopos] :
    derivedPushforward.{u} f.toRingedToposSiteHom ⋙ derivedSectionsOverObject Y V ≅
      derivedSectionsOverObject X (f.u.obj V) :=
  derivedSectionsOverObjectPushforwardIsoOfKInjective f V
    (isKInjective_pushforwardTopos_of_flat f)

end RingedSite

end Stacks.Cohomology.LerayUnbounded

end
