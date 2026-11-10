module

import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.LerayForUnboundedSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.GlobalSectionsAndPushforward
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposModulesPullbackTopos

/-!
# Leray for unbounded derived global sections along a morphism of ringed sites

Let `f : (C, O_C) ⟶ (D, O_D)` be a morphism of ringed sites, given by the continuous functor
`u : D ⥤ C`. Stacks 0D6H asserts two things: that `RΓ(D, -) ∘ Rf_* = RΓ(C, -)` as functors
`D(O_C) ⟶ D(Γ(O_D))`, and that `RΓ(V, -) ∘ Rf_* = RΓ(u(V), -)` for an object `V` of `D`. The
second assertion is
`Stacks.Cohomology.LerayUnbounded.derivedSectionsOverObjectPushforwardIsoGeneral`; this file
proves the first, the **global-sections clause**, for a flat `f`, and isolates the single input
on which it depends. That input is then discharged for an arbitrary morphism of ringed sites in
`LerayForUnboundedGlobalSectionsGeneral.lean`, where the tag for this clause lives.

That input is the same as for the other clause: `ComputesSecond f_* (Γ(D, -))`, that `f_* I`
computes `RΓ(D, -)` for every K-injective complex `I` of `O_C`-modules. It is weaker than
Stacks 093Y — that degreewise `f_*` carries K-injective complexes to K-injective complexes —
which discharges it for a flat `f` and which is, being a lemma about flat morphisms, false in
general; see the `## Implementation notes` of `LerayForUnboundedSections.lean`. Given the input,
the clause is one application of the brick
`Stacks.Cohomology.LerayUnbounded.derivedCompIsoOfComputes` to the underived identity, with the
global sections functor in the role of the second functor.

**The two sides are modules over different rings.** Unlike the clause on sections over an
object, where `Γ(V, f_*M) = Γ(u(V), M)` holds on the nose, the underived identity here is not an
equality: `Γ(D, f_*M)` is a module over `Γ(O_D)` while `Γ(C, M)` is a module over `Γ(O_C)`. The
identity of functors into `D(Γ(O_D))` that the source states therefore reads the right hand side
through restriction of scalars along the ring map `Γ(O_D) ⟶ Γ(O_C)` induced by `O_D ⟶ f_* O_C`.
Both the ring map and the underived comparison are already in the library, for a morphism of
ringed topoi: they are `Stacks.Cohomology.SiteModules.globalSectionsRingHom` and
`Stacks.Cohomology.SiteModules.globalSectionsPushforwardIso`, and the comparison is not a
computation with sections — the pushforward along a morphism of topoi is an abstract right
adjoint, so `Γ(D, f_*M)` has no description in terms of sections of `M` — but the adjunction
bijection between maps out of the free module of rank one on either side. What this file adds is
the passage to a morphism of ringed *sites*, along
`AlgebraicGeometry.RingedSite.Hom.pushforwardModulesToposIso`, which identifies the pushforward
of the modules development with Mathlib's pushforward along `u`, the one the derived development
is stated over.

## Main results

All in the namespace `Stacks.Cohomology.LerayUnbounded`.

* `siteGlobalSectionsRingHom`: the ring map `Γ(O_D) ⟶ Γ(O_C)` of a morphism of ringed sites,
  namely the one of the associated morphism of ringed topoi.
* `derivedGlobalSections`: unbounded derived global sections `RΓ(Z, -) : D(O_Z) ⟶ D(Γ(O_Z))` on
  a ringed site, and `derivedGlobalSectionsRestricted`, the derived global sections of the source
  read in `D(Γ(O_D))`, which is the right hand side of the clause.
* `pushforwardToposCompGlobalSectionsIso`: the underived comparison
  `Γ(D, f_*M) ≅ Γ(C, M)` of `Γ(O_D)`-modules, as an isomorphism of functors.
* `derivedGlobalSectionsPushforwardIso`: **Stacks 0D6H, the global-sections clause**, over the
  weakest hypothesis there is — that `f_* I` computes `RΓ(D, -)` for K-injective `I`, which is
  the content of the clause itself and is true for every morphism of ringed sites — and
  `derivedGlobalSectionsPushforwardIsoOfKInjective`, the same over the stronger named hypothesis
  `h093Y` that degreewise direct image preserves K-injectivity.
* `derivedGlobalSectionsPushforwardIsoOfFlat`: the conclusion, unconditionally, for a flat
  morphism of ringed sites. The conclusion for an *arbitrary* morphism of ringed sites is
  `derivedGlobalSectionsPushforwardIsoGeneral` of
  `LerayForUnboundedGlobalSectionsGeneral.lean`, which is this file's
  `derivedGlobalSectionsPushforwardIso` with its hypothesis discharged, and which carries the
  tag.

## Implementation notes

As in `LerayForUnboundedSections.lean`, the hypothesis is carried as an explicit argument
rather than a class, and it is `ComputesSecond f_* (Γ(D, -))` rather than `h093Y`: Stacks 093Y
is a lemma about *flat* morphisms and is false for a general one, so the older spelling of this
paragraph — that whoever discharges Stacks 093Y in general obtains the unrestricted clause — was
pointing at a route that does not exist. `ComputesSecond` is strictly weaker, is exactly the
content of the clause, and is what the source's route through Stacks 0D6E delivers. It is
discharged for every morphism of ringed sites by
`Stacks.Cohomology.LerayUnbounded.computesSecond_pushforwardTopos_globalSections`
(`Cohomology/DerivedPushforward/LerayForUnboundedGlobalSectionsGeneral.lean`),
which is why the tag no longer sits on the flat case.

That composition law is **not** what the source's route is blocked on here. Stacks 0D6E holds
unconditionally, as
`Stacks.Cohomology.DerivedPushforwardCompositionOnTopoi.derivedPushforwardCompIsoUnconditional`
and `quasiIso_mapHomotopyCategory_pushforward_of_isKInjective`
(`Cohomology/DerivedPushforward/CompositionOnRingedTopoiUnconditional.lean:541` and `:445`),
and so does the unbounded derived pullback it rests on,
`Stacks.Cohomology.DerivedPullbackOnRingedTopoi.hasLeftDerivedFunctor_pullbackOnHomotopy`
(`Cohomology/DerivedPullback/DerivedPullbackExistence.lean:130`).
What is missing is the third morphism of the source's chain
`(C, O_C) → (D, O_D) → (pt, O_pt)`: the library's 0D6E composes direct
images along morphisms of ringed topoi presented by morphisms of *sites*, while `Γ(D, -)` is
`M.sections`, the limit over the whole site — the direct image along the structure morphism to
the punctual topos, which no functor of sites presents unless the site has a final object. The
full account, with the ringed-space precedent (Stacks 0D5W) that does have such a presentation,
is under `**Why not the source's proof**` in the module docstring of
`LerayForUnboundedSections.lean`.

**The route that closed the other clause, and that closed this one.** The clause on
sections over an object no longer carries flatness: it is
`Stacks.Cohomology.LerayUnbounded.derivedSectionsOverObjectPushforwardIsoGeneral`
(`Cohomology/DerivedPushforward/LerayForUnboundedSectionsGeneral.lean:235`),
proved by corepresenting `Γ(V, -)` by `j_{V!} O_V` and running
`Stacks.Cohomology.DerivedPullbackOnRingedTopoi.bijective_qh_map_pushforward_of_isKInjective`.
**That route does not need a final object, and it transfers to global sections**: `Γ(D, -)` is
corepresented by the structure sheaf itself, not by any `j_{D!} O_D` — Mathlib's
`CategoryTheory.SheafOfModules.unitHomEquiv` reads `Hom(O_D, M)` as `M.sections`, which is the
limit over the whole site, with no terminal object anywhere. The packaged form is
`Stacks.Cohomology.SiteModules.coyonedaUnitGlobalSectionsIso`
(`StacksFrontier/CategoryTheory/Sites/Cohomology/Modules/GlobalSectionsCorepresentable.lean:113`).
So the punctual presentation above is
what *the source's* proof needs, not what this clause needs.

The four inputs the route needs are these. The comparison `Lf^* ⟶ f^*` of Stacks 06YY is
invertible at `O_D` placed in degree zero, that complex being bounded above with flat terms:
the flatness is `Stacks.SheafOfModules.isFlat_unit`
(`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/FlatUnit.lean:45`), the analogue here of Stacks
03EV's flatness of `j_{V!} O_V` there. The bijectivity of postcomposition is
`bijective_postcomp_quotient_shift_of_isKInjective`
(`Cohomology/DerivedPushforward/PostcompIntoPushforwardOfKInjective.lean:112`),
which is stated for an arbitrary such complex. And the passage from `AddCommGrpCat`,
where the corepresentability lands,
back to `ModuleCat (Γ(O_D))`, where this clause's `G` lands, is
`CategoryTheory.HomologicalComplex.quasiIso_map_iff_of_preservesHomology`
(`Mathlib/Algebra/Homology/QuasiIso.lean:282`) along `forget₂`, whose `PreservesHomology` and
`ReflectsIsomorphisms` are both found by instance search.

The assembly is `LerayForUnboundedGlobalSectionsGeneral.lean`. Two spellings were expected to
need bridging there and did not: `Stacks.SheafOfModules.Tensor.ringSheaf Y.O` against
`(Stacks.SheafOfModules.Tensor.ringSheaf Y.O)` (`Stacks.SheafOfModules.Tensor.ringSheaf Y.O`), and
`(globalSectionsFunctor ⋙ forget₂).mapHomologicalComplex` against the composite of the two
`mapHomologicalComplex`es. Both are definitionally equal, and `exact`
(resp. rewriting with `quasiIso_map_iff_of_preservesHomology`) accepts them with no bridge,
a `def` being a wall for tactics and instance search but not for terms. Note also that
`StacksFrontier.AlgebraicGeometry.AffineVanishingUnbounded` must not be imported into this chain:
it makes instance search fail on `HasDerivedCategory AddCommGrpCat`, which is why the general
clause writes the naturality square out instead of quoting
`isIso_rightDerivedUnit_app_quotient_iff`.

**What flatness still buys.** Flatness — left exactness of `f^*` in the sense of Stacks 03DJ —
is not needed for the clause any more, only for the form of it whose hypothesis is an instance.
That form also asks for `HasWeakSheafify` and `WEqualsLocallyBijective` on the source site, as
`derivedSectionsOverObjectPushforwardIsoOfFlat` does, because `f^*` is only defined under them;
the general form asks for `HasSheafify` and `WEqualsLocallyBijective` on *both* sites, for the
same reason — the comparison of Stacks 06YY that its proof evaluates names `f^*`.

The right hand side is the total right derived functor of global sections *composed with*
restriction of scalars, rather than derived global sections followed by restriction of scalars on
the derived categories. The two agree, restriction of scalars being exact, but the second
spelling needs `CategoryTheory.Functor.mapDerivedCategory` for
`ModuleCat.restrictScalars`, whose exactness is not available as an instance here; and it is the
first spelling that `derivedCompIsoOfComputes` produces.

The three universes of the ringed sites are collapsed, as they are in
`AlgebraicGeometry.RingedSite.Hom` and throughout the derived development.

## References

* [Stacks Project, Tag 0D6H](https://stacks.math.columbia.edu/tag/0D6H)
* [Stacks Project, Tag 093Y](https://stacks.math.columbia.edu/tag/093Y)
* [Stacks Project, Tag 071H](https://stacks.math.columbia.edu/tag/071H)
* [Stacks Project, Tag 03DJ](https://stacks.math.columbia.edu/tag/03DJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open Stacks.Cohomology.SiteModules
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.DerivedFunctor (totalRightDerived)

namespace Stacks.Cohomology.LerayUnbounded

universe u

section GlobalSections

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

variable {X Y : RingedSite.{u, u, u}} (f : RingedSite.Hom X Y)

/-- **The ring map `Γ(O_D) ⟶ Γ(O_C)` of a morphism of ringed sites**, induced on global sections
by the structure map `O_D ⟶ f_* O_C`. It is the ring map
`Stacks.Cohomology.SiteModules.globalSectionsRingHom` of the associated morphism of ringed
topoi, over which the global sections of the source are read as a module over the global
sections of the structure sheaf of the target. -/
noncomputable abbrev siteGlobalSectionsRingHom :=
  globalSectionsRingHom (X := X.ringedTopos) (Y := Y.ringedTopos)
    f.ringedToposHom.toRingedToposModulesHom

/-- Unbounded derived global sections on a ringed site, `RΓ(Z, -) : D(O_Z) ⟶ D(Γ(O_Z))`: the
total right derived functor of the global sections of a sheaf of modules, taken as a module over
the ring of global sections of the structure sheaf (Stacks 071H). -/
noncomputable abbrev derivedGlobalSections (Z : RingedSite.{u, u, u}) :
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ⥤
      DerivedCategory (ModuleCat.{u}
        (RingCat.sectionsSubring (Stacks.SheafOfModules.Tensor.ringSheaf Z.O).obj)) :=
  totalRightDerived
    (globalSectionsFunctor.{u, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))

/-- The unbounded derived global sections of the source of a morphism of ringed sites, read in
`D(Γ(O_D))`: the total right derived functor of global sections with scalars restricted along
`siteGlobalSectionsRingHom`. This is the right hand side `RΓ(C, -)` of the global-sections clause
of Stacks 0D6H, which the source states as a functor `D(O_C) ⟶ D(Γ(O_D))`. -/
noncomputable abbrev derivedGlobalSectionsRestricted :
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
      DerivedCategory (ModuleCat.{u}
        (RingCat.sectionsSubring (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj)) :=
  totalRightDerived
    (globalSectionsFunctor.{u, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙
      ModuleCat.restrictScalars (siteGlobalSectionsRingHom f))

/-- **The underived identity behind the global-sections clause of Stacks 0D6H:** the global
sections of the direct image of a sheaf of modules along a morphism of ringed sites are the
global sections of that sheaf, as modules over `Γ(O_D)`.

Unlike `Stacks.Cohomology.LerayUnbounded.pushforwardTopos_comp_sectionsOverObject` this is not an
equality of functors: the two sides are modules over the different rings `Γ(O_D)` and `Γ(O_C)`,
and the comparison identifies the first with the second after restriction of scalars along
`siteGlobalSectionsRingHom`. It is the comparison
`Stacks.Cohomology.SiteModules.globalSectionsPushforwardIso` of the associated morphism of ringed
topoi, transported along
`AlgebraicGeometry.RingedSite.Hom.pushforwardModulesToposIso` to Mathlib's direct image along
the functor `u` of the underlying sites. -/
noncomputable def pushforwardToposCompGlobalSectionsIso :
    f.toRingedToposSiteHom.pushforwardTopos ⋙
        globalSectionsFunctor.{u, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ≅
      globalSectionsFunctor.{u, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙
        ModuleCat.restrictScalars (siteGlobalSectionsRingHom f) :=
  Functor.isoWhiskerRight (RingedSite.Hom.pushforwardModulesToposIso f).symm
      (globalSectionsFunctor.{u, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ≪≫
    globalSectionsPushforwardIso f.ringedToposHom.toRingedToposModulesHom

attribute [local instance] AlgebraicGeometry.RingedSite.Hom.pushforwardTopos_additive

/-- **Stacks 0D6H, the global-sections clause, over the weakest hypothesis there is.** For a
morphism of ringed sites `f : (C, O_C) ⟶ (D, O_D)` the unbounded derived global sections on `D`
of the unbounded derived direct image are the unbounded derived global sections on `C`, as
functors `D(O_C) ⟶ D(Γ(O_D))`, as soon as `f_* I` computes `RΓ(D, -)` for every K-injective
complex `I` of `O_C`-modules.

That hypothesis is exactly the content of the clause and nothing more, and it is true for every
morphism of ringed sites: it is what the source's route, Stacks 0D6E applied to
`(C, O_C) → (D, O_D) → (pt, O_pt)`, delivers. It is strictly weaker than preservation of
K-injectivity by `f_*`, which is Stacks 093Y and is a lemma *about flat morphisms* — see
`derivedGlobalSectionsPushforwardIsoOfKInjective` for the factorisation through it. -/
noncomputable def derivedGlobalSectionsPushforwardIso
    (hcomputes :
      letI : @Functor.Additive (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
          (ModuleCat.{u} (RingCat.sectionsSubring (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj))
          SheafOfModules.instCategory _ _ _
          (globalSectionsFunctor.{u, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :=
        globalSectionsFunctor_additive (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
      ComputesSecond f.toRingedToposSiteHom.pushforwardTopos
        (globalSectionsFunctor.{u, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) :
    derivedPushforward.{u} f.toRingedToposSiteHom ⋙ derivedGlobalSections Y ≅
      derivedGlobalSectionsRestricted f :=
  letI : @Functor.Additive (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ModuleCat.{u} (RingCat.sectionsSubring (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj))
      SheafOfModules.instCategory _ _ _
      (globalSectionsFunctor.{u, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :=
    globalSectionsFunctor_additive (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
  letI : @Functor.Additive (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ModuleCat.{u} (RingCat.sectionsSubring (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj))
      SheafOfModules.instCategory _ _ _
      (globalSectionsFunctor.{u, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙
        ModuleCat.restrictScalars (siteGlobalSectionsRingHom f)) :=
    (inferInstance : (globalSectionsFunctor.{u, u, u, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙
      ModuleCat.restrictScalars (siteGlobalSectionsRingHom f)).Additive)
  derivedCompIsoOfComputes f.toRingedToposSiteHom.pushforwardTopos
    (globalSectionsFunctor.{u, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (globalSectionsFunctor.{u, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙
      ModuleCat.restrictScalars (siteGlobalSectionsRingHom f))
    (pushforwardToposCompGlobalSectionsIso f) hcomputes

/-- The global-sections clause over the stronger hypothesis `h093Y` that degreewise direct image
preserves K-injectivity.

No tag: `h093Y` is not a hypothesis of the source, which gets the same conclusion from the
composition law of Stacks 0D6E. See `derivedGlobalSectionsPushforwardIsoOfFlat` for the case in
which `h093Y` is discharged, and `derivedGlobalSectionsPushforwardIso` for the weakest
hypothesis under which the conclusion holds. -/
noncomputable def derivedGlobalSectionsPushforwardIsoOfKInjective
    (h093Y : ∀ (I : CochainComplex
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ), I.IsKInjective →
      CochainComplex.IsKInjective
        ((f.toRingedToposSiteHom.pushforwardTopos.mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I)) :
    derivedPushforward.{u} f.toRingedToposSiteHom ⋙ derivedGlobalSections Y ≅
      derivedGlobalSectionsRestricted f :=
  letI : @Functor.Additive (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ModuleCat.{u} (RingCat.sectionsSubring (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj))
      SheafOfModules.instCategory _ _ _
      (globalSectionsFunctor.{u, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :=
    globalSectionsFunctor_additive (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
  derivedGlobalSectionsPushforwardIso f
    (computesSecond_of_isKInjective f.toRingedToposSiteHom.pushforwardTopos
      (globalSectionsFunctor.{u, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) h093Y)

/-- **Stacks 0D6H for a flat morphism of ringed sites, the global-sections clause.** Let
`f : (C, O_C) ⟶ (D, O_D)` be a flat morphism of ringed sites. Then
`RΓ(D, -) ∘ Rf_* = RΓ(C, -)` as functors `D(O_C) ⟶ D(Γ(O_D))`, the right hand side being the
derived global sections on `C` with scalars restricted along the induced ring map
`Γ(O_D) ⟶ Γ(O_C)`.

Flatness is the hypothesis `PreservesFiniteLimits` on `f^*` of Stacks 03DJ, and it is a genuine
restriction: the source assumes no flatness, deducing the lemma instead from the composition law
of Stacks 0D6E applied to `(C, O_C) → (D, O_D) → (pt, O_pt)`. That composition law is available
unconditionally; what is not is the presentation of `Γ(D, -)` as a direct image along a morphism
of ringed *sites* to a punctual one — see the `## Implementation notes` above. The source's
other clause, the one on sections over an object of `D`, is
`Stacks.Cohomology.LerayUnbounded.derivedSectionsOverObjectPushforwardIsoGeneral`.

**No tag: this clause is covered in general.** The flatness here is a genuine restriction,
and the tag sits on
`Stacks.Cohomology.LerayUnbounded.derivedGlobalSectionsPushforwardIsoGeneral`
(`Cohomology/DerivedPushforward/LerayForUnboundedGlobalSectionsGeneral.lean`), which is the same
conclusion for an arbitrary morphism of ringed sites. This flat form is kept because it is the
one whose hypothesis is an instance — `PreservesFiniteLimits` on `f^*` — and so the one instance
search finds without an argument. -/
noncomputable def derivedGlobalSectionsPushforwardIsoOfFlat
    [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [PreservesFiniteLimits f.toRingedToposSiteHom.pullbackTopos] :
    derivedPushforward.{u} f.toRingedToposSiteHom ⋙ derivedGlobalSections Y ≅
      derivedGlobalSectionsRestricted f :=
  derivedGlobalSectionsPushforwardIsoOfKInjective f (isKInjective_pushforwardTopos_of_flat f)

end GlobalSections

end Stacks.Cohomology.LerayUnbounded

end
