module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleRestrictKInjective
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.SheafificationOfTheCohomologyPresheaf
import StacksCore.Tactic.StacksAttribute

/-!
# `RΓ(U, -)` on the small étale site, and Stacks 0D6I at `ε`

Let `S` be a scheme and let `ε : (S_étale, 𝒪) ⟶ (S_Zar, 𝒪_S)` be the morphism of ringed sites of
Stacks 070R/08H7.  The clause of Stacks 0D6H on sections over an object says, for an object `V`
of the target site and `U` its image on the source site, that

`RΓ(V, -) ∘ Rf_* ≅ RΓ(U, -)`;

composed with `H^i` it is the displayed equality `H^i(U, K) = H^i(V, Rf_* K)` of Stacks 0D6I, the
one clause of that tag whose content is not Stacks 0BKV on the target site.  This file proves
both at `ε`, and then the remaining clauses of Stacks 0D6I at `ε` — the ones that *are* Stacks
0BKV on the target site — and so the whole of Stacks 0D6I at `ε`, with `Rε_*` in the spelling
`AlgebraicGeometry.SmallEtale.derivedRestrictModule` that this development uses.

## What was missing, and why the general statement does not apply

Stacks 0D6H and 0D6I are proved in general — see
`Stacks.Cohomology.LerayUnbounded.derivedSectionsOverObjectPushforwardIsoGeneral` and
`Stacks.Cohomology.UnboundedHigherDirectImageOnSites.cohomologySheavesOfTheDerivedDirectImage` —
but for an `AlgebraicGeometry.RingedSite.Hom` of two `AlgebraicGeometry.RingedSite.{u, u, u}`.
The small étale site has its objects in `Type (u + 1)`, so `ε` is not such a morphism and the
general statements do not typecheck at `ε`.

The abstract brick they rest on *is* universe-polymorphic:
`Stacks.Cohomology.LerayUnbounded.derivedCompIsoOfComputes` takes three abelian categories with
independent object and morphism universes, and its hypothesis
`Stacks.Cohomology.LerayUnbounded.ComputesSecond ε_* (Γ(V, -))` — that `ε_* I` computes
`RΓ(V, -)` for every K-injective complex `I` — is proved at `ε` as
`AlgebraicGeometry.SmallEtale.computesSecond_restrictModule`, which is Stacks 093Y at `ε`, `ε`
being flat with `ε^*` exact by the second assertion of Stacks 08H8.  What was missing was only
the *right-hand* side of the comparison: derived sections over an object of the small étale site.

`Stacks.Cohomology.Localization.derivedSectionsOverObject` cannot supply it.  It is stated for a
`AlgebraicGeometry.RingedSite.{u, u, u}`, and relaxing it in place fails.  The instance that is
missing at independent site universes is **not** `CategoryTheory.Abelian`:
`CategoryTheory.Abelian (SheafOfModules.{u} X.ringSheaf)` is synthesized for an
`AlgebraicGeometry.RingedSite.{uX, vX, u}` from the sheafification and local-bijectivity instances
alone.  What fails is the `CategoryTheory.Functor.HasRightDerivedFunctor` that the body's
`CategoryTheory.Functor.totalRightDerived` needs, which comes from the K-injective resolutions,
hence from `CategoryTheory.IsGrothendieckAbelian` — and that *is* unavailable there, the generic
instances asking either for a site small on the nose or for the module universe to dominate the
site universes.  Carrying it as an instance binder would add a hypothesis to a declaration used
throughout the tree.  So derived sections over an object are stated here *at the small étale
site*, where the instance is genuinely available:
`AlgebraicGeometry.smallEtaleRingedSite_isGrothendieckAbelian`, by essential smallness of the
site, is what `CategoryTheory.Functor.totalRightDerived` runs on.

The *underived* sections functor is no obstruction, but it too is stated for a
`AlgebraicGeometry.RingedSite.{u, u, u}`: `Stacks.Cohomology.Localization.sectionsOverObject`.
Its definition — evaluation at `U` followed by the forgetful functor to abelian groups — makes
sense at any ringed site, so it is written out at the small étale site as
`AlgebraicGeometry.SmallEtale.sectionsOverObjectForget`, with its additivity.

## The other two clauses of Stacks 0D6I, at the standard derived categories

Clauses one and three of Stacks 0D6I read the cohomology presheaf on the *target* site: they are
Stacks 0BKV there, composed with `Rf_*`, and they carry no universe obstruction of their own, the
target being `AlgebraicGeometry.Scheme.zariskiRingedSite`, a
`AlgebraicGeometry.RingedSite.{u, u, u}`.  Both are available at `ε`, and are proved below.

What stands in the way is only that
`Stacks.Cohomology.SiteCohomologyPresheaf.sheafificationCohomologyPresheafIso` and
`Stacks.Cohomology.SiteCohomologyPresheaf.cohomologyPresheafEvaluationIso` are stated at
`CategoryTheory.HasDerivedCategory.standard`, so the derived category of `𝒪_S`-modules in them is
the standard one and the free `w` of `Rε_*` has to be the universe that instance supplies.  That
universe is `u + 1` on *both* sides of `ε`, so there is no clash: `SheafOfModules.{u}` of a sheaf
of rings on either site has its objects in `Type (u + 1)`, the categories being categories of
sheaves valued in `ModuleCat.{u}`, and `CategoryTheory.HasDerivedCategory.standard` gives
`HasDerivedCategory.{max u_obj u_hom}` — which is `u + 1` for the small étale site, whose
morphisms also lie in `Type (u + 1)`, and `max (u + 1) u = u + 1` for the small Zariski site,
whose morphisms lie in `Type u`.  `Rε_*` therefore does exist at
`CategoryTheory.HasDerivedCategory.standard`, and nothing in the shared `standard`-pinned
development has to be freed.

The reason this is not simply `attribute [local instance] HasDerivedCategory.standard` is
instance *synthesis*, not typing: at a goal whose universe is already fixed to `u + 1` the
synthesis of `HasDerivedCategory.standard` has to solve `max ?u_obj ?u_hom =?= u + 1` with both
sides metavariables, which Lean does not do.  The four instances are therefore named explicitly
below, as `HasDerivedCategory.standard` applied to the category in question.

## Main definitions

* `AlgebraicGeometry.SmallEtale.sectionsOverObjectForget`: `Γ(U, -)` on the `𝒪`-modules of the
  small étale site, with the module structure forgotten.
* `AlgebraicGeometry.SmallEtale.derivedSectionsOverObject`: `RΓ(U, -) : D(S_étale, 𝒪) ⥤ D(Ab)`,
  the unbounded derived sections over an object `U` of the small étale site of `S`.
* `AlgebraicGeometry.SmallEtale.derivedSectionsOverObjectRestrictModuleIso`: **the clause of
  Stacks 0D6H on sections over an object, at `ε`** — `RΓ(ε(V), -) ≅ RΓ(V, -) ∘ Rε_*`.
* `AlgebraicGeometry.SmallEtale.cohomologyOverObjectRestrictModuleIso`: **the displayed equality
  of Stacks 0D6I at `ε`** — `H^i(ε(V), K) ≅ H^i(V, Rε_* K)`, naturally in `K`.
* `AlgebraicGeometry.SmallEtale.higherDirectImageIsoSheafifyCohomologyPresheafRestrictModule`:
  **the associated-sheaf clause of Stacks 0D6I at `ε`** — the `i`-th cohomology sheaf of
  `Rε_* K` is the sheafification of the presheaf `V ↦ H^i(V, Rε_* K)`, naturally in `K`.
* `AlgebraicGeometry.SmallEtale.cohomologyPresheafEvaluationRestrictModuleIso`: **the clause of
  Stacks 0D6I on values on objects of the target site, at `ε`** — the value on an open `V` of `S`
  of that presheaf is `H^i(V, Rε_* K)`.
* `AlgebraicGeometry.SmallEtale.cohomologyPresheafSourceValueRestrictModuleIso`: the value on `V`
  of that presheaf read on the small étale site, `H^i(ε(V), K)`, which is the description of the
  presheaf the source displays.
* `AlgebraicGeometry.SmallEtale.cohomologySheavesOfDerivedRestrictModule`: **Stacks 0D6I at
  `ε`**, the three clauses together.
* `AlgebraicGeometry.SmallEtale.derivedModuleSectionsRestrictModuleIso`: **the module-valued
  clause of Stacks 0D6H on sections over an object, at `ε`** — the same comparison as
  `derivedSectionsOverObjectRestrictModuleIso` with the module structure kept rather than
  forgotten, as functors into `D(𝒪_S(V))`.  See "The module-valued form" below.

## Main results

* `AlgebraicGeometry.SmallEtale.restrictModuleOfSheaf_comp_sectionsOverObject`: the underived
  identity `Γ(V, ε_* M) = Γ(ε(V), M)`, an equality of functors and not merely an isomorphism.
* `AlgebraicGeometry.SmallEtale.hasRightDerivedFunctor_moduleSections`: **`RΓ(U, -)` exists
  module-valued on the small étale site of a scheme**, with no hypothesis — which is what makes
  `Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.derivedSections` available there.
* `AlgebraicGeometry.SmallEtale.restrictModuleOfSheaf_comp_moduleSections`: the module-valued
  underived identity, again an equality of functors.

## The module-valued form

`AlgebraicGeometry.SmallEtale.derivedSectionsOverObject` lands in
`DerivedCategory AddCommGrpCat`: it is the total right derived functor of
`AlgebraicGeometry.SmallEtale.sectionsOverObjectForget`, which forgets the module structure by
construction.  That is enough for the cohomology *groups* of Stacks 0D6I, and not enough to meet
any statement about a complex of modules — Stacks 08E7, Stacks 065I, or the affine condition of
Stacks 0CSX.  So the comparison is proved here a second time with the module structure kept, out
of the same two inputs, and the module-valued `RΓ(U, -)` it needs is
`Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.derivedSections`, which exists at the
small étale site of a scheme by `hasRightDerivedFunctor_moduleSections`.

The module-valued statement is **not** the abelian-group-valued one with the forgetful functor
deleted, and the reason is worth recording: the structure map of `ε` is not the identity.
`AlgebraicGeometry.SmallEtale.structureMap` at an open `V` is
`(AlgebraicGeometry.Scheme.Opens.topIso V).inv`, the identification of the sections of `𝒪_S` over
`V` with the global functions of the open subscheme `V`, so the two rings `𝒪_S(V)` and `𝒪(ε(V))`
are isomorphic but not equal — not even definitionally, their object universes differing — and
sections over `ε(V)` are `𝒪_S(V)`-modules only after a restriction of scalars.  The underived
identity `restrictModuleOfSheaf_comp_moduleSections` therefore carries a
`ModuleCat.restrictScalars` on the étale side, where it is an equality of functors on the nose,
and the derived comparison carries it in the same place.

## Implementation notes

The `CategoryTheory.HasDerivedCategory` instances of the clause on sections over an object are
left free, as in
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleDerivedPushforward`.
The three remaining clauses are stated at the four standard instances instead, that being what
the shared `standard`-pinned Stacks 0BKV declarations they rest on are available at; they
therefore carry no `CategoryTheory.HasDerivedCategory` hypothesis at all.  The four instances are
`local`, so that nothing is added to global instance search by importing this module; a consumer
that wants them writes `attribute [local instance]` with their names.

`AlgebraicGeometry.SmallEtale.hasDerivedCategory_smallEtaleRingedSite_ringSheaf` restates the
ambient instance for `(AlgebraicGeometry.smallEtaleRingedSite B S hS).ringSheaf`, which is
`AlgebraicGeometry.SmallEtale.structureSheaf B S hS` by `rfl`
(`AlgebraicGeometry.SmallEtale.smallEtaleRingedSite_ringSheaf`) but is not identified with it by
instance search; it names no new fact.

No `@[stacks]` attribute is attached: every statement here is the instance at `ε` of a tag proved
in general, and a tag is not restated at an instance.

## References

* [Stacks Project, Tag 0D6H](https://stacks.math.columbia.edu/tag/0D6H)
* [Stacks Project, Tag 0D6I](https://stacks.math.columbia.edu/tag/0D6I)
* [Stacks Project, Tag 0BKV](https://stacks.math.columbia.edu/tag/0BKV)
* [Stacks Project, Tag 093Y](https://stacks.math.columbia.edu/tag/093Y)
* [Stacks Project, Tag 07A5](https://stacks.math.columbia.edu/tag/07A5)
* [Stacks Project, Tag 08H8](https://stacks.math.columbia.edu/tag/08H8)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cohomology.Localization (sectionsOverObject)
open Stacks.Cohomology.HypercohomologyEdge.HomologyComparison
  (homotopySections exists_quasiIso_isKInjective_sheafOfModules)
open Stacks.Cohomology.SiteCohomologyPresheaf
  (derivedSectionsPresheaf sheafificationCohomologyPresheafIso cohomologyPresheafEvaluationIso)

namespace AlgebraicGeometry.SmallEtale

universe w u

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Sections over an object of the small étale site**, `Γ(U, -)` on the `𝒪`-modules of the
small étale site of `S`, with the module structure forgotten: evaluation at `U` followed by the
forgetful functor to abelian groups.

This is the definition of `Stacks.Cohomology.Localization.sectionsOverObject`, which is stated
for a ringed site with its three universes collapsed, written out at
`AlgebraicGeometry.smallEtaleRingedSite`, whose objects lie one universe above its morphisms. -/
abbrev sectionsOverObjectForget (U : SmallEtale B S hS) :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O) ⥤
      AddCommGrpCat.{u} :=
  SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O)
      (op U) ⋙
    forget₂ (ModuleCat.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O).obj.obj (op U)))
      AddCommGrpCat.{u}

/-- The functor `sectionsOverObjectForget B S hS U` of sections over `U` is additive. -/
instance additive_sectionsOverObjectForget (U : SmallEtale B S hS) :
    (sectionsOverObjectForget B S hS U).Additive where
  map_add := rfl

/-- **The underived identity behind the clause of Stacks 0D6H on sections over an object, at
`ε`.**  Sections over an open `V` of `S` of the restriction `ε_* M` of a sheaf of modules on the
small étale site are the sections of `M` over `ε(V)`.

As in the source this is an *equality* of functors, not merely an isomorphism: `ε_*` is
`SheafOfModules.pushforward` along `AlgebraicGeometry.SmallEtale.structureMap`, whose underlying
operation on presheaves is precomposition with the opposite of
`AlgebraicGeometry.SmallEtale.opensToSmallEtale`, and restricting the scalars along the structure
map leaves the underlying abelian group alone. -/
theorem restrictModuleOfSheaf_comp_sectionsOverObject (V : S.Opens) :
    restrictModuleOfSheaf B S hS ⋙ sectionsOverObject S.zariskiRingedSite V =
      sectionsOverObjectForget B S hS ((opensToSmallEtale B S hS).obj V) := rfl

section FreeDerivedCategory

variable [HasDerivedCategory.{w} (SheafOfModules.{u} (structureSheaf B S hS))]
  [HasDerivedCategory.{w} (SheafOfModules.{u} S.ringCatSheaf)]
  [HasDerivedCategory.{w} AddCommGrpCat.{u}]

/-- The ambient derived category of the `𝒪`-modules on the small étale site, restated for the
sheaf of rings of `AlgebraicGeometry.smallEtaleRingedSite`.  That sheaf of rings is
`AlgebraicGeometry.SmallEtale.structureSheaf` by `rfl`
(`AlgebraicGeometry.SmallEtale.smallEtaleRingedSite_ringSheaf`), but instance search does not
identify the two, so the instance has to be named at this spelling. -/
instance hasDerivedCategory_smallEtaleRingedSite_ringSheaf :
    HasDerivedCategory.{w} (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O)) :=
  inferInstanceAs (HasDerivedCategory.{w} (SheafOfModules.{u} (structureSheaf B S hS)))

/-- **Unbounded derived sections over an object of the small étale site**,
`RΓ(U, -) : D(S_étale, 𝒪) ⥤ D(Ab)`: the total right derived functor of the sections functor
`Γ(U, -)` of `AlgebraicGeometry.SmallEtale.sectionsOverObjectForget`.

It exists because the `𝒪`-modules on `S_étale` are Grothendieck abelian at the universe of their
sections, `AlgebraicGeometry.smallEtaleRingedSite_isGrothendieckAbelian`; that is what
`CategoryTheory.Functor.totalRightDerived` needs, and it is the one input
`Stacks.Cohomology.Localization.derivedSectionsOverObject` cannot have, being stated for a ringed
site with its three universes collapsed. -/
def derivedSectionsOverObject (U : SmallEtale B S hS) :
    DerivedCategory (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O)) ⥤
      DerivedCategory AddCommGrpCat.{u} :=
  Stacks.DerivedFunctor.totalRightDerived
    (sectionsOverObjectForget B S hS U)

/-- **The clause of Stacks 0D6H on sections over an object, at `ε`.**  For an open `V` of `S`,
the unbounded derived sections over `ε(V)` on the small étale site are the unbounded derived
sections over `V` of the unbounded derived direct image along `ε`:

`RΓ(ε(V), -) ≅ RΓ(V, -) ∘ Rε_*`.

Both sides are right derived functors of one and the same functor on the unbounded homotopy
category of `𝒪`-modules on `S_étale`, by the underived equality
`restrictModuleOfSheaf_comp_sectionsOverObject`: the comparison for `Rε_*` is invertible on a
K-injective complex with no hypothesis (Stacks 07A5), and the comparison for `RΓ(V, -)` is
invertible at `ε_* I` by `AlgebraicGeometry.SmallEtale.computesSecond_restrictModule`, which is
Stacks 093Y at `ε`.  Uniqueness of right derived functors identifies the two.

`RΓ(V, -)` on the Zariski side is written out as evaluation at `V` followed by the forgetful
functor, rather than as `Stacks.Cohomology.Localization.sectionsOverObject` of
`AlgebraicGeometry.Scheme.zariskiRingedSite`, because the latter states its source category at
`Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O` while `Rε_*` states its target at
`AlgebraicGeometry.Scheme.ringCatSheaf`.  The two sheaves of rings are equal by `rfl`
(`AlgebraicGeometry.Scheme.zariskiRingedSite_ringSheaf`), so the composite is the same functor
either way; but the additive structures instance search attaches to the two spellings are not
identified by it, and the `CategoryTheory.Functor.Additive` of the sections functor is then asked
for at a preadditive structure that the general instance was not registered at. -/
def derivedSectionsOverObjectRestrictModuleIso (V : S.Opens) :
    derivedSectionsOverObject.{w} B S hS ((opensToSmallEtale B S hS).obj V) ≅
      derivedRestrictModule.{w, w} B S hS ⋙
        Stacks.DerivedFunctor.totalRightDerived
          (SheafOfModules.evaluation.{u} S.ringCatSheaf (op V) ⋙
            forget₂ (ModuleCat.{u} (S.ringCatSheaf.obj.obj (op V))) AddCommGrpCat.{u}) :=
  (Stacks.Cohomology.LerayUnbounded.derivedCompIsoOfComputes
    (restrictModuleOfSheaf B S hS)
    (SheafOfModules.evaluation.{u} S.ringCatSheaf (op V) ⋙
      forget₂ (ModuleCat.{u} (S.ringCatSheaf.obj.obj (op V))) AddCommGrpCat.{u})
    _ (Iso.refl _) (computesSecond_restrictModule B S hS _)).symm

/-- **The displayed equality of Stacks 0D6I at `ε`.**  Cohomology over `ε(V)` on the small étale
site agrees with cohomology over the open `V` after the unbounded derived direct image,

`H^i(ε(V), K) ≅ H^i(V, Rε_* K)`,

naturally in `K`.  This is `H^i` of `derivedSectionsOverObjectRestrictModuleIso`, and it is the
clause of Stacks 0D6I carrying the whole of its content; the other two clauses are Stacks 0BKV on
the Zariski site, which is not statable at `ε` for the reason in the module documentation. -/
def cohomologyOverObjectRestrictModuleIso (V : S.Opens) (i : ℤ) :
    derivedSectionsOverObject.{w} B S hS ((opensToSmallEtale B S hS).obj V) ⋙
        DerivedCategory.homologyFunctor AddCommGrpCat.{u} i ≅
      derivedRestrictModule.{w, w} B S hS ⋙
        Stacks.DerivedFunctor.totalRightDerived
          (SheafOfModules.evaluation.{u} S.ringCatSheaf (op V) ⋙
            forget₂ (ModuleCat.{u} (S.ringCatSheaf.obj.obj (op V))) AddCommGrpCat.{u}) ⋙
        DerivedCategory.homologyFunctor AddCommGrpCat.{u} i :=
  Functor.isoWhiskerRight (derivedSectionsOverObjectRestrictModuleIso.{w} B S hS V)
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u} i) ≪≫ Functor.associator _ _ _

end FreeDerivedCategory

/-! ### `RΓ(U, -)` with its module structure, and the clause on sections over an object there -/

/-- **`RΓ(U, -)` exists module-valued on the small étale site of a scheme**: sections of
`𝒪`-modules at an object `U` of `S_étale`, taken as modules over the ring `𝒪(U)` of sections
there and followed by localization, have an unbounded right derived functor, with no hypothesis.

This is what makes `Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.derivedSections`
available at the small étale site of a scheme, and it is the module-valued counterpart of
`AlgebraicGeometry.SmallEtale.derivedSectionsOverObject`, which forgets the module structure and
lands in `DerivedCategory AddCommGrpCat`.  Evaluation of a sheaf of modules at an object of a
ringed site is additive and left exact, and every complex of `𝒪`-modules on `S_étale` admits a
quasi-isomorphism into a K-injective complex
(`AlgebraicGeometry.SmallEtale.exists_quasiIso_isKInjective`), which is what the derived functor
is computed by; the argument is the one of
`AlgebraicGeometry.Space.hasRightDerivedFunctor_chartSections` for an algebraic space. -/
theorem hasRightDerivedFunctor_moduleSections (U : SmallEtale B S hS) :
    (homotopySections.{u + 1, u, u, u}
      (structureSheaf B S hS) U).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (structureSheaf B S hS)) (ComplexShape.up ℤ)) :=
  have := (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{
      u + 1, u + 1, u + 1, u + 1, u + 1, u + 1}
    (homotopySections.{u + 1, u, u, u} (structureSheaf B S hS) U)
    (exists_quasiIso_isKInjective_sheafOfModules (structureSheaf B S hS))).1
  Functor.hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor _ _

/-- **The underived identity behind the module-valued clause of Stacks 0D6H on sections over an
object, at `ε`.**  Sections over an open `V` of `S` of the restriction `ε_* M`, as a module over
`𝒪_S(V)`, are the sections of `M` over `ε(V)` with their scalars restricted along the structure
map of `ε` at `V`.

Like `AlgebraicGeometry.SmallEtale.restrictModuleOfSheaf_comp_sectionsOverObject` this is an
*equality* of functors, not merely an isomorphism: `ε_*` is `SheafOfModules.pushforward` along
`AlgebraicGeometry.SmallEtale.structureMap`, which is precomposition of the underlying presheaf
with the opposite of `AlgebraicGeometry.SmallEtale.opensToSmallEtale` together with exactly that
restriction of scalars.

The restriction of scalars cannot be dropped, and this is the one place where the module-valued
statement differs in shape from the abelian-group-valued one.  The structure map of `ε` is
**not** the identity: `AlgebraicGeometry.SmallEtale.structureMap` at `V` is
`(AlgebraicGeometry.Scheme.Opens.topIso V).inv`, the identification of the sections of `𝒪_S` over
`V` with the global functions of the open subscheme `V`.  So the two rings `𝒪_S(V)` and `𝒪(ε(V))`
are isomorphic but not equal — they are not even definitionally equal, their very universes
differing in the object slot — and a module over one is only a module over the other after
transport. -/
theorem restrictModuleOfSheaf_comp_moduleSections (V : S.Opens) :
    SheafOfModules.evaluation.{u} (structureSheaf B S hS)
          (op ((opensToSmallEtale B S hS).obj V)) ⋙
        ModuleCat.restrictScalars.{u} ((structureMap B S hS).hom.app (op V)).hom =
      restrictModuleOfSheaf B S hS ⋙ SheafOfModules.evaluation.{u} S.ringCatSheaf (op V) := rfl

/-- Module-valued sections at `ε(V)` followed by the restriction of scalars along the structure
map of `ε` is additive: on a morphism both functors act by acting on the underlying map of
presheaves, and restricting scalars leaves that map alone. -/
instance additive_moduleSections_comp_restrictScalars (V : S.Opens) :
    (SheafOfModules.evaluation.{u} (structureSheaf B S hS)
          (op ((opensToSmallEtale B S hS).obj V)) ⋙
        ModuleCat.restrictScalars.{u} ((structureMap B S hS).hom.app (op V)).hom).Additive where
  map_add := by intros; rfl

section ModuleValued

variable [HasDerivedCategory.{w} (SheafOfModules.{u} (structureSheaf B S hS))]
  [HasDerivedCategory.{w} (SheafOfModules.{u} S.ringCatSheaf)]

/-- **The module-valued clause of Stacks 0D6H on sections over an object, at `ε`.**  For an open
`V` of `S`, the unbounded derived sections over `ε(V)` on the small étale site — read as
`𝒪_S(V)`-modules along the structure map of `ε` — are the unbounded derived sections over `V` of
the unbounded derived direct image along `ε`:

`RΓ(ε(V), -) ⊗_{𝒪(ε(V))} 𝒪_S(V) ≅ RΓ(V, -) ∘ Rε_*`  —  more precisely, `R(Γ(ε(V), -)` followed by
restriction of scalars`) ≅ RΓ(V, -) ∘ Rε_*` as functors into `D(𝒪_S(V))`.

This is `AlgebraicGeometry.SmallEtale.derivedSectionsOverObjectRestrictModuleIso` with the module
structure kept rather than forgotten, and it is what the comparison of `RΓ` across `ε` has to be
in order to meet a statement about complexes of modules, such as Stacks 08E7 or Stacks 065I.
Both sides are right derived functors of one and the same functor on the unbounded homotopy
category of `𝒪`-modules on `S_étale`, by the underived equality
`AlgebraicGeometry.SmallEtale.restrictModuleOfSheaf_comp_moduleSections`: the comparison for
`Rε_*` is invertible on a K-injective complex with no hypothesis (Stacks 07A5), and the one for
`RΓ(V, -)` is invertible at `ε_* I` by
`AlgebraicGeometry.SmallEtale.computesSecond_restrictModule`, which is Stacks 093Y at `ε`.
Uniqueness of right derived functors identifies the two.

The restriction of scalars sits on the étale side rather than the Zariski side because that is
the orientation in which the underived statement is an equality; see
`restrictModuleOfSheaf_comp_moduleSections` for why it cannot be dropped. -/
def derivedModuleSectionsRestrictModuleIso (V : S.Opens)
    [HasDerivedCategory.{w} (ModuleCat.{u} (S.ringCatSheaf.obj.obj (op V)))] :
    Stacks.DerivedFunctor.totalRightDerived
        (SheafOfModules.evaluation.{u} (structureSheaf B S hS)
            (op ((opensToSmallEtale B S hS).obj V)) ⋙
          ModuleCat.restrictScalars.{u} ((structureMap B S hS).hom.app (op V)).hom) ≅
      derivedRestrictModule.{w, w} B S hS ⋙
        Stacks.DerivedFunctor.totalRightDerived
          (SheafOfModules.evaluation.{u} S.ringCatSheaf (op V)) :=
  (Stacks.Cohomology.LerayUnbounded.derivedCompIsoOfComputes
    (restrictModuleOfSheaf B S hS) (SheafOfModules.evaluation.{u} S.ringCatSheaf (op V))
    _ (Iso.refl _) (computesSecond_restrictModule B S hS _)).symm

end ModuleValued

/-! ### The cohomology presheaf of `Rε_*`: the remaining clauses of Stacks 0D6I at `ε` -/

section StandardDerivedCategory

/-- The standard derived category of the `𝒪`-modules on the small étale site of `S`, named
because instance synthesis cannot produce `CategoryTheory.HasDerivedCategory.standard` at a goal
whose universe is already fixed: that would mean solving `max ?u_obj ?u_hom =?= u + 1`. -/
local instance hasDerivedCategoryStandard_structureSheaf :
    HasDerivedCategory.{u + 1} (SheafOfModules.{u} (structureSheaf B S hS)) :=
  HasDerivedCategory.standard _

/-- The standard derived category of the `𝒪_S`-modules.  Its universe is `u + 1`, not `u`: the
objects of `SheafOfModules.{u} S.ringCatSheaf` lie in `Type (u + 1)`, being sheaves valued in
`ModuleCat.{u}`, so `max u_obj u_hom = max (u + 1) u = u + 1`.  This is why `Rε_*`, which needs
one derived-category universe on both sides, does exist at
`CategoryTheory.HasDerivedCategory.standard`. -/
local instance hasDerivedCategoryStandard_ringCatSheaf :
    HasDerivedCategory.{u + 1} (SheafOfModules.{u} S.ringCatSheaf) :=
  HasDerivedCategory.standard _

/-- The standard derived category of the presheaves of `𝒪_S`-modules, where the cohomology
presheaf of Stacks 0BKV lives. -/
local instance hasDerivedCategoryStandard_presheafOfModules :
    HasDerivedCategory.{u + 1} (PresheafOfModules.{u} S.ringCatSheaf.obj) :=
  HasDerivedCategory.standard _

/-- The standard derived category of the abelian groups at the universe of the sections. -/
local instance hasDerivedCategoryStandard_addCommGrpCat :
    HasDerivedCategory.{u + 1} AddCommGrpCat.{u} :=
  HasDerivedCategory.standard _

/-- **The associated-sheaf clause of Stacks 0D6I at `ε`.**  The `i`-th cohomology sheaf of
`Rε_* K` is the sheaf associated to the presheaf `V ↦ H^i(V, Rε_* K)` of `𝒪_S`-modules, naturally
in `K`.

This is Stacks 0BKV on the small Zariski site of `S` —
`Stacks.Cohomology.SiteCohomologyPresheaf.sheafificationCohomologyPresheafIso`, the cohomology
sheaf of an object of `D(𝒪_S)` is the sheafification of its cohomology presheaf — composed with
`Rε_*`, exactly as the clause for a morphism of ringed sites with collapsed universes is
`Stacks.Cohomology.UnboundedHigherDirectImageOnSites`'s
`higherDirectImageIsoSheafifyCohomologyPresheaf`. -/
def higherDirectImageIsoSheafifyCohomologyPresheafRestrictModule (i : ℤ) :
    derivedRestrictModule.{u + 1, u + 1} B S hS ⋙
        DerivedCategory.homologyFunctor (SheafOfModules.{u} S.ringCatSheaf) i ≅
      derivedRestrictModule.{u + 1, u + 1} B S hS ⋙ derivedSectionsPresheaf S.zariskiRingedSite ⋙
        DerivedCategory.homologyFunctor (PresheafOfModules.{u} S.ringCatSheaf.obj) i ⋙
        PresheafOfModules.sheafification (𝟙 S.ringCatSheaf.obj) :=
  (Functor.isoWhiskerLeft (derivedRestrictModule.{u + 1, u + 1} B S hS)
    (sheafificationCohomologyPresheafIso S.zariskiRingedSite i)).symm

/-- **The clause of Stacks 0D6I on values on objects of the target site, at `ε`.**  The value on
an open `V` of `S` of the cohomology presheaf of `Rε_* K` is the hypercohomology
`H^i(V, Rε_* K)`, naturally in `K`.

This is Stacks 0BKV on the small Zariski site of `S` —
`Stacks.Cohomology.SiteCohomologyPresheaf.cohomologyPresheafEvaluationIso` — composed with
`Rε_*`. -/
def cohomologyPresheafEvaluationRestrictModuleIso (V : S.Opens) (i : ℤ) :
    derivedRestrictModule.{u + 1, u + 1} B S hS ⋙ derivedSectionsPresheaf S.zariskiRingedSite ⋙
        DerivedCategory.homologyFunctor (PresheafOfModules.{u} S.ringCatSheaf.obj) i ⋙
        PresheafOfModules.evaluation S.ringCatSheaf.obj (Opposite.op V) ⋙
        forget₂ (ModuleCat.{u} (S.ringCatSheaf.obj.obj (Opposite.op V))) AddCommGrpCat.{u} ≅
      derivedRestrictModule.{u + 1, u + 1} B S hS ⋙
        @Stacks.Cohomology.Localization.derivedSectionsOverObject S.zariskiRingedSite V
          (inferInstance : HasDerivedCategory.{u + 1} (SheafOfModules.{u} S.ringCatSheaf)) _ ⋙
        DerivedCategory.homologyFunctor AddCommGrpCat.{u} i :=
  Functor.isoWhiskerLeft (derivedRestrictModule.{u + 1, u + 1} B S hS)
    (cohomologyPresheafEvaluationIso S.zariskiRingedSite V i)

/-- **The clause of Stacks 0D6I on values read on the source site, at `ε`.**  The value on an
open `V` of `S` of the cohomology presheaf of `Rε_* K` is the hypercohomology `H^i(ε(V), K)` over
`ε(V)` on the small étale site, naturally in `K`.  This is the description of the presheaf that
the source displays.

It is `H^i(V, Rε_* K)` by Stacks 0BKV on the small Zariski site, and that is `H^i(ε(V), K)` by
the displayed equality `cohomologyOverObjectRestrictModuleIso`. -/
def cohomologyPresheafSourceValueRestrictModuleIso (V : S.Opens) (i : ℤ) :
    derivedRestrictModule.{u + 1, u + 1} B S hS ⋙ derivedSectionsPresheaf S.zariskiRingedSite ⋙
        DerivedCategory.homologyFunctor (PresheafOfModules.{u} S.ringCatSheaf.obj) i ⋙
        PresheafOfModules.evaluation S.ringCatSheaf.obj (Opposite.op V) ⋙
        forget₂ (ModuleCat.{u} (S.ringCatSheaf.obj.obj (Opposite.op V))) AddCommGrpCat.{u} ≅
      derivedSectionsOverObject.{u + 1} B S hS ((opensToSmallEtale B S hS).obj V) ⋙
        DerivedCategory.homologyFunctor AddCommGrpCat.{u} i :=
  cohomologyPresheafEvaluationRestrictModuleIso B S hS V i ≪≫
    (cohomologyOverObjectRestrictModuleIso.{u + 1} B S hS V i).symm

/-- **Stacks 0D6I at `ε`.**  For `i : ℤ` the `i`-th cohomology sheaf of `Rε_* K` is the sheaf
associated to the presheaf

`V ↦ H^i(ε(V), K) = H^i(V, Rε_* K)`,

naturally in the object `K` of `D(S_étale, 𝒪)`.

The presheaf is `derivedSectionsPresheaf S.zariskiRingedSite ⋙ H^i` of `Rε_* K`, which carries
its restriction maps and not only its values on objects, and the three components are the three
assertions the source makes about it: that its sheafification is the `i`-th cohomology sheaf of
`Rε_* K`, and that its value on `V` is `H^i(V, Rε_* K)` and is `H^i(ε(V), K)` — the two sides of
the source's displayed equality, whose composite is
`cohomologyOverObjectRestrictModuleIso`.

No `@[stacks 0D6I]` attribute: the tag is stated and proved for an arbitrary morphism of ringed
sites by `Stacks.Cohomology.UnboundedHigherDirectImageOnSites`'s
`cohomologySheavesOfTheDerivedDirectImage`, and this is its instance at `ε`, which is not such a
morphism only because the small étale site has its objects one universe up. -/
def cohomologySheavesOfDerivedRestrictModule (i : ℤ) :
    (derivedRestrictModule.{u + 1, u + 1} B S hS ⋙
          DerivedCategory.homologyFunctor (SheafOfModules.{u} S.ringCatSheaf) i ≅
        derivedRestrictModule.{u + 1, u + 1} B S hS ⋙ derivedSectionsPresheaf S.zariskiRingedSite ⋙
          DerivedCategory.homologyFunctor (PresheafOfModules.{u} S.ringCatSheaf.obj) i ⋙
          PresheafOfModules.sheafification (𝟙 S.ringCatSheaf.obj)) ×
      (∀ V : S.Opens,
          derivedRestrictModule.{u + 1, u + 1} B S hS ⋙
              derivedSectionsPresheaf S.zariskiRingedSite ⋙
              DerivedCategory.homologyFunctor (PresheafOfModules.{u} S.ringCatSheaf.obj) i ⋙
              PresheafOfModules.evaluation S.ringCatSheaf.obj (Opposite.op V) ⋙
              forget₂ (ModuleCat.{u} (S.ringCatSheaf.obj.obj (Opposite.op V)))
                AddCommGrpCat.{u} ≅
            derivedSectionsOverObject.{u + 1} B S hS ((opensToSmallEtale B S hS).obj V) ⋙
              DerivedCategory.homologyFunctor AddCommGrpCat.{u} i) ×
      (∀ V : S.Opens,
          derivedRestrictModule.{u + 1, u + 1} B S hS ⋙
              derivedSectionsPresheaf S.zariskiRingedSite ⋙
              DerivedCategory.homologyFunctor (PresheafOfModules.{u} S.ringCatSheaf.obj) i ⋙
              PresheafOfModules.evaluation S.ringCatSheaf.obj (Opposite.op V) ⋙
              forget₂ (ModuleCat.{u} (S.ringCatSheaf.obj.obj (Opposite.op V)))
                AddCommGrpCat.{u} ≅
            derivedRestrictModule.{u + 1, u + 1} B S hS ⋙
              @Stacks.Cohomology.Localization.derivedSectionsOverObject S.zariskiRingedSite V
                (inferInstance : HasDerivedCategory.{u + 1} (SheafOfModules.{u} S.ringCatSheaf)) _ ⋙
              DerivedCategory.homologyFunctor AddCommGrpCat.{u} i) :=
  ⟨higherDirectImageIsoSheafifyCohomologyPresheafRestrictModule B S hS i,
    fun V => cohomologyPresheafSourceValueRestrictModuleIso B S hS V i,
    fun V => cohomologyPresheafEvaluationRestrictModuleIso B S hS V i⟩

end StandardDerivedCategory

end AlgebraicGeometry.SmallEtale

end
