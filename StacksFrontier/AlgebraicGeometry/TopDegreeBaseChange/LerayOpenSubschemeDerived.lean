module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.LerayOpenSubschemeSections

/-!
# The derived packaging of the open-subscheme crossing at the source of the Leray comparison

`LerayOpenSubschemeSections.lean` builds the **degreewise** crossing
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.preimageSectionsOpenSubschemeIso` of the source of
the Leray comparison of [Stacks, Tag 0D5W] for `f : X ⟶ S` over an open `V ⊆ S` with its source
for the restricted morphism `f ∣_ V` over `⊤`, and builds it twice — once by the sections route
that the `γ⁺` side of conclusion (c) of [Stacks, Tag 0EX3] presents, once by the direct-image
route that the `ψ` side presents — and proves the two routes equal.

This file derives that crossing. Both of the functors the crossing compares are degreewise, and
both of them have a *distinguished* right derived functor on the two sides of the Leray
comparison:

* `Stacks.Cohomology.DerivedSectionsLeray.derivedPreimageSections f V`, the total right derived
  functor of sections over `f⁻¹V`, which is the Leray comparison's source; and
* `Rf_* ⋙ RΓ(V, -)`, its target, which is a right derived functor of the *same* degreewise
  functor with unit `Stacks.Cohomology.DerivedSectionsLeray.lerayUnit f V` — that is exactly what
  `Stacks.Cohomology.DerivedSectionsLeray.isIso_lerayComparison` establishes, and
  `isRightDerivedFunctor_lerayUnit` below reads it off rather than re-proving it.

So the crossing has **two** derived forms, one descending from each, and the compatibility of the
Leray comparison with the crossing is the statement that the first is the Leray comparison
followed by the second. Since both are transformations out of `RΓ(f⁻¹V, -)`,
`Stacks.Cohomology.DerivedSectionsLeray.lerayComparison_ext` applies, and the two descents are
determined by their composites with the derived-functor units; those are the two degreewise
routes, which `preimageSectionsOpenSubschemeIso_eq` identifies.

`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPushforward/LerayRestrictSections.lean` is the
template, one for one: a `…HomotopyIso` splitting the composite off the homotopy category, a
`…Unit`, the `rightDerivedDesc`, and a `…_fac_app` with
its `…_fac_app_comp` form.

## Main definitions

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.openSubschemeRestriction` — restriction of sheaves
  of modules to the open subscheme `f⁻¹V`, with its target ascribed to the open subscheme's own
  structure sheaf. This is `Stacks.Cohomology.HigherDirectImage.moduleRestriction` and nothing
  else; the ascription is forced by instance synthesis, see the implementation notes.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedPreimageSectionsOpenSubscheme` — the
  derived target: derived restriction to the open subscheme `f⁻¹V`, then derived sections over
  `(f ∣_ V)⁻¹⊤`, then derived restriction of scalars along
  `AlgebraicGeometry.Scheme.Opens.topIso` at `V`.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.preimageSectionsOpenSubschemeHomotopyIso` and
  `…preimageSectionsTopRestrictHomotopyIso` — the splitting of the two *exact* factors of the
  degreewise target off the homotopy category.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.openSubschemeUnitOfIsoUnit` — the transformation
  into `Qh ⋙ openSubschemeDerivedTarget` that the universal property consumes, built from an
  arbitrary presentation of the degreewise crossing and an arbitrary unit upstairs;
  `…openSubschemeUnitOfIso` fixes the upstairs unit to the one of `RΓ((f ∣_ V)⁻¹⊤, -)`, and
  `…openSubschemeSectionsUnit` (the `γ⁺` route), `…openSubschemePushforwardUnit` (the `ψ` route)
  and `…openSubschemeLerayUnit` (the `ψ` route with the Leray comparison's target upstairs) are
  its three values.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.openSubschemeSectionsComparison`,
  `…openSubschemePushforwardComparison` and `…openSubschemeLerayComparison` — the three derived
  crossings: out of `RΓ(f⁻¹V, -)`, and twice out of `Rf_* ⋙ RΓ(V, -)`, the last into the target
  the Leray comparison for `f ∣_ V` over `⊤` lands in.

## Main results

* `Stacks.Cohomology.DerivedSectionsLeray.isRightDerivedFunctor_lerayUnit` — the target of the
  Leray comparison is a right derived functor of degreewise sections over `f⁻¹V` at `lerayUnit`.
  Nothing is proved: it is `isIso_lerayComparison` read through
  `CategoryTheory.Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc`, the Leray comparison
  being by definition the `rightDerivedDesc` at `lerayUnit`.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.openSubschemeSectionsUnit_eq` — the two routes'
  units agree, by `preimageSectionsOpenSubschemeIso_eq`.
* `…openSubschemeSectionsComparison_fac_app`, `…_fac_app_comp`,
  `…openSubschemePushforwardComparison_fac_app`, `…_fac_app_comp` — the factorizations that
  characterize the two derived crossings.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.openSubschemeUnitOfIsoUnit_comp` — composing a
  transformation of the upstairs derived functors onto the unit, by the naturality of that
  transformation and nothing else.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.openSubschemeSectionsComparison_eq` — **the
  compatibility of the Leray comparison with the open-subscheme crossing of its source.** There is
  no hypothesis on `f`, on `V` or on the module.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange`
  `.openSubschemeSectionsComparison_comp_lerayComparison_eq` — **the compatibility of the Leray
  comparison of [Stacks, Tag 0D5W] with restriction to an open subscheme**: the crossing of the
  source followed by the Leray comparison for `f ∣_ V` over `⊤` is the Leray comparison for `f`
  over `V` followed by the crossing out of its target. No hypothesis on `f` and none on `V`.

## Implementation notes

*Why the derived target is spelled with `mapDerivedCategory` twice.* Restriction to an open
subspace and restriction of scalars are both exact, so each is its own derived functor and
`CategoryTheory.Functor.mapDerivedCategory` applies; only sections are derived. The restriction to
the open subscheme is the **ringed-space** functor
`Stacks.Cohomology.HigherDirectImage.moduleRestriction`, for the reason
`LerayOpenSubschemeSections.lean` records: `HasDerivedCategory X.Modules` is not synthesisable,
while everything at the `SheafOfModules (structureSheafRing _)` spelling is found.

*The one instance crossing, paid once.* That restriction's declared target is the
modules on `…HigherDirectImage.restrictToOpen X.toRingedSpace (f ⁻¹ᵁ V)`, and the sections functor
it is composed with has source the modules on `(f ⁻¹ᵁ V : Scheme).toRingedSpace`. The two are
definitionally equal and are the recorded spelling pair that instance synthesis cannot cross: the
`CategoryTheory.Functor.Additive` subgoal that
`CategoryTheory.Functor.mapHomotopyCategoryCompIso` generates for the composite
carries the `restrictToOpen` spelling, where neither the declared additivity of
`…DerivedSectionsLeray.preimageSections` nor `CategoryTheory.Functor.instAdditiveComp` applies —
even though both factors are additive and `Functor.instAdditiveComp _ _` inhabits the composite's
additivity when it is asked for on its own. Rather than restate an instance at each composite,
`openSubschemeRestriction` names the restriction with the *other* spelling as its declared target
and carries the three exactness instances across by `inferInstanceAs`, in term mode, where the
conversion runs at default transparency. Every composite below is then in one spelling.

*Why the unit is built from an arbitrary presentation of the degreewise crossing and an arbitrary
unit upstairs.* The two routes are equal but are not the same term, and both are wanted: the `γ⁺`
side of conclusion (c) meets the first and the `ψ` side the second. Building the unit as
`openSubschemeUnitOfIsoUnit` applied to a variable isomorphism makes the two units' equality a
`congrArg` on `preimageSectionsOpenSubschemeIso_eq`, instead of a second traversal of the four
factors. And leaving the upstairs unit variable makes carrying the Leray comparison for `f ∣_ V`
through the whole crossing one lemma at variables, `openSubschemeUnitOfIsoUnit_comp`, whose
content is the naturality of that comparison at one morphism: no factor of the crossing is
unfolded and no reassociation is performed.

*Why [Stacks, Tag 08FE] is not used.* The two Leray comparisons' **targets** — `RΓ(V, -) ∘ Rf_*` and
`RΓ(⊤, -) ∘ R(f ∣_ V)_*` after the restriction — are indeed related by no crossing of sections,
and 08FE (proved; see `DerivedPushforwardOpenSubscheme.lean` for its bridge to this file's
restriction spelling) is one way to relate them. But the universal property does not ask for an
isomorphism of the two targets: it asks for a **transformation** out of `Rf_* ⋙ RΓ(V, -)`, and the
degreewise `ψ` route followed by `lerayUnit (f ∣_ V) ⊤` is one. That is
`openSubschemeLerayComparison`, and it is why
`openSubschemeSectionsComparison_comp_lerayComparison_eq` carries no 08FE.

*Where `rw` gives way to term mode.* Three of the rewrites this file would
naturally use exhaust the 200,000-heartbeat budget and the terms that replace them are instant:
`rw [hnat]` for the naturality step of `openSubschemeUnitOfIsoUnit_comp` (three nested `congrArg`s
instead); `rw [openSubschemeLerayComparison_fac_app …]` on a goal that displays exactly its
left-hand side (an `Eq.trans` instead); and `rw [Category.assoc _ _ _, …]` in the last theorem
(the `Category.assoc` term and a `congrArg` instead). This is the usual `rw`-versus-term
pattern of this development.

*No `@[stacks …]` attribute is placed.* [Stacks, Tag 0D5W] carries its attribute where the Leray
comparison is proved invertible, and conclusion (c) of [Stacks, Tag 0EX3] is proved elsewhere, as
`…TopDegreeBaseChange.isIso_topDirectImageBaseChangeMap` (`BaseChangeTopDegreeConclusion.lean`), by
a route that does not use this file.

## References

* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.HigherDirectImage (moduleRestriction)
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPushforward)
open Stacks.Cohomology.DerivedSectionsLeray
  (sectionsOverOpen preimageSections homotopyPreimageSections derivedPreimageSections
    derivedPreimageSectionsUnit derivedSectionsOverOpen lerayUnit lerayComparison
    lerayComparison_ext lerayComparison_fac lerayComparison_fac_app_comp isIso_lerayComparison)

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.Cohomology.DerivedSectionsLeray

/-- **The target of the Leray comparison is a right derived functor of degreewise sections over
`f⁻¹V`, at `lerayUnit`.** For a morphism `f : X ⟶ Y` of ringed spaces and an open `V ⊆ Y`, the
composite `Rf_* ⋙ RΓ(V, -)` together with `lerayUnit f V` satisfies the universal property of the
total right derived functor of `Γ(f⁻¹V, -)`.

Nothing is proved here. `lerayComparison f V` *is*
`CategoryTheory.Functor.rightDerivedDesc` at `lerayUnit f V`, so
`CategoryTheory.Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc` read right to left at
`isIso_lerayComparison f V` ([Stacks, Tag 0D5W]) supplies the instance. It is seated as an
instance so that a further `rightDerivedDesc` out of the Leray comparison's target can be
written down. -/
instance isRightDerivedFunctor_lerayUnit {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (V : Opens Y.carrier) :
    (derivedPushforward f ⋙ derivedSectionsOverOpen Y V).IsRightDerivedFunctor (lerayUnit f V)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X))
        (ComplexShape.up ℤ)) :=
  (Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc _ (derivedPreimageSectionsUnit f V)
    _ _ (lerayUnit f V)).2 (isIso_lerayComparison f V)

end Stacks.Cohomology.DerivedSectionsLeray

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

variable {X S : Scheme.{u}} (f : X ⟶ S) (V : S.Opens)

/-! ### Restriction to the open subscheme, at the open subscheme's own structure sheaf

`Stacks.Cohomology.HigherDirectImage.moduleRestriction X.toRingedSpace (f ⁻¹ᵁ V)` has target the
modules on `…HigherDirectImage.restrictToOpen X.toRingedSpace (f ⁻¹ᵁ V)`, while
`Stacks.Cohomology.DerivedSectionsLeray.preimageSections (f ∣_ V) ⊤` has source the modules on
`(f ⁻¹ᵁ V : Scheme).toRingedSpace`. The two spellings are definitionally equal — the degreewise
crossing of `LerayOpenSubschemeSections.lean` is stated across them — but they are the recorded
spelling pair that is **not** interchangeable for instance synthesis, and that bites as soon as
the composite is asked for an additive structure: the subgoal
`CategoryTheory.Functor.Additive` that `CategoryTheory.Functor.mapHomotopyCategoryCompIso`
generates for the last two factors carries the `restrictToOpen X.toRingedSpace (f ⁻¹ᵁ V)`
spelling, and there neither the declared additivity of
`…DerivedSectionsLeray.preimageSections` nor `CategoryTheory.Functor.instAdditiveComp` applies.

So the restriction is given a name whose *declared* target is the open subscheme's own structure
sheaf, with its three exactness instances carried over by `inferInstanceAs` — term mode, where
the conversion runs at default transparency. Every composite below is then written in one
spelling and instance search needs no help. -/

/-- **Restriction of sheaves of modules to the open subscheme `f⁻¹V`**, with the target ascribed
to the modules on `(f ⁻¹ᵁ V : Scheme).toRingedSpace`.

This is `Stacks.Cohomology.HigherDirectImage.moduleRestriction X.toRingedSpace (f ⁻¹ᵁ V)` and
nothing else; the ascription is not cosmetic, see this section's note. It is a `def` and not an
`abbrev` on purpose: were it reducible, instance search would unfold it and land back on the
spelling whose instances it cannot use. -/
def openSubschemeRestriction :
    SheafOfModules.{u} (structureSheafRing X.toRingedSpace) ⥤
      SheafOfModules.{u} (structureSheafRing (f ⁻¹ᵁ V : Scheme).toRingedSpace) :=
  moduleRestriction X.toRingedSpace (f ⁻¹ᵁ V)

/-- Restriction to the open subscheme is additive. -/
instance openSubschemeRestriction_additive : (openSubschemeRestriction f V).Additive :=
  inferInstanceAs ((moduleRestriction X.toRingedSpace (f ⁻¹ᵁ V)).Additive)

/-- Restriction to the open subscheme is left exact. -/
instance openSubschemeRestriction_preservesFiniteLimits :
    PreservesFiniteLimits (openSubschemeRestriction f V) :=
  inferInstanceAs (PreservesFiniteLimits (moduleRestriction X.toRingedSpace (f ⁻¹ᵁ V)))

/-- Restriction to the open subscheme is right exact. -/
instance openSubschemeRestriction_preservesFiniteColimits :
    PreservesFiniteColimits (openSubschemeRestriction f V) :=
  inferInstanceAs (PreservesFiniteColimits (moduleRestriction X.toRingedSpace (f ⁻¹ᵁ V)))

/-! ### The derived target -/

/-- **The open-subscheme reading of sections over `f⁻¹V`, with the upstairs derived functor left
open.** Derived restriction to the open subscheme `f⁻¹V`, then a functor `RP` out of the derived
category upstairs, then derived restriction of scalars along
`AlgebraicGeometry.Scheme.Opens.topIso` at `V`: a functor `D(𝒪_X) ⥤ D(Γ(S, V))`.

The two outer factors are exact, so each is its own derived functor and
`CategoryTheory.Functor.mapDerivedCategory` applies; only `RP` is derived, and it is left variable
because the chain below meets it at two values — `RΓ((f ∣_ V)⁻¹⊤, -)` and
`R(f ∣_ V)_* ⋙ RΓ(V, ⊤)`, the Leray comparison's two sides upstairs. -/
abbrev openSubschemeDerivedTarget
    (RP : DerivedCategory (SheafOfModules.{u}
        (structureSheafRing (f ⁻¹ᵁ V : Scheme).toRingedSpace)) ⥤
      DerivedCategory (ModuleCat.{u}
        ((structureSheafRing (V : Scheme).toRingedSpace).obj.obj (op ⊤)))) :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) ⥤
      DerivedCategory (ModuleCat.{u} ((structureSheafRing S.toRingedSpace).obj.obj (op V))) :=
  (openSubschemeRestriction f V).mapDerivedCategory ⋙
    RP ⋙ (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom).mapDerivedCategory

/-- **The derived form of the open-subscheme reading of sections over `f⁻¹V`.** Derived
restriction to the open subscheme `f⁻¹V`, then derived sections over `(f ∣_ V)⁻¹⊤`, then derived
restriction of scalars along `AlgebraicGeometry.Scheme.Opens.topIso` at `V`.

This is `openSubschemeDerivedTarget` at `RΓ((f ∣_ V)⁻¹⊤, -)`: the functor that
`preimageSectionsOpenSubschemeIso` becomes once the sections are derived. -/
abbrev derivedPreimageSectionsOpenSubscheme :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) ⥤
      DerivedCategory (ModuleCat.{u} ((structureSheafRing S.toRingedSpace).obj.obj (op V))) :=
  openSubschemeDerivedTarget f V (derivedPreimageSections (f ∣_ V).toLRSHom.toShHom ⊤)

/-- **The same with the Leray comparison's target upstairs.** `openSubschemeDerivedTarget` at
`R(f ∣_ V)_* ⋙ RΓ(V, ⊤)`: derived restriction to `f⁻¹V`, the derived direct image along
`f ∣_ V`, global derived sections of the open subscheme `V`, and the restriction of scalars. -/
abbrev derivedPushforwardSectionsOpenSubscheme :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) ⥤
      DerivedCategory (ModuleCat.{u} ((structureSheafRing S.toRingedSpace).obj.obj (op V))) :=
  openSubschemeDerivedTarget f V
    (derivedPushforward (f ∣_ V).toLRSHom.toShHom ⋙
      derivedSectionsOverOpen (V : Scheme).toRingedSpace ⊤)

/-! ### Splitting the exact factors off the homotopy category -/

/-- Restriction of scalars along `AlgebraicGeometry.Scheme.Opens.topIso` at `V` commutes with
passing to the derived category: degreewise sections over `(f ∣_ V)⁻¹⊤` read over `Γ(S, V)`,
localized, is those sections localized and then followed by the derived functor of restriction of
scalars. This is the inner half of `preimageSectionsOpenSubschemeHomotopyIso`. -/
def preimageSectionsTopRestrictHomotopyIso :
    (preimageSections (f ∣_ V).toLRSHom.toShHom ⊤ ⋙
          ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ≅
      (preimageSections (f ∣_ V).toLRSHom.toShHom ⊤).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⋙
          (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom).mapDerivedCategory :=
  (Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryCompIso
        (Iso.refl (preimageSections (f ∣_ V).toLRSHom.toShHom ⊤ ⋙
          ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom)) (ComplexShape.up ℤ))
      DerivedCategory.Qh).symm ≪≫
    Functor.isoWhiskerLeft
      ((preimageSections (f ∣_ V).toLRSHom.toShHom ⊤).mapHomotopyCategory (ComplexShape.up ℤ))
      (ModuleCat.restrictScalars
        (Scheme.Opens.topIso V).inv.hom).mapDerivedCategoryFactorsh.symm

/-- **The two exact factors of the degreewise target split off the homotopy category.** The
degreewise target of `preimageSectionsOpenSubschemeIso`, read on the homotopy category and
localized, is restriction to the open subscheme on the homotopy category, then degreewise sections
over `(f ∣_ V)⁻¹⊤` localized, then the derived functor of restriction of scalars.

Only `CategoryTheory.Functor.mapHomotopyCategoryCompIso` at identity isomorphisms and
`CategoryTheory.Functor.mapDerivedCategoryFactorsh` for the two exact factors are used; nothing
is derived yet. -/
def preimageSectionsOpenSubschemeHomotopyIso :
    (openSubschemeRestriction f V ⋙
            preimageSections (f ∣_ V).toLRSHom.toShHom ⊤ ⋙
              ModuleCat.restrictScalars
                (Scheme.Opens.topIso V).inv.hom).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh ≅
      (openSubschemeRestriction f V).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (preimageSections (f ∣_ V).toLRSHom.toShHom ⊤).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh ⋙
            (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom).mapDerivedCategory :=
  (Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryCompIso
        (Iso.refl (openSubschemeRestriction f V ⋙
          preimageSections (f ∣_ V).toLRSHom.toShHom ⊤ ⋙
            ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom)) (ComplexShape.up ℤ))
      DerivedCategory.Qh).symm ≪≫
    Functor.isoWhiskerLeft
      ((openSubschemeRestriction f V).mapHomotopyCategory (ComplexShape.up ℤ))
      (preimageSectionsTopRestrictHomotopyIso f V)

/-! ### The unit the universal property consumes -/

/-- **The transformation the universal property consumes, from an arbitrary presentation of the
degreewise crossing and an arbitrary unit upstairs.** Given an isomorphism `α` of degreewise
sections over `f⁻¹V` with their open-subscheme reading, and a transformation `u` from degreewise
sections over `(f ∣_ V)⁻¹⊤` into a functor `RP` on the derived category, the canonical
transformation from degreewise sections over `f⁻¹V` into `Qh ⋙ openSubschemeDerivedTarget f V RP`:
`α` on the homotopy category, the splitting of the two exact factors, `u`, and the comparison of
restriction to the open subscheme with localization.

Both arguments are variable on purpose. `α` is, so that the two routes of
`LerayOpenSubschemeSections.lean` give two units whose equality is a `congrArg`
(`openSubschemeSectionsUnit_eq`); and `u` is, so that composing a transformation of the upstairs
derived functors onto the result is one lemma at variables
(`openSubschemeUnitOfIsoUnit_comp`), which is what carries the Leray comparison upstairs through
the whole crossing. -/
def openSubschemeUnitOfIsoUnit
    (α : preimageSections f.toLRSHom.toShHom V ≅
      openSubschemeRestriction f V ⋙
        preimageSections (f ∣_ V).toLRSHom.toShHom ⊤ ⋙
          ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom)
    {RP : DerivedCategory (SheafOfModules.{u}
        (structureSheafRing (f ⁻¹ᵁ V : Scheme).toRingedSpace)) ⥤
      DerivedCategory (ModuleCat.{u}
        ((structureSheafRing (V : Scheme).toRingedSpace).obj.obj (op ⊤)))}
    (u : (preimageSections (f ∣_ V).toLRSHom.toShHom ⊤).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RP) :
    homotopyPreimageSections f.toLRSHom.toShHom V ⟶
      DerivedCategory.Qh ⋙ openSubschemeDerivedTarget f V RP :=
  Functor.whiskerRight (NatTrans.mapHomotopyCategory α.hom (ComplexShape.up ℤ))
      DerivedCategory.Qh ≫
    (preimageSectionsOpenSubschemeHomotopyIso f V).hom ≫
    Functor.whiskerLeft
        ((openSubschemeRestriction f V).mapHomotopyCategory (ComplexShape.up ℤ))
        (Functor.whiskerRight u
          (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom).mapDerivedCategory) ≫
    Functor.whiskerRight
      (openSubschemeRestriction f V).mapDerivedCategoryFactorsh.inv
      (RP ⋙ (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom).mapDerivedCategory)

/-- **The unit at a presentation of the degreewise crossing**, with the upstairs unit the one of
`RΓ((f ∣_ V)⁻¹⊤, -)`: `openSubschemeUnitOfIsoUnit` at
`Stacks.Cohomology.DerivedSectionsLeray.derivedPreimageSectionsUnit`. -/
def openSubschemeUnitOfIso
    (α : preimageSections f.toLRSHom.toShHom V ≅
      openSubschemeRestriction f V ⋙
        preimageSections (f ∣_ V).toLRSHom.toShHom ⊤ ⋙
          ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom) :
    homotopyPreimageSections f.toLRSHom.toShHom V ⟶
      DerivedCategory.Qh ⋙ derivedPreimageSectionsOpenSubscheme f V :=
  openSubschemeUnitOfIsoUnit f V α (derivedPreimageSectionsUnit (f ∣_ V).toLRSHom.toShHom ⊤)

/-- **Composing a transformation of the upstairs derived functors onto the unit.** For `L` a
transformation of the two functors the crossing may land in upstairs, the unit built from `u ≫ L`
is the unit built from `u`, followed by `L` whiskered by the derived restriction on the left and by
the derived restriction of scalars on the right.

Only the last two factors of `openSubschemeUnitOfIsoUnit` are touched: the comparison of
restriction to the open subscheme with localization is carried past `L` by `L`'s naturality, and
nothing else is looked inside. There is no hypothesis on `α`, on `u` or on `L`. -/
theorem openSubschemeUnitOfIsoUnit_comp
    (α : preimageSections f.toLRSHom.toShHom V ≅
      openSubschemeRestriction f V ⋙
        preimageSections (f ∣_ V).toLRSHom.toShHom ⊤ ⋙
          ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom)
    {RP RQ : DerivedCategory (SheafOfModules.{u}
        (structureSheafRing (f ⁻¹ᵁ V : Scheme).toRingedSpace)) ⥤
      DerivedCategory (ModuleCat.{u}
        ((structureSheafRing (V : Scheme).toRingedSpace).obj.obj (op ⊤)))}
    (u : (preimageSections (f ∣_ V).toLRSHom.toShHom ⊤).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RP)
    (L : RP ⟶ RQ) :
    openSubschemeUnitOfIsoUnit f V α (u ≫ Functor.whiskerLeft DerivedCategory.Qh L) =
      openSubschemeUnitOfIsoUnit f V α u ≫
        Functor.whiskerLeft DerivedCategory.Qh
          (Functor.whiskerLeft (openSubschemeRestriction f V).mapDerivedCategory
            (Functor.whiskerRight L
              (ModuleCat.restrictScalars
                (Scheme.Opens.topIso V).inv.hom).mapDerivedCategory)) := by
  ext K
  have hnat := congrArg
    (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom).mapDerivedCategory.map
    (L.naturality ((openSubschemeRestriction f V).mapDerivedCategoryFactorsh.inv.app K))
  simp only [Functor.map_comp] at hnat
  dsimp only [openSubschemeUnitOfIsoUnit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.comp_map]
  simp only [Category.assoc, Functor.map_comp]
  exact congrArg _ (congrArg _ (congrArg _ hnat.symm))

/-- The unit of the `γ⁺` side's route: `openSubschemeUnitOfIso` at the sections presentation
`preimageSectionsOpenSubschemeIso` of the degreewise crossing. -/
def openSubschemeSectionsUnit :
    homotopyPreimageSections f.toLRSHom.toShHom V ⟶
      DerivedCategory.Qh ⋙ derivedPreimageSectionsOpenSubscheme f V :=
  openSubschemeUnitOfIso f V (preimageSectionsOpenSubschemeIso f V)

/-- The unit of the `ψ` side's route: `openSubschemeUnitOfIso` at the direct-image presentation
`preimageSectionsOpenSubschemePushforwardIso` of the degreewise crossing. -/
def openSubschemePushforwardUnit :
    homotopyPreimageSections f.toLRSHom.toShHom V ⟶
      DerivedCategory.Qh ⋙ derivedPreimageSectionsOpenSubscheme f V :=
  openSubschemeUnitOfIso f V (preimageSectionsOpenSubschemePushforwardIso f V)

/-- **The two routes' units agree.** This is `preimageSectionsOpenSubschemeIso_eq` carried through
`openSubschemeUnitOfIso`; no factor of either route is looked inside. -/
theorem openSubschemeSectionsUnit_eq :
    openSubschemeSectionsUnit f V = openSubschemePushforwardUnit f V :=
  congrArg (openSubschemeUnitOfIso f V) (preimageSectionsOpenSubschemeIso_eq f V)

/-! ### The derived crossing out of derived sections over the inverse image -/

/-- **The derived crossing, descending from `RΓ(f⁻¹V, -)`.** The transformation
`RΓ(f⁻¹V, -) ⟶ derivedPreimageSectionsOpenSubscheme` induced by `openSubschemeSectionsUnit`
through the universal property of the total right derived functor of sections over `f⁻¹V`. By
`openSubschemeSectionsComparison_fac_app` its composite with the derived-functor unit is that
unit, and that equation determines it. -/
def openSubschemeSectionsComparison :
    derivedPreimageSections f.toLRSHom.toShHom V ⟶ derivedPreimageSectionsOpenSubscheme f V :=
  (derivedPreimageSections f.toLRSHom.toShHom V).rightDerivedDesc
    (derivedPreimageSectionsUnit f.toLRSHom.toShHom V)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (ComplexShape.up ℤ)) _ (openSubschemeSectionsUnit f V)

/-- The factorization of `rightDerivedDesc` through the unit, for the derived category of the
sheaves of modules on `X`, at an object of the homotopy category. -/
private theorem unit_app_comp_rightDerivedDesc_app {H : Type*} [Category H]
    {F : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (ComplexShape.up ℤ) ⥤ H}
    {RF : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) ⥤ H}
    (α : F ⟶ DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) (ComplexShape.up ℤ))]
    {G : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) ⥤ H}
    (β : F ⟶ DerivedCategory.Qh ⋙ G)
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (ComplexShape.up ℤ)) :
    α.app K ≫ (RF.rightDerivedDesc α (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) (ComplexShape.up ℤ)) G β).app
        (DerivedCategory.Qh.obj K) = β.app K :=
  RF.rightDerived_fac_app α _ G β K

/-- The equation characterizing `openSubschemeSectionsComparison`, pointwise: composing it with the
unit of `RΓ(f⁻¹V, -)` recovers `openSubschemeSectionsUnit`. -/
theorem openSubschemeSectionsComparison_fac_app
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (ComplexShape.up ℤ)) :
    (derivedPreimageSectionsUnit f.toLRSHom.toShHom V).app K ≫
        (openSubschemeSectionsComparison f V).app (DerivedCategory.Qh.obj K) =
      (openSubschemeSectionsUnit f V).app K :=
  unit_app_comp_rightDerivedDesc_app _ _ K

/-- `openSubschemeSectionsComparison_fac_app` with a further morphism appended, the form in which a
rewrite inside a longer composite uses it. -/
theorem openSubschemeSectionsComparison_fac_app_comp
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (ComplexShape.up ℤ))
    {T : DerivedCategory (ModuleCat.{u} ((structureSheafRing S.toRingedSpace).obj.obj (op V)))}
    (g : (derivedPreimageSectionsOpenSubscheme f V).obj (DerivedCategory.Qh.obj K) ⟶ T) :
    (derivedPreimageSectionsUnit f.toLRSHom.toShHom V).app K ≫
        (openSubschemeSectionsComparison f V).app (DerivedCategory.Qh.obj K) ≫ g =
      (openSubschemeSectionsUnit f V).app K ≫ g := by
  rw [← Category.assoc, openSubschemeSectionsComparison_fac_app]

/-! ### The derived crossing out of the Leray comparison's target -/

/-- **The derived crossing, descending from `Rf_* ⋙ RΓ(V, -)`.** The transformation
`Rf_* ⋙ RΓ(V, -) ⟶ derivedPreimageSectionsOpenSubscheme` induced by
`openSubschemePushforwardUnit` through the universal property that
`Stacks.Cohomology.DerivedSectionsLeray.isRightDerivedFunctor_lerayUnit` records for the Leray
comparison's target. -/
def openSubschemePushforwardComparison :
    derivedPushforward f.toLRSHom.toShHom ⋙ derivedSectionsOverOpen S.toRingedSpace V ⟶
      derivedPreimageSectionsOpenSubscheme f V :=
  (derivedPushforward f.toLRSHom.toShHom ⋙
      derivedSectionsOverOpen S.toRingedSpace V).rightDerivedDesc
    (lerayUnit f.toLRSHom.toShHom V)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (ComplexShape.up ℤ)) _ (openSubschemePushforwardUnit f V)

/-- The equation characterizing `openSubschemePushforwardComparison`, pointwise: composing it with
`lerayUnit` recovers `openSubschemePushforwardUnit`. -/
theorem openSubschemePushforwardComparison_fac_app
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (ComplexShape.up ℤ)) :
    (lerayUnit f.toLRSHom.toShHom V).app K ≫
        (openSubschemePushforwardComparison f V).app (DerivedCategory.Qh.obj K) =
      (openSubschemePushforwardUnit f V).app K :=
  unit_app_comp_rightDerivedDesc_app _ _ K

/-- `openSubschemePushforwardComparison_fac_app` with a further morphism appended, the form in
which a rewrite inside a longer composite uses it. -/
theorem openSubschemePushforwardComparison_fac_app_comp
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (ComplexShape.up ℤ))
    {T : DerivedCategory (ModuleCat.{u} ((structureSheafRing S.toRingedSpace).obj.obj (op V)))}
    (g : (derivedPreimageSectionsOpenSubscheme f V).obj (DerivedCategory.Qh.obj K) ⟶ T) :
    (lerayUnit f.toLRSHom.toShHom V).app K ≫
        (openSubschemePushforwardComparison f V).app (DerivedCategory.Qh.obj K) ≫ g =
      (openSubschemePushforwardUnit f V).app K ≫ g := by
  rw [← Category.assoc, openSubschemePushforwardComparison_fac_app]

/-! ### The compatibility -/

/-- **The Leray comparison is compatible with the open-subscheme crossing of its source.** For a
morphism of schemes `f : X ⟶ S` and an open `V ⊆ S`, the derived crossing out of `RΓ(f⁻¹V, -)` is
the Leray comparison of [Stacks, Tag 0D5W] followed by the derived crossing out of
`Rf_* ⋙ RΓ(V, -)`. Both sides are transformations
`RΓ(f⁻¹V, -) ⟶ derivedPreimageSectionsOpenSubscheme f V` of functors
`D(𝒪_X) ⥤ D(Γ(S, V))`. There is no hypothesis on `f` and none on `V`.

Both sides come out of the total right derived functor `RΓ(f⁻¹V, -)`, so
`Stacks.Cohomology.DerivedSectionsLeray.lerayComparison_ext` reduces the statement to the
composites with the derived-functor unit; the two factorizations and
`Stacks.Cohomology.DerivedSectionsLeray.lerayComparison_fac_app_comp` collapse those to the two
routes' units, which agree by `openSubschemeSectionsUnit_eq`. -/
theorem openSubschemeSectionsComparison_eq :
    openSubschemeSectionsComparison f V =
      lerayComparison f.toLRSHom.toShHom V ≫ openSubschemePushforwardComparison f V := by
  apply lerayComparison_ext f.toLRSHom.toShHom V
  ext K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app]
  rw [openSubschemeSectionsComparison_fac_app f V K, lerayComparison_fac_app_comp,
    openSubschemePushforwardComparison_fac_app f V K, openSubschemeSectionsUnit_eq]

/-! ### The two Leray comparisons -/

/-- The unit of the `ψ` route with the **Leray comparison's target** upstairs:
`openSubschemeUnitOfIsoUnit` at the direct-image presentation of the degreewise crossing and at
`Stacks.Cohomology.DerivedSectionsLeray.lerayUnit (f ∣_ V) ⊤`. -/
def openSubschemeLerayUnit :
    homotopyPreimageSections f.toLRSHom.toShHom V ⟶
      DerivedCategory.Qh ⋙ derivedPushforwardSectionsOpenSubscheme f V :=
  openSubschemeUnitOfIsoUnit f V (preimageSectionsOpenSubschemePushforwardIso f V)
    (lerayUnit (f ∣_ V).toLRSHom.toShHom ⊤)

/-- **The `ψ` unit followed by the Leray comparison upstairs is the `ψ` unit with the Leray
comparison's target upstairs.** This is
`Stacks.Cohomology.DerivedSectionsLeray.lerayComparison_fac` for `f ∣_ V` over `⊤` carried through
`openSubschemeUnitOfIsoUnit_comp`; nothing is assumed of `f` or of `V`. -/
theorem openSubschemePushforwardUnit_comp_lerayComparison :
    openSubschemePushforwardUnit f V ≫
        Functor.whiskerLeft DerivedCategory.Qh
          (Functor.whiskerLeft (openSubschemeRestriction f V).mapDerivedCategory
            (Functor.whiskerRight (lerayComparison (f ∣_ V).toLRSHom.toShHom ⊤)
              (ModuleCat.restrictScalars
                (Scheme.Opens.topIso V).inv.hom).mapDerivedCategory)) =
      openSubschemeLerayUnit f V :=
  (openSubschemeUnitOfIsoUnit_comp f V (preimageSectionsOpenSubschemePushforwardIso f V)
        (derivedPreimageSectionsUnit (f ∣_ V).toLRSHom.toShHom ⊤)
        (lerayComparison (f ∣_ V).toLRSHom.toShHom ⊤)).symm.trans
    (congrArg (openSubschemeUnitOfIsoUnit f V (preimageSectionsOpenSubschemePushforwardIso f V))
      (lerayComparison_fac (f ∣_ V).toLRSHom.toShHom ⊤))

/-- **The derived crossing out of the Leray comparison's target, with the Leray comparison's target
upstairs too.** The transformation
`Rf_* ⋙ RΓ(V, -) ⟶ derivedPushforwardSectionsOpenSubscheme f V` induced by
`openSubschemeLerayUnit` through the universal property that
`Stacks.Cohomology.DerivedSectionsLeray.isRightDerivedFunctor_lerayUnit` records. -/
def openSubschemeLerayComparison :
    derivedPushforward f.toLRSHom.toShHom ⋙ derivedSectionsOverOpen S.toRingedSpace V ⟶
      derivedPushforwardSectionsOpenSubscheme f V :=
  (derivedPushforward f.toLRSHom.toShHom ⋙
      derivedSectionsOverOpen S.toRingedSpace V).rightDerivedDesc
    (lerayUnit f.toLRSHom.toShHom V)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (ComplexShape.up ℤ)) _ (openSubschemeLerayUnit f V)

/-- The equation characterizing `openSubschemeLerayComparison`, pointwise. -/
theorem openSubschemeLerayComparison_fac_app
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (ComplexShape.up ℤ)) :
    (lerayUnit f.toLRSHom.toShHom V).app K ≫
        (openSubschemeLerayComparison f V).app (DerivedCategory.Qh.obj K) =
      (openSubschemeLerayUnit f V).app K :=
  unit_app_comp_rightDerivedDesc_app _ _ K

/-- `openSubschemeLerayComparison_fac_app` with a further morphism appended, the form in which a
rewrite inside a longer composite uses it. -/
theorem openSubschemeLerayComparison_fac_app_comp
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (ComplexShape.up ℤ))
    {T : DerivedCategory (ModuleCat.{u} ((structureSheafRing S.toRingedSpace).obj.obj (op V)))}
    (g : (derivedPushforwardSectionsOpenSubscheme f V).obj (DerivedCategory.Qh.obj K) ⟶ T) :
    (lerayUnit f.toLRSHom.toShHom V).app K ≫
        (openSubschemeLerayComparison f V).app (DerivedCategory.Qh.obj K) ≫ g =
      (openSubschemeLerayUnit f V).app K ≫ g := by
  rw [← Category.assoc, openSubschemeLerayComparison_fac_app]

/-- **The Leray comparison for `f` over `V` and the Leray comparison for `f ∣_ V` over `⊤` agree
across the open-subscheme crossing.** For a morphism of schemes `f : X ⟶ S` and an open `V ⊆ S`,
the derived crossing of the Leray comparison's source, followed by the Leray comparison of
[Stacks, Tag 0D5W] for the restricted morphism `f ∣_ V` over the whole of the open subscheme `V`,
is the Leray comparison for `f` over `V` followed by the derived crossing out of its target. Both
sides are transformations
`RΓ(f⁻¹V, -) ⟶ derivedPushforwardSectionsOpenSubscheme f V` of functors `D(𝒪_X) ⥤ D(Γ(S, V))`.

**There is no hypothesis on `f` and none on `V`**, and the two Leray comparisons are the existing
ones: nothing here re-proves [Stacks, Tag 0D5W], and [Stacks, Tag 08FE] is not used — the two
descents land in two targets that the Leray comparison upstairs already relates, so no comparison
of `Rf_*` with `R(f ∣_ V)_*` is needed.

Both sides come out of `RΓ(f⁻¹V, -)`, so
`Stacks.Cohomology.DerivedSectionsLeray.lerayComparison_ext` reduces the statement to the
composites with the derived-functor unit; the three factorizations collapse those to
`openSubschemePushforwardUnit` followed by the Leray comparison upstairs, and to
`openSubschemeLerayUnit`, which `openSubschemePushforwardUnit_comp_lerayComparison` identifies. -/
theorem openSubschemePushforwardComparison_comp_lerayComparison :
    openSubschemePushforwardComparison f V ≫
        Functor.whiskerLeft (openSubschemeRestriction f V).mapDerivedCategory
          (Functor.whiskerRight (lerayComparison (f ∣_ V).toLRSHom.toShHom ⊤)
            (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom).mapDerivedCategory) =
      openSubschemeLerayComparison f V := by
  apply (derivedPushforward f.toLRSHom.toShHom ⋙
      derivedSectionsOverOpen S.toRingedSpace V).rightDerived_ext
    (lerayUnit f.toLRSHom.toShHom V)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (ComplexShape.up ℤ))
  ext K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app]
  rw [openSubschemePushforwardComparison_fac_app_comp f V K]
  exact (NatTrans.congr_app (openSubschemePushforwardUnit_comp_lerayComparison f V) K).trans
    (openSubschemeLerayComparison_fac_app f V K).symm

/-- **The derived crossing of the Leray comparison's source, followed by the Leray comparison for
`f ∣_ V` over `⊤`, is the Leray comparison for `f` over `V` followed by the crossing of its
target.** For a morphism of schemes `f : X ⟶ S` and an open `V ⊆ S`,
`openSubschemeSectionsComparison` followed by the Leray comparison of [Stacks, Tag 0D5W] for
`f ∣_ V` over `⊤` equals the Leray comparison for `f` over `V` followed by
`openSubschemeLerayComparison`. There is no hypothesis on `f` and none on `V`. -/
theorem openSubschemeSectionsComparison_comp_lerayComparison_eq :
    openSubschemeSectionsComparison f V ≫
        Functor.whiskerLeft (openSubschemeRestriction f V).mapDerivedCategory
          (Functor.whiskerRight (lerayComparison (f ∣_ V).toLRSHom.toShHom ⊤)
            (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom).mapDerivedCategory) =
      lerayComparison f.toLRSHom.toShHom V ≫ openSubschemeLerayComparison f V := by
  rw [openSubschemeSectionsComparison_eq]
  exact (Category.assoc _ _ _).trans
    (congrArg _ (openSubschemePushforwardComparison_comp_lerayComparison f V))

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
