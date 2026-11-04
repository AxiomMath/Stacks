module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.LerayOpenSubschemeDerived
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.LerayOpenSubschemeSectionsLE

/-!
# The derived packaging of the open-subscheme crossing at a smaller open

`LerayOpenSubschemeSectionsLE.lean` builds the **degreewise** crossing
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.preimageSectionsOpenSubschemeLE` of the source of the
Leray comparison of [Stacks, Tag 0D5W] for `f : X ⟶ S` over an open `V ⊆ S` with its source for
the restricted morphism `AlgebraicGeometry.Scheme.Hom.resLE f V U e` over `⊤`, at an **arbitrary**
open `U ≤ f⁻¹V` of `X`. This file derives that crossing, and proves the compatibility of the two
Leray comparisons across it.

`LerayOpenSubschemeDerived.lean` is the template one for one; the only mathematical difference is
that at `U < f⁻¹V` the degreewise crossing is a plain transformation rather than an isomorphism —
it is the restriction of sections from `f⁻¹V` to `U` — so the unit the universal property consumes
is built from a transformation and not from an `Iso`. Nothing here needs it to be invertible: the
universal property of `RΓ(f⁻¹V, -)` asks only for a transformation out of the degreewise functor.

Both ends of the compatibility are right derived functors of the *same* degreewise functor
`Γ(f⁻¹V, -)`:

* `Stacks.Cohomology.DerivedSectionsLeray.derivedPreimageSections f V`, the Leray comparison's
  source; and
* `Rf_* ⋙ RΓ(V, -)`, its target, which is one at
  `Stacks.Cohomology.DerivedSectionsLeray.lerayUnit f V` by
  `Stacks.Cohomology.DerivedSectionsLeray.isRightDerivedFunctor_lerayUnit`
  (`LerayOpenSubschemeDerived.lean`).

So the crossing has two derived forms, one descending from each, and
`Stacks.Cohomology.DerivedSectionsLeray.lerayComparison_ext` compares them.

*Why this exists beside the `U = f⁻¹V` file, and why it is an addition and not a refactor.* The
tail of conclusion (c) of [Stacks, Tag 0EX3] meets [Stacks, Tag 089W] at the `resLE`
`h'.resLE (f'⁻¹V) (f''⁻¹W)`, upstairs open `f''⁻¹W`, while its `γ⁺` side reads the same factor at
the unrestricted `h'` over `f'⁻¹V`, upstairs open `h'⁻¹(f'⁻¹V)`. The two existing facts that name
`lerayComparison (h' ∣_ (f'⁻¹V)) ⊤` — `…DerivedSectionsLeray.lerayComparison_comp` at the pair
`((f''⁻¹W ↪ h'⁻¹(f'⁻¹V)), h' ∣_ (f'⁻¹V))`, and
`…TopDegreeBaseChange.openSubschemeSectionsComparison_comp_lerayComparison_eq` at `(h', f'⁻¹V)` —
name it in incompatible whiskerings and do not compose. The statement at an arbitrary `U` relates
`lerayComparison (f.resLE V U e) ⊤` to `lerayComparison f V` in one step, so neither of those two
facts is needed. The `ψ` half of the `U = f⁻¹V` file does **not** generalise, since
`(f.resLE V U e)_*(F|_U)` is not `(f_* F)|_V`; the pair
`…preimageSectionsOpenSubschemePushforwardIso` / `…preimageSectionsOpenSubschemeIso_eq` and the
second descent `…openSubschemePushforwardComparison` stay special to `U = f⁻¹V`, and this file does
not need them.

## Main definitions

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.openSubschemeRestrictionOf` — restriction of
  sheaves of modules to an open subscheme `U` of `X`, with its target ascribed to the open
  subscheme's own structure sheaf. `…openSubschemeRestriction f V` is its value at `U := f⁻¹V`,
  which `openSubschemeRestriction_eq` records; the ascription is forced by instance synthesis, see
  the implementation notes.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.openSubschemeDerivedTargetOf` — derived
  restriction to the open subscheme `U`, then a functor on the derived category upstairs, then
  derived restriction of scalars along `AlgebraicGeometry.Scheme.Opens.topIso` at `V`;
  `…derivedPreimageSectionsOpenSubschemeLE` and `…derivedPushforwardSectionsOpenSubschemeLE` are
  its two values at the Leray comparison's two sides upstairs.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.preimageSectionsOpenSubschemeHomotopyIsoLE` and
  `…preimageSectionsTopRestrictHomotopyIsoLE` — the splitting of the two *exact* factors of the
  degreewise target off the homotopy category.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.openSubschemeUnitOfNatTransUnit` — the
  transformation into `Qh ⋙ openSubschemeDerivedTargetOf` that the universal property consumes,
  from an arbitrary presentation of the degreewise crossing and an arbitrary unit upstairs;
  `…openSubschemeSectionsUnitLE` and `…openSubschemeLerayUnitLE` are its two values.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.openSubschemeSectionsComparisonLE` and
  `…openSubschemeLerayComparisonLE` — the two derived crossings, out of `RΓ(f⁻¹V, -)` and out of
  `Rf_* ⋙ RΓ(V, -)`.

## Main results

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.openSubschemeUnitOfNatTransUnit_comp` — composing
  a transformation of the upstairs derived functors onto the unit, by the naturality of that
  transformation and nothing else.
* `…openSubschemeSectionsComparisonLE_fac_app`, `…_fac_app_comp` and
  `…openSubschemeLerayComparisonLE_fac_app` — the factorizations that characterize the two derived
  crossings.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.openSubschemeSectionsUnitLE_comp_lerayComparison`
  — the sections unit followed by the Leray comparison upstairs is the unit with the Leray
  comparison's target upstairs.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange`
  `.openSubschemeSectionsComparisonLE_comp_lerayComparison_eq` — **the compatibility of the Leray
  comparison of [Stacks, Tag 0D5W] with restriction to a smaller open subscheme**: the crossing of
  the source followed by the Leray comparison for `f.resLE V U e` over `⊤` is the Leray comparison
  for `f` over `V` followed by the crossing out of its target. No hypothesis on `f`, on `V`, on `U`
  or on the module.

## Implementation notes

*Why the derived target is spelled with `mapDerivedCategory` twice.* Restriction to an open
subspace and restriction of scalars are both exact, so each is its own derived functor; only
sections are derived. The restriction is the **ringed-space** functor
`Stacks.Cohomology.HigherDirectImage.moduleRestriction`, for the reason
`LerayOpenSubschemeSections.lean` records: `HasDerivedCategory X.Modules` is not synthesisable,
while everything at the `SheafOfModules (structureSheafRing _)` spelling is found.

*The one instance crossing, paid exactly as in the `U = f⁻¹V` file.* That restriction's declared
target is the modules on `…HigherDirectImage.restrictToOpen X.toRingedSpace U`, and the sections
functor it is composed with has source the modules on `(U : Scheme).toRingedSpace`. The two are
definitionally equal and are the recorded spelling pair that instance synthesis cannot cross: the
`CategoryTheory.Functor.Additive` subgoal `CategoryTheory.Functor.mapHomotopyCategoryCompIso`
generates carries the `restrictToOpen` spelling, where neither the declared additivity of
`…DerivedSectionsLeray.preimageSections` nor `CategoryTheory.Functor.instAdditiveComp` applies. So
`openSubschemeRestrictionOf` names the restriction with the other spelling as its *declared* target
and carries the three exactness instances across by `inferInstanceAs`, in term mode, where the
conversion runs at default transparency. It is deliberately a `def` and not an `abbrev`: were it
reducible, instance search would unfold it and land back on the spelling whose instances it cannot
use.

*Why the unit is built from an arbitrary presentation of the crossing and an arbitrary unit
upstairs.* Leaving the upstairs unit variable makes carrying the Leray comparison for
`f.resLE V U e` through the whole crossing one lemma at variables,
`openSubschemeUnitOfNatTransUnit_comp`, whose content is the naturality of that comparison at one
morphism: no factor of the crossing is unfolded and no reassociation is performed. The degreewise
presentation is variable for symmetry with the `U = f⁻¹V` file, where two presentations are
wanted; here there is only one, since the `ψ` route does not generalise.

*Why there is no second descent out of `Rf_* ⋙ RΓ(V, -)`.* The `U = f⁻¹V` file carries two,
`…openSubschemePushforwardComparison` into the sections target and `…openSubschemeLerayComparison`
into the Leray target, and reaches the compatibility in two steps. Here the compatibility is proved
in one: both of its sides come out of `RΓ(f⁻¹V, -)`, so `lerayComparison_ext` applies directly and
the three factorizations collapse the two composites with the derived-functor unit to the two
units, which `openSubschemeSectionsUnitLE_comp_lerayComparison` identifies.

*Why [Stacks, Tag 08FE] is not used.* The two Leray comparisons' targets — `RΓ(V, -) ∘ Rf_*` and
`RΓ(⊤, -) ∘ R(f.resLE V U e)_*` after the restriction — are related by no crossing of sections, and
08FE (proved; `DerivedPushforwardOpenSubscheme.lean` bridges it to this file's restriction
spelling) is one way to relate them. But the universal property does not ask for an isomorphism of
the two targets: it asks for a transformation out of `Rf_* ⋙ RΓ(V, -)`, and the degreewise crossing
followed by `lerayUnit (f.resLE V U e) ⊤` is one. That is `openSubschemeLerayComparisonLE`.

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
    lerayComparison_ext lerayComparison_fac lerayComparison_fac_app_comp)

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

/-! ### Restriction to an open subscheme, at the open subscheme's own structure sheaf -/

/-- **Restriction of sheaves of modules to an open subscheme `U`**, with the target ascribed to the
modules on `(U : Scheme).toRingedSpace`.

This is `Stacks.Cohomology.HigherDirectImage.moduleRestriction X.toRingedSpace U` and nothing else;
the ascription is not cosmetic, see this module's implementation notes. It is the open-indexed form
of `…TopDegreeBaseChange.openSubschemeRestriction`, which is its value at `U := f⁻¹V`. -/
def openSubschemeRestrictionOf (X : Scheme.{u}) (U : X.Opens) :
    SheafOfModules.{u} (structureSheafRing X.toRingedSpace) ⥤
      SheafOfModules.{u} (structureSheafRing (U : Scheme).toRingedSpace) :=
  moduleRestriction X.toRingedSpace U

/-- Restriction to an open subscheme is additive. -/
instance openSubschemeRestrictionOf_additive (X : Scheme.{u}) (U : X.Opens) :
    (openSubschemeRestrictionOf X U).Additive :=
  inferInstanceAs ((moduleRestriction X.toRingedSpace U).Additive)

/-- Restriction to an open subscheme is left exact. -/
instance openSubschemeRestrictionOf_preservesFiniteLimits (X : Scheme.{u}) (U : X.Opens) :
    PreservesFiniteLimits (openSubschemeRestrictionOf X U) :=
  inferInstanceAs (PreservesFiniteLimits (moduleRestriction X.toRingedSpace U))

/-- Restriction to an open subscheme is right exact. -/
instance openSubschemeRestrictionOf_preservesFiniteColimits (X : Scheme.{u}) (U : X.Opens) :
    PreservesFiniteColimits (openSubschemeRestrictionOf X U) :=
  inferInstanceAs (PreservesFiniteColimits (moduleRestriction X.toRingedSpace U))

/-- The restriction of `LerayOpenSubschemeDerived.lean` is this one at the preimage open: no second
construction is hidden here, and the equality holds by definition. -/
theorem openSubschemeRestriction_eq {X S : Scheme.{u}} (f : X ⟶ S) (V : S.Opens) :
    openSubschemeRestriction f V = openSubschemeRestrictionOf X (f ⁻¹ᵁ V) := rfl

variable {X S : Scheme.{u}} (f : X ⟶ S) (V : S.Opens) {U : X.Opens} (e : U ≤ f ⁻¹ᵁ V)

/-! ### The derived target -/

/-- **The open-subscheme reading of sections over `f⁻¹V` at the smaller open `U`, with the upstairs
derived functor left open.** Derived restriction to the open subscheme `U`, then a functor `RP` out
of the derived category upstairs, then derived restriction of scalars along
`AlgebraicGeometry.Scheme.Opens.topIso` at `V`: a functor `D(𝒪_X) ⥤ D(Γ(S, V))`.

The two outer factors are exact, so each is its own derived functor; only `RP` is derived, and it
is left variable because the chain below meets it at two values — `RΓ((f.resLE V U e)⁻¹⊤, -)` and
`R(f.resLE V U e)_* ⋙ RΓ(V, ⊤)`, the Leray comparison's two sides upstairs. -/
abbrev openSubschemeDerivedTargetOf (X : Scheme.{u}) (U : X.Opens) {S : Scheme.{u}} (V : S.Opens)
    (RP : DerivedCategory (SheafOfModules.{u} (structureSheafRing (U : Scheme).toRingedSpace)) ⥤
      DerivedCategory (ModuleCat.{u}
        ((structureSheafRing (V : Scheme).toRingedSpace).obj.obj (op ⊤)))) :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) ⥤
      DerivedCategory (ModuleCat.{u} ((structureSheafRing S.toRingedSpace).obj.obj (op V))) :=
  (openSubschemeRestrictionOf X U).mapDerivedCategory ⋙
    RP ⋙ (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom).mapDerivedCategory

/-- **The derived form of the open-subscheme reading of sections over `f⁻¹V` at `U`.** Derived
restriction to the open subscheme `U`, then derived sections over `(f.resLE V U e)⁻¹⊤`, then
derived restriction of scalars along `AlgebraicGeometry.Scheme.Opens.topIso` at `V`: the functor
that `preimageSectionsOpenSubschemeLE` becomes once the sections are derived. -/
abbrev derivedPreimageSectionsOpenSubschemeLE :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) ⥤
      DerivedCategory (ModuleCat.{u} ((structureSheafRing S.toRingedSpace).obj.obj (op V))) :=
  openSubschemeDerivedTargetOf X U V (derivedPreimageSections (f.resLE V U e).toLRSHom.toShHom ⊤)

/-- **The same with the Leray comparison's target upstairs.** `openSubschemeDerivedTargetOf` at
`R(f.resLE V U e)_* ⋙ RΓ(V, ⊤)`: derived restriction to `U`, the derived direct image along
`f.resLE V U e`, global derived sections of the open subscheme `V`, and the restriction of
scalars. -/
abbrev derivedPushforwardSectionsOpenSubschemeLE :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) ⥤
      DerivedCategory (ModuleCat.{u} ((structureSheafRing S.toRingedSpace).obj.obj (op V))) :=
  openSubschemeDerivedTargetOf X U V
    (derivedPushforward (f.resLE V U e).toLRSHom.toShHom ⋙
      derivedSectionsOverOpen (V : Scheme).toRingedSpace ⊤)

/-! ### Splitting the exact factors off the homotopy category -/

/-- Restriction of scalars along `AlgebraicGeometry.Scheme.Opens.topIso` at `V` commutes with
passing to the derived category: degreewise sections over `(f.resLE V U e)⁻¹⊤` read over `Γ(S, V)`,
localized, is those sections localized and then followed by the derived functor of restriction of
scalars. This is the inner half of `preimageSectionsOpenSubschemeHomotopyIsoLE`. -/
def preimageSectionsTopRestrictHomotopyIsoLE :
    (preimageSections (f.resLE V U e).toLRSHom.toShHom ⊤ ⋙
          ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ≅
      (preimageSections (f.resLE V U e).toLRSHom.toShHom ⊤).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⋙
          (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom).mapDerivedCategory :=
  (Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryCompIso
        (Iso.refl (preimageSections (f.resLE V U e).toLRSHom.toShHom ⊤ ⋙
          ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom)) (ComplexShape.up ℤ))
      DerivedCategory.Qh).symm ≪≫
    Functor.isoWhiskerLeft
      ((preimageSections (f.resLE V U e).toLRSHom.toShHom ⊤).mapHomotopyCategory
        (ComplexShape.up ℤ))
      (ModuleCat.restrictScalars
        (Scheme.Opens.topIso V).inv.hom).mapDerivedCategoryFactorsh.symm

/-- **The two exact factors of the degreewise target split off the homotopy category.** The
degreewise target of `preimageSectionsOpenSubschemeLE`, read on the homotopy category and
localized, is restriction to the open subscheme `U` on the homotopy category, then degreewise
sections over `(f.resLE V U e)⁻¹⊤` localized, then the derived functor of restriction of scalars.

Only `CategoryTheory.Functor.mapHomotopyCategoryCompIso` at identity isomorphisms and
`CategoryTheory.Functor.mapDerivedCategoryFactorsh` for the two exact factors are used; nothing is
derived yet. -/
def preimageSectionsOpenSubschemeHomotopyIsoLE :
    (openSubschemeRestrictionOf X U ⋙
            preimageSections (f.resLE V U e).toLRSHom.toShHom ⊤ ⋙
              ModuleCat.restrictScalars
                (Scheme.Opens.topIso V).inv.hom).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh ≅
      (openSubschemeRestrictionOf X U).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (preimageSections (f.resLE V U e).toLRSHom.toShHom ⊤).mapHomotopyCategory
            (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh ⋙
            (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom).mapDerivedCategory :=
  (Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryCompIso
        (Iso.refl (openSubschemeRestrictionOf X U ⋙
          preimageSections (f.resLE V U e).toLRSHom.toShHom ⊤ ⋙
            ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom)) (ComplexShape.up ℤ))
      DerivedCategory.Qh).symm ≪≫
    Functor.isoWhiskerLeft
      ((openSubschemeRestrictionOf X U).mapHomotopyCategory (ComplexShape.up ℤ))
      (preimageSectionsTopRestrictHomotopyIsoLE f V e)

/-! ### The unit the universal property consumes -/

/-- **The transformation the universal property consumes, from an arbitrary presentation of the
degreewise crossing and an arbitrary unit upstairs.** Given a transformation `α` of degreewise
sections over `f⁻¹V` into their open-subscheme reading at `U`, and a transformation `u` from
degreewise sections over `(f.resLE V U e)⁻¹⊤` into a functor `RP` on the derived category, the
canonical transformation from degreewise sections over `f⁻¹V` into
`Qh ⋙ openSubschemeDerivedTargetOf X U V RP`: `α` on the homotopy category, the splitting of the
two exact factors, `u`, and the comparison of restriction to the open subscheme with localization.

Unlike `…openSubschemeUnitOfIsoUnit`, which this generalizes, `α` is a plain transformation: at
`U < f⁻¹V` the degreewise crossing is the restriction of sections and is not invertible, and the
universal property does not ask it to be. `u` is variable so that composing a transformation of the
upstairs derived functors onto the result is one lemma at variables,
`openSubschemeUnitOfNatTransUnit_comp`. -/
def openSubschemeUnitOfNatTransUnit
    (α : preimageSections f.toLRSHom.toShHom V ⟶
      openSubschemeRestrictionOf X U ⋙
        preimageSections (f.resLE V U e).toLRSHom.toShHom ⊤ ⋙
          ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom)
    {RP : DerivedCategory (SheafOfModules.{u}
        (structureSheafRing (U : Scheme).toRingedSpace)) ⥤
      DerivedCategory (ModuleCat.{u}
        ((structureSheafRing (V : Scheme).toRingedSpace).obj.obj (op ⊤)))}
    (u : (preimageSections (f.resLE V U e).toLRSHom.toShHom ⊤).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RP) :
    homotopyPreimageSections f.toLRSHom.toShHom V ⟶
      DerivedCategory.Qh ⋙ openSubschemeDerivedTargetOf X U V RP :=
  Functor.whiskerRight (NatTrans.mapHomotopyCategory α (ComplexShape.up ℤ))
      DerivedCategory.Qh ≫
    (preimageSectionsOpenSubschemeHomotopyIsoLE f V e).hom ≫
    Functor.whiskerLeft
        ((openSubschemeRestrictionOf X U).mapHomotopyCategory (ComplexShape.up ℤ))
        (Functor.whiskerRight u
          (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom).mapDerivedCategory) ≫
    Functor.whiskerRight
      (openSubschemeRestrictionOf X U).mapDerivedCategoryFactorsh.inv
      (RP ⋙ (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom).mapDerivedCategory)

/-- **Composing a transformation of the upstairs derived functors onto the unit.** For `L` a
transformation of the two functors the crossing may land in upstairs, the unit built from `u ≫ L`
is the unit built from `u`, followed by `L` whiskered by the derived restriction on the left and by
the derived restriction of scalars on the right.

Only the last two factors of `openSubschemeUnitOfNatTransUnit` are touched: the comparison of
restriction to the open subscheme with localization is carried past `L` by `L`'s naturality, and
nothing else is looked inside. There is no hypothesis on `α`, on `u` or on `L`. -/
theorem openSubschemeUnitOfNatTransUnit_comp
    (α : preimageSections f.toLRSHom.toShHom V ⟶
      openSubschemeRestrictionOf X U ⋙
        preimageSections (f.resLE V U e).toLRSHom.toShHom ⊤ ⋙
          ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom)
    {RP RQ : DerivedCategory (SheafOfModules.{u}
        (structureSheafRing (U : Scheme).toRingedSpace)) ⥤
      DerivedCategory (ModuleCat.{u}
        ((structureSheafRing (V : Scheme).toRingedSpace).obj.obj (op ⊤)))}
    (u : (preimageSections (f.resLE V U e).toLRSHom.toShHom ⊤).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RP)
    (L : RP ⟶ RQ) :
    openSubschemeUnitOfNatTransUnit f V e α (u ≫ Functor.whiskerLeft DerivedCategory.Qh L) =
      openSubschemeUnitOfNatTransUnit f V e α u ≫
        Functor.whiskerLeft DerivedCategory.Qh
          (Functor.whiskerLeft (openSubschemeRestrictionOf X U).mapDerivedCategory
            (Functor.whiskerRight L
              (ModuleCat.restrictScalars
                (Scheme.Opens.topIso V).inv.hom).mapDerivedCategory)) := by
  ext K
  have hnat := congrArg
    (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom).mapDerivedCategory.map
    (L.naturality ((openSubschemeRestrictionOf X U).mapDerivedCategoryFactorsh.inv.app K))
  simp only [Functor.map_comp] at hnat
  dsimp only [openSubschemeUnitOfNatTransUnit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.comp_map]
  simp only [Category.assoc, Functor.map_comp]
  exact congrArg _ (congrArg _ (congrArg _ hnat.symm))

/-- The unit of the crossing: `openSubschemeUnitOfNatTransUnit` at the degreewise crossing
`preimageSectionsOpenSubschemeLE` and at the unit of `RΓ((f.resLE V U e)⁻¹⊤, -)`. -/
def openSubschemeSectionsUnitLE :
    homotopyPreimageSections f.toLRSHom.toShHom V ⟶
      DerivedCategory.Qh ⋙ derivedPreimageSectionsOpenSubschemeLE f V e :=
  openSubschemeUnitOfNatTransUnit f V e (preimageSectionsOpenSubschemeLE f V e)
    (derivedPreimageSectionsUnit (f.resLE V U e).toLRSHom.toShHom ⊤)

/-- The same unit with the **Leray comparison's target** upstairs:
`openSubschemeUnitOfNatTransUnit` at the degreewise crossing and at
`Stacks.Cohomology.DerivedSectionsLeray.lerayUnit (f.resLE V U e) ⊤`. -/
def openSubschemeLerayUnitLE :
    homotopyPreimageSections f.toLRSHom.toShHom V ⟶
      DerivedCategory.Qh ⋙ derivedPushforwardSectionsOpenSubschemeLE f V e :=
  openSubschemeUnitOfNatTransUnit f V e (preimageSectionsOpenSubschemeLE f V e)
    (lerayUnit (f.resLE V U e).toLRSHom.toShHom ⊤)

/-- **The sections unit followed by the Leray comparison upstairs is the unit with the Leray
comparison's target upstairs.** This is
`Stacks.Cohomology.DerivedSectionsLeray.lerayComparison_fac` for `f.resLE V U e` over `⊤` carried
through `openSubschemeUnitOfNatTransUnit_comp`; no factor of the crossing is unfolded and nothing
is assumed of `f`, of `V` or of `U`. -/
theorem openSubschemeSectionsUnitLE_comp_lerayComparison :
    openSubschemeSectionsUnitLE f V e ≫
        Functor.whiskerLeft DerivedCategory.Qh
          (Functor.whiskerLeft (openSubschemeRestrictionOf X U).mapDerivedCategory
            (Functor.whiskerRight (lerayComparison (f.resLE V U e).toLRSHom.toShHom ⊤)
              (ModuleCat.restrictScalars
                (Scheme.Opens.topIso V).inv.hom).mapDerivedCategory)) =
      openSubschemeLerayUnitLE f V e :=
  (openSubschemeUnitOfNatTransUnit_comp f V e (preimageSectionsOpenSubschemeLE f V e)
        (derivedPreimageSectionsUnit (f.resLE V U e).toLRSHom.toShHom ⊤)
        (lerayComparison (f.resLE V U e).toLRSHom.toShHom ⊤)).symm.trans
    (congrArg (openSubschemeUnitOfNatTransUnit f V e (preimageSectionsOpenSubschemeLE f V e))
      (lerayComparison_fac (f.resLE V U e).toLRSHom.toShHom ⊤))

/-! ### The two derived crossings -/

/-- **The derived crossing, descending from `RΓ(f⁻¹V, -)`.** The transformation
`RΓ(f⁻¹V, -) ⟶ derivedPreimageSectionsOpenSubschemeLE` induced by `openSubschemeSectionsUnitLE`
through the universal property of the total right derived functor of sections over `f⁻¹V`. By
`openSubschemeSectionsComparisonLE_fac_app` its composite with the derived-functor unit is that
unit, and that equation determines it. -/
def openSubschemeSectionsComparisonLE :
    derivedPreimageSections f.toLRSHom.toShHom V ⟶
      derivedPreimageSectionsOpenSubschemeLE f V e :=
  (derivedPreimageSections f.toLRSHom.toShHom V).rightDerivedDesc
    (derivedPreimageSectionsUnit f.toLRSHom.toShHom V)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (ComplexShape.up ℤ)) _ (openSubschemeSectionsUnitLE f V e)

/-- The equation characterizing `openSubschemeSectionsComparisonLE`, pointwise: composing it with
the unit of `RΓ(f⁻¹V, -)` recovers `openSubschemeSectionsUnitLE`. -/
theorem openSubschemeSectionsComparisonLE_fac_app
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (ComplexShape.up ℤ)) :
    (derivedPreimageSectionsUnit f.toLRSHom.toShHom V).app K ≫
        (openSubschemeSectionsComparisonLE f V e).app (DerivedCategory.Qh.obj K) =
      (openSubschemeSectionsUnitLE f V e).app K :=
  (derivedPreimageSections f.toLRSHom.toShHom V).rightDerived_fac_app
    (derivedPreimageSectionsUnit f.toLRSHom.toShHom V)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (ComplexShape.up ℤ)) _ (openSubschemeSectionsUnitLE f V e) K

/-- `openSubschemeSectionsComparisonLE_fac_app` with a further morphism appended, the form in which
a rewrite inside a longer composite uses it. -/
theorem openSubschemeSectionsComparisonLE_fac_app_comp
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (ComplexShape.up ℤ))
    {T : DerivedCategory (ModuleCat.{u} ((structureSheafRing S.toRingedSpace).obj.obj (op V)))}
    (g : (derivedPreimageSectionsOpenSubschemeLE f V e).obj (DerivedCategory.Qh.obj K) ⟶ T) :
    (derivedPreimageSectionsUnit f.toLRSHom.toShHom V).app K ≫
        (openSubschemeSectionsComparisonLE f V e).app (DerivedCategory.Qh.obj K) ≫ g =
      (openSubschemeSectionsUnitLE f V e).app K ≫ g := by
  rw [← Category.assoc, openSubschemeSectionsComparisonLE_fac_app]

/-- **The derived crossing, descending from `Rf_* ⋙ RΓ(V, -)`, into the target the Leray
comparison upstairs lands in.** The transformation
`Rf_* ⋙ RΓ(V, -) ⟶ derivedPushforwardSectionsOpenSubschemeLE` induced by
`openSubschemeLerayUnitLE` through the universal property that
`Stacks.Cohomology.DerivedSectionsLeray.isRightDerivedFunctor_lerayUnit` records for the Leray
comparison's target. -/
def openSubschemeLerayComparisonLE :
    derivedPushforward f.toLRSHom.toShHom ⋙ derivedSectionsOverOpen S.toRingedSpace V ⟶
      derivedPushforwardSectionsOpenSubschemeLE f V e :=
  (derivedPushforward f.toLRSHom.toShHom ⋙
      derivedSectionsOverOpen S.toRingedSpace V).rightDerivedDesc
    (lerayUnit f.toLRSHom.toShHom V)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (ComplexShape.up ℤ)) _ (openSubschemeLerayUnitLE f V e)

/-- The equation characterizing `openSubschemeLerayComparisonLE`, pointwise. -/
theorem openSubschemeLerayComparisonLE_fac_app
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (ComplexShape.up ℤ)) :
    (lerayUnit f.toLRSHom.toShHom V).app K ≫
        (openSubschemeLerayComparisonLE f V e).app (DerivedCategory.Qh.obj K) =
      (openSubschemeLerayUnitLE f V e).app K :=
  (derivedPushforward f.toLRSHom.toShHom ⋙
      derivedSectionsOverOpen S.toRingedSpace V).rightDerived_fac_app
    (lerayUnit f.toLRSHom.toShHom V)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (ComplexShape.up ℤ)) _ (openSubschemeLerayUnitLE f V e) K

/-! ### The compatibility -/

/-- **The Leray comparison for `f` over `V` and the Leray comparison for `f.resLE V U e` over `⊤`
agree across the open-subscheme crossing at the smaller open `U`.** For a morphism of schemes
`f : X ⟶ S`, an open `V ⊆ S` and an open `U ≤ f⁻¹V` of `X`, the derived crossing of the Leray
comparison's source, followed by the Leray comparison of [Stacks, Tag 0D5W] for the restricted
morphism `AlgebraicGeometry.Scheme.Hom.resLE f V U e` over the whole of the open subscheme `V`, is
the Leray comparison for `f` over `V` followed by the derived crossing out of its target. Both
sides are transformations
`RΓ(f⁻¹V, -) ⟶ derivedPushforwardSectionsOpenSubschemeLE f V e` of functors
`D(𝒪_X) ⥤ D(Γ(S, V))`.

**There is no hypothesis on `f`, on `V`, on `U` or on the module**, and the two Leray comparisons
are the library's: nothing here re-proves [Stacks, Tag 0D5W], and [Stacks, Tag 08FE] is not used.
At `U = f⁻¹V` this is `…openSubschemeSectionsComparison_comp_lerayComparison_eq`, up to
`AlgebraicGeometry.Scheme.Hom.resLE_eq_morphismRestrict`.

Both sides come out of `RΓ(f⁻¹V, -)`, so
`Stacks.Cohomology.DerivedSectionsLeray.lerayComparison_ext` reduces the statement to the
composites with the derived-functor unit; the three factorizations collapse those to the sections
unit followed by the Leray comparison upstairs, and to `openSubschemeLerayUnitLE`, which
`openSubschemeSectionsUnitLE_comp_lerayComparison` identifies. -/
theorem openSubschemeSectionsComparisonLE_comp_lerayComparison_eq :
    openSubschemeSectionsComparisonLE f V e ≫
        Functor.whiskerLeft (openSubschemeRestrictionOf X U).mapDerivedCategory
          (Functor.whiskerRight (lerayComparison (f.resLE V U e).toLRSHom.toShHom ⊤)
            (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom).mapDerivedCategory) =
      lerayComparison f.toLRSHom.toShHom V ≫ openSubschemeLerayComparisonLE f V e := by
  apply lerayComparison_ext f.toLRSHom.toShHom V
  ext K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app]
  rw [openSubschemeSectionsComparisonLE_fac_app_comp f V e K, lerayComparison_fac_app_comp,
    openSubschemeLerayComparisonLE_fac_app f V e K]
  exact NatTrans.congr_app (openSubschemeSectionsUnitLE_comp_lerayComparison f V e) K

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
