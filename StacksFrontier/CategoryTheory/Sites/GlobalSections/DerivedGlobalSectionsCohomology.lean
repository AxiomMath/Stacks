module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparison
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Derived global sections are sheaf cohomology, on a site whose objects are not small

Global sections of abelian sheaves on a site are corepresented by the constant sheaf on the
integers, so their right derived functors are the `Ext`-functors out of that sheaf, which is
Mathlib's `CategoryTheory.Sheaf.functorH`. This file proves that with the universe of the
objects of the site left free of the universe of its morphisms, and the coefficient universe
only required to absorb the former.

## Main results

* `Stacks.Cohomology.GlobalSections.globalSectionsCorepresentation`: global sections are
  corepresented by the constant sheaf on `ULift ℤ`.
* `Stacks.Cohomology.GlobalSections.rightDerivedΓIsoFunctorH`: **the right derived functors of
  global sections are the sheaf cohomology functors.**
* `Stacks.Cohomology.GlobalSections.subsingleton_sheafH_iff_isZero_rightDerivedΓ`: the vanishing
  forms of the two therefore agree.

## Implementation notes

`Stacks.Cohomology.BiggerSiteGlobal.functorHIsoRightDerivedSiteSections` is the same statement
for a site whose underlying category is small, with coefficients in the single universe of that
category. Both restrictions fail for the small étale site of a scheme `X : Scheme.{u}`, whose
objects form a `Type (u + 1)` while its morphisms form a `Type u`, and whose abelian sheaves are
taken with coefficients in `AddCommGrpCat.{u + 1}`. Coefficients here are
`AddCommGrpCat.{max u w}` for an object universe `u` and a free `w`, which is the general shape:
morphisms of sheaves on a `Type u`-indexed site with those coefficients again form a
`Type (max u w)`, and that is what makes global sections and the corepresenting `Hom`-functor
land in the same category.

The two ingredients are both already general: the corepresentation is the constant sheaf
adjunction together with `AddCommGrpCat.uliftZMultiplesAddEquiv`, and the passage from a
corepresented functor to `Ext` is `Stacks.ModuleSheafCohomology.rightDerivedCoyonedaSuccIso` in
positive degree and `Stacks.ModuleSheafCohomology.extZeroIsoCoyoneda` in degree zero.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace Stacks.Cohomology.GlobalSections

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max u w}]
  [HasGlobalSectionsFunctor J AddCommGrpCat.{max u w}]

/-- Global sections of abelian sheaves are additive, being a right adjoint and hence preserving
binary products. -/
public theorem additive_Γ : (Sheaf.Γ J AddCommGrpCat.{max u w}).Additive :=
  Functor.additive_of_preserves_binary_products _

attribute [local instance] additive_Γ

/-- **Global sections of abelian sheaves are corepresented by the constant sheaf on `ℤ`.** -/
public noncomputable def globalSectionsCorepresentation :
    Sheaf.Γ J AddCommGrpCat.{max u w} ≅ preadditiveCoyoneda.obj
      (op ((constantSheaf J AddCommGrpCat.{max u w}).obj
        (AddCommGrpCat.of (ULift.{max u w} ℤ)))) := by
  refine (NatIso.ofComponents (fun F =>
    (((constantSheafΓAdj J AddCommGrpCat.{max u w}).homAddEquiv
        (AddCommGrpCat.of (ULift.{max u w} ℤ)) F).trans
      (AddCommGrpCat.uliftZMultiplesAddEquiv _)).toAddCommGrpIso) ?_).symm
  intro F G map
  ext element
  change ((constantSheaf J AddCommGrpCat.{max u w}).obj
    (AddCommGrpCat.of (ULift.{max u w} ℤ)) ⟶ F) at element
  change ((constantSheafΓAdj J AddCommGrpCat.{max u w}).homEquiv _ G (element ≫ map))
      (ULift.up (1 : ℤ)) =
    ((Sheaf.Γ J AddCommGrpCat.{max u w}).map map)
      (((constantSheafΓAdj J AddCommGrpCat.{max u w}).homEquiv _ F element) (ULift.up (1 : ℤ)))
  rw [Adjunction.homEquiv_naturality_right]
  rfl

omit [HasGlobalSectionsFunctor J AddCommGrpCat.{max u w}] in
/-- **The cohomology functors of a site are the `Ext`-functors out of the constant sheaf on `ℤ`**,
as an equality of functors and not merely an isomorphism. `CategoryTheory.Sheaf.functorH` is
defined objectwise as `CategoryTheory.Sheaf.H`, which is that `Ext`, so this is `rfl`.

It is stated because the two spellings are definitionally equal but not interchangeably so: the
unifier sees through the two functor structures when it is handed this equation, and does **not**
when it is asked to discover the identification while solving for the middle object of a
composition, where it exhausts the default heartbeat budget. Consumers that have to cross between
the spellings compose through `CategoryTheory.eqToHom` of this equality. -/
public theorem functorH_eq_extFunctorObj
    [HasExt.{max u w} (Sheaf J AddCommGrpCat.{max u w})] (n : ℕ) :
    Sheaf.functorH J n =
      Abelian.extFunctorObj ((constantSheaf J AddCommGrpCat.{max u w}).obj
        (AddCommGrpCat.of (ULift.{max u w} ℤ))) n :=
  rfl

open ModuleSheafCohomology in
/-- **The right derived functors of global sections are the `Ext`-functors out of the constant
sheaf on `ℤ`.** Global sections are corepresented by that sheaf, so this is
`ModuleSheafCohomology.extFunctorObjIsoRightDerived` at the corepresentation
`globalSectionsCorepresentation`, read in the direction a consumer wants.

This carries the same content as `rightDerivedΓIsoFunctorH` but with its target spelled
`Abelian.extFunctorObj` rather than `CategoryTheory.Sheaf.functorH`. The two spellings are
definitionally equal; the reason for having both is that a proof which computes with *this* body
never has to cross between them in a morphism type, and a proof which computes with the body of
`rightDerivedΓIsoFunctorH` does, which exceeds the default heartbeat budget. Every
`Ext`-versus-resolution comparison in this library has to compute with the body, so this is the
form to use; `rightDerivedΓIsoFunctorH` is this composed with `functorH_eq_extFunctorObj`. -/
@[sga "4 V 2.1.1" "special case",
  sga "4½ Arcata 1.6.5" "more general",
  sga "7 VII 1.4" "special case"]
public noncomputable def rightDerivedΓIsoExtFunctorObj
    [HasExt.{max u w} (Sheaf J AddCommGrpCat.{max u w})]
    [EnoughInjectives (Sheaf J AddCommGrpCat.{max u w})] (n : ℕ) :
    (Sheaf.Γ J AddCommGrpCat.{max u w}).rightDerived n ≅
      Abelian.extFunctorObj ((constantSheaf J AddCommGrpCat.{max u w}).obj
        (AddCommGrpCat.of (ULift.{max u w} ℤ))) n :=
  match n with
  | 0 => (Sheaf.Γ J AddCommGrpCat.{max u w}).rightDerivedZeroIsoSelf ≪≫
      globalSectionsCorepresentation J ≪≫ (extZeroIsoCoyoneda _).symm
  | n + 1 => rightDerivedIso (globalSectionsCorepresentation J) (n + 1) ≪≫
      rightDerivedCoyonedaSuccIso _ n

open ModuleSheafCohomology in
/-- In degree zero the comparison is left exactness of global sections followed by the
corepresentation. -/
public theorem rightDerivedΓIsoExtFunctorObj_zero
    [HasExt.{max u w} (Sheaf J AddCommGrpCat.{max u w})]
    [EnoughInjectives (Sheaf J AddCommGrpCat.{max u w})] :
    rightDerivedΓIsoExtFunctorObj J 0 =
      (Sheaf.Γ J AddCommGrpCat.{max u w}).rightDerivedZeroIsoSelf ≪≫
        globalSectionsCorepresentation J ≪≫
          (extZeroIsoCoyoneda ((constantSheaf J AddCommGrpCat.{max u w}).obj
            (AddCommGrpCat.of (ULift.{max u w} ℤ)))).symm :=
  rfl

open ModuleSheafCohomology in
/-- In positive degree the comparison is `rightDerivedCoyonedaSuccIso` transported along the
corepresentation. -/
public theorem rightDerivedΓIsoExtFunctorObj_succ
    [HasExt.{max u w} (Sheaf J AddCommGrpCat.{max u w})]
    [EnoughInjectives (Sheaf J AddCommGrpCat.{max u w})] (n : ℕ) :
    rightDerivedΓIsoExtFunctorObj J (n + 1) =
      rightDerivedIso (globalSectionsCorepresentation J) (n + 1) ≪≫
        rightDerivedCoyonedaSuccIso ((constantSheaf J AddCommGrpCat.{max u w}).obj
          (AddCommGrpCat.of (ULift.{max u w} ℤ))) n :=
  rfl

/-- **The right derived functors of global sections are the sheaf cohomology functors.** Global
sections are corepresented by the constant sheaf on `ℤ`, and sheaf cohomology is `Ext` out of
that sheaf.

This is `rightDerivedΓIsoExtFunctorObj` with its target rewritten by
`functorH_eq_extFunctorObj`. The statement is the one it always was; splitting the construction
in two is what lets a consumer compute with the body without crossing the two spellings of the
target in a morphism type. -/
public noncomputable def rightDerivedΓIsoFunctorH
    [HasExt.{max u w} (Sheaf J AddCommGrpCat.{max u w})]
    [EnoughInjectives (Sheaf J AddCommGrpCat.{max u w})] (n : ℕ) :
    (Sheaf.Γ J AddCommGrpCat.{max u w}).rightDerived n ≅ Sheaf.functorH J n :=
  rightDerivedΓIsoExtFunctorObj J n ≪≫ eqToIso (functorH_eq_extFunctorObj J n).symm

/-- `rightDerivedΓIsoFunctorH` is `rightDerivedΓIsoExtFunctorObj` read across the identification
of the two spellings of the target. This is the equation a consumer crossing between them uses,
and it is the reason the cast is explicit rather than left to the unifier. -/
public theorem rightDerivedΓIsoFunctorH_hom_comp_eqToHom
    [HasExt.{max u w} (Sheaf J AddCommGrpCat.{max u w})]
    [EnoughInjectives (Sheaf J AddCommGrpCat.{max u w})] (n : ℕ) :
    (rightDerivedΓIsoFunctorH J n).hom ≫ eqToHom (functorH_eq_extFunctorObj J n) =
      (rightDerivedΓIsoExtFunctorObj J n).hom := by
  change ((rightDerivedΓIsoExtFunctorObj J n ≪≫
    eqToIso (functorH_eq_extFunctorObj J n).symm).hom) ≫ _ = _
  rw [Iso.trans_hom, Category.assoc, eqToIso.hom, eqToHom_trans, eqToHom_refl, Category.comp_id]

/-- Sheaf cohomology over the site vanishes in degree `n` exactly when the `n`-th right derived
functor of global sections does. -/
public theorem subsingleton_sheafH_iff_isZero_rightDerivedΓ
    [HasExt.{max u w} (Sheaf J AddCommGrpCat.{max u w})]
    [EnoughInjectives (Sheaf J AddCommGrpCat.{max u w})]
    (F : Sheaf J AddCommGrpCat.{max u w}) (n : ℕ) :
    Subsingleton (Sheaf.H.{max u w, max u w} F n) ↔
      IsZero (((Sheaf.Γ J AddCommGrpCat.{max u w}).rightDerived n).obj F) :=
  AddCommGrpCat.isZero_iff_subsingleton.symm.trans
    (((rightDerivedΓIsoFunctorH J n).app F).isZero_iff.symm)

end Stacks.Cohomology.GlobalSections

end
