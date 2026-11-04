module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.RightDerivedSectionsEssentiallySmall
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The comparison of `Ext` with right-derived sections, as a construction

For an object `U` of a site, the `Ext`-functors out of the free abelian sheaf on `U` are the right
derived functors of sections over `U`, with the coefficient universe independent of the objects
of the site. The existence statements
`ModuleSheafCohomology.nonempty_extFunctorObj_iso_rightDerived_of_extZeroIso` and
`nonempty_extFunctorObj_iso_rightDerived_sections_of_enoughInjectives` give such isomorphisms
only through `Nonempty.some`. This file constructs the comparisons explicitly, each with a
degree-zero normalisation.

## Main definitions

* `ModuleSheafCohomology.extDeltaFunctorIsoRightDerivedOfExtZeroIso`,
  `ModuleSheafCohomology.extFunctorObjIsoRightDerivedOfExtZeroIso`: the comparison of the
  `Ext`-functors out of a corepresenting object with the right derived functors of a
  corepresented left exact functor.
* `Stacks.Cohomology.FreeYonedaUnivLE.extDeltaFunctorIsoRightDerivedSections`,
  `Stacks.Cohomology.FreeYonedaUnivLE.extFunctorObjIsoRightDerivedSections`,
  `Stacks.Cohomology.FreeYonedaUnivLE.cohomologyPresheafObjIsoRightDerivedSectionsPinned`,
  `Stacks.Cohomology.FreeYonedaUnivLE.sheafCohomologyIsoRightDerivedSectionsPinned`: the
  comparison on a site, as an isomorphism of `δ`-functors and its components.

## Main results

* `ModuleSheafCohomology.extFunctorObjIsoRightDerivedOfExtZeroIso_hom_zero`,
  `extFunctorObjIsoRightDerivedSections_hom_zero`,
  `cohomologyPresheafObjIsoRightDerivedSectionsPinned_hom_zero`,
  `sheafCohomologyIsoRightDerivedSectionsPinned_hom_zero`: the degree-zero components of the
  comparisons.

## Implementation notes

Each comparison is `CategoryTheory.DeltaFunctor.IsUniversal.isoOfIso` of the degree-zero
comparison, between the universal `δ`-functors `Ext⁎(X, -)` and `R⁎G`. By
`CategoryTheory.DeltaFunctor.IsUniversal.iso_ext` it is the unique isomorphism of `δ`-functors
with the given degree-zero component, and by `CategoryTheory.DeltaFunctor.hom_ext_zero` morphisms
of `δ`-functors out of `Ext⁎(X, -)` are determined by their degree-zero components.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Abelian

namespace ModuleSheafCohomology

universe w v u dc dc'

noncomputable section

section Pinned

variable {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{w} A] [EnoughInjectives A]

variable (G : A ⥤ AddCommGrpCat.{w}) [G.Additive]

section HasDerivedCategory

variable [HasDerivedCategory.{dc} A] [HasDerivedCategory.{dc'} AddCommGrpCat.{w}]

variable [PreservesFiniteLimits G] (X : A) (α : extFunctorObj X 0 ≅ G)

/-- The degree-zero comparison that `extDeltaFunctorIsoRightDerivedOfExtZeroIso` extends:
`𝟭 A ⋙ Ext⁰(X, -) ≅ G ≅ R⁰G`. -/
def extZeroIsoRightDerivedZero :
    (extDeltaFunctor (𝟭 A) X).functor 0 ≅
      (Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives G).functor 0 :=
  Functor.leftUnitor _ ≪≫ α ≪≫ G.rightDerivedZeroIsoSelf.symm

/-- **The right derived functors of a corepresented left exact functor are the `Ext`-functors
out of the corepresenting object**, as an isomorphism of `δ`-functors and with the `Ext` universe
independent of the morphisms of the category. For an additive, left exact
`G : A ⥤ AddCommGrpCat.{w}` whose values are the degree-zero `Ext`-groups out of `X : A`, the
`δ`-functor `Ext⁎(X, -)` is the `δ`-functor `R⁎G`.

This is `ModuleSheafCohomology.nonempty_extFunctorObj_iso_rightDerived_of_extZeroIso` as a
*construction*: both `extDeltaFunctor (𝟭 A) X` and the right derived `δ`-functor of `G` are
universal, so [Stacks, Tag 010U] extends the degree-zero identification to every degree, and
this is `CategoryTheory.DeltaFunctor.IsUniversal.isoOfIso` of that identification. Its
degree-zero component is `extZeroIsoRightDerivedZero`
(`extDeltaFunctorIsoRightDerivedOfExtZeroIso_hom_app_zero`); the two universality facts are
`extDeltaFunctor_id_isUniversal` and
`Stacks.Cohomology.DeltaAcyclicCollapse.isUniversal_rightDerivedDeltaFunctor`, and
`CategoryTheory.DeltaFunctor.IsUniversal.iso_ext` then makes it the *unique* isomorphism of
`δ`-functors with that degree-zero component. -/
@[sga "3 XXIV 1.13" "more general", sga "4 V 2.1.1" "more general"]
def extDeltaFunctorIsoRightDerivedOfExtZeroIso :
    extDeltaFunctor (𝟭 A) X ≅
      Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives G :=
  letI : (extDeltaFunctor (𝟭 A) X).IsUniversal :=
    extDeltaFunctor_isUniversal (𝟭 A) X fun _ _ _ e => Ext.eq_zero_of_injective e
  letI : (Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives G).IsUniversal :=
    DeltaFunctor.isUniversal_of_isZero_injective _
      fun n I _ => G.isZero_rightDerived_obj_injective_succ n I
  DeltaFunctor.IsUniversal.isoOfIso (extZeroIsoRightDerivedZero G X α)

/-- The degree-zero component of `extDeltaFunctorIsoRightDerivedOfExtZeroIso` is
`extZeroIsoRightDerivedZero`. -/
lemma extDeltaFunctorIsoRightDerivedOfExtZeroIso_hom_app_zero :
    (extDeltaFunctorIsoRightDerivedOfExtZeroIso G X α).hom.app 0 =
      (extZeroIsoRightDerivedZero G X α).hom :=
  let : (extDeltaFunctor (𝟭 A) X).IsUniversal :=
    extDeltaFunctor_isUniversal (𝟭 A) X fun _ _ _ e => Ext.eq_zero_of_injective e
  let : (Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives G).IsUniversal :=
    DeltaFunctor.isUniversal_of_isZero_injective _
      fun n I _ => G.isZero_rightDerived_obj_injective_succ n I
  DeltaFunctor.IsUniversal.isoOfIso_hom_app_zero (extZeroIsoRightDerivedZero G X α)

/-- The inverse of `extDeltaFunctorIsoRightDerivedOfExtZeroIso` in degree zero is the inverse of
`extZeroIsoRightDerivedZero`. -/
lemma extDeltaFunctorIsoRightDerivedOfExtZeroIso_inv_app_zero :
    (extDeltaFunctorIsoRightDerivedOfExtZeroIso G X α).inv.app 0 =
      (extZeroIsoRightDerivedZero G X α).inv := by
  refine Iso.inv_ext' (f := extZeroIsoRightDerivedZero G X α) ?_
  rw [← extDeltaFunctorIsoRightDerivedOfExtZeroIso_hom_app_zero]
  exact congrArg (fun η ↦ η.app 0) (extDeltaFunctorIsoRightDerivedOfExtZeroIso G X α).hom_inv_id

/-- The degree-`n` component of `extDeltaFunctorIsoRightDerivedOfExtZeroIso`, as an isomorphism
of functors. This is `extFunctorObjIsoRightDerivedOfExtZeroIso` with the derived categories taken
from the ambient instances rather than from `CategoryTheory.HasDerivedCategory.standard`. -/
def extFunctorObjIsoRightDerivedApp (n : ℕ) : extFunctorObj X n ≅ G.rightDerived n :=
  (Functor.leftUnitor _).symm ≪≫
    { hom := (extDeltaFunctorIsoRightDerivedOfExtZeroIso G X α).hom.app n
      inv := (extDeltaFunctorIsoRightDerivedOfExtZeroIso G X α).inv.app n
      hom_inv_id :=
        congrArg (fun η ↦ η.app n) (extDeltaFunctorIsoRightDerivedOfExtZeroIso G X α).hom_inv_id
      inv_hom_id :=
        congrArg (fun η ↦ η.app n) (extDeltaFunctorIsoRightDerivedOfExtZeroIso G X α).inv_hom_id }

/-- The forward map of `extFunctorObjIsoRightDerivedApp` is the inverse left unitor followed by
the degree-`n` component of `extDeltaFunctorIsoRightDerivedOfExtZeroIso`. -/
lemma extFunctorObjIsoRightDerivedApp_hom (n : ℕ) :
    (extFunctorObjIsoRightDerivedApp G X α n).hom =
      (Functor.leftUnitor (extFunctorObj X n)).inv ≫
        (extDeltaFunctorIsoRightDerivedOfExtZeroIso G X α).hom.app n :=
  rfl

/-- The inverse of `extFunctorObjIsoRightDerivedApp` is the degree-`n` component of the inverse of
`extDeltaFunctorIsoRightDerivedOfExtZeroIso` followed by the left unitor. -/
lemma extFunctorObjIsoRightDerivedApp_inv (n : ℕ) :
    (extFunctorObjIsoRightDerivedApp G X α n).inv =
      (extDeltaFunctorIsoRightDerivedOfExtZeroIso G X α).inv.app n ≫
        (Functor.leftUnitor (extFunctorObj X n)).hom :=
  rfl

/-- In degree zero, `extFunctorObjIsoRightDerivedApp` is `α` followed by the inverse of
`CategoryTheory.Functor.rightDerivedZeroIsoSelf`. -/
lemma extFunctorObjIsoRightDerivedApp_hom_zero :
    (extFunctorObjIsoRightDerivedApp G X α 0).hom =
      α.hom ≫ G.rightDerivedZeroIsoSelf.inv := by
  rw [extFunctorObjIsoRightDerivedApp_hom,
    extDeltaFunctorIsoRightDerivedOfExtZeroIso_hom_app_zero]
  exact (Functor.leftUnitor (extFunctorObj X 0)).inv_hom_id_assoc _

end HasDerivedCategory

variable [PreservesFiniteLimits G] (X : A) (α : extFunctorObj X 0 ≅ G)

/-- **The right derived functors of a corepresented left exact functor are the `Ext`-functors
out of the corepresenting object**, in degree `n`: the `n`-th right derived functor of `G` is
`Extⁿ(X, -)`.

This is `nonempty_extFunctorObj_iso_rightDerived_of_extZeroIso` as a construction: it is the
degree-`n` component of `extDeltaFunctorIsoRightDerivedOfExtZeroIso` at the standard derived
categories (`extFunctorObjIsoRightDerivedOfExtZeroIso_eq_app`), hence pinned, and in degree zero
it is the given `α` (`extFunctorObjIsoRightDerivedOfExtZeroIso_hom_zero`).

The derived categories are supplied internally by `CategoryTheory.HasDerivedCategory.standard`,
so this statement — like the `Nonempty` one it refines — carries no `HasDerivedCategory`
hypothesis: the universality argument of [Stacks, Tag 010U] uses the derived categories but the
result does not mention them. -/
@[sga "3 XXIV 1.13" "more general", sga "4 V 2.1.1" "more general"]
def extFunctorObjIsoRightDerivedOfExtZeroIso (n : ℕ) :
    extFunctorObj X n ≅ G.rightDerived n :=
  letI := HasDerivedCategory.standard A
  letI := HasDerivedCategory.standard AddCommGrpCat.{w}
  extFunctorObjIsoRightDerivedApp G X α n

/-- `extFunctorObjIsoRightDerivedOfExtZeroIso` *is* the degree-`n` component of the `δ`-functor
isomorphism, at the standard derived categories. -/
lemma extFunctorObjIsoRightDerivedOfExtZeroIso_eq_app (n : ℕ) :
    letI := HasDerivedCategory.standard A
    letI := HasDerivedCategory.standard AddCommGrpCat.{w}
    extFunctorObjIsoRightDerivedOfExtZeroIso G X α n = extFunctorObjIsoRightDerivedApp G X α n :=
  rfl

/-- **The degree-zero normalisation of the pinned comparison**: in degree zero
`extFunctorObjIsoRightDerivedOfExtZeroIso` is the given `α` followed by the inverse of
`CategoryTheory.Functor.rightDerivedZeroIsoSelf` — equivalently, by
`CategoryTheory.Functor.toRightDerivedZero`. -/
lemma extFunctorObjIsoRightDerivedOfExtZeroIso_hom_zero :
    (extFunctorObjIsoRightDerivedOfExtZeroIso G X α 0).hom =
      α.hom ≫ G.rightDerivedZeroIsoSelf.inv :=
  let := HasDerivedCategory.standard A
  let := HasDerivedCategory.standard AddCommGrpCat.{w}
  extFunctorObjIsoRightDerivedApp_hom_zero G X α

end Pinned

end

end ModuleSheafCohomology

namespace Stacks.Cohomology.FreeYonedaUnivLE

universe s t v u dc dc'

noncomputable section

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max v t}]
  [HasExt.{max v t} (Sheaf J AddCommGrpCat.{max v t})]

section EnoughInjectives

variable [EnoughInjectives (Sheaf J AddCommGrpCat.{max v t})]

section DeltaLevel

variable [HasDerivedCategory.{dc} (Sheaf J AddCommGrpCat.{max v t})]
  [HasDerivedCategory.{dc'} AddCommGrpCat.{max v t}]

/-- **The `Ext`-functors out of the free abelian sheaf on `U` are the right derived functors of
sections over `U`**, at any coefficient universe dominating the morphisms of the site — as a
pinned isomorphism of `δ`-functors, the one whose degree-zero component is `extZeroIsoSections`.

This is `extFunctorObjIsoRightDerivedSections` at the level of `δ`-functors;
`CategoryTheory.DeltaFunctor.IsUniversal.iso_ext` makes it the unique such isomorphism, and
`CategoryTheory.DeltaFunctor.hom_ext_zero` reduces a naturality square for it to degree zero. -/
@[sga "4 V 2.1.1" "special case"]
def extDeltaFunctorIsoRightDerivedSections (U : C) :
    ModuleSheafCohomology.extDeltaFunctor (𝟭 (Sheaf J AddCommGrpCat.{max v t}))
        ((freeYoneda.{t} J).obj U) ≅
      Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
        ((sheafSections J AddCommGrpCat.{max v t}).obj (op U)) :=
  ModuleSheafCohomology.extDeltaFunctorIsoRightDerivedOfExtZeroIso
    ((sheafSections J AddCommGrpCat.{max v t}).obj (op U)) _ (extZeroIsoSections.{t} J U)

/-- The degree-zero component of `extDeltaFunctorIsoRightDerivedSections` is
`ModuleSheafCohomology.extZeroIsoRightDerivedZero` of `extZeroIsoSections`. -/
lemma extDeltaFunctorIsoRightDerivedSections_hom_app_zero (U : C) :
    (extDeltaFunctorIsoRightDerivedSections.{t} J U).hom.app 0 =
      (ModuleSheafCohomology.extZeroIsoRightDerivedZero
        ((sheafSections J AddCommGrpCat.{max v t}).obj (op U)) _
        (extZeroIsoSections.{t} J U)).hom :=
  ModuleSheafCohomology.extDeltaFunctorIsoRightDerivedOfExtZeroIso_hom_app_zero _ _ _

end DeltaLevel

/-- **The `Ext`-functors out of the free abelian sheaf on `U` are the right derived functors of
sections over `U`**, at any coefficient universe dominating the morphisms of the site, as a
*construction*. This is
`nonempty_extFunctorObj_iso_rightDerived_sections_of_enoughInjectives` pinned: the degree-`p`
component of `extDeltaFunctorIsoRightDerivedSections`, with degree-zero normalisation
`extFunctorObjIsoRightDerivedSections_hom_zero`. -/
@[sga "4 V 2.1.1" "Ext^p(Z_U, special case"]
def extFunctorObjIsoRightDerivedSections (U : C) (p : ℕ) :
    extFunctorObj.{max v t} ((freeYoneda.{t} J).obj U) p ≅
      ((sheafSections J AddCommGrpCat.{max v t}).obj (op U)).rightDerived p :=
  ModuleSheafCohomology.extFunctorObjIsoRightDerivedOfExtZeroIso
    ((sheafSections J AddCommGrpCat.{max v t}).obj (op U)) _ (extZeroIsoSections.{t} J U) p

/-- **The degree-zero normalisation of `extFunctorObjIsoRightDerivedSections`**: it is
`extZeroIsoSections` followed by the inverse of
`CategoryTheory.Functor.rightDerivedZeroIsoSelf`. -/
lemma extFunctorObjIsoRightDerivedSections_hom_zero (U : C) :
    (extFunctorObjIsoRightDerivedSections.{t} J U 0).hom =
      (extZeroIsoSections.{t} J U).hom ≫
        ((sheafSections J AddCommGrpCat.{max v t}).obj (op U)).rightDerivedZeroIsoSelf.inv :=
  ModuleSheafCohomology.extFunctorObjIsoRightDerivedOfExtZeroIso_hom_zero
    ((sheafSections J AddCommGrpCat.{max v t}).obj (op U)) _ (extZeroIsoSections.{t} J U)

/-- **Sheaf cohomology over an object of the site is right-derived sections**, at any coefficient
universe dominating the morphisms of the site, as a *construction*. This is
`cohomologyPresheafObjIsoRightDerivedSectionsOfEnoughInjectives` pinned: the degree-`p` component
of `extDeltaFunctorIsoRightDerivedSections` evaluated at `F`, with degree-zero normalisation
`cohomologyPresheafObjIsoRightDerivedSectionsPinned_hom_zero`. -/
@[sga "4 V 2.1.2" "Ext^q(A_X, special case"]
def cohomologyPresheafObjIsoRightDerivedSectionsPinned
    (F : Sheaf J AddCommGrpCat.{max v t}) (p : ℕ) (U : C) :
    (cohomologyPresheaf.{max v t, t} F p).obj (op U) ≅
      (((sheafSections J AddCommGrpCat.{max v t}).obj (op U)).rightDerived p).obj F :=
  (extFunctorObjIsoRightDerivedSections.{t} J U p).app F

/-- **The degree-zero normalisation of
`cohomologyPresheafObjIsoRightDerivedSectionsPinned`.** -/
lemma cohomologyPresheafObjIsoRightDerivedSectionsPinned_hom_zero
    (F : Sheaf J AddCommGrpCat.{max v t}) (U : C) :
    (cohomologyPresheafObjIsoRightDerivedSectionsPinned.{t} J F 0 U).hom =
      (extZeroIsoSections.{t} J U).hom.app F ≫
        ((sheafSections J AddCommGrpCat.{max v t}).obj
          (op U)).rightDerivedZeroIsoSelf.inv.app F := by
  show (extFunctorObjIsoRightDerivedSections.{t} J U 0).hom.app F = _
  rw [extFunctorObjIsoRightDerivedSections_hom_zero]
  rfl

end EnoughInjectives

section Pinned

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{v}] [HasExt.{v} (Sheaf J AddCommGrpCat.{v})]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{v})]

/-- **Mathlib's sheaf cohomology over an object of the site is right-derived sections**, as a
pinned construction: `sheafCohomologyIsoRightDerivedSections` with the comparison of the
cohomology presheaf with right-derived sections taken in its pinned form
`cohomologyPresheafObjIsoRightDerivedSectionsPinned` rather than as a choice. It has a
degree-zero normalisation, `sheafCohomologyIsoRightDerivedSectionsPinned_hom_zero`, and is the
degree-`p` component of an isomorphism of `δ`-functors,
`extDeltaFunctorIsoRightDerivedSections`. -/
@[sga "4 V 2.1.2" "H^q(X, special case"]
def sheafCohomologyIsoRightDerivedSectionsPinned (F : Sheaf J AddCommGrpCat.{v}) (p : ℕ) (T : C) :
    Sheaf.H' F p T ≅
      (((sheafSections J AddCommGrpCat.{v}).obj (op T)).rightDerived p).obj F :=
  (cohomologyPresheafObjIsoPinned.{v} J F p T).symm ≪≫
    cohomologyPresheafObjIsoRightDerivedSectionsPinned.{v} J F p T

/-- **The degree-zero normalisation of `sheafCohomologyIsoRightDerivedSectionsPinned`**: the
pinned identification of `CategoryTheory.Sheaf.H'` with the cohomology presheaf, followed by
`extZeroIsoSections` and the inverse of `CategoryTheory.Functor.rightDerivedZeroIsoSelf`. -/
lemma sheafCohomologyIsoRightDerivedSectionsPinned_hom_zero
    (F : Sheaf J AddCommGrpCat.{v}) (T : C) :
    (sheafCohomologyIsoRightDerivedSectionsPinned.{v} J F 0 T).hom =
      (cohomologyPresheafObjIsoPinned.{v} J F 0 T).inv ≫
        (extZeroIsoSections.{v} J T).hom.app F ≫
          ((sheafSections J AddCommGrpCat.{v}).obj
            (op T)).rightDerivedZeroIsoSelf.inv.app F := by
  show (cohomologyPresheafObjIsoPinned.{v} J F 0 T).inv ≫
    (cohomologyPresheafObjIsoRightDerivedSectionsPinned.{v} J F 0 T).hom = _
  rw [cohomologyPresheafObjIsoRightDerivedSectionsPinned_hom_zero]
  rfl

end Pinned

end

end Stacks.Cohomology.FreeYonedaUnivLE

end
