module
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.FreeYonedaSectionsUnivLE
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.RightDerivedSectionsEssentiallySmall
import all StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.RightDerivedSectionsEssentiallySmall

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.BigSiteObjectCohomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.FreeYonedaRightDerivedUnivLE
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# Naturality of the comparison of sheaf cohomology with right-derived sections

The isomorphism `sheafCohomologyIsoRightDerivedSections` between the cohomology of an abelian
sheaf on an object `T` and the right-derived functors of the sections functor at `T`, evaluated
at that sheaf, is natural in the sheaf.

## Main results

* `sheafCohomologyIsoRightDerivedSections_hom_naturality`: The forward isomorphism is natural in
  the sheaf.
* `sheafCohomologyIsoRightDerivedSections_inv_naturality`: The inverse isomorphism is natural in
  the sheaf.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Abelian

namespace ModuleSheafCohomology

universe w v u

noncomputable section

end

end ModuleSheafCohomology

namespace Stacks.Cohomology.FreeYonedaUnivLE

universe s t v u

noncomputable section

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max v t}]
  [HasExt.{max v t} (Sheaf J AddCommGrpCat.{max v t})]

section EnoughInjectives

variable [EnoughInjectives (Sheaf J AddCommGrpCat.{max v t})]

end EnoughInjectives

section Pinned

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{v}] [HasExt.{v} (Sheaf J AddCommGrpCat.{v})]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{v})]

/-- **`sheafCohomologyIsoRightDerivedSections` is natural in the sheaf.** Both of its factors are
components of natural isomorphisms of functors on abelian sheaves: the comparison of the two free
abelian sheaves on `T`, transported along `CategoryTheory.Abelian.extFunctor`, and the chosen
identification of `Ext` out of the free abelian sheaf with right-derived sections. -/
theorem sheafCohomologyIsoRightDerivedSections_hom_naturality
    {F G : Sheaf J AddCommGrpCat.{v}} (ψ : F ⟶ G) (p : ℕ) (T : C) :
    ((Sheaf.cohomologyPresheafFunctor J p).map ψ).app (op T) ≫
        (sheafCohomologyIsoRightDerivedSections J G p T).hom =
      (sheafCohomologyIsoRightDerivedSections J F p T).hom ≫
        (((sheafSections J AddCommGrpCat.{v}).obj (op T)).rightDerived p).map ψ :=
  (((extFunctor.{v} p).map ((freeYonedaIso J).app T).hom.op) ≫
    (nonempty_extFunctorObj_iso_rightDerived_sections_of_enoughInjectives.{v}
      J T p).some.hom).naturality ψ

/-- `sheafCohomologyIsoRightDerivedSections_hom_naturality`, for the inverse. -/
theorem sheafCohomologyIsoRightDerivedSections_inv_naturality
    {F G : Sheaf J AddCommGrpCat.{v}} (ψ : F ⟶ G) (p : ℕ) (T : C) :
    (sheafCohomologyIsoRightDerivedSections J F p T).inv ≫
        ((Sheaf.cohomologyPresheafFunctor J p).map ψ).app (op T) =
      (((sheafSections J AddCommGrpCat.{v}).obj (op T)).rightDerived p).map ψ ≫
        (sheafCohomologyIsoRightDerivedSections J G p T).inv := by
  rw [Iso.inv_comp_eq,
    ← reassoc_of% (sheafCohomologyIsoRightDerivedSections_hom_naturality J ψ p T),
    Iso.hom_inv_id, Category.comp_id]

end Pinned

section EssentiallySmall

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{v}]

section

attribute [local instance] enoughInjectives_essentiallySmallSite hasExt_essentiallySmallSite

end

end EssentiallySmall

end

end Stacks.Cohomology.FreeYonedaUnivLE

end
