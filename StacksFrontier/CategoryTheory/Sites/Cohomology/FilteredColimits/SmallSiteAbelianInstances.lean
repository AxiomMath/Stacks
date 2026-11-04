module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Sites.GlobalSections
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Abelian sheaves on a site: enough injectives, and additivity of global sections

Facts about sheaves with values in an abelian category that the global-cohomology development
needs in every one of its steps. All are one-line consequences of Mathlib results — `Sheaf J Ab`
is a Grothendieck abelian category for a small site, and global sections preserve binary
products — and none is available to instance search as stated, so each consumer has to install
it locally.

They are collected here, as plain statements rather than instances, so that the modules of the
development install the same declarations with `attribute [local instance]` instead of restating
them. That keeps the global instance set unchanged: nothing here is an instance, and each
consumer's `local instance` scope is exactly what it was.

## Main results

* `Stacks.Cohomology.ColimitsOfCohomology.enoughInjectives_sheaf_ab`: abelian sheaves on a small
  site have enough injectives.
* `Stacks.Cohomology.ColimitsOfCohomology.additive_sheafΓ`: global sections of sheaves with
  values in an abelian category is an additive functor.
* `Stacks.Cohomology.ColimitsOfCohomology.additive_globalSections_ab`: its special case for
  abelian sheaves on a small site.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.ColimitsOfCohomology

universe u

/-- Abelian sheaves on a small site have enough injectives: the category is Grothendieck abelian.
Stated rather than registered, so that a consumer installs it with
`attribute [local instance]` and no global instance set changes. -/
@[sga "4 I 7.13" "special case", sga "4½ Arcata 1.6.3" "special case"]
theorem enoughInjectives_sheaf_ab {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) :
    EnoughInjectives (Sheaf J (Ab.{u})) :=
  IsGrothendieckAbelian.enoughInjectives

/-- The global sections functor on sheaves with values in an abelian category is additive, being
a right adjoint and hence preserving binary products. Stated rather than registered, for the
same reason as `enoughInjectives_sheaf_ab`. -/
theorem additive_sheafΓ {C : Type*} [Category* C] (J : GrothendieckTopology C) (A : Type*)
    [Category* A] [Abelian A] [HasSheafify J A] [HasGlobalSectionsFunctor J A] :
    (Sheaf.Γ J A).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Global sections of abelian sheaves on a small site is additive, preserving binary products.
Stated rather than registered, for the same reason as `enoughInjectives_sheaf_ab`. -/
theorem additive_globalSections_ab {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) :
    (Sheaf.Γ J (Ab.{u})).Additive :=
  additive_sheafΓ J _

end Stacks.Cohomology.ColimitsOfCohomology

end
