module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Sites.Equivalence
public import StacksFrontier.CategoryTheory.Sites.AbelianSheafificationExistence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.RingedToposOfAFibredCategory

/-!
# Sheafification of abelian groups on a site, in a large enough universe

Presheaves of `AddCommGrpCat.{t}` on a site whose objects and morphisms both inject into `Type t`
admit sheafification, and the resulting category of abelian sheaves is Grothendieck abelian.

## Main results

* `Stacks.Sites.FibredCategory.hasSheafify_addCommGrpCat`: sheafification exists.
* `Stacks.Sites.FibredCategory.isGrothendieckAbelian_sheaf_addCommGrpCat`: the sheaf category is
  Grothendieck abelian.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Sites.FibredCategory

/-- Abelian groups valued in a universe containing both the objects and the morphisms of a site
admit sheafification on it. -/
theorem hasSheafify_addCommGrpCat.{u, v, t} {E : Type u} [Category.{v} E]
    (K : GrothendieckTopology E) [UnivLE.{u, t}] [UnivLE.{v, t}] :
    HasSheafify K AddCommGrpCat.{t} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall K

/-- Abelian sheaves on a site, with sections in a universe containing both the objects and the
morphisms of the site, form a Grothendieck abelian category. -/
theorem isGrothendieckAbelian_sheaf_addCommGrpCat.{u, v, t} {E : Type u} [Category.{v} E]
    (K : GrothendieckTopology E) [UnivLE.{u, t}] [UnivLE.{v, t}]
    [HasSheafify K AddCommGrpCat.{t}] :
    IsGrothendieckAbelian.{t} (Sheaf K AddCommGrpCat.{t}) := by
  let _ : HasSheafify ((equivSmallModel.{t} E).inverse.inducedTopology K) AddCommGrpCat.{t} :=
    inferInstance
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall.{t, t, v, t + 1, u} K _

end Stacks.Sites.FibredCategory

end
