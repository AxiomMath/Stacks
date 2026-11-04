module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LeftExact

/-!
# Abelian sheafification with larger coefficients

The coefficient universe may exceed both universes of the site. Filtered-colimit
preservation restricts to the site's size, and the characterization of sheafification
equivalences transports from a small model in the coefficient universe.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace Stacks.Sites.UniverseBridge

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)

/-- Abelian sheafification exists in any coefficient universe containing the site's sizes. -/
theorem hasWeakSheafify_addCommGrp : HasWeakSheafify J AddCommGrpCat.{max u w} := by
  let : PreservesFilteredColimitsOfSize.{u, u}
      (forget AddCommGrpCat.{max u w}) :=
    preservesFilteredColimitsOfSize_shrink (forget AddCommGrpCat.{max u w})
  infer_instance

/-- Abelian sheafification in a larger universe inverts precisely the locally bijective maps. -/
theorem wEqualsLocallyBijective_addCommGrp :
    J.WEqualsLocallyBijective AddCommGrpCat.{max u w} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, max u w,
    u, (max u w) + 1, max u w} J

end Stacks.Sites.UniverseBridge

end
