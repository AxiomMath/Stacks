module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Injective
public import Mathlib.CategoryTheory.Abelian.Exact
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexOfAFamily
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.InjectivePresheafVanishing
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.IntegralComplex
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.IntegralComplexIsAResolution
public import StacksCore.Tactic.StacksAttribute

/-!
# Čech cohomology of an injective presheaf

The positive-degree Čech cohomology of an injective presheaf of abelian groups vanishes for
every family of morphisms for which the Čech complex is defined.

## Main results

* `Stacks.CechSite.injective_presheaf_cechCohomology_isZero` (imported, and carrying
  `@[stacks 03OR]`): positive-degree Čech cohomology of an injective abelian presheaf
  vanishes.

## Implementation notes

A family of morphisms with fixed target is represented by a `PreZeroHypercover`. The finite
nonempty fibre products needed for its Čech complex are expressed as products in the over
category. Vanishing of the resulting abelian group object is expressed by `IsZero`. The
coefficient universe contains the object, morphism and family-index universes, so the free
abelian Čech complex used in the source's proof belongs to the same presheaf category as the
injective object.

## References

* [Stacks Project, Tag 03OR](https://stacks.math.columbia.edu/tag/03OR)
-/

@[expose] public section

universe w v u u'

namespace Stacks.CechSite

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {X : C} (E : PreZeroHypercover.{w} X)
  [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun a ↦ Over.mk (E.f (i a)))]
  (I : Cᵒᵖ ⥤ AddCommGrpCat.{max w u' u v}) [Injective I]

-- NO `injective_cechCohomology_isZero` HERE. It restated, with the identical `variable`
-- block and instance arguments, the theorem that proves it:
-- `Stacks.CechSite.injective_presheaf_cechCohomology_isZero`
-- (`StacksFrontier/CategoryTheory/Sites/Cohomology/Cech/InjectivePresheafVanishing.lean`:63),
-- which this module already imports at :8. `@[stacks 03OR]` moved onto that theorem, which
-- is the declaration covering the content.

end Stacks.CechSite
