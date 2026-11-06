module

public import Mathlib.CategoryTheory.ObjectProperty.FiniteLimits
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import Mathlib.CategoryTheory.Limits.FullSubcategory

/-!
# Closure under finite limits from closure under finite products and equalizers

A property of objects `P : ObjectProperty C` in a category with finite limits is closed under
finite limits as soon as it is closed under finite products and under equalizers: a limit of a
finite diagram is the equalizer of two maps between two finite products of the objects of the
diagram, so no other shape has to be examined.

The point of the reduction is that the shapes `Discrete ι` and `WalkingParallelPair` have *no
nonidentity composable pairs of morphisms*. A verification of closure under a general finite shape
has to produce a diagram in the subcategory, hence a *functorial* choice of lift for every
morphism of the shape; after the reduction only two parallel morphisms have to be lifted and the
functoriality obligation disappears. This is what makes the criterion usable for closure
properties which are only available locally, such as finite local constancy of a sheaf of sets.

## Main results

* `CategoryTheory.ObjectProperty.IsClosedUnderFiniteLimits.mk'` — closure under finite limits
  from closure under finite products and equalizers.
* `CategoryTheory.ObjectProperty.IsClosedUnderFiniteColimits.mk'` — closure under finite colimits
  from closure under finite coproducts and coequalizers.

## References

* [Stacks Project, Tag 002N](https://stacks.math.columbia.edu/tag/002N)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C] (P : ObjectProperty C)

/-- A property of objects of a category with finite limits which is closed under isomorphisms,
finite products and equalizers is closed under all finite limits. -/
lemma IsClosedUnderFiniteLimits.mk' [HasFiniteLimits C] [P.IsClosedUnderIsomorphisms]
    [P.IsClosedUnderFiniteProducts] [P.IsClosedUnderLimitsOfShape WalkingParallelPair] :
    P.IsClosedUnderFiniteLimits := by
  have hfin : HasFiniteLimits P.FullSubcategory :=
    hasFiniteLimits_of_hasEqualizers_and_finite_products
  have hprod : PreservesFiniteProducts P.ι := ⟨fun _ ↦ inferInstance⟩
  have hpres : PreservesFiniteLimits P.ι :=
    preservesFiniteLimits_of_preservesEqualizers_and_finiteProducts P.ι
  exact ⟨fun _ _ _ ↦ P.isClosedUnderLimitsOfShape_of_preservesLimitsOfShape_ι _⟩

/-- A property of objects of a category with finite colimits which is closed under isomorphisms,
finite coproducts and coequalizers is closed under all finite colimits. -/
lemma IsClosedUnderFiniteColimits.mk' [HasFiniteColimits C] [P.IsClosedUnderIsomorphisms]
    [P.IsClosedUnderFiniteCoproducts] [P.IsClosedUnderColimitsOfShape WalkingParallelPair] :
    P.IsClosedUnderFiniteColimits := by
  have hfin : HasFiniteColimits P.FullSubcategory :=
    hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts
  have hcoprod : PreservesFiniteCoproducts P.ι := ⟨fun _ ↦ inferInstance⟩
  have hpres : PreservesFiniteColimits P.ι :=
    preservesFiniteColimits_of_preservesCoequalizers_and_finiteCoproducts P.ι
  exact ⟨fun _ _ _ ↦ P.isClosedUnderColimitsOfShape_of_preservesColimitsOfShape_ι _⟩

end CategoryTheory.ObjectProperty

end
