module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactDerivedHomologyComposition
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactFunctorBoundedBelow

/-!
# The homology comparison on the bounded below derived category, and composition

The degreewise action of an exact functor on the bounded below derived category,
`CategoryTheory.Functor.mapDerivedCategoryPlus`, is the restriction of its action on the
unbounded derived category along the fully faithful inclusion
`DerivedCategory.Plus.ι`, and the homology functors on the two sides are related the same way.
This file transports the composition law for the homology comparison to the bounded below
setting.

Everything here is the unbounded statement read through `DerivedCategory.Plus.ι`. What makes
that possible without any further work is that the inclusion is fully faithful and that it
intertwines the two levels definitionally: `DerivedCategory.Plus.homologyFunctor` *is*
`DerivedCategory.Plus.ι` followed by the unbounded homology functor, and the degreewise action
on the bounded below derived category is a lift of the unbounded action along the inclusion.

## Main definitions

* `Stacks.DerivedFunctor.mapDerivedCategoryPlusCompIso`: the composite of the degreewise actions
  of two exact functors on the bounded below derived category is the degreewise action of the
  composite — the image under the inclusion of
  `Stacks.DerivedFunctor.mapDerivedCategoryCompIso`.

## Main results

* `Stacks.DerivedFunctor.ι_map_mapDerivedCategoryPlusCompIso_hom_app`: the inclusion carries the
  bounded below comparison to the unbounded one.
* `Stacks.DerivedFunctor.derivedHomologyIso_comp_hom_app_plus`: **the composition law for the
  homology comparison on the bounded below derived category.**

## References

* [Stacks Project, Tag 0EZF](https://stacks.math.columbia.edu/tag/0EZF)
* [Stacks Project, Tag 03Q8](https://stacks.math.columbia.edu/tag/03Q8)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace Stacks.DerivedFunctor

section Plus

variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]
  [Abelian A] [Abelian B] [Abelian C]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
  (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- **The composite of the degreewise actions of two exact functors on the bounded below derived
category is the degreewise action of the composite.** It is the unbounded comparison
`Stacks.DerivedFunctor.mapDerivedCategoryCompIso`, pulled back along the fully faithful
inclusion of the bounded below subcategory. -/
def mapDerivedCategoryPlusCompIso :
    F.mapDerivedCategoryPlus ⋙ G.mapDerivedCategoryPlus ≅
      (F ⋙ G).mapDerivedCategoryPlus :=
  (DerivedCategory.TStructure.t.plus.fullyFaithfulι.whiskeringRight _).preimageIso
    (Functor.isoWhiskerLeft DerivedCategory.Plus.ι (mapDerivedCategoryCompIso F G))

/-- The inclusion of the bounded below subcategory carries the comparison of the degreewise
actions to the unbounded one. -/
theorem ι_map_mapDerivedCategoryPlusCompIso_hom_app (K : DerivedCategory.Plus A) :
    DerivedCategory.Plus.ι.map ((mapDerivedCategoryPlusCompIso F G).hom.app K) =
      (mapDerivedCategoryCompIso F G).hom.app (DerivedCategory.Plus.ι.obj K) := by
  have h : Functor.whiskerRight (mapDerivedCategoryPlusCompIso F G).hom
        DerivedCategory.Plus.ι =
      (Functor.isoWhiskerLeft DerivedCategory.Plus.ι
        (mapDerivedCategoryCompIso F G)).hom :=
    (DerivedCategory.TStructure.t.plus.fullyFaithfulι.whiskeringRight _).map_preimage _
  exact congr_app h K

/-- **The homology comparison of an exact functor is compatible with composition, on the bounded
below derived category.** -/
theorem derivedHomologyIso_comp_hom_app_plus (n : ℤ) (K : DerivedCategory.Plus A) :
    (derivedHomologyIso G n).hom.app
          (DerivedCategory.Plus.ι.obj (F.mapDerivedCategoryPlus.obj K)) ≫
        G.map ((derivedHomologyIso F n).hom.app (DerivedCategory.Plus.ι.obj K)) =
      (DerivedCategory.Plus.homologyFunctor C n).map
          ((mapDerivedCategoryPlusCompIso F G).hom.app K) ≫
        (derivedHomologyIso (F ⋙ G) n).hom.app (DerivedCategory.Plus.ι.obj K) := by
  have h : (DerivedCategory.Plus.homologyFunctor C n).map
        ((mapDerivedCategoryPlusCompIso F G).hom.app K) =
      (DerivedCategory.homologyFunctor C n).map
        ((mapDerivedCategoryCompIso F G).hom.app (DerivedCategory.Plus.ι.obj K)) := by
    rw [← ι_map_mapDerivedCategoryPlusCompIso_hom_app]
    rfl
  rw [h]
  exact derivedHomologyIso_comp_hom_app F G n (DerivedCategory.Plus.ι.obj K)

end Plus

end Stacks.DerivedFunctor

end
