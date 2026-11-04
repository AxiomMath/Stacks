module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import StacksFrontier.Homology.DerivedCategory.LocallySmall

/-!
# The degreewise derived functor of an exact functor preserves direct sums

Let `A` and `B` be abelian categories with their morphisms in a universe `v`, both Grothendieck
abelian relative to `v`, and let `F : A ⥤ B` be an exact additive functor preserving direct sums
indexed by a type `J` in `Type v`. Then the degreewise derived functor
`CategoryTheory.Functor.mapDerivedCategory` of `F` preserves `J`-indexed direct sums, at any
choice of model of the two derived categories.

The functor on complexes preserves direct sums, because colimits of complexes are computed
degreewise, and `DerivedCategory.Q` preserves direct sums on a Grothendieck abelian category
(`Stacks.SmallDerivedCategory.derivedCategoryQ_preservesCoproducts`, [Stacks, Tag 07D9]) and is
essentially surjective; so the property transfers from `Q ⋙ F_*` to `F_*` by
`preservesColimitsOfShape_discrete_of_essSurj_comp`.

## Main results

* `Stacks.SmallDerivedCategory.preservesColimitsOfShape_discrete_mapDerivedCategory`.

## Implementation notes

This is the coefficient-free form of the route taken by
`Stacks.ChaoticSite.preservesColimitsOfShape_discrete_restrictionMapDerivedCategory`, which proves
the same of restriction along a functor between small categories and supplies the preservation of
direct sums by `DerivedCategory.Q` from `EnoughInjectives` instead. That statement is about one
specific functor and keeps the coefficient hypotheses its own setting carries; the statement below
asks only for what the argument uses, namely that both sides are Grothendieck abelian relative to
the universe indexing the direct sums.

## References

* [Stacks Project, Tag 07D9](https://stacks.math.columbia.edu/tag/07D9)
* [Stacks Project, Tag 079Q](https://stacks.math.columbia.edu/tag/079Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe uA uB v

namespace Stacks.SmallDerivedCategory

variable {A : Type uA} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
  [HasDerivedCategory A]
  {B : Type uB} [Category.{v} B] [Abelian B] [IsGrothendieckAbelian.{v} B]
  [HasDerivedCategory B]

/-- **The degreewise derived functor of an exact functor preserves direct sums** indexed by the
universe relative to which the two sides are Grothendieck abelian, as soon as the functor itself
does. -/
theorem preservesColimitsOfShape_discrete_mapDerivedCategory
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (J : Type v) [PreservesColimitsOfShape (Discrete J) F] :
    PreservesColimitsOfShape (Discrete J) F.mapDerivedCategory := by
  let : HasCoproducts.{v} A := fun K ↦ inferInstance
  let : HasCoproducts.{v} B := fun K ↦ inferInstance
  have : PreservesColimitsOfShape (Discrete J) (DerivedCategory.Q (C := A)) :=
    derivedCategoryQ_preservesCoproducts A J
  have : PreservesColimitsOfShape (Discrete J) (DerivedCategory.Q (C := B)) :=
    derivedCategoryQ_preservesCoproducts B J
  have : HasColimitsOfShape (Discrete J) (DerivedCategory B) :=
    hasColimitsOfShape_discrete_derivedCategory B J
  have : PreservesColimitsOfShape (Discrete J)
      (DerivedCategory.Q (C := A) ⋙ F.mapDerivedCategory) :=
    preservesColimitsOfShape_of_natIso F.mapDerivedCategoryFactors.symm
  exact _root_.preservesColimitsOfShape_discrete_of_essSurj_comp
    (DerivedCategory.Q (C := A)) F.mapDerivedCategory J

end Stacks.SmallDerivedCategory

end
