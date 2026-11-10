module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCategories.ContActionForget
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCategory.FieldFundamentalGroup
public import StacksCore.Tactic.StacksAttribute

/-!
# Finite `G`-sets and the forgetful functor to sets

For a topological group `G`, [Stacks, Tag 0BMS] names two things: the full subcategory
`Finite-G-Sets` of the category `G-Sets` of [Stacks, Tag 04JJ] on the finite objects, and the
forgetful functor `Finite-G-Sets ⟶ Sets`, whose notation [Stacks, Tag 0BMT] the later tags
0BMU, 0BMV and 0BN0 use.

## Main results

* `CategoryTheory.exists_forget_fiberFunctor_contActionFintypeCat` — the forgetful functor of
  the tag exists on continuous actions of `G` on finite sets, and is a fibre functor preserving
  finite limits and finite colimits; composed with the inclusion of finite sets into sets it is
  the forgetful functor to sets.
* `CategoryTheory.equiv_finiteContinuousGSet` — the full subcategory of `G-Sets` on the finite
  objects is the category of continuous actions of `G` on finite sets.

## Implementation notes

The tag asserts no proposition: it introduces notation. So the two results here are naming
statements in the existential-witness style this repository uses for Example tags, and together
they form the covering set — the first for the forgetful functor, the second for the identification
of `Finite-G-Sets`.

Everything is assembled from results already in the library; nothing new is proved. The
fibre-functor and exactness instances come from
`StacksFrontier/AlgebraicGeometry/FundamentalGroup/GaloisCategories/ContinuousActions.lean` and
`StacksFrontier/AlgebraicGeometry/FundamentalGroup/GaloisCategories/ContActionForget.lean`, and the
identification of the full subcategory from
`AlgebraicGeometry.finiteContinuousGSetEquivalence`.

The two statements cannot be folded into one. `AlgebraicGeometry.finiteContinuousGSetEquivalence`
is not bi-universe-polymorphic: it pins the universe of `G` to the universe of the sets acted on,
whereas `AlgebraicGeometry.FiniteContinuousGSet` itself lives in `Type (max u₁ (u₂ + 1))`. A single
combined statement therefore fails to elaborate.

What this file deliberately does **not** claim is that the forgetful functor makes
`Finite-G-Sets` a Galois category. That is not what Tag 0BMS says — it is the content of the later
tags — and it does not follow by instance search, the connected-decomposition axiom requiring a
real proof.

Mathlib's `Mathlib/CategoryTheory/Galois/Examples.lean` treats `Action FintypeCat G` for a
*discrete* group, which is a strictly larger category than the one this tag names; the topological
case is the repository's own `ContAction`.

## References

* [Stacks Project, Tag 0BMS](https://stacks.math.columbia.edu/tag/0BMS)
* [Stacks Project, Tag 04JJ](https://stacks.math.columbia.edu/tag/04JJ)
-/

@[expose] public section

open CategoryTheory Limits
open scoped FintypeCatDiscrete

namespace CategoryTheory

universe u v

/-- **Stacks 0BMS**, the forgetful functor. For a topological group `G` there is a functor from
the category of continuous actions of `G` on finite sets to finite sets which is a fibre functor,
preserves finite limits and finite colimits, and which becomes the forgetful functor to sets after
composing with the inclusion of finite sets into sets. -/
@[stacks 0BMS "the forgetful functor from finite `G`-sets", sga "1 V 5.1" "partial"]
theorem exists_forget_fiberFunctor_contActionFintypeCat
    (G : Type v) [Group G] [TopologicalSpace G] :
    ∃ F : ContAction FintypeCat.{u} G ⥤ FintypeCat.{u},
      PreGaloisCategory.FiberFunctor F ∧
      PreservesFiniteLimits F ∧ PreservesFiniteColimits F ∧
      Nonempty (F ⋙ FintypeCat.incl ≅ forget (ContAction FintypeCat.{u} G)) :=
  ⟨forget₂ _ _, inferInstance, inferInstance, inferInstance, ⟨forget₂InclIso⟩⟩

/-- **Stacks 0BMS**, the subcategory. The full subcategory of the category `G-Sets` of
[Stacks, Tag 04JJ] on the finite objects is the category of continuous actions of `G` on finite
sets. -/
@[stacks 0BMS "the full subcategory of `G`-Sets on the finite objects"]
theorem equiv_finiteContinuousGSet (G : Type u) [Group G] [TopologicalSpace G] :
    Nonempty (AlgebraicGeometry.FiniteContinuousGSet.{u, u} G ≌ ContAction FintypeCat.{u} G) :=
  ⟨AlgebraicGeometry.finiteContinuousGSetEquivalence⟩

end CategoryTheory

end
