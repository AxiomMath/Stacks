module

public import StacksFrontier.AlgebraicGeometry.FilteredCardIndex.Basic
public import StacksFrontier.AlgebraicGeometry.FinitelyPresentableComposition.Basic

/-!
# The composed two-stage colimit in the shape a Stacks tag asks for

`Stacks.FinitelyPresentableComposition.exists_isColimit_of_twoStage` delivers the composed colimit
over a filtered *category*.  [Stacks, Tag 0817] asks instead for a **directed preorder** in a fixed
universe, and that reindexing is already available, in general, as
`Stacks.FilteredCardIndex.exists_directed_index_of_isFiltered` (filtered plus essentially small,
no order hypothesis, via `CategoryTheory.IsFiltered.exists_directed`).  This file composes the
two, which is the only thing it does.

The smallness hypothesis of the reindexing is free here: the index of the composed system is
`CategoryTheory.InducedCategory` on the objects of `Σ i, K i`, hence a `SmallCategory` in
`Type w`, and a small category is essentially `w`-small by instance search.

## Main results

* `Stacks.FinitelyPresentableComposition.exists_directed_index_of_twoStage`: a filtered colimit of
  filtered colimits of finitely presentable objects is a colimit over a **nonempty directed
  preorder in `Type w`**, every object of the diagram being a stage of the inner systems.

## What is not done, and no stacks attribute

**No `@[stacks]` attribute is attached.** This is still a statement about an arbitrary category
with a presentability hypothesis on the stages, not about algebra sheaves on a scheme; for
[Stacks, Tag 0817] part (2) the hypothesis `hfp` has to be discharged, and
[Stacks, Tag 01BS] is one way to do that — `hfp` is
`Stacks.FinitelyPresentableComposition.TwoStagePresentable`, which asks presentability only along
the cocones being composed and is therefore weaker than that tag.

## References

* [Stacks Project, Tag 0817](https://stacks.math.columbia.edu/tag/0817)
* [Stacks Project, Tag 01BS](https://stacks.math.columbia.edu/tag/01BS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace Stacks.FinitelyPresentableComposition

attribute [local instance] Cardinal.fact_isRegular_aleph0

variable {C : Type u} [Category.{w} C] {A : C}
  {I : Type w} [SmallCategory I] [IsFiltered I] {D : I ⥤ C}
  (t : D ⟶ (Functor.const I).obj A)
  {K : I → Type w} [∀ i, SmallCategory (K i)] [∀ i, IsFiltered (K i)]
  {E : ∀ i, K i ⥤ C} (s : ∀ i, E i ⟶ (Functor.const (K i)).obj (D.obj i))
  (ht : IsColimit (Cocone.mk A t)) (hs : ∀ i, IsColimit (Cocone.mk (D.obj i) (s i)))
  (hfp : TwoStagePresentable t s)

include ht hs hfp in
/-- **A filtered colimit of filtered colimits of finitely presentable objects is a directed
colimit over a preorder in `Type w` of those objects.**

This is `Stacks.FinitelyPresentableComposition.exists_isColimit_of_twoStage` followed by
`Stacks.FilteredCardIndex.exists_directed_index_of_isFiltered`.  The conclusion is the shape
[Stacks, Tag 0817] states its two parts in: an index type in the universe of the inner and outer
indices, a preorder on it which is nonempty and directed, a diagram, and a colimiting cocone with
vertex `A`, with every object of the diagram satisfying whatever the stages satisfy. -/
theorem exists_directed_index_of_twoStage (P : C → Prop)
    (hP : ∀ (i : I) (k : K i), P ((E i).obj k)) :
    ∃ (J : Type w) (_ : Preorder J) (_ : Nonempty J) (_ : IsDirected J (· ≤ ·))
      (F : J ⥤ C) (σ : F ⟶ (Functor.const J).obj A) (_ : IsColimit (Cocone.mk A σ)),
      ∀ j, P (F.obj j) := by
  have : IsFiltered (Index t s) := isFiltered_index t s hfp
  exact Stacks.FilteredCardIndex.exists_directed_index_of_isFiltered (coconeIndex t s).ι
    (isColimit_coconeIndex t s ht hs hfp) P fun p => hP p.1 p.2

end Stacks.FinitelyPresentableComposition

end
