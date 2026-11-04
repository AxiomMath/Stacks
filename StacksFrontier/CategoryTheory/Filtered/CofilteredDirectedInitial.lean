module

public import Mathlib.CategoryTheory.Presentable.Directed

/-!
# A cofiltered category receives an initial functor from a codirected order

Deligne's lemma (Stacks 0032), in Mathlib as `CategoryTheory.IsFiltered.exists_directed`, gives
for a small filtered category `J` a directed partial order `α` and a final functor `α ⥤ J`.
Applied to the opposite of a small cofiltered category `I` it gives a directed partial order `α`
and an initial functor `αᵒᵖ ⥤ I`. Along an initial functor, cones over a diagram out of `I` are
limiting exactly when their whiskerings are, so a limit indexed by an arbitrary cofiltered
category is also a limit indexed by the opposite of a directed set — the shape of the inverse
systems of the source (Situations 084R, 084W). This is how results stated for directed inverse
systems are applied to the cofiltered systems over which Artin's Axioms, Definition 07XL
quantifies.

## Main results

* `CategoryTheory.IsCofiltered.exists_directed_initial`: the initial functor from the opposite of
  a directed partial order.
* `CategoryTheory.IsCofiltered.isLimit_whisker_directed`: the reindexed cone of a limit cone is
  limiting.

## References

* [Stacks Project, Tag 0032](https://stacks.math.columbia.edu/tag/0032)
* [Stacks Project, Tag 07XL](https://stacks.math.columbia.edu/tag/07XL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace CategoryTheory.IsCofiltered

/-- **Stacks 0032, for cofiltered categories.** A small cofiltered category `I` receives an
initial functor from the opposite of a nonempty directed partial order. -/
theorem exists_directed_initial (I : Type w) [SmallCategory I] [IsCofiltered I] :
    ∃ (α : Type w) (_ : PartialOrder α) (_ : IsDirected α (· ≤ ·)) (_ : Nonempty α)
      (F : αᵒᵖ ⥤ I), F.Initial := by
  obtain ⟨α, _, _, _, F, _⟩ := IsFiltered.exists_directed Iᵒᵖ
  exact ⟨α, _, inferInstance, inferInstance, F.leftOp, inferInstance⟩

/-- A limit cone over a diagram out of a cofiltered category stays limiting when reindexed along
an initial functor, for instance the one of
`CategoryTheory.IsCofiltered.exists_directed_initial`. -/
noncomputable def isLimit_whisker_directed {I : Type w} [SmallCategory I] {α : Type w}
    [PartialOrder α] (F : αᵒᵖ ⥤ I) [F.Initial] {C : Type u} [Category.{v} C] {D : I ⥤ C}
    {c : Cone D} (hc : IsLimit c) : IsLimit (c.whisker F) :=
  (Functor.Initial.isLimitWhiskerEquiv F c).symm hc

end CategoryTheory.IsCofiltered

end
