module

public import Mathlib.SetTheory.Cardinal.EventuallyConst
public import StacksFrontier.Homology.Injectives.Size.SubobjectCardinality
import StacksCore.Tactic.StacksAttribute

/-!
# Eventually constant chains of subobjects

Let `C` be an abelian category with a separator `U` and let `X` be an object of `C`. The final
clause of Tag 0E8N says that a monotone (or antitone) chain of subobjects of `X`, indexed by a
well-ordered type whose cofinality exceeds the number of morphisms `U ⟶ X`, is eventually
constant.

The proof is a cofinality argument on top of the chain bound
`Stacks.Injectives.cardinality_le_hom_of_strictMono_subobject`. If the chain were *not*
eventually constant then, by `Filter.EventuallyConst.of_not_isCofinal_rangeSplitting`, the set
of indices picked out by `Set.rangeSplitting f` would be cofinal in the index type; on that set
the chain is strictly monotone, so the chain bound caps its cardinality by `#(U ⟶ X)`, and
`Order.cof_le` then caps the cofinality of the index type by the same cardinal — contradicting
the hypothesis.

## Main definitions

No new definitions are introduced.

## Main results

* `Stacks.Injectives.eventuallyConst_subobject_of_monotone`: an increasing chain of subobjects
  indexed by a well-order of large cofinality is eventually constant.
* `Stacks.Injectives.eventuallyConst_subobject_of_antitone`: the same for a decreasing chain.

## Implementation notes

The index is an arbitrary well-ordered type together with the hypothesis on its order
cofinality `Order.cof`; an ordinal provides such a type through `Ordinal.ToType`. Eventual
constancy is `Filter.EventuallyConst` for the filter `Filter.atTop`. As with the chain bounds of
`StacksDraft.Ch19.Sec11.SubobjectCardinality`, the increasing and decreasing cases are stated
separately.

Mathlib's `Filter.EventuallyConst.of_monotone_of_lt_cof` is the same cofinality argument run
against a bound on `#(Subobject X)` itself; here the available bound is on `#(U ⟶ X)` instead,
which is why the argument is repeated rather than invoked.

## References

* [Stacks Project, Tag 0E8N](https://stacks.math.columbia.edu/tag/0E8N)
-/

@[expose] public section

open CategoryTheory Filter

universe w v u

namespace Stacks.Injectives

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A monotone map becomes strictly monotone when restricted to the set of indices chosen by
`Set.rangeSplitting`, since it takes each value there exactly once. -/
theorem strictMono_restrict_rangeSplitting {α : Type*} {β : Type*}
    [LinearOrder α] [PartialOrder β] {f : α → β} (hf : Monotone f) :
    StrictMono fun x : Set.range (Set.rangeSplitting f) => f x.1 := by
  have hm : Monotone fun x : Set.range (Set.rangeSplitting f) => f x.1 := fun _ _ h => hf h
  refine hm.strictMono_of_injective ?_
  intro x y h
  obtain ⟨p, hp⟩ := x.2
  obtain ⟨q, hq⟩ := y.2
  have hpq : p = q := Subtype.ext (by
    rw [← Set.apply_rangeSplitting f p, ← Set.apply_rangeSplitting f q]
    simpa only [Function.comp_apply, hp, hq] using h)
  exact Subtype.ext (hp.symm.trans ((congrArg _ hpq).trans hq))

/-- **Stacks 0E8N.** An increasing well-ordered chain of subobjects is eventually constant if
the cofinality of the index order exceeds the number of morphisms from a separator to the
ambient object. -/
@[stacks 0E8N "eventually constant"]
theorem eventuallyConst_subobject_of_monotone {U X : C} (hU : IsSeparator U)
    {α : Type w} [LinearOrder α] [WellFoundedLT α]
    (hcof : Cardinal.lift.{w} (Cardinal.mk (U ⟶ X)) <
      Cardinal.lift.{v} (Order.cof α)) (f : α → Subobject X) (hf : Monotone f) :
    atTop.EventuallyConst f := by
  classical
  have : Nonempty α := by by_contra!; simp at hcof
  refine Filter.EventuallyConst.of_not_isCofinal_rangeSplitting hf ?_
  intro hcofinal
  exact absurd hcof (not_lt_of_ge ((Cardinal.lift_le.mpr (Order.cof_le hcofinal)).trans
    (cardinality_le_hom_of_strictMono_subobject hU (fun i => f i.1)
      (strictMono_restrict_rangeSplitting hf))))

/-- **Stacks 0E8N.** A decreasing well-ordered chain of subobjects is eventually constant if
the cofinality of the index order exceeds the number of morphisms from a separator to the
ambient object. -/
@[stacks 0E8N "eventually constant"]
theorem eventuallyConst_subobject_of_antitone {U X : C} (hU : IsSeparator U)
    {α : Type w} [LinearOrder α] [WellFoundedLT α]
    (hcof : Cardinal.lift.{w} (Cardinal.mk (U ⟶ X)) <
      Cardinal.lift.{v} (Order.cof α)) (f : α → Subobject X) (hf : Antitone f) :
    atTop.EventuallyConst f := by
  classical
  have : Nonempty α := by by_contra!; simp at hcof
  show atTop.EventuallyConst (OrderDual.toDual ∘ f)
  refine Filter.EventuallyConst.of_not_isCofinal_rangeSplitting hf.dual_right ?_
  intro hcofinal
  exact absurd hcof (not_lt_of_ge ((Cardinal.lift_le.mpr (Order.cof_le hcofinal)).trans
    (cardinality_le_hom_of_strictAnti_subobject hU (fun i => f i.1)
      (strictMono_restrict_rangeSplitting (f := OrderDual.toDual ∘ f) hf.dual_right))))

end Stacks.Injectives
