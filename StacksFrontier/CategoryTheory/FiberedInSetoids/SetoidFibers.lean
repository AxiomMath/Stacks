module

public import StacksFrontier.CategoryTheory.FiberedInSetoids.Defs
public import StacksFrontier.CategoryTheory.FiberedInSetoids.Setoid

/-!
# Categories fibred in setoids have setoid fibres (Stacks 04SA)

Stacks Tag `04SA` (Definition 4.39.1) calls `p : 𝒳 ⥤ 𝒮` a category fibred in setoids when it is
fibred in groupoids and all of its fibre categories are setoids, a *setoid* (Stacks `02XZ`) being a
groupoid in which every object has exactly one automorphism, the identity. The library's
`CategoryTheory.Functor.IsFiberedInSetoids` asks for thin fibres instead; this file proves that the
two say the same thing.

## Main results

* `CategoryTheory.Functor.isFiberedInSetoids_iff`: `p` is fibred in setoids iff it is fibred in
  groupoids and every fibre category is a setoid (`IsSetoidCategory`).

## References

* [Stacks Project, Definition 4.39.1 (Tag 04SA)](https://stacks.math.columbia.edu/tag/04SA)
-/

@[expose] public section

namespace CategoryTheory.Functor

universe v₁ v₂ u₁ u₂

variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category.{v₁} 𝒮] [Category.{v₂} 𝒳]

/-- **Stacks 04SA.** A functor `p : 𝒳 ⥤ 𝒮` is fibred in setoids if and only if it is fibred in
groupoids (Stacks `003T`) and every fibre category `p.Fiber S` is a setoid in the sense of Stacks
`02XZ`: a groupoid in which every object has exactly one automorphism, the identity. -/
@[stacks 04SA "Stacks' definition verbatim: fibred in groupoids, and every fibre category is a \
setoid (`IsSetoidCategory`, Stacks 02XZ)."]
theorem isFiberedInSetoids_iff (p : 𝒳 ⥤ 𝒮) :
    p.IsFiberedInSetoids ↔
      p.IsFiberedInGroupoids ∧ ∀ S : 𝒮, IsSetoidCategory (p.Fiber S) := by
  refine ⟨fun hp ↦ ⟨hp.isFiberedInGroupoids, fun S ↦ ⟨fun f ↦ ?_, fun X f ↦ ?_⟩⟩, ?_⟩
  · have := hp.isFiberedInGroupoids.fiber_isGroupoid S
    exact IsGroupoid.all_isIso f
  · have := hp.fiber_isThin S X X
    exact Subsingleton.elim _ _
  · rintro ⟨hg, hs⟩
    refine ⟨hg, fun S a b ↦ ⟨fun f g ↦ ?_⟩⟩
    have := (hs S).1 g
    have h := (hs S).2 a (f ≫ CategoryTheory.inv g)
    simpa using congrArg (· ≫ g) h

end CategoryTheory.Functor
