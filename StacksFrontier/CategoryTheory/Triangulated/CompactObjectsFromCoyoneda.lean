module

public import StacksFrontier.CategoryTheory.Triangulated.CompactObjects

/-! # Compactness from preservation of direct sums by the corepresented functor

An object `P` of a preadditive category is compact (`CategoryTheory.IsCompactObject`) exactly
when the additive functor it corepresents, `preadditiveCoyoneda.obj (op P)`, preserves
coproducts of the index types in question. The implication from compactness to preservation is
already in `StacksFrontier.CategoryTheory.Triangulated.CompactObjects`; this file supplies the
converse, which is the form in which compactness is established in practice: one exhibits a
natural isomorphism of `preadditiveCoyoneda.obj (op P)` with a functor already known to commute
with direct sums, and reads off compactness.

The proof has two halves. Injectivity of the compactness map needs no hypothesis and is
`CategoryTheory.injective_cofanMap`. Surjectivity is where the preservation is used: the group
`P ⟶ ∐ E` is the colimit of the groups `P ⟶ E i`, and the image of the compactness map is a
subgroup of it containing every coprojection's image, hence everything.

## Main results

* `CategoryTheory.isCompactObject_of_preservesColimitsOfShape_preadditiveCoyoneda`: an object
  whose corepresented functor preserves `Discrete I`-shaped colimits for every `I : Type w` is
  compact in the sense indexed by `Type w`.

## References

* [Stacks project, Tag 07LS](https://stacks.math.columbia.edu/tag/07LS)
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Limits Opposite Preadditive

/-- An object of a preadditive category is compact as soon as the additive functor it
corepresents preserves coproducts indexed by the relevant types. This is the converse of
`CategoryTheory.preservesColimitsOfShape_discrete_of_isCompactObject`. -/
theorem isCompactObject_of_preservesColimitsOfShape_preadditiveCoyoneda
    {C : Type u} [Category.{v} C] [Preadditive C] (P : C)
    (h : ∀ I : Type w, PreservesColimitsOfShape (Discrete I)
      (preadditiveCoyoneda.obj (op P))) :
    IsCompactObject.{w} P := by
  refine ⟨@fun I _ E _ => ?_⟩
  let := h I
  exact ⟨injective_cofanMap P (Limits.Sigma.ι E) (coproductIsCoproduct E), fun f =>
    Pretriangulated.mem_of_isColimit
      (isColimitOfPreserves (preadditiveCoyoneda.obj (op P)) (coproductIsCoproduct E))
      (cofanMap P (Limits.Sigma.ι E)).range
      (fun ⟨i⟩ x => ⟨DirectSum.of _ i x, cofanMap_of P (Limits.Sigma.ι E) i x⟩) f⟩

end CategoryTheory

end
