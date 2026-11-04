module

public import Mathlib.CategoryTheory.Presentable.Directed
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.LimitPreserving

/-!
# Limit preservation tested on directed inverse systems

`AlgebraicGeometry.LimitPreserving` (Stacks 049J, part (1)) asks a presheaf to turn every
cofiltered inverse system of affine schemes, indexed by an arbitrary small cofiltered category,
into a filtered colimit of sets. Stacks states it for *directed* inverse systems, and the two
agree: by Deligne's theorem (Stacks 0032, `CategoryTheory.IsFiltered.exists_directed`) a small
cofiltered category receives an initial functor from the opposite of a directed partially ordered
set, and restricting both the limit cone and the colimit cocone along it changes neither being a
limit nor being a colimit.

The descent results for algebraic spaces of this library are stated for directed index sets, so
this is what lets limit preservation, in the form that local finite presentation is read off
from (Stacks 04AK), be proved from them.

## Main results

* `AlgebraicGeometry.limitPreserving_of_directed`: a presheaf which turns every directed inverse
  system of affine schemes into a colimit is limit preserving.
* `AlgebraicGeometry.relativelyLimitPreserving_of_directed`: the same for relative limit
  preservation (Stacks 049J, part (2)).

## References

* [Stacks Project, Tag 049J](https://stacks.math.columbia.edu/tag/049J)
* [Stacks Project, Tag 0032](https://stacks.math.columbia.edu/tag/0032)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w z z'

namespace AlgebraicGeometry

/-- **Limit preservation is tested on directed inverse systems.** A presheaf which turns every
inverse system of affine schemes indexed by the opposite of a directed partially ordered set, with
affine limit, into a colimit of sets is limit preserving in the sense of Stacks 049J, part (1),
for all small cofiltered index categories. -/
theorem limitPreserving_of_directed {C : Type z} [Category.{z'} C] (toScheme : C ⥤ Scheme.{u})
    (F : Cᵒᵖ ⥤ Type v)
    (h : ∀ (Λ : Type w) [PartialOrder Λ] [IsDirected Λ (· ≤ ·)] [Nonempty Λ] (D : Λᵒᵖ ⥤ C)
      (c : Cone D), IsLimit (toScheme.mapCone c) → (∀ i, IsAffine (toScheme.obj (D.obj i))) →
        IsAffine (toScheme.obj c.pt) → Nonempty (IsColimit (F.mapCocone c.op))) :
    LimitPreserving.{u, v, w, w} toScheme F := by
  intro I _ _ D c hc hD hpt
  obtain ⟨α, _, _, _, G, _⟩ := IsFiltered.exists_directed Iᵒᵖ
  have hc' : IsLimit (toScheme.mapCone (c.whisker G.leftOp)) :=
    (Functor.Initial.isLimitWhiskerEquiv G.leftOp (toScheme.mapCone c)).symm hc
  obtain ⟨hcol⟩ := h α (G.leftOp ⋙ D) (c.whisker G.leftOp) hc' (fun i => hD _) hpt
  exact ⟨(Functor.Final.isColimitWhiskerEquiv G.leftOp.op (F.mapCocone c.op)) hcol⟩

/-- **Relative limit preservation is tested on directed inverse systems.** A transformation of
presheaves on the big fppf site of `S` is relatively limit preserving (Stacks 049J, part (2)) as
soon as, over every section of its target, the presheaf of lifts turns every directed inverse
system of affine schemes with affine limit into a colimit of sets. -/
theorem relativelyLimitPreserving_of_directed (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type v} (a : F ⟶ G)
    (h : ∀ (X : BigFppfOver B S hS) (y : G.obj (Opposite.op X)) (Λ : Type w) [PartialOrder Λ]
      [IsDirected Λ (· ≤ ·)] [Nonempty Λ] (D : Λᵒᵖ ⥤ Over X) (c : Cone D),
      IsLimit ((Over.forget X ⋙ BigFppfOver.toScheme B S hS).mapCone c) →
      (∀ i, IsAffine ((Over.forget X ⋙ BigFppfOver.toScheme B S hS).obj (D.obj i))) →
      IsAffine ((Over.forget X ⋙ BigFppfOver.toScheme B S hS).obj c.pt) →
      Nonempty (IsColimit ((sectionFiber B S hS a X y).mapCocone c.op))) :
    RelativelyLimitPreserving.{u, v, w, w} B S hS a :=
  fun X y => limitPreserving_of_directed _ _ (h X y)

end AlgebraicGeometry

end
