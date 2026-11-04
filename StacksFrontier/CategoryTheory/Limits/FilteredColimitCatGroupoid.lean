module

public import StacksFrontier.CategoryTheory.FiberedCategory.SplitFiberEvaluation
public import StacksFrontier.CategoryTheory.Limits.FilteredColimitCatStages

/-!
# A filtered colimit of groupoids is a groupoid

The criterion of Stacks 0CMW (`CategoryTheory.Limits.CategoricalPullback.squareComparison` is
fully faithful iff the comparison of the square of relative diagonals is an equivalence) needs
two of the four corners of the square to be groupoids. For the canonical square of Stacks 0CMR
those corners are the fibre of a category fibred in groupoids over the cone point and the colimit
of the fibres at the stages, so this file supplies the two facts that make them groupoids: a
groupoid structure transports along a fully faithful functor, and a *filtered* colimit in `Cat`
of groupoids is a groupoid.

The second is where filteredness is needed: a morphism of the colimit is only a morphism of some
stage *up to* the equivalence relation the colimit quotients by, and it is filteredness that
produces a single stage carrying a representative
(`CategoryTheory.Cat.exists_stage_hom_pair_of_colimit`). The inverse is then the image of the
inverse at that stage.

## Main results

* `CategoryTheory.isGroupoid_of_fullyFaithful`: a category with a fully faithful functor to a
  groupoid is a groupoid.
* `CategoryTheory.Functor.SplitFiber.instIsGroupoid`: the fibre over `V` of the split model of
  Stacks 004A is a groupoid as soon as the fibres of `p` are, its morphisms being by definition
  the morphisms of a fibre of `p`.
* `CategoryTheory.Cat.isGroupoid_colimit`: a filtered colimit in `Cat` of groupoids is a
  groupoid.

## References

* [Stacks Project, Tag 0CMW](https://stacks.math.columbia.edu/tag/0CMW)
* [Stacks Project, Tag 004A](https://stacks.math.columbia.edu/tag/004A)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

universe u v w u₁ u₂ v₁ v₂

/-- **A category admitting a fully faithful functor to a groupoid is a groupoid.** A morphism
whose image is invertible is invertible, a fully faithful functor reflecting isomorphisms. -/
lemma isGroupoid_of_fullyFaithful {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    (F : C ⥤ D) [F.Full] [F.Faithful] [IsGroupoid D] : IsGroupoid C where
  all_isIso {_ _} f := by
    have : IsIso (F.map f) := IsGroupoid.all_isIso _
    exact isIso_of_fully_faithful F f

/-- **A category equivalent to a groupoid is a groupoid.** -/
lemma isGroupoid_of_equivalence {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    (e : C ≌ D) [IsGroupoid C] : IsGroupoid D :=
  isGroupoid_of_fullyFaithful e.inverse

/-- A universe lift of a groupoid is a groupoid. -/
instance isGroupoid_asSmall {C : Type u₁} [Category.{v₁} C] [IsGroupoid C] :
    IsGroupoid (AsSmall.{w} C) :=
  isGroupoid_of_equivalence AsSmall.equiv

/-- A category bundled into `Cat` is a groupoid when it is one. Stated as an instance because
the comparison functors of a 2-commutative square of `Cat` present their corners in this bundled
form, which instance synthesis does not see through. -/
instance isGroupoid_catOf (C : Type u₁) [Category.{v₁} C] [IsGroupoid C] :
    IsGroupoid ↑(Cat.of C) :=
  inferInstanceAs (IsGroupoid C)

namespace Functor.SplitFiber

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳]

/-- **The fibre over `V` of the split model of Stacks 004A is a groupoid** when the fibres of `p`
are: a morphism of `CategoryTheory.Functor.SplitFiber p V` *is* a morphism of the fibre `𝒳_V`. -/
instance instIsGroupoid (p : 𝒳 ⥤ 𝒞) [p.IsFibered] (V : 𝒞) [IsGroupoid (p.Fiber V)] :
    IsGroupoid (p.SplitFiber V) :=
  isGroupoid_of_fullyFaithful (evaluation p V)

end Functor.SplitFiber

namespace Cat

section Colimit

variable {I : Type v} [Category.{w} I] [IsFiltered I]
  (F : I ⥤ Cat.{max u v w, max u v w}) [HasColimit F]
  [HasColimit (F ⋙ CategoryTheory.nerveFunctor.{max u v w, max u v w})]

/-- **A filtered colimit in `Cat` of groupoids is a groupoid.** A morphism of the colimit is
carried by a single stage, where it is invertible; the colimit inclusion carries the inverse to
an inverse. -/
lemma isGroupoid_colimit (h : ∀ i : I, IsGroupoid ↑(F.obj i)) :
    IsGroupoid ↑(colimit F) where
  all_isIso {x y} f := by
    obtain ⟨j, a, b, f', -, hx, hy, hf', -⟩ := exists_stage_hom_pair_of_colimit.{u, v, w} F f f
    have := h j
    have : IsIso f' := IsGroupoid.all_isIso f'
    have hcomp : IsIso (eqToHom hx ≫ f ≫ eqToHom hy.symm) := by
      rw [← hf']
      infer_instance
    have hf : f = eqToHom hx.symm ≫ (eqToHom hx ≫ f ≫ eqToHom hy.symm) ≫ eqToHom hy := by
      simp
    rw [hf]
    infer_instance

end Colimit

end Cat

end CategoryTheory

end
