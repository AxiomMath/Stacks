module

public import Mathlib.CategoryTheory.Adjunction.Comma
public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import Mathlib.CategoryTheory.Sites.Over

/-!
# Pointwise right Kan extensions along a localization functor of a category with pullbacks

Let `C` be a category with pullbacks and let `f : X ⟶ Y` be a morphism of `C`. Restriction of
presheaves along `CategoryTheory.Over.map f` has pointwise right Kan extensions, with values in an
*arbitrary* category and with no size hypothesis: `Over.map f ⊣ Over.pullback f`, so `Over.map f`
is a left adjoint, so each structured arrow category over `(Over.map f).op` has an initial object,
and a functor out of a category with an initial object has a limit given by its value there.

## Main results

* `Stacks.Localization.hasPointwiseRightKanExtension_overMapOp` — restriction of presheaves along
  `Over.map f` has pointwise right Kan extensions when `C` has pullbacks.

## References

* [Stacks Project, Tag 03CE](https://stacks.math.columbia.edu/tag/03CE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w' w v u

namespace Stacks.Localization

variable {C : Type u} [Category.{v} C]

/-- **Restriction of presheaves along `Over.map f` has pointwise right Kan extensions**, for an
arbitrary target category and with no size hypothesis, as soon as `C` has pullbacks. -/
public lemma hasPointwiseRightKanExtension_overMapOp [HasPullbacks C] {X Y : C} (f : X ⟶ Y)
    (A : Type w) [Category.{w'} A] (F : (Over X)ᵒᵖ ⥤ A) :
    (Over.map f).op.HasPointwiseRightKanExtension F := by
  have hadj : (Over.map f).op.IsRightAdjoint := ⟨_, ⟨(Over.mapPullbackAdj f).op⟩⟩
  intro Z
  have : HasInitial (StructuredArrow Z (Over.map f).op) :=
    isRightAdjoint_iff_hasInitial_structuredArrow.mp hadj Z
  exact Limits.hasLimit_of_domain_hasInitial

end Stacks.Localization

end
