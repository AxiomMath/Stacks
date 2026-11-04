module

public import Mathlib.CategoryTheory.Yoneda
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Morphisms of representable presheaves

The Yoneda embedding is fully faithful, so a morphism `h_T ⟶ h_U` of representable presheaves is
the Yoneda image of a unique morphism `T ⟶ U`, and that morphism is the one the Yoneda bijection
`CategoryTheory.yonedaEquiv` reads off from it. This file records the two directions of that
statement in the rewriting form their uses need: the Yoneda image of `yonedaEquiv h` is `h`, and
`yonedaEquiv.symm u` is the Yoneda image of `u`.

Mathlib has one half of the round trip, `CategoryTheory.yonedaEquiv_yoneda_map`, which cancels
the bijection *after* the embedding; both lemmas below are that identity transported across the
injectivity of the bijection, which is what cancels it *before* the embedding instead. The
two forms are not interchangeable in a `rw`: a goal mentioning a morphism of presheaves that was
produced by `yonedaEquiv` — the universal property of a fibre product of representables, say, or
the structure morphism of a chart — has no `yoneda.map` in it to rewrite under.

## Main results

* `CategoryTheory.yoneda_map_yonedaEquiv`: a morphism of representable presheaves is the Yoneda
  image of the morphism it corresponds to under the Yoneda bijection.
* `CategoryTheory.yonedaEquiv_symm_eq_yoneda_map`: the inverse Yoneda bijection sends a morphism
  of the category to its Yoneda image.

## Implementation notes

The statements are at a general category `C : Type w` with `Category.{v} C`, with the two
universes unrelated, so that they serve both a small site and a big one — in particular the big
fppf site over a scheme, where `w = v + 1`.

`CategoryTheory.yoneda_map_yonedaEquiv` is stated a second time in this library, as
`Stacks.Sites.GlobalSectionsAsEqualizer.yoneda_map_yonedaEquiv` of
`StacksFrontier/CategoryTheory/Sites/GlobalSections/AsEqualizerInstance.lean`. The two are the same
statement under different names. That copy is
stated for a `CategoryTheory.SmallCategory` — one universe, not two — so it does not apply at the
universe levels of the uses here.
-/

@[expose] public section

universe v w

namespace CategoryTheory

variable {C : Type w} [Category.{v} C]

/-- A morphism of representable presheaves is the Yoneda image of the morphism it corresponds to
under the Yoneda bijection. -/
@[ega "0 8.1.4" "partial", ega "0 8.1.6", sga "4 I 1.4"]
theorem yoneda_map_yonedaEquiv {T U : C} (h : yoneda.obj T ⟶ yoneda.obj U) :
    yoneda.map (yonedaEquiv h) = h :=
  yonedaEquiv.injective (yonedaEquiv_yoneda_map _)

/-- The Yoneda bijection sends a morphism of the category to the Yoneda image of it. -/
@[ega "0 8.1.6", sga "4 I 1.4"]
theorem yonedaEquiv_symm_eq_yoneda_map {T U : C} (u : T ⟶ U) :
    (yonedaEquiv.symm u : yoneda.obj T ⟶ yoneda.obj U) = yoneda.map u :=
  yonedaEquiv.injective (by rw [Equiv.apply_symm_apply, yonedaEquiv_yoneda_map])

end CategoryTheory
