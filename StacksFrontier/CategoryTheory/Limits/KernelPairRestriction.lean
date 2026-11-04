module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Square
public import Mathlib.CategoryTheory.Yoneda

/-!
# Restricting a kernel pair along a base change of its chart

Let `F` be a presheaf on a category `C`, let `q : h_U ⟶ F` be a morphism from a representable
presheaf and let `t, s : R ⟶ U` be a kernel pair of `q`, that is `h_R` is the fibre product
of `h_U` with itself over `F`. Let `f : h_V ⟶ F` be another morphism from a representable
presheaf whose fibre product with `q` is again representable, by `W` with projections
`i : W ⟶ U` and `g : W ⟶ V`.

Then the restricted relation `R ×_U W ⟶ W` is a kernel pair of `g`. The two projections are
`pullback.snd t i` and the morphism produced here, which covers `pullback.fst t i ≫ s`.

This is the step that turns the relation of a presentation of an algebraic space into a
relation on an open part of its chart.

## Main results

* `CategoryTheory.Limits.exists_isKernelPair_restrict_of_isKernelPair`: the restricted
  relation is a kernel pair of `g`.

## Implementation notes

The morphism `j : R ×_U W ⟶ W` is produced by the universal property of `W`, in the presheaf
category, out of `pullback.fst t i ≫ s` and `pullback.snd t i ≫ g`; it descends to `C`
because the Yoneda embedding is fully faithful.

That `j` and `pullback.snd t i` form a kernel pair of `g` is read off by pasting: the
rectangle built from the chosen pullback square of `t` against `i` and from the kernel-pair
square of `q` is a pullback, and `W` is a pullback over `F`, so the remaining square is one
too by `CategoryTheory.IsPullback.of_right`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory.Limits

/-- **The restriction of a kernel pair along a base change of its chart is a kernel pair.**
If `t, s : R ⟶ U` is a kernel pair of `q : h_U ⟶ F` and `W` with `i : W ⟶ U`, `g : W ⟶ V` is
the fibre product of `q` with `f : h_V ⟶ F`, then there is `j : R ×_U W ⟶ W` covering
`pullback.fst t i ≫ s` such that `j` and `pullback.snd t i` form a kernel pair of `g`. -/
theorem exists_isKernelPair_restrict_of_isKernelPair {C : Type u} [Category.{v} C]
    [HasPullbacks C] {R U W V : C} {F : Cᵒᵖ ⥤ Type v}
    (t s : R ⟶ U) (q : yoneda.obj U ⟶ F)
    (hR : IsPullback (yoneda.map s) (yoneda.map t) q q)
    (i : W ⟶ U) (g : W ⟶ V) (f : yoneda.obj V ⟶ F)
    (hW : IsPullback (yoneda.map i) (yoneda.map g) q f) :
    ∃ j : pullback t i ⟶ W,
      j ≫ i = pullback.fst t i ≫ s ∧ IsPullback j (pullback.snd t i) g g := by
  have hpaste := ((IsPullback.of_hasPullback t i).map yoneda).paste_horiz hR
  have hcomm : yoneda.map (pullback.fst t i ≫ s) ≫ q =
      yoneda.map (pullback.snd t i ≫ g) ≫ f := by
    simp only [Functor.map_comp, Category.assoc]
    rw [← hW.w]
    exact hpaste.w
  obtain ⟨j, hj⟩ := yoneda.map_surjective (hW.lift (yoneda.map (pullback.fst t i ≫ s))
    (yoneda.map (pullback.snd t i ≫ g)) hcomm)
  have hjg : j ≫ g = pullback.snd t i ≫ g := yoneda.map_injective <| by
    rw [Functor.map_comp, hj]; exact hW.lift_snd _ _ hcomm
  have hji : j ≫ i = pullback.fst t i ≫ s := yoneda.map_injective <| by
    rw [Functor.map_comp, hj]; exact hW.lift_fst _ _ hcomm
  refine ⟨j, hji, ?_⟩
  · refine IsPullback.of_map yoneda hjg ?_
    refine IsPullback.of_right (h₂₂ := f) (h₁₂ := yoneda.map i) ?_ ?_ hW
    · simpa only [← Functor.map_comp, hji, hW.w] using hpaste
    · simpa only [← Functor.map_comp] using congrArg yoneda.map hjg

end CategoryTheory.Limits

end
