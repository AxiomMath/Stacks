module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# A chart of a fibre product, from a chart of one of its factors

If `W` is the fibre product of `k ≫ t` and `s`, and `H` is the fibre product of `t` and `s`, then
`W` is the fibre product of `k` and the first projection of `H`. This is the pasting law for
pullback squares read right to left: the outer square and the right-hand square are cartesian,
hence so is the left-hand one.

## Main results

* `CategoryTheory.Limits.isPullback_chart_into_pullback`: the left-hand square is cartesian.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Limits

/-- A chart of a fibre product, from a chart of one of its factors.

If `W` is the fibre product of `k ≫ t` and `s`, and `H` is the fibre product of `t` and `s`,
then `W` is the fibre product of `k` and the first projection of `H`. This is the pasting law
read right to left. -/
theorem isPullback_chart_into_pullback {C : Type*} [Category* C]
    {W X T U F H : C} {pX : W ⟶ X} {pU : W ⟶ U} {k : X ⟶ T} {t : T ⟶ F} {s : U ⟶ F}
    {qT : H ⟶ T} {qU : H ⟶ U} (hW : IsPullback pX pU (k ≫ t) s) (hH : IsPullback qT qU t s) :
    IsPullback pX
      (hH.flip.lift pU (pX ≫ k) (by simpa only [Category.assoc] using hW.w.symm)) k qT :=
  (IsPullback.of_right' hW.flip hH.flip).flip

end CategoryTheory.Limits
