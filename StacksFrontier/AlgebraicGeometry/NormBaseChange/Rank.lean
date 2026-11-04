module

public import StacksFrontier.AlgebraicGeometry.Divisors.Norm.Basic
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.BaseChange

/-!
# Base change of the norm of a finite locally free morphism of positive constant rank

Stacks Tag 0BD2 asserts that the canonical determinant norm of a finite locally free morphism
`f : X ⟶ Y` of positive constant rank `d` is compatible with an arbitrary base change: for a
cartesian square
```
X' --g'--> X
|f'        |f
Y' --g-->  Y
```
the morphism `f'` is again finite locally free of the *same* rank `d`, and the norm of a section
pulled back to `X'` is the pullback of its norm.

The norm identity itself is `Stacks.Divisors.finiteLocallyFreeNormOfRank_app_baseChange`, which
carries finite local freeness of rank `d` of `f'` as a hypothesis. This file supplies that
hypothesis — `Stacks.Morphisms.IsFiniteLocallyFreeOfRank.of_isPullback` — and so states the
positive constant-rank base-change clause of Tag 0BD2 in the form that asserts it.

## Main results

* `Stacks.Divisors.finiteLocallyFreeNormOfRank_baseChange`: the positive constant-rank
  base-change clause of Tag 0BD2.

## Implementation notes

What this clause adds over `Stacks.Divisors.finiteLocallyFreeNorm_baseChange` is that the base
change preserves the *rank*, not merely finite local freeness. That is
`Stacks.Morphisms.IsFiniteLocallyFreeOfRank.of_isPullback`, proved from the Fitting-ideal
characterisation of finite local freeness of a given rank; neither the base-change morphism of
direct images of Tag 02KG nor its invertibility is needed.

## References

* [Stacks Project, Tag 0BD2](https://stacks.math.columbia.edu/tag/0BD2)
* [Stacks Project, Tag 02KA](https://stacks.math.columbia.edu/tag/02KA)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Divisors

/-- **Stacks Project, Tag 0BD2.** At positive constant rank, arbitrary base change preserves the
specified degree and the norm on sections: around a cartesian square the base change `f'` of a
morphism `f` that is finite locally free of rank `d` is again finite locally free of rank `d`,
and the degree-`d` norm of a section of the structure sheaf pulled back around the square is the
pullback of its degree-`d` norm. -/
@[stacks 0BD2 "compatibility of the degree-d norm with arbitrary base change"]
theorem finiteLocallyFreeNormOfRank_baseChange
    {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y')
    (g' : X' ⟶ X) (g : Y' ⟶ Y) (d : ℕ)
    [Morphisms.IsFiniteLocallyFreeOfRank f d] (hd : 0 < d)
    (sq : IsPullback g' f' f g) :
    ∃ h' : Morphisms.IsFiniteLocallyFreeOfRank f' d,
      letI := h'
      ∀ (U : Y.Opens) (s : Γ(X, f ⁻¹ᵁ U)),
        (finiteLocallyFreeNormOfRank f' d hd).1.app (g ⁻¹ᵁ U)
            (g'.appLE (f ⁻¹ᵁ U) (f' ⁻¹ᵁ (g ⁻¹ᵁ U)) (by
              intro x hx
              change f (g' x) ∈ U
              rw [← Scheme.Hom.comp_apply, sq.w, Scheme.Hom.comp_apply]
              exact hx) s) =
          g.app U ((finiteLocallyFreeNormOfRank f d hd).1.app U s) := by
  let h' : Morphisms.IsFiniteLocallyFreeOfRank f' d :=
    Morphisms.IsFiniteLocallyFreeOfRank.of_isPullback sq
  exact ⟨h', fun U s ↦ finiteLocallyFreeNormOfRank_app_baseChange f f' g' g d hd sq U s⟩

end Stacks.Divisors

end
