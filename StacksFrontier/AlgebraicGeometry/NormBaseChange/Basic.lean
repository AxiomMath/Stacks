module

public import StacksFrontier.AlgebraicGeometry.Divisors.Norm.Basic
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.BaseChange

/-!
# Base change of the norm of a finite locally free morphism

Stacks Tag 0BD2 asserts that the canonical determinant norm of a finite locally free morphism
`f : X ⟶ Y` is compatible with an arbitrary base change: for a cartesian square
```
X' --g'--> X
|f'        |f
Y' --g-->  Y
```
the morphism `f'` is again finite locally free, and the norm of a section pulled back to `X'` is
the pullback of its norm.

The norm identity itself is `Stacks.Divisors.finiteLocallyFreeNorm_app_baseChange`, which carries
finite local freeness of `f'` as a hypothesis. This file supplies that hypothesis — finite local
freeness is stable under arbitrary base change — and so states the base-change clause of Tag
0BD2 in the form that asserts it.

## Main results

* `Stacks.Divisors.finiteLocallyFreeNorm_baseChange`: the base-change clause of Tag 0BD2.

## Implementation notes

Stability of finite local freeness under base change is
`Stacks.Morphisms.isFiniteLocallyFree_isStableUnderBaseChange` (Tag 02KD), imported from
`StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.BaseChange` and applied to the given
cartesian square. No comparison of direct images around the square is needed, so neither the
base-change morphism `g^* f_* ⟶ f'_* g'^*` of Tag 02KG nor its invertibility enters.

The positive constant-rank clause of Tag 0BD2 is *not* here: stability of the rank would need the
identification of `Stacks.Morphisms.IsFiniteLocallyFreeOfRank f d` with constancy of Mathlib's
`AlgebraicGeometry.Scheme.Hom.finrank`, which is exactly the relation left as a `TODO` in
`Mathlib/AlgebraicGeometry/Morphisms/FlatRank.lean`. The norm identity at constant rank is
available as `Stacks.Divisors.finiteLocallyFreeNormOfRank_app_baseChange`, with the rank of the
base change as a hypothesis.

## References

* [Stacks Project, Tag 0BD2](https://stacks.math.columbia.edu/tag/0BD2)
* [Stacks Project, Tag 02KB](https://stacks.math.columbia.edu/tag/02KB)
* [Stacks Project, Tag 02KD](https://stacks.math.columbia.edu/tag/02KD)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Divisors

/-- **Stacks Project, Tag 0BD2.** Formation of the canonical determinant norm commutes with
arbitrary base change, even when the rank is not constant: around a cartesian square the base
change `f'` of a finite locally free morphism `f` is again finite locally free, and the norm of a
section of the structure sheaf pulled back around the square is the pullback of its norm. -/
@[stacks 0BD2 "compatibility with arbitrary base change"]
theorem finiteLocallyFreeNorm_baseChange
    {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y')
    (g' : X' ⟶ X) (g : Y' ⟶ Y)
    [Morphisms.IsFiniteLocallyFree f]
    (sq : IsPullback g' f' f g) :
    ∃ h' : Morphisms.IsFiniteLocallyFree f',
      letI := h'
      ∀ (U : Y.Opens) (s : Γ(X, f ⁻¹ᵁ U)),
        (finiteLocallyFreeNorm f').app (g ⁻¹ᵁ U)
            (g'.appLE (f ⁻¹ᵁ U) (f' ⁻¹ᵁ (g ⁻¹ᵁ U)) (by
              intro x hx
              change f (g' x) ∈ U
              rw [← Scheme.Hom.comp_apply, sq.w, Scheme.Hom.comp_apply]
              exact hx) s) =
          g.app U ((finiteLocallyFreeNorm f).app U s) :=
  have : Morphisms.IsFiniteLocallyFree f' :=
    Morphisms.isFiniteLocallyFree_isStableUnderBaseChange.of_isPullback sq
      ‹Morphisms.IsFiniteLocallyFree f›
  ⟨this, finiteLocallyFreeNorm_app_baseChange f f' g' g sq⟩

end Stacks.Divisors

end
