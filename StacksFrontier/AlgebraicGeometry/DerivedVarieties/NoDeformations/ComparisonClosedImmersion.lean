module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.NoDeformations.ConstantFamily
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import StacksCore.Tactic.StacksAttribute

/-!
# The comparison morphism `Y_s ×_k Y_s ⟶ X ×_S Y` is a closed immersion

Let `k` be a field, let `q : S ⟶ Spec k` be a morphism with a section `s : Spec k ⟶ S` (a
`k`-rational point), and let `g : Y ⟶ S` be arbitrary. Write `Y_s = Y ×_S Spec k` for the fibre
and `X = Y_s ×_k S` for the constant family with that fibre, as in
`StacksFrontier/AlgebraicGeometry/DerivedVarieties/NoDeformations/ConstantFamily.lean`.

[Stacks, Tag 0G0R] opens by calling the comparison morphism

`i : Y_s ×_k Y_s = X_s ×_S Y_s ⟶ X ×_S Y`

a closed immersion, on the grounds that it is the inclusion of the fibre of `X ×_S Y ⟶ S` over
`s`. `AlgebraicGeometry.fibreSquareToProductComparison` builds that morphism, but as a bare
morphism; this file supplies the two facts the source uses about it.

## Main results

* `AlgebraicGeometry.isClosedImmersion_of_comp_eq_id'` — a `k`-rational point
  `s : Spec k ⟶ S`, being a section of `q : S ⟶ Spec k`, is a closed immersion.
* `AlgebraicGeometry.isPullback_fibreSquareToProductComparison` — **the pullback pasting**: the
  square with `i` along the top and `s` along the bottom,

  ```
  Y_s ×_k Y_s  --- i --->  X ×_S Y
       |                      |
       v                      v
     Spec k   --- s --->      S
  ```

  is a pullback square. Equivalently, `i` exhibits `Y_s ×_k Y_s` as the fibre of
  `X ×_S Y ⟶ S` over `s`, which is exactly what [Stacks, Tag 0G0R] asserts when it writes
  `Y_s × Y_s = (X ×_S Y)_s`.
* `AlgebraicGeometry.isClosedImmersion_fibreSquareToProductComparison` — hence `i` is a closed
  immersion.

## Implementation notes

*Why a pasting and not `Scheme.Hom.fiberι`.* Mathlib's `AlgebraicGeometry.Scheme.Hom.fiber` is
the pullback along `S.fromSpecResidueField` at a *topological* point of `S`, not along a given
`k`-rational point `s : Spec k ⟶ S`. The two agree for a `k`-rational point, but nothing in this
library identifies them, and the identification is not needed: `IsPullback` says what is wanted
directly, and `MorphismProperty.IsStableUnderBaseChange.of_isPullback` consumes it.

*How the pasting is assembled.* Three squares are pasted, each of them a defining pullback
square of one of the four pullbacks in play:

* `Y_s ×_k Y_s` is the pullback of `π : Y_s ⟶ Spec k` against itself;
* `X = Y_s ×_k S` is the pullback of `π` against `q`;
* `X ×_S Y` is the pullback of `X ⟶ S` against `g`;
* `Y_s` is the pullback of `g` against `s`.

Two applications of `CategoryTheory.IsPullback.of_right` cut the first square down — first past
`X ×_S Y ⟶ X ⟶ Y_s`, then past `X ×_S Y ⟶ X`— to the square with `i` on top and the fibre
inclusion `Y_s ⟶ Y` on the bottom, and one `CategoryTheory.IsPullback.paste_vert` with the fibre
square of `g` at `s` turns that into the statement over `s`. The section hypothesis
`s ≫ q = 𝟙` enters exactly once, in `fibreAtRationalPoint_comp_eq`, where it collapses
`Y_s ⟶ Y ⟶ S ⟶ Spec k` to `π`.

*No hypothesis beyond the source's.* `g` is arbitrary here: neither smoothness nor properness is
used, so neither is assumed. `q` carries no finite-type hypothesis either.

## References

* [Stacks Project, Tag 0G0R](https://stacks.math.columbia.edu/tag/0G0R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

section ConstantFamily

variable {k : Type u} [Field k] {S Y : Scheme.{u}}
  (q : S ⟶ Spec (.of k)) (g : Y ⟶ S) (s : Spec (.of k) ⟶ S)

/-- **The projection `p : X ×_S Y ⟶ S`** of [Stacks, Tag 0G0R], where `X = Y_s ×_k S` is the
constant family with fibre `Y_s`: the second projection followed by `g`. -/
abbrev constantFamilyProductToBase : Limits.pullback (constantFamilyπ q g s) g ⟶ S :=
  Limits.pullback.snd (constantFamilyπ q g s) g ≫ g

/-- **A `k`-rational point is a closed immersion.** A section `s : Spec k ⟶ S` of a morphism
`q : S ⟶ Spec k` is a closed immersion, because `Spec k` is a one-point scheme for `k` a field
and a section onto a subsingleton target is a closed immersion. -/
theorem isClosedImmersion_of_isSection (hs : s ≫ q = 𝟙 _) : IsClosedImmersion s :=
  isClosedImmersion_of_comp_eq_id q s hs

/-- The composite `Y_s ⟶ Y ⟶ S ⟶ Spec k` is the structure morphism `π : Y_s ⟶ Spec k` of the
fibre, because `s` is a section of `q`. -/
theorem fibreAtRationalPoint_comp_eq (hs : s ≫ q = 𝟙 _) :
    (fibreAtRationalPointι g s ≫ g) ≫ q = fibreAtRationalPointπ g s := by
  rw [Limits.pullback.condition, Category.assoc, hs, Category.comp_id]

/-- The comparison morphism composed into `X` and then onto the first factor `Y_s` of
`X = Y_s ×_k S` is the first projection of `Y_s ×_k Y_s`. -/
theorem fibreSquareToProductComparison_comp_fst_fst (hs : s ≫ q = 𝟙 _) :
    (fibreSquareToProductComparison q g s hs ≫
        Limits.pullback.fst (constantFamilyπ q g s) g) ≫
      Limits.pullback.fst (fibreAtRationalPointπ g s) q =
      Limits.pullback.fst (fibreAtRationalPointπ g s) (fibreAtRationalPointπ g s) := by
  rw [fibreSquareToProductComparison, Limits.pullback.lift_fst, Limits.pullback.lift_fst]

/-- The comparison morphism composed into `Y` is the second projection of `Y_s ×_k Y_s`
followed by the fibre inclusion `Y_s ⟶ Y`. -/
theorem fibreSquareToProductComparison_comp_snd (hs : s ≫ q = 𝟙 _) :
    fibreSquareToProductComparison q g s hs ≫
        Limits.pullback.snd (constantFamilyπ q g s) g =
      Limits.pullback.snd (fibreAtRationalPointπ g s) (fibreAtRationalPointπ g s) ≫
        fibreAtRationalPointι g s := by
  rw [fibreSquareToProductComparison, Limits.pullback.lift_snd]

/-- **`Y_s ×_k Y_s` is the pullback of `X ×_S Y ⟶ Y` along the fibre inclusion `Y_s ⟶ Y`.**
This is the middle stage of the pasting; it is the square with the comparison morphism `i` on
top and the fibre inclusion `Y_s ⟶ Y` on the bottom. -/
theorem isPullback_fibreSquareToProductComparison_fibreι (hs : s ≫ q = 𝟙 _) :
    IsPullback (fibreSquareToProductComparison q g s hs)
      (Limits.pullback.snd (fibreAtRationalPointπ g s) (fibreAtRationalPointπ g s))
      (Limits.pullback.snd (constantFamilyπ q g s) g)
      (fibreAtRationalPointι g s) := by
  -- Cut the square `Y_s ×_k Y_s ⟶ X` over `Y_s ⟶ S` down past `X ×_S Y ⟶ X`.
  refine IsPullback.of_right ?_ (fibreSquareToProductComparison_comp_snd q g s hs)
    (IsPullback.of_hasPullback (constantFamilyπ q g s) g)
  -- Cut the defining square of `Y_s ×_k Y_s` down past `X ⟶ Y_s`.
  refine IsPullback.of_right ?_ ?_ (IsPullback.of_hasPullback (fibreAtRationalPointπ g s) q)
  · rw [fibreSquareToProductComparison_comp_fst_fst q g s hs,
      fibreAtRationalPoint_comp_eq q g s hs]
    exact IsPullback.of_hasPullback (fibreAtRationalPointπ g s) (fibreAtRationalPointπ g s)
  · rw [Category.assoc, Limits.pullback.condition, ← Category.assoc,
      fibreSquareToProductComparison_comp_snd q g s hs, Category.assoc]

/-- **The comparison morphism exhibits `Y_s ×_k Y_s` as the fibre of `X ×_S Y ⟶ S` over `s`.**

This is the identification `Y_s × Y_s = (X ×_S Y)_s` with which [Stacks, Tag 0G0R] begins, in
the form of a pullback square: the square with the comparison morphism
`i : Y_s ×_k Y_s ⟶ X ×_S Y` along the top and the `k`-rational point `s : Spec k ⟶ S` along the
bottom is a pullback square. -/
theorem isPullback_fibreSquareToProductComparison (hs : s ≫ q = 𝟙 _) :
    IsPullback (fibreSquareToProductComparison q g s hs)
      (Limits.pullback.snd (fibreAtRationalPointπ g s) (fibreAtRationalPointπ g s) ≫
        fibreAtRationalPointπ g s)
      (Limits.pullback.snd (constantFamilyπ q g s) g ≫ g) s :=
  (isPullback_fibreSquareToProductComparison_fibreι q g s hs).paste_vert
    (IsPullback.of_hasPullback g s)

/-- **The comparison morphism `i : Y_s ×_k Y_s ⟶ X ×_S Y` is a closed immersion**, as
[Stacks, Tag 0G0R] says it is: it is the base change of the `k`-rational point
`s : Spec k ⟶ S`, which is a closed immersion, along `X ×_S Y ⟶ S`. -/
theorem isClosedImmersion_fibreSquareToProductComparison (hs : s ≫ q = 𝟙 _) :
    IsClosedImmersion (fibreSquareToProductComparison q g s hs) :=
  IsClosedImmersion.isStableUnderBaseChange.of_isPullback
    (isPullback_fibreSquareToProductComparison q g s hs).flip
    (isClosedImmersion_of_isSection q s hs)

end ConstantFamily

end AlgebraicGeometry

end
