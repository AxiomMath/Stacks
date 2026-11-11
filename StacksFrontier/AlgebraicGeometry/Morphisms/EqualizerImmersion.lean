module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# The equalizer of two morphisms of schemes over a base

Let `X` and `Y` be schemes over `S` and let `a b : X ⟶ Y` be morphisms over `S`. The equalizer
of `a` and `b` in the category `Over S`, whose underlying morphism of schemes is
`(CategoryTheory.Limits.equalizer.ι a b).left`, is a base change of the diagonal
`Y ⟶ Y ×[S] Y`. Since a diagonal is always an immersion, the equalizer is an immersion, that is,
a locally closed subscheme of `X`. It is the largest locally closed subscheme of `X` on which
`a` and `b` agree: by the universal property of the equalizer every morphism `j : W ⟶ X` with
`j ≫ a = j ≫ b` factors uniquely through it, and this applies in particular to every immersion.
If `Y` is separated over `S`, the diagonal is a closed immersion, and so is the equalizer.

## Main results

* `AlgebraicGeometry.isImmersion_equalizer_ι_left`: the equalizer is an immersion.
* `AlgebraicGeometry.equalizer_ι_left_comp_eq`: `a` and `b` agree on the equalizer.
* `AlgebraicGeometry.existsUnique_comp_equalizer_ι_left`: every morphism on which `a` and `b`
  agree factors uniquely through the equalizer.
* `AlgebraicGeometry.exists_largest_isImmersion_eq`: the statement of Stacks 01KM as a whole.

## Implementation notes

The clause for separated `Y` is Mathlib's instance
`AlgebraicGeometry.isClosedImmersion_equalizer_ι_left`, which Mathlib registers for 01KM; it
covers only that clause. The general clause, that the equalizer is an immersion, is proved here
in the same way, from Mathlib's instance that a diagonal is an immersion.

## References

* [Stacks Project, Tag 01KM](https://stacks.math.columbia.edu/tag/01KM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {S : Scheme.{u}} {X Y : Over S} (a b : X ⟶ Y)

/-- The equalizer of two morphisms `a b : X ⟶ Y` of schemes over `S` is an immersion into `X`:
it is a base change of the diagonal of `Y ⟶ S`, which is an immersion. -/
@[stacks 01KM "the equalizer of a and b is an immersion, i.e. a locally closed subscheme of X"]
theorem isImmersion_equalizer_ι_left : IsImmersion (equalizer.ι a b).left := by
  refine MorphismProperty.of_isPullback
    ((Limits.isPullback_equalizer_prod a b).map (Over.forget _)).flip ?_
  have e : (prod.lift (𝟙 Y) (𝟙 Y)).left ≫ (Over.prodLeftIsoPullback Y Y).hom =
      pullback.diagonal Y.hom := by
    ext1 <;> simp [← Over.comp_left]
  have : IsImmersion ((prod.lift (𝟙 Y) (𝟙 Y)).left ≫ (Over.prodLeftIsoPullback Y Y).hom) := by
    rw [e]
    infer_instance
  exact (IsImmersion.comp_iff _ (Over.prodLeftIsoPullback Y Y).hom).mp this

/-- The morphisms `a` and `b` agree on their equalizer. -/
theorem equalizer_ι_left_comp_eq :
    (equalizer.ι a b).left ≫ a.left = (equalizer.ι a b).left ≫ b.left := by
  rw [← Over.comp_left, equalizer.condition, Over.comp_left]

/-- Every morphism of schemes `j : W ⟶ X` on which `a` and `b` agree factors uniquely through
the equalizer of `a` and `b`. In particular the equalizer contains every locally closed
subscheme of `X` on which `a` and `b` agree. -/
@[stacks 01KM "maximality: every morphism on which a and b agree factors through the equalizer"]
theorem existsUnique_comp_equalizer_ι_left {W : Scheme.{u}} (j : W ⟶ X.left)
    (h : j ≫ a.left = j ≫ b.left) :
    ∃! l : W ⟶ (equalizer a b).left, l ≫ (equalizer.ι a b).left = j := by
  let j' : Over.mk (j ≫ X.hom) ⟶ X := Over.homMk j
  have h' : j' ≫ a = j' ≫ b := Over.OverMorphism.ext (by simpa [j'] using h)
  have := isImmersion_equalizer_ι_left a b
  refine ⟨(equalizer.lift j' h').left, ?_, fun l hl ↦ ?_⟩
  · dsimp only
    rw [← Over.comp_left, equalizer.lift_ι]
    rfl
  · rw [← cancel_mono (equalizer.ι a b).left, hl, ← Over.comp_left, equalizer.lift_ι]
    rfl

/-- **Stacks 01KM.** Let `a b : X ⟶ Y` be morphisms of schemes over `S`. There is a largest
locally closed subscheme `Z` of `X` on which `a` and `b` agree: an immersion `ι : Z ⟶ X` with
`ι ≫ a = ι ≫ b` through which every immersion `j : W ⟶ X` with `j ≫ a = j ≫ b` factors
uniquely. Moreover `Z` is a closed subscheme if `Y` is separated over `S`. The scheme `Z` is the
equalizer of `a` and `b`. -/
@[stacks 01KM "full statement: the largest locally closed Z with a = b on Z, closed if Y separated"]
theorem exists_largest_isImmersion_eq :
    ∃ (Z : Scheme.{u}) (ι : Z ⟶ X.left), IsImmersion ι ∧ ι ≫ a.left = ι ≫ b.left ∧
      (∀ (W : Scheme.{u}) (j : W ⟶ X.left), IsImmersion j → j ≫ a.left = j ≫ b.left →
        ∃! l : W ⟶ Z, l ≫ ι = j) ∧
      (IsSeparated Y.hom → IsClosedImmersion ι) :=
  ⟨(equalizer a b).left, (equalizer.ι a b).left, isImmersion_equalizer_ι_left a b,
    equalizer_ι_left_comp_eq a b,
    fun _ j _ h ↦ existsUnique_comp_equalizer_ι_left a b j h,
    fun _ ↦ isClosedImmersion_equalizer_ι_left a b⟩

end AlgebraicGeometry
