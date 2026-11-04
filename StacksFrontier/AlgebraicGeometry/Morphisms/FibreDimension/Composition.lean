module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FibreDimensionBaseChange.Composite
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Equidimensional

/-!
# Relative dimension of a composition

Let `f : X ⟶ Y` and `g : Y ⟶ S` be morphisms of schemes locally of finite type. Relative
dimension in the sense of Tag 02NJ is subadditive along `f ≫ g`: a bound `≤ d` for `f` and a
bound `≤ e` for `g` give the bound `≤ d + e` for the composition. If moreover `f` is flat and
the two relative dimensions are exactly `d` and `e`, the relative dimension of `f ≫ g` is
exactly `d + e`.

## Main results

* `AlgebraicGeometry.RelativeDimensionLE.comp`: relative dimension at most `d` composed with
  relative dimension at most `e` has relative dimension at most `d + e`.
* `AlgebraicGeometry.RelativeDimension.comp_of_flat`: for a flat first factor the exact relative
  dimensions add.

## Implementation notes

Composition is written in categorical order, so `f ≫ g` is the morphism denoted `g ∘ f` in the
source. Both statements reduce to the local dimension inequality for the fibres of a composition
(Tag 02JS) and its equality under flatness; for the exact relative dimension the passage between
constancy of the local dimension of a fibre and equidimensionality of that fibre is Tag 0A21.

## References

* [Stacks Project, Tag 02NL](https://stacks.math.columbia.edu/tag/02NL)
* [Stacks Project, Tag 02NJ](https://stacks.math.columbia.edu/tag/02NJ)
* [Stacks Project, Tag 02JS](https://stacks.math.columbia.edu/tag/02JS)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X Y S : Scheme.{u}}

/-- A morphism locally of finite type whose fibres all have local dimension `d` at each of their
points has relative dimension `d`: such a fibre is equidimensional of dimension `d`. -/
private theorem relativeDimension_of_topologicalKrullDimAt_fiber_eq (f : X ⟶ S)
    [LocallyOfFiniteType f] {d : ℕ}
    (h : ∀ (s : S) (w : f.fiber s), topologicalKrullDimAt (f.fiber s) w = (d : WithBot ℕ∞)) :
    RelativeDimension f d := by
  intro s hs
  refine ⟨equidimensional_of_topologicalKrullDimAt_eq (S.residueField s) (f.fiber s)
    (f.fiberToSpecResidueField s) (h s), ?_⟩
  rw [topologicalKrullDim_eq_iSup_localKrullDim]
  have hloc : ∀ w : f.fiber s, localKrullDim (f.fiber s) w = (d : WithBot ℕ∞) := fun w ↦ by
    rw [← topologicalKrullDimAt_eq_localKrullDim]; exact h s w
  simp_rw [hloc]
  have : Nonempty (f.fiber s) := hs
  exact iSup_const

/-- **Stacks Project, Tag 02NL.** If `f` has relative dimension at most `d` and `g` has relative
dimension at most `e`, then `f ≫ g` has relative dimension at most `d + e`. -/
@[stacks 02NL "the inequality"]
public theorem RelativeDimensionLE.comp (f : X ⟶ Y) (g : Y ⟶ S) [LocallyOfFiniteType f]
    [LocallyOfFiniteType g] {d e : ℕ} (hf : RelativeDimensionLE f d)
    (hg : RelativeDimensionLE g e) : RelativeDimensionLE (f ≫ g) (d + e) := by
  intro x
  change topologicalKrullDimAt ((f ≫ g).fiber ((f ≫ g) x)) ((f ≫ g).asFiber x) ≤
    ((d + e : ℕ) : WithBot ℕ∞)
  rw [Nat.cast_add]
  exact (topologicalKrullDimAt_fiber_comp_le_add f g x).trans
    (add_le_add (hf.at x) (hg.at (f x)))

/-- **Stacks Project, Tag 02NL.** If `f` has relative dimension `d`, `g` has relative dimension
`e` and `f` is flat, then `f ≫ g` has relative dimension `d + e`. -/
@[stacks 02NL "the exact relative dimension of a flat composition"]
public theorem RelativeDimension.comp_of_flat (f : X ⟶ Y) (g : Y ⟶ S) [LocallyOfFiniteType f]
    [LocallyOfFiniteType g] [Flat f] {d e : ℕ} (hf : RelativeDimension f d)
    (hg : RelativeDimension g e) : RelativeDimension (f ≫ g) (d + e) := by
  refine relativeDimension_of_topologicalKrullDimAt_fiber_eq (f ≫ g) fun s w ↦ ?_
  rw [← Scheme.Hom.topologicalKrullDimAt_fiber_fiberι (f ≫ g) s w]
  set x : X := (f ≫ g).fiberι s w with hx
  obtain ⟨heqf, hdimf⟩ := hf (f x) ⟨f.asFiber x⟩
  obtain ⟨heqg, hdimg⟩ := hg (g (f x)) ⟨g.asFiber (f x)⟩
  have hflat : IsFlatAt f.toLRSHom.toShHom x := Flat.stalkMap f x
  rw [topologicalKrullDimAt_fiber_comp_eq_add_of_isFlatAt f g x hflat,
    topologicalKrullDimAt_eq_of_equidimensional (Y.residueField (f x)) (f.fiber (f x))
      (f.fiberToSpecResidueField (f x)) heqf hdimf (f.asFiber x),
    topologicalKrullDimAt_eq_of_equidimensional (S.residueField (g (f x))) (g.fiber (g (f x)))
      (g.fiberToSpecResidueField (g (f x))) heqg hdimg (g.asFiber (f x)), Nat.cast_add]

end AlgebraicGeometry

end
