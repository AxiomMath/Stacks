module

public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorRepresentableAmbient
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.DoubledOriginNotSeparated

/-!
# The hypothesis of Stacks Tag 0B9A is vacuous for `d ≤ 1`, and carries no separatedness

Stacks Tag 0B9A assumes that for every `s ∈ S` and every `d`-tuple of points of the fibre `X_s`
some affine open of `X` contains all `d` of them. For `d ≤ 1` that assumption holds for *every*
morphism of schemes — `Stacks.Hilbert.exists_isAffineOpen_forall_mem_of_le_one` — while the
proof of the tag needs, for its footnote, an affine open around `d + 1` points of one fibre, and
in particular around *two* points, which by
`AlgebraicGeometry.isSeparated_of_exists_isAffineOpen_pair` is enough to make `X ⟶ S` separated.

This file witnesses the gap between the two with a concrete scheme: affine space with its origin
doubled, whose coordinate morphism is not separated
(`AlgebraicGeometry.not_isSeparated_coordinateMorphism`), so no affine open contains both chart
origins even though they lie in one fibre. The tag's hypothesis for `d ≤ 1` therefore does not
imply the two-point case, and the `@[stacks 0B9A]` attribute accordingly sits on the theorem
`nonempty_representsHilbertFunctorOfRank_of_exists_isAffineOpen_forall_mem_of_ne_one`, which
states the tag under the source's own `d`-tuple hypothesis for every `d ≠ 1`, its proof for
`2 ≤ d` running through
`nonempty_representsHilbertFunctorOfRank_of_exists_isAffineOpen_forall_mem_of_two_le`, where
that hypothesis does contain the two-point case (both in the namespace `Stacks.Hilbert`); the
generalisation to every `d`,
`Stacks.Hilbert.nonempty_representsHilbertFunctorOfRank_of_exists_isAffineOpen_forall_mem`, asks
for it at `max d 2` points instead. For this same scheme the tag's conclusion itself fails at
`d = 1`: no scheme represents its degree-`1` Hilbert functor, which is
`Stacks.Hilbert.not_nonempty_representsHilbertFunctorOfRank_one` in
`StacksFrontier/AlgebraicGeometry/Picard/HilbertFunctorRepresentableAmbientNotRepresentable.lean`.

## Main results

* `Stacks.Hilbert.exists_isAffineOpen_forall_mem_of_le_one` — for `d ≤ 1` the hypothesis of
  Stacks Tag 0B9A holds for every morphism of schemes.
* `AlgebraicGeometry.not_exists_isAffineOpen_pair_coordinateMorphism` — it does not imply the
  two-point case: for the coordinate morphism of affine space with doubled origin, in positive
  dimension, some two points of a fibre lie in no common affine open.
* `AlgebraicGeometry.not_hasAffineFinitePointsInFibres_coordinateMorphism` — a fortiori the set
  form `AlgebraicGeometry.HasAffineFinitePointsInFibres` fails for that morphism.

## Implementation notes

Both negative statements are contrapositives of
`AlgebraicGeometry.isSeparated_of_exists_isAffineOpen_pair` against the proved
non-separatedness of the coordinate morphism; no property of the doubled origin is used beyond
that non-separatedness.

## References

* [Stacks Project, Tag 0B9A](https://stacks.math.columbia.edu/tag/0B9A)
* [Stacks Project, Tag 04QI](https://stacks.math.columbia.edu/tag/04QI)
* [Stacks Project, Tag 01JD](https://stacks.math.columbia.edu/tag/01JD)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.Hilbert

/-- **For `d ≤ 1` the hypothesis of Stacks Tag 0B9A holds for every morphism of schemes**: a
tuple of at most one point of a fibre lies in an affine open of `X` because every point of a
scheme does, and an empty tuple lies in the empty affine open. -/
theorem exists_isAffineOpen_forall_mem_of_le_one {X S : Scheme.{u}} (f : X ⟶ S) {d : ℕ}
    (hd : d ≤ 1) (s : S) (x : Fin d → X) (_hx : ∀ i, f.base (x i) = s) :
    ∃ U : X.Opens, IsAffineOpen U ∧ ∀ i, x i ∈ U := by
  rcases Nat.lt_or_ge d 1 with hd' | hd'
  · exact ⟨⊥, isAffineOpen_bot _, fun i => absurd i.isLt (by omega)⟩
  · have hd1 : d = 1 := le_antisymm hd hd'
    subst hd1
    obtain ⟨U, hU, hxU, -⟩ :=
      exists_isAffineOpen_mem_and_subset (U := ⊤) (Set.mem_univ (x 0))
    refine ⟨U, hU, fun i => ?_⟩
    rwa [show i = 0 from Subsingleton.elim i 0]

end Stacks.Hilbert

namespace AlgebraicGeometry

/-- **The hypothesis of Stacks Tag 0B9A does not imply its two-point case.** For the coordinate
morphism of affine `n`-space with its origin doubled, `n > 0`, there are two points of a single
fibre lying in no common affine open: that morphism is not separated, and two points of a fibre
in a common affine open would make it separated by
`AlgebraicGeometry.isSeparated_of_exists_isAffineOpen_pair`.

Its hypothesis for `d ≤ 1` holds for this morphism, as it does for every morphism of schemes, by
`Stacks.Hilbert.exists_isAffineOpen_forall_mem_of_le_one`. -/
theorem not_exists_isAffineOpen_pair_coordinateMorphism (k : Type u) [Field k] (n : ℕ)
    (hn : 0 < n) :
    ¬ ∀ (s : Spec (.of (MvPolynomial (Fin n) k))) (x y : affineSpaceWithDoubledZero k n),
        (coordinateMorphism k n).base x = s → (coordinateMorphism k n).base y = s →
          ∃ U : (affineSpaceWithDoubledZero k n).Opens, IsAffineOpen U ∧ x ∈ U ∧ y ∈ U :=
  fun h => not_isSeparated_coordinateMorphism k n hn
    (isSeparated_of_exists_isAffineOpen_pair (coordinateMorphism k n) h)

/-- **The set form of the fibrewise affineness hypothesis fails for the doubled origin.** It
implies the two-point case, which
`AlgebraicGeometry.not_exists_isAffineOpen_pair_coordinateMorphism` refutes. -/
theorem not_hasAffineFinitePointsInFibres_coordinateMorphism (k : Type u) [Field k] (n : ℕ)
    (hn : 0 < n) :
    ¬ HasAffineFinitePointsInFibres (coordinateMorphism k n) := by
  refine fun h => not_exists_isAffineOpen_pair_coordinateMorphism k n hn fun s x y hx hy => ?_
  obtain ⟨U, hU, hmem⟩ := h s {x, y} (Set.toFinite _) (by
    rintro z (rfl | rfl)
    · exact hx
    · exact hy)
  exact ⟨U, hU, hmem (Set.mem_insert _ _), hmem (Set.mem_insert_of_mem _ rfl)⟩

end AlgebraicGeometry

end
