module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.OpenImmersionCriterion
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.EtaleUniversallyBounded
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.UniversallyBoundedBaseChange

/-!
# An étale morphism whose fibres have degree at most one is an open immersion

This is the base case of the induction of the third paragraph of Stacks 03XW: there the
induction runs on an integer `n` bounding the degrees of the fibres of an étale morphism
`T' ⟶ T` of affine schemes, and for `n = 1` the source says that `T' ⟶ T` is an open immersion
by Étale Morphisms, Theorem 025G, "and the result is clear".

The passage from the bound to the hypotheses of Tag 025G is a counting argument. Tag 025G asks
for universal injectivity, which is surjectivity of the relative diagonal, and surjectivity of
the relative diagonal is what a bound of one on the fibre degrees gives: the fibre of the first
projection `X ×_Y X ⟶ X` over a point `x` has at most one point, by Tag 03J7 and the
cardinality criterion of Tag 03WU, and it contains the point contributed by the diagonal, so
every point of `X ×_Y X` over `x` *is* that point.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.surjective_diagonal_of_boundsFiberDegrees_one`: the relative diagonal of
  an étale morphism whose fibre degrees are bounded by one is surjective.
* `AlgebraicGeometry.isOpenImmersion_of_boundsFiberDegrees_one`: such a morphism is an open
  immersion.

## Implementation notes

Nothing here carries a tag: this is the use the proof of Stacks 03XW makes of Tag 025G, not a
statement of a tag of its own. Tag 025G is `AlgebraicGeometry.tfae_isOpenImmersion`, Tag 03WU is
`AlgebraicGeometry.etale_boundsFiberDegrees_tfae` and Tag 03J7 is the instance
`AlgebraicGeometry.boundsFiberDegrees_isStableUnderBaseChange`.

No separatedness is needed, and in particular the clopen decomposition of `X ×_Y X` of
`StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.EtaleDiagonalDecomposition` is not used:
the two points of the fibre which the argument compares are produced directly by
`AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback`, and the field-valued point along
which the fibre is taken is the residue field at the point of `X ×_Y X` under consideration.

## References

* [Stacks Project, Tag 03XW](https://stacks.math.columbia.edu/tag/03XW)
* [Stacks Project, Tag 025G](https://stacks.math.columbia.edu/tag/025G)
* [Stacks Project, Tag 03J7](https://stacks.math.columbia.edu/tag/03J7)
* [Stacks Project, Tag 03WU](https://stacks.math.columbia.edu/tag/03WU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The relative diagonal of an étale morphism whose fibre degrees are bounded by one is
surjective.

For a point `z` of `X ×_Y X` let `x` be its image under the first projection and let `K` be the
residue field of `X ×_Y X` at `z`. The fibre of the first projection over the resulting
`K`-valued point of `X` has at most one point, because the first projection is a base change of
`f` (Tag 03J7) and so inherits the bound, which in the cardinality form of Tag 03WU is a bound
on the number of points of every field-valued base change. That fibre contains a point over `z`
and a point over the image of `x` under the diagonal, so those two points of `X ×_Y X`
agree. -/
theorem surjective_diagonal_of_boundsFiberDegrees_one [Etale f]
    (h : BoundsFiberDegrees f ((1 : ℕ) : ℤ)) :
    Surjective (pullback.diagonal f) := by
  have hbc : BoundsFiberDegrees (pullback.fst f f) ((1 : ℕ) : ℤ) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := fun {_ _ : Scheme.{u}} (p : _ ⟶ _) ↦ BoundsFiberDegrees p ((1 : ℕ) : ℤ))
      (IsPullback.of_hasPullback f f).flip h
  have hcard := ((etale_boundsFiberDegrees_tfae (pullback.fst f f) 1).out 1 2).mp hbc
  refine ⟨fun z ↦ ?_⟩
  have hcp : ((pullback f f).fromSpecResidueField z) (IsLocalRing.closedPoint _) = z :=
    Scheme.fromSpecResidueField_apply z _
  have hgc : ((pullback f f).fromSpecResidueField z ≫ pullback.fst f f)
      (IsLocalRing.closedPoint _) = pullback.fst f f z :=
    (Scheme.Hom.comp_apply _ _ _).trans (congrArg (fun y ↦ (pullback.fst f f) y) hcp)
  have hsub : Subsingleton (pullback ((pullback f f).fromSpecResidueField z ≫
      pullback.fst f f) (pullback.fst f f) : Scheme.{u}) :=
    Cardinal.le_one_iff_subsingleton.mp (by
      exact_mod_cast hcard _ ((pullback f f).fromSpecResidueField z ≫ pullback.fst f f))
  obtain ⟨p₁, -, hp₁⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := (pullback f f).fromSpecResidueField z ≫ pullback.fst f f)
    (g := pullback.fst f f) (IsLocalRing.closedPoint _) z hgc
  obtain ⟨p₂, -, hp₂⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := (pullback f f).fromSpecResidueField z ≫ pullback.fst f f)
    (g := pullback.fst f f) (IsLocalRing.closedPoint _)
    (pullback.diagonal f (pullback.fst f f z))
    (by rw [hgc, ← Scheme.Hom.comp_apply, pullback.diagonal_fst]; rfl)
  refine ⟨pullback.fst f f z, ?_⟩
  rw [← hp₂, Subsingleton.elim p₂ p₁]
  exact hp₁

/-- **The base case of the induction of Stacks 03XW.** An étale morphism of schemes whose fibre
degrees are bounded by one is an open immersion.

This is Tag 025G applied to the universal injectivity which
`AlgebraicGeometry.surjective_diagonal_of_boundsFiberDegrees_one` provides. -/
@[sga "1 I 5.1" "sufficiency"]
theorem isOpenImmersion_of_boundsFiberDegrees_one [Etale f]
    (h : BoundsFiberDegrees f ((1 : ℕ) : ℤ)) :
    IsOpenImmersion f := by
  have hui : UniversallyInjective f :=
    (UniversallyInjective.iff_diagonal f).mpr
      (surjective_diagonal_of_boundsFiberDegrees_one f h)
  have hand : UniversallyInjective f ∧ Etale f := ⟨hui, inferInstance⟩
  exact ((tfae_isOpenImmersion f).out 2 1).mp hand

end AlgebraicGeometry

end
