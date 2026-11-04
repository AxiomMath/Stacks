module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FibreDimensionBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Equidimensional

/-!
# Relative dimension is stable under base change

Let `f : X ⟶ S` be a morphism of schemes locally of finite type and let `f' : X' ⟶ S'` be a base
change of `f`. The fibres of `f'` are the base changes of the fibres of `f` along extensions of
residue fields, so they have the same local dimension at corresponding points. Hence both the
exact relative dimension `d` and the bound `≤ d` of Tag 02NJ are inherited by `f'`.

## Main results

* `AlgebraicGeometry.RelativeDimension.of_isPullback`: relative dimension `d` is preserved by
  base change.
* `AlgebraicGeometry.RelativeDimensionLE.of_isPullback`: relative dimension at most `d` is
  preserved by base change.

## Implementation notes

An arbitrary base change is presented by a cartesian square rather than by Mathlib's chosen
pullback object. Local finite type for the base-changed morphism is not an extra hypothesis: it
follows from the square, and is installed in the statement itself so that the relative-dimension
predicate for `f'` is well formed.

The comparison of local fibre dimensions across the square is Tag 02FY, and the passage between
constancy of the local dimension of a fibre and equidimensionality of that fibre is Tag 0A21.

## References

* [Stacks Project, Tag 02NK](https://stacks.math.columbia.edu/tag/02NK)
* [Stacks Project, Tag 02NJ](https://stacks.math.columbia.edu/tag/02NJ)
* [Stacks Project, Tag 02FY](https://stacks.math.columbia.edu/tag/02FY)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The fibre of a morphism locally of finite type is locally of finite type over the residue
field. -/
private theorem locallyOfFiniteType_fiberToSpecResidueField_of_locallyOfFiniteType
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (s : S) :
    LocallyOfFiniteType (f.fiberToSpecResidueField s) := by
  change LocallyOfFiniteType (Limits.pullback.snd f (S.fromSpecResidueField s))
  infer_instance

/-- In a cartesian square over a morphism `f` of relative dimension `d`, the fibre of the base
change has local dimension `d` at every point of its source: the fibre of `f'` through `x'` has
the same local dimension as the fibre of `f` through the image of `x'`, and the latter is
equidimensional of dimension `d`. -/
private theorem topologicalKrullDimAt_fiber_eq_of_isPullback_of_relativeDimension
    {X' X S' S : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    (hsq : IsPullback g' f' f g) [LocallyOfFiniteType f] {d : ℕ}
    (hf : RelativeDimension f d) (x' : X') :
    topologicalKrullDimAt (f'.fiber (f' x')) (f'.asFiber x') = (d : WithBot ℕ∞) := by
  have := locallyOfFiniteType_fiberToSpecResidueField_of_locallyOfFiniteType f (f (g' x'))
  obtain ⟨heq, hdim⟩ := hf (f (g' x')) ⟨f.asFiber (g' x')⟩
  rw [topologicalKrullDimAt_fiber_eq_of_isPullback hsq x']
  exact topologicalKrullDimAt_eq_of_equidimensional (S.residueField (f (g' x')))
    (f.fiber (f (g' x'))) (f.fiberToSpecResidueField (f (g' x'))) heq hdim (f.asFiber (g' x'))

/-- **Stacks Project, Tag 02NK.** Relative dimension `d` in the sense of Tag 02NJ is preserved by
an arbitrary base change: every nonempty fibre of the base change has local dimension `d` at each
of its points, hence is equidimensional of dimension `d`. -/
@[stacks 02NK "relative dimension d"]
public theorem RelativeDimension.of_isPullback {X' X S' S : Scheme.{u}} {g' : X' ⟶ X}
    {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S} (hsq : IsPullback g' f' f g)
    [LocallyOfFiniteType f] {d : ℕ} (hf : RelativeDimension f d) :
    letI : LocallyOfFiniteType f' := MorphismProperty.of_isPullback hsq inferInstance
    RelativeDimension f' d := by
  have : LocallyOfFiniteType f' := MorphismProperty.of_isPullback hsq inferInstance
  intro s' hs'
  have hlocal : ∀ w : f'.fiber s', topologicalKrullDimAt (f'.fiber s') w = (d : WithBot ℕ∞) :=
    fun w ↦ (Scheme.Hom.topologicalKrullDimAt_fiber_fiberι f' s' w).symm.trans
      (topologicalKrullDimAt_fiber_eq_of_isPullback_of_relativeDimension hsq hf (f'.fiberι s' w))
  have := locallyOfFiniteType_fiberToSpecResidueField_of_locallyOfFiniteType f' s'
  refine ⟨equidimensional_of_topologicalKrullDimAt_eq (S'.residueField s') (f'.fiber s')
    (f'.fiberToSpecResidueField s') hlocal, ?_⟩
  rw [topologicalKrullDim_eq_iSup_localKrullDim]
  have hloc : ∀ w : f'.fiber s', localKrullDim (f'.fiber s') w = (d : WithBot ℕ∞) := fun w ↦ by
    rw [← topologicalKrullDimAt_eq_localKrullDim]; exact hlocal w
  simp_rw [hloc]
  have : Nonempty (f'.fiber s') := hs'
  exact iSup_const

/-- **Stacks Project, Tag 02NK.** A bound `≤ d` on the relative dimension in the sense of
Tag 02NJ is preserved by an arbitrary base change, because the local dimension of a fibre is
unchanged along the square. -/
@[stacks 02NK "relative dimension at most d"]
public theorem RelativeDimensionLE.of_isPullback {X' X S' S : Scheme.{u}} {g' : X' ⟶ X}
    {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S} (hsq : IsPullback g' f' f g)
    [LocallyOfFiniteType f] {d : ℕ} (hf : RelativeDimensionLE f d) :
    letI : LocallyOfFiniteType f' := MorphismProperty.of_isPullback hsq inferInstance
    RelativeDimensionLE f' d := by
  have : LocallyOfFiniteType f' := MorphismProperty.of_isPullback hsq inferInstance
  intro x'
  rw [relativeDimensionLEAt_iff, topologicalKrullDimAt_fiber_eq_of_isPullback hsq x']
  exact hf (g' x')

end AlgebraicGeometry

end
