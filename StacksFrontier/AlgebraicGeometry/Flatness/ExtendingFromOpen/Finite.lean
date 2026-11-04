module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Flatness.ExtendingFromOpen.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Defs

/-!
# Finiteness of a proper flat morphism over a dense open

A flat and proper morphism of schemes which is finite over a dense open subscheme of the base is
finite everywhere, provided either the morphism is locally of finite presentation or the open is
retrocompact.

## Main results

* `AlgebraicGeometry.isFinite_of_isFinite_over_dense_open`: a proper flat morphism which is finite
  over a dense open of the base is finite.

## Implementation notes

The restriction of the morphism to the open subscheme is written as the base-change morphism
`CategoryTheory.Limits.pullback.snd f U.ι`, and the two alternative finiteness assumptions of
the source are kept as a disjunction.

## References

* [Stacks Project, Tag 0B48](https://stacks.math.columbia.edu/tag/0B48)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A proper flat morphism which is finite over a dense open of the base is finite, provided it is
locally of finite presentation or the open is retrocompact. -/
@[stacks 0B48]
theorem isFinite_of_isFinite_over_dense_open {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [Flat f] (U : S.Opens) (hU : Dense (U : Set S))
    [IsFinite (pullback.snd f U.ι)]
    (hfin : LocallyOfFinitePresentation f ∨ IsRetrocompact (U : Set S)) :
    IsFinite f := by
  have hdim : RelativeDimensionLE f 0 :=
    relativeDimensionLE_of_dense_open f U hU 0
      (fun x => le_of_eq ((quasiFiniteAt_iff_fiberDimensionAt_eq_zero
        (pullback.snd f U.ι) x).mp
        (((forall_quasiFiniteAt_iff (pullback.snd f U.ι)).mpr
          ⟨inferInstance, inferInstance⟩) x))) hfin
  exact (IsFinite.iff_isProper_and_locallyQuasiFinite f).2
    ⟨inferInstance, ((forall_quasiFiniteAt_iff f).mp fun x ↦
      (quasiFiniteAt_iff_fiberDimensionAt_eq_zero f x).mpr
        (le_antisymm (hdim x) (topologicalKrullDimAt_nonneg (f.asFiber x)))).2⟩

end AlgebraicGeometry

end
