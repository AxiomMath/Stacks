module

public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import StacksFrontier.AlgebraicGeometry.FibreDimensionBaseChange.Product

/-!
# Closed points and local dimension under an algebraic extension of the base field

Let `X` be a scheme locally of finite type over a field `k` and let `K/k` be an *algebraic*
extension. The projection `X_K = X ×_{Spec k} Spec K ⟶ X` is then a closed map, so it carries
closed points to closed points; combined with part (1) of [Stacks, Tag 02FY] in the one-point
form `AlgebraicGeometry.topologicalKrullDimAt_eq_of_isPullback_of_subsingleton`, this says that
an equidimensionality statement at the closed points of `X` transports to the closed points of
`X_K`.

This is the half of "dimensions are not changed by replacing `k` by a bigger field" that the
global statement `AlgebraicGeometry.topologicalKrullDim_pullback_spec_algebraMap` does not give:
a dimension count run at the closed points of `X` over `k̄` needs to know not only that
`dim X_{k̄} = dim X` but that `dim_{x'} X_{k̄} = n` at every closed point `x'` of `X_{k̄}`, and
for that one has to know that `x'` lies over a closed point of `X`.

## Main results

* `AlgebraicGeometry.isClosedMap_pullback_fst_spec_algebraMap`: for `K/k` algebraic, the
  projection `X_K ⟶ X` is a closed map, being a base change of the integral morphism
  `Spec K ⟶ Spec k`.
* `AlgebraicGeometry.isClosed_singleton_pullback_fst_spec_algebraMap`: a closed point of `X_K`
  lies over a closed point of `X`.
* `AlgebraicGeometry.topologicalKrullDimAt_pullback_spec_algebraMap_eq_of_isClosed`: if `X` has
  local dimension `n` at each of its closed points, then so does `X_K` at each of its closed
  points.

## Implementation notes

Closedness of the projection is Mathlib's: an algebraic extension of fields is integral, so
`Spec K ⟶ Spec k` is `AlgebraicGeometry.IsIntegralHom`, that property is stable under base
change, and an integral morphism is universally closed. No finite type hypothesis on `X` is
needed for closedness; it is needed only for the dimension statement, which rests on Tag 02FY.

No `@[stacks]` attribute is attached. The clause of Tag 02FY in play is part (1), registered
faithfully and in full generality on
`AlgebraicGeometry.topologicalKrullDimAt_fiber_eq_of_isPullback`; what is added here is the
bookkeeping about closed points that lets that clause be used at closed points, not a further
clause of the tag.

## References

* [Stacks Project, Tag 02FY](https://stacks.math.columbia.edu/tag/02FY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (k K : Type u) [Field k] [Field K] [Algebra k K]

/-- **An algebraic extension of fields is an integral morphism on spectra.** -/
instance isIntegralHom_spec_algebraMap [Algebra.IsAlgebraic k K] :
    IsIntegralHom (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
  rw [IsIntegralHom.SpecMap_iff, CommRingCat.hom_ofHom]
  exact algebraMap_isIntegral_iff.mpr (Algebra.isAlgebraic_iff_isIntegral.mp ‹_›)

variable {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **For `K/k` algebraic the projection `X_K ⟶ X` is a closed map.** It is a base change of
`Spec K ⟶ Spec k`, which is integral, hence universally closed. -/
theorem isClosedMap_pullback_fst_spec_algebraMap [Algebra.IsAlgebraic k K] :
    IsClosedMap (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :=
  (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).isClosedMap

/-- **A closed point of `X_K` lies over a closed point of `X`**, for `K/k` algebraic. -/
theorem isClosed_singleton_pullback_fst_spec_algebraMap [Algebra.IsAlgebraic k K]
    {x' : ↑(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))))}
    (hx' : IsClosed ({x'} : Set ↑(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))))) :
    IsClosed ({(pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).base x'} :
      Set X) := by
  have h := isClosedMap_pullback_fst_spec_algebraMap k K f _ hx'
  rwa [Set.image_singleton] at h

/-- **Equidimensionality at the closed points survives an algebraic extension of the base
field.** If `X` is locally of finite type over `k` and has local dimension `n` at each of its
closed points, and `K/k` is algebraic, then `X_K` has local dimension `n` at each of its closed
points: such a point lies over a closed point of `X` by
`AlgebraicGeometry.isClosed_singleton_pullback_fst_spec_algebraMap`, and the local dimension is
unchanged along the projection by part (1) of [Stacks, Tag 02FY]. -/
theorem topologicalKrullDimAt_pullback_spec_algebraMap_eq_of_isClosed [Algebra.IsAlgebraic k K]
    [LocallyOfFiniteType f] {n : ℕ}
    (hdim : ∀ x : X, IsClosed ({x} : Set X) → topologicalKrullDimAt X x = (n : WithBot ℕ∞))
    (x' : ↑(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))))
    (hx' : IsClosed ({x'} : Set ↑(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))))) :
    topologicalKrullDimAt ↑(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) x' =
      (n : WithBot ℕ∞) := by
  rw [← topologicalKrullDimAt_eq_of_isPullback_of_subsingleton
    (IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) x']
  exact hdim _ (isClosed_singleton_pullback_fst_spec_algebraMap k K f hx')

end AlgebraicGeometry

end
