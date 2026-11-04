module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroups.CrossedProductSplit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.BrauerGroupFunctionField
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.Hilbert90

/-!
# Galois cohomology of the multiplicative group of the function field of a curve

Let `k` be algebraically closed and let `K` be a finitely generated extension of `k` of
transcendence degree one — for instance the function field of a curve over `k`. Every locally
constant `2`-cocycle of the absolute Galois group of `K` with values in the units of a separable
closure is a coboundary: the triviality of the Brauer group of `K` splits every crossed product,
and the inflation argument reduces an infinite-level cocycle to a finite Galois level where
crossed products are available.

In degree one the corresponding statement needs no hypothesis at all: it is Hilbert 90 for
infinite Galois extensions, `Stacks.GaloisCohomology.isMulCoboundary₁_separableClosure`, which is
already available for every field.

## Main results

* `Stacks.GaloisCohomology.isMulCoboundary₂_separableClosure_of_essFiniteType_trdeg_eq_one`:
  degree-two vanishing for a finitely generated extension of transcendence degree one of an
  algebraically closed field.
* `Stacks.GaloisCohomology.isMulCoboundary₂_separableClosure_functionField`: the same for the
  function field of a curve over an algebraically closed field.

## Implementation notes

Group cohomology is used in the explicit cocycle form of Mathlib's `groupCohomology.IsMulCocycle₂`
and `groupCohomology.IsMulCoboundary₂` together with local constancy, rather than through
`Stacks.GroupCohomology.continuousGroupCohomology`. That is the form in which the crossed-product
machinery of this development is stated, and the comparison of the two is not part of this file.

The hypothesis of
`Stacks.GaloisCohomology.isMulCoboundary₂_separableClosure_of_forall_brauer` asks only that the
relative Brauer group of each finite Galois subextension be trivial; the triviality of the whole
Brauer group of `K` discharges it without looking at the subextension, which is why the
subextension argument is ignored below.

## References

* [Stacks Project, Tag 03RG](https://stacks.math.columbia.edu/tag/03RG): the vanishing of
  `H^q(Spec K, 𝐆_m)` for `q ≥ 1` when `K` has transcendence degree one over an algebraically
  closed field. The results here are its Galois-cohomological content in degrees one and two.
  Degrees `q ≥ 3` are a separate argument, through the four-term sequence
  `0 → A → M → M ⊗ 𝐐 → B → 0`, and the identification of Galois cohomology with the étale
  cohomology of `Spec K` is Tag 03QU, which this library does have, in every degree, as
  `AlgebraicGeometry.etaleSheafCohomologyAddEquivContinuousGroupCohomology`. Feeding the
  results here into it would still need their cocycle form to be compared with
  `continuousGroupCohomology`, which the library does not relate above degree zero.
* [Stacks Project, Tag 03R8](https://stacks.math.columbia.edu/tag/03R8): the criterion that turns
  the vanishing of Brauer groups of all finite extensions into this vanishing.
* [Stacks Project, Tag 03RF](https://stacks.math.columbia.edu/tag/03RF): the Brauer group input,
  `AlgebraicGeometry.brauerGroup_functionField_eq_one`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory groupCohomology

universe u

namespace Stacks.GaloisCohomology

/-- Every locally constant `2`-cocycle of the absolute Galois group of a finitely generated field
extension of transcendence degree one of an algebraically closed field, with values in the units
of a separable closure, is a coboundary. -/
theorem isMulCoboundary₂_separableClosure_of_essFiniteType_trdeg_eq_one
    (k : Type u) [Field k] [IsAlgClosed k] (K : Type u) [Field K] [Algebra k K]
    [Algebra.EssFiniteType k K] (h : Algebra.trdeg k K = 1)
    (f : Gal(SeparableClosure K/K) × Gal(SeparableClosure K/K) → (SeparableClosure K)ˣ)
    (hloc : IsLocallyConstant f) (hf : IsMulCocycle₂ f) : IsMulCoboundary₂ f :=
  isMulCoboundary₂_separableClosure_of_forall_brauer K
    (fun _ y _ => brauerGroup_eq_one_of_essFiniteType_trdeg_eq_one k K h y) f hloc hf

set_option synthInstance.maxHeartbeats 400000 in
-- The function field is a coercion of a `CommRingCat`, and unfolding it is needed to find the
-- action of the absolute Galois group on the units of the separable closure.
/-- Every locally constant `2`-cocycle of the absolute Galois group of the function field of a
curve over an algebraically closed field, with values in the units of a separable closure, is a
coboundary. -/
theorem isMulCoboundary₂_separableClosure_functionField (k : Type u) [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [IsCurve k g]
    (f : Gal(SeparableClosure X.functionField/X.functionField) ×
        Gal(SeparableClosure X.functionField/X.functionField) →
      (SeparableClosure X.functionField)ˣ)
    (hloc : IsLocallyConstant f) (hf : IsMulCocycle₂ f) : IsMulCoboundary₂ f :=
  isMulCoboundary₂_separableClosure_of_forall_brauer X.functionField
    (fun _ y _ => brauerGroup_functionField_eq_one k g y) f hloc hf

end Stacks.GaloisCohomology

end
