module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.NoDeformations.CaseIKernelVanishing
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.NoDeformations.CohomologySupportSubscheme

/-!
# Case I of Stacks 0G0R: the closed point is off the subscheme

Case I of [Stacks, Tag 0G0R] takes a closed point `z` of the fibre `Y_s ×_k Y_s` that does not
lie on the diagonal and concludes `K|_{U(z)} = 0` for some open neighbourhood `U(z)` of `z` in
`X ×_S Y`; in the source's bookkeeping it then sets `Z(z) = ∅`. With `Z` taken to be the
scheme-theoretic support of `H^0(K)` there is no bookkeeping to do: the vanishing of the stalk of
`H^0(K)` at `z` already says that `z` is off `Z`.

That is this file. `AlgebraicGeometry.exists_mem_forall_isZero_stalkHomology_caseI` supplies the
vanishing from the source's own hypothesis — that the cohomology of `L i^* K` is supported on a
set not containing `z`, which in the source is the diagonal — and
`AlgebraicGeometry.notMem_support_cohomologySupportIdeal_of_isZero_stalk` turns it into the
statement about `Z`.

## Main results

* `AlgebraicGeometry.notMem_support_cohomologySupportIdeal_caseI`: a closed point of a closed
  subscheme `Z₀ ⊆ W` off the support of the cohomology of `L i^* K` has image off the
  scheme-theoretic support of `H^0(K)`.

## Implementation notes

`AlgebraicGeometry.Scheme.Modules` is by definition `SheafOfModules W.ringCatSheaf`, and the two
spellings of perfectness — `AlgebraicGeometry.RingedSpace.IsPerfect` and
`Stacks.Cohomology.PerfectComplexes.IsPerfect` — are the same predicate, so the two statements
being composed take their arguments at the same types with no transport.

## References

* [Stacks Project, Tag 0G0R](https://stacks.math.columbia.edu/tag/0G0R)
* [Stacks Project, Tag 0G03](https://stacks.math.columbia.edu/tag/0G03)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u

namespace AlgebraicGeometry

attribute [local instance 100000] HasDerivedCategory.standard

variable {Z₀ W : Scheme.{u}} (i : Z₀ ⟶ W) [IsClosedImmersion i] [IsNoetherian W]

/-- **Case I of [Stacks, Tag 0G0R], read on the subscheme `Z`.** Let `i : Z₀ ⟶ W` be a closed
immersion into a Noetherian scheme, let `K` be a perfect object of `D(𝒪_W)`, let `z` be a closed
point of `Z₀` and suppose the cohomology of `L i^* K` is supported on a subset `T` of `Z₀` with
`z ∉ T`. Then `i(z)` does not lie on the scheme-theoretic support of `H^0(K)`.

In the source `Z₀` is the fibre `Y_s ×_k Y_s`, `L i^* K` is `Δ_{Y_s/k,*}𝒪_{Y_s}`, `T` is the
diagonal, and `z ∉ T` is the case distinction opening Case I. -/
theorem notMem_support_cohomologySupportIdeal_caseI
    (z : Z₀) (hz : IsClosed ({z} : Set Z₀)) (T : Set Z₀) (hzT : z ∉ T)
    (K : DerivedCategory W.Modules)
    (hK : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := W.toRingedSpace) K)
    (hT : CohomologySupportedOn Z₀.ringCatSheaf T
      ((derivedPullback i.toLRSHom.toShHom).obj K)) :
    i.base z ∉ (cohomologySupportIdeal K hK).support := by
  have : IsLocallyNoetherian W := inferInstance
  obtain ⟨U, hiz, hU⟩ :=
    exists_mem_forall_isZero_stalkHomology_caseI_of_cohomologySupportedOn i z hz T hzT K hK hT
  exact notMem_support_cohomologySupportIdeal_of_isZero_stalk K hK (i.base z)
    (hU (i.base z) hiz 0)

end AlgebraicGeometry

end
