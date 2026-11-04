module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.KrullDimension
public import StacksFrontier.Algebra.Homology.DerivedCategory.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentAbelian.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.Regular
public import StacksFrontier.AlgebraicGeometry.CoherentAbelian.SchemeModules

/-!
# The `Hom`-vanishing across a cohomology gap, as a predicate

On a regular Noetherian scheme `X` of dimension `d` there is no nonzero morphism from a bounded
complex with coherent cohomology concentrated in degrees `≥ a + d` to one concentrated in degrees
`< a`. This is part (2) of [Stacks, Tag 0FZ3], and it is the only input of the splitting of
[Stacks, Tag 0FZ4] in which regularity and the dimension of `X` are used.

## Main definitions

* `AlgebraicGeometry.HomVanishingAcrossSeparatedCohomologyGap` (also called
  `AlgebraicGeometry.SeparatedCohomologyHomVanishing`) is part (2) of [Stacks, Tag 0FZ3] as a
  predicate on a scheme and a natural number: no nonzero morphisms between bounded complexes with
  coherent cohomology whose cohomological ranges are separated by the dimension.

## Implementation notes

Packaging the statement as a predicate lets the splitting of [Stacks, Tag 0FZ4] be stated against
a single hypothesis. The predicate holds for every regular Noetherian scheme:
see `AlgebraicGeometry.forall_separatedCohomologyHomVanishing`.

Membership of a complex in `D^b_{Coh}(𝒪_X)` is spelled out as the conjunction of `t`-boundedness
for the canonical t-structure and coherence of every cohomology sheaf, rather than through a
subcategory, so that complexes formed in `D(𝒪_X)` — the truncations of [Stacks, Tag 0FZ4], say —
can be fed in without transporting along an equivalence. The derived category is read at
`CategoryTheory.HasDerivedCategory.standard`, for the same reason.

## References

* [Stacks Project, Tag 0FZ3](https://stacks.math.columbia.edu/tag/0FZ3)
* [Stacks Project, Tag 0FZ4](https://stacks.math.columbia.edu/tag/0FZ4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard

/-- **[Stacks, Tag 0FZ3] part (2).** On a regular Noetherian scheme `X` of dimension `d` there
is no nonzero morphism from a bounded complex with coherent cohomology whose cohomology lives in
degrees `≥ a + d` to one whose cohomology lives in degrees `< a`.

This is the input the splitting of [Stacks, Tag 0FZ4] rests on, and it is the only place where
regularity and the dimension of `X` enter that argument. -/
public def HomVanishingAcrossSeparatedCohomologyGap (X : Scheme.{u}) [IsNoetherian X] (d : ℕ) :
    Prop :=
  IsRegular X → topologicalKrullDim X = (d : WithBot ℕ∞) →
    ∀ K L : DerivedCategory X.Modules,
      DerivedCategory.TStructure.t.bounded K →
      DerivedCategory.TStructure.t.bounded L →
      (∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj K).IsCoherent) →
      (∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj L).IsCoherent) →
      ∀ a : ℤ,
        (∀ i : ℤ, i < a + (d : ℤ) →
          IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj K)) →
        (∀ i : ℤ, a ≤ i →
          IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj L)) →
        Subsingleton (K ⟶ L)

/-- Alternative name for `HomVanishingAcrossSeparatedCohomologyGap`: part (2) of
[Stacks, Tag 0FZ3] as a `Prop`. -/
public alias SeparatedCohomologyHomVanishing := HomVanishingAcrossSeparatedCohomologyGap

end AlgebraicGeometry

end
