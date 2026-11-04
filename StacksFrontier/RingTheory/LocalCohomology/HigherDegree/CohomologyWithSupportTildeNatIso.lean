module

public import StacksFrontier.AlgebraicGeometry.Properties.ExtendFiniteType.LerayDegreewiseNatural
public import StacksFrontier.RingTheory.LocalCohomology.HigherDegree.CohomologyWithSupportComparison
public import StacksFrontier.RingTheory.LocalCohomology.HigherDegree.ComplementCohomologyDeltaNatural

/-!
# Stacks 0A6T degreewise, as a natural isomorphism of functors of the module

Let `A` be a Noetherian ring, let `I ⊆ A` be a finitely generated ideal, let `X = Spec A` and let
`Z = V(I)`. Stacks 0A6T identifies the cohomology of `X` with support in `Z` of the sheaf `M̃`,
read as an `A`-module, with the right derived functor of the algebraic `Z`-supported sections of
`M`, in every degree. `Stacks.LocalCohomologySequence.cohomologyWithSupportTildeIso` states that
identification one module at a time. This file states it as an isomorphism of **functors** of the
module.

The difference matters whenever the identification has to be applied to a tower of modules and
then passed to the inverse limit: an isomorphism of each individual term does not identify the
limits unless it is compatible with the transition maps, which is naturality.

Only one of the two factors of the object-level comparison needed work. The degreewise comparison
of the composite `M ↦ Γ_Z(X, M̃)` with `Γ_Z(X, -)` applied to `M̃` is
`Stacks.Cohomology.LerayDegreewise.rightDerivedCompNatIso`, whose hypotheses here are right
acyclicity of `Ẽ` for `Γ_Z(X, -)` at every injective `E` — Stacks 0A6T's input, available as
`Stacks.LocalCohomologySequence.rightAcyclic_sectionsWithSupport_tilde_of_injective` — and right
acyclicity of every module for `M ↦ M̃`, which holds because that functor is exact. The second
factor, `Stacks.LocalCohomologyTilde.rightDerivedSectionsWithSupportTildeIso`, is already a
natural isomorphism.

## Main definitions

* `Stacks.LocalCohomologySequence.cohomologyWithSupportTildeNatIso` — **Stacks 0A6T degreewise,
  as a natural isomorphism of functors of the module.**

## Main results

* `Stacks.LocalCohomologySequence.cohomologyWithSupportTildeNatIso_hom_app` — its component at a
  module is the object-level comparison
  `Stacks.LocalCohomologySequence.cohomologyWithSupportTildeIso`, so nothing new is chosen.

## Implementation notes

The closed subset is `PrimeSpectrum.zeroLocus (I : Set A)` on the algebraic side and
`Stacks.LocalCohomologySequence.zeroLocusSubset I` on the geometric one; the two are the same
set, and `Stacks.LocalCohomologyTilde.supportSubset` is the identity on sets, so the three
spellings agree definitionally. This is the same juggling that
`Stacks.LocalCohomologySequence.cohomologyWithSupportTildeIso` performs.

No Stacks tag attribute is attached. Tag 0A6T is already registered in degree zero on
`Stacks.LocalCohomologyTilde.sectionsWithSupportTildeIso` and degreewise on
`Stacks.LocalCohomologySequence.cohomologyWithSupportTildeIso`; this is the latter restated, not
a further clause.

## References

* [Stacks Project, Tag 0A6T](https://stacks.math.columbia.edu/tag/0A6T)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
* [Stacks Project, Tag 05T8](https://stacks.math.columbia.edu/tag/05T8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open Stacks.Cohomology.SectionsWithSupport
open Stacks.LocalCohomologyTilde

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

namespace Stacks.LocalCohomologySequence

variable {A : CommRingCat.{u}}

/-- **Stacks 0A6T degreewise, as a natural isomorphism of functors of the module.** For a
Noetherian ring `A` and a finitely generated ideal `I`, the functor `M ↦ H^n_{V(I)}(X, M̃)` read
over `A` is isomorphic to the `n`-th right derived functor of the algebraic `V(I)`-supported
sections, naturally in `M`. -/
def cohomologyWithSupportTildeNatIso [IsNoetherianRing A] (I : Ideal A) (hI : I.FG) (n : ℕ) :
    cohomologyWithSupportBaseFunctor I n ≅
      (Stacks.LocalCohomology.sectionsWithSupportInFunctor.{u, u} A
        (PrimeSpectrum.zeroLocus (I : Set A))).rightDerived n :=
  Functor.isoWhiskerRight
      (Stacks.Cohomology.LerayDegreewise.rightDerivedCompNatIso (tildeSheafFunctor A)
        (sectionsWithSupport (Spec A).toRingedSpace (zeroLocusSubset I)
          (isClosed_zeroLocusSubset _))
        (fun E hE => have := hE; rightAcyclic_sectionsWithSupport_tilde_of_injective I hI E)
        rightAcyclic_tildeSheafFunctor n).symm (globalToBase A) ≪≫
    rightDerivedSectionsWithSupportTildeIso (PrimeSpectrum.zeroLocus (I : Set A))
      (isClosed_zeroLocusSubset I) n

/-- The component of the natural comparison at a module is the object-level comparison
`Stacks.LocalCohomologySequence.cohomologyWithSupportTildeIso`: the natural version is the same
isomorphism, assembled from the same two factors in the same order. -/
theorem cohomologyWithSupportTildeNatIso_hom_app [IsNoetherianRing A] (I : Ideal A) (hI : I.FG)
    (n : ℕ) (M : ModuleCat.{u} A) :
    (cohomologyWithSupportTildeNatIso I hI n).hom.app M =
      (cohomologyWithSupportTildeIso I hI M n).hom :=
  rfl

end Stacks.LocalCohomologySequence

end
