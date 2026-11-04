module

public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentComplex.QuasiCompactBounded
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.QuasicoherentCohomology
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectDual
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.RingedSiteComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PseudoCoherentAndFiniteTorDimension
import StacksCore.Tactic.StacksAttribute

/-!
# The dual of a perfect complex on a scheme

Let `X` be a scheme and let `K` be a perfect object of `D(𝒪_X)`. The **dual** of `K` is
`K^∨ = R𝓗om(K, 𝒪_X)`, the derived internal Hom into the structure sheaf placed in degree zero,
read off the ringed site of opens of `X` (`Stacks.SheafOfModules.derivedDual`). Then `K^∨` is
again perfect, its cohomology sheaves are quasi-coherent, and it is bounded above when `X` is
quasi-compact (part of [Stacks, Tag 08DQ]).

## Main results

* `Stacks.DerivedQCoh.isPerfect_derivedDual`: the dual of a perfect object of `D(𝒪_X)` is
  perfect.
* `Stacks.DerivedQCoh.isQuasicoherent_homology_derivedDual`: its cohomology sheaves are
  quasi-coherent.
* `Stacks.DerivedQCoh.exists_isLE_derivedDual`: on a quasi-compact scheme the dual is bounded
  above.

## References

* [Stacks Project, Tag 08DQ](https://stacks.math.columbia.edu/tag/08DQ)
* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
* [Stacks Project, Tag 08CM](https://stacks.math.columbia.edu/tag/08CM)
* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
* [Stacks Project, Tag 08E5](https://stacks.math.columbia.edu/tag/08E5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.DerivedQCoh

attribute [local instance 100000] HasDerivedCategory.standard

/-- The dual of a perfect object of `D(𝒪_X)` is perfect. -/
theorem isPerfect_derivedDual (X : Scheme.{u}) (K : DerivedCategory X.Modules)
    (hK : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) K) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace)
      (Stacks.SheafOfModules.derivedDual X.sheaf K) :=
  let : HasDerivedCategory.{u + 1} (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace) :=
    HasDerivedCategory.standard _
  (Stacks.Cohomology.PerfectComplexes.isPerfect_iff_ringedSite X.toRingedSpace _).2
    (Stacks.SheafOfModules.isPerfect_derivedDual X.sheaf K
      ((Stacks.Cohomology.PerfectComplexes.isPerfect_iff_ringedSite X.toRingedSpace K).1 hK))

/-- The dual of a perfect object of `D(𝒪_X)` has quasi-coherent cohomology sheaves. -/
theorem isQuasicoherent_homology_derivedDual (X : Scheme.{u}) (K : DerivedCategory X.Modules)
    (hK : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) K) (i : ℤ) :
    ((DerivedCategory.homologyFunctor X.Modules i).obj
      (Stacks.SheafOfModules.derivedDual X.sheaf K)).IsQuasicoherent :=
  AlgebraicGeometry.isQuasicoherentDerived_of_isPseudoCoherent X
    (Stacks.SheafOfModules.derivedDual X.sheaf K)
    (Stacks.Cohomology.TorAmplitude.isPseudoCoherent_of_isPerfect
      (Stacks.SheafOfModules.derivedDual X.sheaf K) (isPerfect_derivedDual X K hK)) i

/-- On a quasi-compact scheme the dual of a perfect object of `D(𝒪_X)` lies in cohomological
degrees `≤ b` for some `b`. -/
theorem exists_isLE_derivedDual (X : Scheme.{u}) [CompactSpace X]
    (K : DerivedCategory X.Modules)
    (hK : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) K) :
    ∃ b : ℤ, (Stacks.SheafOfModules.derivedDual X.sheaf K).IsLE b :=
  Stacks.AlgebraicGeometry.PerfectCohomology.exists_isLE_of_isPerfect X _
    (isPerfect_derivedDual X K hK)

end Stacks.DerivedQCoh

end
