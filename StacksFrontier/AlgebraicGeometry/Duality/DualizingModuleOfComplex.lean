module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.CoherentCohomology

/-!
# The dualizing module of a dualizing complex

Let `X` be a Noetherian scheme with a dualizing complex `K` ([Stacks, Tag 0A87], here
`Stacks.Duality.IsDualizingComplex`), and let `n` be the least cohomological degree in which `K`
has nonvanishing cohomology. The cohomology sheaf `H^n(K)` is then the *dualizing module* `ω_X`
of [Stacks, Section 48.22]; it depends on the choice of `K` up to tensoring by an invertible
module. This file records that relation between a sheaf of modules and a dualizing complex and
proves that a dualizing module is coherent.

## Main definitions

* `Stacks.Duality.IsDualizingModuleOf` — `ω` is the dualizing module of the dualizing complex `K`,
  realized in the leftmost degree `n` in which `K` has nonvanishing cohomology.

## Main results

* `Stacks.Duality.IsDualizingModuleOf.isCoherent` — a dualizing module on a connected Noetherian
  scheme is a coherent `𝒪_X`-module.
* `Stacks.Duality.IsDualizingModuleOf.stacksIsCoherent` — the same conclusion for the coherence
  predicate `Stacks.SheafOfModules.IsCoherent`.

## References

* [Stacks Project, Tag 0AWK](https://stacks.math.columbia.edu/tag/0AWK)
* [Stacks Project, Tag 0A87](https://stacks.math.columbia.edu/tag/0A87)
* [Stacks Project, Tag 0A7B](https://stacks.math.columbia.edu/tag/0A7B)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u w

namespace Stacks.Duality

/-- `ω` is a **dualizing module** on a locally Noetherian scheme `X`, realized by the dualizing
complex `K` in degree `n`: the degree `n` is the least one in which `K` has nonvanishing
cohomology, and `ω` is the cohomology sheaf of `K` in that degree. -/
structure IsDualizingModuleOf {X : Scheme.{u}} [IsLocallyNoetherian X]
    [HasDerivedCategory.{w} X.Modules] (ω : X.Modules) (K : DerivedCategory X.Modules)
    (n : ℤ) : Prop where
  /-- `K` is a dualizing complex on `X`. -/
  isDualizingComplex : IsDualizingComplex K
  /-- The cohomology of `K` in degree `n` is nonzero. -/
  nonzero : ¬ IsZero ((DerivedCategory.homologyFunctor X.Modules n).obj K)
  /-- The cohomology of `K` vanishes in every degree below `n`. -/
  isZero_of_lt : ∀ i < n, IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj K)
  /-- `ω` is the cohomology sheaf of `K` in degree `n`. -/
  eq_homology : ω = (DerivedCategory.homologyFunctor X.Modules n).obj K

/-- A dualizing module on a connected Noetherian scheme is a coherent `𝒪_X`-module: it is a
cohomology sheaf of a dualizing complex, and those are coherent. -/
@[stacks 0AWK "coherence"]
theorem IsDualizingModuleOf.isCoherent {X : Scheme.{u}} [IsNoetherian X] [ConnectedSpace X]
    [HasDerivedCategory.{w} X.Modules] {ω : X.Modules} {K : DerivedCategory X.Modules} {n : ℤ}
    (h : IsDualizingModuleOf ω K n) : _root_.SheafOfModules.IsCoherent ω := by
  rw [h.eq_homology]
  exact isCoherent_homology_of_isDualizingComplex h.isDualizingComplex n

/-- A dualizing module on a connected Noetherian scheme is coherent in the sense of
`Stacks.SheafOfModules.IsCoherent`. -/
theorem IsDualizingModuleOf.stacksIsCoherent {X : Scheme.{u}} [IsNoetherian X] [ConnectedSpace X]
    [HasDerivedCategory.{w} X.Modules] {ω : X.Modules} {K : DerivedCategory X.Modules} {n : ℤ}
    (h : IsDualizingModuleOf ω K n) : _root_.Stacks.SheafOfModules.IsCoherent ω := by
  rw [h.eq_homology]
  exact stacksIsCoherent_homology_of_isDualizingComplex h.isDualizingComplex n

end Stacks.Duality

end
