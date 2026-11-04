module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Duality.DualizingModuleOverField

/-!
# The dualizing module `H^{-dim(X)}(ω_X^•)` of a complex

The convention of [Stacks, Tag 0AWJ] calls `ω_X = H^{-dim(X)}(ω_X^•)` the dualizing module of
`X`, for `ω_X^•` the complex normalized relative to `k[0]`. The definition only reads off one
cohomology sheaf of the complex, so it is stated here for an arbitrary complex `K` in `D(𝒪_X)`.
Over a field and for `X` separated, it agrees with `Stacks.Duality.normalizedDualizingModule` at
`f^!𝒪_{Spec(k)}`.

## Main definitions

* `Stacks.Duality.normalizedDualizingModuleOfComplex` — `H^{-dim(X)}(K)` for `K ∈ D(𝒪_X)`.

## References

* [Stacks Project, Tag 0AWJ](https://stacks.math.columbia.edu/tag/0AWJ)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u w

namespace Stacks.Duality

section Module

variable {X : Scheme.{u}}

/-- **The dualizing module `ω_X = H^{-dim(X)}(ω_X^•)`** of [Stacks, Tag 0AWJ]: the cohomology
sheaf in degree minus the dimension of `X` of a complex `ω_X^•`, which the example takes to be
the complex normalized relative to `k[0]`. Over a field this is the customary dualizing module
of an equidimensional scheme of finite type over `k`. -/
def normalizedDualizingModuleOfComplex (K : DerivedCategory X.Modules) : X.Modules :=
  (DerivedCategory.homologyFunctor X.Modules
    (-(ENat.toNat ((topologicalKrullDim X).getD 0) : ℤ))).obj K

end Module

section Field

variable {k : Type u} [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
  (A : UpperShriek fun X : Scheme.{u} => DerivedCategory X.Modules)
  [IsSeparated p] [LocallyOfFiniteType p] [QuasiCompact p]

/-- The dualizing module of the complex normalized relative to `k[0]` is the dualizing module of
`Stacks.Duality.normalizedDualizingModule`. -/
theorem normalizedDualizingModuleOfComplex_normalizedUpperShriekOverField {ι : Type w}
    (𝒰 : SeparatedCovering p ι) :
    normalizedDualizingModuleOfComplex (normalizedUpperShriekOverField p A 𝒰).complex =
      normalizedDualizingModule (normalizedUpperShriekOverField p A 𝒰) :=
  rfl

end Field

end Stacks.Duality

end
