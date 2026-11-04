module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.KrullDimension
public import Mathlib.RingTheory.Spectrum.Prime.Topology
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Affine opens read through their rings of functions

An affine open `U` of a scheme `X` is homeomorphic to the spectrum of `Γ(X, U)`
(`AlgebraicGeometry.IsAffineOpen.isoSpec`). Consequently its Krull dimension is the Krull
dimension of `Γ(X, U)`, it is irreducible when `Γ(X, U)` is a domain, and it is a reduced scheme
when `Γ(X, U)` is reduced.

## Main results

* `AlgebraicGeometry.IsAffineOpen.topologicalKrullDim_eq`: `dim U = dim Γ(X, U)`.
* `AlgebraicGeometry.IsAffineOpen.irreducibleSpace`: `U` is irreducible if `Γ(X, U)` is a domain.
* `AlgebraicGeometry.IsAffineOpen.isReduced`: `U` is reduced if `Γ(X, U)` is reduced.
-/

@[expose] public section

namespace AlgebraicGeometry

/-- **The Krull dimension of an affine open is that of its ring of functions.** -/
theorem IsAffineOpen.topologicalKrullDim_eq {X : Scheme} {U : X.Opens} (hU : IsAffineOpen U) :
    topologicalKrullDim U = ringKrullDim Γ(X, U) := by
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact IsHomeomorph.topologicalKrullDim_eq _ hU.isoSpec.hom.homeomorph.isHomeomorph

/-- An affine open whose ring of functions is a domain is irreducible. -/
theorem IsAffineOpen.irreducibleSpace {X : Scheme} {U : X.Opens} (hU : IsAffineOpen U)
    [IsDomain Γ(X, U)] : IrreducibleSpace U :=
  (hU.isoSpec.hom.homeomorph.irreducibleSpace_iff).mpr inferInstance

/-- An affine open whose ring of functions is reduced is a reduced scheme. -/
@[ega "I 5.1.4" "partial"]
theorem IsAffineOpen.isReduced {X : Scheme} {U : X.Opens} (hU : IsAffineOpen U)
    [_root_.IsReduced Γ(X, U)] : IsReduced U.toScheme :=
  isReduced_of_isOpenImmersion hU.isoSpec.hom

end AlgebraicGeometry
