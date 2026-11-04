module

public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.FittingIdeals
public import StacksFrontier.AlgebraicGeometry.QuasicoherentBasicOpen.Basic

/-!
# Fitting ideal sheaves are an isomorphism invariant

Isomorphic quasi-coherent modules of finite type on a scheme have the same Fitting ideal
sheaves. This is the scheme-level counterpart of `fittingIdeal_eq_of_linearEquiv`, the
invariance of the module-theoretic Fitting ideal under a linear equivalence.

## Main results

* `AlgebraicGeometry.fittingIdeal_congr`: an isomorphism of quasi-coherent modules of finite
  type carries the `k`-th Fitting ideal sheaf of one to that of the other.
* `AlgebraicGeometry.fittingIdealOfNat_congr`: the same statement for the ℕ-indexed
  specialization.

## References

* [Stacks Project, Tag 0C3D](https://stacks.math.columbia.edu/tag/0C3D)
-/

@[expose] public section

noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- Isomorphic quasi-coherent modules of finite type on a scheme have equal `k`-th Fitting ideal
sheaves, for every integer `k`. -/
theorem fittingIdeal_congr {X : Scheme.{u}} {F G : X.Modules} [F.IsFiniteType]
    [F.IsQuasicoherent] [G.IsFiniteType] [G.IsQuasicoherent] (e : F ≅ G) (k : ℤ) :
    fittingIdeal F k = fittingIdeal G k :=
  fittingIdeal_eq_of_iso e k

/-- Isomorphic quasi-coherent modules of finite type on a scheme have equal `r`-th ℕ-indexed
Fitting ideal sheaves, for every natural number `r`. -/
theorem fittingIdealOfNat_congr {X : Scheme.{u}} {F G : X.Modules} [F.IsFiniteType]
    [F.IsQuasicoherent] [G.IsFiniteType] [G.IsQuasicoherent] (e : F ≅ G) (r : ℕ) :
    fittingIdealOfNat F r = fittingIdealOfNat G r :=
  fittingIdeal_congr e (r : ℤ)

end AlgebraicGeometry

end

end
