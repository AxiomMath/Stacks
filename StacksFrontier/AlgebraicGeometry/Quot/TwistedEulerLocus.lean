module

public import StacksFrontier.AlgebraicGeometry.Quot.TwistedEulerCharacteristic
public import StacksFrontier.Topology.LocallyConstant.PolynomialFamilyLocus

/-!
# The locus of a prescribed Hilbert polynomial in a family of coherent sheaves

Let `(T, 𝓕)` be an object of `Coh_{X/B}` and `L` an invertible `𝒪_X`-module.  The locus of points
`t ∈ T` at which `n ↦ χ(X_t, 𝓕_t ⊗ L_t^{⊗ n})` is a prescribed function `P` is open and closed as
soon as each `t ↦ χ(X_t, 𝓕_t ⊗ L_t^{⊗ n})` is locally constant and the functions
`n ↦ χ(X_t, 𝓕_t ⊗ L_t^{⊗ n})` are polynomials whose degree is bounded by a locally bounded
function of `t`.  This is the step of the source (Stacks 0DNE for `E_i = L^{⊗ i}`, and so the
case `E_i = L^{⊗ i}` of Stacks 0DPG and 0DPQ) at which infinitely many conditions are reduced to
finitely many near every point.

## Main results

* `AlgebraicGeometry.Space.CoherentObject.isClopen_setOf_twistedEuler_eq`: the locus of a
  prescribed Hilbert polynomial is open and closed, given local constancy of the twisted Euler
  characteristics and a locally bounded bound on their degrees.

## Implementation notes

The two inputs are hypotheses of this reduction lemma, which is not a registration.  Local
constancy of `t ↦ χ(X_t, 𝓕_t ⊗ L_t^{⊗ n})` is the instance of Stacks 0D1Z for the perfect object
`Rf_{T,*}(𝓕 ⊗ L_T^{⊗ n})` of Stacks 0A1P.  That `n ↦ χ(X_t, 𝓕_t ⊗ L_t^{⊗ n})` is a polynomial of
degree at most the dimension of the support of `𝓕_t` is the theorem of Snapper on the proper
fibre `X_t`; over a scheme the dimensions of the fibres of a quasi-compact morphism locally of
finite type are locally bounded by
`AlgebraicGeometry.exists_mem_nhds_topologicalKrullDim_fiber_le`.

## References

* [Stacks Project, Tag 0DNE](https://stacks.math.columbia.edu/tag/0DNE)
* [Stacks Project, Tag 0DNF](https://stacks.math.columbia.edu/tag/0DNF)
* [Stacks Project, Tag 0DPQ](https://stacks.math.columbia.edu/tag/0DPQ)
-/

@[expose] public noncomputable section

open Topology

universe u

namespace AlgebraicGeometry.Space.CoherentObject

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {D : CoherentSituation B S hS}

/-- **The locus of a prescribed Hilbert polynomial in a family of coherent sheaves is open and
closed**, given that each twisted Euler characteristic `t ↦ χ(X_t, 𝓕_t ⊗ L_t^{⊗ n})` is locally
constant and that `n ↦ χ(X_t, 𝓕_t ⊗ L_t^{⊗ n})` is a polynomial of degree at most `δ t` for a
locally bounded `δ`. -/
theorem isClopen_setOf_twistedEuler_eq (L : Modules.{u, u} B S hS D.X.1 D.X.2)
    [Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS D.X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS D.X.1 D.X.2).O)).property L]
    (A : CoherentObject D)
    (hlc : ∀ n, IsLocallyConstant fun t : A.testScheme => twistedEuler L A t n)
    {δ : A.testScheme → ℕ} (hpoly : ∀ t, IsPolynomialOfDegreeLE (twistedEuler L A t) (δ t))
    (hδ : ∀ t, ∃ U ∈ 𝓝 t, ∃ d : ℕ, ∀ t' ∈ U, δ t' ≤ d) (P : ℤ → ℤ) :
    IsClopen {t : A.testScheme | ∀ n, twistedEuler L A t n = P n} :=
  isClopen_setOf_forall_eq_of_isPolynomialOfDegreeLE_of_locallyBounded hlc hpoly hδ P

end AlgebraicGeometry.Space.CoherentObject

end
