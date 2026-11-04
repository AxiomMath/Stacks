module

public import StacksFrontier.AlgebraicGeometry.Quot.NumericalDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedFibreEulerLocallyConstant

/-!
# Local constancy of the numerical invariants of a coherent family

Let `(T, 𝓕)` be an object of `Coh_{X/B}` and `i ∈ I`.  Stacks 0DNC asserts that the function
`χ_i : |T| → ℤ`, `t ↦ χ(K_i ⊗^𝐋 κ(t))`, is locally constant, by two citations: `K_i` is a perfect
object of `D(𝒪_T)` (Stacks 0A1P) and the derived-fibre Euler characteristic of a perfect object
is locally constant (Stacks 0D1Z).  This file carries out the second step: once `K_i` is
perfect, `χ_i` is locally constant.

## Main results

* `AlgebraicGeometry.Space.NumericalSituation.isLocallyConstant_numericalEuler_of_isPerfect`:
  `χ_i` is locally constant on `|T|` as soon as `K_i` is perfect.

## Implementation notes

`χ_i` is `AlgebraicGeometry.Space.NumericalSituation.numericalEuler`, the derived-fibre Euler
characteristic `AlgebraicGeometry.Space.derivedFibreEuler` of `K_i` on the algebraic space
represented by `T`, so the statement is Stacks 0D1Z
(`AlgebraicGeometry.Space.isLocallyConstant_derivedFibreEuler`) at `K_i`.  The perfectness of
`K_i` is the hypothesis; it is the content of Stacks 0A1P, a result about the derived direct
image of a derived tensor product along a morphism of finite presentation, which this file does
not prove.

## References

* [Stacks Project, Tag 0DNC](https://stacks.math.columbia.edu/tag/0DNC)
* [Stacks Project, Tag 0D1Z](https://stacks.math.columbia.edu/tag/0D1Z)
* [Stacks Project, Tag 0A1P](https://stacks.math.columbia.edu/tag/0A1P)
-/

/- This reduction is deliberately not registered under 0DNC.
Its one remaining input is perfectness of `K_i` (Stacks 0A1P); given that, this gives local
constancy of `χ_i` unconditionally. -/

@[expose] public noncomputable section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
/- The standard model is forced by the base
`AlgebraicGeometry.Space.smallEtaleDerivedModulePullback`. -/
attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {D : CoherentSituation B S hS}

namespace NumericalSituation

variable (N : NumericalSituation.{u, v, u} B S hS D) (A : CoherentObject D)

/-- **The functions `χ_i` of a perfect `K_i` are locally constant.**  For an object `(T, 𝓕)` of
`Coh_{X/B}` and `i ∈ I`, if `K_i = Rf_{T,*}(E_{i,T} ⊗^𝐋 𝓕)` is a perfect object of `D(𝒪_T)` then
`χ_i : |T| → ℤ` is locally constant.  This is Stacks 0D1Z applied to `K_i`. -/
theorem isLocallyConstant_numericalEuler_of_isPerfect (i : N.I)
    (hK : (smallEtaleRingedSite B S hS (testSpace A).1 (testSpace A).2).IsPerfect
      (N.numericalDirectImage A i)) :
    IsLocallyConstant (N.numericalEuler A i) :=
  isLocallyConstant_derivedFibreEuler B S hS (testSpace A) (N.numericalDirectImage A i) hK

end NumericalSituation

end AlgebraicGeometry.Space

end
