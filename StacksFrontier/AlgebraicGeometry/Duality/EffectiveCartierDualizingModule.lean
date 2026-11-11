module

public import StacksFrontier.AlgebraicGeometry.Coherent.HomColimit.IdealPowTensorIso
public import StacksFrontier.AlgebraicGeometry.Duality.DivisorSheafTwistDualizing
public import StacksFrontier.AlgebraicGeometry.Duality.EffectiveCartierAdjunctionModule
public import StacksFrontier.AlgebraicGeometry.Duality.EffectiveCartierPullbackDualizing
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.Invertible
import StacksCore.Tactic.StacksAttribute

/-!
# The dualizing module of an effective Cartier divisor

Let `X` be a locally Noetherian scheme, let `D ⊆ X` be an effective Cartier divisor with closed
immersion `i : D ⟶ X` and normal sheaf `𝒩 = i^* 𝒪_X(D)`, and let `ω` be a quasi-coherent
`𝒪_X`-module which placed in some cohomological degree is a dualizing complex on `X`. Write
`a(-)` for the right adjoint of derived pushforward along `i` of
[Stacks, Tag 0A76](https://stacks.math.columbia.edu/tag/0A76). This file proves that

`𝒩 ⊗_{𝒪_D} i^*ω`, equivalently `H¹(a(ω))`, is a dualizing module on `D`.

For the inclusion of an effective Cartier divisor, clause (7) of [Stacks, Tag 0AU3] identifies
`i^!` with `Li^*(-) ⊗_{𝒪_D} 𝒩[-1]`, so for a module `ω` the degree-one cohomology of `i^!ω` is
`𝒩 ⊗ i^*ω`; clause (4)(a) of the same tag, which is [Stacks, Tag 0AA3], is the assertion that
`i^!` of a dualizing complex is dualizing. The statements below are that assertion for the
inclusion of an effective Cartier divisor, read on a module.

## Main results

* `Stacks.Divisors.isDualizingModule_normalTensorPullback` — `𝒩 ⊗ i^*ω` is a dualizing module
  on `D`.
* `Stacks.Divisors.isDualizingModule_homologyOne_derivedSheafHomExactSupport` — the same for
  `H¹(a(ω))`, which is the shape a consumer that defines the dualizing module of the divisor as
  the normalization of [Stacks, Remark 0B4R] needs.

## The proof

`Stacks.Divisors.isDualizingModule_pullback` says that the pullback along `i` of a module which
is dualizing on `X` is dualizing on `D`. Applied to `𝒪_X(D) ⊗ ω`, which is dualizing on `X` by
`Stacks.Duality.isDualizingComplex_single_divisorSheaf_tensor`, it gives the first statement,
because pullback is monoidal (`Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso`) so that
`i^*(𝒪_X(D) ⊗ ω) ≅ 𝒩 ⊗ i^*ω`. The second follows by transport along the module-level adjunction
formula `Stacks.Divisors.nonempty_homologyOne_derivedSheafHomExactSupport_iso`, which identifies
`H¹(a(ω))` with `𝒩 ⊗ i^*ω` for every module `ω` whatsoever.

## References

* [Stacks Project, Tag 0AA3](https://stacks.math.columbia.edu/tag/0AA3)
* [Stacks Project, Tag 0AU3](https://stacks.math.columbia.edu/tag/0AU3)
* [Stacks Project, Tag 0AA4](https://stacks.math.columbia.edu/tag/0AA4)
* [Stacks Project, Tag 0A76](https://stacks.math.columbia.edu/tag/0A76)
* [Stacks Project, Tag 0B4R](https://stacks.math.columbia.edu/tag/0B4R)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory RingedSpaceModuleAdjunction

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Stacks.Divisors

variable {X : Scheme.{u}} [IsLocallyNoetherian X] (D : X.IdealSheafData)
  [IsEffectiveCartierDivisor D]

/-- **The normal sheaf twist of the restriction of a dualizing module is a dualizing module.**
For an effective Cartier divisor `D ⊆ X` with closed immersion `i` and normal sheaf
`𝒩 = i^*𝒪_X(D)`, and for a quasi-coherent `𝒪_X`-module `ω` which placed in degree `n` is a
dualizing complex on `X`, the `𝒪_D`-module `𝒩 ⊗ i^*ω` is a dualizing module on `D`.

This is clause (4)(a) of [Stacks, Tag 0AU3] for the inclusion of an effective Cartier divisor,
read on a module through clause (7) of the same tag. -/
theorem isDualizingModule_normalTensorPullback (ω : X.Modules) [ω.IsQuasicoherent] (n : ℤ)
    (hω : Stacks.Duality.IsDualizingComplex
      ((DerivedCategory.singleFunctor X.Modules n).obj ω)) :
    letI : IsLocallyNoetherian D.subscheme := D.isLocallyNoetherian_subscheme
    Stacks.Duality.IsDualizingModule
      (((Stacks.SheafOfModules.Tensor.sheafTensor
            (Stacks.SheafOfModules.ringedSite D.subscheme.sheaf).O).obj
          ((Scheme.Modules.pullback D.subschemeι).obj (divisorSheaf D))).obj
        ((Scheme.Modules.pullback D.subschemeι).obj ω)) := by
  let : IsLocallyNoetherian D.subscheme := D.isLocallyNoetherian_subscheme
  have h1 : (divisorSheaf D).IsQuasicoherent := inferInstance
  have h2 : ω.IsQuasicoherent := inferInstance
  exact Stacks.Duality.isDualizingModule_of_iso
    (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso D.subschemeι (divisorSheaf D) ω)
    (@isDualizingModule_pullback X _ D _ _
      (@AlgebraicGeometry.tensorSheaf_isQuasicoherent X.toRingedSpace (divisorSheaf D) ω h1 h2)
      0 (Stacks.Duality.isDualizingComplex_single_divisorSheaf_tensor D ω n hω))

/-- **[Stacks, Tag 0AA3] for the inclusion of an effective Cartier divisor, read on a module.**
Let `D ⊆ X` be an effective Cartier divisor on a locally Noetherian scheme, with closed immersion
`i : D ⟶ X`, and let `a(-)` be the right adjoint of derived pushforward along `i` of
[Stacks, Tag 0A76]. If a quasi-coherent `𝒪_X`-module `ω` placed in some degree is a dualizing
complex on `X`, then the `𝒪_D`-module `H¹(a(ω))` is a dualizing module on `D`.

Degree one is the degree [Stacks, Remark 0B4R] selects, and
`Stacks.Divisors.nonempty_homologyOne_derivedSheafHomExactSupport_iso` identifies `H¹(a(ω))` with
the normal sheaf twist `𝒩 ⊗ i^*ω` of the restriction.

This special case carries no `@[stacks]` attribute: clause (4)(a) of [Stacks, Section 0AU3] in
general is `Stacks.Duality.isDualizingComplex_upperShriek_obj` ([Stacks, Tag 0AA3]). -/
theorem isDualizingModule_homologyOne_derivedSheafHomExactSupport (ω : X.Modules)
    [ω.IsQuasicoherent] (n : ℤ) (hω : Stacks.Duality.IsDualizingComplex
      ((DerivedCategory.singleFunctor X.Modules n).obj ω)) :
    letI : IsLocallyNoetherian D.subscheme := D.isLocallyNoetherian_subscheme
    Stacks.Duality.IsDualizingModule
      ((DerivedCategory.homologyFunctor D.subscheme.Modules 1).obj
        ((closedQuotient D).derivedSheafHomExactSupport.obj
          ((DerivedCategory.singleFunctor X.Modules 0).obj ω))) := by
  let : IsLocallyNoetherian D.subscheme := D.isLocallyNoetherian_subscheme
  obtain ⟨e⟩ := nonempty_homologyOne_derivedSheafHomExactSupport_iso D ω
  exact Stacks.Duality.isDualizingModule_of_iso e.symm
    (isDualizingModule_normalTensorPullback D ω n hω)

end Stacks.Divisors

end
