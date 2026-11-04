module

public import Mathlib.CategoryTheory.Abelian.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.TensorCanonicalSection

/-!
# Factoring the action of the ideal sheaf of a divisor through a submodule

Let `X` be a scheme, `D ⊆ X` an effective Cartier divisor with ideal sheaf `ℐ_D` and invertible
sheaf `𝒪_X(D)`, and let `λ : F ⟶ G` be a morphism of `𝒪_X`-modules. The ideal sheaf acts on `G`
through

`ℐ_D ⊗_{𝒪_X} G ⟶ 𝒪_X ⊗_{𝒪_X} G ≅ G`,

and the hypothesis of interest is that this action *lands in `F`*: the composite of the action
with `G ⟶ coker λ` vanishes. When `λ` is a monomorphism this is exactly the condition
`ℐ_D · G ⊆ F`, and it makes the action factor through `λ`.

## Main definitions

* `Stacks.Divisors.idealAction`: the action `ℐ_D ⊗_{𝒪_X} G ⟶ G` of the ideal sheaf on an
  `𝒪_X`-module.
* `Stacks.Divisors.idealActionFactor`: the factorisation `ℐ_D ⊗_{𝒪_X} G ⟶ F` of that action
  through a monomorphism `λ : F ⟶ G` killing it modulo `λ`.

## Main results

* `Stacks.Divisors.idealActionFactor_comp`: the factorisation does factor the action, i.e.
  `idealActionFactor ≫ λ = idealAction`.

## Implementation notes

The category `X.Modules` of `𝒪_X`-modules is abelian, so a monomorphism is the kernel of its
own cokernel (`CategoryTheory.Abelian.monoIsKernelOfCokernel`). Mathlib packages the resulting
factorisation as `CategoryTheory.Abelian.monoLift`, which takes exactly the vanishing hypothesis
`idealAction D G ≫ cokernel.π λ = 0` and returns a morphism, not merely its existence; the
factorisation here is that morphism, so it is a construction and not a choice. No geometry
enters: the statements of this file are about an arbitrary morphism of `𝒪_X`-modules and the
ideal sheaf of an arbitrary closed subscheme, with effectivity of the divisor nowhere used.

The ideal sheaf `ℐ_D` lives at the index `Stacks.SheafOfModules.TensorStalkRingedSpace`
`.structureSheafRing X.toRingedSpace`, while `AlgebraicGeometry.Scheme.Modules` is written over
`X.ringCatSheaf`; the two sheaves of rings are equal by `rfl`, so the ideal sheaf is an object of
`X.Modules` with no transport, exactly as in
`StacksFrontier/AlgebraicGeometry/Divisors/TensorCanonicalSection.lean`.

## References

* [Stacks Project, Tag 01WX](https://stacks.math.columbia.edu/tag/01WX)
* [Stacks Project, Tag 0G5G](https://stacks.math.columbia.edu/tag/0G5G)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Stacks.Divisors

variable {X : Scheme.{u}}

/-- The inclusion `ℐ_D ⟶ 𝒪_X` of the ideal sheaf of a closed subscheme `D ⊆ X`, read as a
morphism of `X.Modules`. -/
abbrev idealSheafInclusion (D : X.IdealSheafData) :
    negativeTwist' D ⟶ SheafOfModules.unit X.ringCatSheaf :=
  Stacks.ClosedImmersion.idealSheafι D.subschemeι.toLRSHom.toShHom

/-- **The action of the ideal sheaf of `D` on an `𝒪_X`-module `G`**: the ideal inclusion
tensored with `G`, followed by the left unit constraint, so
`ℐ_D ⊗_{𝒪_X} G ⟶ 𝒪_X ⊗_{𝒪_X} G ≅ G`. Its image is the product `ℐ_D · G`. -/
def idealAction (D : X.IdealSheafData) (G : X.Modules) :
    Scheme.Modules.tensorObj (negativeTwist' D) G ⟶ G :=
  Scheme.Modules.tensorRightMap (idealSheafInclusion D) G ≫
    (Stacks.SheafOfModules.Invertible.tensorProductLeftUnitor X.sheaf.obj
      X.ringCatSheaf.property G).hom

/-- **The factorisation of the action of `ℐ_D` through a submodule.** If `λ : F ⟶ G` is a
monomorphism of `𝒪_X`-modules and the action of `ℐ_D` on `G` dies in `coker λ` — that is,
`ℐ_D · G ⊆ F` — then the action factors through `λ`, and this is the factorisation.

The category `X.Modules` is abelian, so `λ` is the kernel of `cokernel.π λ`
(`CategoryTheory.Abelian.monoIsKernelOfCokernel`) and the factorisation is the induced map into
that kernel. -/
def idealActionFactor (D : X.IdealSheafData) {F G : X.Modules} (lam : F ⟶ G) [Mono lam]
    (hlam : idealAction D G ≫ cokernel.π lam = 0) :
    Scheme.Modules.tensorObj (negativeTwist' D) G ⟶ F :=
  Abelian.monoLift lam (idealAction D G) hlam

/-- **The factorisation of `Stacks.Divisors.idealActionFactor` does factor the action of
`ℐ_D`.** -/
@[reassoc (attr := simp)]
theorem idealActionFactor_comp (D : X.IdealSheafData) {F G : X.Modules} (lam : F ⟶ G) [Mono lam]
    (hlam : idealAction D G ≫ cokernel.π lam = 0) :
    idealActionFactor D lam hlam ≫ lam = idealAction D G :=
  Abelian.monoLift_comp lam (idealAction D G) hlam

end Stacks.Divisors

end
