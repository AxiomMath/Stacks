module

public import StacksFrontier.Deformation.Examples.Geometric.SpacesInfinitesimalAutomorphismsDerivations
public import StacksFrontier.Deformation.Examples.Geometric.SpacesFiniteDimensionalExt

/-!
# `Der_k(𝒪_X, 𝒪_X)` is finite dimensional for a proper algebraic space

In the situation of Stacks 0E3Z, let `X` be an algebraic space over the residue field `k`.  The
derivations `Der_k(𝒪_X, 𝒪_X)` (`Deformation.Examples.SpaceDerivations` at the structure morphism
`X ⟶ Spec k`) form a `k`-vector space, `c` acting by multiplication by the function
`spaceResidueFieldRingHom c` on `X` (`AlgebraicGeometry.Space.derivationModuleOfRingHom`).
Postcomposition with the universal derivation of Stacks 04CT is a `k`-linear isomorphism
`Hom_{𝒪_X}(Ω_{X/k}, 𝒪_X) ≃ Der_k(𝒪_X, 𝒪_X)`
(`AlgebraicGeometry.Space.differentialsHomLinearEquiv`, Stacks 0E41), so for `X` proper over
`k` the derivations form a finite-dimensional vector space, by the finiteness of
`Hom_{𝒪_X}(Ω_{X/k}, 𝒪_X)` (`Deformation.Examples.moduleFinite_spaceDifferentialsHom`, from
Stacks 0D0Z and 0D0T).

## Main results

* `Deformation.Examples.finiteDimensional_spaceDerivations`: finite dimensionality for `X` proper
  over `k`.

## References

* [Stacks Project, Tag 0E42](https://stacks.math.columbia.edu/tag/0E42)
* [Stacks Project, Tag 0E41](https://stacks.math.columbia.edu/tag/0E41)
* [Stacks Project, Tag 04CT](https://stacks.math.columbia.edu/tag/04CT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open Stacks.Cohomology.SiteModules

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.DerivedTensor.ResolutionByExtensionsByZero.instAbelian

namespace Deformation.Examples

variable {Λ : Type u} {k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable (B : BigFppfSite.{u}) (hΛ : B.Contains (Spec (.of Λ)))
variable (hSpec : ∀ A : ArtinianLocalAlgCat.{u, u, u} Λ k, B.Contains (Spec (.of A)))
variable (X : (BigFppfOver B (Spec (.of Λ)) hΛ)ᵒᵖ ⥤ Type u)
  (hX : IsAlgebraicSpace B (Spec (.of Λ)) hΛ X)
  (toK : X ⟶ yoneda.obj (spaceBaseOver B hΛ hSpec (residueFieldBase Λ k)))

/-- **`Der_k(𝒪_X, 𝒪_X)` is finite dimensional for `X` proper over `k`**, `k` acting through
`Deformation.Examples.spaceResidueFieldRingHom`: by Stacks 0E41 it is
`Hom_{𝒪_X}(Ω_{X/k}, 𝒪_X)` as a `k`-vector space, which is finite dimensional by Stacks 0D0Z and
Stacks 0D0T (`Deformation.Examples.moduleFinite_spaceDifferentialsHom`). -/
theorem finiteDimensional_spaceDerivations (hproper : Space.IsProper B (Spec (.of Λ)) hΛ toK) :
    letI : Module k (SpaceDerivations B hΛ (spaceStructureMap B hΛ hSpec X hX toK)) :=
      Space.derivationModuleOfRingHom B (Spec (.of Λ)) hΛ (X := spaceOf B hΛ X hX)
        (spaceResidueFieldRingHom B hΛ hSpec X hX toK)
        (spaceStructureMap B hΛ hSpec X hX toK) (spaceStructureModule B hΛ (spaceOf B hΛ X hX))
    FiniteDimensional k (SpaceDerivations B hΛ (spaceStructureMap B hΛ hSpec X hX toK)) := by
  let := (Space.modulesLinearOfRingHom B (Spec (.of Λ)) hΛ (X := spaceOf B hΛ X hX)
    (spaceResidueFieldRingHom B hΛ hSpec X hX toK)).homModule
    (Space.sheafOfDifferentials B (Spec (.of Λ)) hΛ (spaceStructureMap B hΛ hSpec X hX toK))
    (spaceStructureModule B hΛ (spaceOf B hΛ X hX))
  let : Module k (SpaceDerivations B hΛ (spaceStructureMap B hΛ hSpec X hX toK)) :=
    Space.derivationModuleOfRingHom B (Spec (.of Λ)) hΛ (X := spaceOf B hΛ X hX)
      (spaceResidueFieldRingHom B hΛ hSpec X hX toK)
      (spaceStructureMap B hΛ hSpec X hX toK) (spaceStructureModule B hΛ (spaceOf B hΛ X hX))
  have h := moduleFinite_spaceDifferentialsHom B hΛ hSpec X hX toK hproper
  exact @Module.Finite.equiv k _ _ _ _ _ _ _ h (Space.differentialsHomLinearEquiv B (Spec (.of Λ))
    hΛ (X := spaceOf B hΛ X hX) (spaceResidueFieldRingHom B hΛ hSpec X hX toK)
    (spaceStructureMap B hΛ hSpec X hX toK) (spaceStructureModule B hΛ (spaceOf B hΛ X hX)))

end Deformation.Examples

end
