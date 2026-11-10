module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.AdicQuotientSystem
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.IdealPowerQuasicoherent
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.LimitSections
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.NeighbourhoodHoms
public import StacksFrontier.AlgebraicGeometry.QuasicoherentBasicOpen.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# The affine sections of `lim ℱ/𝓘ⁿℱ` are the adic completion of the sections

Let `X` be a locally Noetherian scheme, `𝓘 ⊂ 𝒪_X` a quasi-coherent sheaf of ideals and `ℱ` a
coherent `𝒪_X`-module. Over an affine open `U`, with `A = Γ(X, U)` and `I = 𝓘(U)`,

`Γ(U, lim ℱ/𝓘ⁿℱ) = lim Γ(ℱ, U)/Iⁿ Γ(ℱ, U)`,

the right-hand side being Mathlib's `AdicCompletion I Γ(ℱ, U)`.

This is the affine-section computation of the object both part (2) and part (3) of
[Stacks, Tag 0A0K] name, read at the tower `Stacks.Algebraization.adicQuotientSystem` those parts
are stated over, rather than at the shifted tower `n ↦ ℱ/𝓘ⁿ⁺¹ℱ` of
`Stacks.Algebraization.completionFunctor`.

## What this composes

Both halves were already available and only the composition was missing:

* `Stacks.Algebraization.completionSectionsEquiv` computes the affine sections of the limit of the
  *shifted* tower, which is the indexing `Stacks.Algebraization.completionFunctor` uses;
* `Stacks.Algebraization.NeighbourhoodHoms.adicCompletionLimitIso` identifies the limit of the
  shifted tower with the limit of `Stacks.Algebraization.adicQuotientSystem` — shifting a tower
  indexed by `ℕᵒᵖ` does not change its limit, the level-zero leg of a cone being determined by the
  level-one leg.

## Main results

* `Stacks.Algebraization.adicQuotientLimitSectionsEquiv` — the identification above.
* `Stacks.Algebraization.adicQuotientLimitComparison` — the canonical map
  `ℱ ⟶ lim ℱ/𝓘ⁿℱ` of modules on `X`, in the indexing of
  `Stacks.Algebraization.adicQuotientSystem`, and
  `Stacks.Algebraization.adicQuotientLimitSectionsEquiv_of`, which says that the identification
  above carries the completion map of `Γ(ℱ, U)` to the sections of that canonical map over `U`.

  This is what makes the identification *natural in the affine open* without any statement about
  two opens being proved: the completion map `Γ(ℱ, U) ⟶ Γ(U, lim ℱ/𝓘ⁿℱ)` is the component at `U`
  of a morphism of sheaves, so its compatibility with restriction is that morphism's own
  naturality. The corresponding statement for the shifted tower is
  `Stacks.Algebraization.completionSectionsEquiv_of`.

## References

* [Stacks Project, Tag 0A0K](https://stacks.math.columbia.edu/tag/0A0K)
* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.Algebraization

/-! The module structures on sections are `local instance`s of
`Completion/IdealPowerQuasicoherent.lean`; they are reactivated here rather than restated. -/

attribute [local instance] sectionsModuleΓ sectionsModuleΓSheaf sectionsSMulCommClassΓ
  monoSubmoduleι sectionsModuleΓPresheaf sectionsModuleΓSheafPresheaf sectionsModuleΓSheafVal

/-- **The affine sections of the limit of the adic quotient tower are the adic completion of the
sections.** For a coherent module `ℱ` on a locally Noetherian scheme, an arbitrary quasi-coherent
sheaf of ideals `𝓘` and an affine open `U`, with `A = Γ(X, U)` and `I = 𝓘(U)`,

`Γ(U, lim ℱ/𝓘ⁿℱ) ≅ AdicCompletion I Γ(ℱ, U)`.

`Stacks.Algebraization.completionSectionsEquiv` is this statement for the shifted tower
`n ↦ ℱ/𝓘ⁿ⁺¹ℱ`, and
`Stacks.Algebraization.NeighbourhoodHoms.adicCompletionLimitIso` identifies the two limits. -/
public def adicQuotientLimitSectionsEquiv (X : Scheme.{u}) [IsLocallyNoetherian X]
    (I : X.IdealSheafData)
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (U : X.affineOpens) :
    AdicCompletion (I.ideal U) Γ(F.obj, U) ≃ₗ[Γ(X, U)]
      Γ((show X.Modules from limit (C := X.Modules) (adicQuotientSystem I F.obj)), U.1) :=
  (completionSectionsEquiv X I F U).trans
    (AlgebraicGeometry.sectionsLinearEquivOfIso
      (NeighbourhoodHoms.adicCompletionLimitIso I F) U.1).symm

/-- **The canonical map `ℱ ⟶ lim ℱ/𝓘ⁿℱ`**, in the indexing of
`Stacks.Algebraization.adicQuotientSystem`. It is the canonical map
`Stacks.Algebraization.completionToLimit` into the limit of the shifted tower, read through
`Stacks.Algebraization.NeighbourhoodHoms.adicCompletionLimitIso`. -/
public def adicQuotientLimitComparison (X : Scheme.{u}) [IsLocallyNoetherian X]
    (I : X.IdealSheafData)
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) :
    F.obj ⟶ (show X.Modules from limit (C := X.Modules) (adicQuotientSystem I F.obj)) :=
  completionToLimit X I F ≫ (NeighbourhoodHoms.adicCompletionLimitIso I F).inv

/-- **The affine-sections identification carries the completion map to the sections of the
canonical map `ℱ ⟶ lim ℱ/𝓘ⁿℱ`.** This is
`Stacks.Algebraization.completionSectionsEquiv_of` read through
`Stacks.Algebraization.NeighbourhoodHoms.adicCompletionLimitIso`.

The point of the statement is that the right-hand side is the component at `U` of a morphism of
sheaves on `X`, so it commutes with restriction to a smaller affine open by that morphism's
naturality; the left-hand side mentions only data attached to `U`. -/
public theorem adicQuotientLimitSectionsEquiv_of (X : Scheme.{u}) [IsLocallyNoetherian X]
    (I : X.IdealSheafData)
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (U : X.affineOpens)
    (s : Γ(F.obj, U)) :
    adicQuotientLimitSectionsEquiv X I F U (AdicCompletion.of (I.ideal U) Γ(F.obj, U) s) =
      Scheme.Modules.Hom.app (adicQuotientLimitComparison X I F) U.1 s := by
  change (AlgebraicGeometry.sectionsLinearEquivOfIso
      (NeighbourhoodHoms.adicCompletionLimitIso I F) U.1).symm
      (completionSectionsEquiv X I F U (AdicCompletion.of (I.ideal U) Γ(F.obj, U) s)) = _
  rw [completionSectionsEquiv_of]
  rfl

end Stacks.Algebraization

end
