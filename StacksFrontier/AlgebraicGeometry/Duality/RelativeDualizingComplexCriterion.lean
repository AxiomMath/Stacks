module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplex
public import StacksFrontier.AlgebraicGeometry.Modules.DerivedAlgebraUnitSection
public import StacksFrontier.CategoryTheory.CurriedActionIsIso
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.CompositionApplicationLawGeneral
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.CompositionApplicationLawNaturality

/-!
# A criterion for the second condition of a relative dualizing complex

Let `W ⊆ X ×_S X` be an open through which the diagonal factors as a closed immersion
`Δ : X ⟶ W` and let `E` be an object of `D(𝒪_W)`. If `Hom(Δ_*𝒪_X, E)` is free of rank one over
the commutative ring `End(Δ_*𝒪_X)` on a generator `θ`, and `R𝓗om(Δ_*𝒪_X, E)` is abstractly
isomorphic to `Δ_*𝒪_X`, then the map `Δ_*𝒪_X ⟶ R𝓗om(Δ_*𝒪_X, E)` that `θ` defines is an
isomorphism: condition (2) of [Stacks, Tag 0E2T] holds for `θ`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.isIso_diagonalAction_of_isRankOneHom` — the
  criterion.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite StrictlyPerfect

universe u

namespace AlgebraicGeometry.Scheme.Hom.DiagonalOpen

attribute [local instance] HasDerivedCategory.standard
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor

variable {X S : Scheme.{u}} {f : X ⟶ S} (D : DiagonalOpen f)

/-- **The map that a generator of `Hom(Δ_*𝒪_X, E)` defines is invertible** as soon as
`R𝓗om(Δ_*𝒪_X, E) ≅ Δ_*𝒪_X`: the formal criterion `CategoryTheory.isIso_curry_symm_mul_comp`
at the tensor–internal-hom bijection of Stacks 08DI, with the section `a ↦ a ⊗ 1` of the
derived multiplication. -/
theorem isIso_diagonalAction_of_isRankOneHom (K : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (_h : IsRankOneHom D.diagonalObject (D.derivedPullbackProj K))
    (θ : D.diagonalObject ⟶ D.derivedPullbackProj K)
    (hθ : Function.Bijective (fun c : D.diagonalObject ⟶ D.diagonalObject => c ≫ θ))
    (ψ : D.diagonalObject ≅
      ((Stacks.SheafOfModules.derivedSheafHom D.W.sheaf).obj (op D.diagonalObject)).obj
        (D.derivedPullbackProj K)) :
    IsIso (D.diagonalAction K θ) := by
  have hcurry : ∀ {Z Z' : DerivedCategory (Stacks.SheafOfModules.StructureSheafModules D.W.sheaf)}
      (c : Z' ⟶ Z) (g : Z ⟶ ((Stacks.SheafOfModules.derivedSheafHom D.W.sheaf).obj
        (op D.diagonalObject)).obj (D.derivedPullbackProj K)),
      Stacks.SheafOfModules.derivedSheafHomTensorEquiv D.W.sheaf Z' D.diagonalObject
          (D.derivedPullbackProj K) (c ≫ g) =
        ((Stacks.SheafOfModules.derivedTensor D.W.sheaf).map c).app D.diagonalObject ≫
          Stacks.SheafOfModules.derivedSheafHomTensorEquiv D.W.sheaf Z D.diagonalObject
            (D.derivedPullbackProj K) g :=
    fun c g => Stacks.SheafOfModules.derivedSheafHomTensorEquiv_naturality_source D.W.sheaf
      _ _ c g
  have key := isIso_curry_symm_mul_comp_of_addEquiv
    ((Stacks.SheafOfModules.derivedTensor D.W.sheaf).flip.obj D.diagonalObject)
    (fun Z => Stacks.SheafOfModules.derivedSheafHomTensorEquiv D.W.sheaf Z D.diagonalObject
      (D.derivedPullbackProj K)) hcurry
    (Stacks.RelativeSpec.AlgebraSheaf.derivedMul D.diagonalAlgebra)
    (Stacks.RelativeSpec.AlgebraSheaf.derivedUnitSection D.diagonalAlgebra)
    (Stacks.RelativeSpec.AlgebraSheaf.derivedUnitSection_naturality D.diagonalAlgebra)
    (Stacks.RelativeSpec.AlgebraSheaf.isIso_derivedUnitSection_comp_derivedMul D.diagonalAlgebra)
    _h.1 θ hθ ψ
  rw [diagonalAction]
  convert key using 4

end AlgebraicGeometry.Scheme.Hom.DiagonalOpen

end
