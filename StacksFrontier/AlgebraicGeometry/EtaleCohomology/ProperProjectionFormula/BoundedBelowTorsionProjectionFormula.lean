module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperProjectionFormula.TorsionBoundedBelowProjectionFormula
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedTensorHom.BoundedBelowTensor
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedTensorHom.TorsionTensor

/-!
# The projection formula for a proper morphism and a bounded below object with torsion cohomology

Let `f : X ⟶ Y` be a proper morphism of schemes, `E ∈ D^+(X_étale)` with torsion cohomology
sheaves and `K ∈ D^+(Y_étale)`. Then the projection map
`Rf_*E ⊗^L_ℤ K ⟶ Rf_*(E ⊗^L_ℤ f^{-1}K)` is an isomorphism [Stacks, Tag 0F0F].

The proof is the one of the Stacks project. The object `E ⊗^L_ℤ f^{-1}K` is bounded below
(`Stacks.EtaleCohomology.isGE_etaleDerivedTensor_of_isGE`) with torsion cohomology sheaves
(`Stacks.EtaleCohomology.isTorsionEtaleModule_homology_etaleDerivedTensor`), so proper base change
holds at `E` and at `E ⊗^L_ℤ f^{-1}K`; checking on geometric points reduces to the case of a
separably closed base field, which is [Stacks, Tag 0F14]. That assembly is
`Stacks.EtaleCohomology.isIso_projectionFormulaMap_etaleRingedToposHom_of_isGE_of_tensor`.

## Main results

* `Stacks.EtaleCohomology.isIso_etalePushforwardProjectionMap_of_isProper_of_isGE`: Stacks 0F0F.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.EtaleCohomology

/-- **Projection formula for a proper morphism and a bounded below object with torsion
cohomology** [Stacks, Tag 0F0F]. Let `f : X ⟶ Y` be a proper morphism of schemes, let
`E ∈ D^+(X_étale)` have torsion cohomology sheaves and let `K ∈ D^+(Y_étale)`. Then the projection
map `Rf_*E ⊗^L_ℤ K ⟶ Rf_*(E ⊗^L_ℤ f^{-1}K)` is an isomorphism in `D(Y_étale, ℤ)`. -/
@[stacks 0F0F]
theorem isIso_etalePushforwardProjectionMap_of_isProper_of_isGE {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f] (E : DerivedCategory (EtaleModules.{u, 0} ℤ X)) (a : ℤ) (hE : E.IsGE a)
    (hT : ∀ n, IsTorsionEtaleModule.{u, 0} ℤ X ((DerivedCategory.homologyFunctor _ n).obj E))
    (K : DerivedCategory (EtaleModules.{u, 0} ℤ Y)) (b : ℤ) (hK : K.IsGE b) :
    IsIso (etalePushforwardProjectionMap.{u, 0} ℤ f E K) := by
  rw [isIso_etalePushforwardProjectionMap_iff]
  exact isIso_projectionFormulaMap_etaleRingedToposHom_of_isGE_of_tensor f E a hE hT K b hK
    (a + b - 1)
    (isGE_etaleDerivedTensor_of_isGE E _ a b hE
      (isGE_etaleModuleDerivedInverseImage_obj ℤ f K b hK))
    (isTorsionEtaleModule_homology_etaleDerivedTensor E _ hT)

end Stacks.EtaleCohomology

end
