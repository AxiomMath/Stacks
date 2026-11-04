module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedTensorHom.InverseImage

/-!
# The inverse image of the derived internal Hom on `D(X_étale, Λ)`

Let `g : X ⟶ Y` be a morphism of schemes and `Λ` a commutative ring. The derived inverse image
`g⁻¹ : D(Y_étale, Λ) ⥤ D(X_étale, Λ)` commutes with the derived tensor product
(`Stacks.EtaleCohomology.etaleDerivedInverseImageTensorIso`, Stacks 07A4), so it carries a
canonical comparison with the derived internal Hom (Stacks 08JF)

`g⁻¹ RHom_Λ(K, M) ⟶ RHom_Λ(g⁻¹K, g⁻¹M)`,

the transpose, under the tensor–internal-Hom adjunction of `D(X_étale, Λ)`, of

`g⁻¹RHom(K, M) ⊗^L g⁻¹K ≅ g⁻¹(RHom(K, M) ⊗^L K) ⟶ g⁻¹M`,

`g⁻¹` of the evaluation (`Stacks.EtaleCohomology.etaleDerivedInverseImageHomComparison`). It is
compatible with the tensor–internal-Hom adjunctions on the two sides
(`Stacks.EtaleCohomology.etaleDerivedInverseImage_map_homEquiv_symm_comp_homComparison`): the
inverse image of the transpose of `P : A ⊗^L K ⟶ M`, followed by the comparison, is the transpose
of `g⁻¹ P` read through Stacks 07A4.

This is the comparison along a geometric point in the stalk computation of the duality morphism
of a smooth proper curve, in the proof of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

The statements consume `Stacks.EtaleCohomology.etaleDerivedHom`, defined in the standard model
`HasDerivedCategory.standard` of the derived category, as a local instance.

## Main definitions

* `Stacks.EtaleCohomology.etaleDerivedInverseImageHomComparison`.

## Main results

* `Stacks.EtaleCohomology.etaleDerivedInverseImageHomComparison_adjoint`: its transpose.
* `Stacks.EtaleCohomology.etaleDerivedInverseImage_map_homEquiv_symm_comp_homComparison`: the
  compatibility with the tensor–internal-Hom adjunctions.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type r) [CommRing Λ] {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- **The comparison of Stacks 08JF for the étale inverse image**:
`g⁻¹ RHom_Λ(K, M) ⟶ RHom_Λ(g⁻¹K, g⁻¹M)`, the transpose of `g⁻¹` of the evaluation read through
the comparison `etaleDerivedInverseImageTensorIso` of Stacks 07A4. -/
def etaleDerivedInverseImageHomComparison (K M : DerivedCategory (EtaleModules.{u, r} Λ Y)) :
    (etaleModuleDerivedInverseImage.{u, r} Λ g).obj
        (((etaleDerivedHom.{u, r} Λ Y).obj (op K)).obj M) ⟶
      ((etaleDerivedHom.{u, r} Λ X).obj
        (op ((etaleModuleDerivedInverseImage.{u, r} Λ g).obj K))).obj
        ((etaleModuleDerivedInverseImage.{u, r} Λ g).obj M) :=
  ((etaleTensorHomAdjunction.{u, r} Λ X).homEquiv _ _ _).symm
    ((etaleDerivedInverseImageTensorIso.{u, r} Λ g).inv.app
        (((etaleDerivedHom.{u, r} Λ Y).obj (op K)).obj M, K) ≫
      (etaleModuleDerivedInverseImage.{u, r} Λ g).map
        ((etaleTensorHomAdjunction.{u, r} Λ Y).homEquiv
          (((etaleDerivedHom.{u, r} Λ Y).obj (op K)).obj M) K M (𝟙 _)))

/-- **The transpose of the comparison** is `g⁻¹` of the evaluation, read through Stacks 07A4. -/
theorem etaleDerivedInverseImageHomComparison_adjoint
    (K M : DerivedCategory (EtaleModules.{u, r} Λ Y)) :
    (etaleTensorHomAdjunction.{u, r} Λ X).homEquiv _ _ _
        (etaleDerivedInverseImageHomComparison.{u, r} Λ g K M) =
      (etaleDerivedInverseImageTensorIso.{u, r} Λ g).inv.app
          (((etaleDerivedHom.{u, r} Λ Y).obj (op K)).obj M, K) ≫
        (etaleModuleDerivedInverseImage.{u, r} Λ g).map
          ((etaleTensorHomAdjunction.{u, r} Λ Y).homEquiv
            (((etaleDerivedHom.{u, r} Λ Y).obj (op K)).obj M) K M (𝟙 _)) := by
  rw [etaleDerivedInverseImageHomComparison, Equiv.apply_symm_apply]

/-- **The comparison is compatible with the tensor–internal-Hom adjunctions**: for
`P : A ⊗^L K ⟶ M` on `Y`, the inverse image of its transpose `A ⟶ RHom(K, M)` followed by the
comparison is the transpose of `g⁻¹A ⊗^L g⁻¹K ≅ g⁻¹(A ⊗^L K) ⟶ g⁻¹M`. -/
theorem etaleDerivedInverseImage_map_homEquiv_symm_comp_homComparison
    {A K M : DerivedCategory (EtaleModules.{u, r} Λ Y)}
    (P : ((etaleDerivedTensor.{u, r} Λ Y).obj A).obj K ⟶ M) :
    (etaleModuleDerivedInverseImage.{u, r} Λ g).map
        (((etaleTensorHomAdjunction.{u, r} Λ Y).homEquiv _ _ _).symm P) ≫
      etaleDerivedInverseImageHomComparison.{u, r} Λ g K M =
      ((etaleTensorHomAdjunction.{u, r} Λ X).homEquiv _ _ _).symm
        ((etaleDerivedInverseImageTensorIso.{u, r} Λ g).inv.app (A, K) ≫
          (etaleModuleDerivedInverseImage.{u, r} Λ g).map P) := by
  rw [Equiv.eq_symm_apply, (etaleTensorHomAdjunction.{u, r} Λ X).homEquiv_naturality_source]
  dsimp only [Functor.prod_obj]
  rw [etaleDerivedInverseImageHomComparison_adjoint]
  set φ := ((etaleTensorHomAdjunction.{u, r} Λ Y).homEquiv _ _ _).symm P
  have hα : (((etaleDerivedTensor.{u, r} Λ X).map
        ((etaleModuleDerivedInverseImage.{u, r} Λ g).map φ)).app
          ((etaleModuleDerivedInverseImage.{u, r} Λ g).obj K) ≫
        ((etaleDerivedTensor.{u, r} Λ X).obj ((etaleModuleDerivedInverseImage.{u, r} Λ g).obj
          (((etaleDerivedHom.{u, r} Λ Y).obj (op K)).obj M))).map
          ((etaleModuleDerivedInverseImage.{u, r} Λ g).map (𝟙 K))) ≫
      (etaleDerivedInverseImageTensorIso.{u, r} Λ g).inv.app
          (((etaleDerivedHom.{u, r} Λ Y).obj (op K)).obj M, K) =
      (etaleDerivedInverseImageTensorIso.{u, r} Λ g).inv.app (A, K) ≫
        (etaleModuleDerivedInverseImage.{u, r} Λ g).map
          (((etaleDerivedTensor.{u, r} Λ Y).map φ).app K ≫
            ((etaleDerivedTensor.{u, r} Λ Y).obj
              (((etaleDerivedHom.{u, r} Λ Y).obj (op K)).obj M)).map (𝟙 K)) :=
    (etaleDerivedInverseImageTensorIso.{u, r} Λ g).inv.naturality
      ((φ, 𝟙 K) : ((A, K) : _ × _) ⟶ (((etaleDerivedHom.{u, r} Λ Y).obj (op K)).obj M, K))
  simp only [CategoryTheory.Functor.map_id, Category.comp_id] at hα
  have hP : ((etaleDerivedTensor.{u, r} Λ Y).map φ).app K ≫
      (etaleTensorHomAdjunction.{u, r} Λ Y).homEquiv _ _ _ (𝟙 _) = P := by
    rw [← (etaleTensorHomAdjunction.{u, r} Λ Y).homEquiv_naturality_source, Category.comp_id,
      Equiv.apply_symm_apply]
  rw [← Category.assoc, hα, Category.assoc, ← Functor.map_comp, hP]

end Stacks.EtaleCohomology
