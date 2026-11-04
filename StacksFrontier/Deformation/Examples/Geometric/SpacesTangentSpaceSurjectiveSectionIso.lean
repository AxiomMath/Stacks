module

public import StacksFrontier.Deformation.Examples.Geometric.SpacesTangentSpaceSurjectiveGlobalFunction

/-!
# The section `1 ⊗ 1 : 𝒪_X ⟶ 𝒪_X ⊗_k k` is an isomorphism

For an algebraic space `X` over the field `k`, the section `1 ⊗ 1` of `𝒪_X ⊗_k k`
(`Deformation.Examples.spaceRankOneSection`) is an isomorphism: its inverse is the morphism
`𝒪_X ⊗_k k ⟶ 𝒪_X` corresponding, by the mapping property of `𝒪_X ⊗_k -`, to the `k`-linear map
`k ⟶ Γ(X, 𝒪_X)`, `1 ↦ 1`. One composite is the identity by the mapping property, the other
because morphisms out of `𝒪_X ⊗_k k` are determined by the sections `1 ⊗ a = a · (1 ⊗ 1)`.

## Main results

* `Deformation.Examples.isIso_spaceRankOneSection`.

## References

* [Stacks Project, Tag 0D3F](https://stacks.math.columbia.edu/tag/0D3F)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite AlgebraicGeometry.Space

universe u

namespace Deformation.Examples

variable {Λ : Type u} {k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable (B : BigFppfSite.{u}) (hΛ : B.Contains (Spec (.of Λ)))
variable (hSpec : ∀ A : ArtinianLocalAlgCat.{u, u, u} Λ k, B.Contains (Spec (.of A)))
variable (X : (BigFppfOver B (Spec (.of Λ)) hΛ)ᵒᵖ ⥤ Type u)
  (hX : IsAlgebraicSpace B (Spec (.of Λ)) hΛ X)
  (toK : X ⟶ yoneda.obj (spaceBaseOver B hΛ hSpec (residueFieldBase Λ k)))

/-- The morphism `𝒪_X ⊗_k k ⟶ 𝒪_X` of `1 ↦ 1`. -/
def spaceRankOneSectionInv :
    spaceRankOneCoefficient B hΛ hSpec X hX toK ⟶ unitModule B (Spec (.of Λ)) hΛ hX :=
  ((baseRingTensorModuleAdjunction B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)
    (spaceDefoFieldHom B hΛ hSpec X hX toK)).homEquiv _ _).symm
    ((ModuleCat.selfHomEquiv k
      ((baseRingGlobalSectionsModule B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)
        (spaceDefoFieldHom B hΛ hSpec X hX toK)).obj (unitModule B (Spec (.of Λ)) hΛ hX))).symm
      ((modelSectionsHomEquiv B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)
        (spaceDefoFieldHom B hΛ hSpec X hX toK) _).symm (𝟙 _)))

/-- `1 ⊗ 1` followed by `𝒪_X ⊗_k k ⟶ 𝒪_X` is the identity of `𝒪_X`. -/
theorem spaceRankOneSection_comp_inv :
    spaceRankOneSection B hΛ hSpec X hX toK ≫ spaceRankOneSectionInv B hΛ hSpec X hX toK = 𝟙 _ := by
  let A := baseRingTensorModuleAdjunction B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)
    (spaceDefoFieldHom B hΛ hSpec X hX toK)
  apply (modelSectionsHomEquiv B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)
    (spaceDefoFieldHom B hΛ hSpec X hX toK) _).symm.injective
  rw [modelSectionsHomEquiv_symm_naturality, spaceRankOneSection, baseRingTensorSection,
    Equiv.symm_apply_apply]
  have h := congrArg (fun f => ModuleCat.Hom.hom f (1 : k))
    (A.homEquiv_unit _ _ (spaceRankOneSectionInv B hΛ hSpec X hX toK))
  refine h.symm.trans ?_
  rw [spaceRankOneSectionInv, Equiv.apply_symm_apply]
  exact (ModuleCat.selfHomEquiv k ((baseRingGlobalSectionsModule B (Spec (.of Λ)) hΛ
    (spaceOf B hΛ X hX) (spaceDefoFieldHom B hΛ hSpec X hX toK)).obj
      (unitModule B (Spec (.of Λ)) hΛ hX))).apply_symm_apply
    ((modelSectionsHomEquiv B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)
      (spaceDefoFieldHom B hΛ hSpec X hX toK) _).symm (𝟙 _))

/-- **The sections `1 ⊗ m = m · (1 ⊗ 1)`.** -/
theorem spaceRankOneSection_smul (m : k) :
    baseRingTensorSection B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)
        (spaceDefoFieldHom B hΛ hSpec X hX toK)
        ((forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)).obj (FGModuleCat.of k k)) m =
      unitModuleMul B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)
          (globalFunctionsOfMap (spaceStructureMap B hΛ hSpec X hX toK)
            (spaceDefoAlgebraEquiv (B := B) (hΛ := hΛ) (hSpec := hSpec) (residueFieldBase Λ k) m)) ≫
        spaceRankOneSection B hΛ hSpec X hX toK := by
  let A := baseRingTensorModuleAdjunction B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)
    (spaceDefoFieldHom B hΛ hSpec X hX toK)
  have hm : (A.unit.app ((forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)).obj
      (FGModuleCat.of k k))).hom m =
      m • (A.unit.app ((forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)).obj
        (FGModuleCat.of k k))).hom (1 : k) := by
    rw [← map_smul]
    exact congrArg _ (mul_one m).symm
  refine (congrArg (modelSectionsHomEquiv B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)
    (spaceDefoFieldHom B hΛ hSpec X hX toK) _) hm).trans ?_
  exact modelSectionsHomEquiv_smul B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)
    (spaceStructureMap B hΛ hSpec X hX toK) _ _ _

/-- `𝒪_X ⊗_k k ⟶ 𝒪_X` followed by `1 ⊗ 1` is the identity of `𝒪_X ⊗_k k`. -/
theorem spaceRankOneSectionInv_comp :
    spaceRankOneSectionInv B hΛ hSpec X hX toK ≫ spaceRankOneSection B hΛ hSpec X hX toK = 𝟙 _ :=
  baseRingTensorModule_hom_ext B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)
    (spaceDefoFieldHom B hΛ hSpec X hX toK) fun m => by
      have h := spaceRankOneSection_smul B hΛ hSpec X hX toK m
      refine (congrArg (· ≫ _) h).trans ((Category.assoc _ _ _).trans ?_)
      refine (congrArg (_ ≫ ·) ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ spaceRankOneSection B hΛ hSpec X hX toK)
          (spaceRankOneSection_comp_inv B hΛ hSpec X hX toK)).trans (Category.id_comp _)))).trans ?_
      exact h.symm.trans (Category.comp_id _).symm

/-- **`1 ⊗ 1 : 𝒪_X ⟶ 𝒪_X ⊗_k k` is an isomorphism.** -/
instance isIso_spaceRankOneSection : IsIso (spaceRankOneSection B hΛ hSpec X hX toK) :=
  ⟨⟨spaceRankOneSectionInv B hΛ hSpec X hX toK, spaceRankOneSection_comp_inv B hΛ hSpec X hX toK,
    spaceRankOneSectionInv_comp B hΛ hSpec X hX toK⟩⟩

end Deformation.Examples

end
