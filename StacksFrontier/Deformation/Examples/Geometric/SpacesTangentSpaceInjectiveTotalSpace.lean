module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatDeformationTotalSpaceIso
public import StacksFrontier.Deformation.Examples.Geometric.SpacesTangentSpaceInjectiveChartOverBase
public import StacksFrontier.Deformation.Examples.Geometric.SpacesTangentSpaceTangentClass

/-!
# Isomorphic extensions of deformations of an algebraic space give isomorphic total spaces

In the situation of Stacks 0E3Z, let `x, x'` be two deformations of the algebraic space `X` over
`k[V]`, with total spaces `X'₁ ⟶ Spec k[V]` and `X'₂ ⟶ Spec k[V]`, and let `e` be an isomorphism
of their extensions `0 ⟶ 𝒪_X ⊗_k V ⟶ 𝒪_{X'_j}|_X ⟶ 𝒪_X ⟶ 0` of `f⁻¹𝒪_{Spec k}`-algebras
(`Deformation.Examples.spaceTangentExtension`). Then there is an isomorphism `X'₁ ≅ X'₂` under `X`
and over `Spec k[V]`.

The isomorphism of the structure sheaves read on `X` given by `e` determines an isomorphism of the
small étale ringed topoi of `X'₁` and `X'₂` (the closed fibres are thickenings, Stacks 05ZM), and
Stacks 05YZ produces the isomorphism of total spaces from it. The base here is `S = Spec Λ`,
where Stacks 05YZ needs the chart morphisms of the isomorphism of ringed topoi to be over `S`
(`AlgebraicGeometry.Space.IsChartOverBase`); they are over the affine `Spec k[V]`, hence over `S`,
because the isomorphism pulls back the functions of `Spec k[V]` along the two structure morphisms
to each other: the constants `k ⊆ k[V]` since `e` is a morphism of `f⁻¹𝒪_{Spec k}`-algebras, and
`V ⊆ k[V]` since `e` is the identity on the ideals `𝒪_X ⊗_k V`
(`AlgebraicGeometry.Space.exists_iso_comp_eq_of_inverseImageStructureSheafIso_of_functions`).
The same compatibility with functions makes the isomorphism lie over `Spec k[V]` (Stacks 05Z1).

This is the step "isomorphic extensions give isomorphic deformations" of the injectivity in the
proof of the second display of [Stacks Project, Tag 0E41] (as in Stacks 0D1K, through the
identification of first-order deformations with extensions of Stacks 0D17).

## Main results

* `Deformation.Examples.isEquivalence_pushforward_spaceDefoThickeningIso_hom_comp`
* `Deformation.Examples.spaceDefoFunctionSectionE_map_retraction`
* `Deformation.Examples.exists_iso_spaceDefoArrow_comp_eq_of_iso`

## References

* [Stacks Project, Tag 0E41](https://stacks.math.columbia.edu/tag/0E41)
* [Stacks Project, Tag 05YZ](https://stacks.math.columbia.edu/tag/05YZ)
* [Stacks Project, Tag 05ZM](https://stacks.math.columbia.edu/tag/05ZM)
* [Stacks Project, Tag 05Z1](https://stacks.math.columbia.edu/tag/05Z1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Sheaf
open AlgebraicGeometry.Space Deformation.Artin Deformation.AlgebraExtension

attribute [local instance] MorphismOfTopoi.preservesFiniteLimits

universe u

namespace Deformation.Examples

variable {Λ : Type u} {k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable (B : BigFppfSite.{u}) (hΛ : B.Contains (Spec (.of Λ)))
variable (hSpec : ∀ A : ArtinianLocalAlgCat.{u, u, u} Λ k, B.Contains (Spec (.of A)))
variable (X : (BigFppfOver B (Spec (.of Λ)) hΛ)ᵒᵖ ⥤ Type u)
  (hX : IsAlgebraicSpace B (Spec (.of Λ)) hΛ X)
  (toK : X ⟶ yoneda.obj (spaceBaseOver B hΛ hSpec (residueFieldBase Λ k)))

/-! ### The closed fibre is a thickening -/

/-- **The direct image along `X ≅ Z ⊂ X'` is an equivalence of étale topoi**, `Z` the closed
fibre of a deformation `X'`: the composite is a closed immersion, surjective on points because
`Z ⊂ X'` is a thickening (Stacks 05ZM). -/
theorem isEquivalence_pushforward_spaceDefoThickeningIso_hom_comp
    (y : Over (spaceSpecialFiber B hΛ hSpec X hX toK))
    (hA : IsLocalRing.maximalIdeal y.left.base ^ 2 = ⊥) :
    (smallEtaleRingedToposHom B (Spec (.of Λ)) hΛ
      ((spaceDefoThickeningIso B hΛ hSpec X hX toK y hA).hom ≫
        subspaceInclusion B (Spec (.of Λ)) hΛ _ (spaceDefoThickening B hΛ hSpec X hX toK y
          hA))).toToposHom.pushforward.IsEquivalence := by
  obtain ⟨hG, -⟩ := isFirstOrderThickening_spaceDefoThickening B hΛ hSpec X hX toK y hA
  have : IsIso (spaceDefoThickeningIso B hΛ hSpec X hX toK y hA).hom.hom :=
    (ObjectProperty.ι _).map_isIso (spaceDefoThickeningIso B hΛ hSpec X hX toK y hA).hom
  have hci : IsClosedImmersion B (Spec (.of Λ)) hΛ
      ((spaceDefoThickeningIso B hΛ hSpec X hX toK y hA).hom ≫
        subspaceInclusion B (Spec (.of Λ)) hΛ _
          (spaceDefoThickening B hΛ hSpec X hX toK y hA)).hom :=
    isClosedImmersion_comp B (Spec (.of Λ)) hΛ _ _
      (isClosedImmersion_of_isIso B (Spec (.of Λ)) hΛ _)
      (isClosedImmersion_inclusion_of_isThickening B (Spec (.of Λ)) hΛ hG)
  refine isEquivalence_pushforward_smallEtaleRingedToposHom B (Spec (.of Λ)) hΛ _ hci
    ((surjective_iff_pointsMap_surjective B (Spec (.of Λ)) hΛ hX y.left.algebraic _ hci.rep).2 ?_)
  rw [show ((spaceDefoThickeningIso B hΛ hSpec X hX toK y hA).hom ≫
      subspaceInclusion B (Spec (.of Λ)) hΛ _ (spaceDefoThickening B hΛ hSpec X hX toK y hA)).hom =
        (spaceDefoThickeningIso B hΛ hSpec X hX toK y hA).hom.hom ≫
          (subspaceInclusion B (Spec (.of Λ)) hΛ _
            (spaceDefoThickening B hΛ hSpec X hX toK y hA)).hom from rfl,
    pointsMap_comp]
  exact hG.2.comp (pointsMap_surjective_of_isIso B (Spec (.of Λ)) hΛ _)

/-! ### The global sections of the middle term given by constants -/

section Retraction

variable {y : Over (spaceSpecialFiber B hΛ hSpec X hX toK)}
  (hsq : IsLocalRing.maximalIdeal y.left.base ^ 2 = ⊥)
  (r : spaceBaseOver B hΛ hSpec y.left.base ⟶ spaceBaseOver B hΛ hSpec (residueFieldBase Λ k))
  (hr : spaceDefoBaseImmersion B hΛ hSpec X hX toK y ≫ r = 𝟙 _)

/-- Postcomposition with `X ≅ Z` is continuous for the small étale topologies. -/
local instance smallEtalePostcomp_spaceDefoThickeningIso_isContinuous :
    (smallEtalePostcomp B (Spec (.of Λ)) hΛ (spaceDefoThickeningIso B hΛ hSpec X hX toK y hsq).hom
    (isEtale_hom_of_iso B (Spec (.of Λ)) hΛ
      (spaceDefoThickeningIso B hΛ hSpec X hX toK y hsq))).IsContinuous
    (SmallEtale.topology B (Spec (.of Λ)) hΛ X)
    (SmallEtale.topology B (Spec (.of Λ)) hΛ (spaceDefoFibreSpace B hΛ hSpec X hX toK y hsq).1) :=
  smallEtalePostcomp_isContinuous B (Spec (.of Λ)) hΛ _ _

/-- Postcomposition with `X ≅ Z` is cocontinuous for the small étale topologies. -/
local instance smallEtalePostcomp_spaceDefoThickeningIso_isCocontinuous :
    (smallEtalePostcomp B (Spec (.of Λ)) hΛ (spaceDefoThickeningIso B hΛ hSpec X hX toK y hsq).hom
    (isEtale_hom_of_iso B (Spec (.of Λ)) hΛ
      (spaceDefoThickeningIso B hΛ hSpec X hX toK y hsq))).IsCocontinuous
    (SmallEtale.topology B (Spec (.of Λ)) hΛ X)
    (SmallEtale.topology B (Spec (.of Λ)) hΛ (spaceDefoFibreSpace B hΛ hSpec X hX toK y hsq).1) :=
  smallEtalePostcomp_isCocontinuous B (Spec (.of Λ)) hΛ _ _

/-- **The algebra structure of the extension of a deformation on `X`**: through
`f = (θ ≫ i) ≫ g`, the étale restriction along `θ : X ≅ Z` of the inverse image along
`i : Z ⟶ X'` of `g^♯`, `g : X' ⟶ Spec A ⟶ Spec k` the retracted structure morphism. -/
theorem spaceDefoTensorBaseExtension_algebraMap :
    (spaceDefoTensorBaseExtension B hΛ hSpec X hX toK hsq r hr).algebraMap =
      eqToHom (congrArg (inverseImageStructureSheaf B (Spec (.of Λ)) hΛ)
        (spaceDefoThickeningIso_hom_comp_retractedStructureMap B hΛ hSpec X hX toK hsq r hr).symm) ≫
        (etaleRestrictionRingComparison B (Spec (.of Λ)) hΛ
          (spaceDefoThickeningIso B hΛ hSpec X hX toK y hsq).hom
          (isEtale_hom_of_iso B (Spec (.of Λ)) hΛ
            (spaceDefoThickeningIso B hΛ hSpec X hX toK y hsq))
          (subspaceInclusion B (Spec (.of Λ)) hΛ _ (spaceDefoThickening B hΛ hSpec X hX toK y hsq) ≫
            spaceDefoRetractedStructureMap B hΛ hSpec X hX toK r)).α.hom ≫
        (Deformation.AlgebraExtension.ringRes (SmallEtale.topology B (Spec (.of Λ)) hΛ X)
          (smallEtalePostcomp B (Spec (.of Λ)) hΛ
            (spaceDefoThickeningIso B hΛ hSpec X hX toK y hsq).hom
            (isEtale_hom_of_iso B (Spec (.of Λ)) hΛ
              (spaceDefoThickeningIso B hΛ hSpec X hX toK y hsq)))).map
          (inverseImageStructureSheafMap B (Spec (.of Λ)) hΛ
            (subspaceInclusion B (Spec (.of Λ)) hΛ _
              (spaceDefoThickening B hΛ hSpec X hX toK y hsq))
            (spaceDefoRetractedStructureMap B hΛ hSpec X hX toK r)) :=
  rfl

/-- **The global section of the middle term given by a constant**: for a retraction
`r : Spec A ⟶ Spec k` and `c ∈ Γ(Spec k)`, the global section of the middle term of the extension
of the deformation given by the function `r^♯c` of its base is the image of `f⁻¹c` under the
algebra structure `f⁻¹𝒪_{Spec k} ⟶ (i⁻¹𝒪_{X'})|_X`, on underlying sheaves of sets. -/
theorem spaceDefoFunctionSectionE_map_retraction
    (c : baseRing B (Spec (.of Λ)) hΛ (spaceBaseOver B hΛ hSpec (residueFieldBase Λ k))) :
    spaceDefoFunctionSectionE B hΛ hSpec X hX toK y hsq
        ((Scheme.Γ.map ((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map r).op).hom c) =
      (smallEtaleRingedToposHom B (Spec (.of Λ)) hΛ
          (spaceStructureMap B hΛ hSpec X hX toK)).toToposHom.inverseImage.globalSectionMap
          (functionGlobalSection
            (𝟙 (schemeSpace (spaceBaseOver B hΛ hSpec (residueFieldBase Λ k)))) c) ≫
        (sheafCompose (SmallEtale.topology B (Spec (.of Λ)) hΛ X) (forget CommRingCat.{u})).map
          (spaceDefoTensorBaseExtension B hΛ hSpec X hX toK hsq r hr).algebraMap := by
  have h1 := (globalFunctionsOfMap_comp B (Spec (.of Λ)) hΛ
    (spaceTotalToBase B hΛ hSpec y.left) r c).symm
  have h2 := ringOneHom_comp_map_unitModuleMul_globalFunctionsOfMap_eq B (Spec (.of Λ)) hΛ
    (spaceDefoRetractedStructureMap B hΛ hSpec X hX toK r) c
  have h3 := globalSectionMap_comp_forget_map_inverseImageStructureSheafMap B (Spec (.of Λ)) hΛ
    ((spaceDefoThickeningIso B hΛ hSpec X hX toK y hsq).hom ≫
      subspaceInclusion B (Spec (.of Λ)) hΛ _ (spaceDefoThickening B hΛ hSpec X hX toK y hsq))
    (spaceDefoRetractedStructureMap B hΛ hSpec X hX toK r)
    (functionGlobalSection (𝟙 (schemeSpace (spaceBaseOver B hΛ hSpec (residueFieldBase Λ k)))) c)
  have h4 := globalSectionMap_comp_forget_map_eqToHom_inverseImageStructureSheaf B (Spec (.of Λ)) hΛ
    ((Category.assoc _ _ _).trans
      (spaceDefoThickeningIso_hom_comp_retractedStructureMap B hΛ hSpec X hX toK hsq r hr)).symm
    (functionGlobalSection (𝟙 (schemeSpace (spaceBaseOver B hΛ hSpec (residueFieldBase Λ k)))) c)
  have h5 := (Iso.comp_inv_eq _).mp ((Category.assoc _ _ _).trans
    (etaleRestrictionRingComparison_α_map_inverseImageStructureSheafMap B (Spec (.of Λ)) hΛ
      (spaceDefoThickeningIso B hΛ hSpec X hX toK y hsq).hom
      (isEtale_hom_of_iso B (Spec (.of Λ)) hΛ (spaceDefoThickeningIso B hΛ hSpec X hX toK y hsq))
      (subspaceInclusion B (Spec (.of Λ)) hΛ _ (spaceDefoThickening B hΛ hSpec X hX toK y hsq))
      (spaceDefoRetractedStructureMap B hΛ hSpec X hX toK r)))
  have hU := (congrArg (fun t => (ringOneHom (structureRingSheaf B (Spec (.of Λ)) hΛ
      (spaceTotalSpace B hΛ hSpec y.left)) ≫
      (moduleSheafFunctor (structureRingSheaf B (Spec (.of Λ)) hΛ
        (spaceTotalSpace B hΛ hSpec y.left))).map
        (unitModuleMul B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec y.left) t) :
      ⊤_ _ ⟶ (sheafCompose (SmallEtale.topology B (Spec (.of Λ)) hΛ
        (spaceTotalSpace B hΛ hSpec y.left).1) (forget CommRingCat.{u})).obj
          (smallEtaleRingedTopos B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec y.left)).O))
    h1).trans h2
  refine (congrArg (fun t => (smallEtaleRingedToposHom B (Spec (.of Λ)) hΛ
      ((spaceDefoThickeningIso B hΛ hSpec X hX toK y hsq).hom ≫
        subspaceInclusion B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec y.left)
          (spaceDefoThickening B hΛ hSpec X hX toK y hsq))).toToposHom.inverseImage.globalSectionMap
        t ≫
    (sheafCompose (SmallEtale.topology B (Spec (.of Λ)) hΛ X) (forget CommRingCat.{u})).map
      (etaleRestrictionRingComparison B (Spec (.of Λ)) hΛ
        (spaceDefoThickeningIso B hΛ hSpec X hX toK y hsq).hom
        (isEtale_hom_of_iso B (Spec (.of Λ)) hΛ (spaceDefoThickeningIso B hΛ hSpec X hX toK y hsq))
        (subspaceInclusion B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec y.left)
          (spaceDefoThickening B hΛ hSpec X hX toK y hsq))).α.hom) hU).trans ?_
  refine (congrArg (· ≫ (sheafCompose (SmallEtale.topology B (Spec (.of Λ)) hΛ X)
    (forget CommRingCat.{u})).map
      (etaleRestrictionRingComparison B (Spec (.of Λ)) hΛ
        (spaceDefoThickeningIso B hΛ hSpec X hX toK y hsq).hom
        (isEtale_hom_of_iso B (Spec (.of Λ)) hΛ (spaceDefoThickeningIso B hΛ hSpec X hX toK y hsq))
        (subspaceInclusion B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec y.left)
          (spaceDefoThickening B hΛ hSpec X hX toK y hsq))).α.hom) h3.symm).trans ?_
  refine (congrArg (fun t => (t ≫ (sheafCompose (SmallEtale.topology B (Spec (.of Λ)) hΛ X)
    (forget CommRingCat.{u})).map (inverseImageStructureSheafMap B (Spec (.of Λ)) hΛ
      ((spaceDefoThickeningIso B hΛ hSpec X hX toK y hsq).hom ≫
        subspaceInclusion B (Spec (.of Λ)) hΛ _ (spaceDefoThickening B hΛ hSpec X hX toK y hsq))
      (spaceDefoRetractedStructureMap B hΛ hSpec X hX toK r))) ≫
    (sheafCompose (SmallEtale.topology B (Spec (.of Λ)) hΛ X) (forget CommRingCat.{u})).map
      (etaleRestrictionRingComparison B (Spec (.of Λ)) hΛ
        (spaceDefoThickeningIso B hΛ hSpec X hX toK y hsq).hom
        (isEtale_hom_of_iso B (Spec (.of Λ)) hΛ (spaceDefoThickeningIso B hΛ hSpec X hX toK y hsq))
        (subspaceInclusion B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec y.left)
          (spaceDefoThickening B hΛ hSpec X hX toK y hsq))).α.hom) h4.symm).trans ?_
  refine (Category.assoc _ _ _).trans ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ?_))
  have hmap : ∀ {P Q R W : Sheaf (SmallEtale.topology B (Spec (.of Λ)) hΛ X) CommRingCat.{u}}
      (p : P ⟶ Q) (q : Q ⟶ R) (r' : R ⟶ W) {s : P ⟶ W}, p ≫ q ≫ r' = s →
      (sheafCompose (SmallEtale.topology B (Spec (.of Λ)) hΛ X) (forget CommRingCat.{u})).map p ≫
        (sheafCompose (SmallEtale.topology B (Spec (.of Λ)) hΛ X) (forget CommRingCat.{u})).map q ≫
          (sheafCompose (SmallEtale.topology B (Spec (.of Λ)) hΛ X)
            (forget CommRingCat.{u})).map r' =
        (sheafCompose (SmallEtale.topology B (Spec (.of Λ)) hΛ X)
          (forget CommRingCat.{u})).map s := by
    intro P Q R W p q r' s h
    rw [← h, Functor.map_comp, Functor.map_comp]
  refine (hmap _ _ _ (congrArg (eqToHom _ ≫ ·) h5.symm)).trans ?_
  exact congrArg (sheafCompose (SmallEtale.topology B (Spec (.of Λ)) hΛ X)
    (forget CommRingCat.{u})).map
      (spaceDefoTensorBaseExtension_algebraMap B hΛ hSpec X hX toK hsq r hr).symm

end Retraction

end Deformation.Examples

end
