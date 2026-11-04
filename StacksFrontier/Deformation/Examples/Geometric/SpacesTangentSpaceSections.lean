module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatDeformationTensorExtensionGlobalSection
public import StacksFrontier.Deformation.Examples.Geometric.SpacesTangentSpaceExtension

/-!
# The sections `1 ⊗ a` of the ideal of the extension of a deformation of an algebraic space

For a point `x` of the deformation category of an algebraic space `X` over `k` (Stacks 0E3Z),
over an algebra `A` of `𝒞_Λ` with `𝔪_A² = 0`, the ideal of its extension
(`Deformation.Examples.spaceDefoTensorBaseExtension`) is `𝒪_X ⊗_k 𝔪_A`, and its section `1 ⊗ a`
is included into `𝒪_{X'}|_X` as the pullback to `X` of the function `a` of `Spec A` along the
structure morphism `X' ⟶ Spec A`. This is the computation which makes the class of a deformation
natural in the coefficient module in the proof of [Stacks Project, Tag 0E41].

## Main results

* `Deformation.Examples.baseRingTensorSection_spaceDefoTensorIdealIso_inv`: the section `1 ⊗ a`
  of `𝒪_Z ⊗_R I` is the pullback to `Z` of the section `g^♯a` of the ideal of `Z ⊆ X'`.
* `Deformation.Examples.incl_baseRingTensorSection_comp_spaceDefoTensorLinearIdealIso_inv`: the
  section `1 ⊗ v` of `𝒪_{X₀} ⊗_k 𝔪_A` is included as the inverse image of the function `g^♯a`
  of `X'`.

## References

* [Stacks Project, Tag 0E41](https://stacks.math.columbia.edu/tag/0E41)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Space Deformation.Artin Deformation.AlgebraExtension CategoryTheory.Sheaf

attribute [local instance] MorphismOfTopoi.preservesFiniteLimits

universe u

namespace Deformation.Examples

variable {Λ : Type u} {k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable (B : BigFppfSite.{u}) (hΛ : B.Contains (Spec (.of Λ)))
variable (hSpec : ∀ A : ArtinianLocalAlgCat.{u, u, u} Λ k, B.Contains (Spec (.of A)))
variable (X : (BigFppfOver B (Spec (.of Λ)) hΛ)ᵒᵖ ⥤ Type u)
  (hX : IsAlgebraicSpace B (Spec (.of Λ)) hΛ X)
  (toK : X ⟶ yoneda.obj (spaceBaseOver B hΛ hSpec (residueFieldBase Λ k)))
variable (x : Over (spaceSpecialFiber B hΛ hSpec X hX toK))
  (hsq : IsLocalRing.maximalIdeal x.left.base ^ 2 = ⊥)

/-- **The sections `1 ⊗ a` of `𝒪_Z ⊗_R I` are the classes of the functions `a`**: read through
`AlgebraicGeometry.Space.deformationTensorIdealIso`, the section `1 ⊗ a` is the pullback to the
closed fibre `Z` of the section `g^♯a` of the ideal of `Z ⊆ X'`, `g : X' ⟶ Spec A` the structure
morphism. -/
theorem baseRingTensorSection_spaceDefoTensorIdealIso_inv
    (a : spaceDefoBaseKernel B hΛ hSpec X hX toK x hsq) :
    baseRingTensorSection B (Spec (.of Λ)) hΛ (spaceDefoFibreSpace B hΛ hSpec X hX toK x hsq)
        (baseRingHomOfMap (spaceDefoFibreBaseProjection B hΛ hSpec X hX toK x hsq))
        (spaceDefoBaseKernel B hΛ hSpec X hX toK x hsq) a ≫
        (spaceDefoTensorIdealIso B hΛ hSpec X hX toK x hsq).inv =
      modulePullbackGlobalSection B (Spec (.of Λ)) hΛ
        (subspaceInclusion B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec x.left)
          (spaceDefoThickening B hΛ hSpec X hX toK x hsq))
        (preimageIdealSection B (Spec (.of Λ)) hΛ (spaceTotalToBase B hΛ hSpec x.left)
          (rangeSubspace B (Spec (.of Λ)) hΛ (spaceDefoBaseImmersion B hΛ hSpec X hX toK x)
            (isClosedImmersion_spaceDefoBaseImmersion B hΛ hSpec X hX toK x hsq))
          ⟨a.1, (closedSubspaceBaseIdeal_rangeSubspace B (Spec (.of Λ)) hΛ
            (spaceDefoBaseImmersion B hΛ hSpec X hX toK x)
            (isClosedImmersion_spaceDefoBaseImmersion B hΛ hSpec X hX toK x hsq)).symm ▸ a.2⟩) :=
  baseRingTensorSection_conormalModulePreimageSquareZeroIso_inv B (Spec (.of Λ)) hΛ
    (spaceTotalToBase B hΛ hSpec x.left) (spaceDefoBaseImmersion B hΛ hSpec X hX toK x)
    (isClosedImmersion_spaceDefoBaseImmersion B hΛ hSpec X hX toK x hsq)
    (x.left.flat) (isAffine_spaceDefoBase B hΛ hSpec X hX toK x)
    (spaceDefoBaseImmersion_Γ_ker_sq B hΛ hSpec X hX toK x hsq) a

/-- The kernel inclusion of `AlgebraicGeometry.Space.deformationTensorAlgebraExtension` is that of
the first-order thickening, read through `AlgebraicGeometry.Space.deformationTensorIdealIso`. -/
theorem spaceDefoTensorAlgebraExtension_kernelInclusion {Y : AlgebraicSpaces B (Spec (.of Λ)) hΛ}
    (g : spaceTotalSpace B hΛ hSpec x.left ⟶ Y) :
    (spaceDefoTensorAlgebraExtension B hΛ hSpec X hX toK x hsq g).kernelInclusion =
      (SheafOfModules.restrictScalars
        ((sheafCompose (SmallEtale.topology B (Spec (.of Λ)) hΛ
            (spaceDefoThickening B hΛ hSpec X hX toK x hsq).1.toFunctor)
          (forget₂ CommRingCat.{u} RingCat.{u})).map
          (firstOrderAlgebraExtension B (Spec (.of Λ)) hΛ
            (spaceDefoThickening B hΛ hSpec X hX toK x hsq)
            (isFirstOrderThickening_spaceDefoThickening B hΛ hSpec X hX toK x hsq)
            g).reduction)).map
          (spaceDefoTensorIdealIso B hΛ hSpec X hX toK x hsq).inv ≫
        (firstOrderAlgebraExtension B (Spec (.of Λ)) hΛ
          (spaceDefoThickening B hΛ hSpec X hX toK x hsq)
          (isFirstOrderThickening_spaceDefoThickening B hΛ hSpec X hX toK x hsq)
          g).kernelInclusion :=
  rfl

/-- **The kernel inclusion on the sections `1 ⊗ a`.** In the extension
`AlgebraicGeometry.Space.deformationTensorAlgebraExtension`, the section `1 ⊗ a` of the ideal
`𝒪_Z ⊗_R I` is included into `i⁻¹𝒪_{X'}` as the class of the function `g^♯a` of `X'`
(`g : X' ⟶ Spec A` the structure morphism), carried by the inclusion
`AlgebraicGeometry.Space.conormalInverseImageι` of the first-order thickening `Z ⊆ X'`. -/
theorem spaceDefoTensorAlgebraExtension_incl_baseRingTensorSection
    {Y : AlgebraicSpaces B (Spec (.of Λ)) hΛ} (g : spaceTotalSpace B hΛ hSpec x.left ⟶ Y)
    (a : spaceDefoBaseKernel B hΛ hSpec X hX toK x hsq)
    {U : (SmallEtale B (Spec (.of Λ)) hΛ
      (spaceDefoThickening B hΛ hSpec X hX toK x hsq).1.toFunctor)ᵒᵖ} :
    (spaceDefoTensorAlgebraExtension B hΛ hSpec X hX toK x hsq g).incl
        ((baseRingTensorSection B (Spec (.of Λ)) hΛ (spaceDefoFibreSpace B hΛ hSpec X hX toK x hsq)
          (baseRingHomOfMap (spaceDefoFibreBaseProjection B hΛ hSpec X hX toK x hsq))
          (spaceDefoBaseKernel B hΛ hSpec X hX toK x hsq) a).val.app U
          (1 : (structureRingSheaf B (Spec (.of Λ)) hΛ
            (spaceDefoFibreSpace B hΛ hSpec X hX toK x hsq)).obj.obj U)) =
      (conormalInverseImageι B (Spec (.of Λ)) hΛ (spaceDefoThickening B hΛ hSpec X hX toK x hsq)
          (isFirstOrderThickening_spaceDefoThickening B hΛ hSpec X hX toK x hsq)).val.app U
        ((modulePullbackGlobalSection B (Spec (.of Λ)) hΛ
          (subspaceInclusion B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec x.left)
            (spaceDefoThickening B hΛ hSpec X hX toK x hsq))
          (preimageIdealSection B (Spec (.of Λ)) hΛ (spaceTotalToBase B hΛ hSpec x.left)
            (rangeSubspace B (Spec (.of Λ)) hΛ (spaceDefoBaseImmersion B hΛ hSpec X hX toK x)
              (isClosedImmersion_spaceDefoBaseImmersion B hΛ hSpec X hX toK x hsq))
            ⟨a.1, (closedSubspaceBaseIdeal_rangeSubspace B (Spec (.of Λ)) hΛ
              (spaceDefoBaseImmersion B hΛ hSpec X hX toK x)
              (isClosedImmersion_spaceDefoBaseImmersion B hΛ hSpec X hX toK x hsq)).symm ▸
                a.2⟩)).val.app U
          (1 : (structureRingSheaf B (Spec (.of Λ)) hΛ
            (spaceDefoFibreSpace B hΛ hSpec X hX toK x hsq)).obj.obj U)) := by
  have h := congrArg (fun t => t.val.app U
      (1 : (structureRingSheaf B (Spec (.of Λ)) hΛ
        (spaceDefoFibreSpace B hΛ hSpec X hX toK x hsq)).obj.obj U))
    (baseRingTensorSection_spaceDefoTensorIdealIso_inv B hΛ hSpec X hX toK x hsq a)
  refine (firstOrderAlgebraExtension_incl B (Spec (.of Λ)) hΛ
    (spaceDefoThickening B hΛ hSpec X hX toK x hsq)
    (isFirstOrderThickening_spaceDefoThickening B hΛ hSpec X hX toK x hsq) g _).trans ?_
  exact congrArg (fun m => (conormalInverseImageι B (Spec (.of Λ)) hΛ
    (spaceDefoThickening B hΛ hSpec X hX toK x hsq)
    (isFirstOrderThickening_spaceDefoThickening B hΛ hSpec X hX toK x hsq)).val.app U m)
    ((SheafOfModules.comp_val_app_apply _ _ _ _).symm.trans h)

/-- **The sections `1 ⊗ v` of `𝒪_{X₀} ⊗_k 𝔪_A`**, read through
`AlgebraicGeometry.Space.deformationTensorLinearIdealIso`: the restriction to `X₀ ≅ Z` of the
section `1 ⊗ v` of `𝒪_Z ⊗_R I`. -/
theorem baseRingTensorSection_spaceDefoTensorLinearIdealIso_inv
    (v : RingHom.squareZeroKer (residueMap x.left.base) (residueMap_surjective' x.left.base)
      (ker_residueMap_sq_of_maximalIdeal_sq hsq)) :
    baseRingTensorSection B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)
        (spaceDefoFieldHom B hΛ hSpec X hX toK)
        (RingHom.squareZeroKer (residueMap x.left.base) (residueMap_surjective' x.left.base)
      (ker_residueMap_sq_of_maximalIdeal_sq hsq)) v ≫
        (spaceDefoTensorLinearIdealIso B hΛ hSpec X hX toK x hsq).inv =
      modulePullbackGlobalSection B (Spec (.of Λ)) hΛ
          (spaceDefoThickeningIso B hΛ hSpec X hX toK x hsq).hom
          (baseRingTensorSection B (Spec (.of Λ)) hΛ (spaceDefoFibreSpace B hΛ hSpec X hX toK x hsq)
            (baseRingHomOfMap (spaceDefoFibreBaseProjection B hΛ hSpec X hX toK x hsq))
            (spaceDefoBaseKernel B hΛ hSpec X hX toK x hsq)
            ((RingHom.squareZeroKerRingEquivIso _ _
              (spaceDefoAlgebraEquiv (B := B) (hΛ := hΛ) (hSpec := hSpec) x.left.base)
              (spaceDefoAlgebraEquiv (B := B) (hΛ := hΛ) (hSpec := hSpec) (residueFieldBase Λ k))
              (spaceDefoBaseImmersion_Γ_comp B hΛ hSpec X hX toK x)
              (spaceDefoBaseImmersion_Γ_surjective B hΛ hSpec X hX toK x)
              (spaceDefoBaseImmersion_Γ_ker_sq B hΛ hSpec X hX toK x hsq)
              (residueMap_surjective' x.left.base)
      (ker_residueMap_sq_of_maximalIdeal_sq hsq)).inv.hom v)) ≫
        ((modulePullbackIsoEtaleRestrictionModule B (Spec (.of Λ)) hΛ
          (spaceDefoThickeningIso B hΛ hSpec X hX toK x hsq).hom
          (isEtale_hom_of_iso B (Spec (.of Λ)) hΛ _)).app _).hom := by
  have h₅ := baseRingTensorSection_map B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)
    (spaceDefoFieldHom B hΛ hSpec X hX toK)
    (RingHom.squareZeroKerRingEquivIso _ _
      (spaceDefoAlgebraEquiv (B := B) (hΛ := hΛ) (hSpec := hSpec) x.left.base)
      (spaceDefoAlgebraEquiv (B := B) (hΛ := hΛ) (hSpec := hSpec) (residueFieldBase Λ k))
      (spaceDefoBaseImmersion_Γ_comp B hΛ hSpec X hX toK x)
      (spaceDefoBaseImmersion_Γ_surjective B hΛ hSpec X hX toK x)
      (spaceDefoBaseImmersion_Γ_ker_sq B hΛ hSpec X hX toK x hsq)
      (residueMap_surjective' x.left.base)
      (ker_residueMap_sq_of_maximalIdeal_sq hsq)).inv v
  have h₄ := baseRingTensorSection_restrictScalarsIso_hom B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)
    (baseRingHomOfMap (spaceStructureMap B hΛ hSpec X hX toK))
    (spaceDefoAlgebraEquiv (B := B) (hΛ := hΛ) (hSpec := hSpec) (residueFieldBase Λ k)).surjective
    (spaceDefoBaseKernel B hΛ hSpec X hX toK x hsq)
    ((RingHom.squareZeroKerRingEquivIso _ _
      (spaceDefoAlgebraEquiv (B := B) (hΛ := hΛ) (hSpec := hSpec) x.left.base)
      (spaceDefoAlgebraEquiv (B := B) (hΛ := hΛ) (hSpec := hSpec) (residueFieldBase Λ k))
      (spaceDefoBaseImmersion_Γ_comp B hΛ hSpec X hX toK x)
      (spaceDefoBaseImmersion_Γ_surjective B hΛ hSpec X hX toK x)
      (spaceDefoBaseImmersion_Γ_ker_sq B hΛ hSpec X hX toK x hsq)
      (residueMap_surjective' x.left.base)
      (ker_residueMap_sq_of_maximalIdeal_sq hsq)).inv.hom v)
  have h₃ := baseRingTensorSection_eqToIso_inv B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)
    (φ := baseRingHomOfMap (spaceStructureMap B hΛ hSpec X hX toK))
    (φ' := baseRingHomOfMap ((spaceDefoThickeningIso B hΛ hSpec X hX toK x hsq).hom ≫
      spaceDefoFibreBaseProjection B hΛ hSpec X hX toK x hsq))
    (congrArg baseRingHomOfMap
      (spaceDefoThickeningIso_hom_comp_fibreBaseProjection B hΛ hSpec X hX toK x hsq))
    (spaceDefoBaseKernel B hΛ hSpec X hX toK x hsq)
    ((RingHom.squareZeroKerRingEquivIso _ _
      (spaceDefoAlgebraEquiv (B := B) (hΛ := hΛ) (hSpec := hSpec) x.left.base)
      (spaceDefoAlgebraEquiv (B := B) (hΛ := hΛ) (hSpec := hSpec) (residueFieldBase Λ k))
      (spaceDefoBaseImmersion_Γ_comp B hΛ hSpec X hX toK x)
      (spaceDefoBaseImmersion_Γ_surjective B hΛ hSpec X hX toK x)
      (spaceDefoBaseImmersion_Γ_ker_sq B hΛ hSpec X hX toK x hsq)
      (residueMap_surjective' x.left.base)
      (ker_residueMap_sq_of_maximalIdeal_sq hsq)).inv.hom v)
  have h₂ := baseRingTensorSection_comp_pullbackCompIso_inv B (Spec (.of Λ)) hΛ
    (spaceDefoThickeningIso B hΛ hSpec X hX toK x hsq).hom
    (spaceDefoFibreBaseProjection B hΛ hSpec X hX toK x hsq)
    (spaceDefoBaseKernel B hΛ hSpec X hX toK x hsq)
    ((RingHom.squareZeroKerRingEquivIso _ _
      (spaceDefoAlgebraEquiv (B := B) (hΛ := hΛ) (hSpec := hSpec) x.left.base)
      (spaceDefoAlgebraEquiv (B := B) (hΛ := hΛ) (hSpec := hSpec) (residueFieldBase Λ k))
      (spaceDefoBaseImmersion_Γ_comp B hΛ hSpec X hX toK x)
      (spaceDefoBaseImmersion_Γ_surjective B hΛ hSpec X hX toK x)
      (spaceDefoBaseImmersion_Γ_ker_sq B hΛ hSpec X hX toK x hsq)
      (residueMap_surjective' x.left.base)
      (ker_residueMap_sq_of_maximalIdeal_sq hsq)).inv.hom v)
  refine CategoryTheory.comp_trans_trans_trans_trans_inv
    ((modulePullbackIsoEtaleRestrictionModule B (Spec (.of Λ)) hΛ
      (spaceDefoThickeningIso B hΛ hSpec X hX toK x hsq).hom
      (isEtale_hom_of_iso B (Spec (.of Λ)) hΛ _)).app _).symm
    ((baseRingTensorModulePullbackCompIso B (Spec (.of Λ)) hΛ
      (spaceDefoThickeningIso B hΛ hSpec X hX toK x hsq).hom
      (spaceDefoFibreBaseProjection B hΛ hSpec X hX toK x hsq)).app
        (spaceDefoBaseKernel B hΛ hSpec X hX toK x hsq))
    (eqToIso (congrArg
      (fun φ => (baseRingTensorModule B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX) φ).obj
        (spaceDefoBaseKernel B hΛ hSpec X hX toK x hsq))
      (congrArg baseRingHomOfMap
        (spaceDefoThickeningIso_hom_comp_fibreBaseProjection B hΛ hSpec X hX toK x hsq))))
    ((baseRingTensorModuleRestrictScalarsIso B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)
      (spaceDefoAlgebraEquiv (B := B) (hΛ := hΛ) (hSpec := hSpec) (residueFieldBase Λ k)).toRingHom
      (baseRingHomOfMap (spaceStructureMap B hΛ hSpec X hX toK))
      (spaceDefoAlgebraEquiv (B := B) (hΛ := hΛ) (hSpec := hSpec)
        (residueFieldBase Λ k)).surjective).app _).symm
    ((baseRingTensorModule B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)
      (spaceDefoFieldHom B hΛ hSpec X hX toK)).mapIso
      (RingHom.squareZeroKerRingEquivIso _ _
        (spaceDefoAlgebraEquiv (B := B) (hΛ := hΛ) (hSpec := hSpec) x.left.base)
        (spaceDefoAlgebraEquiv (B := B) (hΛ := hΛ) (hSpec := hSpec) (residueFieldBase Λ k))
        (spaceDefoBaseImmersion_Γ_comp B hΛ hSpec X hX toK x) _ _
        (residueMap_surjective' x.left.base)
      (ker_residueMap_sq_of_maximalIdeal_sq hsq)))
    _ ?s4 ?s3 ?s2 ?s1 _ ?h5 ?h4 ?h3 ?h2 ?h1
    (spaceDefoTensorLinearIdealIso B hΛ hSpec X hX toK x hsq) rfl
  case h5 => exact h₅
  case h4 => exact h₄
  case h3 => exact h₃
  case h2 => exact h₂
  case h1 => rfl

/-- **The section `1 ⊗ a` of the ideal of a deformation, on sheaves of sets**: in the extension
`AlgebraicGeometry.Space.deformationTensorAlgebraExtension`, the unit section followed by `1 ⊗ a`
and the inclusion of the ideal into `i⁻¹𝒪_{X'}` is the inverse image along the inclusion
`i : Z ⟶ X'` of the closed fibre of the global section `g^♯a` of `𝒪_{X'}`, `g : X' ⟶ Spec A` the
structure morphism. -/
theorem ringOneHom_comp_map_baseRingTensorSection_comp_spaceDefoTensorAlgebraExtension_inclSheafSets
    {Y : AlgebraicSpaces B (Spec (.of Λ)) hΛ} (g : spaceTotalSpace B hΛ hSpec x.left ⟶ Y)
    (a : spaceDefoBaseKernel B hΛ hSpec X hX toK x hsq) :
    ringOneHom ((sheafCompose (SmallEtale.topology B (Spec (.of Λ)) hΛ
          (spaceDefoThickening B hΛ hSpec X hX toK x hsq).1.toFunctor)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj
          (smallEtaleRingedTopos B (Spec (.of Λ)) hΛ
            (spaceDefoFibreSpace B hΛ hSpec X hX toK x hsq)).O) ≫
        (moduleSheafFunctor ((sheafCompose (SmallEtale.topology B (Spec (.of Λ)) hΛ
          (spaceDefoThickening B hΛ hSpec X hX toK x hsq).1.toFunctor)
          (forget₂ CommRingCat.{u} RingCat.{u})).obj
            (smallEtaleRingedTopos B (Spec (.of Λ)) hΛ
              (spaceDefoFibreSpace B hΛ hSpec X hX toK x hsq)).O)).map
          (baseRingTensorSection B (Spec (.of Λ)) hΛ (spaceDefoFibreSpace B hΛ hSpec X hX toK x hsq)
            (baseRingHomOfMap (spaceDefoFibreBaseProjection B hΛ hSpec X hX toK x hsq))
            (spaceDefoBaseKernel B hΛ hSpec X hX toK x hsq) a) ≫
        (spaceDefoTensorAlgebraExtension B hΛ hSpec X hX toK x hsq g).inclSheafSets =
      (thickeningToposHom B (Spec (.of Λ)) hΛ
          (spaceDefoThickening B hΛ hSpec X hX toK x hsq)).inverseImage.globalSectionMap
        (ringOneHom (structureRingSheaf B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec x.left)) ≫
          (moduleSheafFunctor (structureRingSheaf B (Spec (.of Λ)) hΛ
              (spaceTotalSpace B hΛ hSpec x.left))).map
            (unitModuleMul B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec x.left)
              (globalFunctionsOfMap (spaceTotalToBase B hΛ hSpec x.left) a.1))) := by
  have hc := ringOneHom_comp_map_conormalInverseImageι_modulePullbackGlobalSection B (Spec (.of Λ))
    hΛ (spaceDefoThickening B hΛ hSpec X hX toK x hsq)
    (isFirstOrderThickening_spaceDefoThickening B hΛ hSpec X hX toK x hsq)
    (preimageIdealSection B (Spec (.of Λ)) hΛ (spaceTotalToBase B hΛ hSpec x.left)
      (rangeSubspace B (Spec (.of Λ)) hΛ (spaceDefoBaseImmersion B hΛ hSpec X hX toK x)
        (isClosedImmersion_spaceDefoBaseImmersion B hΛ hSpec X hX toK x hsq))
      ⟨a.1, (closedSubspaceBaseIdeal_rangeSubspace B (Spec (.of Λ)) hΛ
        (spaceDefoBaseImmersion B hΛ hSpec X hX toK x)
        (isClosedImmersion_spaceDefoBaseImmersion B hΛ hSpec X hX toK x hsq)).symm ▸ a.2⟩)
  have hs' : preimageIdealSection B (Spec (.of Λ)) hΛ (spaceTotalToBase B hΛ hSpec x.left)
      (rangeSubspace B (Spec (.of Λ)) hΛ (spaceDefoBaseImmersion B hΛ hSpec X hX toK x)
        (isClosedImmersion_spaceDefoBaseImmersion B hΛ hSpec X hX toK x hsq))
      ⟨a.1, (closedSubspaceBaseIdeal_rangeSubspace B (Spec (.of Λ)) hΛ
        (spaceDefoBaseImmersion B hΛ hSpec X hX toK x)
        (isClosedImmersion_spaceDefoBaseImmersion B hΛ hSpec X hX toK x hsq)).symm ▸ a.2⟩ ≫
      (definingIdealSheaf B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec x.left)
        (spaceDefoThickening B hΛ hSpec X hX toK x hsq)).ι =
      unitModuleMul B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec x.left)
        (globalFunctionsOfMap (spaceTotalToBase B hΛ hSpec x.left) a.1) :=
    preimageIdealSection_ι B (Spec (.of Λ)) hΛ _ _ _
  have hm := congrArg (fun m : SheafOfModules.unit (structureRingSheaf B (Spec (.of Λ)) hΛ
      (spaceTotalSpace B hΛ hSpec x.left)) ⟶ SheafOfModules.unit (structureRingSheaf B
        (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec x.left)) =>
    (thickeningToposHom B (Spec (.of Λ)) hΛ
        (spaceDefoThickening B hΛ hSpec X hX toK x hsq)).inverseImage.globalSectionMap
      (ringOneHom (structureRingSheaf B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec x.left)) ≫
        (moduleSheafFunctor (structureRingSheaf B (Spec (.of Λ)) hΛ
          (spaceTotalSpace B hΛ hSpec x.left))).map m)) hs'
  refine Eq.trans ?_ (hc.trans hm)
  exact Deformation.AlgebraExtension.ringOneHom_comp_map_comp_inclSheafSets_eq_of_incl
    (spaceDefoTensorAlgebraExtension B hΛ hSpec X hX toK x hsq g)
    (baseRingTensorSection B (Spec (.of Λ)) hΛ (spaceDefoFibreSpace B hΛ hSpec X hX toK x hsq)
      (baseRingHomOfMap (spaceDefoFibreBaseProjection B hΛ hSpec X hX toK x hsq))
      (spaceDefoBaseKernel B hΛ hSpec X hX toK x hsq) a)
    (structureSharpRingInverseImage B (Spec (.of Λ)) hΛ
      (subspaceInclusion B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec x.left)
        (spaceDefoThickening B hΛ hSpec X hX toK x hsq)))
    (modulePullbackGlobalSection B (Spec (.of Λ)) hΛ
      (subspaceInclusion B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec x.left)
        (spaceDefoThickening B hΛ hSpec X hX toK x hsq))
      (preimageIdealSection B (Spec (.of Λ)) hΛ (spaceTotalToBase B hΛ hSpec x.left)
        (rangeSubspace B (Spec (.of Λ)) hΛ (spaceDefoBaseImmersion B hΛ hSpec X hX toK x)
          (isClosedImmersion_spaceDefoBaseImmersion B hΛ hSpec X hX toK x hsq))
        ⟨a.1, (closedSubspaceBaseIdeal_rangeSubspace B (Spec (.of Λ)) hΛ
          (spaceDefoBaseImmersion B hΛ hSpec X hX toK x)
          (isClosedImmersion_spaceDefoBaseImmersion B hΛ hSpec X hX toK x hsq)).symm ▸ a.2⟩))
    (conormalInverseImageι B (Spec (.of Λ)) hΛ (spaceDefoThickening B hΛ hSpec X hX toK x hsq)
      (isFirstOrderThickening_spaceDefoThickening B hΛ hSpec X hX toK x hsq))
    (fun U => spaceDefoTensorAlgebraExtension_incl_baseRingTensorSection B hΛ hSpec X hX toK x hsq
      g a (U := U))

/-- Postcomposition with the isomorphism `spaceDefoThickeningIso` is continuous for the small
étale topologies. -/
local instance : (smallEtalePostcomp B (Spec (.of Λ)) hΛ
    (spaceDefoThickeningIso B hΛ hSpec X hX toK x hsq).hom
    (isEtale_hom_of_iso B (Spec (.of Λ)) hΛ
      (spaceDefoThickeningIso B hΛ hSpec X hX toK x hsq))).IsContinuous
    (SmallEtale.topology B (Spec (.of Λ)) hΛ X)
    (SmallEtale.topology B (Spec (.of Λ)) hΛ (spaceDefoFibreSpace B hΛ hSpec X hX toK x hsq).1) :=
  smallEtalePostcomp_isContinuous B (Spec (.of Λ)) hΛ _ _

/-- Postcomposition with the isomorphism `spaceDefoThickeningIso` is cocontinuous for the small
étale topologies. -/
local instance : (smallEtalePostcomp B (Spec (.of Λ)) hΛ
    (spaceDefoThickeningIso B hΛ hSpec X hX toK x hsq).hom
    (isEtale_hom_of_iso B (Spec (.of Λ)) hΛ
      (spaceDefoThickeningIso B hΛ hSpec X hX toK x hsq))).IsCocontinuous
    (SmallEtale.topology B (Spec (.of Λ)) hΛ X)
    (SmallEtale.topology B (Spec (.of Λ)) hΛ (spaceDefoFibreSpace B hΛ hSpec X hX toK x hsq).1) :=
  smallEtalePostcomp_isCocontinuous B (Spec (.of Λ)) hΛ _ _

variable {x} (r : spaceBaseOver B hΛ hSpec x.left.base ⟶
    spaceBaseOver B hΛ hSpec (residueFieldBase Λ k))
  (hr : spaceDefoBaseImmersion B hΛ hSpec X hX toK x ≫ r = 𝟙 _)

/-- **The section `1 ⊗ v` of `𝒪_{X₀} ⊗_k 𝔪_A`, on sheaves of sets**: in the extension
`AlgebraicGeometry.Space.deformationTensorBaseExtension` of a deformation, on the space `X₀` it
deforms, the unit section followed by `1 ⊗ v` (read through
`AlgebraicGeometry.Space.deformationTensorLinearIdealIso`) and the inclusion of the ideal is the
inverse image along `X₀ ≅ Z ⊆ X'` of the function `g^♯a` of `X'`, `a ∈ 𝔪_A` the element `v`
read in `Γ(Spec A)`, through `(e ≫ i)⁻¹𝒪_{X'} ≅ (i⁻¹𝒪_{X'})|_{X₀}`. -/
theorem incl_baseRingTensorSection_comp_spaceDefoTensorLinearIdealIso_inv
    (v : RingHom.squareZeroKer (residueMap x.left.base) (residueMap_surjective' x.left.base)
      (ker_residueMap_sq_of_maximalIdeal_sq hsq))
    (V : (SmallEtale B (Spec (.of Λ)) hΛ X)ᵒᵖ)
    (p : (sectionsFunctor _ V).obj
      (⊤_ Sheaf (SmallEtale.topology B (Spec (.of Λ)) hΛ X) (Type u))) :
    (spaceDefoTensorBaseExtension B hΛ hSpec X hX toK hsq r hr).incl
        ((baseRingTensorSection B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)
            (spaceDefoFieldHom B hΛ hSpec X hX toK)
            (RingHom.squareZeroKer (residueMap x.left.base) (residueMap_surjective' x.left.base)
      (ker_residueMap_sq_of_maximalIdeal_sq hsq)) v ≫
            (spaceDefoTensorLinearIdealIso B hΛ hSpec X hX toK x hsq).inv).val.app V
          (1 : (structureRingSheaf B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)).obj.obj V)) =
      (sectionsFunctor _ V).map
        ((smallEtaleSetRestriction B (Spec (.of Λ)) hΛ
          (spaceDefoThickeningIso B hΛ hSpec X hX toK x hsq).hom
          (isEtale_hom_of_iso B (Spec (.of Λ)) hΛ
            (spaceDefoThickeningIso B hΛ hSpec X hX toK x hsq))).globalSectionMap
          ((smallEtaleRingedToposHom B (Spec (.of Λ)) hΛ (subspaceInclusion B (Spec (.of Λ)) hΛ
          (spaceTotalSpace B hΛ hSpec x.left)
          (spaceDefoThickening B hΛ hSpec X hX toK x hsq))).toToposHom.inverseImage.globalSectionMap
            (ringOneHom (structureRingSheaf B (Spec (.of Λ)) hΛ
                (spaceTotalSpace B hΛ hSpec x.left)) ≫
              (moduleSheafFunctor (structureRingSheaf B (Spec (.of Λ)) hΛ
                  (spaceTotalSpace B hΛ hSpec x.left))).map
                (unitModuleMul B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec x.left)
                  (globalFunctionsOfMap (spaceTotalToBase B hΛ hSpec x.left)
                    ((RingHom.squareZeroKerRingEquivIso _ _
                      (spaceDefoAlgebraEquiv (B := B) (hΛ := hΛ) (hSpec := hSpec) x.left.base)
                      (spaceDefoAlgebraEquiv (B := B) (hΛ := hΛ) (hSpec := hSpec)
                        (residueFieldBase Λ k))
                      (spaceDefoBaseImmersion_Γ_comp B hΛ hSpec X hX toK x)
                      (spaceDefoBaseImmersion_Γ_surjective B hΛ hSpec X hX toK x)
                      (spaceDefoBaseImmersion_Γ_ker_sq B hΛ hSpec X hX toK x hsq)
                      (residueMap_surjective' x.left.base)
      (ker_residueMap_sq_of_maximalIdeal_sq hsq)).inv.hom v).1))))) p := by
  have hL := baseRingTensorSection_spaceDefoTensorLinearIdealIso_inv B hΛ hSpec X hX toK x hsq v
  have hZ :=
    ringOneHom_comp_map_baseRingTensorSection_comp_spaceDefoTensorAlgebraExtension_inclSheafSets
    B hΛ hSpec X hX toK x hsq (spaceDefoRetractedStructureMap B hΛ hSpec X hX toK r)
    ((RingHom.squareZeroKerRingEquivIso _ _
      (spaceDefoAlgebraEquiv (B := B) (hΛ := hΛ) (hSpec := hSpec) x.left.base)
      (spaceDefoAlgebraEquiv (B := B) (hΛ := hΛ) (hSpec := hSpec) (residueFieldBase Λ k))
      (spaceDefoBaseImmersion_Γ_comp B hΛ hSpec X hX toK x)
      (spaceDefoBaseImmersion_Γ_surjective B hΛ hSpec X hX toK x)
      (spaceDefoBaseImmersion_Γ_ker_sq B hΛ hSpec X hX toK x hsq)
      (residueMap_surjective' x.left.base)
      (ker_residueMap_sq_of_maximalIdeal_sq hsq)).inv.hom v)
  refine Eq.trans ?_
    (sectionsFunctor_map_globalSectionMap_smallEtaleSetRestriction B (Spec (.of Λ)) hΛ
      (spaceDefoThickeningIso B hΛ hSpec X hX toK x hsq).hom
      (isEtale_hom_of_iso B (Spec (.of Λ)) hΛ
        (spaceDefoThickeningIso B hΛ hSpec X hX toK x hsq))
      ((smallEtaleRingedToposHom B (Spec (.of Λ)) hΛ (subspaceInclusion B (Spec (.of Λ)) hΛ
        (spaceTotalSpace B hΛ hSpec x.left)
        (spaceDefoThickening B hΛ hSpec X hX toK x hsq))).toToposHom.inverseImage.globalSectionMap
        (ringOneHom (structureRingSheaf B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec x.left)) ≫
          (moduleSheafFunctor (structureRingSheaf B (Spec (.of Λ)) hΛ
              (spaceTotalSpace B hΛ hSpec x.left))).map
            (unitModuleMul B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec x.left)
              (globalFunctionsOfMap (spaceTotalToBase B hΛ hSpec x.left)
                ((RingHom.squareZeroKerRingEquivIso _ _
                  (spaceDefoAlgebraEquiv (B := B) (hΛ := hΛ) (hSpec := hSpec) x.left.base)
                  (spaceDefoAlgebraEquiv (B := B) (hΛ := hΛ) (hSpec := hSpec)
                    (residueFieldBase Λ k))
                  (spaceDefoBaseImmersion_Γ_comp B hΛ hSpec X hX toK x)
                  (spaceDefoBaseImmersion_Γ_surjective B hΛ hSpec X hX toK x)
                  (spaceDefoBaseImmersion_Γ_ker_sq B hΛ hSpec X hX toK x hsq)
                  (residueMap_surjective' x.left.base)
                  (ker_residueMap_sq_of_maximalIdeal_sq hsq)).inv.hom v).1)))) V p).symm
  refine Eq.trans ?_
    (Deformation.AlgebraExtension.incl_eq_of_ringOneHom_comp_map_comp_inclSheafSets_eq _ _ _ hZ _ _)
  have hv := congrArg (fun m => m.val.app V
      (1 : (structureRingSheaf B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)).obj.obj V)) hL
  refine (castBase_incl B (Spec (.of Λ)) hΛ
    (spaceDefoThickeningIso_hom_comp_retractedStructureMap B hΛ hSpec X hX toK hsq r hr)
    _ _).trans ?_
  refine (etaleRestrictionFunctor_obj_incl B (Spec (.of Λ)) hΛ
    (spaceDefoThickeningIso B hΛ hSpec X hX toK x hsq).hom
    (isEtale_hom_of_iso B (Spec (.of Λ)) hΛ (spaceDefoThickeningIso B hΛ hSpec X hX toK x hsq)) _
    (spaceDefoTensorAlgebraExtension B hΛ hSpec X hX toK x hsq
      (spaceDefoRetractedStructureMap B hΛ hSpec X hX toK r)) _).trans ?_
  refine congrArg (spaceDefoTensorAlgebraExtension B hΛ hSpec X hX toK x hsq
    (spaceDefoRetractedStructureMap B hΛ hSpec X hX toK r)).incl (hv.trans ?_)
  exact modulePullbackGlobalSection_comp_modulePullbackIsoEtaleRestrictionModule_hom_val_app_one B
    (Spec (.of Λ)) hΛ (spaceDefoThickeningIso B hΛ hSpec X hX toK x hsq).hom
    (isEtale_hom_of_iso B (Spec (.of Λ)) hΛ (spaceDefoThickeningIso B hΛ hSpec X hX toK x hsq)) _ V

end Deformation.Examples

end
