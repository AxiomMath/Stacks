module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatPredeformationFiniteTangentClass
public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatDeformationTotalSpaceIso
public import StacksFrontier.Deformation.Examples.Geometric.SpacesTangentSpaceInjectiveTotalSpaceIso

/-!
# Isomorphic extensions of deformations in `Spaces'_{fp, flat, proper}` over a general base

Let `x₀ = (X₀ ⟶ Spec k)` be an object of `Spaces'_{fp, flat, proper}` over the big fppf site of an
arbitrary scheme `S`, and let `x, x'` be two deformations of `x₀` over `k[V]`, with total spaces
`X'₁ ⟶ Spec k[V]` and `X'₂ ⟶ Spec k[V]`. An isomorphism `e` of their extensions
`0 ⟶ 𝒪_{X₀} ⊗_k V ⟶ 𝒪_{X'_j}|_{X₀} ⟶ 𝒪_{X₀} ⟶ 0` of `f₀⁻¹𝒪_{Spec k}`-algebras
(`AlgebraicGeometry.Space.deformationTangentExtension`) gives an isomorphism `X'₁ ≅ X'₂` under
`X₀` and over `Spec k[V]`.

Over `Spec ℤ` this is `AlgebraicGeometry.Space.exists_iso_deformationArrow_comp_eq_of_iso`. Over
an arbitrary base Stacks 05YZ needs the chart morphisms of the isomorphism of ringed topoi to lie
over `S`; they lie over the affine `Spec k[V]`, because `e` pulls back the functions of
`Spec k[V]` along the two structure morphisms to each other: the constants `k ⊆ k[V]` since `e`
is a morphism of `f₀⁻¹𝒪_{Spec k}`-algebras, and `V ⊆ k[V]` since `e` is the identity on the
ideals `𝒪_{X₀} ⊗_k V`
(`AlgebraicGeometry.Space.exists_iso_comp_eq_of_inverseImageStructureSheafIso_of_functions`).
This is the argument of `Deformation.Examples.exists_iso_spaceDefoArrow_comp_eq_of_iso` for the
deformation category of an algebraic space, carried out for deformations in
`Spaces'_{fp, flat, proper}`.

## Main results

* `AlgebraicGeometry.Space.deformationFunctionSectionE_map_retraction`: the global section of the
  middle term of a deformation given by a constant.
* `AlgebraicGeometry.ProperFlatSpaceDeformation.exists_iso_deformationArrow_comp_eq_of_iso`:
  isomorphic extensions give total spaces isomorphic under `X₀` and over `Spec k[V]`.

## References

* [Stacks Project, Tag 0D1K](https://stacks.math.columbia.edu/tag/0D1K)
* [Stacks Project, Tag 05YZ](https://stacks.math.columbia.edu/tag/05YZ)
* [Stacks Project, Tag 05Z1](https://stacks.math.columbia.edu/tag/05Z1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Sheaf
open Deformation Deformation.Artin Deformation.AlgebraExtension

attribute [local instance] MorphismOfTopoi.preservesFiniteLimits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] {iΛ : Spec (.of Λ) ⟶ S}
  {y₀ : CartesianProperFlatSpaces B S hS}
  {hy₀ : (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion).obj y₀ =
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}

/-- Discrete limits of presheaves of sets on the small étale site (instance search times out
without this shortcut). -/
local instance (priority := high) hasLimitsOfShape_discrete_finiteTangentTotalSpace
    (Z : AlgebraicSpaces B S hS) (J : Type u) :
    HasLimitsOfShape (Discrete J) ((smallEtaleRingedTopos B S hS Z).Cᵒᵖ ⥤ Type u) :=
  functorCategoryHasLimitsOfShape

/-- The terminal sheaf of sets on the small étale site (instance search times out without this
shortcut). -/
local instance (priority := high) hasTerminal_topos_finiteTangentTotalSpace
    (Z : AlgebraicSpaces B S hS) :
    HasLimitsOfShape (Discrete PEmpty.{1}) (smallEtaleRingedTopos B S hS Z).Topos :=
  letI : HasLimitsOfShape (Discrete PEmpty.{1}) ((SmallEtale B S hS Z.1)ᵒᵖ ⥤ Type u) :=
    functorCategoryHasLimitsOfShape
  letI : CreatesLimitsOfShape (Discrete PEmpty.{1})
      (sheafToPresheaf (SmallEtale.topology B S hS Z.1) (Type u)) :=
    Sheaf.createsLimitsOfShape
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape
    (sheafToPresheaf (SmallEtale.topology B S hS Z.1) (Type u))

/-! ### The global sections of the middle term given by constants -/

section Retraction

variable {x : DeformationObject iΛ (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion)
    y₀ hy₀}
  (hsq : RingHom.ker (residueMap x.algebra) ^ 2 = ⊥)
  (r : (cartesianProperFlatProjection B S hS).obj x.point ⟶
    (cartesianProperFlatProjection B S hS).obj y₀)
  (hr : (cartesianProperFlatProjection B S hS).map x.arrow ≫ r = 𝟙 _)

/-- Postcomposition with `X₀ ≅ Z` is continuous for the small étale topologies. -/
local instance smallEtalePostcomp_deformationThickeningIso_isContinuous :
    (smallEtalePostcomp B S hS (deformationThickeningIso B S hS x hsq).hom
    (isEtale_hom_of_iso B S hS (deformationThickeningIso B S hS x hsq))).IsContinuous
    (SmallEtale.topology B S hS y₀.obj.obj.left.1)
    (SmallEtale.topology B S hS (deformationFibreSpace B S hS x hsq).1) :=
  smallEtalePostcomp_isContinuous B S hS _ _

/-- Postcomposition with `X₀ ≅ Z` is cocontinuous for the small étale topologies. -/
local instance smallEtalePostcomp_deformationThickeningIso_isCocontinuous :
    (smallEtalePostcomp B S hS (deformationThickeningIso B S hS x hsq).hom
    (isEtale_hom_of_iso B S hS (deformationThickeningIso B S hS x hsq))).IsCocontinuous
    (SmallEtale.topology B S hS y₀.obj.obj.left.1)
    (SmallEtale.topology B S hS (deformationFibreSpace B S hS x hsq).1) :=
  smallEtalePostcomp_isCocontinuous B S hS _ _

/-- **The algebra structure of the extension of a deformation on `X₀`**: through
`f₀ = (θ ≫ i) ≫ g`, the étale restriction along `θ : X₀ ≅ Z` of the inverse image along
`i : Z ⟶ X'` of `g^♯`, `g : X' ⟶ Spec A ⟶ Spec k` the retracted structure morphism. -/
theorem deformationTensorBaseExtension_algebraMap :
    (deformationTensorBaseExtension B S hS hsq r hr).algebraMap =
      eqToHom (congrArg (inverseImageStructureSheaf B S hS)
        (deformationThickeningIso_hom_comp_retractedStructureMap B S hS hsq r hr).symm) ≫
        (etaleRestrictionRingComparison B S hS (deformationThickeningIso B S hS x hsq).hom
          (isEtale_hom_of_iso B S hS (deformationThickeningIso B S hS x hsq))
          (subspaceInclusion B S hS _ (deformationThickening B S hS x hsq) ≫
            deformationRetractedStructureMap B S hS r)).α.hom ≫
        (Deformation.AlgebraExtension.ringRes (SmallEtale.topology B S hS y₀.obj.obj.left.1)
          (smallEtalePostcomp B S hS (deformationThickeningIso B S hS x hsq).hom
            (isEtale_hom_of_iso B S hS (deformationThickeningIso B S hS x hsq)))).map
          (inverseImageStructureSheafMap B S hS
            (subspaceInclusion B S hS _ (deformationThickening B S hS x hsq))
            (deformationRetractedStructureMap B S hS r)) :=
  rfl

/-- **The global section of the middle term given by a constant**: for a retraction
`r : Spec A ⟶ Spec k` and `c ∈ Γ(Spec k)`, the global section of the middle term of the extension
of the deformation given by the function `r^♯c` of its base is the image of `f₀⁻¹c` under the
algebra structure `f₀⁻¹𝒪_{Spec k} ⟶ (i⁻¹𝒪_{X'})|_{X₀}`, on underlying sheaves of sets. -/
theorem deformationFunctionSectionE_map_retraction
    (c : baseRing B S hS ((cartesianProperFlatProjection B S hS).obj y₀)) :
    deformationFunctionSectionE B S hS x hsq
        ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map r).op).hom c) =
      (smallEtaleRingedToposHom B S hS
          (baseStructureMap B S hS (y₀ := y₀))).toToposHom.inverseImage.globalSectionMap
          (functionGlobalSection
            (𝟙 (schemeSpace ((cartesianProperFlatProjection B S hS).obj y₀))) c) ≫
        (sheafCompose (SmallEtale.topology B S hS y₀.obj.obj.left.1) (forget CommRingCat.{u})).map
          (deformationTensorBaseExtension B S hS hsq r hr).algebraMap := by
  have h1 := (globalFunctionsOfMap_comp B S hS (deformationStructureMap B S hS x) r c).symm
  have h2 := ringOneHom_comp_map_unitModuleMul_globalFunctionsOfMap_eq B S hS
    (deformationRetractedStructureMap B S hS r) c
  have h3 := globalSectionMap_comp_forget_map_inverseImageStructureSheafMap B S hS
    ((deformationThickeningIso B S hS x hsq).hom ≫
      subspaceInclusion B S hS _ (deformationThickening B S hS x hsq))
    (deformationRetractedStructureMap B S hS r)
    (functionGlobalSection (𝟙 (schemeSpace ((cartesianProperFlatProjection B S hS).obj y₀))) c)
  have h4 := globalSectionMap_comp_forget_map_eqToHom_inverseImageStructureSheaf B S hS
    ((Category.assoc _ _ _).trans
      (deformationThickeningIso_hom_comp_retractedStructureMap B S hS hsq r hr)).symm
    (functionGlobalSection (𝟙 (schemeSpace ((cartesianProperFlatProjection B S hS).obj y₀))) c)
  have h5 := (Iso.comp_inv_eq _).mp ((Category.assoc _ _ _).trans
    (etaleRestrictionRingComparison_α_map_inverseImageStructureSheafMap B S hS
      (deformationThickeningIso B S hS x hsq).hom
      (isEtale_hom_of_iso B S hS (deformationThickeningIso B S hS x hsq))
      (subspaceInclusion B S hS _ (deformationThickening B S hS x hsq))
      (deformationRetractedStructureMap B S hS r)))
  have hU := (congrArg (fun t => (ringOneHom (structureRingSheaf B S hS
      (deformationSpace B S hS x)) ≫
      (moduleSheafFunctor (structureRingSheaf B S hS (deformationSpace B S hS x))).map
        (unitModuleMul B S hS (deformationSpace B S hS x) t) :
      ⊤_ _ ⟶ (sheafCompose (SmallEtale.topology B S hS (deformationSpace B S hS x).1)
        (forget CommRingCat.{u})).obj (smallEtaleRingedTopos B S hS (deformationSpace B S hS x)).O))
    h1).trans h2
  refine (congrArg (fun t => (smallEtaleRingedToposHom B S hS
      ((deformationThickeningIso B S hS x hsq).hom ≫
        subspaceInclusion B S hS (deformationSpace B S hS x)
          (deformationThickening B S hS x hsq))).toToposHom.inverseImage.globalSectionMap t ≫
    (sheafCompose (SmallEtale.topology B S hS y₀.obj.obj.left.1) (forget CommRingCat.{u})).map
      (etaleRestrictionRingComparison B S hS (deformationThickeningIso B S hS x hsq).hom
        (isEtale_hom_of_iso B S hS (deformationThickeningIso B S hS x hsq))
        (subspaceInclusion B S hS (deformationSpace B S hS x)
          (deformationThickening B S hS x hsq))).α.hom) hU).trans ?_
  refine (congrArg (· ≫ (sheafCompose (SmallEtale.topology B S hS y₀.obj.obj.left.1)
    (forget CommRingCat.{u})).map
      (etaleRestrictionRingComparison B S hS (deformationThickeningIso B S hS x hsq).hom
        (isEtale_hom_of_iso B S hS (deformationThickeningIso B S hS x hsq))
        (subspaceInclusion B S hS (deformationSpace B S hS x)
          (deformationThickening B S hS x hsq))).α.hom) h3.symm).trans ?_
  refine (congrArg (fun t => (t ≫ (sheafCompose (SmallEtale.topology B S hS y₀.obj.obj.left.1)
    (forget CommRingCat.{u})).map (inverseImageStructureSheafMap B S hS
      ((deformationThickeningIso B S hS x hsq).hom ≫
        subspaceInclusion B S hS _ (deformationThickening B S hS x hsq))
      (deformationRetractedStructureMap B S hS r))) ≫
    (sheafCompose (SmallEtale.topology B S hS y₀.obj.obj.left.1) (forget CommRingCat.{u})).map
      (etaleRestrictionRingComparison B S hS (deformationThickeningIso B S hS x hsq).hom
        (isEtale_hom_of_iso B S hS (deformationThickeningIso B S hS x hsq))
        (subspaceInclusion B S hS (deformationSpace B S hS x)
          (deformationThickening B S hS x hsq))).α.hom) h4.symm).trans ?_
  refine (Category.assoc _ _ _).trans ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ?_))
  have hmap : ∀ {P Q R W : Sheaf (SmallEtale.topology B S hS y₀.obj.obj.left.1) CommRingCat.{u}}
      (p : P ⟶ Q) (q : Q ⟶ R) (r' : R ⟶ W) {s : P ⟶ W}, p ≫ q ≫ r' = s →
      (sheafCompose (SmallEtale.topology B S hS y₀.obj.obj.left.1) (forget CommRingCat.{u})).map
          p ≫
        (sheafCompose (SmallEtale.topology B S hS y₀.obj.obj.left.1) (forget CommRingCat.{u})).map
            q ≫
          (sheafCompose (SmallEtale.topology B S hS y₀.obj.obj.left.1)
            (forget CommRingCat.{u})).map r' =
        (sheafCompose (SmallEtale.topology B S hS y₀.obj.obj.left.1)
          (forget CommRingCat.{u})).map s := by
    intro P Q R W p q r' s h
    rw [← h, Functor.map_comp, Functor.map_comp]
  refine (hmap _ _ _ (congrArg (eqToHom _ ≫ ·) h5.symm)).trans ?_
  exact congrArg (sheafCompose (SmallEtale.topology B S hS y₀.obj.obj.left.1)
    (forget CommRingCat.{u})).map
      (deformationTensorBaseExtension_algebraMap B S hS hsq r hr).symm

end Retraction

end AlgebraicGeometry.Space

end
