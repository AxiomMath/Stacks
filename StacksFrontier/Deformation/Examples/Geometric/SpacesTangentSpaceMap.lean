module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatDeformationMapGlobalSection
public import StacksFrontier.Deformation.Examples.Geometric.SpacesTangentSpaceClass

/-!
# Naturality of the class of a deformation of an algebraic space in `V`

Let `φ : x ⟶ x'` be a morphism of the deformation category of an algebraic space `X` over `k`
(Stacks 0E3Z), lying over `A ⟶ A'` in `𝒞_Λ`, with map of total spaces `h : X'_{x'} ⟶ X'_x`. The
inverse image of `h^♯` is a homomorphism of the middle terms of the extensions of `x` and `x'` on
`X`, over `𝒪_X` and, for compatible retractions onto `Spec k`, under `f⁻¹𝒪_{Spec k}`: a morphism
of extensions along the map of ideals it induces. It carries the section of the middle term given
by a function `a` of `Spec A` to the one given by its image in `A'`; so for a morphism over
`k[g] : k[V] ⟶ k[W]` the map of ideals `𝒪_X ⊗_k V ⟶ 𝒪_X ⊗_k W` is `𝒪_X ⊗ g`, and the class of
`x'` is the class of `x` pushed along `𝒪_X ⊗ g`. This is the naturality in `V` of the classes in
the proof of [Stacks Project, Tag 0E41], as for proper flat families.

## Main results

* `Deformation.Examples.spaceTangentKernelMap_eq`: the map of ideals is `𝒪_X ⊗ g`.
* `Deformation.Examples.spaceTangentFiberClass_map`: naturality of the class.

## References

* [Stacks Project, Tag 0E41](https://stacks.math.columbia.edu/tag/0E41)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Space Deformation.Artin Deformation.AlgebraExtension CategoryTheory.Sheaf

attribute [local instance] MorphismOfTopoi.preservesFiniteLimits

universe u

set_option synthInstance.maxHeartbeats 400000 in
/-- Products of presheaves of sets, supplied directly: instance search for them times out. -/
local instance (priority := high) hasProducts_presheaf_SpacesTangentSpaceMap
    (C : Type*) [Category C] : HasProducts.{0} (C ⥤ Type u) :=
  inferInstance

set_option synthInstance.maxHeartbeats 400000 in
/-- Small products of presheaves of sets, supplied directly: instance search for them times
out. -/
local instance (priority := high) hasProducts_presheaf_SpacesTangentSpaceMap'
    (C : Type*) [Category C] : HasProducts.{u} (C ⥤ Type u) :=
  inferInstance

set_option synthInstance.maxHeartbeats 400000 in
/-- Finite limits of sheaves of sets, supplied directly: instance search for them times out. -/
local instance (priority := high) hasFiniteLimits_sheaf_SpacesTangentSpaceMap
    {C : Type*} [Category C] (J : GrothendieckTopology C) :
    HasFiniteLimits (Sheaf J (Type u)) :=
  inferInstance

set_option synthInstance.maxHeartbeats 400000 in
/-- The terminal sheaf of sets, supplied directly: instance search for it times out. -/
local instance (priority := high) hasTerminal_sheaf_SpacesTangentSpaceMap
    {C : Type*} [Category C] (J : GrothendieckTopology C) :
    HasTerminal (Sheaf J (Type u)) :=
  inferInstance

namespace Deformation.Examples

variable {Λ : Type u} {k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable (B : BigFppfSite.{u}) (hΛ : B.Contains (Spec (.of Λ)))
variable (hSpec : ∀ A : ArtinianLocalAlgCat.{u, u, u} Λ k, B.Contains (Spec (.of A)))
variable (X : (BigFppfOver B (Spec (.of Λ)) hΛ)ᵒᵖ ⥤ Type u)
  (hX : IsAlgebraicSpace B (Spec (.of Λ)) hΛ X)
  (toK : X ⟶ yoneda.obj (spaceBaseOver B hΛ hSpec (residueFieldBase Λ k)))

variable {x x' : Over (spaceSpecialFiber B hΛ hSpec X hX toK)} (φ : x ⟶ x')

/-- The map of total spaces `X'_{x'} ⟶ X'_x` of a morphism of the deformation category. -/
abbrev spaceDefoMorphismSpaceMap :
    spaceTotalSpace B hΛ hSpec x'.left ⟶ spaceTotalSpace B hΛ hSpec x.left :=
  ObjectProperty.homMk φ.left.map

/-- The map of total spaces commutes with the structure arrows from `X`. -/
theorem spaceDefoArrow_comp_spaceDefoMorphismSpaceMap :
    spaceDefoArrow B hΛ hSpec X hX toK x' ≫ spaceDefoMorphismSpaceMap B hΛ hSpec X hX toK φ =
      spaceDefoArrow B hΛ hSpec X hX toK x :=
  ObjectProperty.hom_ext _ (spaceSpecialMap_comp B hΛ hSpec X hX toK φ)

/-- The map of total spaces lies over the map of bases. -/
theorem spaceDefoMorphismSpaceMap_comp_structureMap :
    spaceDefoMorphismSpaceMap B hΛ hSpec X hX toK φ ≫ spaceTotalToBase B hΛ hSpec x.left =
      spaceTotalToBase B hΛ hSpec x'.left ≫
        schemeSpaceMap (spaceBaseOverMap B hΛ hSpec φ.left.base) :=
  ObjectProperty.hom_ext _ φ.left.cartesian.w

/-- Retracted structure maps along a morphism, for compatible retractions. -/
theorem spaceDefoMorphismSpaceMap_comp_retractedStructureMap
    (r : spaceBaseOver B hΛ hSpec x.left.base ⟶ spaceBaseOver B hΛ hSpec (residueFieldBase Λ k))
    (r' : spaceBaseOver B hΛ hSpec x'.left.base ⟶ spaceBaseOver B hΛ hSpec (residueFieldBase Λ k))
    (hrr : spaceBaseOverMap B hΛ hSpec φ.left.base ≫ r = r') :
    spaceDefoMorphismSpaceMap B hΛ hSpec X hX toK φ ≫
        spaceDefoRetractedStructureMap B hΛ hSpec X hX toK r =
      spaceDefoRetractedStructureMap B hΛ hSpec X hX toK r' := by
  apply ObjectProperty.hom_ext
  show φ.left.map ≫ x.left.toBase ≫ yoneda.map r = x'.left.toBase ≫ yoneda.map r'
  rw [← Category.assoc, φ.left.cartesian.w, Category.assoc, ← yoneda.map_comp, hrr]

variable (hsq : IsLocalRing.maximalIdeal x.left.base ^ 2 = ⊥)
  (hsq' : IsLocalRing.maximalIdeal x'.left.base ^ 2 = ⊥)

/-- The map of total spaces commutes with the inclusions of the thickenings `X₀ ⟶ X'_{x'}` and
`X₀ ⟶ X'_x`. -/
theorem spaceDefoThickeningIso_comp_spaceDefoMorphismSpaceMap :
    ((spaceDefoThickeningIso B hΛ hSpec X hX toK x' hsq').hom ≫
        subspaceInclusion B (Spec (.of Λ)) hΛ _ (spaceDefoThickening B hΛ hSpec X hX toK x' hsq')) ≫
        spaceDefoMorphismSpaceMap B hΛ hSpec X hX toK φ =
      (spaceDefoThickeningIso B hΛ hSpec X hX toK x hsq).hom ≫
        subspaceInclusion B (Spec (.of Λ)) hΛ _
          (spaceDefoThickening B hΛ hSpec X hX toK x hsq) := by
  rw [spaceDefoThickeningIso_hom_comp_subspaceInclusion,
    spaceDefoThickeningIso_hom_comp_subspaceInclusion,
    spaceDefoArrow_comp_spaceDefoMorphismSpaceMap]

/-- **The homomorphism of middle terms of the extensions of a morphism of deformations**: the
inverse image along `u' : X₀ ⟶ X'_{x'}` of `h^♯`, read on the restrictions of the inverse images
of the structure sheaves to `X₀`. -/
def spaceDefoMiddleMap :=
  etaleRestrictionInverseImageMap B (Spec (.of Λ)) hΛ _
    (isEtale_hom_of_iso B (Spec (.of Λ)) hΛ _) _ _
    (isEtale_hom_of_iso B (Spec (.of Λ)) hΛ _) _ (spaceDefoMorphismSpaceMap B hΛ hSpec X hX toK φ)
    (spaceDefoThickeningIso_comp_spaceDefoMorphismSpaceMap B hΛ hSpec X hX toK φ hsq hsq')

variable {hsq} (r : spaceBaseOver B hΛ hSpec x.left.base ⟶
    spaceBaseOver B hΛ hSpec (residueFieldBase Λ k))
  (hr : spaceDefoBaseImmersion B hΛ hSpec X hX toK x ≫ r = 𝟙 _)

variable (r' : spaceBaseOver B hΛ hSpec x'.left.base ⟶
    spaceBaseOver B hΛ hSpec (residueFieldBase Λ k))
  (hr' : spaceDefoBaseImmersion B hΛ hSpec X hX toK x' ≫ r' = 𝟙 _)

/-- The homomorphism of middle terms of a morphism of deformations is over `𝒪_{X₀}`. -/
theorem spaceDefoMiddleMap_comp_reduction :
    spaceDefoMiddleMap B hΛ hSpec X hX toK φ hsq hsq' ≫
        (spaceDefoTensorBaseExtension B hΛ hSpec X hX toK hsq' r' hr').reduction =
      (spaceDefoTensorBaseExtension B hΛ hSpec X hX toK hsq r hr).reduction :=
  etaleRestrictionInverseImageMap_comp_reduction B (Spec (.of Λ)) hΛ _ _ _ _ _ _ _ _

variable (hg : spaceDefoMorphismSpaceMap B hΛ hSpec X hX toK φ ≫
      spaceDefoRetractedStructureMap B hΛ hSpec X hX toK r =
    spaceDefoRetractedStructureMap B hΛ hSpec X hX toK r')

include hg in
/-- The homomorphism of middle terms of a morphism of deformations is under
`f₀⁻¹𝒪_{Spec k}` when the retractions onto `Spec k` are compatible. -/
theorem algebraMap_comp_spaceDefoMiddleMap :
    (spaceDefoTensorBaseExtension B hΛ hSpec X hX toK hsq r hr).algebraMap ≫
        spaceDefoMiddleMap B hΛ hSpec X hX toK φ hsq hsq' =
      (spaceDefoTensorBaseExtension B hΛ hSpec X hX toK hsq' r' hr').algebraMap := by
  have L := etaleRestrictionInverseImageMap_algebraMap B (Spec (.of Λ)) hΛ _
    (isEtale_hom_of_iso B (Spec (.of Λ)) hΛ _) _ _
    (isEtale_hom_of_iso B (Spec (.of Λ)) hΛ _) _ _
    (spaceDefoThickeningIso_comp_spaceDefoMorphismSpaceMap B hΛ hSpec X hX toK φ hsq hsq') _ _ hg
      ((spaceDefoThickeningIso_hom_comp_retractedStructureMap B hΛ hSpec X hX toK hsq r hr).trans
        (spaceDefoThickeningIso_hom_comp_retractedStructureMap B hΛ hSpec X hX toK hsq' r'
          hr').symm)
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans L)).trans ?_
  refine (eqToHom_trans_assoc _ _ _).trans ?_
  rfl

/-- **The morphism of extensions of a morphism of deformations**, along the map of ideals induced
by `AlgebraicGeometry.Space.deformationMiddleMap`. -/
def spaceDefoBaseMapAlong :
    MapAlong.{u, u + 1, u} (J := SmallEtale.topology B (Spec (.of Λ)) hΛ X)
      (inducedKernelMap.{u, u + 1, u} (J := SmallEtale.topology B (Spec (.of Λ)) hΛ X)
        (spaceDefoTensorBaseExtension B hΛ hSpec X hX toK hsq r hr)
        (spaceDefoTensorBaseExtension B hΛ hSpec X hX toK hsq' r' hr')
        (spaceDefoMiddleMap B hΛ hSpec X hX toK φ hsq hsq')
        (spaceDefoMiddleMap_comp_reduction B hΛ hSpec X hX toK φ hsq' r hr r' hr'))
      (spaceDefoTensorBaseExtension B hΛ hSpec X hX toK hsq r hr)
      (spaceDefoTensorBaseExtension B hΛ hSpec X hX toK hsq' r' hr') :=
  mapAlongInducedKernelMap.{u, u + 1, u} (J := SmallEtale.topology B (Spec (.of Λ)) hΛ X)
    _ _ _ _ (algebraMap_comp_spaceDefoMiddleMap B hΛ hSpec X hX toK φ hsq' r hr r' hr' hg)

/-! ### Over `k[V]` -/
variable (hsq)

/-- **The global section of the middle term of a deformation given by a function of its base**:
for `a ∈ Γ(Spec A)`, the étale restriction to `X₀ ≅ Z` of the inverse image along `i : Z ⟶ X'` of
the global section `g^♯a` of `𝒪_{X'}`, `g : X' ⟶ Spec A` the structure morphism, on underlying
sheaves of sets. -/
abbrev spaceDefoFunctionSection
    (x : Over (spaceSpecialFiber B hΛ hSpec X hX toK))
    (hsq : IsLocalRing.maximalIdeal x.left.base ^ 2 = ⊥)
    (a : baseRing B (Spec (.of Λ)) hΛ (spaceBaseOver B hΛ hSpec x.left.base)) :=
  (smallEtaleSetRestriction B (Spec (.of Λ)) hΛ
    (spaceDefoThickeningIso B hΛ hSpec X hX toK x hsq).hom
    (isEtale_hom_of_iso B (Spec (.of Λ)) hΛ
      (spaceDefoThickeningIso B hΛ hSpec X hX toK x hsq))).globalSectionMap
    ((smallEtaleRingedToposHom B (Spec (.of Λ)) hΛ
        (subspaceInclusion B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec x.left)
          (spaceDefoThickening B hΛ hSpec X hX toK x
            hsq))).toToposHom.inverseImage.globalSectionMap
      (ringOneHom (structureRingSheaf B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec x.left)) ≫
        (moduleSheafFunctor
          (structureRingSheaf B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec x.left))).map
          (unitModuleMul B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec x.left)
            (globalFunctionsOfMap (spaceTotalToBase B hΛ hSpec x.left) a))))

/-- Postcomposition with the étale isomorphism `X₀ ≅ Z` is continuous for the small étale
topologies. -/
local instance (x : Over (spaceSpecialFiber B hΛ hSpec X hX toK))
    (hsq : IsLocalRing.maximalIdeal x.left.base ^ 2 = ⊥) :
    (smallEtalePostcomp B (Spec (.of Λ)) hΛ (spaceDefoThickeningIso B hΛ hSpec X hX toK x hsq).hom
    (isEtale_hom_of_iso B (Spec (.of Λ)) hΛ
      (spaceDefoThickeningIso B hΛ hSpec X hX toK x hsq))).IsContinuous
    (SmallEtale.topology B (Spec (.of Λ)) hΛ X)
    (SmallEtale.topology B (Spec (.of Λ)) hΛ (spaceDefoFibreSpace B hΛ hSpec X hX toK x hsq).1) :=
  smallEtalePostcomp_isContinuous B (Spec (.of Λ)) hΛ _ _

/-- Postcomposition with the étale isomorphism `X₀ ≅ Z` is cocontinuous for the small étale
topologies. -/
local instance (x : Over (spaceSpecialFiber B hΛ hSpec X hX toK))
    (hsq : IsLocalRing.maximalIdeal x.left.base ^ 2 = ⊥) :
    (smallEtalePostcomp B (Spec (.of Λ)) hΛ (spaceDefoThickeningIso B hΛ hSpec X hX toK x hsq).hom
    (isEtale_hom_of_iso B (Spec (.of Λ)) hΛ
      (spaceDefoThickeningIso B hΛ hSpec X hX toK x hsq))).IsCocontinuous
    (SmallEtale.topology B (Spec (.of Λ)) hΛ X)
    (SmallEtale.topology B (Spec (.of Λ)) hΛ (spaceDefoFibreSpace B hΛ hSpec X hX toK x hsq).1) :=
  smallEtalePostcomp_isCocontinuous B (Spec (.of Λ)) hΛ _ _

/-- The global section of the middle term given by a function `a` of the base, read through
`(e ≫ i)⁻¹𝒪_{X'} ≅ (i⁻¹𝒪_{X'})|_{X₀}`. -/
theorem spaceDefoFunctionSection_eq
    (x : Over (spaceSpecialFiber B hΛ hSpec X hX toK))
    (hsq : IsLocalRing.maximalIdeal x.left.base ^ 2 = ⊥)
    (a : baseRing B (Spec (.of Λ)) hΛ (spaceBaseOver B hΛ hSpec x.left.base)) :
    spaceDefoFunctionSection B hΛ hSpec X hX toK x hsq a =
      (smallEtaleRingedToposHom B (Spec (.of Λ)) hΛ
          ((spaceDefoThickeningIso B hΛ hSpec X hX toK x hsq).hom ≫
          subspaceInclusion B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec x.left)
            (spaceDefoThickening B hΛ hSpec X hX toK x
              hsq))).toToposHom.inverseImage.globalSectionMap
          (ringOneHom (structureRingSheaf B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec x.left)) ≫
            (moduleSheafFunctor
              (structureRingSheaf B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec x.left))).map
              (unitModuleMul B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec x.left)
                (globalFunctionsOfMap (spaceTotalToBase B hΛ hSpec x.left) a)) :
            ⊤_ _ ⟶ (sheafCompose
              (SmallEtale.topology B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec x.left).1)
              (forget CommRingCat.{u})).obj
                (smallEtaleRingedTopos B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec x.left)).O) ≫
        (sheafCompose (SmallEtale.topology B (Spec (.of Λ)) hΛ X) (forget CommRingCat.{u})).map
          (etaleRestrictionRingComparison B (Spec (.of Λ)) hΛ
            (spaceDefoThickeningIso B hΛ hSpec X hX toK x hsq).hom
            (isEtale_hom_of_iso B (Spec (.of Λ)) hΛ
              (spaceDefoThickeningIso B hΛ hSpec X hX toK x hsq))
            (subspaceInclusion B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec x.left)
              (spaceDefoThickening B hΛ hSpec X hX toK x hsq))).α.hom :=
  (globalSectionMap_comp_forget_map_etaleRestrictionRingComparison_α_hom B (Spec (.of Λ)) hΛ
    (spaceDefoThickeningIso B hΛ hSpec X hX toK x hsq).hom
    (isEtale_hom_of_iso B (Spec (.of Λ)) hΛ (spaceDefoThickeningIso B hΛ hSpec X hX toK x hsq))
    (subspaceInclusion B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec x.left)
      (spaceDefoThickening B hΛ hSpec X hX toK x hsq))
    _).symm

/-- `AlgebraicGeometry.Space.deformationFunctionSection` read through
`(e ≫ i)⁻¹𝒪_{X'} ≅ (i⁻¹𝒪_{X'})|_{X₀}`, as a global section of the restricted inverse image of the
structure sheaf (the middle term of the extension of the deformation). -/
abbrev spaceDefoFunctionSectionE
    (x : Over (spaceSpecialFiber B hΛ hSpec X hX toK))
    (hsq : IsLocalRing.maximalIdeal x.left.base ^ 2 = ⊥)
    (a : baseRing B (Spec (.of Λ)) hΛ (spaceBaseOver B hΛ hSpec x.left.base)) :=
  (smallEtaleRingedToposHom B (Spec (.of Λ)) hΛ
      ((spaceDefoThickeningIso B hΛ hSpec X hX toK x hsq).hom ≫
      subspaceInclusion B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec x.left)
        (spaceDefoThickening B hΛ hSpec X hX toK x hsq))).toToposHom.inverseImage.globalSectionMap
      (ringOneHom (structureRingSheaf B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec x.left)) ≫
        (moduleSheafFunctor
          (structureRingSheaf B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec x.left))).map
          (unitModuleMul B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec x.left)
            (globalFunctionsOfMap (spaceTotalToBase B hΛ hSpec x.left) a)) :
        ⊤_ _ ⟶ (sheafCompose
          (SmallEtale.topology B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec x.left).1)
          (forget CommRingCat.{u})).obj
            (smallEtaleRingedTopos B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec x.left)).O) ≫
    (sheafCompose (SmallEtale.topology B (Spec (.of Λ)) hΛ X) (forget CommRingCat.{u})).map
      (etaleRestrictionRingComparison B (Spec (.of Λ)) hΛ
        (spaceDefoThickeningIso B hΛ hSpec X hX toK x hsq).hom
        (isEtale_hom_of_iso B (Spec (.of Λ)) hΛ (spaceDefoThickeningIso B hΛ hSpec X hX toK x hsq))
        (subspaceInclusion B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec x.left)
          (spaceDefoThickening B hΛ hSpec X hX toK x hsq))).α.hom

/-- **The map of middle terms of a morphism of deformations on functions of the base**: for a
morphism `φ : x ⟶ x'` of deformations over `ρ : A ⟶ A'` and `a ∈ Γ(Spec A)`,
`AlgebraicGeometry.Space.deformationMiddleMap` carries the global section of the middle term of
`x` given by `a` to that of `x'` given by `ρ(a)`, on underlying sheaves of sets. -/
theorem spaceDefoFunctionSection_comp_forget_map_spaceDefoMiddleMap
    (a : baseRing B (Spec (.of Λ)) hΛ (spaceBaseOver B hΛ hSpec x.left.base)) :
    spaceDefoFunctionSection B hΛ hSpec X hX toK x hsq a ≫
        (sheafCompose (SmallEtale.topology B (Spec (.of Λ)) hΛ X) (forget CommRingCat.{u})).map
          (spaceDefoMiddleMap B hΛ hSpec X hX toK φ hsq hsq') =
      spaceDefoFunctionSection B hΛ hSpec X hX toK x' hsq'
        ((Scheme.Γ.map ((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map
          (spaceBaseOverMap B hΛ hSpec φ.left.base)).op).hom a) := by
  have hI := globalSectionMap_comp_forget_map_etaleRestrictionInverseImageMap B (Spec (.of Λ)) hΛ
    (spaceDefoThickeningIso B hΛ hSpec X hX toK x hsq).hom
    (isEtale_hom_of_iso B (Spec (.of Λ)) hΛ (spaceDefoThickeningIso B hΛ hSpec X hX toK x hsq))
    (subspaceInclusion B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec x.left)
      (spaceDefoThickening B hΛ hSpec X hX toK x hsq))
    (spaceDefoThickeningIso B hΛ hSpec X hX toK x' hsq').hom
    (isEtale_hom_of_iso B (Spec (.of Λ)) hΛ (spaceDefoThickeningIso B hΛ hSpec X hX toK x' hsq'))
    (subspaceInclusion B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec x'.left)
      (spaceDefoThickening B hΛ hSpec X hX toK x' hsq'))
    (spaceDefoMorphismSpaceMap B hΛ hSpec X hX toK φ)
    (spaceDefoThickeningIso_comp_spaceDefoMorphismSpaceMap B hΛ hSpec X hX toK φ hsq hsq')
    (ringOneHom (structureRingSheaf B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec x.left)) ≫
      (moduleSheafFunctor
        (structureRingSheaf B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec x.left))).map
        (unitModuleMul B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec x.left)
          (globalFunctionsOfMap (spaceTotalToBase B hΛ hSpec x.left) a)))
  have hC := globalSectionMap_unitModuleMul_globalFunctionsOfMap_comp_structureSharpInverseImage
    B (Spec (.of Λ)) hΛ (spaceDefoMorphismSpaceMap B hΛ hSpec X hX toK φ)
    (spaceTotalToBase B hΛ hSpec x.left) a
  have hF : globalFunctionsOfMap (spaceDefoMorphismSpaceMap B hΛ hSpec X hX toK φ ≫
      spaceTotalToBase B hΛ hSpec x.left) a =
      globalFunctionsOfMap (spaceTotalToBase B hΛ hSpec x'.left)
        ((Scheme.Γ.map ((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map
          (spaceBaseOverMap B hΛ hSpec φ.left.base)).op).hom a) :=
    (congrArg (fun f : spaceTotalSpace B hΛ hSpec x'.left ⟶
        schemeSpace (spaceBaseOver B hΛ hSpec x.left.base) =>
        globalFunctionsOfMap f a)
      (spaceDefoMorphismSpaceMap_comp_structureMap B hΛ hSpec X hX toK φ)).trans
      (globalFunctionsOfMap_comp B (Spec (.of Λ)) hΛ _ _ a)
  refine (congrArg (· ≫ (sheafCompose (SmallEtale.topology B (Spec (.of Λ)) hΛ X)
    (forget CommRingCat.{u})).map (spaceDefoMiddleMap B hΛ hSpec X hX toK φ hsq hsq'))
    (spaceDefoFunctionSection_eq B hΛ hSpec X hX toK x hsq a)).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) ((sheafCompose (SmallEtale.topology B (Spec (.of Λ)) hΛ X)
    (forget CommRingCat.{u})).map_comp _ _).symm).trans ?_
  refine hI.trans ?_
  refine Eq.trans ?_ (spaceDefoFunctionSection_eq B hΛ hSpec X hX toK x' hsq' _).symm
  refine congrArg (fun t => (smallEtaleRingedToposHom B (Spec (.of Λ)) hΛ
      ((spaceDefoThickeningIso B hΛ hSpec X hX toK x' hsq').hom ≫
        subspaceInclusion B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec x'.left)
          (spaceDefoThickening B hΛ hSpec X hX toK x'
            hsq'))).toToposHom.inverseImage.globalSectionMap t ≫
      (sheafCompose (SmallEtale.topology B (Spec (.of Λ)) hΛ X) (forget CommRingCat.{u})).map
        (etaleRestrictionRingComparison B (Spec (.of Λ)) hΛ
          (spaceDefoThickeningIso B hΛ hSpec X hX toK x' hsq').hom
          (isEtale_hom_of_iso B (Spec (.of Λ)) hΛ
            (spaceDefoThickeningIso B hΛ hSpec X hX toK x' hsq'))
          (subspaceInclusion B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec x'.left)
            (spaceDefoThickening B hΛ hSpec X hX toK x' hsq'))).α.hom) (hC.trans ?_)
  exact congrArg (fun r =>
    ringOneHom (structureRingSheaf B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec x'.left)) ≫
    (moduleSheafFunctor
      (structureRingSheaf B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec x'.left))).map
      (unitModuleMul B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec x'.left) r)) hF

/-- `AlgebraicGeometry.Space.deformationFunctionSection_comp_forget_map_spaceDefoMiddleMap`,
read through `(e ≫ i)⁻¹𝒪_{X'} ≅ (i⁻¹𝒪_{X'})|_{X₀}`. -/
theorem spaceDefoFunctionSectionE_comp_forget_map_spaceDefoMiddleMap
    (a : baseRing B (Spec (.of Λ)) hΛ (spaceBaseOver B hΛ hSpec x.left.base)) :
    spaceDefoFunctionSectionE B hΛ hSpec X hX toK x hsq a ≫
        (sheafCompose (SmallEtale.topology B (Spec (.of Λ)) hΛ X) (forget CommRingCat.{u})).map
          (spaceDefoMiddleMap B hΛ hSpec X hX toK φ hsq hsq') =
      spaceDefoFunctionSectionE B hΛ hSpec X hX toK x' hsq'
        ((Scheme.Γ.map ((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map
          (spaceBaseOverMap B hΛ hSpec φ.left.base)).op).hom a) :=
  ((congrArg (· ≫ (sheafCompose (SmallEtale.topology B (Spec (.of Λ)) hΛ X)
      (forget CommRingCat.{u})).map (spaceDefoMiddleMap B hΛ hSpec X hX toK φ hsq hsq'))
      (spaceDefoFunctionSection_eq B hΛ hSpec X hX toK x hsq a)).symm.trans
    (spaceDefoFunctionSection_comp_forget_map_spaceDefoMiddleMap B hΛ hSpec X hX toK φ hsq hsq'
      a)).trans
    (spaceDefoFunctionSection_eq B hΛ hSpec X hX toK x' hsq' _)


end Deformation.Examples

end
