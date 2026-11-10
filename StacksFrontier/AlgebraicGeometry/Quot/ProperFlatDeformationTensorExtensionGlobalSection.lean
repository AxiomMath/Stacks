module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatDeformationTensorExtension
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalFunctionsOfMapGlobalSectionSets
public import
  StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleRestrictionInverseImageGlobalSection
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ConormalInverseImageGlobalSectionSets
public import StacksFrontier.Deformation.AlgebraExtension.KernelGlobalSectionSets

/-!
# The sections `1 ⊗ a` of the ideal of a deformation, on sheaves of sets

Let `X' ⟶ Spec A` be a deformation whose residue kernel `I` squares to zero, `Z ⊆ X'` its closed
fibre and `i : Z ⟶ X'` the inclusion. In the extension
`AlgebraicGeometry.Space.deformationTensorAlgebraExtension` of `𝒪_Z` by `𝒪_Z ⊗_R I`, the section
`1 ⊗ a` of the ideal is included into `i⁻¹𝒪_{X'}` as the inverse image along `i` of the function
`g^♯a` of `X'`, `g : X' ⟶ Spec A` the structure morphism, on underlying sheaves of sets. This is
the computation of the kernel map of a morphism of deformations in the proof of Stacks 0D1K.

## Main results

* `ringOneHom_comp_map_baseRingTensorSection_comp_deformationTensorAlgebraExtension_inclSheafSets`

## References

* [Stacks Project, Tag 0D1K](https://stacks.math.columbia.edu/tag/0D1K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

attribute [local instance] MorphismOfTopoi.preservesFiniteLimits

universe u

namespace Deformation.AlgebraExtension

variable {C : Type*} [Category C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.HasSheafCompose (forget RingCat.{u})] [J.HasSheafCompose (forget AddCommGrpCat.{u})]
  {A O : Sheaf J CommRingCat.{u}} {a : A ⟶ O}
  {M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O)}

/-- **The image in the middle term of a global section of the kernel, compared sectionwise**: if
the inclusion of `w` at `1` agrees on every object with `ι` applied to a global section `w'` of
an `R`-module restricted along `φ : 𝒪' ⟶ R`, the two global sections `⊤ ⟶ 𝒪'` agree. -/
theorem ringOneHom_comp_map_comp_inclSheafSets_eq_of_incl (P : AlgebraExtension a M)
    (w : SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O) ⟶ M)
    {R : Sheaf J RingCat.{u}}
    (φ : (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj P.extension ⟶ R)
    {N : SheafOfModules.{u} R} (w' : SheafOfModules.unit R ⟶ N)
    (ι : (SheafOfModules.restrictScalars φ).obj N ⟶
      SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj P.extension))
    (h : ∀ U : Cᵒᵖ, P.incl (w.val.app U
        (1 : ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O).obj.obj U)) =
      ι.val.app U (w'.val.app U (1 : R.obj.obj U))) :
    ringOneHom ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O) ≫
        (moduleSheafFunctor ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O)).map
          w ≫ P.inclSheafSets =
      ringOneHom R ≫ (moduleSheafFunctor ((sheafCompose J
        (forget₂ CommRingCat.{u} RingCat.{u})).obj P.extension)).map
          ((SheafOfModules.restrictScalars φ).map w' ≫ ι) :=
  hom_ext_sections fun U _ => h U


set_option synthInstance.maxHeartbeats 400000 in
-- `HasLimitsOfShape (Discrete J) (Cᵒᵖ ⥤ Type u)` (for `⊤_ Sheaf J (Type u)`) exceeds the
-- default typeclass budget
set_option maxHeartbeats 800000 in
-- elaborating the nested `sheafCompose`/`forget₂` sheaf-of-modules terms is heavy
/-- **A global section of the kernel read in the middle term, sectionwise**: the image in the
middle term of a global section `w` of the kernel is a global section `z` as soon as the inclusion
of the value of `w` at `1` is the value of `z`, over every object. -/
theorem ringOneHom_comp_map_comp_inclSheafSets_eq_of_forall (P : AlgebraExtension a M)
    (w : SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O) ⟶ M)
    (z : ⊤_ Sheaf J (Type u) ⟶
      Sheaf.ringSheaf ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj P.extension))
    (h : ∀ (U : Cᵒᵖ) (p : (sectionsFunctor J U).obj (⊤_ Sheaf J (Type u))),
      P.incl (w.val.app U
        (1 : ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O).obj.obj U)) =
        (sectionsFunctor J U).map z p) :
    ringOneHom ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O) ≫
        (moduleSheafFunctor ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O)).map
          w ≫ P.inclSheafSets = z :=
  hom_ext_sections fun U p => h U p


set_option synthInstance.maxHeartbeats 400000 in
-- `HasLimitsOfShape (Discrete J) (Cᵒᵖ ⥤ Type u)` (for `⊤_ Sheaf J (Type u)`) exceeds the
-- default typeclass budget
set_option maxHeartbeats 800000 in
-- elaborating the nested `sheafCompose`/`forget₂` sheaf-of-modules terms is heavy
/-- `Deformation.AlgebraExtension.ringOneHom_comp_map_comp_inclSheafSets_eq_of_forall`, with the
middle term read through the forgetful functor of commutative rings. -/
theorem ringOneHom_comp_map_comp_inclSheafSets_eq_of_forall_commRing
    [J.HasSheafCompose (forget CommRingCat.{u})] (P : AlgebraExtension a M)
    (w : SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O) ⟶ M)
    (z : ⊤_ Sheaf J (Type u) ⟶ (sheafCompose J (forget CommRingCat.{u})).obj P.extension)
    (h : ∀ (U : Cᵒᵖ) (p : (sectionsFunctor J U).obj (⊤_ Sheaf J (Type u))),
      P.incl (w.val.app U
        (1 : ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O).obj.obj U)) =
        (sectionsFunctor J U).map z p) :
    ringOneHom ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O) ≫
        (moduleSheafFunctor ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O)).map
          w ≫ P.inclSheafSets = z :=
  hom_ext_sections fun U p => h U p

set_option synthInstance.maxHeartbeats 400000 in
-- `HasLimitsOfShape (Discrete J) (Cᵒᵖ ⥤ Type u)` (for `⊤_ Sheaf J (Type u)`) exceeds the
-- default typeclass budget
set_option maxHeartbeats 800000 in
-- elaborating the nested `sheafCompose`/`forget₂` sheaf-of-modules terms is heavy
/-- The converse reading: if the image in the middle term of a global section `w` of the kernel
is `z`, the inclusion of the value of `w` at `1` is the value of `z`, over every object. -/
theorem incl_eq_of_ringOneHom_comp_map_comp_inclSheafSets_eq (P : AlgebraExtension a M)
    (w : SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O) ⟶ M)
    (z : ⊤_ Sheaf J (Type u) ⟶
      Sheaf.ringSheaf ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj P.extension))
    (h : ringOneHom ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O) ≫
        (moduleSheafFunctor ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O)).map
          w ≫ P.inclSheafSets = z)
    (U : Cᵒᵖ) (p : (sectionsFunctor J U).obj (⊤_ Sheaf J (Type u))) :
    P.incl (w.val.app U
        (1 : ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O).obj.obj U)) =
      (sectionsFunctor J U).map z p :=
  sectionsFunctor_map_congr h U p

end Deformation.AlgebraExtension


namespace AlgebraicGeometry.Space

open Deformation.Artin

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] {iΛ : Spec (.of Λ) ⟶ S}
  {y₀ : CartesianProperFlatSpaces B S hS}
  {hy₀ : (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion).obj y₀ =
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
  (x : DeformationObject iΛ (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion) y₀ hy₀)
  (hsq : RingHom.ker (residueMap x.algebra) ^ 2 = ⊥)

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for these limits on the small étale site is slow
/-- Discrete limits of presheaves of sets on the small étale site (instance search times out
without this shortcut). -/
local instance (priority := high)
    hasLimitsOfShape_discrete_ProperFlatDeformationTensorExtensionGlobalSection
    (Z : AlgebraicSpaces B S hS) (J : Type u) :
    HasLimitsOfShape (Discrete J) ((smallEtaleRingedTopos B S hS Z).Cᵒᵖ ⥤ Type u) :=
  inferInstance

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for these limits on the small étale site is slow
/-- The terminal sheaf of sets on the small étale site (instance search times out without this
shortcut). -/
local instance (priority := high)
    hasLimitsOfShape_pEmpty_topos_ProperFlatDeformationTensorExtensionGlobalSection
    (Z : AlgebraicSpaces B S hS) :
    HasLimitsOfShape (Discrete PEmpty.{1}) (smallEtaleRingedTopos B S hS Z).Topos :=
  haveI : HasLimitsOfShape (Discrete PEmpty.{1})
      ((SmallEtale B S hS Z.1)ᵒᵖ ⥤ Type u) :=
    functorCategoryHasLimitsOfShape
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape
    (sheafToPresheaf (SmallEtale.topology B S hS Z.1) (Type u))

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for these limits on the small étale site is slow
/-- Discrete limits of presheaves of sets on the small étale site (instance search times out
without this shortcut). -/
local instance (priority := high)
    hasLimitsOfShape_discreteF_ProperFlatDeformationTensorExtensionGlobalSection
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (J : Type u) :
    HasLimitsOfShape (Discrete J) ((SmallEtale B S hS F)ᵒᵖ ⥤ Type u) :=
  inferInstance

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for these limits on the small étale site is slow
/-- Discrete limits indexed by `Type` of presheaves of sets on the small étale site (instance
search times out without this shortcut). -/
local instance (priority := high)
    hasLimitsOfShape_discrete₀_ProperFlatDeformationTensorExtensionGlobalSection
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (J : Type) :
    HasLimitsOfShape (Discrete J) ((SmallEtale B S hS F)ᵒᵖ ⥤ Type u) :=
  inferInstance

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for these limits on the small étale site is slow
/-- Discrete limits of sheaves of sets on the small étale site (instance search times out
without this shortcut). -/
local instance (priority := high)
    hasDiscreteLimits_topos_ProperFlatDeformationTensorExtensionGlobalSection
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (J : Type) :
    HasLimitsOfShape (Discrete J) (Sheaf (SmallEtale.topology B S hS F) (Type u)) :=
  letI : HasLimitsOfShape (Discrete J) (Type u) := inferInstance
  letI : HasLimitsOfShape (Discrete J) ((SmallEtale B S hS F)ᵒᵖ ⥤ Type u) :=
    hasLimitsOfShape_discrete₀_ProperFlatDeformationTensorExtensionGlobalSection B S hS F J
  letI : CreatesLimitsOfShape (Discrete J)
      (sheafToPresheaf (SmallEtale.topology B S hS F) (Type u)) :=
    Sheaf.createsLimitsOfShape
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape
    (sheafToPresheaf (SmallEtale.topology B S hS F) (Type u))

/-- The terminal sheaf of sets on the small étale site (instance search times out without this
shortcut). -/
local instance (priority := high)
    hasTerminal_topos_ProperFlatDeformationTensorExtensionGlobalSection
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    HasTerminal (Sheaf (SmallEtale.topology B S hS F) (Type u)) :=
  hasDiscreteLimits_topos_ProperFlatDeformationTensorExtensionGlobalSection B S hS F PEmpty

set_option maxHeartbeats 800000 in
-- the statement and the final `exact` elaborate large explicit sheaf-of-modules terms
/-- **The section `1 ⊗ a` of the ideal of a deformation, on sheaves of sets**: in the extension
`AlgebraicGeometry.Space.deformationTensorAlgebraExtension`, the unit section followed by `1 ⊗ a`
and the inclusion of the ideal into `i⁻¹𝒪_{X'}` is the inverse image along the inclusion
`i : Z ⟶ X'` of the closed fibre of the global section `g^♯a` of `𝒪_{X'}`, `g : X' ⟶ Spec A` the
structure morphism. -/
theorem
    ringOneHom_comp_map_baseRingTensorSection_comp_deformationTensorAlgebraExtension_inclSheafSets
    {Y : AlgebraicSpaces B S hS} (g : deformationSpace B S hS x ⟶ Y)
    (a : deformationBaseKernel B S hS x hsq) :
    ringOneHom ((sheafCompose (SmallEtale.topology B S hS
          (deformationThickening B S hS x hsq).1.toFunctor)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj
          (smallEtaleRingedTopos B S hS (deformationFibreSpace B S hS x hsq)).O) ≫
        (moduleSheafFunctor ((sheafCompose (SmallEtale.topology B S hS
          (deformationThickening B S hS x hsq).1.toFunctor)
          (forget₂ CommRingCat.{u} RingCat.{u})).obj
            (smallEtaleRingedTopos B S hS (deformationFibreSpace B S hS x hsq)).O)).map
          (baseRingTensorSection B S hS (deformationFibreSpace B S hS x hsq)
            (baseRingHomOfMap (deformationFibreBaseProjection B S hS x hsq))
            (deformationBaseKernel B S hS x hsq) a) ≫
        (deformationTensorAlgebraExtension B S hS x hsq g).inclSheafSets =
      (thickeningToposHom B S hS (deformationThickening B S hS x hsq)).inverseImage.globalSectionMap
        (ringOneHom (structureRingSheaf B S hS (deformationSpace B S hS x)) ≫
          (moduleSheafFunctor (structureRingSheaf B S hS (deformationSpace B S hS x))).map
            (unitModuleMul B S hS (deformationSpace B S hS x)
              (globalFunctionsOfMap (deformationStructureMap B S hS x) a.1))) := by
  have hc := ringOneHom_comp_map_conormalInverseImageι_modulePullbackGlobalSection B S hS
    (deformationThickening B S hS x hsq)
    (isFirstOrderThickening_deformationThickening B S hS x hsq)
    (preimageIdealSection B S hS (deformationStructureMap B S hS x)
      (rangeSubspace B S hS (deformationBaseImmersion B S hS x)
        (isClosedImmersion_deformationBaseImmersion B S hS x hsq))
      ⟨a.1, (closedSubspaceBaseIdeal_rangeSubspace B S hS (deformationBaseImmersion B S hS x)
        (isClosedImmersion_deformationBaseImmersion B S hS x hsq)).symm ▸ a.2⟩)
  have hs' : preimageIdealSection B S hS (deformationStructureMap B S hS x)
      (rangeSubspace B S hS (deformationBaseImmersion B S hS x)
        (isClosedImmersion_deformationBaseImmersion B S hS x hsq))
      ⟨a.1, (closedSubspaceBaseIdeal_rangeSubspace B S hS (deformationBaseImmersion B S hS x)
        (isClosedImmersion_deformationBaseImmersion B S hS x hsq)).symm ▸ a.2⟩ ≫
      (definingIdealSheaf B S hS (deformationSpace B S hS x)
        (deformationThickening B S hS x hsq)).ι =
      unitModuleMul B S hS (deformationSpace B S hS x)
        (globalFunctionsOfMap (deformationStructureMap B S hS x) a.1) :=
    preimageIdealSection_ι B S hS _ _ _
  have hm := congrArg (fun m : SheafOfModules.unit (structureRingSheaf B S hS
      (deformationSpace B S hS x)) ⟶ SheafOfModules.unit (structureRingSheaf B S hS
      (deformationSpace B S hS x)) =>
    (thickeningToposHom B S hS (deformationThickening B S hS x hsq)).inverseImage.globalSectionMap
      (ringOneHom (structureRingSheaf B S hS (deformationSpace B S hS x)) ≫
        (moduleSheafFunctor (structureRingSheaf B S hS (deformationSpace B S hS x))).map m)) hs'
  refine Eq.trans ?_ (hc.trans hm)
  exact Deformation.AlgebraExtension.ringOneHom_comp_map_comp_inclSheafSets_eq_of_incl
    (deformationTensorAlgebraExtension B S hS x hsq g)
    (baseRingTensorSection B S hS (deformationFibreSpace B S hS x hsq)
      (baseRingHomOfMap (deformationFibreBaseProjection B S hS x hsq))
      (deformationBaseKernel B S hS x hsq) a)
    (structureSharpRingInverseImage B S hS
      (subspaceInclusion B S hS (deformationSpace B S hS x) (deformationThickening B S hS x hsq)))
    (modulePullbackGlobalSection B S hS
      (subspaceInclusion B S hS (deformationSpace B S hS x) (deformationThickening B S hS x hsq))
      (preimageIdealSection B S hS (deformationStructureMap B S hS x)
        (rangeSubspace B S hS (deformationBaseImmersion B S hS x)
          (isClosedImmersion_deformationBaseImmersion B S hS x hsq))
        ⟨a.1, (closedSubspaceBaseIdeal_rangeSubspace B S hS (deformationBaseImmersion B S hS x)
          (isClosedImmersion_deformationBaseImmersion B S hS x hsq)).symm ▸ a.2⟩))
    (conormalInverseImageι B S hS (deformationThickening B S hS x hsq)
      (isFirstOrderThickening_deformationThickening B S hS x hsq))
    (fun U => deformationTensorAlgebraExtension_incl_baseRingTensorSection B S hS x hsq g a
      (U := U))

/-- Postcomposition with the isomorphism `X₀ ≅ Z` of the space a deformation deforms onto its
closed fibre, as a functor of small étale sites, is continuous. -/
local instance : (smallEtalePostcomp B S hS (deformationThickeningIso B S hS x hsq).hom
    (isEtale_hom_of_iso B S hS (deformationThickeningIso B S hS x hsq))).IsContinuous
    (SmallEtale.topology B S hS y₀.obj.obj.left.1)
    (SmallEtale.topology B S hS (deformationFibreSpace B S hS x hsq).1) :=
  smallEtalePostcomp_isContinuous B S hS _ _

/-- Postcomposition with the isomorphism `X₀ ≅ Z` of the space a deformation deforms onto its
closed fibre, as a functor of small étale sites, is cocontinuous. -/
local instance : (smallEtalePostcomp B S hS (deformationThickeningIso B S hS x hsq).hom
    (isEtale_hom_of_iso B S hS (deformationThickeningIso B S hS x hsq))).IsCocontinuous
    (SmallEtale.topology B S hS y₀.obj.obj.left.1)
    (SmallEtale.topology B S hS (deformationFibreSpace B S hS x hsq).1) :=
  smallEtalePostcomp_isCocontinuous B S hS _ _

variable {x} (r : (cartesianProperFlatProjection B S hS).obj x.point ⟶
    (cartesianProperFlatProjection B S hS).obj y₀)
  (hr : (cartesianProperFlatProjection B S hS).map x.arrow ≫ r = 𝟙 _)

set_option maxHeartbeats 800000 in
-- the statement and the `refine` chain elaborate large explicit sheaf-of-modules terms
/-- **The section `1 ⊗ v` of `𝒪_{X₀} ⊗_k 𝔪_A`, on sheaves of sets**: in the extension
`AlgebraicGeometry.Space.deformationTensorBaseExtension` of a deformation, on the space `X₀` it
deforms, the unit section followed by `1 ⊗ v` (read through
`AlgebraicGeometry.Space.deformationTensorLinearIdealIso`) and the inclusion of the ideal is the
inverse image along `X₀ ≅ Z ⊆ X'` of the function `g^♯a` of `X'`, `a ∈ 𝔪_A` the element `v`
read in `Γ(Spec A)`, through `(e ≫ i)⁻¹𝒪_{X'} ≅ (i⁻¹𝒪_{X'})|_{X₀}`. -/
theorem incl_baseRingTensorSection_comp_deformationTensorLinearIdealIso_inv
    (v : RingHom.squareZeroKer (residueMap x.algebra) (residueMap_surjective' x.algebra) hsq)
    (V : (SmallEtale B S hS y₀.obj.obj.left.1)ᵒᵖ)
    (p : (sectionsFunctor _ V).obj
      (⊤_ Sheaf (SmallEtale.topology B S hS y₀.obj.obj.left.1) (Type u))) :
    (deformationTensorBaseExtension B S hS hsq r hr).incl
        ((baseRingTensorSection B S hS y₀.obj.obj.left (baseFieldHom B S hS (hy₀ := hy₀))
            (RingHom.squareZeroKer (residueMap x.algebra) (residueMap_surjective' x.algebra)
              hsq) v ≫
            (deformationTensorLinearIdealIso B S hS x hsq).inv).val.app V
          (1 : (structureRingSheaf B S hS y₀.obj.obj.left).obj.obj V)) =
      (sectionsFunctor _ V).map
        ((smallEtaleSetRestriction B S hS (deformationThickeningIso B S hS x hsq).hom
          (isEtale_hom_of_iso B S hS (deformationThickeningIso B S hS x hsq))).globalSectionMap
          ((smallEtaleRingedToposHom B S hS (subspaceInclusion B S hS (deformationSpace B S hS x)
              (deformationThickening B S hS x hsq))).toToposHom.inverseImage.globalSectionMap
            (ringOneHom (structureRingSheaf B S hS (deformationSpace B S hS x)) ≫
              (moduleSheafFunctor (structureRingSheaf B S hS (deformationSpace B S hS x))).map
                (unitModuleMul B S hS (deformationSpace B S hS x)
                  (globalFunctionsOfMap (deformationStructureMap B S hS x)
                    ((RingHom.squareZeroKerRingEquivIso _ _ (deformationAlgebraEquiv B S hS x)
                      (baseResidueFieldEquiv B S hS hy₀) (deformationBaseImmersion_Γ_comp B S hS x)
                      (deformationBaseImmersion_Γ_surjective B S hS x)
                      (deformationBaseImmersion_Γ_ker_sq B S hS x hsq)
                      (residueMap_surjective' x.algebra) hsq).inv.hom v).1))))) p := by
  have hL := baseRingTensorSection_deformationTensorLinearIdealIso_inv B S hS x hsq v
  have hZ :=
    ringOneHom_comp_map_baseRingTensorSection_comp_deformationTensorAlgebraExtension_inclSheafSets
      B S hS x hsq (deformationRetractedStructureMap B S hS r)
      ((RingHom.squareZeroKerRingEquivIso _ _ (deformationAlgebraEquiv B S hS x)
        (baseResidueFieldEquiv B S hS hy₀) (deformationBaseImmersion_Γ_comp B S hS x)
        (deformationBaseImmersion_Γ_surjective B S hS x)
        (deformationBaseImmersion_Γ_ker_sq B S hS x hsq)
        (residueMap_surjective' x.algebra) hsq).inv.hom v)
  refine Eq.trans ?_ (sectionsFunctor_map_globalSectionMap_smallEtaleSetRestriction B S hS
    (deformationThickeningIso B S hS x hsq).hom
    (isEtale_hom_of_iso B S hS (deformationThickeningIso B S hS x hsq))
    ((smallEtaleRingedToposHom B S hS (subspaceInclusion B S hS (deformationSpace B S hS x)
              (deformationThickening B S hS x hsq))).toToposHom.inverseImage.globalSectionMap
            (ringOneHom (structureRingSheaf B S hS (deformationSpace B S hS x)) ≫
              (moduleSheafFunctor (structureRingSheaf B S hS (deformationSpace B S hS x))).map
                (unitModuleMul B S hS (deformationSpace B S hS x)
                  (globalFunctionsOfMap (deformationStructureMap B S hS x)
                    ((RingHom.squareZeroKerRingEquivIso _ _ (deformationAlgebraEquiv B S hS x)
                      (baseResidueFieldEquiv B S hS hy₀) (deformationBaseImmersion_Γ_comp B S hS x)
                      (deformationBaseImmersion_Γ_surjective B S hS x)
                      (deformationBaseImmersion_Γ_ker_sq B S hS x hsq)
                      (residueMap_surjective' x.algebra) hsq).inv.hom v).1)))) V p).symm
  refine Eq.trans ?_
    (Deformation.AlgebraExtension.incl_eq_of_ringOneHom_comp_map_comp_inclSheafSets_eq _ _ _ hZ _ _)
  have hv := congrArg (fun m => m.val.app V
      (1 : (structureRingSheaf B S hS y₀.obj.obj.left).obj.obj V)) hL
  refine (castBase_incl B S hS
    (deformationThickeningIso_hom_comp_retractedStructureMap B S hS hsq r hr) _ _).trans ?_
  refine (etaleRestrictionFunctor_obj_incl B S hS (deformationThickeningIso B S hS x hsq).hom
    (isEtale_hom_of_iso B S hS (deformationThickeningIso B S hS x hsq)) _
    (deformationTensorAlgebraExtension B S hS x hsq
      (deformationRetractedStructureMap B S hS r)) _).trans ?_
  refine congrArg (deformationTensorAlgebraExtension B S hS x hsq
    (deformationRetractedStructureMap B S hS r)).incl (hv.trans ?_)
  exact modulePullbackGlobalSection_comp_modulePullbackIsoEtaleRestrictionModule_hom_val_app_one
    B S hS (deformationThickeningIso B S hS x hsq).hom
    (isEtale_hom_of_iso B S hS (deformationThickeningIso B S hS x hsq)) _ V

end AlgebraicGeometry.Space

end
