module

public import StacksFrontier.Deformation.Examples.Geometric.SpacesTangentSpaceSurjectiveDeformation

/-!
# The class of the deformation realizing an extension is the class of the extension

Let `x` be the deformation of `X` over `k[ε]` realizing an extension `P` of
`f⁻¹𝒪_{Spec k}`-algebras of `𝒪_X` by `𝒪_X ⊗_k k` (`Deformation.Examples.spaceSurjPoint`). The
middle term of `P` is `i⁻¹𝒪_{X'}` (Stacks 05ZT), and the middle term of the extension of `x` is
the restriction to `X ≅ Z` of the inverse image of `𝒪_{X'}` along the closed fibre `Z ⊆ X'`;
both are inverse images of `𝒪_{X'}` along the same map `X ⟶ X'`, which gives a morphism of
extensions. On the section `1 ⊗ 1` of the ideal it is the identity: the function `ε` of `X'`
restricts to `e = 1 ⊗ 1` in `P`, and to the section given by `ε ∈ k[ε]` in the extension of
`x`. So the map of ideals is the identity and the class of `x` is the class of `P`.

## Main results

* `Deformation.Examples.spaceSurjMiddleMap`: the morphism of middle terms.
* `Deformation.Examples.spaceSurjKernelMap_eq_id`: the map of ideals is the identity.
* `Deformation.Examples.spaceTangentFiberClass_spaceSurjPoint`: the class of `x` is that of `P`.

## References

* [Stacks Project, Tag 0E41](https://stacks.math.columbia.edu/tag/0E41)
* [Stacks Project, Tag 05ZT](https://stacks.math.columbia.edu/tag/05ZT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Space AlgebraicGeometry.Space.SquareZeroExtension
open Deformation.AlgebraExtension CategoryTheory.Sheaf Deformation.Artin

attribute [local instance] MorphismOfTopoi.preservesFiniteLimits

universe u

namespace Deformation.Examples

variable {Λ : Type u} {k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable (B : BigFppfSite.{u}) (hΛ : B.Contains (Spec (.of Λ)))
variable (hSpec : ∀ A : ArtinianLocalAlgCat.{u, u, u} Λ k, B.Contains (Spec (.of A)))
variable (X : (BigFppfOver B (Spec (.of Λ)) hΛ)ᵒᵖ ⥤ Type u)
  (hX : IsAlgebraicSpace B (Spec (.of Λ)) hΛ X)
  (toK : X ⟶ yoneda.obj (spaceBaseOver B hΛ hSpec (residueFieldBase Λ k)))

set_option synthInstance.maxHeartbeats 400000 in
/-- Discrete limits of presheaves of sets on the small étale site (instance search times out
without this shortcut). -/
local instance (priority := high) hasLimitsOfShape_discrete_SpacesTangentSpaceSurjectiveClassComparison
    {S : Scheme.{u}} {hS : B.Contains S} (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (J : Type u) :
    HasLimitsOfShape (Discrete J) ((SmallEtale B S hS F)ᵒᵖ ⥤ Type u) :=
  inferInstance

set_option synthInstance.maxHeartbeats 400000 in
/-- Discrete limits indexed by `Type` of presheaves of sets on the small étale site (instance
search times out without this shortcut). -/
local instance (priority := high) hasLimitsOfShape_discrete₀_SpacesTangentSpaceSurjectiveClassComparison
    {S : Scheme.{u}} {hS : B.Contains S} (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (J : Type) :
    HasLimitsOfShape (Discrete J) ((SmallEtale B S hS F)ᵒᵖ ⥤ Type u) :=
  inferInstance

set_option synthInstance.maxHeartbeats 400000 in
/-- Discrete limits of sheaves of sets on the small étale site (instance search times out
without this shortcut). -/
local instance (priority := high) hasDiscreteLimits_topos_SpacesTangentSpaceSurjectiveClassComparison
    {S : Scheme.{u}} {hS : B.Contains S} (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (J : Type) :
    HasLimitsOfShape (Discrete J) (Sheaf (SmallEtale.topology B S hS F) (Type u)) :=
  letI : HasLimitsOfShape (Discrete J) (Type u) := inferInstance
  letI : HasLimitsOfShape (Discrete J) ((SmallEtale B S hS F)ᵒᵖ ⥤ Type u) :=
    hasLimitsOfShape_discrete₀_SpacesTangentSpaceSurjectiveClassComparison B F J
  letI : CreatesLimitsOfShape (Discrete J)
      (sheafToPresheaf (SmallEtale.topology B S hS F) (Type u)) :=
    Sheaf.createsLimitsOfShape
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape
    (sheafToPresheaf (SmallEtale.topology B S hS F) (Type u))

/-- The terminal sheaf of sets on the small étale site (instance search times out without this
shortcut). -/
local instance (priority := high) hasTerminal_topos_SpacesTangentSpaceSurjectiveClassComparison
    {S : Scheme.{u}} {hS : B.Contains S} (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    HasTerminal (Sheaf (SmallEtale.topology B S hS F) (Type u)) :=
  hasDiscreteLimits_topos_SpacesTangentSpaceSurjectiveClassComparison B F PEmpty

/-- The maps `(u ≫ h)⁻¹𝒪_Y ⟶ u⁻¹𝒪_X` along equal morphisms agree, read through the
identifications of the inverse images along equal morphisms. -/
theorem _root_.AlgebraicGeometry.Space.eqToHom_inverseImageStructureSheafMap_eqToHom
    {S : Scheme.{u}} {hS : B.Contains S} {W X' Y : AlgebraicSpaces B S hS} {f : W ⟶ Y}
    {u₁ u₂ : W ⟶ X'} {h₁ h₂ : X' ⟶ Y} (hu : u₁ = u₂) (hh : h₁ = h₂) (e₁ : u₁ ≫ h₁ = f)
    (e₂ : u₂ ≫ h₂ = f) :
    eqToHom (congrArg (inverseImageStructureSheaf B S hS) e₁.symm) ≫
        inverseImageStructureSheafMap B S hS u₁ h₁ ≫
        eqToHom (congrArg (inverseImageStructureSheaf B S hS) hu) =
      eqToHom (congrArg (inverseImageStructureSheaf B S hS) e₂.symm) ≫
        inverseImageStructureSheafMap B S hS u₂ h₂ := by
  subst hu hh
  simp

/-- The inverse image of a global section along equal morphisms, read through the
identification of the inverse images. -/
theorem _root_.AlgebraicGeometry.Space.globalSectionMap_comp_eqToHom
    {S : Scheme.{u}} {hS : B.Contains S} {W X' : AlgebraicSpaces B S hS} {u₁ u₂ : W ⟶ X'}
    (hu : u₁ = u₂)
    (τ : ⊤_ Sheaf (SmallEtale.topology B S hS X'.1) (Type u) ⟶
      (sheafCompose _ (forget CommRingCat.{u})).obj (smallEtaleRingedTopos B S hS X').O) :
    ((smallEtaleRingedToposHom B S hS u₁).toToposHom.inverseImage.globalSectionMap τ ≫
        (sheafCompose (SmallEtale.topology B S hS W.1) (forget CommRingCat.{u})).map
          (eqToHom (congrArg (inverseImageStructureSheaf B S hS) hu)) :
        ⊤_ Sheaf (SmallEtale.topology B S hS W.1) (Type u) ⟶
          (sheafCompose (SmallEtale.topology B S hS W.1) (forget CommRingCat.{u})).obj
            (inverseImageStructureSheaf B S hS u₂)) =
      (smallEtaleRingedToposHom B S hS u₂).toToposHom.inverseImage.globalSectionMap τ := by
  subst hu
  simp only [eqToHom_refl]
  exact Category.comp_id _

/-- The homomorphism of middle terms of a morphism of extensions transported along an equality
of the maps of ideals. -/
theorem _root_.Deformation.AlgebraExtension.MapAlong.hom_cast {C : Type*} [Category C]
    {J : GrothendieckTopology C} [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    {A O : Sheaf J CommRingCat.{u}} {a : A ⟶ O}
    {M N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O)}
    {P : AlgebraExtension a M} {Q : AlgebraExtension a N} {φ φ' : M ⟶ N} (e : φ = φ')
    (g : MapAlong φ P Q) :
    (cast (congrArg (fun ψ : M ⟶ N => MapAlong ψ P Q) e) g).hom = g.hom := by
  subst e
  rfl

/-- Postcomposition with `X ≅ Z` is continuous for the small étale topologies. -/
local instance (x : Over (spaceSpecialFiber B hΛ hSpec X hX toK))
    (hsq : IsLocalRing.maximalIdeal x.left.base ^ 2 = ⊥) :
    (smallEtalePostcomp B (Spec (.of Λ)) hΛ (spaceDefoThickeningIso B hΛ hSpec X hX toK x hsq).hom
    (isEtale_hom_of_iso B (Spec (.of Λ)) hΛ
      (spaceDefoThickeningIso B hΛ hSpec X hX toK x hsq))).IsContinuous
    (SmallEtale.topology B (Spec (.of Λ)) hΛ X)
    (SmallEtale.topology B (Spec (.of Λ)) hΛ (spaceDefoFibreSpace B hΛ hSpec X hX toK x hsq).1) :=
  smallEtalePostcomp_isContinuous B (Spec (.of Λ)) hΛ _ _

/-- Postcomposition with `X ≅ Z` is cocontinuous for the small étale topologies. -/
local instance (x : Over (spaceSpecialFiber B hΛ hSpec X hX toK))
    (hsq : IsLocalRing.maximalIdeal x.left.base ^ 2 = ⊥) :
    (smallEtalePostcomp B (Spec (.of Λ)) hΛ (spaceDefoThickeningIso B hΛ hSpec X hX toK x hsq).hom
    (isEtale_hom_of_iso B (Spec (.of Λ)) hΛ
      (spaceDefoThickeningIso B hΛ hSpec X hX toK x hsq))).IsCocontinuous
    (SmallEtale.topology B (Spec (.of Λ)) hΛ X)
    (SmallEtale.topology B (Spec (.of Λ)) hΛ (spaceDefoFibreSpace B hΛ hSpec X hX toK x hsq).1) :=
  smallEtalePostcomp_isCocontinuous B (Spec (.of Λ)) hΛ _ _

variable (P : AlgebraExtension (J := SmallEtale.topology B (Spec (.of Λ)) hΛ X)
  (inverseImageBaseMap B (Spec (.of Λ)) hΛ (spaceStructureMap B hΛ hSpec X hX toK))
  (spaceRankOneCoefficient B hΛ hSpec X hX toK))
  (hflat : Space.IsFlat B (Spec (.of Λ)) hΛ (spaceSurjToDual B hΛ hSpec X hX toK P).hom)
  (hcart : IsPullback (spaceSurjImmersion B hΛ hSpec X hX toK P).hom toK
      (spaceSurjToDual B hΛ hSpec X hX toK P).hom
      (yoneda.map (spaceDualImmersion B hΛ hSpec)))

/-- Abbreviation for the square-zero extension `spaceSurjExtension`. -/
local notation "E" => spaceSurjExtension B hΛ hSpec X hX toK P
/-- Abbreviation for the presentation. -/
local notation "Pp" => spaceSurjPresentation B hΛ hSpec X hX toK
/-- Abbreviation for the containment of the chart thickening. -/
local notation "hU" => contains_spaceSurj_chartRealizedScheme B hΛ hSpec X hX toK P _
/-- Abbreviation for the realizing deformation. -/
local notation "xP" => spaceSurjPoint B hΛ hSpec X hX toK P hflat hcart
/-- Abbreviation for the square-zero condition of the realizing deformation. -/
local notation "hA" =>
  spaceFiber_maximalIdeal_sq B hΛ hSpec X hX toK (spaceSurjPoint B hΛ hSpec X hX toK P hflat hcart)

/-- **`X ≅ Z ⊆ X'` is `X ⟶ X'`** for the realizing deformation. -/
theorem spaceSurjThickeningIso_comp_inclusion :
    (spaceDefoThickeningIso B hΛ hSpec X hX toK (xP).1 hA).hom ≫
        subspaceInclusion B (Spec (.of Λ)) hΛ _
          (spaceDefoThickening B hΛ hSpec X hX toK (xP).1 hA) =
      spaceSurjImmersion B hΛ hSpec X hX toK P :=
  spaceDefoThickeningIso_hom_comp_subspaceInclusion B hΛ hSpec X hX toK (xP).1 hA

/-- **The morphism of middle terms**: `𝒜 ≅ i⁻¹𝒪_{X'}`, read as `(X ≅ Z ⊆ X')⁻¹𝒪_{X'}` and as the
restriction to `X ≅ Z` of the inverse image along `Z ⊆ X'`. -/
def spaceSurjMiddleMap :
    P.extension ⟶ (spaceTangentExtension B hΛ hSpec X hX toK xP).extension :=
  ((E).quotientSheafIso Pp hU hU).inv ≫
    eqToHom (congrArg (inverseImageStructureSheaf B (Spec (.of Λ)) hΛ)
      (spaceSurjThickeningIso_comp_inclusion B hΛ hSpec X hX toK P hflat hcart).symm) ≫
    (etaleRestrictionRingComparison B (Spec (.of Λ)) hΛ
      (spaceDefoThickeningIso B hΛ hSpec X hX toK (xP).1 hA).hom
      (isEtale_hom_of_iso B (Spec (.of Λ)) hΛ
        (spaceDefoThickeningIso B hΛ hSpec X hX toK (xP).1 hA))
      (subspaceInclusion B (Spec (.of Λ)) hΛ _
        (spaceDefoThickening B hΛ hSpec X hX toK (xP).1 hA))).α.hom

/-- The morphism of middle terms is an isomorphism. -/
def spaceSurjMiddleIso :
    P.extension ≅ (spaceTangentExtension B hΛ hSpec X hX toK xP).extension :=
  ((E).quotientSheafIso Pp hU hU).symm ≪≫
    eqToIso (congrArg (inverseImageStructureSheaf B (Spec (.of Λ)) hΛ)
      (spaceSurjThickeningIso_comp_inclusion B hΛ hSpec X hX toK P hflat hcart).symm) ≪≫
    (etaleRestrictionRingComparison B (Spec (.of Λ)) hΛ
      (spaceDefoThickeningIso B hΛ hSpec X hX toK (xP).1 hA).hom
      (isEtale_hom_of_iso B (Spec (.of Λ)) hΛ
        (spaceDefoThickeningIso B hΛ hSpec X hX toK (xP).1 hA))
      (subspaceInclusion B (Spec (.of Λ)) hΛ _
        (spaceDefoThickening B hΛ hSpec X hX toK (xP).1 hA))).α

/-- The forward map of `Deformation.Examples.spaceSurjMiddleIso` is
`Deformation.Examples.spaceSurjMiddleMap`. -/
theorem spaceSurjMiddleIso_hom :
    (spaceSurjMiddleIso B hΛ hSpec X hX toK P hflat hcart).hom =
      spaceSurjMiddleMap B hΛ hSpec X hX toK P hflat hcart :=
  rfl

/-- The morphism of middle terms is over `𝒪_X`. -/
theorem spaceSurjMiddleMap_comp_reduction :
    spaceSurjMiddleMap B hΛ hSpec X hX toK P hflat hcart ≫
        (spaceTangentExtension B hΛ hSpec X hX toK xP).reduction = P.reduction := by
  have h1 := etaleRestrictionRingComparison_α_hom_comp_reduction B (Spec (.of Λ)) hΛ
    (spaceDefoThickeningIso B hΛ hSpec X hX toK (xP).1 hA).hom
    (isEtale_hom_of_iso B (Spec (.of Λ)) hΛ (spaceDefoThickeningIso B hΛ hSpec X hX toK (xP).1 hA))
    (subspaceInclusion B (Spec (.of Λ)) hΛ _ (spaceDefoThickening B hΛ hSpec X hX toK (xP).1 hA))
  have h2 := structureSharpInverseImage_eqToHom B (Spec (.of Λ)) hΛ
    (spaceSurjThickeningIso_comp_inclusion B hΛ hSpec X hX toK P hflat hcart).symm
  have h3 := (E).quotientSheafIso_hom_comp_π Pp hU hU
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) (Category.assoc _ _ _)).trans ?_
  refine (congrArg (fun t => _ ≫ _ ≫ t) h1).trans ?_
  refine (congrArg (_ ≫ ·) h2).trans ?_
  exact (Iso.inv_comp_eq _).mpr h3.symm

/-- The morphism of middle terms is under `f⁻¹𝒪_{Spec k}`. -/
theorem algebraMap_comp_spaceSurjMiddleMap :
    P.algebraMap ≫ spaceSurjMiddleMap B hΛ hSpec X hX toK P hflat hcart =
      (spaceTangentExtension B hΛ hSpec X hX toK xP).algebraMap := by
  have hT := (E).toBase_eq_thickeningQuotientToBase Pp _ _ (presentationOverChart_comm _ _ _) _
    (presentationOverChartRelHom_target _ _ _) (presentationOverChartRelHom_source _ _ _) hU hU
  have hR := etaleRestrictionRingComparison_α_map_inverseImageStructureSheafMap B (Spec (.of Λ)) hΛ
    (spaceDefoThickeningIso B hΛ hSpec X hX toK (xP).1 hA).hom
    (isEtale_hom_of_iso B (Spec (.of Λ)) hΛ (spaceDefoThickeningIso B hΛ hSpec X hX toK (xP).1 hA))
    (subspaceInclusion B (Spec (.of Λ)) hΛ _ (spaceDefoThickening B hΛ hSpec X hX toK (xP).1 hA))
    (spaceDefoRetractedStructureMap B hΛ hSpec X hX toK
      (spaceTangentRetraction B hΛ hSpec X hX toK xP))
  have hR' := (Iso.comp_inv_eq _).mp ((Category.assoc _ _ _).trans hR)
  have hh : spaceSurjToBase B hΛ hSpec X hX toK P =
      spaceDefoRetractedStructureMap B hΛ hSpec X hX toK
        (spaceTangentRetraction B hΛ hSpec X hX toK xP) := by
    refine (spaceSurjToDual_comp B hΛ hSpec X hX toK P).symm.trans ?_
    simp only [spaceTangentRetraction, spaceFiberConstants, eqToHom_refl, Category.comp_id]
    rfl
  have hG := eqToHom_inverseImageStructureSheafMap_eqToHom B
    (spaceSurjThickeningIso_comp_inclusion B hΛ hSpec X hX toK P hflat hcart).symm hh
    (spaceSurjImmersion_comp_toBase B hΛ hSpec X hX toK P)
    (spaceDefoThickeningIso_hom_comp_retractedStructureMap B hΛ hSpec X hX toK hA
      (spaceTangentRetraction B hΛ hSpec X hX toK xP)
      (spaceDefoBaseImmersion_comp_spaceTangentRetraction B hΛ hSpec X hX toK xP))
  have hT' : P.algebraMap = eqToHom (congrArg (inverseImageStructureSheaf B (Spec (.of Λ)) hΛ)
        (spaceSurjImmersion_comp_toBase B hΛ hSpec X hX toK P).symm) ≫
      inverseImageStructureSheafMap B (Spec (.of Λ)) hΛ (spaceSurjImmersion B hΛ hSpec X hX toK P)
        (spaceSurjToBase B hΛ hSpec X hX toK P) ≫ ((E).quotientSheafIso Pp hU hU).hom := by
    refine hT.trans ?_
    unfold inverseImageStructureSheafMap
    simp only [Category.assoc]
    rfl
  unfold spaceSurjMiddleMap
  rw [hT']
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
    (congrArg (_ ≫ ·) (Iso.hom_inv_id_assoc _ _)))).trans ?_
  refine (congrArg (_ ≫ ·) (Category.assoc _ _ _).symm).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) hG).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  exact (congrArg (_ ≫ ·) hR').symm

/-- The function `ε ∈ k[ε]`, read on `Spec k[ε]`. -/
abbrev spaceDualEps : baseRing B (Spec (.of Λ)) hΛ
    (spaceBaseOver B hΛ hSpec (spaceDualNumbers (Λ := Λ) (k := k))) :=
  spaceDefoAlgebraEquiv (B := B) (hΛ := hΛ) (hSpec := hSpec) _
    (TrivSqZeroExt.inr (R := k) (M := (forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)).obj
      (FGModuleCat.of k k)) (1 : k))

/-- **The pullback of `ε ∈ k[ε]` along `X' ⟶ Spec k[ε]` is `ε`.** -/
theorem globalFunctionsOfMap_spaceSurjToDual_val (U : (SmallEtale B (Spec (.of Λ)) hΛ
      (spaceSurjAmbient B hΛ hSpec X hX toK P).1)ᵒᵖ) :
    (globalFunctionsOfMap (spaceSurjToDual B hΛ hSpec X hX toK P) (spaceDualEps B hΛ hSpec)).1 U =
      (spaceSurjEps B hΛ hSpec X hX toK P).1 U := by
  have h1 := congrArg (fun φ => (φ (spaceDualEps B hΛ hSpec)).1 U)
    (pullbackToGlobalFunctions_spaceSurjToDual B hΛ hSpec X hX toK P)
  refine h1.trans ?_
  refine congrArg (fun t : globalFunctions B (Spec (.of Λ)) hΛ
    (spaceSurjAmbient B hΛ hSpec X hX toK P).1 => t.1 U) ?_
  refine (RingHom.comp_apply _ _ _).trans ?_
  refine (congrArg (spaceSurjDualHom B hΛ hSpec X hX toK P)
    (RingEquiv.symm_apply_apply _ _)).trans ?_
  show spaceSurjConstants B hΛ hSpec X hX toK P 0 +
    spaceSurjConstants B hΛ hSpec X hX toK P 1 * spaceSurjEps B hΛ hSpec X hX toK P = _
  rw [map_zero, map_one, zero_add, one_mul]

/-- **`ε` is multiplication by `ε` on the unit function**, on sheaves of sets. -/
theorem spaceSurjEpsSet_eq :
    spaceSurjEpsSet B hΛ hSpec X hX toK P =
      ringOneHom (structureRingSheaf B (Spec (.of Λ)) hΛ (spaceSurjAmbient B hΛ hSpec X hX toK P)) ≫
        (moduleSheafFunctor (structureRingSheaf B (Spec (.of Λ)) hΛ
          (spaceSurjAmbient B hΛ hSpec X hX toK P))).map
          (unitModuleMul B (Spec (.of Λ)) hΛ (spaceSurjAmbient B hΛ hSpec X hX toK P)
            (globalFunctionsOfMap (spaceSurjToDual B hΛ hSpec X hX toK P)
              (spaceDualEps B hΛ hSpec))) := by
  refine hom_ext_sections fun U q => ?_
  refine (globalFunctionsOfSection_apply (spaceSurjEpsSet B hΛ hSpec X hX toK P) U q).symm.trans ?_
  refine (globalFunctionsOfMap_spaceSurjToDual_val B hΛ hSpec X hX toK P U).symm.trans ?_
  exact (unitModuleMul_val_app_one B (Spec (.of Λ)) hΛ (spaceSurjAmbient B hΛ hSpec X hX toK P)
    _ U.unop).symm

/-- The function of the base given by `1 ∈ k`, for the realizing deformation, is `ε`. -/
theorem spaceTangentFunction_spaceSurjPoint :
    spaceTangentFunction B hΛ hSpec X hX toK xP (1 : k) = spaceDualEps B hΛ hSpec :=
  spaceTangentFunction_eq B hΛ hSpec X hX toK xP (1 : k)

/-- **The morphism of middle terms carries `e = 1 ⊗ 1` to the section given by `ε ∈ k[ε]`.** -/
theorem spaceSurjEpsSection_comp_spaceSurjMiddleMap :
    spaceSurjEpsSection B hΛ hSpec X hX toK P ≫
        (sheafCompose (SmallEtale.topology B (Spec (.of Λ)) hΛ X) (forget CommRingCat.{u})).map
          (spaceSurjMiddleMap B hΛ hSpec X hX toK P hflat hcart) =
      spaceDefoFunctionSectionE B hΛ hSpec X hX toK (xP).1 hA
        (spaceTangentFunction B hΛ hSpec X hX toK xP (1 : k)) := by
  have h0 := globalSectionMap_spaceSurjEpsSet B hΛ hSpec X hX toK P
  have h1 : spaceSurjEpsSection B hΛ hSpec X hX toK P ≫
      (sheafCompose (SmallEtale.topology B (Spec (.of Λ)) hΛ X) (forget CommRingCat.{u})).map
        ((E).quotientSheafIso Pp hU hU).inv =
      (smallEtaleRingedToposHom B (Spec (.of Λ)) hΛ
        (spaceSurjImmersion B hΛ hSpec X hX toK P)).toToposHom.inverseImage.globalSectionMap
        (spaceSurjEpsSet B hΛ hSpec X hX toK P) := by
    refine (congrArg (· ≫ _) h0.symm).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (_ ≫ ·)
      (((sheafCompose (SmallEtale.topology B (Spec (.of Λ)) hΛ X)
          (forget CommRingCat.{u})).map_comp _ _).symm.trans
        ((congrArg (sheafCompose (SmallEtale.topology B (Spec (.of Λ)) hΛ X)
            (forget CommRingCat.{u})).map (Iso.hom_inv_id _)).trans
          ((sheafCompose (SmallEtale.topology B (Spec (.of Λ)) hΛ X)
            (forget CommRingCat.{u})).map_id _)))).trans ?_
    exact Category.comp_id _
  have h2 := globalSectionMap_comp_eqToHom B
    (spaceSurjThickeningIso_comp_inclusion B hΛ hSpec X hX toK P hflat hcart).symm
    (spaceSurjEpsSet B hΛ hSpec X hX toK P)
  unfold spaceSurjMiddleMap
  refine (congrArg (_ ≫ ·) ((sheafCompose (SmallEtale.topology B (Spec (.of Λ)) hΛ X)
    (forget CommRingCat.{u})).map_comp _ _)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) h1).trans ?_
  refine (congrArg (_ ≫ ·) ((sheafCompose (SmallEtale.topology B (Spec (.of Λ)) hΛ X)
    (forget CommRingCat.{u})).map_comp _ _)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  have h3 := congrArg (· ≫ (sheafCompose (SmallEtale.topology B (Spec (.of Λ)) hΛ X)
      (forget CommRingCat.{u})).map (etaleRestrictionRingComparison B (Spec (.of Λ)) hΛ
      (spaceDefoThickeningIso B hΛ hSpec X hX toK (xP).1 hA).hom
      (isEtale_hom_of_iso B (Spec (.of Λ)) hΛ
        (spaceDefoThickeningIso B hΛ hSpec X hX toK (xP).1 hA))
      (subspaceInclusion B (Spec (.of Λ)) hΛ _
        (spaceDefoThickening B hΛ hSpec X hX toK (xP).1 hA))).α.hom) h2
  refine Eq.trans ?_ (h3.trans ?_)
  · rfl
  · rw [spaceSurjEpsSet_eq B hΛ hSpec X hX toK P]
    refine Eq.trans ?_ (congrArg (spaceDefoFunctionSectionE B hΛ hSpec X hX toK (xP).1 hA)
      (spaceTangentFunction_spaceSurjPoint B hΛ hSpec X hX toK P hflat hcart)).symm
    rfl

/-- **The map of ideals of the morphism of middle terms is the identity of `𝒪_X ⊗_k k`.** -/
theorem spaceSurjKernelMap_eq_id :
    inducedKernelMap.{u, u + 1, u} (J := SmallEtale.topology B (Spec (.of Λ)) hΛ X) P
        (spaceTangentExtension B hΛ hSpec X hX toK xP)
        (spaceSurjMiddleMap B hΛ hSpec X hX toK P hflat hcart)
        (spaceSurjMiddleMap_comp_reduction B hΛ hSpec X hX toK P hflat hcart) = 𝟙 _ := by
  suffices hs : spaceRankOneSection B hΛ hSpec X hX toK ≫
      (inducedKernelMap.{u, u + 1, u} (J := SmallEtale.topology B (Spec (.of Λ)) hΛ X) P
        (spaceTangentExtension B hΛ hSpec X hX toK xP)
        (spaceSurjMiddleMap B hΛ hSpec X hX toK P hflat hcart)
        (spaceSurjMiddleMap_comp_reduction B hΛ hSpec X hX toK P hflat hcart)) =
      spaceRankOneSection B hΛ hSpec X hX toK from
    (Category.id_comp _).symm.trans ((congrArg (· ≫ _)
      (spaceRankOneSectionInv_comp B hΛ hSpec X hX toK).symm).trans ((Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) hs).trans (spaceRankOneSectionInv_comp B hΛ hSpec X hX toK))))
  refine hom_ext_of_incl (J := SmallEtale.topology B (Spec (.of Λ)) hΛ X)
    (spaceTangentExtension B hΛ hSpec X hX toK xP) fun U p => ?_
  have h1 := SheafOfModules.comp_val_app_apply (spaceRankOneSection B hΛ hSpec X hX toK)
    (inducedKernelMap.{u, u + 1, u} (J := SmallEtale.topology B (Spec (.of Λ)) hΛ X) P
        (spaceTangentExtension B hΛ hSpec X hX toK xP)
        (spaceSurjMiddleMap B hΛ hSpec X hX toK P hflat hcart)
        (spaceSurjMiddleMap_comp_reduction B hΛ hSpec X hX toK P hflat hcart)) U
    (1 : (structureRingSheaf B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)).obj.obj U)
  have hK := incl_inducedKernelMap_val_app_eq.{u, u + 1, u}
    (J := SmallEtale.topology B (Spec (.of Λ)) hΛ X) P
    (spaceTangentExtension B hΛ hSpec X hX toK xP)
    (spaceSurjMiddleMap B hΛ hSpec X hX toK P hflat hcart)
    (spaceSurjMiddleMap_comp_reduction B hΛ hSpec X hX toK P hflat hcart)
    ((spaceRankOneSection B hΛ hSpec X hX toK).val.app U
      (1 : (structureRingSheaf B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)).obj.obj U))
    (spaceSurjEpsSection B hΛ hSpec X hX toK P)
    (spaceDefoFunctionSectionE B hΛ hSpec X hX toK (xP).1 hA
      (spaceTangentFunction B hΛ hSpec X hX toK xP (1 : k))) p
    (spaceSurjEpsSection_app B hΛ hSpec X hX toK P U p).symm
    (spaceSurjEpsSection_comp_spaceSurjMiddleMap B hΛ hSpec X hX toK P hflat hcart)
  have h3 := (spaceTangentExtension_incl_baseRingTensorSection B hΛ hSpec X hX toK xP (1 : k)
      U p).trans
    (sectionsFunctor_map_congr (spaceDefoFunctionSection_eq B hΛ hSpec X hX toK (xP).1 hA
      (spaceTangentFunction B hΛ hSpec X hX toK xP (1 : k))) U p)
  exact (congrArg (spaceTangentExtension B hΛ hSpec X hX toK xP).incl h1).trans (hK.trans h3.symm)

/-- The map of ideals of the morphism of middle terms is the identity, sectionwise. -/
theorem spaceSurjKernelMap_val_app (U : (SmallEtale B (Spec (.of Λ)) hΛ X)ᵒᵖ)
    (m : (spaceRankOneCoefficient B hΛ hSpec X hX toK).val.obj U) :
    (inducedKernelMap.{u, u + 1, u} (J := SmallEtale.topology B (Spec (.of Λ)) hΛ X) P
        (spaceTangentExtension B hΛ hSpec X hX toK xP)
        (spaceSurjMiddleMap B hΛ hSpec X hX toK P hflat hcart)
        (spaceSurjMiddleMap_comp_reduction B hΛ hSpec X hX toK P hflat hcart)).val.app U m = m :=
  congrArg (fun ψ : spaceRankOneCoefficient B hΛ hSpec X hX toK ⟶
      spaceRankOneCoefficient B hΛ hSpec X hX toK => ψ.val.app U m)
    (spaceSurjKernelMap_eq_id B hΛ hSpec X hX toK P hflat hcart)

/-- The morphism of middle terms on the ideal `𝒪_X ⊗_k k`. -/
theorem spaceSurjMiddleMap_kernel_comm (U : (SmallEtale B (Spec (.of Λ)) hΛ X)ᵒᵖ)
    (m : (spaceRankOneCoefficient B hΛ hSpec X hX toK).val.obj U) :
    (spaceSurjMiddleMap B hΛ hSpec X hX toK P hflat hcart).hom.app U (P.incl m) =
      (spaceTangentExtension B hΛ hSpec X hX toK xP).incl m :=
  (hom_incl P (spaceTangentExtension B hΛ hSpec X hX toK xP)
      (spaceSurjMiddleMap B hΛ hSpec X hX toK P hflat hcart)
      (spaceSurjMiddleMap_comp_reduction B hΛ hSpec X hX toK P hflat hcart) m).trans
    (congrArg (spaceTangentExtension B hΛ hSpec X hX toK xP).incl
      (spaceSurjKernelMap_val_app B hΛ hSpec X hX toK P hflat hcart U m))

/-- **The morphism of extensions from `P` to the extension of the realizing deformation**,
inducing the identity on `𝒪_X ⊗_k k`. -/
def spaceSurjExtensionHom :
    MapAlong.{u, u + 1, u} (J := SmallEtale.topology B (Spec (.of Λ)) hΛ X) (𝟙 _) P
      (spaceTangentExtension B hΛ hSpec X hX toK xP) :=
  cast (congrArg (fun φ : spaceRankOneCoefficient B hΛ hSpec X hX toK ⟶
      spaceRankOneCoefficient B hΛ hSpec X hX toK =>
        MapAlong.{u, u + 1, u} (J := SmallEtale.topology B (Spec (.of Λ)) hΛ X) φ P
          (spaceTangentExtension B hΛ hSpec X hX toK xP))
    (spaceSurjKernelMap_eq_id B hΛ hSpec X hX toK P hflat hcart))
    (mapAlongInducedKernelMap.{u, u + 1, u} (J := SmallEtale.topology B (Spec (.of Λ)) hΛ X) P
      (spaceTangentExtension B hΛ hSpec X hX toK xP)
      (spaceSurjMiddleMap B hΛ hSpec X hX toK P hflat hcart)
      (spaceSurjMiddleMap_comp_reduction B hΛ hSpec X hX toK P hflat hcart)
      (algebraMap_comp_spaceSurjMiddleMap B hΛ hSpec X hX toK P hflat hcart))

/-- The homomorphism of middle terms of `Deformation.Examples.spaceSurjExtensionHom` is
`Deformation.Examples.spaceSurjMiddleMap`. -/
theorem spaceSurjExtensionHom_hom :
    (spaceSurjExtensionHom B hΛ hSpec X hX toK P hflat hcart).hom =
      spaceSurjMiddleMap B hΛ hSpec X hX toK P hflat hcart :=
  MapAlong.hom_cast.{u, u + 1, u} (C := SmallEtale B (Spec (.of Λ)) hΛ X)
    (J := SmallEtale.topology B (Spec (.of Λ)) hΛ X)
    (spaceSurjKernelMap_eq_id B hΛ hSpec X hX toK P hflat hcart) _

/-- The morphism of extensions from `P` to the extension of the realizing deformation is an
isomorphism on middle terms. -/
instance : IsIso (spaceSurjExtensionHom B hΛ hSpec X hX toK P hflat hcart).hom := by
  rw [spaceSurjExtensionHom_hom, ← spaceSurjMiddleIso_hom]
  infer_instance

/-- **The class of the deformation realizing `P` is the class of `P`.** -/
theorem spaceTangentFiberClass_spaceSurjPoint :
    spaceTangentFiberClass B hΛ hSpec X hX toK xP = modelExtClass B (Spec (.of Λ)) hΛ P :=
  (modelExtClass_eq_of_iso B (Spec (.of Λ)) hΛ
    (@asIso.{u + 1, u + 1} _ AlgebraExtension.instCategory.{u, u + 1, u} _ _
      (spaceSurjExtensionHom B hΛ hSpec X hX toK P hflat hcart)
      (AlgebraExtension.isIso_of_isIso_hom (J := SmallEtale.topology B (Spec (.of Λ)) hΛ X)
        (spaceSurjExtensionHom B hΛ hSpec X hX toK P hflat hcart)))).symm

end Deformation.Examples

end
