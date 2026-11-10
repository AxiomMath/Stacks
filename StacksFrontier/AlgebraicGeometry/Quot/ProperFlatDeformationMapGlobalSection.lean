module

public import StacksFrontier.Algebra.Module.OppositeOfCommSemiring
public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatDeformationMap
public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatDeformationTensorExtensionGlobalSection

/-!
# The map of middle terms of a morphism of deformations, on functions of the base

For a morphism `φ : x ⟶ x'` of deformations over `ρ : A ⟶ A'` (both residue kernels squaring to
zero), the homomorphism `AlgebraicGeometry.Space.deformationMiddleMap` of the middle terms of
their extensions on `X₀` carries the global section of the middle term of `x` given by a function
`a ∈ Γ(Spec A)` (the étale restriction to `X₀` of the inverse image of `g^♯a`) to the global
section of the middle term of `x'` given by `ρ(a)`, on underlying sheaves of sets. This is the
computation of the map of ideals of a morphism of deformations in the proof of Stacks 0D1K.

## Main results

* `AlgebraicGeometry.Space.globalFunctionsOfMap_comp`
* `AlgebraicGeometry.Space.deformationFunctionSection_comp_forget_map_deformationMiddleMap`

## References

* [Stacks Project, Tag 0D1K](https://stacks.math.columbia.edu/tag/0D1K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Deformation

attribute [local instance] MorphismOfTopoi.preservesFiniteLimits

universe u

namespace Deformation.AlgebraExtension

variable {C : Type*} [Category C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.HasSheafCompose (forget RingCat.{u})] [J.HasSheafCompose (forget AddCommGrpCat.{u})]
  {A O : Sheaf J CommRingCat.{u}} {a : A ⟶ O}
  {M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O)}

set_option synthInstance.maxHeartbeats 400000 in
-- Lean v4.35.0: `HasLimitsOfShape (Discrete J) (Cᵒᵖ ⥤ Type u)` (for `⊤_ Sheaf J (Type u)`)
-- exceeds the default typeclass budget.
/-- **Global sections of the kernel are determined by their inclusions at `1`**, sectionwise. -/
theorem hom_ext_of_incl (P : AlgebraExtension a M)
    {w w' : SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O) ⟶ M}
    (h : ∀ (U : Cᵒᵖ) (_ : (sectionsFunctor J U).obj (⊤_ Sheaf J (Type u))),
      P.incl (w.val.app U
        (1 : ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O).obj.obj U)) =
      P.incl (w'.val.app U
        (1 : ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O).obj.obj U))) :
    w = w' :=
  hom_ext_ringOneHom (hom_ext_sections fun U p => P.incl_injective (h U p))

set_option synthInstance.maxHeartbeats 400000 in
-- Lean v4.35.0: `HasLimitsOfShape (Discrete J) (Cᵒᵖ ⥤ Type u)` (for `⊤_ Sheaf J (Type u)`)
-- exceeds the default typeclass budget.
omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.HasSheafCompose (forget RingCat.{u})] [J.HasSheafCompose (forget AddCommGrpCat.{u})] in
/-- A global section of the underlying sheaf of sets of a sheaf of commutative rings, followed by
a homomorphism `g`, on a section: `g` applied to the value. -/
theorem sectionsFunctor_map_comp_sheafCompose_forget_map
    [J.HasSheafCompose (forget CommRingCat.{u})]
    {R R' : Sheaf J CommRingCat.{u}} (g : R ⟶ R')
    (σ : ⊤_ Sheaf J (Type u) ⟶ (sheafCompose J (forget CommRingCat.{u})).obj R) (U : Cᵒᵖ)
    (p : (sectionsFunctor J U).obj (⊤_ Sheaf J (Type u))) :
    (sectionsFunctor J U).map (σ ≫ (sheafCompose J (forget CommRingCat.{u})).map g) p =
      g.hom.app U ((sectionsFunctor J U).map σ p) :=
  rfl

set_option synthInstance.maxHeartbeats 400000 in
-- Lean v4.35.0: `HasLimitsOfShape (Discrete J) (Cᵒᵖ ⥤ Type u)` (for `⊤_ Sheaf J (Type u)`)
-- exceeds the default typeclass budget.
omit [J.HasSheafCompose (forget RingCat.{u})] [J.HasSheafCompose (forget AddCommGrpCat.{u})] in
/-- The induced map of ideals on a section included as the value of a global section of the
middle term: if `P.incl m` is the value at `p` of a global section `z` of the underlying sheaf of
sets of the middle term of `P`, and `z` followed by `h` is `z'`, then the image of `m` under the
induced map of ideals is included as the value of `z'` at `p`. -/
theorem incl_inducedKernelMap_val_app_eq [J.HasSheafCompose (forget CommRingCat.{u})]
    {A' : Sheaf J CommRingCat.{u}} {a' : A' ⟶ O}
    {N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O)}
    (P : AlgebraExtension a M) (Q : AlgebraExtension a' N) (h : P.extension ⟶ Q.extension)
    (hh : h ≫ Q.reduction = P.reduction) {U : Cᵒᵖ} (m : M.val.obj U)
    (z : ⊤_ Sheaf J (Type u) ⟶ (sheafCompose J (forget CommRingCat.{u})).obj P.extension)
    (z' : ⊤_ Sheaf J (Type u) ⟶ (sheafCompose J (forget CommRingCat.{u})).obj Q.extension)
    (p : (sectionsFunctor J U).obj (⊤_ Sheaf J (Type u)))
    (hm : P.incl m = (sectionsFunctor J U).map z p)
    (hz : z ≫ (sheafCompose J (forget CommRingCat.{u})).map h = z') :
    Q.incl ((inducedKernelMap P Q h hh).val.app U m) = (sectionsFunctor J U).map z' p := by
  rw [← hom_incl, hm, ← hz]
  rfl

end Deformation.AlgebraExtension

namespace AlgebraicGeometry.Space

open Deformation.Artin

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for discrete limits on the small étale site times out at the default budget
/-- Discrete limits of presheaves of sets on the small étale site (instance search times out
without this shortcut). -/
local instance (priority := high) hasLimitsOfShape_discrete_ProperFlatDeformationMapGlobalSection
    (Z : AlgebraicSpaces B S hS) (J : Type u) :
    HasLimitsOfShape (Discrete J) ((smallEtaleRingedTopos B S hS Z).Cᵒᵖ ⥤ Type u) :=
  inferInstance

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for discrete limits on the small étale site times out at the default budget
/-- The terminal sheaf of sets on the small étale site (instance search times out without this
shortcut). -/
local instance (priority := high)
    hasLimitsOfShape_pEmpty_topos_ProperFlatDeformationMapGlobalSection
    (Z : AlgebraicSpaces B S hS) :
    HasLimitsOfShape (Discrete PEmpty.{1}) (smallEtaleRingedTopos B S hS Z).Topos :=
  haveI : HasLimitsOfShape (Discrete PEmpty.{1})
      ((SmallEtale B S hS Z.1)ᵒᵖ ⥤ Type u) :=
    functorCategoryHasLimitsOfShape
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape
    (sheafToPresheaf (SmallEtale.topology B S hS Z.1) (Type u))

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for discrete limits on the small étale site times out at the default budget
/-- Discrete limits of presheaves of sets on the small étale site (instance search times out
without this shortcut). -/
local instance (priority := high) hasLimitsOfShape_discreteF_ProperFlatDeformationMapGlobalSection
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (J : Type u) :
    HasLimitsOfShape (Discrete J) ((SmallEtale B S hS F)ᵒᵖ ⥤ Type u) :=
  inferInstance

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for discrete limits on the small étale site times out at the default budget
/-- Discrete limits indexed by `Type` of presheaves of sets on the small étale site (instance
search times out without this shortcut). -/
local instance (priority := high) hasLimitsOfShape_discrete₀_ProperFlatDeformationMapGlobalSection
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (J : Type) :
    HasLimitsOfShape (Discrete J) ((SmallEtale B S hS F)ᵒᵖ ⥤ Type u) :=
  inferInstance

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for discrete limits on the small étale site times out at the default budget
/-- Discrete limits of sheaves of sets on the small étale site (instance search times out
without this shortcut). -/
local instance (priority := high) hasDiscreteLimits_topos_ProperFlatDeformationMapGlobalSection
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (J : Type) :
    HasLimitsOfShape (Discrete J) (Sheaf (SmallEtale.topology B S hS F) (Type u)) :=
  letI : HasLimitsOfShape (Discrete J) (Type u) := inferInstance
  letI : HasLimitsOfShape (Discrete J) ((SmallEtale B S hS F)ᵒᵖ ⥤ Type u) :=
    hasLimitsOfShape_discrete₀_ProperFlatDeformationMapGlobalSection B S hS F J
  letI : CreatesLimitsOfShape (Discrete J)
      (sheafToPresheaf (SmallEtale.topology B S hS F) (Type u)) :=
    Sheaf.createsLimitsOfShape
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape
    (sheafToPresheaf (SmallEtale.topology B S hS F) (Type u))

/-- The terminal sheaf of sets on the small étale site (instance search times out without this
shortcut). -/
local instance (priority := high) hasTerminal_topos_ProperFlatDeformationMapGlobalSection
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    HasTerminal (Sheaf (SmallEtale.topology B S hS F) (Type u)) :=
  hasDiscreteLimits_topos_ProperFlatDeformationMapGlobalSection B S hS F PEmpty

/-- **Pulling back a function along a composite `X ⟶ T ⟶ T'`**: the pullback of `a ∈ Γ(T', 𝒪)`
along `f ≫ j` is the pullback along `f` of its pullback along `j`. -/
theorem globalFunctionsOfMap_comp {X : AlgebraicSpaces B S hS} {T T' : BigFppfOver B S hS}
    (f : X ⟶ schemeSpace T) (j : T ⟶ T') (a : baseRing B S hS T') :
    globalFunctionsOfMap (f ≫ (schemeSpaceFunctor B S hS).map j) a =
      globalFunctionsOfMap f ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map j).op).hom a) := by
  refine Subtype.ext (funext fun V => ?_)
  change (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (chartToBaseOfMap
      (f ≫ (schemeSpaceFunctor B S hS).map j) _)).op).hom a =
    (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (chartToBaseOfMap f _)).op).hom
      ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map j).op).hom a)
  rw [chartToBaseOfMap_comp, Functor.map_comp, op_comp, Functor.map_comp]
  rfl

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] {iΛ : Spec (.of Λ) ⟶ S}
  {y₀ : CartesianProperFlatSpaces B S hS}
  {hy₀ : (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion).obj y₀ =
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}

/-- Postcomposition with the isomorphism `deformationThickeningIso` is continuous for the small
étale topologies on the two fibres. -/
local instance (x : DeformationObject iΛ (cartesianProperFlatProjection B S hS ⋙
    Over.post B.inclusion) y₀ hy₀) (hsq : RingHom.ker (residueMap x.algebra) ^ 2 = ⊥) :
    (smallEtalePostcomp B S hS (deformationThickeningIso B S hS x hsq).hom
    (isEtale_hom_of_iso B S hS (deformationThickeningIso B S hS x hsq))).IsContinuous
    (SmallEtale.topology B S hS y₀.obj.obj.left.1)
    (SmallEtale.topology B S hS (deformationFibreSpace B S hS x hsq).1) :=
  smallEtalePostcomp_isContinuous B S hS _ _

/-- Postcomposition with the isomorphism `deformationThickeningIso` is cocontinuous for the small
étale topologies on the two fibres. -/
local instance (x : DeformationObject iΛ (cartesianProperFlatProjection B S hS ⋙
    Over.post B.inclusion) y₀ hy₀) (hsq : RingHom.ker (residueMap x.algebra) ^ 2 = ⊥) :
    (smallEtalePostcomp B S hS (deformationThickeningIso B S hS x hsq).hom
    (isEtale_hom_of_iso B S hS (deformationThickeningIso B S hS x hsq))).IsCocontinuous
    (SmallEtale.topology B S hS y₀.obj.obj.left.1)
    (SmallEtale.topology B S hS (deformationFibreSpace B S hS x hsq).1) :=
  smallEtalePostcomp_isCocontinuous B S hS _ _

/-- **The global section of the middle term of a deformation given by a function of its base**:
for `a ∈ Γ(Spec A)`, the étale restriction to `X₀ ≅ Z` of the inverse image along `i : Z ⟶ X'` of
the global section `g^♯a` of `𝒪_{X'}`, `g : X' ⟶ Spec A` the structure morphism, on underlying
sheaves of sets. -/
abbrev deformationFunctionSection
    (x : DeformationObject iΛ (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion) y₀ hy₀)
    (hsq : RingHom.ker (residueMap x.algebra) ^ 2 = ⊥)
    (a : baseRing B S hS ((cartesianProperFlatProjection B S hS).obj x.point)) :=
  (smallEtaleSetRestriction B S hS (deformationThickeningIso B S hS x hsq).hom
    (isEtale_hom_of_iso B S hS (deformationThickeningIso B S hS x hsq))).globalSectionMap
    ((smallEtaleRingedToposHom B S hS (subspaceInclusion B S hS (deformationSpace B S hS x)
        (deformationThickening B S hS x hsq))).toToposHom.inverseImage.globalSectionMap
      (ringOneHom (structureRingSheaf B S hS (deformationSpace B S hS x)) ≫
        (moduleSheafFunctor (structureRingSheaf B S hS (deformationSpace B S hS x))).map
          (unitModuleMul B S hS (deformationSpace B S hS x)
            (globalFunctionsOfMap (deformationStructureMap B S hS x) a))))

variable {x x' : DeformationObject iΛ (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion)
    y₀ hy₀}
  (φ : DeformationMorphism iΛ (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion)
    y₀ hy₀ x x')
  (hsq : RingHom.ker (residueMap x.algebra) ^ 2 = ⊥)
  (hsq' : RingHom.ker (residueMap x'.algebra) ^ 2 = ⊥)

/-- The global section of the middle term given by a function `a` of the base, read through
`(e ≫ i)⁻¹𝒪_{X'} ≅ (i⁻¹𝒪_{X'})|_{X₀}`. -/
theorem deformationFunctionSection_eq
    (x : DeformationObject iΛ (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion) y₀ hy₀)
    (hsq : RingHom.ker (residueMap x.algebra) ^ 2 = ⊥)
    (a : baseRing B S hS ((cartesianProperFlatProjection B S hS).obj x.point)) :
    deformationFunctionSection B S hS x hsq a =
      (smallEtaleRingedToposHom B S hS ((deformationThickeningIso B S hS x hsq).hom ≫
          subspaceInclusion B S hS (deformationSpace B S hS x)
            (deformationThickening B S hS x hsq))).toToposHom.inverseImage.globalSectionMap
          (ringOneHom (structureRingSheaf B S hS (deformationSpace B S hS x)) ≫
            (moduleSheafFunctor (structureRingSheaf B S hS (deformationSpace B S hS x))).map
              (unitModuleMul B S hS (deformationSpace B S hS x)
                (globalFunctionsOfMap (deformationStructureMap B S hS x) a)) :
            ⊤_ _ ⟶ (sheafCompose (SmallEtale.topology B S hS (deformationSpace B S hS x).1)
              (forget CommRingCat.{u})).obj
                (smallEtaleRingedTopos B S hS (deformationSpace B S hS x)).O) ≫
        (sheafCompose (SmallEtale.topology B S hS y₀.obj.obj.left.1) (forget CommRingCat.{u})).map
          (etaleRestrictionRingComparison B S hS (deformationThickeningIso B S hS x hsq).hom
            (isEtale_hom_of_iso B S hS (deformationThickeningIso B S hS x hsq))
            (subspaceInclusion B S hS (deformationSpace B S hS x)
              (deformationThickening B S hS x hsq))).α.hom :=
  (globalSectionMap_comp_forget_map_etaleRestrictionRingComparison_α_hom B S hS
    (deformationThickeningIso B S hS x hsq).hom
    (isEtale_hom_of_iso B S hS (deformationThickeningIso B S hS x hsq))
    (subspaceInclusion B S hS (deformationSpace B S hS x) (deformationThickening B S hS x hsq))
    _).symm

/-- `AlgebraicGeometry.Space.deformationFunctionSection` read through
`(e ≫ i)⁻¹𝒪_{X'} ≅ (i⁻¹𝒪_{X'})|_{X₀}`, as a global section of the restricted inverse image of the
structure sheaf (the middle term of the extension of the deformation). -/
abbrev deformationFunctionSectionE
    (x : DeformationObject iΛ (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion) y₀ hy₀)
    (hsq : RingHom.ker (residueMap x.algebra) ^ 2 = ⊥)
    (a : baseRing B S hS ((cartesianProperFlatProjection B S hS).obj x.point)) :=
  (smallEtaleRingedToposHom B S hS ((deformationThickeningIso B S hS x hsq).hom ≫
      subspaceInclusion B S hS (deformationSpace B S hS x)
        (deformationThickening B S hS x hsq))).toToposHom.inverseImage.globalSectionMap
      (ringOneHom (structureRingSheaf B S hS (deformationSpace B S hS x)) ≫
        (moduleSheafFunctor (structureRingSheaf B S hS (deformationSpace B S hS x))).map
          (unitModuleMul B S hS (deformationSpace B S hS x)
            (globalFunctionsOfMap (deformationStructureMap B S hS x) a)) :
        ⊤_ _ ⟶ (sheafCompose (SmallEtale.topology B S hS (deformationSpace B S hS x).1)
          (forget CommRingCat.{u})).obj
            (smallEtaleRingedTopos B S hS (deformationSpace B S hS x)).O) ≫
    (sheafCompose (SmallEtale.topology B S hS y₀.obj.obj.left.1) (forget CommRingCat.{u})).map
      (etaleRestrictionRingComparison B S hS (deformationThickeningIso B S hS x hsq).hom
        (isEtale_hom_of_iso B S hS (deformationThickeningIso B S hS x hsq))
        (subspaceInclusion B S hS (deformationSpace B S hS x)
          (deformationThickening B S hS x hsq))).α.hom

/-- **The map of middle terms of a morphism of deformations on functions of the base**: for a
morphism `φ : x ⟶ x'` of deformations over `ρ : A ⟶ A'` and `a ∈ Γ(Spec A)`,
`AlgebraicGeometry.Space.deformationMiddleMap` carries the global section of the middle term of
`x` given by `a` to that of `x'` given by `ρ(a)`, on underlying sheaves of sets. -/
theorem deformationFunctionSection_comp_forget_map_deformationMiddleMap
    (a : baseRing B S hS ((cartesianProperFlatProjection B S hS).obj x.point)) :
    deformationFunctionSection B S hS x hsq a ≫
        (sheafCompose (SmallEtale.topology B S hS y₀.obj.obj.left.1) (forget CommRingCat.{u})).map
          (deformationMiddleMap B S hS φ hsq hsq') =
      deformationFunctionSection B S hS x' hsq'
        ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
          ((cartesianProperFlatProjection B S hS).map φ.arrow)).op).hom a) := by
  have hI := globalSectionMap_comp_forget_map_etaleRestrictionInverseImageMap B S hS
    (deformationThickeningIso B S hS x hsq).hom
    (isEtale_hom_of_iso B S hS (deformationThickeningIso B S hS x hsq))
    (subspaceInclusion B S hS (deformationSpace B S hS x) (deformationThickening B S hS x hsq))
    (deformationThickeningIso B S hS x' hsq').hom
    (isEtale_hom_of_iso B S hS (deformationThickeningIso B S hS x' hsq'))
    (subspaceInclusion B S hS (deformationSpace B S hS x') (deformationThickening B S hS x' hsq'))
    (deformationMorphismSpaceMap B S hS φ)
    (deformationThickeningIso_comp_deformationMorphismSpaceMap B S hS φ hsq hsq')
    (ringOneHom (structureRingSheaf B S hS (deformationSpace B S hS x)) ≫
      (moduleSheafFunctor (structureRingSheaf B S hS (deformationSpace B S hS x))).map
        (unitModuleMul B S hS (deformationSpace B S hS x)
          (globalFunctionsOfMap (deformationStructureMap B S hS x) a)))
  have hC := globalSectionMap_unitModuleMul_globalFunctionsOfMap_comp_structureSharpInverseImage
    B S hS (deformationMorphismSpaceMap B S hS φ) (deformationStructureMap B S hS x) a
  have hF : globalFunctionsOfMap (deformationMorphismSpaceMap B S hS φ ≫
      deformationStructureMap B S hS x) a =
      globalFunctionsOfMap (deformationStructureMap B S hS x')
        ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
          ((cartesianProperFlatProjection B S hS).map φ.arrow)).op).hom a) :=
    (congrArg (fun f : deformationSpace B S hS x' ⟶
        schemeSpace ((cartesianProperFlatProjection B S hS).obj x.point) =>
        globalFunctionsOfMap f a)
      (deformationMorphismSpaceMap_comp_structureMap B S hS φ)).trans
      (globalFunctionsOfMap_comp B S hS _ _ a)
  refine (congrArg (· ≫ (sheafCompose (SmallEtale.topology B S hS y₀.obj.obj.left.1)
    (forget CommRingCat.{u})).map (deformationMiddleMap B S hS φ hsq hsq'))
    (deformationFunctionSection_eq B S hS x hsq a)).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) ((sheafCompose (SmallEtale.topology B S hS y₀.obj.obj.left.1)
    (forget CommRingCat.{u})).map_comp _ _).symm).trans ?_
  refine hI.trans ?_
  refine Eq.trans ?_ (deformationFunctionSection_eq B S hS x' hsq' _).symm
  refine congrArg (fun t => (smallEtaleRingedToposHom B S hS ((deformationThickeningIso B S hS x'
      hsq').hom ≫ subspaceInclusion B S hS (deformationSpace B S hS x')
        (deformationThickening B S hS x' hsq'))).toToposHom.inverseImage.globalSectionMap t ≫
      (sheafCompose (SmallEtale.topology B S hS y₀.obj.obj.left.1) (forget CommRingCat.{u})).map
        (etaleRestrictionRingComparison B S hS (deformationThickeningIso B S hS x' hsq').hom
          (isEtale_hom_of_iso B S hS (deformationThickeningIso B S hS x' hsq'))
          (subspaceInclusion B S hS (deformationSpace B S hS x')
            (deformationThickening B S hS x' hsq'))).α.hom) (hC.trans ?_)
  exact congrArg (fun r => ringOneHom (structureRingSheaf B S hS (deformationSpace B S hS x')) ≫
    (moduleSheafFunctor (structureRingSheaf B S hS (deformationSpace B S hS x'))).map
      (unitModuleMul B S hS (deformationSpace B S hS x') r)) hF

/-- `AlgebraicGeometry.Space.deformationFunctionSection_comp_forget_map_deformationMiddleMap`,
read through `(e ≫ i)⁻¹𝒪_{X'} ≅ (i⁻¹𝒪_{X'})|_{X₀}`. -/
theorem deformationFunctionSectionE_comp_forget_map_deformationMiddleMap
    (a : baseRing B S hS ((cartesianProperFlatProjection B S hS).obj x.point)) :
    deformationFunctionSectionE B S hS x hsq a ≫
        (sheafCompose (SmallEtale.topology B S hS y₀.obj.obj.left.1) (forget CommRingCat.{u})).map
          (deformationMiddleMap B S hS φ hsq hsq') =
      deformationFunctionSectionE B S hS x' hsq'
        ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
          ((cartesianProperFlatProjection B S hS).map φ.arrow)).op).hom a) :=
  ((congrArg (· ≫ (sheafCompose (SmallEtale.topology B S hS y₀.obj.obj.left.1)
      (forget CommRingCat.{u})).map (deformationMiddleMap B S hS φ hsq hsq'))
      (deformationFunctionSection_eq B S hS x hsq a)).symm.trans
    (deformationFunctionSection_comp_forget_map_deformationMiddleMap B S hS φ hsq hsq' a)).trans
    (deformationFunctionSection_eq B S hS x' hsq' _)

/-- The base map of a morphism of deformations over `ρ : A ⟶ A'` is `Spec ρ`, through the
identifications of the bases with `Spec A` and `Spec A'`. -/
theorem toScheme_map_map_arrow_comp_deformationSpecIso_hom :
    (BigFppfOver.toScheme B S hS).map ((cartesianProperFlatProjection B S hS).map φ.arrow) ≫
        (deformationSpecIso B S hS x).hom =
      (deformationSpecIso B S hS x').hom ≫
        Spec.map (CommRingCat.ofHom φ.ringHom.hom.toRingHom) := by
  have key : (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion).map φ.arrow ≫
      eqToHom x.base = eqToHom x'.base ≫
        Over.homMk (V := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ x.algebra)) ≫ iΛ))
          (Spec.map (CommRingCat.ofHom φ.ringHom.hom.toRingHom)) (by
            change Spec.map _ ≫ Spec.map _ ≫ iΛ = Spec.map _ ≫ iΛ
            rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
            exact congrArg (fun f => Spec.map (CommRingCat.ofHom f) ≫ iΛ)
              φ.ringHom.hom.comp_algebraMap) := by
    ext1
    have hb := φ.arrow_base
    simp only [Over.comp_left, Over.homMk_left]
    rw [← hb, Over.eqToHom_left, Over.eqToHom_left]
    simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  have h := congrArg CommaMorphism.left key
  simp only [Over.comp_left, Over.homMk_left, Over.eqToHom_left] at h
  exact h

/-- **Pulling back functions along a morphism of deformations is its ring map**: through
`A ≅ Γ(Spec A)` and `A' ≅ Γ(Spec A')`, pullback of functions along the base map of `φ` is
`ρ : A ⟶ A'`. -/
theorem Γ_map_map_arrow_deformationAlgebraEquiv (a : x.algebra) :
    (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
        ((cartesianProperFlatProjection B S hS).map φ.arrow)).op).hom
        (deformationAlgebraEquiv B S hS x a) =
      deformationAlgebraEquiv B S hS x' (φ.ringHom.hom a) := by
  have hM : (Scheme.ΓSpecIso (CommRingCat.of x.algebra)).inv ≫
      Scheme.Γ.map (deformationSpecIso B S hS x).hom.op ≫
        Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
          ((cartesianProperFlatProjection B S hS).map φ.arrow)).op =
      CommRingCat.ofHom φ.ringHom.hom.toRingHom ≫
        (Scheme.ΓSpecIso (CommRingCat.of x'.algebra)).inv ≫
        Scheme.Γ.map (deformationSpecIso B S hS x').hom.op := by
    have h1 : Scheme.Γ.map (deformationSpecIso B S hS x).hom.op ≫
        Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
          ((cartesianProperFlatProjection B S hS).map φ.arrow)).op =
        Scheme.Γ.map (Spec.map (CommRingCat.ofHom φ.ringHom.hom.toRingHom)).op ≫
          Scheme.Γ.map (deformationSpecIso B S hS x').hom.op :=
      (Scheme.Γ.map_comp (deformationSpecIso B S hS x).hom.op ((BigFppfOver.toScheme B S hS).map
          ((cartesianProperFlatProjection B S hS).map φ.arrow)).op).symm.trans
        ((congrArg (fun m : (BigFppfOver.toScheme B S hS).obj
            ((cartesianProperFlatProjection B S hS).obj x'.point) ⟶
              Spec (CommRingCat.of x.algebra) =>
            Scheme.Γ.map m.op)
          (toScheme_map_map_arrow_comp_deformationSpecIso_hom B S hS φ)).trans
        (Scheme.Γ.map_comp (Spec.map (CommRingCat.ofHom φ.ringHom.hom.toRingHom)).op
          (deformationSpecIso B S hS x').hom.op))
    refine (congrArg (_ ≫ ·) h1).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine Eq.trans ?_ (Category.assoc _ _ _)
    exact congrArg (· ≫ _) (Scheme.ΓSpecIso_inv_naturality _).symm
  exact congrArg (fun m => m.hom a) hM


/-- A finite-dimensional `k`-module `W` is a `kᵐᵒᵖ`-module via `MulOpposite.unop`. -/
local instance (W : FGModuleCat.{u} k) : Module kᵐᵒᵖ W :=
  Module.oppositeOfCommSemiring k W

/-- The actions of `k` and `kᵐᵒᵖ` on a finite-dimensional `k`-module agree. -/
local instance (W : FGModuleCat.{u} k) : IsCentralScalar k W :=
  Module.isCentralScalar_oppositeOfCommSemiring k W

/-- For `A = k[V]` with square-zero maximal ideal, the inverse of `squareZeroKerOfEqIso` sends
`v ∈ V` to the element `(0, v)` of `k[V]`, transported to `A` along `hA`. -/
theorem _root_.Deformation.Artin.squareZeroKerOfEqIso_inv_apply_coe
    (A : ArtinianLocalAlgCat.{u, u, u} Λ k) (V : FGModuleCat.{u} k)
    (hA : A = (artinianSquareZeroExtensionFunctor Λ k).obj V)
    (hsq : RingHom.ker (residueMap A) ^ 2 = ⊥)
    (v : (forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)).obj V) :
    ((show RingHom.ker (residueMap A) from (squareZeroKerOfEqIso Λ A V hA hsq).inv.hom v).1 : A) =
      (eqToHom hA.symm).hom.toRingHom (TrivSqZeroExt.inr (R := k) (M := V.obj) v) := by
  subst hA
  rfl

section Tangent

variable (V : FGModuleCat.{u} k)
  (hx : x.algebra = (artinianSquareZeroExtensionFunctor Λ k).obj V)

/-- The element of `Γ(Spec A)` given by `v ∈ V`, for a deformation over `A = k[V]`. -/
abbrev deformationTangentFunction (v : (forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)).obj V) :
    baseRing B S hS ((cartesianProperFlatProjection B S hS).obj x.point) :=
  ((RingHom.squareZeroKerRingEquivIso _ _ (deformationAlgebraEquiv B S hS x)
    (baseResidueFieldEquiv B S hS hy₀) (deformationBaseImmersion_Γ_comp B S hS x)
    (deformationBaseImmersion_Γ_surjective B S hS x)
    (deformationBaseImmersion_Γ_ker_sq B S hS x (ker_residueMap_sq_of_eq B S hS V x hx))
    (residueMap_surjective' x.algebra) (ker_residueMap_sq_of_eq B S hS V x hx)).inv.hom
    ((squareZeroKerOfEqIso Λ x.algebra V hx (ker_residueMap_sq_of_eq B S hS V x hx)).inv.hom v)).1

/-- **The section `1 ⊗ v` of `𝒪_{X₀} ⊗_k V` in the extension of a deformation over `k[V]`**,
sectionwise: its inclusion into the middle term is the value of the global section given by the
function `v` of the base (`AlgebraicGeometry.Space.deformationFunctionSection`). -/
theorem deformationTangentExtension_incl_baseRingTensorSection
    (v : (forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)).obj V)
    (W : (SmallEtale B S hS y₀.obj.obj.left.1)ᵒᵖ)
    (p : (sectionsFunctor _ W).obj
      (⊤_ Sheaf (SmallEtale.topology B S hS y₀.obj.obj.left.1) (Type u))) :
    (deformationTangentExtension B S hS V x hx).incl
        ((baseRingTensorSection B S hS y₀.obj.obj.left (baseFieldHom B S hS (hy₀ := hy₀))
          ((forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)).obj V) v).val.app W
          (1 : (structureRingSheaf B S hS y₀.obj.obj.left).obj.obj W)) =
      (sectionsFunctor _ W).map (deformationFunctionSection B S hS x
        (ker_residueMap_sq_of_eq B S hS V x hx) (deformationTangentFunction B S hS V hx v)) p := by
  have hm := baseRingTensorSection_map B S hS y₀.obj.obj.left (baseFieldHom B S hS (hy₀ := hy₀))
    (squareZeroKerOfEqIso Λ x.algebra V hx (ker_residueMap_sq_of_eq B S hS V x hx)).inv v
  have hK := incl_baseRingTensorSection_comp_deformationTensorLinearIdealIso_inv B S hS
    (ker_residueMap_sq_of_eq B S hS V x hx) (tangentRetraction B S hS V x hx)
    (map_arrow_comp_tangentRetraction B S hS V x hx)
    ((squareZeroKerOfEqIso Λ x.algebra V hx (ker_residueMap_sq_of_eq B S hS V x hx)).inv.hom v) W p
  refine Eq.trans ?_ hK
  have e1 := Deformation.AlgebraExtension.incl_transportKernel
    (deformationKernelExtension B S hS (ker_residueMap_sq_of_eq B S hS V x hx)
      (tangentRetraction B S hS V x hx) (map_arrow_comp_tangentRetraction B S hS V x hx))
    ((baseRingTensorModule B S hS y₀.obj.obj.left (baseFieldHom B S hS (hy₀ := hy₀))).mapIso
      (squareZeroKerOfEqIso Λ x.algebra V hx (ker_residueMap_sq_of_eq B S hS V x hx)))
    ((baseRingTensorSection B S hS y₀.obj.obj.left (baseFieldHom B S hS (hy₀ := hy₀))
          ((forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)).obj V) v).val.app W
          (1 : (structureRingSheaf B S hS y₀.obj.obj.left).obj.obj W))
  have e2 := Deformation.AlgebraExtension.incl_transportKernel
    (deformationTensorBaseExtension B S hS (ker_residueMap_sq_of_eq B S hS V x hx)
      (tangentRetraction B S hS V x hx) (map_arrow_comp_tangentRetraction B S hS V x hx))
    (deformationTensorLinearIdealIso B S hS x (ker_residueMap_sq_of_eq B S hS V x hx))
    (((baseRingTensorModule B S hS y₀.obj.obj.left (baseFieldHom B S hS (hy₀ := hy₀))).map
      (squareZeroKerOfEqIso Λ x.algebra V hx (ker_residueMap_sq_of_eq B S hS V x hx)).inv).val.app W
      ((baseRingTensorSection B S hS y₀.obj.obj.left (baseFieldHom B S hS (hy₀ := hy₀))
          ((forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)).obj V) v).val.app W
          (1 : (structureRingSheaf B S hS y₀.obj.obj.left).obj.obj W)))
  refine e1.trans (e2.trans ?_)
  refine congrArg (deformationTensorBaseExtension B S hS (ker_residueMap_sq_of_eq B S hS V x hx)
    (tangentRetraction B S hS V x hx) (map_arrow_comp_tangentRetraction B S hS V x hx)).incl ?_
  have h3 := SheafOfModules.comp_val_app_apply
    (baseRingTensorSection B S hS y₀.obj.obj.left (baseFieldHom B S hS (hy₀ := hy₀))
      (RingHom.squareZeroKer (residueMap x.algebra) (residueMap_surjective' x.algebra)
        (ker_residueMap_sq_of_eq B S hS V x hx))
      ((squareZeroKerOfEqIso Λ x.algebra V hx (ker_residueMap_sq_of_eq B S hS V x hx)).inv.hom v))
    (deformationTensorLinearIdealIso B S hS x (ker_residueMap_sq_of_eq B S hS V x hx)).inv W
    (1 : (structureRingSheaf B S hS y₀.obj.obj.left).obj.obj W)
  have h4 := SheafOfModules.comp_val_app_apply
    (baseRingTensorSection B S hS y₀.obj.obj.left (baseFieldHom B S hS (hy₀ := hy₀))
          ((forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)).obj V) v)
    ((baseRingTensorModule B S hS y₀.obj.obj.left (baseFieldHom B S hS (hy₀ := hy₀))).map
      (squareZeroKerOfEqIso Λ x.algebra V hx (ker_residueMap_sq_of_eq B S hS V x hx)).inv) W
    (1 : (structureRingSheaf B S hS y₀.obj.obj.left).obj.obj W)
  have h5 := congrArg (fun t => t.val.app W
    (1 : (structureRingSheaf B S hS y₀.obj.obj.left).obj.obj W)) hm
  exact (congrArg ((deformationTensorLinearIdealIso B S hS x
    (ker_residueMap_sq_of_eq B S hS V x hx)).inv.val.app W) (h4.symm.trans h5)).trans h3.symm

/-- The function of the base given by `v ∈ V` is the image of `ε v ∈ k[V]` in `Γ(Spec A)`. -/
theorem deformationTangentFunction_eq (v : (forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)).obj V) :
    deformationTangentFunction B S hS V hx v =
      deformationAlgebraEquiv B S hS x
        ((eqToHom hx.symm).hom.toRingHom (TrivSqZeroExt.inr (R := k) (M := V.obj) v)) :=
  congrArg (deformationAlgebraEquiv B S hS x)
    (squareZeroKerOfEqIso_inv_apply_coe x.algebra V hx (ker_residueMap_sq_of_eq B S hS V x hx) v)

variable (V' : FGModuleCat.{u} k)
  (hx' : x'.algebra = (artinianSquareZeroExtensionFunctor Λ k).obj V')

/-- **Functions of the base along a morphism of deformations over `k[f]`**: pulling back the
function given by `v ∈ V` gives the function given by `f v ∈ V'`. -/
theorem Γ_map_map_arrow_deformationTangentFunction (f : V ⟶ V')
    (hρ : φ.ringHom = eqToHom hx ≫ (artinianSquareZeroExtensionFunctor Λ k).map f ≫
      eqToHom hx'.symm)
    (v : (forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)).obj V) :
    (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
        ((cartesianProperFlatProjection B S hS).map φ.arrow)).op).hom
        (deformationTangentFunction B S hS V hx v) =
      deformationTangentFunction B S hS V' hx'
        (((forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)).map f).hom v) := by
  rw [deformationTangentFunction_eq, deformationTangentFunction_eq,
    Γ_map_map_arrow_deformationAlgebraEquiv]
  refine congrArg (deformationAlgebraEquiv B S hS x') ?_
  have key : ∀ (A A' : ArtinianLocalAlgCat.{u, u, u} Λ k)
      (h : A = (artinianSquareZeroExtensionFunctor Λ k).obj V)
      (h' : A' = (artinianSquareZeroExtensionFunctor Λ k).obj V') (ρ : A ⟶ A')
      (hρ : ρ = eqToHom h ≫ (artinianSquareZeroExtensionFunctor Λ k).map f ≫ eqToHom h'.symm),
      ρ.hom ((eqToHom h.symm).hom.toRingHom (TrivSqZeroExt.inr (R := k) (M := V.obj) v)) =
        (eqToHom h'.symm).hom.toRingHom (TrivSqZeroExt.inr (R := k) (M := V'.obj)
          (((forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)).map f).hom v)) := by
    intro A A' h h' ρ hρ
    subst h h' hρ
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    change ((artinianSquareZeroExtensionFunctor Λ k).map f).hom (TrivSqZeroExt.inr v) =
      TrivSqZeroExt.inr _
    exact TrivSqZeroExt.map_inr (f := f.hom.hom) v
  exact key x.algebra x'.algebra hx hx' φ.ringHom hρ

/-- `deformationTangentExtension_incl_baseRingTensorSection`, read through
`(e ≫ i)⁻¹𝒪_{X'} ≅ (i⁻¹𝒪_{X'})|_{X₀}`. -/
private theorem incl_baseRingTensorSection_eq_sectionE
    (V : FGModuleCat.{u} k) (hx : x.algebra = (artinianSquareZeroExtensionFunctor Λ k).obj V)
    (v : (forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)).obj V)
    (W : (SmallEtale B S hS y₀.obj.obj.left.1)ᵒᵖ)
    (p : (sectionsFunctor _ W).obj
      (⊤_ Sheaf (SmallEtale.topology B S hS y₀.obj.obj.left.1) (Type u))) :
    (deformationTangentExtension B S hS V x hx).incl
        ((baseRingTensorSection B S hS y₀.obj.obj.left (baseFieldHom B S hS (hy₀ := hy₀))
          ((forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)).obj V) v).val.app W
          (1 : (structureRingSheaf B S hS y₀.obj.obj.left).obj.obj W)) =
      (sectionsFunctor _ W).map (deformationFunctionSectionE B S hS x
        (ker_residueMap_sq_of_eq B S hS V x hx) (deformationTangentFunction B S hS V hx v)) p :=
  (deformationTangentExtension_incl_baseRingTensorSection B S hS V hx v W p).trans
    (sectionsFunctor_map_congr (deformationFunctionSection_eq B S hS x
      (ker_residueMap_sq_of_eq B S hS V x hx) (deformationTangentFunction B S hS V hx v)) W p)

/-- **The map of ideals of a morphism of deformations over `k[f]` is `𝒪_{X₀} ⊗ f`** (the
computation in the proof of Stacks 0D1K): for a morphism of deformations over
`k[f] : k[V] ⟶ k[V']`, the map `𝒪_{X₀} ⊗_k V ⟶ 𝒪_{X₀} ⊗_k V'` of ideals of their extensions
induced by the map of middle terms is `𝒪_{X₀} ⊗_k f`. -/
theorem deformationTangentKernelMap_eq (f : V ⟶ V')
    (hρ : φ.ringHom = eqToHom hx ≫ (artinianSquareZeroExtensionFunctor Λ k).map f ≫
      eqToHom hx'.symm) :
    deformationTangentKernelMap B S hS φ V V' hx hx' =
      (baseRingTensorModule B S hS y₀.obj.obj.left (baseFieldHom B S hS (hy₀ := hy₀))).map
        ((forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)).map f) := by
  refine baseRingTensorModule_hom_ext B S hS y₀.obj.obj.left (baseFieldHom B S hS (hy₀ := hy₀))
    fun v => ?_
  refine Eq.trans ?_ (baseRingTensorSection_map B S hS y₀.obj.obj.left
    (baseFieldHom B S hS (hy₀ := hy₀)) ((forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)).map f)
    v).symm
  refine Deformation.AlgebraExtension.hom_ext_of_incl
    (J := SmallEtale.topology B S hS y₀.obj.obj.left.1)
    (deformationTangentExtension B S hS V' x' hx') fun W p => ?_
  have h1 := SheafOfModules.comp_val_app_apply
    (baseRingTensorSection B S hS y₀.obj.obj.left (baseFieldHom B S hS (hy₀ := hy₀))
      ((forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)).obj V) v)
    (deformationTangentKernelMap B S hS φ V V' hx hx') W
    (1 : (structureRingSheaf B S hS y₀.obj.obj.left).obj.obj W)
  have h3 := incl_baseRingTensorSection_eq_sectionE B S hS V hx v W p
  have h5 := Γ_map_map_arrow_deformationTangentFunction B S hS φ V hx V' hx' f hρ v
  have h6 := incl_baseRingTensorSection_eq_sectionE B S hS V' hx'
    (((forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)).map f).hom v) W p
  have hz := deformationFunctionSectionE_comp_forget_map_deformationMiddleMap B S hS φ
    (ker_residueMap_sq_of_eq B S hS V x hx) (ker_residueMap_sq_of_eq B S hS V' x' hx')
    (deformationTangentFunction B S hS V hx v)
  refine (congrArg (deformationTangentExtension B S hS V' x' hx').incl h1).trans ?_
  refine (Deformation.AlgebraExtension.incl_inducedKernelMap_val_app_eq.{u, u + 1, u}
    (J := SmallEtale.topology B S hS y₀.obj.obj.left.1)
    (deformationTangentExtension B S hS V x hx) (deformationTangentExtension B S hS V' x' hx')
    (deformationTangentMiddleMap B S hS φ V V' hx hx')
    (deformationTangentMiddleMap_comp_reduction B S hS φ V V' hx hx') _ _ _ p h3 hz).trans ?_
  exact (congrArg (fun t => (sectionsFunctor _ W).map (deformationFunctionSectionE B S hS x'
    (ker_residueMap_sq_of_eq B S hS V' x' hx') t) p) h5).trans h6.symm

end Tangent

end AlgebraicGeometry.Space

end
