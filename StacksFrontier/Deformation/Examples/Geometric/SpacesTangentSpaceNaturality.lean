module

public import StacksFrontier.Algebra.Module.OppositeOfCommSemiring
public import StacksFrontier.Deformation.Examples.Geometric.SpacesTangentSpaceMap

/-!
# The class of a deformation of an algebraic space over `k[V]` is natural in `V`

For a morphism `φ : x ⟶ y` of the deformation category of an algebraic space `X` over `k`
(Stacks 0E3Z) lying over `k[g] : k[V] ⟶ k[W]`, the morphism of extensions of `φ` is along
`𝒪_X ⊗ g : 𝒪_X ⊗_k V ⟶ 𝒪_X ⊗_k W` (`Deformation.Examples.spaceTangentKernelMap_eq`), so the class
of `y` in `Ext¹(NL_{X/k}, 𝒪_X ⊗_k W)` is the class of `x` pushed along `𝒪_X ⊗ g`
(`Deformation.Examples.spaceTangentFiberClass_map`). This is the naturality in `V` used in the
proof of [Stacks Project, Tag 0E41] to make the classes `k`-linear.

## References

* [Stacks Project, Tag 0E41](https://stacks.math.columbia.edu/tag/0E41)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

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

/-- A finite-dimensional `k`-vector space is a `kᵐᵒᵖ`-module, with `op a` acting as `a`. -/
local instance (M : FGModuleCat.{u} k) : Module kᵐᵒᵖ M :=
  Module.oppositeOfCommSemiring k M

/-- The actions of `k` and `kᵐᵒᵖ` on a finite-dimensional `k`-vector space agree. -/
local instance (M : FGModuleCat.{u} k) : IsCentralScalar k M :=
  Module.isCentralScalar_oppositeOfCommSemiring k M

/-- **Pulling back functions along `Spec A' ⟶ Spec A` is the ring map `A ⟶ A'`**, through
`A ≃ Γ(Spec A)`. -/
theorem Γ_map_spaceBaseOverMap_spaceDefoAlgebraEquiv {A A' : ArtinianLocalAlgCat.{u, u, u} Λ k}
    (f : A ⟶ A') (a : A) :
    (Scheme.Γ.map ((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map
        (spaceBaseOverMap B hΛ hSpec f)).op).hom
        (spaceDefoAlgebraEquiv (B := B) (hΛ := hΛ) (hSpec := hSpec) A a) =
      spaceDefoAlgebraEquiv (B := B) (hΛ := hΛ) (hSpec := hSpec) A' (f.hom a) := by
  have hm : (BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map (spaceBaseOverMap B hΛ hSpec f) =
      Spec.map (CommRingCat.ofHom f.hom.toRingHom) := B.inclusion.map_preimage _
  rw [hm]
  have h := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f.hom.toRingHom)
  exact (congrArg (fun g => g.hom a) h).symm

variable {V W : FGModuleCat.{u} k}
  {x : (spaceDeformationProjection B hΛ hSpec X hX toK).Fiber
    ((squareZeroExtensionArtinian Λ k).obj V)}
  {y : (spaceDeformationProjection B hΛ hSpec X hX toK).Fiber
    ((squareZeroExtensionArtinian Λ k).obj W)}
  (g : V ⟶ W) (φ : x.1 ⟶ y.1)
  (hφ : φ.left.base = eqToHom (spaceFiber_base_eq B hΛ hSpec X hX toK x) ≫
    (squareZeroExtensionArtinian Λ k).map g ≫
      eqToHom (spaceFiber_base_eq B hΛ hSpec X hX toK y).symm)

include hφ in
/-- The constants are preserved by a morphism over `k[g]`. -/
theorem spaceFiberConstants_comp :
    spaceFiberConstants B hΛ hSpec X hX toK x ≫ φ.left.base =
      spaceFiberConstants B hΛ hSpec X hX toK y := by
  rw [hφ]
  simp only [spaceFiberConstants, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp]
  rw [← Category.assoc, spaceConstants_comp_map]

include hφ in
/-- The retractions of the constants are compatible along a morphism over `k[g]`. -/
theorem spaceBaseOverMap_comp_spaceTangentRetraction :
    spaceBaseOverMap B hΛ hSpec φ.left.base ≫ spaceTangentRetraction B hΛ hSpec X hX toK x =
      spaceTangentRetraction B hΛ hSpec X hX toK y :=
  (spaceBaseOverMap_comp B hΛ hSpec _ _).symm.trans
    (congrArg (spaceBaseOverMap B hΛ hSpec) (spaceFiberConstants_comp B hΛ hSpec X hX toK g φ hφ))

/-- The homomorphism of middle terms of the extensions of a morphism over `k[g]`. -/
def spaceTangentMiddleMap :
    (spaceTangentExtension B hΛ hSpec X hX toK x).extension ⟶
      (spaceTangentExtension B hΛ hSpec X hX toK y).extension :=
  spaceDefoMiddleMap B hΛ hSpec X hX toK φ (spaceFiber_maximalIdeal_sq B hΛ hSpec X hX toK x)
    (spaceFiber_maximalIdeal_sq B hΛ hSpec X hX toK y)

/-- The homomorphism of middle terms of a morphism over `k[g]` commutes with the reductions. -/
theorem spaceTangentMiddleMap_comp_reduction :
    spaceTangentMiddleMap B hΛ hSpec X hX toK φ ≫
        (spaceTangentExtension B hΛ hSpec X hX toK y).reduction =
      (spaceTangentExtension B hΛ hSpec X hX toK x).reduction :=
  spaceDefoMiddleMap_comp_reduction B hΛ hSpec X hX toK φ
    (spaceFiber_maximalIdeal_sq B hΛ hSpec X hX toK y) _
    (spaceDefoBaseImmersion_comp_spaceTangentRetraction B hΛ hSpec X hX toK x) _
    (spaceDefoBaseImmersion_comp_spaceTangentRetraction B hΛ hSpec X hX toK y)

include hφ in
/-- The homomorphism of middle terms of a morphism over `k[g]` commutes with the structure
maps of the extensions. -/
theorem algebraMap_comp_spaceTangentMiddleMap :
    (spaceTangentExtension B hΛ hSpec X hX toK x).algebraMap ≫
        spaceTangentMiddleMap B hΛ hSpec X hX toK φ =
      (spaceTangentExtension B hΛ hSpec X hX toK y).algebraMap :=
  algebraMap_comp_spaceDefoMiddleMap B hΛ hSpec X hX toK φ
    (spaceFiber_maximalIdeal_sq B hΛ hSpec X hX toK y) _
    (spaceDefoBaseImmersion_comp_spaceTangentRetraction B hΛ hSpec X hX toK x) _
    (spaceDefoBaseImmersion_comp_spaceTangentRetraction B hΛ hSpec X hX toK y)
    (spaceDefoMorphismSpaceMap_comp_retractedStructureMap B hΛ hSpec X hX toK φ _ _
      (spaceBaseOverMap_comp_spaceTangentRetraction B hΛ hSpec X hX toK g φ hφ))

/-- The map of ideals `𝒪_X ⊗_k V ⟶ 𝒪_X ⊗_k W` induced by a morphism. -/
def spaceTangentKernelMap :=
  inducedKernelMap.{u, u + 1, u} (J := SmallEtale.topology B (Spec (.of Λ)) hΛ X)
    (spaceTangentExtension B hΛ hSpec X hX toK x) (spaceTangentExtension B hΛ hSpec X hX toK y)
    (spaceTangentMiddleMap B hΛ hSpec X hX toK φ)
    (spaceTangentMiddleMap_comp_reduction B hΛ hSpec X hX toK φ)

/-- **The morphism of extensions of a morphism over `k[g]`**, along the induced map of ideals. -/
def spaceTangentMapAlong :
    MapAlong.{u, u + 1, u} (J := SmallEtale.topology B (Spec (.of Λ)) hΛ X)
      (spaceTangentKernelMap B hΛ hSpec X hX toK φ)
      (spaceTangentExtension B hΛ hSpec X hX toK x) (spaceTangentExtension B hΛ hSpec X hX toK y) :=
  mapAlongInducedKernelMap.{u, u + 1, u} (J := SmallEtale.topology B (Spec (.of Λ)) hΛ X)
    _ _ _ _ (algebraMap_comp_spaceTangentMiddleMap B hΛ hSpec X hX toK g φ hφ)

variable (x) in
/-- The element of `Γ(Spec A)` given by `v ∈ V`, for a point over `A = k[V]`. -/
abbrev spaceTangentFunction (v : (forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)).obj V) :
    baseRing B (Spec (.of Λ)) hΛ (spaceBaseOver B hΛ hSpec x.1.left.base) :=
  ((RingHom.squareZeroKerRingEquivIso _ _
    (spaceDefoAlgebraEquiv (B := B) (hΛ := hΛ) (hSpec := hSpec) x.1.left.base)
    (spaceDefoAlgebraEquiv (B := B) (hΛ := hΛ) (hSpec := hSpec) (residueFieldBase Λ k))
    (spaceDefoBaseImmersion_Γ_comp B hΛ hSpec X hX toK x.1)
    (spaceDefoBaseImmersion_Γ_surjective B hΛ hSpec X hX toK x.1)
    (spaceDefoBaseImmersion_Γ_ker_sq B hΛ hSpec X hX toK x.1
      (spaceFiber_maximalIdeal_sq B hΛ hSpec X hX toK x))
    (residueMap_surjective' x.1.left.base)
    (ker_residueMap_sq_of_maximalIdeal_sq
      (spaceFiber_maximalIdeal_sq B hΛ hSpec X hX toK x))).inv.hom
    ((spaceTangentKernelIso B hΛ hSpec X hX toK x).inv.hom v)).1

variable (x) in
/-- **The section `1 ⊗ v` of `𝒪_X ⊗_k V` in the extension of a point over `k[V]`**, sectionwise:
its inclusion into the middle term is the value of the global section given by the function `v`
of the base. -/
theorem spaceTangentExtension_incl_baseRingTensorSection
    (v : (forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)).obj V)
    (U : (SmallEtale B (Spec (.of Λ)) hΛ X)ᵒᵖ)
    (p : (sectionsFunctor _ U).obj
      (⊤_ Sheaf (SmallEtale.topology B (Spec (.of Λ)) hΛ X) (Type u))) :
    (spaceTangentExtension B hΛ hSpec X hX toK x).incl
        ((baseRingTensorSection B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)
          (spaceDefoFieldHom B hΛ hSpec X hX toK)
          ((forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)).obj V) v).val.app U
          (1 : (structureRingSheaf B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)).obj.obj U)) =
      (sectionsFunctor _ U).map (spaceDefoFunctionSection B hΛ hSpec X hX toK x.1
        (spaceFiber_maximalIdeal_sq B hΛ hSpec X hX toK x)
        (spaceTangentFunction B hΛ hSpec X hX toK x v)) p := by
  have hm := baseRingTensorSection_map B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)
    (spaceDefoFieldHom B hΛ hSpec X hX toK) (spaceTangentKernelIso B hΛ hSpec X hX toK x).inv v
  have hK := incl_baseRingTensorSection_comp_spaceDefoTensorLinearIdealIso_inv B hΛ hSpec X hX toK
    (spaceFiber_maximalIdeal_sq B hΛ hSpec X hX toK x)
    (spaceTangentRetraction B hΛ hSpec X hX toK x)
    (spaceDefoBaseImmersion_comp_spaceTangentRetraction B hΛ hSpec X hX toK x)
    ((spaceTangentKernelIso B hΛ hSpec X hX toK x).inv.hom v) U p
  refine Eq.trans ?_ hK
  have e1 := Deformation.AlgebraExtension.incl_transportKernel
    (spaceDefoKernelExtension B hΛ hSpec X hX toK (spaceFiber_maximalIdeal_sq B hΛ hSpec X hX toK x)
      (spaceTangentRetraction B hΛ hSpec X hX toK x)
      (spaceDefoBaseImmersion_comp_spaceTangentRetraction B hΛ hSpec X hX toK x))
    ((baseRingTensorModule B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)
      (spaceDefoFieldHom B hΛ hSpec X hX toK)).mapIso (spaceTangentKernelIso B hΛ hSpec X hX toK x))
    ((baseRingTensorSection B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)
      (spaceDefoFieldHom B hΛ hSpec X hX toK)
          ((forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)).obj V) v).val.app U
          (1 : (structureRingSheaf B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)).obj.obj U))
  have e2 := Deformation.AlgebraExtension.incl_transportKernel
    (spaceDefoTensorBaseExtension B hΛ hSpec X hX toK
      (spaceFiber_maximalIdeal_sq B hΛ hSpec X hX toK x)
      (spaceTangentRetraction B hΛ hSpec X hX toK x)
      (spaceDefoBaseImmersion_comp_spaceTangentRetraction B hΛ hSpec X hX toK x))
    (spaceDefoTensorLinearIdealIso B hΛ hSpec X hX toK x.1
      (spaceFiber_maximalIdeal_sq B hΛ hSpec X hX toK x))
    (((baseRingTensorModule B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)
      (spaceDefoFieldHom B hΛ hSpec X hX toK)).map
      (spaceTangentKernelIso B hΛ hSpec X hX toK x).inv).val.app U
      ((baseRingTensorSection B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)
        (spaceDefoFieldHom B hΛ hSpec X hX toK)
          ((forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)).obj V) v).val.app U
          (1 : (structureRingSheaf B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)).obj.obj U)))
  refine e1.trans (e2.trans ?_)
  refine congrArg (spaceDefoTensorBaseExtension B hΛ hSpec X hX toK
    (spaceFiber_maximalIdeal_sq B hΛ hSpec X hX toK x)
    (spaceTangentRetraction B hΛ hSpec X hX toK x)
    (spaceDefoBaseImmersion_comp_spaceTangentRetraction B hΛ hSpec X hX toK x)).incl ?_
  have h3 := SheafOfModules.comp_val_app_apply
    (baseRingTensorSection B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)
      (spaceDefoFieldHom B hΛ hSpec X hX toK)
      (RingHom.squareZeroKer (residueMap x.1.left.base) (residueMap_surjective' x.1.left.base)
        (ker_residueMap_sq_of_maximalIdeal_sq (spaceFiber_maximalIdeal_sq B hΛ hSpec X hX toK x)))
      ((spaceTangentKernelIso B hΛ hSpec X hX toK x).inv.hom v))
    (spaceDefoTensorLinearIdealIso B hΛ hSpec X hX toK x.1
      (spaceFiber_maximalIdeal_sq B hΛ hSpec X hX toK x)).inv U
    (1 : (structureRingSheaf B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)).obj.obj U)
  have h4 := SheafOfModules.comp_val_app_apply
    (baseRingTensorSection B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)
      (spaceDefoFieldHom B hΛ hSpec X hX toK)
          ((forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)).obj V) v)
    ((baseRingTensorModule B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)
      (spaceDefoFieldHom B hΛ hSpec X hX toK)).map
      (spaceTangentKernelIso B hΛ hSpec X hX toK x).inv) U
    (1 : (structureRingSheaf B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)).obj.obj U)
  have h5 := congrArg (fun t => t.val.app U
    (1 : (structureRingSheaf B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)).obj.obj U)) hm
  exact (congrArg ((spaceDefoTensorLinearIdealIso B hΛ hSpec X hX toK x.1
    (spaceFiber_maximalIdeal_sq B hΛ hSpec X hX toK x)).inv.val.app U) (h4.symm.trans h5)).trans
    h3.symm

variable (x) in
/-- The function of the base given by `v ∈ V` is the image of `ε v ∈ k[V]` in `Γ(Spec A)`. -/
theorem spaceTangentFunction_eq (v : (forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)).obj V) :
    spaceTangentFunction B hΛ hSpec X hX toK x v =
      spaceDefoAlgebraEquiv (B := B) (hΛ := hΛ) (hSpec := hSpec) x.1.left.base
        ((eqToHom (spaceFiber_base_eq B hΛ hSpec X hX toK x).symm).hom.toRingHom
          (TrivSqZeroExt.inr (R := k) (M := V.obj) v)) :=
  congrArg (spaceDefoAlgebraEquiv (B := B) (hΛ := hΛ) (hSpec := hSpec) x.1.left.base)
    (squareZeroKerOfEqIso_inv_apply_coe x.1.left.base V
      (spaceFiber_base_eq B hΛ hSpec X hX toK x) _ v)

include hφ in
/-- **Functions of the base along a morphism over `k[g]`**: pulling back the function given by
`v ∈ V` gives the function given by `g v ∈ W`. -/
theorem Γ_map_spaceTangentFunction (v : (forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)).obj V) :
    (Scheme.Γ.map ((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map
        (spaceBaseOverMap B hΛ hSpec φ.left.base)).op).hom
        (spaceTangentFunction B hΛ hSpec X hX toK x v) =
      spaceTangentFunction B hΛ hSpec X hX toK y
        (((forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)).map g).hom v) := by
  rw [spaceTangentFunction_eq, spaceTangentFunction_eq,
    Γ_map_spaceBaseOverMap_spaceDefoAlgebraEquiv]
  refine congrArg (spaceDefoAlgebraEquiv (B := B) (hΛ := hΛ) (hSpec := hSpec) y.1.left.base) ?_
  have key : ∀ (A A' : ArtinianLocalAlgCat.{u, u, u} Λ k)
      (h : A = (squareZeroExtensionArtinian Λ k).obj V)
      (h' : A' = (squareZeroExtensionArtinian Λ k).obj W) (ρ : A ⟶ A')
      (hρ : ρ = eqToHom h ≫ (squareZeroExtensionArtinian Λ k).map g ≫ eqToHom h'.symm),
      ρ.hom ((eqToHom h.symm).hom.toRingHom (TrivSqZeroExt.inr (R := k) (M := V.obj) v)) =
        (eqToHom h'.symm).hom.toRingHom (TrivSqZeroExt.inr (R := k) (M := W.obj)
          (((forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)).map g).hom v)) := by
    intro A A' h h' ρ hρ
    subst h h' hρ
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    change ((squareZeroExtensionArtinian Λ k).map g).hom (TrivSqZeroExt.inr v) =
      TrivSqZeroExt.inr _
    exact TrivSqZeroExt.map_inr (f := g.hom.hom) v
  exact key x.1.left.base y.1.left.base (spaceFiber_base_eq B hΛ hSpec X hX toK x)
    (spaceFiber_base_eq B hΛ hSpec X hX toK y) φ.left.base hφ

/-- Sectionwise, `1 ⊗ v` in the extension of a point is the global section given by the function
`v` of the base, read in the middle term. -/
private theorem incl_baseRingTensorSection_eq_functionSectionE
    (x : (spaceDeformationProjection B hΛ hSpec X hX toK).Fiber
      ((squareZeroExtensionArtinian Λ k).obj V))
    (v : (forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)).obj V)
    (U : (SmallEtale B (Spec (.of Λ)) hΛ X)ᵒᵖ)
    (p : (sectionsFunctor _ U).obj
      (⊤_ Sheaf (SmallEtale.topology B (Spec (.of Λ)) hΛ X) (Type u))) :
    (spaceTangentExtension B hΛ hSpec X hX toK x).incl
        ((baseRingTensorSection B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)
          (spaceDefoFieldHom B hΛ hSpec X hX toK)
          ((forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)).obj V) v).val.app U
          (1 : (structureRingSheaf B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)).obj.obj U)) =
      (sectionsFunctor _ U).map (spaceDefoFunctionSectionE B hΛ hSpec X hX toK x.1
        (spaceFiber_maximalIdeal_sq B hΛ hSpec X hX toK x)
        (spaceTangentFunction B hΛ hSpec X hX toK x v)) p :=
  (spaceTangentExtension_incl_baseRingTensorSection B hΛ hSpec X hX toK x v U p).trans
    (sectionsFunctor_map_congr (spaceDefoFunctionSection_eq B hΛ hSpec X hX toK x.1
      (spaceFiber_maximalIdeal_sq B hΛ hSpec X hX toK x)
      (spaceTangentFunction B hΛ hSpec X hX toK x v)) U p)

include hφ in
/-- **The map of ideals of a morphism over `k[g]` is `𝒪_X ⊗ g`.** -/
theorem spaceTangentKernelMap_eq :
    spaceTangentKernelMap B hΛ hSpec X hX toK φ =
      (baseRingTensorModule B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)
        (spaceDefoFieldHom B hΛ hSpec X hX toK)).map
        ((forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)).map g) := by
  refine baseRingTensorModule_hom_ext B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)
    (spaceDefoFieldHom B hΛ hSpec X hX toK) fun v => ?_
  refine Eq.trans ?_ (baseRingTensorSection_map B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)
    (spaceDefoFieldHom B hΛ hSpec X hX toK)
    ((forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)).map g) v).symm
  refine Deformation.AlgebraExtension.hom_ext_of_incl
    (J := SmallEtale.topology B (Spec (.of Λ)) hΛ X)
    (spaceTangentExtension B hΛ hSpec X hX toK y) fun U p => ?_
  have h1 := SheafOfModules.comp_val_app_apply
    (baseRingTensorSection B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)
      (spaceDefoFieldHom B hΛ hSpec X hX toK)
      ((forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)).obj V) v)
    (spaceTangentKernelMap B hΛ hSpec X hX toK φ) U
    (1 : (structureRingSheaf B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)).obj.obj U)
  have h3 := incl_baseRingTensorSection_eq_functionSectionE B hΛ hSpec X hX toK x v U p
  have h5 := Γ_map_spaceTangentFunction B hΛ hSpec X hX toK g φ hφ v
  have h6 := incl_baseRingTensorSection_eq_functionSectionE B hΛ hSpec X hX toK y
    (((forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)).map g).hom v) U p
  have hz := spaceDefoFunctionSectionE_comp_forget_map_spaceDefoMiddleMap B hΛ hSpec X hX toK φ
    (spaceFiber_maximalIdeal_sq B hΛ hSpec X hX toK x)
    (spaceFiber_maximalIdeal_sq B hΛ hSpec X hX toK y)
    (spaceTangentFunction B hΛ hSpec X hX toK x v)
  refine (congrArg (spaceTangentExtension B hΛ hSpec X hX toK y).incl h1).trans ?_
  refine (Deformation.AlgebraExtension.incl_inducedKernelMap_val_app_eq.{u, u + 1, u}
    (J := SmallEtale.topology B (Spec (.of Λ)) hΛ X)
    (spaceTangentExtension B hΛ hSpec X hX toK x) (spaceTangentExtension B hΛ hSpec X hX toK y)
    (spaceTangentMiddleMap B hΛ hSpec X hX toK φ)
    (spaceTangentMiddleMap_comp_reduction B hΛ hSpec X hX toK φ) _ _ _ p h3 hz).trans ?_
  exact (congrArg (fun t => (sectionsFunctor _ U).map
    (spaceDefoFunctionSectionE B hΛ hSpec X hX toK y.1
      (spaceFiber_maximalIdeal_sq B hΛ hSpec X hX toK y) t) p) h5).trans h6.symm

include hφ in
/-- **Naturality of the class of a deformation over `k[V]`**: for a morphism over `k[g]`, the
class of the target in `Ext¹(NL_{X/k}, 𝒪_X ⊗_k W)` is the class of the source pushed along
`𝒪_X ⊗ g`. -/
theorem spaceTangentFiberClass_map :
    spaceTangentFiberClass B hΛ hSpec X hX toK y =
      (spaceTangentExtFunctor B hΛ hSpec X hX toK).map g
        (spaceTangentFiberClass B hΛ hSpec X hX toK x) := by
  have key : ∀ ψ : (baseRingTensorModule B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)
        (spaceDefoFieldHom B hΛ hSpec X hX toK)).obj
          ((forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)).obj V) ⟶
      (baseRingTensorModule B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)
        (spaceDefoFieldHom B hΛ hSpec X hX toK)).obj
          ((forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)).obj W),
      ψ = (baseRingTensorModule B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)
        (spaceDefoFieldHom B hΛ hSpec X hX toK)).map
          ((forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)).map g) →
      AlgebraExtension.extOneMap ((AlgebraExtension.moduleRes
          (smallEtaleModelTopology B (Spec (.of Λ)) hΛ X)
          (modelEquiv B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)).inverse
          (structureSheaf B (Spec (.of Λ)) hΛ X hX)).map ψ)
        (spaceTangentFiberClass B hΛ hSpec X hX toK x) =
      (spaceTangentExtFunctor B hΛ hSpec X hX toK).map g
        (spaceTangentFiberClass B hΛ hSpec X hX toK x) := by
    intro ψ hψ
    subst hψ
    rfl
  exact (modelExtClass_mapAlong B (Spec (.of Λ)) hΛ
    (spaceTangentMapAlong B hΛ hSpec X hX toK g φ hφ)).trans
    (key _ (spaceTangentKernelMap_eq B hΛ hSpec X hX toK g φ hφ))

end Deformation.Examples

end
