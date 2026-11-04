module

public import StacksFrontier.Algebra.Module.OppositeOfCommSemiring
public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatDeformationClass
public import StacksFrontier.CategoryTheory.Preadditive.FGModuleCatHomFunctor
public import StacksFrontier.Deformation.Examples.Geometric.SpacesTangentSpaceSections

/-!
# The class of a deformation of an algebraic space over `k[V]`

In the situation of Stacks 0E3Z, let `X` be an algebraic space over the field `k` and let `x` be a
point of its deformation category over `k[V] = k ⊕ V`, `V` a finite-dimensional `k`-vector space.
The constants `k ⊆ k[V]` give a retraction `Spec k[V] ⟶ Spec k`, and the structure sheaf of the
total space read on `X` is an extension of `f⁻¹𝒪_{Spec k}`-algebras

`0 ⟶ 𝒪_X ⊗_k V ⟶ 𝒪_{X'}|_X ⟶ 𝒪_X ⟶ 0`

(`Deformation.Examples.spaceTangentExtension`). Its class (Stacks 0GQ5, taken on the `Type u`
model of the small étale site of `X`) lies in `Ext¹(NL_{X/k}, 𝒪_X ⊗_k V)`, the value at `V` of the
additive `k`-linear functor `Deformation.Examples.spaceTangentExtFunctor`.

## Main definitions

* `Deformation.Examples.spaceConstants`: the constants `k ⟶ k[V]` in `𝒞_Λ`.
* `Deformation.Examples.spaceTangentExtension`: the extension of a deformation over `k[V]`.
* `Deformation.Examples.spaceTangentCoefficientFunctor`: `V ↦ (𝒪_X ⊗_k V)[1]` on the model.
* `Deformation.Examples.spaceTangentExtFunctor`: `V ↦ Ext¹(NL_{X/k}, 𝒪_X ⊗_k V)`.
* `Deformation.Examples.spaceTangentFiberClass`: the class of a deformation over `k[V]`.

## References

* [Stacks Project, Tag 0E41](https://stacks.math.columbia.edu/tag/0E41)
* [Stacks Project, Tag 0GQ5](https://stacks.math.columbia.edu/tag/0GQ5)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
attribute [local instance] SheafOfModules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Space Deformation.Artin Deformation.AlgebraExtension

universe u

namespace Deformation.Examples

variable {Λ : Type u} {k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable (B : BigFppfSite.{u}) (hΛ : B.Contains (Spec (.of Λ)))
variable (hSpec : ∀ A : ArtinianLocalAlgCat.{u, u, u} Λ k, B.Contains (Spec (.of A)))
variable (X : (BigFppfOver B (Spec (.of Λ)) hΛ)ᵒᵖ ⥤ Type u)
  (hX : IsAlgebraicSpace B (Spec (.of Λ)) hΛ X)
  (toK : X ⟶ yoneda.obj (spaceBaseOver B hΛ hSpec (residueFieldBase Λ k)))

/-- The right action of `k` on a `k`-module, the one through which `k[V]` is formed. -/
local instance (M : FGModuleCat.{u} k) : Module kᵐᵒᵖ M :=
  Module.oppositeOfCommSemiring k M

/-- The left and right actions of `k` on a `k`-module agree. -/
local instance (M : FGModuleCat.{u} k) : IsCentralScalar k M :=
  Module.isCentralScalar_oppositeOfCommSemiring k M

variable (Λ) in
/-- **The constants `k ⟶ k[V]`**, as a morphism of `𝒞_Λ`. -/
def spaceConstants (V : FGModuleCat.{u} k) :
    residueFieldBase Λ k ⟶ (squareZeroExtensionArtinian Λ k).obj V where
  hom := { toRingHom := squareZeroSection Λ k V, commutes' := fun _ => rfl }
  isLocal := ⟨fun _ ha => TrivSqZeroExt.isUnit_iff_isUnit_fst.mp ha⟩
  residue_comm a := (squareZeroExtensionArtinian_residue Λ k V _).trans
    (residueFieldBase_residueEquiv_residue Λ k a).symm

/-- The constants are preserved by `k[g]`. -/
theorem spaceConstants_comp_map {V W : FGModuleCat.{u} k} (g : V ⟶ W) :
    spaceConstants Λ V ≫ (squareZeroExtensionArtinian Λ k).map g = spaceConstants Λ W := by
  ext a
  exact TrivSqZeroExt.map_inl (f := g.hom.hom) a

/-- The maximal ideal of `k[V]` squares to zero. -/
theorem maximalIdeal_sq_squareZeroExtensionArtinian (V : FGModuleCat.{u} k) :
    IsLocalRing.maximalIdeal ((squareZeroExtensionArtinian Λ k).obj V) ^ 2 = ⊥ := by
  rw [← ker_residueMap_eq_maximalIdeal]
  exact ker_residueMap_sq_artinianSquareZero Λ k V

section Fiber

variable {V : FGModuleCat.{u} k}
  (x : (spaceDeformationProjection B hΛ hSpec X hX toK).Fiber
    ((squareZeroExtensionArtinian Λ k).obj V))

/-- The coefficient algebra of a point of the fibre over `k[V]` is `k[V]`. -/
theorem spaceFiber_base_eq : x.1.left.base = (squareZeroExtensionArtinian Λ k).obj V := x.2

/-- The maximal ideal of the coefficient algebra of a point over `k[V]` squares to zero. -/
theorem spaceFiber_maximalIdeal_sq : IsLocalRing.maximalIdeal x.1.left.base ^ 2 = ⊥ := by
  rw [spaceFiber_base_eq B hΛ hSpec X hX toK x]
  exact maximalIdeal_sq_squareZeroExtensionArtinian V

/-- The constants of the coefficient algebra of a point over `k[V]`. -/
abbrev spaceFiberConstants : residueFieldBase Λ k ⟶ x.1.left.base :=
  spaceConstants Λ V ≫ eqToHom (spaceFiber_base_eq B hΛ hSpec X hX toK x).symm

/-- **The retraction `Spec k[V] ⟶ Spec k` of the constants.** -/
abbrev spaceTangentRetraction :
    spaceBaseOver B hΛ hSpec x.1.left.base ⟶ spaceBaseOver B hΛ hSpec (residueFieldBase Λ k) :=
  spaceBaseOverMap B hΛ hSpec (spaceFiberConstants B hΛ hSpec X hX toK x)

/-- The retraction of the constants is a retraction of `Spec k ⟶ Spec k[V]`. -/
theorem spaceDefoBaseImmersion_comp_spaceTangentRetraction :
    spaceDefoBaseImmersion B hΛ hSpec X hX toK x.1 ≫ spaceTangentRetraction B hΛ hSpec X hX toK x =
      𝟙 _ := by
  have h : spaceFiberConstants B hΛ hSpec X hX toK x ≫ x.1.hom.base = 𝟙 (residueFieldBase Λ k) :=
    isTerminal_residueFieldBase.hom_ext _ _
  refine (spaceBaseOverMap_comp B hΛ hSpec (spaceFiberConstants B hΛ hSpec X hX toK x)
    x.1.hom.base).symm.trans ?_
  exact (congrArg (spaceBaseOverMap B hΛ hSpec) h).trans (spaceBaseOverMap_id B hΛ hSpec _)

/-- The kernel `𝔪_{k[V]}` of a point over `k[V]` is `V`. -/
def spaceTangentKernelIso :
    RingHom.squareZeroKer (residueMap x.1.left.base) (residueMap_surjective' x.1.left.base)
        (ker_residueMap_sq_of_maximalIdeal_sq (spaceFiber_maximalIdeal_sq B hΛ hSpec X hX toK x)) ≅
      (forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)).obj V :=
  squareZeroKerOfEqIso Λ x.1.left.base V (spaceFiber_base_eq B hΛ hSpec X hX toK x) _

/-- **The extension of a deformation over `k[V]`, with ideal `𝒪_X ⊗_k V`**: the extension of
`Deformation.Examples.spaceDefoKernelExtension` for the retraction of the constants, its ideal
`𝒪_X ⊗_k 𝔪_{k[V]}` read as `𝒪_X ⊗_k V`. -/
def spaceTangentExtension :
    AlgebraExtension (J := SmallEtale.topology B (Spec (.of Λ)) hΛ X)
      (inverseImageBaseMap B (Spec (.of Λ)) hΛ (spaceStructureMap B hΛ hSpec X hX toK))
      ((baseRingTensorModule B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)
        (spaceDefoFieldHom B hΛ hSpec X hX toK)).obj
        ((forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)).obj V)) :=
  (spaceDefoKernelExtension B hΛ hSpec X hX toK (spaceFiber_maximalIdeal_sq B hΛ hSpec X hX toK x)
      (spaceTangentRetraction B hΛ hSpec X hX toK x)
      (spaceDefoBaseImmersion_comp_spaceTangentRetraction B hΛ hSpec X hX toK x)).transportKernel
    ((baseRingTensorModule B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)
      (spaceDefoFieldHom B hΛ hSpec X hX toK)).mapIso (spaceTangentKernelIso B hΛ hSpec X hX toK x))

end Fiber

/-! ### The receptacle `V ↦ Ext¹(NL_{X/k}, 𝒪_X ⊗_k V)` -/

/-- The functor `M ↦ (𝒪_X ⊗_k M)[1]` from `k`-modules to the derived category of modules on the
model of the small étale site of `X`. -/
abbrev spaceDefoClassFunctor :=
  baseRingTensorModule B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)
      (spaceDefoFieldHom B hΛ hSpec X hX toK) ⋙
    moduleRes (smallEtaleModelTopology B (Spec (.of Λ)) hΛ X)
      (modelEquiv B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)).inverse
      (structureSheaf B (Spec (.of Λ)) hΛ X (spaceOf B hΛ X hX).2) ⋙
    DerivedCategory.singleFunctor (SheafOfModules.{u}
      ((sheafCompose (smallEtaleModelTopology B (Spec (.of Λ)) hΛ X)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj
        ((ringRes (smallEtaleModelTopology B (Spec (.of Λ)) hΛ X)
          (modelEquiv B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)).inverse).obj
          (structureSheaf B (Spec (.of Λ)) hΛ X (spaceOf B hΛ X hX).2)))) 0 ⋙
    shiftFunctor _ (1 : ℤ)

/-- The functor `M ↦ (𝒪_X ⊗_k M)[1]` is additive. -/
instance : (spaceDefoClassFunctor B hΛ hSpec X hX toK).Additive := by
  have := baseRingTensorModule_additive B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)
    (spaceDefoFieldHom B hΛ hSpec X hX toK)
  have : (moduleRes (smallEtaleModelTopology B (Spec (.of Λ)) hΛ X)
      (modelEquiv B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)).inverse
      (structureSheaf B (Spec (.of Λ)) hΛ X (spaceOf B hΛ X hX).2)).Additive := ⟨rfl⟩
  have h4 : (moduleRes (smallEtaleModelTopology B (Spec (.of Λ)) hΛ X)
      (modelEquiv B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)).inverse
      (structureSheaf B (Spec (.of Λ)) hΛ X (spaceOf B hΛ X hX).2) ⋙
    DerivedCategory.singleFunctor (SheafOfModules.{u}
      ((sheafCompose (smallEtaleModelTopology B (Spec (.of Λ)) hΛ X)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj
        ((ringRes (smallEtaleModelTopology B (Spec (.of Λ)) hΛ X)
          (modelEquiv B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)).inverse).obj
          (structureSheaf B (Spec (.of Λ)) hΛ X (spaceOf B hΛ X hX).2)))) 0 ⋙
    shiftFunctor _ (1 : ℤ)).Additive := inferInstance
  exact ⟨fun {M N f g} => (congrArg (moduleRes (smallEtaleModelTopology B (Spec (.of Λ)) hΛ X)
      (modelEquiv B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)).inverse
      (structureSheaf B (Spec (.of Λ)) hΛ X (spaceOf B hΛ X hX).2) ⋙
    DerivedCategory.singleFunctor _ 0 ⋙ shiftFunctor _ (1 : ℤ)).map
      ((baseRingTensorModule B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)
          (spaceDefoFieldHom B hΛ hSpec X hX toK)).map_add
        (f := f) (g := g))).trans (Functor.map_add _)⟩





/-- **`V ↦ (𝒪_X ⊗_k V)[1]`** on finite-dimensional `k`-vector spaces, in the derived category of
modules on the model of the small étale site of `X`. -/
abbrev spaceTangentCoefficientFunctor :=
  forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k) ⋙ spaceDefoClassFunctor B hΛ hSpec X hX toK

/-- The functor `V ↦ (𝒪_X ⊗_k V)[1]` is additive. -/
instance : (spaceTangentCoefficientFunctor B hΛ hSpec X hX toK).Additive :=
  inferInstance

/-- **The receptacle `V ↦ Ext¹(NL_{X/k}, 𝒪_X ⊗_k V)`**, an additive `k`-linear functor of the
finite-dimensional `k`-vector space `V`: `Ext¹` is computed on the model of the small étale site of
`X`, and `k` acts through the coefficients. -/
abbrev spaceTangentExtFunctor : FGModuleCat.{u} k ⥤ ModuleCat.{u} k :=
  (spaceTangentCoefficientFunctor B hΛ hSpec X hX toK).homFunctorOfAdditive
    (DerivedCategory.Q.obj (modelNaiveCotangentComplex B (Spec (.of Λ)) hΛ
      (spaceStructureMap B hΛ hSpec X hX toK)))

/-- **The class of a deformation over `k[V]`** in `Ext¹(NL_{X/k}, 𝒪_X ⊗_k V)`: the class
(Stacks 0GQ5) of `Deformation.Examples.spaceTangentExtension`. -/
def spaceTangentFiberClass {V : FGModuleCat.{u} k}
    (x : (spaceDeformationProjection B hΛ hSpec X hX toK).Fiber
      ((squareZeroExtensionArtinian Λ k).obj V)) :
    (spaceTangentExtFunctor B hΛ hSpec X hX toK).obj V :=
  modelExtClass B (Spec (.of Λ)) hΛ (spaceTangentExtension B hΛ hSpec X hX toK x)

end Deformation.Examples

end
