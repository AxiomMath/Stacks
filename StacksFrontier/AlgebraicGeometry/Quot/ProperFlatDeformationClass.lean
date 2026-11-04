module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatDeformationTensorExtension
public import StacksFrontier.AlgebraicGeometry.Spaces.BaseRingTensorModuleInverseLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ModelExtensionClass
public import StacksFrontier.CategoryTheory.Preadditive.ModuleCatFunctorDualClasses

/-!
# The class of a deformation in `Ext¹(NL_{X₀/k}, 𝒪_{X₀} ⊗_k 𝔪_A)`

For a deformation `X' ⟶ Spec A` of `x₀ = (X₀ ⟶ Spec k)` over an algebra `A` of `𝒞_Λ` with
square-zero residue kernel `𝔪_A` and a retraction `r` of `Spec k ⟶ Spec A`, the structure sheaf
of `X'` read on `X₀` is an extension of `f₀⁻¹𝒪_{Spec k}`-algebras of `𝒪_{X₀}`
(`AlgebraicGeometry.Space.deformationTensorBaseExtension`) whose ideal is `𝒪_{X₀} ⊗_k 𝔪_A`
(`AlgebraicGeometry.Space.deformationTensorLinearIdealIso`). Read with that ideal it has a
class in `Ext¹(NL_{X₀/k}, 𝒪_{X₀} ⊗_k 𝔪_A)` (Stacks 0GQ5), the deformation class of the proof of
[Stacks Project, Tag 0D1K]; over `A = k[V]` the ideal is `𝒪_{X₀} ⊗_k V`.

## Main definitions

* `AlgebraicGeometry.Space.deformationKernelExtension`: the extension of a deformation, with ideal
  `𝒪_{X₀} ⊗_k 𝔪_A`.
* `AlgebraicGeometry.Space.deformationExtClass`: its class.
* `AlgebraicGeometry.Space.deformationClassFunctor`: `V ↦ (𝒪_{X₀} ⊗_k V)[1]`, additive.
* `AlgebraicGeometry.Space.deformationTangentExtension`,
  `AlgebraicGeometry.Space.deformationTangentClass`: over `k[V]`, the extension with ideal
  `𝒪_{X₀} ⊗_k V` (constants `k ⊆ k[V]` as the retraction) and its class.
* `AlgebraicGeometry.Space.deformationDualClass`: `λ ↦ (𝒪_{X₀} ⊗ λ)_* ξ`, `k`-linear on `V^*`.

## References

* [Stacks Project, Tag 0D1K](https://stacks.math.columbia.edu/tag/0D1K)
* [Stacks Project, Tag 0GQ5](https://stacks.math.columbia.edu/tag/0GQ5)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
attribute [local instance] SheafOfModules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory Deformation Deformation.AlgebraExtension Deformation.Artin

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] {iΛ : Spec (.of Λ) ⟶ S}
  {y₀ : CartesianProperFlatSpaces B S hS}
  {hy₀ : (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion).obj y₀ =
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
  {x : DeformationObject iΛ (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion) y₀ hy₀}
  (hsq : RingHom.ker (residueMap x.algebra) ^ 2 = ⊥)
  (r : (cartesianProperFlatProjection B S hS).obj x.point ⟶
    (cartesianProperFlatProjection B S hS).obj y₀)
  (hr : (cartesianProperFlatProjection B S hS).map x.arrow ≫ r = 𝟙 _)

/-- **The extension of a deformation, with ideal `𝒪_{X₀} ⊗_k 𝔪_A`.** The extension
`AlgebraicGeometry.Space.deformationTensorBaseExtension` of `f₀⁻¹𝒪_{Spec k}`-algebras of `𝒪_{X₀}`,
its ideal read as `𝒪_{X₀} ⊗_k 𝔪_A` through
`AlgebraicGeometry.Space.deformationTensorLinearIdealIso`. -/
def deformationKernelExtension :
    AlgebraExtension (J := SmallEtale.topology B S hS y₀.obj.obj.left.1)
      (inverseImageBaseMap B S hS (baseStructureMap B S hS (y₀ := y₀)))
      ((baseRingTensorModule B S hS y₀.obj.obj.left (baseFieldHom B S hS (hy₀ := hy₀))).obj
        (RingHom.squareZeroKer (residueMap x.algebra) (residueMap_surjective' x.algebra) hsq)) :=
  (deformationTensorBaseExtension B S hS hsq r hr).transportKernel
    (deformationTensorLinearIdealIso B S hS x hsq)

/-- **The class of a deformation** in `Ext¹(NL_{X₀/k}, 𝒪_{X₀} ⊗_k 𝔪_A)`: the class (Stacks 0GQ5)
of `AlgebraicGeometry.Space.deformationKernelExtension`, on the model of the small étale site of
`X₀`. -/
def deformationExtClass :=
  modelExtClass B S hS (deformationKernelExtension B S hS hsq r hr)

/-! ### The class over `k[V]` -/

section SquareZero

variable (Λ) (y₀) (hy₀)

/-- **The functor `V ↦ (𝒪_{X₀} ⊗_k V)[1]`** from `k`-modules to the derived category of
`𝒪_{X₀}`-modules on the model of the small étale site of `X₀`, `k` acting on `𝒪_{X₀}` through the
structure morphism of `x₀`. Morphisms `NL_{X₀/k} ⟶ (𝒪_{X₀} ⊗_k V)[1]` are
`Ext¹(NL_{X₀/k}, 𝒪_{X₀} ⊗_k V)`. -/
abbrev deformationClassFunctor :=
  baseRingTensorModule B S hS y₀.obj.obj.left (baseFieldHom B S hS (hy₀ := hy₀)) ⋙
    moduleRes (smallEtaleModelTopology B S hS y₀.obj.obj.left.1)
      (modelEquiv B S hS y₀.obj.obj.left).inverse
      (structureSheaf B S hS y₀.obj.obj.left.1 y₀.obj.obj.left.2) ⋙
    DerivedCategory.singleFunctor (SheafOfModules.{u}
      ((sheafCompose (smallEtaleModelTopology B S hS y₀.obj.obj.left.1)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj
        ((ringRes (smallEtaleModelTopology B S hS y₀.obj.obj.left.1)
          (modelEquiv B S hS y₀.obj.obj.left).inverse).obj
          (structureSheaf B S hS y₀.obj.obj.left.1 y₀.obj.obj.left.2)))) 0 ⋙
    shiftFunctor _ (1 : ℤ)

/-- The functor `V ↦ (𝒪_{X₀} ⊗_k V)[1]` is additive. -/
instance : (deformationClassFunctor B S hS Λ y₀ hy₀).Additive := by
  have := baseRingTensorModule_additive B S hS y₀.obj.obj.left (baseFieldHom B S hS (hy₀ := hy₀))
  have : (moduleRes (smallEtaleModelTopology B S hS y₀.obj.obj.left.1)
      (modelEquiv B S hS y₀.obj.obj.left).inverse
      (structureSheaf B S hS y₀.obj.obj.left.1 y₀.obj.obj.left.2)).Additive := ⟨rfl⟩
  exact ⟨fun {M N f g} => (congrArg (moduleRes (smallEtaleModelTopology B S hS y₀.obj.obj.left.1)
      (modelEquiv B S hS y₀.obj.obj.left).inverse
      (structureSheaf B S hS y₀.obj.obj.left.1 y₀.obj.obj.left.2) ⋙
    DerivedCategory.singleFunctor _ 0 ⋙ shiftFunctor _ (1 : ℤ)).map
      ((baseRingTensorModule B S hS y₀.obj.obj.left (baseFieldHom B S hS (hy₀ := hy₀))).map_add
        (f := f) (g := g))).trans (Functor.map_add _)⟩

end SquareZero

/-! ### The class of a deformation over `k[V]` -/

section Tangent

variable (V : FGModuleCat.{u} k)
  (x : DeformationObject iΛ (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion) y₀ hy₀)
  (hx : x.algebra = (artinianSquareZeroExtensionFunctor Λ k).obj V)

include hx in
/-- The residue kernel of an algebra equal to `k[V]` squares to zero. -/
theorem ker_residueMap_sq_of_eq : RingHom.ker (residueMap x.algebra) ^ 2 = ⊥ :=
  hx ▸ ker_residueMap_sq_artinianSquareZero Λ k V

/-- The inclusion of constants `k ⟶ A` for an algebra `A` equal to `k[V]`. -/
def tangentSection : k →+* x.algebra :=
  (eqToHom hx.symm).hom.toRingHom.comp (squareZeroSection Λ k V)

/-- The inclusion of constants `k ⟶ k[V]`, transported along an equality `A = k[V]`, is
compatible with the structure maps from `Λ`. -/
theorem eqToHom_squareZeroSection_comp_algebraMap {A : ArtinianLocalAlgCat.{u, u, u} Λ k}
    (h : A = (artinianSquareZeroExtensionFunctor Λ k).obj V) :
    ((eqToHom h.symm).hom.toRingHom.comp (squareZeroSection Λ k V)).comp (algebraMap Λ k) =
      algebraMap Λ A := by
  cases h
  exact squareZeroSection_comp_algebraMap V

/-- The inclusion of constants `k ⟶ k[V]`, transported along an equality `A = k[V]`, is a section
of the residue map `A ⟶ k`. -/
theorem residueMap_comp_eqToHom_squareZeroSection {A : ArtinianLocalAlgCat.{u, u, u} Λ k}
    (h : A = (artinianSquareZeroExtensionFunctor Λ k).obj V) :
    (residueMap A).comp ((eqToHom h.symm).hom.toRingHom.comp (squareZeroSection Λ k V)) =
      RingHom.id k := by
  cases h
  exact residueMap_comp_squareZeroSection V

/-- The inclusion of constants `k ⟶ A` is compatible with the structure maps from `Λ`. -/
theorem tangentSection_comp_algebraMap :
    (tangentSection B S hS V x hx).comp (algebraMap Λ k) = algebraMap Λ x.algebra :=
  eqToHom_squareZeroSection_comp_algebraMap V hx

/-- The inclusion of constants `k ⟶ A` is a section of the residue map `A ⟶ k`. -/
theorem residueMap_comp_tangentSection :
    (residueMap x.algebra).comp (tangentSection B S hS V x hx) = RingHom.id k :=
  residueMap_comp_eqToHom_squareZeroSection V hx

/-- The retraction `Spec A ⟶ Spec k` of the constants, for a deformation over `A = k[V]`. -/
abbrev tangentRetraction :
    (cartesianProperFlatProjection B S hS).obj x.point ⟶
      (cartesianProperFlatProjection B S hS).obj y₀ :=
  baseRetraction (cartesianProperFlatProjection B S hS) x (tangentSection B S hS V x hx)
    (tangentSection_comp_algebraMap B S hS V x hx)

/-- The retraction `Spec A ⟶ Spec k` of the constants is a retraction of the image of the
arrow `x₀ ⟶ x` of the deformation. -/
theorem map_arrow_comp_tangentRetraction :
    (cartesianProperFlatProjection B S hS).map x.arrow ≫ tangentRetraction B S hS V x hx = 𝟙 _ :=
  map_arrow_comp_baseRetraction (cartesianProperFlatProjection B S hS) x _ _
    (residueMap_comp_tangentSection B S hS V x hx)

/-- **The extension of a deformation over `k[V]`, with ideal `𝒪_{X₀} ⊗_k V`.** -/
def deformationTangentExtension :
    AlgebraExtension (J := SmallEtale.topology B S hS y₀.obj.obj.left.1)
      (inverseImageBaseMap B S hS (baseStructureMap B S hS (y₀ := y₀)))
      ((baseRingTensorModule B S hS y₀.obj.obj.left (baseFieldHom B S hS (hy₀ := hy₀))).obj
        ((forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)).obj V)) :=
  (deformationKernelExtension B S hS (ker_residueMap_sq_of_eq B S hS V x hx)
      (tangentRetraction B S hS V x hx)
      (map_arrow_comp_tangentRetraction B S hS V x hx)).transportKernel
    ((baseRingTensorModule B S hS y₀.obj.obj.left (baseFieldHom B S hS (hy₀ := hy₀))).mapIso
      (squareZeroKerOfEqIso Λ x.algebra V hx (ker_residueMap_sq_of_eq B S hS V x hx)))

/-- **The class of a deformation over `k[V]`** in `Ext¹(NL_{X₀/k}, 𝒪_{X₀} ⊗_k V)`. -/
def deformationTangentClass :=
  modelExtClass B S hS (deformationTangentExtension B S hS V x hx)

attribute [local instance] Functor.evalModule

/-- **The linear forms on `V` acting on the class of a deformation over `k[V]`**:
`λ ↦ (𝒪_{X₀} ⊗ λ)_*(ξ_x) ∈ Ext¹(NL_{X₀/k}, 𝒪_{X₀} ⊗_k k)`, `k`-linear in `λ`. -/
def deformationDualClass :=
  (deformationClassFunctor B S hS Λ y₀ hy₀).dualClassMap
    (V := (forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)).obj V)
    (deformationTangentClass B S hS V x hx)

end Tangent

end AlgebraicGeometry.Space

end
