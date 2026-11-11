module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatDeformationDualClassMap
public import StacksFrontier.CategoryTheory.Preadditive.FGModuleCatHomFunctor
public import StacksFrontier.Deformation.Smooth.IsomorphismClasses
public import StacksFrontier.Deformation.TangentSpace.FiniteDimensional

/-!
# The class map on isomorphism classes of deformations in `Spaces'_{fp, flat, proper}`

Let `x₀ = (X₀ ⟶ Spec k)` be an object of `𝒳 = Spaces'_{fp, flat, proper}` over the big fppf site
of an arbitrary scheme `S`, with `Spec k ⟶ S` presented through `Spec k ⟶ Spec Λ ⟶ S`, and let
`𝓕 = 𝓕_{𝒳,k,x₀}` be its predeformation category over `𝒞_Λ` (Stacks 07T2). A deformation of `x₀`
over `k[V]` has a class in `Ext¹(NL_{X₀/k}, 𝒪_{X₀} ⊗_k V)`
(`AlgebraicGeometry.Space.deformationTangentClass`), the class of the extension of
`f₀⁻¹𝒪_{Spec k}`-algebras of `𝒪_{X₀}` given by its structure sheaf (Stacks 0D17, 0GQ5). This file
shows that the class only depends on the isomorphism class of the deformation, so that it
descends to the value at `V` of the tangent-space set functor `V ↦ 𝓕(k[V])/≅`
(`AlgebraicGeometry.ProperFlatSpaceDeformation.tangentExtClassAt`), naturally in `V` against the
additive `k`-linear functor `V ↦ Ext¹(NL_{X₀/k}, 𝒪_{X₀} ⊗_k V)`
(`AlgebraicGeometry.ProperFlatSpaceDeformation.tangentExtFunctor`). This is the shape consumed by
`Deformation.finiteDimensional_artinianTangentSpace_of_natural_injection` in the proof of
Stacks 0D1K over a general base.

## Main definitions

* `AlgebraicGeometry.ProperFlatSpaceDeformation.predeformationBased`: `𝓕` as a based category.
* `AlgebraicGeometry.ProperFlatSpaceDeformation.tangentExtFunctor`:
  `V ↦ Ext¹(NL_{X₀/k}, 𝒪_{X₀} ⊗_k V)`.
* `AlgebraicGeometry.ProperFlatSpaceDeformation.tangentExtClassAt`: the class map on isomorphism
  classes of deformations over `k[V]`.

## Main results

* `AlgebraicGeometry.ProperFlatSpaceDeformation.tangentExtClassAt_naturality`: the class map is
  natural in `V`.

## References

* [Stacks Project, Tag 0D1K](https://stacks.math.columbia.edu/tag/0D1K)
* [Stacks Project, Tag 0D17](https://stacks.math.columbia.edu/tag/0D17)
* [Stacks Project, Tag 0GQ5](https://stacks.math.columbia.edu/tag/0GQ5)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
attribute [local instance] SheafOfModules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory Deformation Deformation.Artin AlgebraicGeometry.Space

universe u

namespace AlgebraicGeometry.ProperFlatSpaceDeformation

attribute [local instance] PredeformationConstruction.category

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] (iΛ : Spec (.of Λ) ⟶ S)
  (x₀ : CartesianProperFlatSpaces B S hS)
  (hx₀ : (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion).obj x₀ =
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))

/-- The predeformation category `𝓕_{𝒳,k,x₀}` of `𝒳 = Spaces'_{fp, flat, proper}` over a general
base, as a based category over `𝒞_Λ`. -/
abbrev predeformationBased : BasedCategory (ArtinianLocalAlgCat.{u, u, u} Λ k) :=
  BasedCategory.ofFunctor
    (predeformationCategory iΛ (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion) x₀
      hx₀).projection

/-! ### The receptacle `V ↦ Ext¹(NL_{X₀/k}, 𝒪_{X₀} ⊗_k V)` -/

/-- **`V ↦ (𝒪_{X₀} ⊗_k V)[1]`** on finite-dimensional `k`-vector spaces, in the derived category
of modules on the model of the small étale site of `X₀`. -/
abbrev tangentCoefficientFunctor :=
  forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k) ⋙ deformationClassFunctor B S hS Λ x₀ hx₀

/-- **The receptacle `V ↦ Ext¹(NL_{X₀/k}, 𝒪_{X₀} ⊗_k V)`**, an additive `k`-linear functor of the
finite-dimensional `k`-vector space `V`: `Ext¹` is computed on the model of the small étale site of
`X₀`, and `k` acts through the coefficients. -/
abbrev tangentExtFunctor : FGModuleCat.{u} k ⥤ ModuleCat.{u} k :=
  (tangentCoefficientFunctor B S hS iΛ x₀ hx₀).homFunctorOfAdditive
    (DerivedCategory.Q.obj (modelNaiveCotangentComplex B S hS (baseStructureMap B S hS (y₀ := x₀))))

/-! ### The class map on isomorphism classes -/

variable {B S hS iΛ x₀ hx₀} in
/-- The class of a point of the fibre of `𝓕` over `k[V]`, in the receptacle at `V`. -/
def tangentFiberClass {V : FGModuleCat.{u} k}
    (x : (predeformationBased B S hS iΛ x₀ hx₀).p.Fiber
      ((squareZeroExtensionArtinian Λ k).obj V)) :
    (tangentExtFunctor B S hS iΛ x₀ hx₀).obj V :=
  deformationTangentClass B S hS V x.1 x.2

/-- A morphism of points of the fibres of `𝓕` lying over `k[g]` lies over `k[g]` read on
the algebras of the two deformations. -/
theorem fiber_ringHom_eq {V W : FGModuleCat.{u} k}
    (x : (predeformationBased B S hS iΛ x₀ hx₀).p.Fiber ((squareZeroExtensionArtinian Λ k).obj V))
    (y : (predeformationBased B S hS iΛ x₀ hx₀).p.Fiber ((squareZeroExtensionArtinian Λ k).obj W))
    (g : V ⟶ W) (φ : x.1 ⟶ y.1)
    [(predeformationBased B S hS iΛ x₀ hx₀).p.IsHomLift ((squareZeroExtensionArtinian Λ k).map g)
      φ] :
    (φ : DeformationMorphism iΛ (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion) x₀
      hx₀ x.1 y.1).ringHom =
      eqToHom x.2 ≫ (artinianSquareZeroExtensionFunctor Λ k).map g ≫ eqToHom y.2.symm :=
  IsHomLift.fac' (predeformationBased B S hS iΛ x₀ hx₀).p
    ((squareZeroExtensionArtinian Λ k).map g) φ

/-- **Naturality of the class of a point of a fibre**: for a morphism over `k[g]`, the class of
the target is the class of the source pushed along `𝒪_{X₀} ⊗ g`. -/
theorem tangentFiberClass_map {V W : FGModuleCat.{u} k}
    (x : (predeformationBased B S hS iΛ x₀ hx₀).p.Fiber ((squareZeroExtensionArtinian Λ k).obj V))
    (y : (predeformationBased B S hS iΛ x₀ hx₀).p.Fiber ((squareZeroExtensionArtinian Λ k).obj W))
    (g : V ⟶ W) (φ : x.1 ⟶ y.1)
    [(predeformationBased B S hS iΛ x₀ hx₀).p.IsHomLift ((squareZeroExtensionArtinian Λ k).map g)
      φ] :
    tangentFiberClass y = (tangentExtFunctor B S hS iΛ x₀ hx₀).map g (tangentFiberClass x) :=
  deformationTangentClass_map B S hS φ V W x.2 y.2 g (fiber_ringHom_eq B S hS iΛ x₀ hx₀ x y g φ)

/-- The class of a point of a fibre over `k[V]` only depends on its isomorphism class. -/
theorem tangentFiberClass_congr (V : FGModuleCat.{u} k)
    (x x' : (predeformationBased B S hS iΛ x₀ hx₀).p.Fiber
      ((squareZeroExtensionArtinian Λ k).obj V))
    (h : IsIsomorphic x x') :
    tangentFiberClass x = tangentFiberClass x' := by
  obtain ⟨e⟩ := h
  have : (predeformationBased B S hS iΛ x₀ hx₀).p.IsHomLift
      ((squareZeroExtensionArtinian Λ k).map (𝟙 V)) e.hom.1 := by
    rw [CategoryTheory.Functor.map_id]; exact e.hom.2
  refine Eq.trans ?_ (tangentFiberClass_map B S hS iΛ x₀ hx₀ x x' (𝟙 V) e.hom.1).symm
  rw [CategoryTheory.Functor.map_id]
  rfl

variable (h𝓕 : IsCofiberedInGroupoids (predeformationBased B S hS iΛ x₀ hx₀).p)

/-- **The class map on isomorphism classes of deformations over `k[V]`.** -/
def tangentExtClassAt (V : FGModuleCat.{u} k)
    (z : (associatedTangentSpaceSetFunctor (predeformationBased B S hS iΛ x₀ hx₀) h𝓕).obj V) :
    (tangentExtFunctor B S hS iΛ x₀ hx₀).obj V :=
  Quotient.liftOn
    (cast (isomorphismClasses_obj (predeformationBased B S hS iΛ x₀ hx₀) h𝓕
      ((squareZeroExtensionArtinian Λ k).obj V)) z)
    tangentFiberClass
    (tangentFiberClass_congr B S hS iΛ x₀ hx₀ V)

/-- The class map on the class of a point of the fibre. -/
theorem tangentExtClassAt_classOf (V : FGModuleCat.{u} k)
    (x : (predeformationBased B S hS iΛ x₀ hx₀).p.Fiber
      ((squareZeroExtensionArtinian Λ k).obj V)) :
    tangentExtClassAt B S hS iΛ x₀ hx₀ h𝓕 V
      (classOf (predeformationBased B S hS iΛ x₀ hx₀) h𝓕 x) = tangentFiberClass x := by
  have h := classOf_eq (predeformationBased B S hS iΛ x₀ hx₀) h𝓕 x
  exact congrArg (fun q => Quotient.liftOn q tangentFiberClass
    (tangentFiberClass_congr B S hS iΛ x₀ hx₀ V)) h

/-- **The class map on isomorphism classes is natural in `V`**, against
`V ↦ Ext¹(NL_{X₀/k}, 𝒪_{X₀} ⊗_k V)`. -/
theorem tangentExtClassAt_naturality {V W : FGModuleCat.{u} k} (g : V ⟶ W)
    (z : (associatedTangentSpaceSetFunctor (predeformationBased B S hS iΛ x₀ hx₀) h𝓕).obj V) :
    tangentExtClassAt B S hS iΛ x₀ hx₀ h𝓕 W
        ((associatedTangentSpaceSetFunctor (predeformationBased B S hS iΛ x₀ hx₀) h𝓕).map g z) =
      (tangentExtFunctor B S hS iΛ x₀ hx₀).map g (tangentExtClassAt B S hS iΛ x₀ hx₀ h𝓕 V z) := by
  obtain ⟨x, rfl⟩ := classOf_surjective (predeformationBased B S hS iΛ x₀ hx₀) h𝓕
    ((squareZeroExtensionArtinian Λ k).obj V) z
  obtain ⟨y₀, φ, hφ⟩ := exists_pushforward h𝓕 ((squareZeroExtensionArtinian Λ k).map g) x.1 x.2
  let : (predeformationBased B S hS iΛ x₀ hx₀).p.IsHomLift
      ((squareZeroExtensionArtinian Λ k).map g) φ := hφ
  let y : (predeformationBased B S hS iΛ x₀ hx₀).p.Fiber
      ((squareZeroExtensionArtinian Λ k).obj W) :=
    ⟨y₀, IsHomLift.codomain_eq (predeformationBased B S hS iΛ x₀ hx₀).p
      ((squareZeroExtensionArtinian Λ k).map g) φ⟩
  have hmap : (associatedTangentSpaceSetFunctor (predeformationBased B S hS iΛ x₀ hx₀) h𝓕).map g
        (classOf (predeformationBased B S hS iΛ x₀ hx₀) h𝓕 x) =
      classOf (predeformationBased B S hS iΛ x₀ hx₀) h𝓕 y :=
    map_classOf (predeformationBased B S hS iΛ x₀ hx₀) h𝓕
      ((squareZeroExtensionArtinian Λ k).map g) x y φ
  refine (congrArg (tangentExtClassAt B S hS iΛ x₀ hx₀ h𝓕 W) hmap).trans ?_
  refine (tangentExtClassAt_classOf B S hS iΛ x₀ hx₀ h𝓕 W y).trans ?_
  refine (tangentFiberClass_map B S hS iΛ x₀ hx₀ x y g φ).trans ?_
  exact congrArg _ (tangentExtClassAt_classOf B S hS iΛ x₀ hx₀ h𝓕 V x).symm

end AlgebraicGeometry.ProperFlatSpaceDeformation

end
