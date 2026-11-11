module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatChartProblem
public import StacksFrontier.Deformation.Artin.Predeformation
public import StacksFrontier.AlgebraicGeometry.Topologies.FppfPostInclusion

/-!
# The obstruction groups of the deformations of a point of `Spaces'_{fp, flat, proper}`

Let `x₀ = (X₀ ⟶ Spec k)` be an object of `𝒳 = Spaces'_{fp, flat, proper}` over a field, presented
over an affine chart `Spec Λ ⟶ S`. A deformation of `x₀` over an object `A` of `𝒞_Λ`
(`Deformation.Artin.DeformationObject`) is an object `x = (X ⟶ Spec A)` of `𝒳` over `Spec A`
with an arrow `x₀ ⟶ x` over the closed point. Its obstruction groups are the groups
`T²(I) = Ext²_{𝒪_X}(L_{X/A}, 𝒪_X ⊗_A I)` of [Stacks, Remark 0D1P], in which the class of
[Stacks, Tag 08V5] of a square-zero thickening of `Spec A` with ideal `I` lives
(`AlgebraicGeometry.Space.ProperFlatLift.chartObstruction`).

This file records a deformation as an object of `𝒳` over the chart `Spec A`, and the condition
that the obstruction groups of all deformations vanish at all `A`-modules killed by `𝔪_A`, the
modules that occur as kernels of small extensions.

## Main definitions

* `Deformation.Artin.DeformationObject.contains`,
  `Deformation.Artin.DeformationObject.obj_eq`: a deformation over
  `A` lies over `Spec A` in the site.
* `AlgebraicGeometry.ProperFlatSpaceDeformation.DeformationObstructionGroupsVanish`.

## References

* [Stacks Project, Remark 0D1P](https://stacks.math.columbia.edu/tag/0D1P)
* [Stacks Project, Tag 08V5](https://stacks.math.columbia.edu/tag/08V5)
-/

@[expose] public noncomputable section

open CategoryTheory Deformation Deformation.Artin

namespace AlgebraicGeometry.ProperFlatSpaceDeformation

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] {iΛ : Spec (.of Λ) ⟶ S}
  {x₀ : CartesianProperFlatSpaces B S hS}
  {hx₀ : (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion).obj x₀ =
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}

/-- The structure morphism `Spec A ⟶ S` of a deformation over `A`, through the chart. -/
abbrev _root_.Deformation.Artin.DeformationObject.toS
    (a : DeformationObject iΛ (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion) x₀
      hx₀) : Spec (.of a.algebra) ⟶ S :=
  Spec.map (CommRingCat.ofHom (algebraMap Λ a.algebra)) ≫ iΛ

/-- The spectrum of the base of a deformation belongs to the site. -/
theorem _root_.Deformation.Artin.DeformationObject.contains
    (a : DeformationObject iΛ (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion) x₀
      hx₀) : B.Contains (Spec (.of a.algebra)) := by
  have h := congrArg Over.left a.base
  change ((cartesianProperFlatProjection B S hS).obj a.point).left.obj = Spec (.of a.algebra) at h
  exact h ▸ ((cartesianProperFlatProjection B S hS).obj a.point).left.property

/-- A deformation over `A` lies over `Spec A`, as an object of the site. -/
theorem _root_.Deformation.Artin.DeformationObject.obj_eq
    (a : DeformationObject iΛ (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion) x₀
      hx₀) :
    (cartesianProperFlatProjection B S hS).obj a.point =
      algebraOver a.algebra B S hS a.toS a.contains :=
  BigFppfOver.obj_injective_post_inclusion B S hS a.base

attribute [local instance] HasDerivedCategory.standard in
/-- **The obstruction groups of all deformations of `x₀` vanish**: for every deformation
`x = (X ⟶ Spec A)` of `x₀` over an object `A` of `𝒞_Λ` and every `A`-module `I` killed by the
maximal ideal of `A`, the group `T²(I) = Ext²_{𝒪_X}(L_{X/A}, 𝒪_X ⊗_A I)` of
[Stacks, Remark 0D1P] is zero. -/
def DeformationObstructionGroupsVanish : Prop :=
  ∀ (a : DeformationObject iΛ (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion) x₀
      hx₀) (I : ModuleCat.{u} a.algebra),
    (∀ r ∈ IsLocalRing.maximalIdeal a.algebra, ∀ i : I, r • i = 0) →
      Subsingleton ((Space.cotangentExtTwo
        (Space.ProperFlatLift.chartStructureMap a.point a.obj_eq)
        (Space.ProperFlatLift.chartBaseRingHom a.point a.obj_eq)).obj I)

end AlgebraicGeometry.ProperFlatSpaceDeformation

end
