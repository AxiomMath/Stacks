module

public import StacksFrontier.Deformation.Artin.ChangeOfField.SiteRestriction
public import StacksFrontier.Deformation.ArtinCriteria.Predeformation
public import StacksFrontier.Deformation.CofiberedPresentation.SmoothPresentation

/-!
# Stacks 07WX as an equivalence over `𝒞_{Λ,l}`

For a category `𝒳` fibred in groupoids over the big fppf site of `S` satisfying (RS), a finite
tower `Λ → k → l` and a Cartesian arrow `η : x_l ⟶ x₀` over `Spec l ⟶ Spec k`, the canonical
functor `(𝓕_{𝒳,k,x₀})_{l/k} ⟶ 𝓕_{𝒳,l,x_l}` of Stacks 07WX is an equivalence of categories
(`Deformation.Artin.Site.changeOfFieldFunctor_isEquivalence`) commuting with the projections to
`𝒞_{Λ,l}`. This file records it as an equivalence over `𝒞_{Λ,l}`, the form in which presentations
are compared.

## Main results

* `Deformation.Artin.Site.changeOfFieldEquivalenceOver`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u v w

namespace Deformation.Artin.Site

variable (T : Deformation.ChangeOfFieldsSituation.{u, u, u})
variable {S : Scheme.{u}}
variable (iΛ : Spec (.of T.Λ) ⟶ S)
variable (B : AlgebraicGeometry.BigFppfSite.{u}) (hS : B.Contains S)
variable {X : Type v} [Category.{w} X]
variable (p : X ⥤ AlgebraicGeometry.BigFppfOver B S hS)
variable (x₀ xₗ : X)
variable (hx₀ : (p ⋙ Over.post B.inclusion).obj x₀ =
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.k)) ≫ iΛ))
variable (hxₗ : (p ⋙ Over.post B.inclusion).obj xₗ =
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.l)) ≫ iΛ))
variable (η : xₗ ⟶ x₀)

/-- **Stacks 07WX, as an equivalence over `𝒞_{Λ,l}`.** Under (RS), restriction of deformations
along a Cartesian arrow `η : x_l ⟶ x₀` over `Spec l ⟶ Spec k` is an equivalence over `𝒞_{Λ,l}`
from the change of residue field of `𝓕_{𝒳,k,x₀}` to `𝓕_{𝒳,l,x_l}`. -/
noncomputable def changeOfFieldEquivalenceOver [IsLocallyNoetherian S]
    (hp : p.IsFiberedInGroupoids)
    (hη : p.IsCartesian (p.map η) η)
    (hηbase : eqToHom (congrArg Over.left hxₗ).symm ≫
      ((p ⋙ Over.post B.inclusion).map η).left ≫
      eqToHom (congrArg Over.left hx₀) =
        Spec.map (CommRingCat.ofHom (algebraMap T.k T.l)))
    (hfinite : LocallyOfFiniteType
        (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.k)) ≫ iΛ) ∧
      QuasiCompact
        (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.k)) ≫ iΛ))
    (hRS : Deformation.Artin.SatisfiesRS B S hS p hp) :
    letI :=
      (Deformation.Artin.predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).category
    letI :=
      (Deformation.Artin.predeformationCategory iΛ (p ⋙ Over.post B.inclusion) xₗ hxₗ).category
    StacksRepresentableCFG.EquivalenceOver
      (Deformation.changeOfFieldsProjection T
        (Deformation.Artin.predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection)
      (Deformation.Artin.predeformationCategory iΛ (p ⋙ Over.post B.inclusion) xₗ
        hxₗ).projection := by
  letI := (Deformation.Artin.predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).category
  letI := (Deformation.Artin.predeformationCategory iΛ (p ⋙ Over.post B.inclusion) xₗ hxₗ).category
  let F := changeOfFieldFunctor T iΛ B hS p x₀ xₗ hx₀ hxₗ η hp hη hηbase
  haveI : F.toFunctor.IsEquivalence :=
    changeOfFieldFunctor_isEquivalence T iΛ B hS p x₀ xₗ hx₀ hxₗ η hp hη hηbase hfinite hRS
  exact Deformation.equivalenceOverOfCofibered
    (Deformation.changeOfFieldsProjection_isPredeformationCategory T _
      (predeformationCategory_isPredeformationCategory B hS iΛ p x₀ hx₀ hp)).cofibered
    F.toFunctor F.projection_comm

end Deformation.Artin.Site

end
