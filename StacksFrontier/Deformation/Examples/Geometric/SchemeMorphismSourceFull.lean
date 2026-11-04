module

public import StacksFrontier.Deformation.CofiberedFull
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismSource
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismsRimSchlessinger
public import StacksFrontier.Deformation.Examples.Geometric.SchemesCofibered
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismsRimSchlessingerUnconditional

/-!
# Fullness of the source-forgetful functor, reduced to one fibre

[Stacks, Tag 0E3X] asserts that `Deformation.Examples.schemeMorphismSourceForgetful`, from
deformations of a morphism `f : X ⟶ Y` to deformations of `X`, is an equivalence. This file
shows that it is full as soon as every arrow between the deformations of `X` induced by two
deformations of `f` that lies over an **identity** of `𝒞_Λ` is in its image.

## Main results

* `Deformation.Examples.schemeMorphismSourceForgetful_comp_projection_cofiberedInGroupoids`:
  the composite of the source-forgetful functor with the projection of deformations of `X` to
  `𝒞_Λ` is cofibered in groupoids.
* `Deformation.Examples.schemeMorphismSourceForgetful_full_of_lift_of_isHomLift_id`: fullness of
  the source-forgetful functor from the lifts of arrows over identities.

## References

* [Stacks Project, Tag 0E3X](https://stacks.math.columbia.edu/tag/0E3X)
* [Stacks Project, Tag 0E3T](https://stacks.math.columbia.edu/tag/0E3T)
* [Stacks Project, Tag 0DY7](https://stacks.math.columbia.edu/tag/0DY7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Deformation.Examples

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (pX : X ⟶ baseSpec (residueFieldBase Λ k)) (pY : Y ⟶ baseSpec (residueFieldBase Λ k))
  (hf : f ≫ pY = pX)

/-- **The composite of the source-forgetful functor with the projection of deformations of `X`
is cofibered in groupoids.** -/
theorem schemeMorphismSourceForgetful_comp_projection_cofiberedInGroupoids :
    IsCofiberedInGroupoids (schemeMorphismSourceForgetful f pX pY hf ⋙
      schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)) := by
  rw [schemeMorphismSourceForgetful_comp_projection f pX pY hf]
  exact isCofiberedInGroupoids_overForget
    (schemeMorphismFamilyFunctor_cofiberedInGroupoids.{u, u} (Λ := Λ) (k := k)) _
    isTerminal_residueFieldBase

/-- **[Stacks, Tag 0E3X], fullness reduced to one fibre.** The source-forgetful functor on
deformations of `f : X ⟶ Y` is full as soon as every arrow between the deformations of `X` that
two deformations of `f` induce, *lying over an identity of `𝒞_Λ`*, is in its image. -/
theorem schemeMorphismSourceForgetful_full_of_lift_of_isHomLift_id
    (hlift : ∀ (R Q : schemeMorphismDeformationCategory f pX pY hf)
      (θ : (schemeMorphismSourceForgetful f pX pY hf).obj R ⟶
        (schemeMorphismSourceForgetful f pX pY hf).obj Q),
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)).IsHomLift
          (𝟙 ((schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)).obj
            ((schemeMorphismSourceForgetful f pX pY hf).obj Q))) θ →
        ∃ ψ : R ⟶ Q, (schemeMorphismSourceForgetful f pX pY hf).map ψ = θ) :
    (schemeMorphismSourceForgetful f pX pY hf).Full :=
  Deformation.full_of_exists_lift_of_isHomLift_id (schemeMorphismSourceForgetful f pX pY hf)
    (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX))
    (schemeMorphismSourceForgetful_comp_projection_cofiberedInGroupoids f pX pY hf)
    (schemeDeformationCategoryProjection_cofiberedInGroupoids (Over.mk pX))
    hlift

end Deformation.Examples

end
