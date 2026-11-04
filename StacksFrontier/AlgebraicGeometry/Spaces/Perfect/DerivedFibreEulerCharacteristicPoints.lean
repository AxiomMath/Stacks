module

public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopologyUnique

/-!
# Local constancy on the points of an algebraic space is étale local

## Main results

* `AlgebraicGeometry.Space.isLocallyConstant_of_forall_exists_chart`: a function on the points
  of an algebraic space is locally constant as soon as every point lies in the image of an étale
  chart on which the function is locally constant.
-/

@[expose] public noncomputable section

open CategoryTheory Topology

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Local constancy on the points of an algebraic space is étale local.** A function on `|X|`
is locally constant as soon as every point is the image of a point of an étale chart
`φ : h_U ⟶ X` along which the function, read on `U` through the homeomorphism of Stacks 03BX, is
locally constant. -/
theorem isLocallyConstant_of_forall_exists_chart {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) {Y : Type*} (f : points B S hS X → Y)
    (h : ∀ x, ∃ (U : BigFppfOver B S hS) (φ : yoneda.obj U ⟶ X)
      (_ : (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ)
      (u : (BigFppfOver.toScheme B S hS).obj U),
      pointsMap B S hS (yoneda.obj U) φ ((schemePointsHomeomorph B S hS U).symm u) = x ∧
        IsLocallyConstant (f ∘ pointsMap B S hS (yoneda.obj U) φ ∘
          (schemePointsHomeomorph B S hS U).symm)) :
    IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  obtain ⟨U, φ, het, u, hu, hlc⟩ := h x
  let ψ := pointsMap B S hS (yoneda.obj U) φ ∘ (schemePointsHomeomorph B S hS U).symm
  have hψ : IsOpenMap ψ :=
    (isOpenMap_pointsMap_of_etale B S hS hX U φ het).comp
      (schemePointsHomeomorph B S hS U).symm.isOpenMap
  let W := (f ∘ ψ) ⁻¹' {f x}
  refine ⟨ψ '' W, hψ W (hlc.isOpen_fiber (f x)), ⟨u, congrArg f hu, hu⟩, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  exact hz

end AlgebraicGeometry.Space

end
