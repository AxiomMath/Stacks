module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartCorrespondenceCompTransport

/-!
# The chart correspondence is read off by transport of the canonical sections

WIP
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

attribute [local instance] smallEtaleTopology_subcanonical

/-- The map of sections of the `f`-map of a homomorphism into the direct image is transport
along the canonical section of the chart diagram: the case of the identity is
`AlgebraicGeometry.Space.inverseImageSectionTransport_chartDiagramSection`, and the general case
follows by naturality in the target sheaf. -/
private theorem fMap_symm_app_eq_transport
    (F : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (G : Sheaf (SmallEtale.topology B S hS Y.1) (Type u))
    (ψ : G ⟶ (smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.obj F)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) (y : G.obj.obj (op d.V)) :
    ((fMapEquivPushforwardHom_ringUniverse B S hS f F G).symm ψ).app d y =
      (inverseImageSectionTransport (smallEtaleRingedToposHom B S hS f) d.V d.U
        (chartDiagramSection B S hS f d)).app F (ψ.hom.app (op d.V) y) := by
  have h := fMapEquivPushforwardHom_ringUniverse_symm_comp_app B S hS f F ψ (𝟙 _) d y
  rw [Category.comp_id] at h
  rw [h, inverseImageSectionTransport_chartDiagramSection,
    fMapEquivPushforwardHom_ringUniverse_eq_fmapDirectImageEquiv]
  rfl

/-- **Homomorphisms into the direct image are determined by transport along the canonical
sections of the chart diagrams.** -/
theorem pushforward_hom_ext_of_transport
    {F : Sheaf (SmallEtale.topology B S hS X.1) (Type u)}
    {G : Sheaf (SmallEtale.topology B S hS Y.1) (Type u)}
    {α β : G ⟶ (smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.obj F}
    (h : ∀ (d : ChartDiagram B S hS X.1 Y.1 f.hom) (y : G.obj.obj (op d.V)),
      (inverseImageSectionTransport (smallEtaleRingedToposHom B S hS f) d.V d.U
          (chartDiagramSection B S hS f d)).app F (α.hom.app (op d.V) y) =
        (inverseImageSectionTransport (smallEtaleRingedToposHom B S hS f) d.V d.U
          (chartDiagramSection B S hS f d)).app F (β.hom.app (op d.V) y)) : α = β := by
  apply (fMapEquivPushforwardHom_ringUniverse B S hS f F G).symm.injective
  generalize hξ : (fMapEquivPushforwardHom_ringUniverse B S hS f F G).symm α = ξ
  generalize hξ' : (fMapEquivPushforwardHom_ringUniverse B S hS f F G).symm β = ξ'
  have key : ∀ d y, ξ.app d y = ξ'.app d y := fun d y => by
    rw [← hξ, ← hξ', fMap_symm_app_eq_transport,
      fMap_symm_app_eq_transport]
    exact h d y
  cases ξ
  cases ξ'
  simp only [FMap.mk.injEq]
  funext d y
  exact key d y

end AlgebraicGeometry.Space

end
