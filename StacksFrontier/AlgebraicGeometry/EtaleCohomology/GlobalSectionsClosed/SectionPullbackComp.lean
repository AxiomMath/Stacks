module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsClosed.FiniteSurjectiveDescent

/-!
# Pulling a section back along a composite

For morphisms of schemes `g : X₁ ⟶ X₂` and `f : X₂ ⟶ X₃` and a sheaf of sets `H` on the small
étale site of `X₃`, the pullback of a section `s ∈ H(W)` to `W ×_{X₃} X₁` along the composite
`g ≫ f` is, through the composition isomorphism `g⁻¹(f⁻¹H) ≅ (g ≫ f)⁻¹H` and the comparison
`(W ×_{X₃} X₂) ×_{X₂} X₁ ≅ W ×_{X₃} X₁` of base changes, the pullback along `g` of the pullback
along `f` of `s`. The composition isomorphism is the mate of the composition of direct images, so
this is the unit characterisation of a mate (`CategoryTheory.unit_conjugateEquiv_symm`).

## Main results

* `Stacks.EtaleCohomology.etalePullbackCompIso_inv_smallEtaleSectionPullback` — the pullback of
  a section along the composite, restricted along the comparison of base changes and transported
  through the composition isomorphism, is the iterated pullback.
* `Stacks.EtaleCohomology.etalePullbackCompIso_hom_smallEtaleSectionPullback` — the same, read in
  the other direction.
* `Stacks.EtaleCohomology.smallEtaleSectionPullback_eq_unit` — the pullback of a section is the
  unit of the inverse-image adjunction.

## References

* [Stacks Project, Tag 03PZ](https://stacks.math.columbia.edu/tag/03PZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u v

namespace Stacks.EtaleCohomology

variable {X₁ X₂ X₃ : Scheme.{u}} (g : X₁ ⟶ X₂) (f : X₂ ⟶ X₃) (p : X₁ ⟶ X₃) (hp : p = g ≫ f)
  (H : Sheaf X₃.smallEtaleTopology (Type (max (u + 1) v)))

/-- The pullback of a section is the unit of the inverse-image adjunction at that section. -/
theorem smallEtaleSectionPullback_eq_unit {Y Z : Scheme.{u}} (i : Z ⟶ Y)
    (F : Sheaf Y.smallEtaleTopology (Type (max (u + 1) v))) (W : Y.Etale)
    (s : F.obj.obj (op W)) :
    smallEtaleSectionPullback.{u, v} i F W s =
      ((smallEtaleInverseImageAdjunction.{u, v} i).unit.app F).hom.app (op W) s :=
  rfl

/-- **Pulling a section back along a composite**, read through the composition isomorphism
`g⁻¹(f⁻¹H) ≅ p⁻¹H`: the iterated pullback of `s ∈ H(W)` is carried to the pullback of `s` along
`p = g ≫ f`, restricted along the comparison `(W ×_{X₃} X₂) ×_{X₂} X₁ ⟶ W ×_{X₃} X₁` of base
changes. -/
theorem etalePullbackCompIso_hom_smallEtaleSectionPullback (W : X₃.Etale)
    (s : H.obj.obj (op W)) :
    ((etalePullbackCompIso f g p hp).hom.app H).hom.app
        (op ((smallEtaleBaseChange g).obj ((smallEtaleBaseChange f).obj W)))
      (smallEtaleSectionPullback.{u, v} g ((smallEtaleInverseImage f).obj H)
        ((smallEtaleBaseChange f).obj W) (smallEtaleSectionPullback.{u, v} f H W s)) =
    ((smallEtaleInverseImage.{u, v} p).obj H).obj.map
        ((etaleBaseChangeCompIso f g p hp).inv.app W).op
      (smallEtaleSectionPullback.{u, v} p H W s) := by
  have h := unit_conjugateEquiv_symm (smallEtaleInverseImageAdjunction.{u, v} p)
    ((smallEtaleInverseImageAdjunction.{u, v} f).comp (smallEtaleInverseImageAdjunction.{u, v} g))
    (etalePushforwardCompIso f g p hp).inv H
  have hu : ((smallEtaleInverseImageAdjunction.{u, v} f).unit.app H).hom.app (op W) ≫
      ((smallEtaleInverseImageAdjunction.{u, v} g).unit.app
        ((smallEtaleInverseImage f).obj H)).hom.app
        (op ((smallEtaleBaseChange f).obj W)) ≫
      ((etalePullbackCompIso f g p hp).hom.app H).hom.app
        (op ((smallEtaleBaseChange g).obj ((smallEtaleBaseChange f).obj W))) =
      ((smallEtaleInverseImageAdjunction.{u, v} p).unit.app H).hom.app (op W) ≫
        ((smallEtaleInverseImage p).obj H).obj.map
          ((etaleBaseChangeCompIso f g p hp).inv.app W).op :=
    (congrArg (fun q => q.hom.app (op W)) h).symm
  have hs := ConcreteCategory.congr_hom hu s
  simp only [ConcreteCategory.comp_apply] at hs
  exact hs

/-- **Pulling a section back along a composite.** For `g : X₁ ⟶ X₂` and `f : X₂ ⟶ X₃` with
`p = g ≫ f`, a sheaf of sets `H` on the small étale site of `X₃` and a section `s ∈ H(W)`: the
pullback of `s` along `p`, restricted to `(W ×_{X₃} X₂) ×_{X₂} X₁` along the comparison of base
changes and transported through the composition isomorphism `p⁻¹H ≅ g⁻¹(f⁻¹H)`, is the pullback
along `g` of the pullback along `f` of `s`. -/
theorem etalePullbackCompIso_inv_smallEtaleSectionPullback (W : X₃.Etale)
    (s : H.obj.obj (op W)) :
    ((etalePullbackCompIso f g p hp).inv.app H).hom.app
        (op ((smallEtaleBaseChange g).obj ((smallEtaleBaseChange f).obj W)))
      (((smallEtaleInverseImage.{u, v} p).obj H).obj.map
        ((etaleBaseChangeCompIso f g p hp).inv.app W).op
        (smallEtaleSectionPullback.{u, v} p H W s)) =
    smallEtaleSectionPullback.{u, v} g ((smallEtaleInverseImage f).obj H)
      ((smallEtaleBaseChange f).obj W) (smallEtaleSectionPullback.{u, v} f H W s) := by
  rw [← etalePullbackCompIso_hom_smallEtaleSectionPullback.{u, v} g f p hp H W s]
  exact ConcreteCategory.congr_hom (congrArg (fun q => q.hom.app
      (op ((smallEtaleBaseChange g).obj ((smallEtaleBaseChange f).obj W))))
    ((etalePullbackCompIso f g p hp).hom_inv_id_app H)) _

end Stacks.EtaleCohomology

end
