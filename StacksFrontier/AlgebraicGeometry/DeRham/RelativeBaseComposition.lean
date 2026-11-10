module

public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothSpectralSequence

/-!
# The coefficient-space morphisms of a composite

For a ringed space `(X, 𝒪_X)` and continuous maps `i₁ : Z ⟶ W`, `i₂ : W ⟶ V`, `j : V ⟶ X`, the
canonical morphisms of ringed spaces
`(Z, (i₁ i₂ j)^{-1}𝒪_X) ⟶ (W, (i₂ j)^{-1}𝒪_X) ⟶ (V, j^{-1}𝒪_X)` compose to the canonical
morphism `(Z, (i₁ i₂ j)^{-1}𝒪_X) ⟶ (V, j^{-1}𝒪_X)` over `i₁ ≫ i₂`. For a scheme `S` and morphisms
`g₁ : Y₁ ⟶ Y₂`, `g₂ : Y₂ ⟶ X`, `f : X ⟶ S` this says that the morphism along which the relative
de Rham complex of `Y₁/S` is pushed forward to `X` does not depend on whether one goes through
`Y₂` or not.

## Main results

* `AlgebraicGeometry.RingedSpace.inverseImageMap_comp`: functoriality of the canonical
  morphisms.
* `Stacks.DeRhamSmooth.relativeBase_comp`: the same for the coefficient-space morphisms of
  schemes over a base.

## Implementation notes

Both structure maps are transposes under the inverse-image/direct-image adjunction, so the
equality is checked after transposing: the transpose of a composite is the unit along the
second map followed by the direct image of the first structure map, which is the transpose of
the first structure map along the composite adjunction, i.e. the unit along the composite.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

-- Arrows of sheaves must be read through the category structure, not the reflexive quiver one.
attribute [-instance] CategoryTheory.catToReflQuiver

namespace AlgebraicGeometry.RingedSpace

variable (X : RingedSpace.{u, u}) {Z W V : TopCat.{u}}

/-- The sheaf-level structure map of `inverseImageMap`. -/
noncomputable abbrev inverseImageMapSheafHom (i : Z ⟶ W) (j : W ⟶ X.carrier) :
    (TopCat.Sheaf.pullback CommRingCat.{u} j).obj X.sheaf ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} i).obj
        ((TopCat.Sheaf.pullback CommRingCat.{u} (i ≫ j)).obj X.sheaf) :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} j).homEquiv X.sheaf
      ((TopCat.Sheaf.pushforward CommRingCat.{u} i).obj
        ((TopCat.Sheaf.pullback CommRingCat.{u} (i ≫ j)).obj X.sheaf))).symm
    ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} (i ≫ j)).unit.app X.sheaf)

/-- The sheaf-level structure map along `i₂` followed by the direct image along `i₂` of the
sheaf-level structure map along `i₁` is the sheaf-level structure map along `i₁ ≫ i₂`. -/
lemma inverseImageMapSheafHom_comp (i₁ : Z ⟶ W) (i₂ : W ⟶ V) (j : V ⟶ X.carrier) :
    inverseImageMapSheafHom X i₂ j ≫
        (TopCat.Sheaf.pushforward CommRingCat.{u} i₂).map (inverseImageMapSheafHom X i₁ (i₂ ≫ j)) =
      inverseImageMapSheafHom X (i₁ ≫ i₂) j := by
  change _ = ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} j).homEquiv X.sheaf
      ((TopCat.Sheaf.pushforward CommRingCat.{u} i₂).obj
        ((TopCat.Sheaf.pushforward CommRingCat.{u} i₁).obj
          ((TopCat.Sheaf.pullback CommRingCat.{u} (i₁ ≫ i₂ ≫ j)).obj X.sheaf)))).symm
    (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} (i₁ ≫ i₂ ≫ j)).unit.app
      X.sheaf : X.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} j).obj
        ((TopCat.Sheaf.pushforward CommRingCat.{u} i₂).obj
          ((TopCat.Sheaf.pushforward CommRingCat.{u} i₁).obj
            ((TopCat.Sheaf.pullback CommRingCat.{u} (i₁ ≫ i₂ ≫ j)).obj X.sheaf)))))
  refine (Equiv.eq_symm_apply _).2 ?_
  rw [Adjunction.homEquiv_naturality_right]
  refine Eq.trans (congrArg (· ≫ _) (Equiv.apply_symm_apply _ _)) ?_
  have h := ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} (i₂ ≫ j)).homEquiv
      X.sheaf ((TopCat.Sheaf.pushforward CommRingCat.{u} i₁).obj
        ((TopCat.Sheaf.pullback CommRingCat.{u} (i₁ ≫ i₂ ≫ j)).obj X.sheaf))).apply_symm_apply
    (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} (i₁ ≫ i₂ ≫ j)).unit.app
      X.sheaf : X.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} (i₂ ≫ j)).obj
        ((TopCat.Sheaf.pushforward CommRingCat.{u} i₁).obj
          ((TopCat.Sheaf.pullback CommRingCat.{u} (i₁ ≫ i₂ ≫ j)).obj X.sheaf))))
  rw [Adjunction.homEquiv_unit] at h
  exact h

/-- **The canonical morphisms of inverse-image ringed spaces compose.** -/
theorem inverseImageMap_comp (i₁ : Z ⟶ W) (i₂ : W ⟶ V) (j : V ⟶ X.carrier) :
    inverseImageMap X i₁ (i₂ ≫ j) ≫ inverseImageMap X i₂ j = inverseImageMap X (i₁ ≫ i₂) j :=
  InducedCategory.hom_ext (PresheafedSpace.hext _ _ rfl
    (heq_of_eq (congrArg (fun t => t.hom) (inverseImageMapSheafHom_comp X i₁ i₂ j))))

end AlgebraicGeometry.RingedSpace

namespace Stacks.DeRhamSmooth

variable {Y₁ Y₂ X S : Scheme.{u}} (g₁ : Y₁ ⟶ Y₂) (g₂ : Y₂ ⟶ X) (f : X ⟶ S)

/-- **The coefficient-space morphism of a composite is the composite.** -/
theorem relativeBase_comp :
    relativeBase g₁ (g₂ ≫ f) ≫ relativeBase g₂ f = relativeBase (g₁ ≫ g₂) f :=
  AlgebraicGeometry.RingedSpace.inverseImageMap_comp _ g₁.base g₂.base f.base

end Stacks.DeRhamSmooth

end
