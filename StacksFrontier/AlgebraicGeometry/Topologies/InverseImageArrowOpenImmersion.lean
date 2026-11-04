module

public import Mathlib.Geometry.RingedSpace.OpenImmersion
public import StacksFrontier.AlgebraicGeometry.Topologies.InverseImageArrow
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.ClosedSubsetPullbackLeftExact

/-!
# The inverse-image ringed space along an open immersion of the source

Let `h : X ⟶ T` be a morphism of ringed spaces and `ι : U ⟶ X` an open immersion. The square
`(ι, 𝟙 T)` from `ι ≫ h` to `h` in the arrow category induces a morphism of inverse-image ringed
spaces `(U, (ι ≫ h)⁻¹𝒪_T) ⟶ (X, h⁻¹𝒪_T)`. This file proves that it is an open immersion.

More generally the conclusion holds for any morphism `u` of arrows whose source component is an
open immersion and whose target component is an isomorphism.

## Main results

* `AlgebraicGeometry.RingedSpace.isOpenImmersion_inverseImageArrowMap`: the induced morphism of
  inverse-image ringed spaces is an open immersion.
* `AlgebraicGeometry.RingedSpace.openImmersionLift`: the lift of a morphism of ringed spaces
  through an open immersion whose range contains its image.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.RingedSpace

/-- The stalk map of a composite of morphisms of ringed spaces. -/
private theorem stalkMap_hom_comp {P Q R : RingedSpace.{u, u}} (f : P ⟶ Q) (g : Q ⟶ R) (x : P) :
    (f ≫ g).hom.stalkMap x = g.hom.stalkMap (f.hom.base x) ≫ f.hom.stalkMap x :=
  PresheafedSpace.stalkMap.comp f.hom g.hom x

/-- **The morphism of inverse-image ringed spaces induced by a morphism of arrows is an open
immersion** when the source component of the morphism of arrows is an open immersion and the
target component is an isomorphism. -/
theorem isOpenImmersion_inverseImageArrowMap {a b : Arrow RingedSpace.{u, u}} (w : a ⟶ b)
    [SheafedSpace.IsOpenImmersion w.left] [IsIso w.right] :
    SheafedSpace.IsOpenImmersion (inverseImageArrowMap w) := by
  have hfac := inverseImageArrowMap_comp_projection w
  have : ∀ x, IsIso ((inverseImageArrowMap w).hom.stalkMap x) := by
    intro x
    have h1 : IsIso ((inverseImageProjection a.right a.hom.hom.base ≫ w.right).hom.stalkMap x) := by
      rw [stalkMap_hom_comp]
      have h2 : IsIso w.right.hom := (SheafedSpace.forgetToPresheafedSpace.map_isIso w.right)
      have h3 := isIso_stalkMap_inverseImageProjection a.right a.hom.hom.base x
      exact @IsIso.comp_isIso _ _ _ _ _ _ _
        (PresheafedSpace.stalkMap.isIso w.right.hom _) h3
    rw [← hfac, stalkMap_hom_comp] at h1
    have := isIso_stalkMap_inverseImageProjection b.right b.hom.hom.base
      ((inverseImageArrowMap w).hom.base x)
    exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ this h1
  exact SheafedSpace.IsOpenImmersion.of_stalk_iso _
    (PresheafedSpace.IsOpenImmersion.base_open (f := w.left.hom))

/-- **The lift of a morphism of ringed spaces through an open immersion** whose range contains
the image of the morphism. -/
def openImmersionLift {X Y Z : RingedSpace.{u, u}} (f : X ⟶ Z) [SheafedSpace.IsOpenImmersion f]
    (g : Y ⟶ Z) (H : Set.range g.hom.base ⊆ Set.range f.hom.base) : Y ⟶ X :=
  InducedCategory.homMk (PresheafedSpace.IsOpenImmersion.lift f.hom g.hom H)

/-- The lift `openImmersionLift f g H`, followed by `f`, is `g`. -/
@[reassoc (attr := simp)]
theorem openImmersionLift_fac {X Y Z : RingedSpace.{u, u}} (f : X ⟶ Z)
    [SheafedSpace.IsOpenImmersion f] (g : Y ⟶ Z)
    (H : Set.range g.hom.base ⊆ Set.range f.hom.base) : openImmersionLift f g H ≫ f = g :=
  InducedCategory.hom_ext (PresheafedSpace.IsOpenImmersion.lift_fac f.hom g.hom H)

end AlgebraicGeometry.RingedSpace

end
