module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.SectionsConormalFibreTwoSpace

/-!
# The two-space comparison of inverse images, through the comparison of Stacks 03LU at a module

Let `g : X' ⟶ X` be a morphism of algebraic spaces, `u : T ⟶ X` and `v : T' ⟶ X'` scheme points
and `h : T' ⟶ T` with `g ∘ v = u ∘ h`.  For `f' : Z ⟶ T'` the identification
`AlgebraicGeometry.Space.pointTwoSpaceCompIso` of `(u ∘ h ∘ f')^*ℰ` with `(v ∘ f')^* g^*ℰ` is the
equation of the two points followed by the comparison of Stacks 03LU at `ℰ`.  This file names that
comparison at a module (`modulePullbackCompObjIso`) and records the unfolding of
`pointTwoSpaceCompIso` through it, with the source of the points read as the represented algebraic
space of `Z`; this is the spelling in which the cocycle of Stacks 03LU behind the comparison of
fibres over two spaces is stated.

## Main definitions

* `AlgebraicGeometry.Space.modulePullbackCompObjIso`: `(a ≫ b)^* M ≅ a^* b^* M`.

## Main results

* `AlgebraicGeometry.Space.pointTwoSpaceCompIso_eq`: `pointTwoSpaceCompIso`, unfolded.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 0B4I](https://stacks.math.columbia.edu/tag/0B4I)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (X : AlgebraicSpaces B S hS) (E : SheafOfModules.{u} (structureRingSheaf B S hS X))

section ModuleCoherence

variable {W Y X₀ : AlgebraicSpaces B S hS}

/-- The comparison `(a ≫ b)^* M ≅ a^* b^* M` of Stacks 03LU at a module, with the iterated inverse
image as its target. -/
def modulePullbackCompObjIso (a : W ⟶ Y) (b : Y ⟶ X₀) (M : Modules.{u, u} B S hS X₀.1 X₀.2) :
    (modulePullback B S hS (a ≫ b)).obj M ≅
      (modulePullback B S hS a).obj ((modulePullback B S hS b).obj M) :=
  ((modulePullbackCompIso B S hS a b).app M).symm

/-- `modulePullbackCompObjIso` is the comparison of Stacks 03LU at the module. -/
theorem modulePullbackCompObjIso_hom (a : W ⟶ Y) (b : Y ⟶ X₀)
    (M : Modules.{u, u} B S hS X₀.1 X₀.2) :
    (modulePullbackCompObjIso a b M).hom = (modulePullbackCompIso B S hS a b).inv.app M :=
  rfl

end ModuleCoherence

section TwoSpaceCocycle

variable {T : BigFppfOver B S hS} (u : yoneda.obj T ⟶ X.1)
  {X' : AlgebraicSpaces B S hS} (g : X' ⟶ X) {T' : BigFppfOver B S hS}
  (v : yoneda.obj T' ⟶ X'.1) (h : T' ⟶ T) (hvh : v ≫ g.hom = yoneda.map h ≫ u)

include hvh in
/-- The inverse images of `ℰ` along the point `u ∘ h ∘ f'` of `X` and along `g ∘ (v ∘ f')` agree,
the source of the points read as the represented algebraic space of `Z`. -/
theorem modulePullback_obj_pointHom_twoSpace_eq {Z : BigFppfOver B S hS} (f' : Z ⟶ T') :
    (modulePullback B S hS
        (X := (⟨yoneda.obj Z, isAlgebraicSpace_yoneda B S hS Z⟩ : AlgebraicSpaces B S hS))
        (pointHom (X := X) (yoneda.map (f' ≫ h) ≫ u))).obj E =
      (modulePullback B S hS (CategoryStruct.comp (obj := AlgebraicSpaces B S hS)
        (X := (⟨yoneda.obj Z, isAlgebraicSpace_yoneda B S hS Z⟩ : AlgebraicSpaces B S hS))
        (pointHom (X := X') (yoneda.map f' ≫ v)) g)).obj E := by
  rw [← yoneda_map_comp_point_twoSpace X u g v h hvh f']
  rfl

/-- **`pointTwoSpaceCompIso`, unfolded**: the equation of the two points followed by the
comparison of Stacks 03LU at `ℰ`, the source of the points read as the represented algebraic
space of `Z`. -/
theorem pointTwoSpaceCompIso_eq {Z : BigFppfOver B S hS} (f' : Z ⟶ T') :
    pointTwoSpaceCompIso X E u g v h hvh f' =
      eqToIso (modulePullback_obj_pointHom_twoSpace_eq X E u g v h hvh f') ≪≫
        modulePullbackCompObjIso
          (W := (⟨yoneda.obj Z, isAlgebraicSpace_yoneda B S hS Z⟩ : AlgebraicSpaces B S hS))
          (pointHom (X := X') (yoneda.map f' ≫ v)) g E :=
  rfl

end TwoSpaceCocycle

end AlgebraicGeometry.Space

end
