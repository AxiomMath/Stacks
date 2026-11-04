module

public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.CategoryTheory.Limits.Comma
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# The components of a limit cone in an arrow category

A limit cone in the arrow category `Arrow T` has limit cones as its source and (when `T` has an
initial object) target components, without any assumption that `T` has limits of the shape at
hand: the source functor is right adjoint to `X ↦ 𝟙 X`, and the target functor to `X ↦ (⊥ ⟶ X)`.

## Main definitions

* `CategoryTheory.Arrow.identityFunctor`: the functor `T ⥤ Arrow T` sending `X` to `𝟙 X`.
* `CategoryTheory.Arrow.fromInitialFunctor`: the functor `T ⥤ Arrow T` sending `X` to the arrow
  out of an initial object.

## Main results

* `CategoryTheory.Arrow.identityFunctorAdjunction`: the source functor is right adjoint to
  `identityFunctor`.
* `CategoryTheory.Arrow.fromInitialFunctorAdjunction`: the target functor is right adjoint to
  `fromInitialFunctor`.
* `CategoryTheory.Arrow.isLimitLeftOfIsLimit`: the source of a limit cone is a limit cone.
* `CategoryTheory.Arrow.isLimitRightOfIsLimit`: the target of a limit cone is a limit cone, when
  `T` has an initial object.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w w' v u

namespace CategoryTheory.Arrow

variable {T : Type u} [Category.{v} T]

/-- The identity arrows, as a functor `T ⥤ Arrow T`. -/
@[simps]
def identityFunctor : T ⥤ Arrow T where
  obj X := Arrow.mk (𝟙 X)
  map f := Arrow.homMk' f f ((Category.comp_id _).trans (Category.id_comp _).symm)

/-- **The source functor of an arrow category is right adjoint to the identity arrows.** -/
def identityFunctorAdjunction : (identityFunctor : T ⥤ Arrow T) ⊣ Arrow.leftFunc :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X A =>
        { toFun := fun (φ : identityFunctor.obj X ⟶ A) => φ.left
          invFun := fun (u : X ⟶ A.left) => Arrow.homMk' u (u ≫ A.hom) (Category.id_comp _).symm
          left_inv := fun φ => Arrow.hom_ext _ _ rfl ((φ.w).trans (Category.id_comp _))
          right_inv := fun u => rfl }
      homEquiv_naturality_left_symm := by
        intro X X' Y f g
        exact Arrow.hom_ext _ _ rfl (Category.assoc _ _ _)
      homEquiv_naturality_right := by
        intro X Y Y' f g
        rfl }

/-- The source functor `Arrow T ⥤ T` is a right adjoint. -/
instance : (Arrow.leftFunc : Arrow T ⥤ T).IsRightAdjoint :=
  identityFunctorAdjunction.isRightAdjoint

variable {J : Type w} [Category.{w'} J] {D : J ⥤ Arrow T} {c : Cone D}

/-- **The source of a limit cone in an arrow category is a limit cone**, for limits of any
size. -/
def isLimitLeftOfIsLimit (hc : IsLimit c) : IsLimit (Arrow.leftFunc.mapCone c) :=
  have := Adjunction.rightAdjoint_preservesLimits.{w', w} (identityFunctorAdjunction (T := T))
  isLimitOfPreserves Arrow.leftFunc hc

/-- The arrows out of an initial object, as a functor `T ⥤ Arrow T`. -/
@[simps]
def fromInitialFunctor {I : T} (hI : IsInitial I) : T ⥤ Arrow T where
  obj X := Arrow.mk (hI.to X)
  map f := Arrow.homMk' (𝟙 I) f (hI.hom_ext _ _)

/-- **The target functor of an arrow category is right adjoint to the arrows out of an initial
object.** -/
def fromInitialFunctorAdjunction {I : T} (hI : IsInitial I) :
    fromInitialFunctor hI ⊣ Arrow.rightFunc :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X A =>
        { toFun := fun (φ : (fromInitialFunctor hI).obj X ⟶ A) => φ.right
          invFun := fun (u : X ⟶ A.right) => Arrow.homMk' (hI.to A.left) u (hI.hom_ext _ _)
          left_inv := fun φ => Arrow.hom_ext _ _ (hI.hom_ext _ _) rfl
          right_inv := fun u => rfl }
      homEquiv_naturality_left_symm := by
        intro X X' Y f g
        exact Arrow.hom_ext _ _ (hI.hom_ext _ _) rfl
      homEquiv_naturality_right := by
        intro X Y Y' f g
        rfl }

/-- **The target of a limit cone in an arrow category with an initial object is a limit cone**,
for limits of any size. -/
def isLimitRightOfIsLimit {I : T} (hI : IsInitial I) (hc : IsLimit c) :
    IsLimit (Arrow.rightFunc.mapCone c) :=
  have := Adjunction.rightAdjoint_preservesLimits.{w', w} (fromInitialFunctorAdjunction hI)
  isLimitOfPreserves Arrow.rightFunc hc

end CategoryTheory.Arrow

end
