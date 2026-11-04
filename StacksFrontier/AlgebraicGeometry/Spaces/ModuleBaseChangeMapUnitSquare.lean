module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleEtaleBaseChangeUnitSquare

/-!
# The unit square of the base change map of modules on algebraic spaces

For a commutative square `i ≫ f = f' ≫ g` of algebraic spaces, the base change map
`AlgebraicGeometry.Space.moduleBaseChangeMap` is the mate of the comparison of the two composite
direct images.  This file records the square it makes with the two **units** of the adjunctions
of the horizontal morphisms, `CategoryTheory.unit_mateEquiv_symm` at those adjunctions.

## Main results

* `AlgebraicGeometry.Space.unit_comp_modulePushforward_map_moduleBaseChangeMap`: the direct image
  along `f` of the unit along `i`, followed by the comparison of the two composite direct images,
  is the unit along `g` followed by the direct image along `g` of the base change map.

## Implementation notes

Reading the mate backwards through the units needs no counit of
`AlgebraicGeometry.Space.modulePullbackAdjunction`: the identity holds for every commutative
square with nothing assumed, and it determines the map, a morphism out of a value of a left
adjoint being determined by its adjunct.  A chartwise reading of the base change map therefore
goes through it, since the unit of `AlgebraicGeometry.Space.modulePullbackAdjunction` is computed
on the sections over an étale chart — it is `AlgebraicGeometry.Space.modulePullbackChartSection`
— and the counit is not.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {X X' Y Y' : AlgebraicSpaces B S hS} (i : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)

/-- `CategoryTheory.unit_mateEquiv_symm` with the 2-cell presented as a plain natural
transformation between the two composites and with every component written out, so that an
instantiation of it has nothing left to unify.  Without this intermediate the instantiation below
exhausts the elaborator's recursion depth on the final match. -/
private theorem unit_mate_of_natTrans {A₁ A₂ A₃ A₄ : Type*}
    [Category A₁] [Category A₂] [Category A₃] [Category A₄]
    {L₁ : A₁ ⥤ A₂} {R₁ : A₂ ⥤ A₁} {L₂ : A₃ ⥤ A₄} {R₂ : A₄ ⥤ A₃}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) {G : A₁ ⥤ A₃} {H : A₂ ⥤ A₄}
    (ρ : R₁ ⋙ G ⟶ H ⋙ R₂) (c : A₁) :
    G.map (adj₁.unit.app c) ≫ ρ.app (L₁.obj c) =
      adj₂.unit.app (G.obj c) ≫
        R₂.map (((mateEquiv adj₁ adj₂).symm (TwoSquare.mk R₁ H G R₂ ρ)).app c) :=
  unit_mateEquiv_symm adj₁ adj₂ (TwoSquare.mk R₁ H G R₂ ρ) c

/-- **The unit square of the base change map itself**, for an arbitrary commutative square and
with no counit anywhere: the direct image along `f` of the unit of the adjunction of `i`,
followed by the comparison of the two composite direct images, is the unit of the adjunction of
`g` followed by the direct image along `g` of
`AlgebraicGeometry.Space.moduleBaseChangeMap`.

Since a morphism out of a value of a left adjoint is determined by its adjunct, this pins the
base change map down exactly as
`AlgebraicGeometry.Space.moduleBaseChangeMap_adjoint_split` does, but through the *units* of the
two adjunctions of the horizontal morphisms instead of the counit of the adjunction of `f`.
That is what a chartwise reading of the base change map needs: this development computes the
unit of `AlgebraicGeometry.Space.modulePullbackAdjunction` on the sections over an étale chart,
as `AlgebraicGeometry.Space.modulePullbackChartSection`, and computes no counit of it.  So the
counit computation that the implementation notes above record as unavailable is not needed to
read the base change map backwards; only the units are.

This is `CategoryTheory.unit_mateEquiv_symm` at the two adjunctions of the horizontal morphisms
and at the 2-cell whose mate the base change map is, which is
`AlgebraicGeometry.Space.modulePushforwardSquareComparison` on the nose. -/
theorem unit_comp_modulePushforward_map_moduleBaseChangeMap (comm : i ≫ f = f' ≫ g)
    (K : Modules.{u, u} B S hS X.1 X.2) :
    (modulePushforward B S hS f).map ((modulePullbackAdjunction B S hS i).unit.app K) ≫
        (modulePushforwardSquareComparison B S hS i f' f g comm).app
          ((modulePullback B S hS i).obj K) =
      (modulePullbackAdjunction B S hS g).unit.app ((modulePushforward B S hS f).obj K) ≫
        (modulePushforward B S hS g).map ((moduleBaseChangeMap f g f' i comm).app K) := by
  have e : moduleBaseChangeMap f g f' i comm =
      (mateEquiv (modulePullbackAdjunction B S hS i)
          (modulePullbackAdjunction B S hS g)).symm
        (TwoSquare.mk (modulePushforward B S hS i) (modulePushforward B S hS f')
          (modulePushforward B S hS f) (modulePushforward B S hS g)
          (modulePushforwardSquareComparison B S hS i f' f g comm)) := rfl
  rw [e]
  exact unit_mate_of_natTrans (modulePullbackAdjunction B S hS i)
    (modulePullbackAdjunction B S hS g)
    (modulePushforwardSquareComparison B S hS i f' f g comm) K

end AlgebraicGeometry.Space

end
