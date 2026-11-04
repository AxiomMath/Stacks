module

public import StacksFrontier.AlgebraicGeometry.AmpleLimit.Basic
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.PullbackSectionCalculus

/-!
# The two spellings of the canonical comparison of an iterated pullback agree

The comparison of the iterated pullback of a sheaf of modules with the pullback along the
composite — `AlgebraicGeometry.Scheme.Modules.pullbackComp` followed by
`AlgebraicGeometry.Scheme.Modules.pullbackCongr` — has two spellings:

* `Stacks.AlgebraicGeometry.ModuleLimits.canHom`, a *morphism*, taking the equation in the
  direction `q ≫ g = pi`;
* `AlgebraicGeometry.Scheme.Modules.pullbackCompObjIso`, an *isomorphism*, taking the equation in
  the direction `h = f ≫ g`.

This file proves that they are the same morphism.

## Main results

* `AlgebraicGeometry.Scheme.Modules.pullbackCompObjIso_hom`: the forward direction of
  `pullbackCompObjIso` is `canHom`.
* `AlgebraicGeometry.Scheme.Modules.canHom_inv_eq`: the inverse of `canHom` is the inverse
  direction of `pullbackCompObjIso`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The forward direction of the isomorphism `AlgebraicGeometry.Scheme.Modules.pullbackCompObjIso`
is the morphism `Stacks.AlgebraicGeometry.ModuleLimits.canHom`, with the equation between the
composite and the third morphism turned round. -/
theorem pullbackCompObjIso_hom {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
    (hh : h = f ≫ g) (M : Z.Modules) :
    (pullbackCompObjIso f g h hh M).hom =
      Stacks.AlgebraicGeometry.ModuleLimits.canHom f g h hh.symm M := by
  simp only [pullbackCompObjIso, Stacks.AlgebraicGeometry.ModuleLimits.canHom,
    Iso.trans_hom, Iso.app_hom]

/-- The inverse of `Stacks.AlgebraicGeometry.ModuleLimits.canHom` is the inverse direction of
`AlgebraicGeometry.Scheme.Modules.pullbackCompObjIso`. -/
theorem canHom_inv_eq {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
    (hh : h = f ≫ g) (M : Z.Modules) :
    inv (Stacks.AlgebraicGeometry.ModuleLimits.canHom f g h hh.symm M) =
      (pullbackCompObjIso f g h hh M).inv := by
  refine IsIso.inv_eq_of_hom_inv_id ?_
  rw [← pullbackCompObjIso_hom f g h hh M]
  exact (pullbackCompObjIso f g h hh M).hom_inv_id

end AlgebraicGeometry.Scheme.Modules

end
