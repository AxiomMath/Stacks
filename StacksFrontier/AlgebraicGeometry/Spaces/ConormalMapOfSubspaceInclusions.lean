module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleOfImmersionBaseChange

/-!
# The canonical map of immersions at a square of closed subspaces

For a commutative square of closed subspaces `Z ⊆ X`, `Z' ⊆ X'` with `g : X ⟶ X'` and
`f : Z ⟶ Z'`, there are two constructions of the canonical map `f^*𝒞_{Z'/X'} ⟶ 𝒞_{Z/X}` of
Stacks 04CP: `AlgebraicGeometry.Space.conormalMap`, the inverse image along the inclusion of the
map `g^*𝓘' ⟶ 𝓘` of defining ideal sheaves, and
`AlgebraicGeometry.Space.conormalMapOfImmersions`, built from the conormal algebras of the two
immersions. In degree one the second is the first conjugated by isomorphisms
(`AlgebraicGeometry.Space.conormalMapOfImmersions_eq_kernelIdealZPowSquareMap` and
`AlgebraicGeometry.Space.kernelIdealSquareMap_one_eq_idealSheafMap`), so one is invertible
exactly when the other is, and both are invertible as soon as the inverse image of the map of
defining ideal sheaves is. This is what lets the conormal criterion of Stacks 06BH, stated for
`AlgebraicGeometry.Space.conormalMapOfImmersions`, be fed by a computation of the map of defining
ideal sheaves, as in the last step of the proof of Stacks 0D3X.

## Main results

* `AlgebraicGeometry.Space.isIso_conormalMapOfImmersions_of_isIso_map_idealSheafMap`.

## References

* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 06BH](https://stacks.math.columbia.edu/tag/06BH)
-/

@[expose] public section

open CategoryTheory

universe u

/-- A functor carries `eqToHom ≫ m ≫ eqToHom` to an isomorphism when it carries `m` to one. -/
theorem CategoryTheory.Functor.isIso_map_eqToHom_comp_comp_eqToHom {C D : Type*} [Category C]
    [Category D] (F : C ⥤ D) {A A' T T' : C} (hA : A = A') (m : A' ⟶ T) (hT : T = T')
    [IsIso (F.map m)] : IsIso (F.map (eqToHom hA ≫ m ≫ eqToHom hT)) := by
  subst hA hT
  simpa using (inferInstance : IsIso (F.map m))

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The canonical map of immersions at a square of closed subspaces is invertible when the
inverse image along the inclusion of `Z` of the map `g^*𝓘' ⟶ 𝓘` of defining ideal sheaves is**:
in degree one it is that inverse image, conjugated by isomorphisms. -/
theorem isIso_conormalMapOfImmersions_of_isIso_map_idealSheafMap {X X' : AlgebraicSpaces B S hS}
    (Z : ClosedSubspaces B S hS X.1) (Z' : ClosedSubspaces B S hS X'.1) (g : X ⟶ X')
    (f : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Z'.1.toFunctor, Z'.2.1⟩ : AlgebraicSpaces B S hS))
    (hsq : subspaceInclusion B S hS X Z ≫ g = f ≫ subspaceInclusion B S hS X' Z')
    (h1 : IsIso ((modulePullback B S hS (subspaceInclusion B S hS X Z)).map
      (idealSheafMap B S hS Z Z' g f hsq))) :
    IsIso (conormalMapOfImmersions B S hS (subspaceInclusion B S hS X Z)
      (subspaceInclusion B S hS X' Z') f g (isImmersion_subspaceInclusion B S hS X Z)
      (isImmersion_subspaceInclusion B S hS X' Z') hsq) := by
  rw [conormalMapOfImmersions_eq_kernelIdealZPowSquareMap, kernelIdealZPowSquareMap_eq,
    kernelIdealSquareMap_one_eq_idealSheafMap]
  have hsqIso := Iso.isIso_hom ((squarePullbackCompIso B S hS (subspaceInclusion B S hS X Z)
      (subspaceInclusion B S hS X' Z') f g hsq).app
    (kernelIdealSheafZPow B S hS (subspaceInclusion B S hS X' Z') 1).toSheafOfModules)
  have hideal := @Functor.isIso_map_eqToHom_comp_comp_eqToHom _ _ _ _
    (modulePullback B S hS (subspaceInclusion B S hS X Z)) _ _ _ _
    (congrArg (modulePullback B S hS g).obj
      (kernelIdealSheafZPow_one_toSheafOfModules_eq B S hS X' Z'))
    (idealSheafMap B S hS Z Z' g f hsq)
    (kernelIdealSheafZPow_one_toSheafOfModules_eq B S hS X Z).symm h1
  exact IsIso.comp_isIso' (Iso.isIso_hom ((modulePullback B S hS _).mapIso
      (conormalModuleOfImmersionZPowIso B S hS _ _).symm)) (IsIso.comp_isIso'
    (@IsIso.comp_isIso' _ _ _ _ _ _ _ hsqIso hideal)
    (Iso.isIso_hom (conormalModuleOfImmersionZPowIso B S hS _ _)))

end AlgebraicGeometry.Space
