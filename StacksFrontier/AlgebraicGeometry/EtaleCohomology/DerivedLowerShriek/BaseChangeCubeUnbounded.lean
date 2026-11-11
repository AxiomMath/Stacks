module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.ProperBaseChangeUnbounded

/-!
# The base change map for `Rf_!` attached to a cube of compactifications, on `D(X_étale, Λ)`

Let `f : X ⟶ Y` and `f' : X' ⟶ Y'` be morphisms with compactifications `j : X ⟶ X̄` and
`j' : X' ⟶ X̄'`, and let `g : Y' ⟶ Y`, `g' : X' ⟶ X` and `φ : X̄' ⟶ X̄` form a commutative cube
whose face through the two open immersions is cartesian. The base change map
`g⁻¹ ∘ Rf_! ⟶ Rf'_! ∘ (g')⁻¹` of [Stacks, Tag 0F7L] on the unbounded derived categories is
defined for such a cube by the recipe of the source: the base change map `g⁻¹ Rf̄_* ⟶ Rf̄'_* φ⁻¹`
followed by the inverse of `(g')⁻¹ ∘ Rj'_! ≅ φ⁻¹ ∘ Rj_!`. For the cube of the base change of `j`
(`AlgebraicGeometry.CompactificationOf.baseChange`) it is
`Stacks.EtaleCohomology.derivedLowerShriekUnboundedBaseChange`. This is the unbounded counterpart
of `Stacks.EtaleCohomology.derivedLowerShriekBaseChangeCube`.

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleDerivedExtensionByZeroUnboundedCubeIso`:
  `(g')⁻¹ ∘ Rj'_! ≅ Rj_! ∘ φ⁻¹` on `D` for a cartesian square.
* `Stacks.EtaleCohomology.derivedLowerShriekUnboundedBaseChangeCube`: the base change map of a
  cube.

## Main results

* `Stacks.EtaleCohomology.derivedLowerShriekUnboundedBaseChange_eq_cube`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

/-- **Extension by zero commutes with inverse image on `D(-_étale, Λ)`**, for an arbitrary
cartesian square `g' ≫ j = j' ≫ φ` with `j` and `j'` étale ([Stacks, Tag 03S6]):
`(g')⁻¹ ∘ Rj'_! ≅ Rj_! ∘ φ⁻¹`. Both extensions by zero are computed degreewise, so this is the
underived isomorphism `Stacks.EtaleCohomology.etaleModuleInverseImageExtensionByZeroIso` read on
derived categories. -/
def etaleModuleDerivedExtensionByZeroUnboundedCubeIso (Λ : Type r) [Ring Λ]
    {X X' Xb Xb' : Scheme.{u}} {g' : X' ⟶ X} {j : X ⟶ Xb} {j' : X' ⟶ Xb'} {φ : Xb' ⟶ Xb}
    [Etale j] [Etale j'] (hc : IsPullback g' j' j φ) :
    (etaleModuleInverseImage.{u, r} Λ g').mapDerivedCategory ⋙
        etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ j' ≅
      etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ j ⋙
        (etaleModuleInverseImage.{u, r} Λ φ).mapDerivedCategory :=
  Functor.isoWhiskerLeft _ (etaleModuleDerivedExtensionByZeroUnboundedIso.{u, r} Λ j') ≪≫
    (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso _ _).symm ≪≫
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _
      (etaleModuleInverseImageExtensionByZeroIso.{u, r} Λ hc) ≪≫
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.isoWhiskerRight (etaleModuleDerivedExtensionByZeroUnboundedIso.{u, r} Λ j).symm _

/-- The isomorphism of
`Stacks.EtaleCohomology.etaleModuleDerivedExtensionByZeroUnboundedBaseChangeIso` is that of the
cube of the base change of the compactification. -/
theorem etaleModuleDerivedExtensionByZeroUnboundedBaseChangeIso_eq_cube (Λ : Type r) [Ring Λ]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    (sq : IsPullback g' f' f g) (j : CompactificationOf (Over.mk f)) :
    etaleModuleDerivedExtensionByZeroUnboundedBaseChangeIso.{u, r} Λ sq j =
      etaleModuleDerivedExtensionByZeroUnboundedCubeIso Λ (j.isPullback_baseChange sq) :=
  rfl

variable (Λ : Type r) [CommRing Λ] {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
  {g : Y' ⟶ Y} {g' : X' ⟶ X}

/-- **The base change map `g⁻¹ ∘ Rf_! ⟶ Rf'_! ∘ (g')⁻¹` of a cube of compactifications, on
`D(X_étale, Λ)`** ([Stacks, Tag 0F7L]): for compactifications `j` of `f` and `j'` of `f'` and
`φ : X̄' ⟶ X̄` with `j' ≫ φ = g' ≫ j` cartesian and `f̄' ≫ g = φ ≫ f̄`, the unbounded base change
map `g⁻¹ Rf̄_* Rj_! ⟶ Rf̄'_* φ⁻¹ Rj_!` followed by `Rf̄'_*` of the inverse of
`(g')⁻¹ ∘ Rj'_! ≅ φ⁻¹ ∘ Rj_!`. -/
def derivedLowerShriekUnboundedBaseChangeCube (j : CompactificationOf (Over.mk f))
    (j' : CompactificationOf (Over.mk f')) (φ : j'.space ⟶ j.space)
    (hc : IsPullback g' j'.immersion j.immersion φ) (w : j'.toBase ≫ g = φ ≫ j.toBase) :
    derivedLowerShriekUnbounded.{u, r} f j Λ ⋙ etaleModuleDerivedInverseImage.{u, r} Λ g ⟶
      etaleModuleDerivedInverseImage.{u, r} Λ g' ⋙ derivedLowerShriekUnbounded.{u, r} f' j' Λ :=
  Functor.whiskerLeft (etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ j.immersion)
      (etaleModuleDerivedBaseChangeUnbounded.{u, r} Λ j.toBase g φ j'.toBase w.symm) ≫
    Functor.whiskerRight (etaleModuleDerivedExtensionByZeroUnboundedCubeIso Λ hc).inv
      (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ j'.toBase)

/-- The base change map of `Stacks.EtaleCohomology.derivedLowerShriekUnboundedBaseChange` is that
of the cube of the base change of the compactification. -/
theorem derivedLowerShriekUnboundedBaseChange_eq_cube (sq : IsPullback g' f' f g)
    (j : CompactificationOf (Over.mk f)) :
    derivedLowerShriekUnboundedBaseChange.{u, r} Λ sq j =
      derivedLowerShriekUnboundedBaseChangeCube Λ j (j.baseChange sq) (pullback.fst j.toBase g)
        (j.isPullback_baseChange sq) pullback.condition.symm :=
  rfl

/-- The component of the base change map of a cube. -/
theorem derivedLowerShriekUnboundedBaseChangeCube_app (j : CompactificationOf (Over.mk f))
    (j' : CompactificationOf (Over.mk f')) (φ : j'.space ⟶ j.space)
    (hc : IsPullback g' j'.immersion j.immersion φ) (w : j'.toBase ≫ g = φ ≫ j.toBase)
    (K : DerivedCategory (EtaleModules.{u, r} Λ X)) :
    (derivedLowerShriekUnboundedBaseChangeCube Λ j j' φ hc w).app K =
      (etaleModuleDerivedBaseChangeUnbounded.{u, r} Λ j.toBase g φ j'.toBase w.symm).app
          ((etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ j.immersion).obj K) ≫
        (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ j'.toBase).map
          ((etaleModuleDerivedExtensionByZeroUnboundedCubeIso Λ hc).inv.app K) :=
  rfl

end Stacks.EtaleCohomology

end
