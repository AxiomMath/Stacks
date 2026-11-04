module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedChaoticConstantDerivedAdjunction

/-!
# The unit of the derived adjunction `F' ⊣ RΓ` on the class of a complex

Let `C` be a small category with the chaotic topology, `R` a commutative ring and `B` a sheaf of
differential graded algebras over the constant sheaf of rings with value `R`, such that extension
of scalars `K ↦ K ⊗_R B` inverts quasi-isomorphisms. The unit of the derived adjunction
`F' ⊣ RΓ` at the class of a complex `K` is invertible exactly when the class of the strict unit
`K ⟶ Γ(K ⊗_R B)` followed by the comparison map `Γ(K ⊗_R B) ⟶ RΓ(K ⊗_R B)` is.

## Main results

* `Stacks.ChaoticSite.isIso_derivedExtendAdjunction_unit_app_Qh_iff`: the unit at the class of
  `K`, as an object of the homotopy category, is invertible exactly when the composite above is.
* `Stacks.ChaoticSite.isIso_derivedExtendAdjunction_unit_app_iff_of_iso`: the unit is invertible
  at isomorphic objects together.

## References

* [Stacks Project, Proposition 24.35.4 (Tag 0GZK)](https://stacks.math.columbia.edu/tag/0GZK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Sheaf Stacks.PresheafOfModules

universe u

namespace Stacks.ChaoticSite

open _root_.SheafOfModules _root_.SheafOfModules.DifferentialGradedModule

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.SheafOfModules.botWEqualsLocallyBijective

variable {C : Type u} [SmallCategory C] {R : Type u} [CommRing R]
  {B : _root_.SheafOfModules.DifferentialGradedAlgebra.{u, u} (constRingSheaf (C := C) R)}

/-- The unit of the adjunction of homotopy categories at the class of a complex is the class of
the strict unit `K ⟶ Γ(K ⊗_R B)`. -/
theorem homotopyExtendAdjunction_unit_app (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    (homotopyExtendAdjunction B).unit.app ((_root_.HomotopyCategory.quotient _ _).obj K) =
      (_root_.HomotopyCategory.quotient _ _).map ((extendAdjunction (castAlg B)).unit.app K) :=
  rfl

/-- The unit of `F' ⊣ RΓ` at the class of `K` is invertible exactly when the class of the strict
unit `K ⟶ Γ(K ⊗_R B)` followed by the comparison map `Γ(K ⊗_R B) ⟶ RΓ(K ⊗_R B)` is. -/
theorem isIso_derivedExtendAdjunction_unit_app_Qh_iff (hB : ExtendInvertsQuasiIso B)
    (K : _root_.HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) :
    IsIso ((derivedExtendAdjunction hB).unit.app (DerivedCategory.Qh.obj K)) ↔
      IsIso (DerivedCategory.Qh.map ((homotopyExtendAdjunction B).unit.app K) ≫
        (globalUnit B).app ((homotopyExtend' B).obj K)) := by
  rw [← derivedExtendAdjunction_unit_fac hB K]
  exact (isIso_comp_right_iff _ _).symm

/-- The unit of `F' ⊣ RΓ` is invertible at isomorphic objects together. -/
theorem isIso_derivedExtendAdjunction_unit_app_iff_of_iso (hB : ExtendInvertsQuasiIso B)
    {X Y : DerivedCategory (ModuleCat.{u} R)} (e : X ≅ Y) :
    IsIso ((derivedExtendAdjunction hB).unit.app X) ↔
      IsIso ((derivedExtendAdjunction hB).unit.app Y) :=
  (MorphismProperty.isomorphisms _).arrow_mk_iso_iff
    (Arrow.isoMk e ((derivedExtend hB ⋙ derivedGlobalSections R B).mapIso e)
      ((derivedExtendAdjunction hB).unit.naturality e.hom))

end Stacks.ChaoticSite

end
