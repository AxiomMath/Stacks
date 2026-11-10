module

public import Mathlib.Algebra.Category.ModuleCat.Ext.Finite
public import Mathlib.RingTheory.Noetherian.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.Ring.Epi.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksFrontier.Homology.KInjective.ChangeOfRings
public import StacksFrontier.RingTheory.Dualizing.CoextendRestrictComparison.HomologyExt
public import StacksFrontier.RingTheory.Ext.DerivedHomFiniteness

/-!
# Coherent cohomology under derived coextension of scalars

For a finite homomorphism of Noetherian rings, the derived functor of coextension of
scalars carries bounded-below complexes with finite cohomology to complexes with the
same properties.

## Main definitions

* `DerivedCategoryB.derivedCategoryBPlus` expresses membership in a bounded-below
  derived category whose cohomology lies in a specified object property.

## Main results

* `Dualizing.isBoundedBelowCoherent_obj_rightDerivedCoextendScalars` proves that derived
  coextension of scalars along a finite ring map preserves this subcategory.

## Implementation notes

The object property in `DerivedCategoryB.derivedCategoryBPlus` is specialized to
finite modules, which are the coherent modules over a Noetherian ring. For modules,
`ModuleCat.coextendScalars f` is the functor
`M ↦ Hom_A(B, M)`, equipped with its natural `B`-module structure. Thus an arbitrary
right derived functor of `ModuleCat.coextendScalars f` is the `RHom_A(B, -)` appearing in
the source. Over a Noetherian ring, coherent modules are exactly finite modules.
The module universe is independent of the ring universe, as in the comparison with Ext
in Tag 0A71.

## References

* [Stacks Project, Tag 0A72](https://stacks.math.columbia.edu/tag/0A72)
-/

@[expose] public section

universe u v w

namespace Dualizing

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated DerivedCategory
open StacksDraft.DerivedHomFiniteness

attribute [local instance] HasDerivedCategory.standard

/-- Derived coextension of scalars along a finite homomorphism of Noetherian rings sends
bounded-below complexes with coherent cohomology to bounded-below complexes with coherent
cohomology. -/
@[stacks 0A72]
theorem isBoundedBelowCoherent_obj_rightDerivedCoextendScalars
    {A B : Type u} [CommRing A] [CommRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    [HasDerivedCategory (ModuleCat.{max v u} A)] [HasDerivedCategory (ModuleCat.{max v u} B)]
    (f : A →+* B) (hf : f.Finite)
    (RF : DerivedCategory (ModuleCat.{max v u} A) ⥤ DerivedCategory (ModuleCat.{max v u} B))
    (alpha : (ModuleCat.coextendScalars f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor alpha
      (HomotopyCategory.quasiIso (ModuleCat.{max v u} A) (ComplexShape.up ℤ))]
    {K : DerivedCategory (ModuleCat.{max v u} A)}
    (hK : DerivedCategoryB.derivedCategoryBPlus
      (fun M : ModuleCat.{max v u} A ↦ Module.Finite A M) K) :
    DerivedCategoryB.derivedCategoryBPlus
      (fun M : ModuleCat.{max v u} B ↦ Module.Finite B M) (RF.obj K) := by
  let : Small.{max v u} A := small_max A
  obtain ⟨⟨a, ha⟩, hcoh⟩ := hK
  have : K.IsGE a := (DerivedCategory.isGE_iff K a).2 ha
  let M : ModuleCat.{max v u} A :=
    (ModuleCat.restrictScalars f).obj (ModuleCat.of B (ULift.{v} B))
  have : Module.Finite A M := by
    change (let : Algebra A B := f.toAlgebra; Module.Finite A (ULift.{v} B))
    let : Algebra A B := f.toAlgebra
    have : Module.Finite A B := hf
    exact Module.Finite.ulift
  have hComparison :=
    Dualizing.derivedCoextendScalarsHomologyLinearEquivExt.{u, v} f RF alpha
  refine ⟨⟨a, fun i hi => ?_⟩, fun i => ?_⟩
  · let e := hComparison.linearEquiv K i
    have : (K⟦i⟧).IsGE (a - i) :=
      DerivedCategory.TStructure.t.isGE_shift K a i (a - i) (by omega)
    have hzero : Subsingleton (DerivedCategory.Ext
        ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj M) K i) :=
      ⟨fun x y => (DerivedCategory.TStructure.t.zero x 0 (a - i) (by omega)).trans
        (DerivedCategory.TStructure.t.zero y 0 (a - i) (by omega)).symm⟩
    exact ModuleCat.isZero_iff_subsingleton.mpr
      ⟨fun x y => e.injective (hzero.elim (e x) (e y))⟩
  · let H := (DerivedCategory.homologyFunctor (ModuleCat.{max v u} B) i).obj (RF.obj K)
    have : Module.Finite A (DerivedCategory.Ext
        ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj M) K i) :=
      finite_ext_of_isGE M K a hcoh i
    have : Module.Finite A ((ModuleCat.restrictScalars f).obj H) :=
      Module.Finite.equiv (hComparison.linearEquiv K i).symm
    exact finite_of_restrictScalars_finite f H

end Dualizing

end
