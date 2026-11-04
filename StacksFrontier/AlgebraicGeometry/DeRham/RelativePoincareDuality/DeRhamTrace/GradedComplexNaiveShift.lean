module

public import StacksFrontier.AlgebraicGeometry.DeRham.NaiveCupProductInverseImageBase
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.DeRhamTrace.GradedComplexLaxShift
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorCommShiftComplexBifunctors

/-!
# The naive cup product along `(X, 𝒪_X) ⟶ (X, f⁻¹𝒪_S)` and the shifts

Let `ι = Stacks.DeRhamDirectImage.toInverseImageBase f`. For a pairing `h : Tot(K ⊗_{𝒪_X} L) ⟶ W`
of complexes of `𝒪_X`-modules, the naive cup product followed by `ι_*h` is a pairing
`Tot(ι_*K ⊗_{f⁻¹𝒪_S} ι_*L) ⟶ ι_*W` (`Stacks.DeRhamDirectImage.pushedCupMap`). On each summand it is
the lax comparison of restriction of scalars followed by `ι_*` of `h` on that summand. Hence it
commutes with the shift of pairings by `(a, b)`, `a + b = 0`, and with the shift of the second
variable and of the target, the identification `ι_*(K[n]) = (ι_*K)[n]` being the identity in each
degree. This is a step of the proof of [Stacks, Tag 0G8K].

## Main definitions

* `Stacks.DeRhamDirectImage.pushedCupMap`: the naive cup product followed by `ι_*h`.

## Main results

* `Stacks.DeRhamDirectImage.ιMapBifunctor_pushedCupMap_f`
* `Stacks.DeRhamDirectImage.mapBifunctorMap_commShiftIso_shiftedPairing_pushedCupMap`
* `Stacks.DeRhamDirectImage.mapBifunctorMap_commShiftIso_rightShift_pushedCupMap`

## References

* [Stacks Project, Tag 0G8K](https://stacks.math.columbia.edu/tag/0G8K)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.NaiveCupProductOnRingedSpaces (pushforwardComplex naiveCupProduct)
open Stacks.Cohomology.DerivedPullbackTensor (tensorComplexBifunctorOn)
open AlgebraicGeometry.RingedSpace.KFlatDerivedPullback renaming Modules → ModulesOn

universe u

namespace Stacks.DeRhamDirectImage

attribute [local implicit_reducible] structureSheafRing
  StacksDraft.KFlat.modulePullback StacksDraft.KFlat.modulePushforward
  Stacks.SheafOfModules.Tensor.ringSheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf TopCat.Presheaf.IsSheaf TopCat.Sheaf

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **The naive cup product followed by `ι_*` of a pairing**: for `h : Tot(K ⊗_{𝒪_X} L) ⟶ W`,
the pairing `Tot(ι_*K ⊗_{f⁻¹𝒪_S} ι_*L) ⟶ ι_*Tot(K ⊗_{𝒪_X} L) ⟶ ι_*W`. -/
def pushedCupMap {A B W : CochainComplex (ModulesOn X.toRingedSpace) ℤ}
    (h : ((tensorComplexBifunctorOn X.toRingedSpace).obj A).obj B ⟶ W) :
    ((tensorComplexBifunctorOn (inverseImageBase f)).obj
      ((pushforwardComplex (toInverseImageBase f)).obj A)).obj
      ((pushforwardComplex (toInverseImageBase f)).obj B) ⟶
      (pushforwardComplex (toInverseImageBase f)).obj W :=
  naiveCupProduct (toInverseImageBase f) A B ≫ (pushforwardComplex (toInverseImageBase f)).map h

/-- On the summand `ι_*K^i ⊗ ι_*L^j`, `pushedCupMap f h` is the lax comparison of restriction of
scalars followed by `ι_*` of `h` on the summand `K^i ⊗ L^j`. -/
theorem ιMapBifunctor_pushedCupMap_f {A B W : CochainComplex (ModulesOn X.toRingedSpace) ℤ}
    (h : ((tensorComplexBifunctorOn X.toRingedSpace).obj A).obj B ⟶ W) (i j k : ℤ)
    (hk : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (i, j) = k) :
    HomologicalComplex.ιMapBifunctor ((pushforwardComplex (toInverseImageBase f)).obj A)
        ((pushforwardComplex (toInverseImageBase f)).obj B)
        (Stacks.SheafOfModules.Tensor.sheafTensor (inverseImageBase f).sheaf) (ComplexShape.up ℤ)
        i j k hk ≫ (pushedCupMap f h).f k =
      inverseImageTensorLax f (A.X i) (B.X j) ≫
        (StacksDraft.KFlat.modulePushforward (toInverseImageBase f)).map
          (HomologicalComplex.ιMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf)
            (ComplexShape.up ℤ) i j k hk ≫ h.f k) :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ _) (ιMapBifunctor_naiveCupProduct_f_toInverseImageBase f A B i j k hk)).trans
      ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Functor.map_comp _ _ _).symm)))

/-- **`pushedCupMap` commutes with the shift of pairings by `(a, b)`**, `a + b = 0`. -/
theorem mapBifunctorMap_commShiftIso_shiftedPairing_pushedCupMap
    {A B W : CochainComplex (ModulesOn X.toRingedSpace) ℤ}
    (h : ((tensorComplexBifunctorOn X.toRingedSpace).obj A).obj B ⟶ W) (a b : ℤ)
    (hab : a + b = 0) :
    HomologicalComplex.mapBifunctorMap
        (((pushforwardComplex (toInverseImageBase f)).commShiftIso a).hom.app A)
        (((pushforwardComplex (toInverseImageBase f)).commShiftIso b).hom.app B)
        (Stacks.SheafOfModules.Tensor.sheafTensor (inverseImageBase f).sheaf) (ComplexShape.up ℤ) ≫
      (tensorComplexBifunctorOn (inverseImageBase f)).shiftedPairing (pushedCupMap f h) a b hab =
      pushedCupMap f ((tensorComplexBifunctorOn X.toRingedSpace).shiftedPairing h a b hab) := by
  have key := CochainComplex.mapBifunctorMap_commShiftIso_shiftedPairing_eq_of_lax
    (C₁ := ModulesOn X.toRingedSpace) (C₂ := ModulesOn X.toRingedSpace)
    (D := ModulesOn X.toRingedSpace) (C₁' := ModulesOn (inverseImageBase f))
    (C₂' := ModulesOn (inverseImageBase f)) (D' := ModulesOn (inverseImageBase f))
    (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf)
    (Stacks.SheafOfModules.Tensor.sheafTensor (inverseImageBase f).sheaf)
    (StacksDraft.KFlat.modulePushforward (toInverseImageBase f))
    (StacksDraft.KFlat.modulePushforward (toInverseImageBase f))
    (StacksDraft.KFlat.modulePushforward (toInverseImageBase f))
    (inverseImageTensorLax f) h a b hab
  refine key (pushedCupMap f h) _ ?_ ?_
  · intro i j k hk
    exact ιMapBifunctor_pushedCupMap_f f h i j k hk
  · intro i j k hk
    have t := ιMapBifunctor_pushedCupMap_f f
      ((tensorComplexBifunctorOn X.toRingedSpace).shiftedPairing h a b hab) i j k hk
    refine t.trans ?_
    refine congrArg (_ ≫ ·)
      (congrArg (StacksDraft.KFlat.modulePushforward (toInverseImageBase f)).map ?_)
    refine congrArg (_ ≫ ·) ?_
    rfl

/-- **`pushedCupMap` commutes with the shift of the second variable and of the target.** -/
theorem mapBifunctorMap_commShiftIso_rightShift_pushedCupMap
    {A B W : CochainComplex (ModulesOn X.toRingedSpace) ℤ}
    (h : ((tensorComplexBifunctorOn X.toRingedSpace).obj A).obj B ⟶ W) (m : ℤ) :
    HomologicalComplex.mapBifunctorMap (𝟙 ((pushforwardComplex (toInverseImageBase f)).obj A))
        (((pushforwardComplex (toInverseImageBase f)).commShiftIso m).hom.app B)
        (Stacks.SheafOfModules.Tensor.sheafTensor (inverseImageBase f).sheaf) (ComplexShape.up ℤ) ≫
      (((tensorComplexBifunctorOn (inverseImageBase f)).obj
          ((pushforwardComplex (toInverseImageBase f)).obj A)).commShiftIso m).hom.app
        ((pushforwardComplex (toInverseImageBase f)).obj B) ≫ (pushedCupMap f h)⟦m⟧' =
      pushedCupMap f (A := A) (B := B⟦m⟧) (W := W⟦m⟧)
        ((((tensorComplexBifunctorOn X.toRingedSpace).obj A).commShiftIso m).hom.app B ≫ h⟦m⟧') ≫
        ((pushforwardComplex (toInverseImageBase f)).commShiftIso m).hom.app W := by
  have key := CochainComplex.mapBifunctorMap_commShiftIso_rightShift_eq_of_lax
    (C₁ := ModulesOn X.toRingedSpace) (C₂ := ModulesOn X.toRingedSpace)
    (D := ModulesOn X.toRingedSpace) (C₁' := ModulesOn (inverseImageBase f))
    (C₂' := ModulesOn (inverseImageBase f)) (D' := ModulesOn (inverseImageBase f))
    (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf)
    (Stacks.SheafOfModules.Tensor.sheafTensor (inverseImageBase f).sheaf)
    (StacksDraft.KFlat.modulePushforward (toInverseImageBase f))
    (StacksDraft.KFlat.modulePushforward (toInverseImageBase f))
    (StacksDraft.KFlat.modulePushforward (toInverseImageBase f))
    (inverseImageTensorLax f) h m
  refine key (pushedCupMap f h) _ ?_ ?_
  · intro i j k hk
    exact ιMapBifunctor_pushedCupMap_f f h i j k hk
  · intro i j k hk
    refine (ιMapBifunctor_pushedCupMap_f f (A := A) (B := B⟦m⟧) (W := W⟦m⟧) _ i j k hk).trans ?_
    refine congrArg (_ ≫ ·)
      (congrArg (StacksDraft.KFlat.modulePushforward (toInverseImageBase f)).map ?_)
    refine congrArg (_ ≫ ·) ?_
    rfl

end Stacks.DeRhamDirectImage

end
