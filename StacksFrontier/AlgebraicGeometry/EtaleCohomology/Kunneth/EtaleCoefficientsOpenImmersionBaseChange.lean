module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.TensorBaseChangeProjection
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.ProjectionMapPushforward
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.EtaleBaseChange

/-!
# Base change along an open immersion on `D(-_étale, ℤ/m)`

For a cartesian square
```
X' <-h-- Y
|f'      |e
S  <-g-- T
```
with `f'` an open immersion, the base change map `(f')⁻¹Rg_* ⟶ Rh_*e⁻¹` of `D(-_étale, ℤ/m)`
(`Stacks.EtaleCohomology.EtaleCoefficients.baseChangeMap`) is an isomorphism at every bounded below
object (`isIso_baseChangeMap_app_of_isOpenImmersion`), in particular at the inverse image of the
structure sheaf along any morphism (`isIso_baseChangeMap_app_pullback_unit_of_isOpenImmersion`).
By `Stacks.EtaleCohomology.EtaleCoefficients.isIso_baseChangeMap_app_iff` it is the abelian base
change map, which is invertible in every degree at every sheaf
(`Stacks.EtaleCohomology.isIso_higherBaseChangeMapAb_app_of_isOpenImmersion`).

## References

* [Stacks Project, Tag 0F1H](https://stacks.math.columbia.edu/tag/0F1H)
* [Stacks Project, Tag 0EYM](https://stacks.math.columbia.edu/tag/0EYM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology.EtaleCoefficients

-- `Stacks.EtaleCohomology.EtaleCoefficients.baseChangeMap` and
-- `Stacks.EtaleCohomology.smallEtaleDerivedBaseChangeAb` (at
-- `StacksFrontier/AlgebraicGeometry/EtaleCohomology/BaseChangeHigher/BaseChangeCondition.lean:220`)
-- are stated for the standard model of the derived category.
attribute [local instance] HasDerivedCategory.standard

attribute [local instance] Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus
attribute [local instance] Stacks.DerivedIndexing.isTriangulated_rightDerivedFunctorPlus

/-! ### Base change along an open immersion -/

section OpenImmersion

variable (m : ℕ) {X' S T Y : Scheme.{u}} (f' : X' ⟶ S) (g : T ⟶ S) (h : Y ⟶ X') (e : Y ⟶ T)

/-- **Base change along an open immersion on `D⁺(-_étale, ℤ/m)`.** For a cartesian square
`h ≫ f' = e ≫ g` with `f'` an open immersion, the base change map `(f')⁻¹Rg_* ⟶ Rh_*e⁻¹` of
`D(-_étale, ℤ/m)` is an isomorphism at every bounded below object: by
`isIso_baseChangeMap_app_iff` it is the abelian one, which is invertible at every sheaf placed in
degree zero (`Stacks.EtaleCohomology.isIso_higherBaseChangeMapAb_app_of_isOpenImmersion`), hence at
every bounded below complex. -/
theorem isIso_baseChangeMap_app_of_isOpenImmersion (sq : IsPullback h e f' g)
    [IsOpenImmersion f']
    (K : DerivedCategory.Plus (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (ringedTopos (ULift.{u + 1} (ZMod m)) T).O))) :
    IsIso ((baseChangeMap (ULift.{u + 1} (ZMod m)) f' g h e sq.w).app
      (DerivedCategory.Plus.ι.obj K)) := by
  rw [isIso_baseChangeMap_app_iff]
  obtain ⟨b, hb⟩ := K.property
  have := commShift_smallEtaleDerivedBaseChangeAb f' g h e sq.w
  have hUK : ((forgetDerivedPlus (ULift.{u + 1} (ZMod m)) T).obj K).IsGE b :=
    (etaleToSheaf (ULift.{u + 1} (ZMod m)) T).isGE_mapDerivedCategoryPlus_obj K b
      ((DerivedCategory.Plus.isGE_ι_obj_iff K b).1 hb)
  refine DerivedCategory.Plus.isIso_app_of_isGE_of_isIso_app_single
    (smallEtaleDerivedBaseChangeAb f' g h e sq.w) ?_ ?_ _ b hUK fun q => ?_
  · intro L k hL
    have := (smallEtalePushforwardAb g).isGE_rightDerivedFunctorPlus_obj L k
    exact (smallEtalePullbackAb f').isGE_rightDerivedFunctorPlus_obj _ k
  · intro L k hL
    have := (smallEtalePullbackAb e).isGE_rightDerivedFunctorPlus_obj L k
    exact (smallEtalePushforwardAb h).isGE_rightDerivedFunctorPlus_obj _ k
  · exact (BaseChangeOverField.isIso_smallEtaleDerivedBaseChangeAb_app_single_iff f' g h e sq.w _).2
      fun r => isIso_higherBaseChangeMapAb_app_of_isOpenImmersion sq r _

/-- The base change map is invertible at `ℤ/m` iff it is at `ℤ/m` placed in degree zero. -/
private theorem isIso_baseChangeMap_app_unit_iff (w : h ≫ f' = e ≫ g) :
    IsIso ((baseChangeMap (ULift.{u + 1} (ZMod m)) f' g h e w).app
      (unit (ULift.{u + 1} (ZMod m)) T)) ↔
    IsIso ((baseChangeMap (ULift.{u + 1} (ZMod m)) f' g h e w).app
      (DerivedCategory.Plus.ι.obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
          (ringedTopos (ULift.{u + 1} (ZMod m)) T).O))))) := by
  let O := SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
    (ringedTopos (ULift.{u + 1} (ZMod m)) T).O)
  have i : DerivedCategory.Plus.ι.obj ((DerivedCategory.Plus.singleFunctor _ 0).obj O) ≅
      unit (ULift.{u + 1} (ZMod m)) T :=
    (DerivedCategory.Plus.singleFunctorιIso _ 0).app O
  exact (NatTrans.isIso_app_iff_of_iso _ i).symm

/-- **Base change along an open immersion at the inverse image of the structure sheaf**: for any
morphism `r : T ⟶ Z`, the base change map of a cartesian square along an open immersion is
invertible at `r⁻¹Λ̲[0] ≅ Λ̲[0]`, a bounded below object. -/
theorem isIso_baseChangeMap_app_pullback_unit_of_isOpenImmersion (sq : IsPullback h e f' g)
    [IsOpenImmersion f'] {Z : Scheme.{u}} (r : T ⟶ Z) :
    IsIso ((baseChangeMap (ULift.{u + 1} (ZMod m)) f' g h e sq.w).app
      ((pullback (ULift.{u + 1} (ZMod m)) r).obj (unit (ULift.{u + 1} (ZMod m)) Z))) := by
  rw [NatTrans.isIso_app_iff_of_iso _ (pullbackUnitIso (ULift.{u + 1} (ZMod m)) r),
    isIso_baseChangeMap_app_unit_iff]
  exact isIso_baseChangeMap_app_of_isOpenImmersion m f' g h e sq _

/-- An exact functor carries an object placed in degree zero of `D⁺` to its image placed in
degree zero. -/
def mapDerivedCategoryPlusSingleFunctorObjIso {A B : Type*} [Category* A] [Category* B]
    [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B] (L : A ⥤ B)
    [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L] (N : A) :
    L.mapDerivedCategoryPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj N) ≅
      (DerivedCategory.Plus.singleFunctor B 0).obj (L.obj N) :=
  DerivedCategory.Plus.ι.preimageIso ((L.mapDerivedCategorySingleFunctor 0).app N)

/-- **The base change map of `D(-_étale, ℤ/m)` at the structure sheaf from the abelian one**: if
the abelian base change map is invertible at the underlying abelian sheaf of `ℤ/m` placed in
degree zero, the base change map of `D(-_étale, ℤ/m)` is invertible at `ℤ/m[0]`. -/
theorem isIso_baseChangeMap_app_unit_of_isIso_single (w : h ≫ f' = e ≫ g)
    (H : IsIso ((smallEtaleDerivedBaseChangeAb f' g h e w).app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((etaleToSheaf (ULift.{u + 1} (ZMod m)) T).obj (SheafOfModules.unit
          (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos (ULift.{u + 1} (ZMod m)) T).O)))))) :
    IsIso ((baseChangeMap (ULift.{u + 1} (ZMod m)) f' g h e w).app
      (unit (ULift.{u + 1} (ZMod m)) T)) := by
  rwa [isIso_baseChangeMap_app_unit_iff, isIso_baseChangeMap_app_iff,
    NatTrans.isIso_app_iff_of_iso _ (mapDerivedCategoryPlusSingleFunctorObjIso _ _)]

end OpenImmersion

end Stacks.EtaleCohomology.EtaleCoefficients

end
