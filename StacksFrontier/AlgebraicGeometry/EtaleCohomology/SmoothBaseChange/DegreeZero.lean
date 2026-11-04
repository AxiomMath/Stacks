module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.HigherBaseChangeDegreeZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.SetAbelianBaseChangeTransfer
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.SmallEtaleBaseChangeAbBridge
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.CitedStatements

/-!
# Base change in degree zero along a flat morphism with geometrically reduced fibres

Stacks 0EYS identifies `f⁻¹ g_* F` with `h_* e⁻¹ F` for a sheaf of sets `F`, in a cartesian square
whose left vertical morphism `f` is flat, locally of finite presentation and has geometrically
reduced fibres. This file reads that statement as the degree-zero case of the base change map
`f⁻¹ R^q g_* ⟶ R^q h_* e⁻¹` on abelian sheaves of Stacks, Remark 0F02, which is how the second
proof of the smooth base change theorem (Stacks, Theorem 0EYU) starts its induction.

Three comparisons are composed, none of them geometric: invertibility of the base change map for
sheaves of sets gives it for abelian sheaves
(`Stacks.EtaleCohomology.isIso_etaleAbelianBaseChange_of_isIso_smallEtaleSetBaseChange`); the
abelian base change map does not depend on the presentation of the inverse image
(`Stacks.EtaleCohomology.isIso_smallEtaleBaseChangeAb_of_isIso_etaleAbelianBaseChange`); and in
degree zero the base change map on higher direct images is the underived one
(`Stacks.EtaleCohomology.map_rightDerivedZeroUnit_comp_higherBaseChangeMapAb_zero`).

## Main results

* `Stacks.EtaleCohomology.SmoothBaseChange.isIso_higherBaseChangeMapAb_zero_of_isIso` — the
  degree-zero base change map is invertible where the underived one is.
* `Stacks.EtaleCohomology.SmoothBaseChange.isIso_higherBaseChangeMapAb_zero_of_flat` — Stacks
  0EYS in degree zero of Remark 0F02.

## References

* [Stacks Project, Tag 0EYS](https://stacks.math.columbia.edu/tag/0EYS)
* [Stacks Project, Tag 0F02](https://stacks.math.columbia.edu/tag/0F02)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology.SmoothBaseChange

attribute [local instance] HasDerivedCategory.standard

/-- The unit `T X ⟶ R⁰ T X` is invertible for the direct image of abelian sheaves. -/
private theorem isIso_rightDerivedZeroUnit_smallEtalePushforwardAb {A B : Scheme.{u}} (k : A ⟶ B)
    (G : Sheaf (smallEtaleTopology A) Ab.{u + 1}) :
    IsIso (Stacks.RightDerivedPlus.rightDerivedZeroUnit (smallEtalePushforwardAb k) G) :=
  have := (smallEtaleAdjunctionAb k).rightAdjoint_preservesLimits
  Stacks.RightDerivedPlus.isIso_rightDerivedZeroUnit _ _

/-- **In degree zero the base change map on higher direct images is invertible wherever the
underived base change map is.** The two differ by the identifications of the left exact direct
images with their degree-zero right derived functors. -/
theorem isIso_higherBaseChangeMapAb_zero_of_isIso {X' Y S T : Scheme.{u}} (f' : X' ⟶ S)
    (g : T ⟶ S) (h : Y ⟶ X') (e : Y ⟶ T) (w : h ≫ f' = e ≫ g)
    (F : Sheaf (smallEtaleTopology T) Ab.{u + 1})
    (hF : IsIso ((smallEtaleBaseChangeAb f' g h e w).app F)) :
    IsIso ((higherBaseChangeMapAb f' g h e w 0).app F) := by
  have := isIso_rightDerivedZeroUnit_smallEtalePushforwardAb g F
  have := isIso_rightDerivedZeroUnit_smallEtalePushforwardAb h ((smallEtalePullbackAb e).obj F)
  have hc : (higherBaseChangeMapAb f' g h e w 0).app F =
      inv ((smallEtalePullbackAb f').map
          (Stacks.RightDerivedPlus.rightDerivedZeroUnit (smallEtalePushforwardAb g) F ≫
            (Stacks.DerivedIndexing.rightDerivedIso (smallEtalePushforwardAb g) 0).inv.app F)) ≫
        (smallEtaleBaseChangeAb f' g h e w).app F ≫
          Stacks.RightDerivedPlus.rightDerivedZeroUnit (smallEtalePushforwardAb h)
            ((smallEtalePullbackAb e).obj F) ≫
          (Stacks.DerivedIndexing.rightDerivedIso (smallEtalePushforwardAb h) 0).inv.app
            ((smallEtalePullbackAb e).obj F) := by
    rw [← map_rightDerivedZeroUnit_comp_higherBaseChangeMapAb_zero f' g h e w F,
      IsIso.inv_hom_id_assoc]
  rw [hc]
  infer_instance

/-- **Stacks 0EYS for abelian sheaves.** The underived base change map of abelian sheaves of a
cartesian square whose left vertical morphism is flat, locally of finite presentation and has
geometrically reduced fibres is an isomorphism: the statement for sheaves of sets transfers to
abelian sheaves. -/
theorem isIso_smallEtaleBaseChangeAb_of_flat (h0EYS : FlatReducedFibresBaseChange.{u})
    {X S Y T : Scheme.{u}} (f : X ⟶ S) (h : Y ⟶ X) (e : Y ⟶ T) (g : T ⟶ S)
    (sq : IsPullback h e f g) [Flat f] [LocallyOfFinitePresentation f]
    [GeometricallyReduced f] : IsIso (smallEtaleBaseChangeAb f g h e sq.w) :=
  isIso_smallEtaleBaseChangeAb_of_isIso_etaleAbelianBaseChange f g h e sq.w
    (isIso_etaleAbelianBaseChange_of_isIso_smallEtaleSetBaseChange g f e h sq.w.symm
      (h0EYS f h e g sq))

/-- **Stacks 0EYS in degree zero of Remark 0F02.** In a cartesian square
```
X  ←-h-  Y
|f       |e
S  ←-g-  T
```
whose left vertical morphism `f` is flat, locally of finite presentation and has geometrically
reduced fibres, the base change map `f⁻¹ R⁰ g_* F ⟶ R⁰ h_* e⁻¹ F` is an isomorphism for every
abelian sheaf `F` on the small étale site of `T`. The input is the statement of Stacks 0EYS for
sheaves of sets. -/
theorem isIso_higherBaseChangeMapAb_zero_of_flat (h0EYS : FlatReducedFibresBaseChange.{u})
    {X S Y T : Scheme.{u}} (f : X ⟶ S) (h : Y ⟶ X) (e : Y ⟶ T) (g : T ⟶ S)
    (sq : IsPullback h e f g) [Flat f] [LocallyOfFinitePresentation f]
    [GeometricallyReduced f] (F : Sheaf (smallEtaleTopology T) Ab.{u + 1}) :
    IsIso ((higherBaseChangeMapAb f g h e sq.w 0).app F) :=
  have := isIso_smallEtaleBaseChangeAb_of_flat h0EYS f h e g sq
  isIso_higherBaseChangeMapAb_zero_of_isIso f g h e sq.w F inferInstance

end Stacks.EtaleCohomology.SmoothBaseChange

end
