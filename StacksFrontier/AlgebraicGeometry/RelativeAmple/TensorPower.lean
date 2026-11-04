module

public import StacksFrontier.AlgebraicGeometry.RelativeAmple.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.AmpleAndExtension.TensorPower
public import StacksFrontier.AlgebraicGeometry.PullbackTensor.StalkFormula
public import StacksFrontier.AlgebraicGeometry.Divisors.TensorPower
public import StacksFrontier.AlgebraicGeometry.Ample.AmpleCriteria
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AmpleBridge.Basic

/-!
# Relative ampleness of a positive tensor power

An invertible sheaf of modules `L` on a scheme `X` is ample relative to a morphism `f : X ⟶ S`
if and only if any one of its positive tensor powers `L^{⊗ n}`, `n ≥ 1`, is.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isRelativelyAmple_iff_tensorPower_isRelativelyAmple`: an
  invertible sheaf of modules is ample relative to a morphism if and only if any one of its
  positive tensor powers is (Stacks Tag 02NN).

## References

* [Stacks Project, Tag 02NN](https://stacks.math.columbia.edu/tag/02NN)
* [Stacks Project, Tag 01PT](https://stacks.math.columbia.edu/tag/01PT)
* [Stacks Project, Tag 01VH](https://stacks.math.columbia.edu/tag/01VH)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory RingedSpaceModuleAdjunction
open Stacks.SheafOfModules

universe u

namespace AlgebraicGeometry.Scheme.Modules

section Pullback

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  (L : SheafOfModules.{u} (structureSheafRing Y))
  [AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf
    (structureSheafRing Y).property L]
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
    (structureSheafRing X).property ((modulePullback f).obj L)]

/-- The pullback of the `(k + 1)`st tensor power of an invertible sheaf of modules is the
`(k + 1)`st tensor power of its pullback. -/
private noncomputable def pullbackTensorPowerIsoFromOne (k : ℕ) :
    (modulePullback f).obj (Invertible.tensorPower Y.presheaf
        (structureSheafRing Y).property L ((k + 1 : ℕ) : ℤ)) ≅
      Invertible.tensorPower X.presheaf (structureSheafRing X).property
        ((modulePullback f).obj L) ((k + 1 : ℕ) : ℤ) :=
  match k with
  | 0 =>
      (modulePullback f).mapIso
          (Invertible.tensorPowerOneIso Y.presheaf (structureSheafRing Y).property L) ≪≫
        (Invertible.tensorPowerOneIso X.presheaf (structureSheafRing X).property
          ((modulePullback f).obj L)).symm
  | k + 1 =>
      ((modulePullback f).mapIso (Invertible.tensorPowerSuccIso Y.presheaf
          (structureSheafRing Y).property L ((k + 1 : ℕ) : ℤ))).symm ≪≫
        Stacks.RingedSpace.pullbackTensorIsoApp f
          (Invertible.tensorPower Y.presheaf (structureSheafRing Y).property L
            ((k + 1 : ℕ) : ℤ)) L ≪≫
        Invertible.tensorProductIso X.presheaf (structureSheafRing X).property
          (pullbackTensorPowerIsoFromOne k) (Iso.refl _) ≪≫
        Invertible.tensorPowerSuccIso X.presheaf (structureSheafRing X).property
          ((modulePullback f).obj L) ((k + 1 : ℕ) : ℤ)

/-- `f^*(L^{⊗ n}) ≅ (f^*L)^{⊗ n}` for a positive exponent `n`. -/
private noncomputable def pullbackTensorPowerIso (n : ℕ) (hn : 1 ≤ n) :
    (modulePullback f).obj (Invertible.tensorPower Y.presheaf
        (structureSheafRing Y).property L (n : ℤ)) ≅
      Invertible.tensorPower X.presheaf (structureSheafRing X).property
        ((modulePullback f).obj L) (n : ℤ) := by
  have heq : n - 1 + 1 = n := Nat.sub_add_cancel hn
  rw [← heq]
  exact pullbackTensorPowerIsoFromOne f L (n - 1)

end Pullback

section Relative

variable {X S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
  (n : ℕ) (V : S.Opens)

/-- Over the inverse image of a fixed open of the base, the pullback of an invertible sheaf of
modules is ample exactly when the pullback of its `n`th tensor power is, for `n ≥ 1`. -/
private theorem isAmple_pullback_iff_tensorPower (hn : 1 ≤ n) :
    letI := Stacks.RingedSpace.algebraicGeometryIsInvertible_modulePullback
      (f ⁻¹ᵁ V).ι.toLRSHom.toShHom L
    letI := Invertible.tensorPower_isInvertible X.presheaf X.ringCatSheaf.2 L (n : ℤ)
    letI := Stacks.RingedSpace.algebraicGeometryIsInvertible_modulePullback
      (f ⁻¹ᵁ V).ι.toLRSHom.toShHom
      (Invertible.tensorPower X.presheaf X.ringCatSheaf.2 L (n : ℤ))
    (Stacks.Ample.IsAmple (f ⁻¹ᵁ V).toScheme
        ((modulePullback (f ⁻¹ᵁ V).ι.toLRSHom.toShHom).obj L) ↔
      Stacks.Ample.IsAmple (f ⁻¹ᵁ V).toScheme
        ((modulePullback (f ⁻¹ᵁ V).ι.toLRSHom.toShHom).obj
          (Invertible.tensorPower X.presheaf X.ringCatSheaf.2 L (n : ℤ)))) := by
  have iLP : AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property
      (Invertible.tensorPower X.presheaf X.ringCatSheaf.2 L (n : ℤ)) :=
    Invertible.tensorPower_isInvertible X.presheaf X.ringCatSheaf.2 L (n : ℤ)
  have iQ : AlgebraicGeometry.SheafOfModules.IsInvertible
      (f ⁻¹ᵁ V).toScheme.toRingedSpace.presheaf
      (structureSheafRing (f ⁻¹ᵁ V).toScheme.toRingedSpace).property
      (Invertible.tensorPower (f ⁻¹ᵁ V).toScheme.toRingedSpace.presheaf
        (structureSheafRing (f ⁻¹ᵁ V).toScheme.toRingedSpace).property
        ((modulePullback (f ⁻¹ᵁ V).ι.toLRSHom.toShHom).obj L) (n : ℤ)) :=
    Invertible.tensorPower_isInvertible _ _ _ _
  have : Stacks.Ample.IsInvertibleModule (f ⁻¹ᵁ V).toScheme
      ((modulePullback (f ⁻¹ᵁ V).ι.toLRSHom.toShHom).obj L) :=
    Stacks.RingedSpace.algebraicGeometryIsInvertible_modulePullback _ L
  have : Stacks.Ample.IsInvertibleModule (f ⁻¹ᵁ V).toScheme
      ((modulePullback (f ⁻¹ᵁ V).ι.toLRSHom.toShHom).obj
        (Invertible.tensorPower X.presheaf X.ringCatSheaf.2 L (n : ℤ))) :=
    Stacks.RingedSpace.algebraicGeometryIsInvertible_modulePullback _ _
  exact ((Stacks.AmpleBridge.isAmple_iff_isAmple _ _).trans
      (((isAmple_iff_tensorPower_isAmple (f ⁻¹ᵁ V).toScheme
          ((modulePullback (f ⁻¹ᵁ V).ι.toLRSHom.toShHom).obj L) n hn).trans
        (isAmple_iff_of_moduleIso
          (pullbackTensorPowerIso (f ⁻¹ᵁ V).ι.toLRSHom.toShHom L n hn)).symm))).trans
    (Stacks.AmpleBridge.isAmple_iff_isAmple _ _).symm

end Relative

/-- An invertible sheaf of modules on a scheme is ample relative to a morphism if and only if any
one of its positive tensor powers is. -/
@[stacks 02NN, ega "II 4.6.9"]
theorem isRelativelyAmple_iff_tensorPower_isRelativelyAmple
    {X S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (n : ℕ) (hn : 1 ≤ n) :
    letI := Invertible.tensorPower_isInvertible X.presheaf X.ringCatSheaf.2 L (n : ℤ)
    Stacks.RelativeAmple.IsRelativelyAmple f L ↔
      Stacks.RelativeAmple.IsRelativelyAmple f
        (Invertible.tensorPower X.presheaf X.ringCatSheaf.2 L (n : ℤ)) :=
  and_congr_right' <| forall₂_congr fun V _ => isAmple_pullback_iff_tensorPower f L n V hn

end AlgebraicGeometry.Scheme.Modules

end
