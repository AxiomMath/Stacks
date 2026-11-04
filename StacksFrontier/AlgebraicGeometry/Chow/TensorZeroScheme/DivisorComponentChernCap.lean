module

public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.FlatPullbackRationallyCompatible
public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.ChernComponentAmbient
public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.ChowDevissage
public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.SupComapSubscheme

/-!
# `i^*[W] = c₁(ℒ₁|_D) ∩ [W] + c₁(ℒ₂|_D) ∩ [W]` for a component of the divisor

In the situation of [Stacks, Tag 0F97] let `W ⊆ Y` be an integral closed subscheme of
δ-dimension `k+1` contained in the divisor `D = Z(s)` of the section `s` of `ℒ₁ ⊗ ℒ₂`. The case
`W ⊆ D` of [Stacks, Tag 0F98] opens with the step

  "`i^*[W] = c₁(ℒ₁) ∩ [W] + c₁(ℒ₂) ∩ [W]` in `CH_{k-1}(D)` by our definition of Gysin
  homomorphisms and the additivity of Lemma 42.25.2"

which this file proves at cycle level: the two cap products are read on `D`, and the two sides
differ by a cycle rationally equivalent to zero witnessed inside the preimage of `W`.

## Main results

* `gysinRuleZeroIdeal_cycle_sub_firstChernComponentCycle_isRationallyEquivalentToZeroWithin`:
  **the step above**: the Gysin cycle of `i` at `W` and the sum of the component cycles of
  `ℒ₁|_D` and `ℒ₂|_D` at the inverse image `W|_D` differ by a cycle rationally equivalent to zero
  on `D`, witnessed inside the preimage of `W`.

## References

* [Stacks Project, Tag 0F97](https://stacks.math.columbia.edu/tag/0F97)
* [Stacks Project, Tag 0F98](https://stacks.math.columbia.edu/tag/0F98)
* [Stacks Project, Tag 02T8](https://stacks.math.columbia.edu/tag/02T8)
* [Stacks Project, Tag 02SP](https://stacks.math.columbia.edu/tag/02SP)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow.TensorZeroScheme

variable (C : Stacks.Chow.ChowSituation.{u}) (Y : Scheme.{u}) (L₁ L₂ : Y.Modules)
  [h₁ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₁]
  [h₂ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₂]
  (s : Γ(Stacks.Divisors.tensorModules L₁ L₂, ⊤)) (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  (k : ℤ) (W : Y.IdealSheafData)

include h₁ h₂ in
/-- **The Gysin cycle of `i : D ⟶ Y` at a component of `D`, as a sum of two cap products on
`D`.** For an integral closed subscheme `W ⊆ Y` of δ-dimension `k+1` contained in `D = Z(s)`, the
Gysin cycle of the rule of `i` at `W` differs from the sum of the first Chern component cycles of
`ℒ₁|_D` and of `ℒ₂|_D` at the inverse image `W|_D` by a cycle rationally equivalent to zero on `D`
witnessed inside the preimage of `W`. -/
theorem gysinRuleZeroIdeal_cycle_sub_firstChernComponentCycle_isRationallyEquivalentToZeroWithin
    (hW : zeroIdeal Y L₁ L₂ s ≤ W) (hWint : IsIntegral W.subscheme)
    (hDim : Stacks.Chow.schemeDeltaDimension C (W.subschemeι ≫ sY) = ((k + 1 : ℤ) : EInt))
    (hWDint : IsIntegral (W.comap (zeroIdeal Y L₁ L₂ s).subschemeι).subscheme)
    (hWDdim : Stacks.Chow.schemeDeltaDimension C
      ((W.comap (zeroIdeal Y L₁ L₂ s).subschemeι).subschemeι ≫
        (zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY) = ((k + 1 : ℤ) : EInt)) :
    Stacks.Chow.IsRationallyEquivalentToZeroWithin C
      ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY) k
      ((gysinRuleZeroIdeal C Y L₁ L₂ s sY k).cycle W hWint hDim -
        (Stacks.Chow.firstChernComponentCycle C ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY) k
            (Stacks.Chow.firstChernComponentCycleRule C
              ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY) k
              ((Scheme.Modules.pullback (zeroIdeal Y L₁ L₂ s).subschemeι).obj L₁))
            (W.comap (zeroIdeal Y L₁ L₂ s).subschemeι) hWDint hWDdim +
          Stacks.Chow.firstChernComponentCycle C ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY) k
            (Stacks.Chow.firstChernComponentCycleRule C
              ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY) k
              ((Scheme.Modules.pullback (zeroIdeal Y L₁ L₂ s).subschemeι).obj L₂))
            (W.comap (zeroIdeal Y L₁ L₂ s).subschemeι) hWDint hWDdim))
      ((zeroIdeal Y L₁ L₂ s).subschemeι.base ⁻¹' (W.support : Set Y)) := by
  have hcar : ((W.comap (zeroIdeal Y L₁ L₂ s).subschemeι).support :
        Set (zeroIdeal Y L₁ L₂ s).subscheme) =
      (zeroIdeal Y L₁ L₂ s).subschemeι.base ⁻¹' (W.support : Set Y) := by
    rw [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage]
  have himg : (W.comap (zeroIdeal Y L₁ L₂ s).subschemeι).map
      (zeroIdeal Y L₁ L₂ s).subschemeι = W :=
    (Scheme.IdealSheafData.map_comap_subschemeι (zeroIdeal Y L₁ L₂ s) W).trans
      (sup_eq_right.2 hW)
  have hA : Stacks.Chow.IsRationallyEquivalentToZeroWithin C
      ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY) k
      ((gysinRuleZeroIdeal C Y L₁ L₂ s sY k).cycle W hWint hDim -
        Stacks.Chow.properPushforward C (W.subschemeι ≫ sY)
          ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY)
          (Scheme.IdealSheafData.inclusion hW) (by simp) k
          (Stacks.Chow.firstChernComponentCycleRule C sY k
            (Stacks.Divisors.tensorModules L₁ L₂) W hWint hDim))
      ((zeroIdeal Y L₁ L₂ s).subschemeι.base ⁻¹' (W.support : Set Y)) :=
    Stacks.Chow.gysinComponentCycle_sub_properPushforward_isRationallyEquivalentToZeroWithin_of_le
      C sY k (Stacks.Divisors.tensorModules L₁ L₂) s
      (Stacks.Chow.firstChernComponentClass C sY k (Stacks.Divisors.tensorModules L₁ L₂))
      W hWint hDim hW _ (Stacks.Chow.firstChernComponentClass_eq_mk _ _ _ _ _ _ _)
  have hB : Stacks.Chow.IsRationallyEquivalentToZeroWithin C
      ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY) k
      (Stacks.Chow.properPushforward C (W.subschemeι ≫ sY)
          ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY)
          (Scheme.IdealSheafData.inclusion hW) (by simp) k
          (Stacks.Chow.firstChernComponentCycleRule C sY k
            (Stacks.Divisors.tensorModules L₁ L₂) W hWint hDim) -
        (Stacks.Chow.properPushforward C (W.subschemeι ≫ sY)
            ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY)
            (Scheme.IdealSheafData.inclusion hW) (by simp) k
            (Stacks.Chow.firstChernComponentCycleRule C sY k L₁ W hWint hDim) +
          Stacks.Chow.properPushforward C (W.subschemeι ≫ sY)
            ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY)
            (Scheme.IdealSheafData.inclusion hW) (by simp) k
            (Stacks.Chow.firstChernComponentCycleRule C sY k L₂ W hWint hDim)))
      ((zeroIdeal Y L₁ L₂ s).subschemeι.base ⁻¹' (W.support : Set Y)) := by
    have h := firstChernComponentCycleRule_tensorObj_sub_isRationallyEquivalentToZeroWithin_of_le
      C sY k (Stacks.Divisors.tensorModules L₁ L₂) s L₁ L₂ W hWint hDim hW
    rwa [Stacks.Chow.properPushforward_add] at h
  have hC₁ := (firstChernComponentCycle_sub_properPushforward_isRationallyEquivalentToZeroWithin
    C ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY) sY (zeroIdeal Y L₁ L₂ s).subschemeι rfl k L₁
    (W.comap (zeroIdeal Y L₁ L₂ s).subschemeι) hWDint hWDdim W himg
    (Scheme.IdealSheafData.inclusion hW)
    (Scheme.IdealSheafData.inclusion_subschemeι hW) hWint hDim).mono (le_of_eq hcar)
  have hC₂ := (firstChernComponentCycle_sub_properPushforward_isRationallyEquivalentToZeroWithin
    C ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY) sY (zeroIdeal Y L₁ L₂ s).subschemeι rfl k L₂
    (W.comap (zeroIdeal Y L₁ L₂ s).subschemeι) hWDint hWDdim W himg
    (Scheme.IdealSheafData.inclusion hW)
    (Scheme.IdealSheafData.inclusion_subschemeι hW) hWint hDim).mono (le_of_eq hcar)
  have hsum := Stacks.Chow.isRationallyEquivalentToZeroWithin_add C
    ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY) k
    (Stacks.Chow.isRationallyEquivalentToZeroWithin_add C
      ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY) k
      (Stacks.Chow.isRationallyEquivalentToZeroWithin_add C
        ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY) k hA hB)
      (Stacks.Chow.isRationallyEquivalentToZeroWithin_neg C
        ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY) k hC₁))
    (Stacks.Chow.isRationallyEquivalentToZeroWithin_neg C
      ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY) k hC₂)
  convert hsum using 1
  abel

end Stacks.Chow.TensorZeroScheme

end
