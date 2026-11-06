module

public import Mathlib.Algebra.Module.LocalizedModule.AtPrime
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Finiteness.Small
public import StacksFrontier.RingTheory.Depth.Defs.Defs
public import StacksFrontier.RingTheory.Depth.FlatLocalHom
public import StacksFrontier.RingTheory.AdicCompletion.Flat
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.LocalRing

/-!
# Depth after completion at a prime

Let `A` be a Noetherian ring, `I` an ideal, and `M` a finite `A`-module. If a
prime `p'` of the `I`-adic completion of `A` lies over `p`, then the depth of the
completed module at `p'` is the sum of the depth of `M` at `p` and the depth of
the fibre of the localized completion map.

## Main results

* `AlgebraicGeometry.depth_localized_adicCompletion`: depth is additive under
  completion and localization at a prime.

## Implementation notes

Both completions and both localizations are the canonical Mathlib
constructions. The condition that `p'` lies over `p` pins down the map between
the two local rings, and the fibre is the quotient by the extension of `p`.

## References

* [Stacks Project, Tag 0EHW](https://stacks.math.columbia.edu/tag/0EHW)
-/

@[expose] public section

noncomputable section

open IsLocalRing
open scoped TensorProduct

namespace AlgebraicGeometry

universe u v

/-- Depth of a finite module after adic completion and localization at a prime
is the depth before completion plus the depth of the local fibre. -/
theorem depth_localized_adicCompletion
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (p : Ideal A) [p.IsPrime]
    (p' : Ideal (AdicCompletion I A)) [p'.IsPrime] [p'.LiesOver p] :
    Module.depth (Localization.AtPrime p')
        (maximalIdeal (Localization.AtPrime p'))
        (LocalizedModule p'.primeCompl (AdicCompletion I M)) =
      Module.depth (Localization.AtPrime p)
          (maximalIdeal (Localization.AtPrime p))
          (LocalizedModule p.primeCompl M) +
        Module.depth (Localization.AtPrime p')
          (maximalIdeal (Localization.AtPrime p'))
          ((Localization.AtPrime p') ⧸
            p.map (algebraMap A (Localization.AtPrime p'))) := by
  let := Localization.AtPrime.algebraOfLiesOver p p'
  let B := AdicCompletion I A
  let R := Localization.AtPrime p
  let S := Localization.AtPrime p'
  let N := LocalizedModule p.primeCompl M
  let N' := LocalizedModule p'.primeCompl (AdicCompletion I M)
  have : Module.Flat A B := AdicCompletion.flat_of_isNoetherian I
  have : Module.Flat A S := Module.Flat.trans A B S
  have : Module.Flat R S :=
    (Module.flat_iff_of_isLocalization R p.primeCompl S).mpr inferInstance
  have hcompletion : IsBaseChange B (AdicCompletion.of I M) := by
    let : Small.{u} M := Module.Finite.small A M
    let M₀ := Shrink.{u} M
    let eM : M₀ ≃ₗ[A] M := Shrink.linearEquiv A M
    have hsmall : IsBaseChange B (AdicCompletion.of I M₀) :=
      IsBaseChange.of_equiv (AdicCompletion.ofTensorProductEquivOfFiniteNoetherian I M₀)
        fun x ↦ by
          change (AdicCompletion.ofTensorProduct I M₀) (1 ⊗ₜ[A] x) = _
          rw [AdicCompletion.ofTensorProduct_tmul, one_smul]
    exact (IsBaseChange.iff_of_equiv_comm eM (AdicCompletion.congr I eM)
      (LinearMap.ext fun x ↦ (AdicCompletion.map_of I eM.toLinearMap x).symm)).mp hsmall
  have hA : IsBaseChange S
      (((LocalizedModule.mkLinearMap p'.primeCompl (AdicCompletion I M)).restrictScalars A).comp
        (AdicCompletion.of I M)) :=
    hcompletion.comp (IsLocalizedModule.isBaseChange p'.primeCompl S _)
  have hR : IsBaseChange R (LocalizedModule.mkLinearMap p.primeCompl M) :=
    IsLocalizedModule.isBaseChange p.primeCompl R _
  let e : S ⊗[R] N ≃ₗ[S] N' :=
    (hR.equiv.symm.baseChange R S) ≪≫ₗ
      TensorProduct.AlgebraTensorModule.cancelBaseChange A R S S M ≪≫ₗ hA.equiv
  have h' : Module.depth S (maximalIdeal S) N' =
      Module.depth R (maximalIdeal R) N +
        Module.depth S (maximalIdeal S)
          (S ⧸ ((maximalIdeal R).map (algebraMap R S) • (⊤ : Submodule S S))) := by
    rw [← Module.depth_eq_depth_of_linearEquiv (maximalIdeal S) e]
    exact Module.depth_tensorProduct_of_flat (R := R) (S := S) (M := N) (N := S)
  have hid : (maximalIdeal R).map (algebraMap R S) =
      p.map (algebraMap A S) := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p R, Ideal.map_map,
      ← IsScalarTower.algebraMap_eq]
  rwa [hid, Ideal.smul_eq_mul, Ideal.mul_top] at h'

end AlgebraicGeometry
