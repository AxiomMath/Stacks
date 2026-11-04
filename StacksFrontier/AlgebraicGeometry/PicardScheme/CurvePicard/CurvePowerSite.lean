/-
Copyright (c) 2026 Stacks Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.SeesawPoints
public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.Representability
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.CurvePower
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.CurvePowerRestriction

/-!
# The powers of a curve as test schemes of the big fppf site

Let `X` be a smooth projective curve over a field `k`, in a big fppf site `B`. The fibre powers
`C^m` of `C = X` over `k` (`Stacks.CurvePower.power`) are of finite type over `k`, hence objects
of the site (`Stacks.PicardFunctor.powerObj`), and the base change `X ×_k C^m` of the Picard
functor at `C^m` is `C^(m+1)` on the nose. So classes on `C^(m+1)` are points of the Picard functor
over `C^m`, with classifying maps `C^m ⟶ J`, and the seesaw principle at rational points
(`Stacks.PicardFunctor.exists_eq_schemePullbackClass_of_points`) applies to them.

## Main definitions

* `Stacks.PicardFunctor.powerObj`: `C^m` as a test scheme.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite MonoidalCategory

universe u

namespace Stacks.PicardFunctor

variable {k : Type u} [Field k] (B : BigFppfSite.{u}) {X : Scheme.{u}} (hX : B.Contains X)
  (hk : B.Contains (Spec (.of k))) (f : B.obj hX ⟶ B.obj hk) [IsProper (B.inclusion.map f)]

/-- The fibre power `C^m` of the curve over `k` is an object of the big fppf site. -/
theorem contains_power (m : ℕ) :
    B.Contains (Stacks.CurvePower.power (curveOver B hX hk f) m).left :=
  have : IsProper (curveOver B hX hk f).hom := inferInstanceAs (IsProper (B.inclusion.map f))
  have := Stacks.CurvePower.isProper_power_hom (C := curveOver B hX hk f) m
  contains_of_isProper B hk (Stacks.CurvePower.power (curveOver B hX hk f) m).hom

/-- **The power `C^m` of the curve as a test scheme of the big fppf site.** -/
abbrev powerObj (m : ℕ) : BigFppfOver B (Spec (.of k)) hk :=
  Over.mk (ObjectProperty.homMk (X := B.obj (contains_power B hX hk f m)) (Y := B.obj hk)
    (Stacks.CurvePower.power (curveOver B hX hk f) m).hom)

/-- The underlying scheme over `Spec k` of `powerObj B hX hk f m` is the power `C^m`. -/
theorem post_powerObj (m : ℕ) :
    (Over.post (X := B.obj hk) B.inclusion).obj (powerObj B hX hk f m) =
      Stacks.CurvePower.power (curveOver B hX hk f) m :=
  rfl

/-- The Picard functor at `C^m` is the Picard group of `C^(m+1) = X ×_k C^m`. -/
theorem picardAt_powerObj (m : ℕ) :
    picardAt B hX hk f (powerObj B hX hk f m) =
      Stacks.Picard.ofScheme (Stacks.CurvePower.power (curveOver B hX hk f) (m + 1)).left :=
  rfl

/-- **The base change of a morphism of powers** `g : C^n ⟶ C^m` is the morphism
`𝟙 × g : C^(n+1) ⟶ C^(m+1)`. -/
theorem baseChangeMap_powerObj {n m : ℕ} (g : powerObj B hX hk f n ⟶ powerObj B hX hk f m) :
    baseChangeMap B hX hk f g =
      (CartesianMonoidalCategory.lift (CartesianMonoidalCategory.fst _ _)
        (CartesianMonoidalCategory.snd _ _ ≫ (Over.post (X := B.obj hk) B.inclusion).map g) :
          Stacks.CurvePower.power (curveOver B hX hk f) (n + 1) ⟶
            Stacks.CurvePower.power (curveOver B hX hk f) (m + 1)).left := by
  rfl

end Stacks.PicardFunctor
