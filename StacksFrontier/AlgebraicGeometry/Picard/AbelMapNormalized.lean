module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.DegreeComponents

/-!
# Normalized Picard classes of a base change

Let `X ⟶ S` have a section `σ` and satisfy the hypothesis of [Stacks, Tag 0B9N]. A Picard class
`x` of a base change `X_T` is *normalized* when `σ_T^* x = 0`. Every class has the normalized
representative `x - p^* σ_T^* x` with the same image in the Picard functor, and two normalized
classes with the same image in the Picard functor are equal ([Stacks, Tag 0B9N]).

This is used in the proof of the smoothness of the morphism `γ_d` of [Stacks, Tag 0BA0].

## Main results

* `Stacks.AbelMap.normalize`, `Stacks.AbelMap.schemePullbackClass_baseChangeSection_normalize`,
  `Stacks.AbelMap.toPicardFunctorHom_normalize`.
* `Stacks.AbelMap.eq_of_toPicardFunctorHom_eq_of_normalized`.

## References

* [Stacks Project, Tag 0B9N](https://stacks.math.columbia.edu/tag/0B9N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.PicardFunctor

universe u

namespace Stacks.AbelMap

variable (B : BigFppfSite.{u}) {X S : Scheme.{u}} (hX : B.Contains X) (hS : B.Contains S)
  (f : B.obj hX ⟶ B.obj hS) (σ : S ⟶ X) (hσ : σ ≫ B.inclusion.map f = 𝟙 S)
  (hOiso : ∀ U : BigFppfOver B S hS, IsIso (baseChangeProj B hX hS f U).toLRSHom.toHom.c)

/-- The normalized representative `x - p^* σ_T^* x` of a Picard class of `X_T`. -/
def normalize (T : BigFppfOver B S hS) (x : picardAt B hX hS f T) : picardAt B hX hS f T :=
  x - Stacks.Picard.schemePullbackClass (baseChangeProj B hX hS f T)
    (Stacks.Picard.schemePullbackClass (baseChangeSection B hX hS f σ hσ T) x)

/-- The normalized representative is normalized. -/
theorem schemePullbackClass_baseChangeSection_normalize (T : BigFppfOver B S hS)
    (x : picardAt B hX hS f T) :
    Stacks.Picard.schemePullbackClass (baseChangeSection B hX hS f σ hσ T)
      (normalize B hX hS f σ hσ T x) = 0 := by
  rw [normalize]
  change Stacks.Picard.schemePullbackClassHom (baseChangeSection B hX hS f σ hσ T) (x - _) = 0
  rw [map_sub]
  change Stacks.Picard.schemePullbackClass (baseChangeSection B hX hS f σ hσ T) x -
    Stacks.Picard.schemePullbackClass (baseChangeSection B hX hS f σ hσ T) _ = 0
  rw [schemePullbackClass_baseChangeSection_baseChangeProj B hX hS f σ hσ T, sub_self]

include hOiso in
/-- The normalized representative has the same image in the Picard functor. -/
theorem toPicardFunctorHom_normalize (T : BigFppfOver B S hS) (x : picardAt B hX hS f T) :
    toPicardFunctorHom B hX hS f T (normalize B hX hS f σ hσ T x) =
      toPicardFunctorHom B hX hS f T x := by
  rw [normalize, map_sub, sub_eq_self]
  exact (exact_schemePullbackClass_baseChangeProj_toPicardFunctorHom B hX hS f σ hσ hOiso T
    _).2 ⟨_, rfl⟩

include hOiso in
/-- **Two normalized Picard classes with the same image in the Picard functor are equal**
([Stacks, Tag 0B9N]). -/
theorem eq_of_toPicardFunctorHom_eq_of_normalized (T : BigFppfOver B S hS)
    {x x' : picardAt B hX hS f T}
    (h : toPicardFunctorHom B hX hS f T x = toPicardFunctorHom B hX hS f T x')
    (hx : Stacks.Picard.schemePullbackClass (baseChangeSection B hX hS f σ hσ T) x = 0)
    (hx' : Stacks.Picard.schemePullbackClass (baseChangeSection B hX hS f σ hσ T) x' = 0) :
    x = x' := by
  obtain ⟨y, rfl⟩ := exists_eq_add_of_toPicardFunctorHom_eq B hX hS f σ hσ hOiso T h
  rw [Stacks.Picard.schemePullbackClass_add, hx, zero_add,
    schemePullbackClass_baseChangeSection_baseChangeProj B hX hS f σ hσ T] at hx'
  rw [hx']
  change x = x + Stacks.Picard.schemePullbackClassHom (baseChangeProj B hX hS f T) 0
  rw [map_zero, add_zero]

end Stacks.AbelMap

end
