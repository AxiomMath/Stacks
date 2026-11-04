/-
Copyright (c) 2026 Stacks Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.ThetaPolarization
public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.NormalizedTranslates
public import StacksFrontier.AlgebraicGeometry.Curves.FunctionFieldCategories
public import StacksCore.Tactic.StacksAttribute

/-!
# Weil's trace formula for an endomorphism of a curve

Let `C` be a smooth projective curve over an algebraically closed field `k` and `φ : C ⟶ C` an
endomorphism over `k` distinct from the identity. Let `V(φ) = (Δ · Γ_φ)` be the intersection
number of the diagonal with the graph of `φ` on `C ×_k C`, `deg φ` the degree of `φ`, and
`Tr_J(φ^*)` the trace of the endomorphism of the Jacobian `J = Pic⁰_{C/k}` induced by pullback,
read on the `ℓ`-adic Tate module of `J` for a prime `ℓ` invertible in `k`. Then
([Stacks, Tag 03U1])

`V(φ) = 1 - Tr_J(φ^*) + deg φ`.

The trace is an integer independent of `ℓ`
(`AlgebraicGeometry.CurveGraph.existsUnique_jacobianTrace`).

## Proof

Choose a big fppf site containing `C` and `Spec k`, a rational point `c₀` of `C` and the Jacobian
`J` representing `Pic⁰`. In genus zero `J` is a point and the formula reads
`V(φ) = 1 + deg φ` (`Stacks.PicardFunctor.fixedPointIntersection_eq_of_dimension_eq_zero_padic`).
In positive genus the polarization `L = 𝒪(Θ)` of the theta divisor
(`Stacks.PicardFunctor.thetaDivisor`) satisfies `(aj - x)^* L = z_x + g[c₀]` for every `x` in the
set of `k`-points with `z_x + g[c₀]` normalized, whose difference set is `J(k)`; this is the input
of `Stacks.PicardFunctor.fixedPointIntersection_eq_of_translates`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

universe u

namespace Stacks.PicardFunctor

variable {k : Type u} [Field k] (B : BigFppfSite.{u}) {X : Scheme.{u}} (hX : B.Contains X)
  (hk : B.Contains (Spec (.of k))) (f : B.obj hX ⟶ B.obj hk)
  [IsCurve k (B.inclusion.map f)] [GeometricallyIrreducible (B.inclusion.map f)]
  [Smooth (B.inclusion.map f)] [IsProper (B.inclusion.map f)]
  [IsProjectiveVariety k (B.inclusion.map f)]
  (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ B.inclusion.map f = 𝟙 _)
  [(picardFunctor B hX hk f).IsRepresentable] [IsAlgClosed k]
  (φ : X ⟶ X) (w : φ ≫ B.inclusion.map f = B.inclusion.map f)

attribute [local instance] isAbelianVariety_jacobian

include σ hσ in
/-- **Weil's formula in positive genus**, at the level of the site. -/
theorem fixedPointIntersection_eq_of_genus_pos (hdim : topologicalKrullDim X ≤ 1)
    (hg : 0 < genus (B.inclusion.map f)) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : k)) :
    ((CurveGraph.fixedPointIntersection (B.inclusion.map f) hdim φ w : ℤ) : ℤ_[ℓ]) =
      1 - CurveGraph.jacobianTateTrace (B.inclusion.map f) hdim φ w ℓ +
        (CurveGraph.curveMapDegree (B.inclusion.map f) φ w : ℤ_[ℓ]) := by
  have := isSeparated_of_isCurve B hX hk f
  have := isNoetherian_of_isCurve B hX hk f
  obtain ⟨U, hU, hUaff⟩ := Stacks.TwoAffineCech.exists_cover_isAffineOpen X hdim
  obtain ⟨x₀, ⟨z₀, hz₀, hzx₀, hN₀⟩, -⟩ := exists_mem_thetaTranslates_mul_inv B hX hk f σ hσ 1
  have := isEffectiveCartierDivisor_thetaDivisor B hX hk f σ hσ U hU hUaff x₀ z₀ hz₀ hzx₀ hN₀
  exact fixedPointIntersection_eq_of_translates B hX hk f σ hσ
    (L := Stacks.Divisors.invertibleSheaf' (thetaDivisorJ B hX hk f σ hσ U hU hUaff))
    (hL := Stacks.Divisors.isInvertible_invertibleSheaf_picard _) φ w hdim hg
    (thetaTranslates B hX hk f σ hσ) (exists_mem_thetaTranslates_mul_inv B hX hk f σ hσ)
    (fun x ⟨z, hz, hzx, hN⟩ =>
      ⟨z, hz, hzx, classQ_thetaDivisor B hX hk f σ hσ U hU hUaff x z hz hzx hN⟩) ℓ hℓ

end Stacks.PicardFunctor

namespace AlgebraicGeometry.CurveGraph

open Stacks.PicardFunctor

/-- **Weil's formula, at the level of the site, in any genus.** -/
theorem fixedPointIntersection_eq_padic {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsCurve k f] [Smooth f] [IsProper f]
    (hdim : topologicalKrullDim C ≤ 1) (φ : C ⟶ C) (w : φ ≫ f = f)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : k)) :
    ((fixedPointIntersection f hdim φ w : ℤ) : ℤ_[ℓ]) =
      1 - jacobianTateTrace f hdim φ w ℓ + (curveMapDegree f φ w : ℤ_[ℓ]) := by
  let S₀ : Set Scheme.{u} := insert C {Spec (.of k)}
  have : Small.{u} S₀ := by dsimp [S₀]; infer_instance
  obtain ⟨B, hB⟩ := BigFppfSite.exists_containing S₀
  have hX : B.Contains C := hB C (by simp [S₀])
  have hk : B.Contains (Spec (.of k)) := hB _ (by simp [S₀])
  let f' : B.obj hX ⟶ B.obj hk := ObjectProperty.homMk f
  have : IsCurve k (B.inclusion.map f') := ‹IsCurve k f›
  have : Smooth (B.inclusion.map f') := ‹Smooth f›
  have : IsProper (B.inclusion.map f') := ‹IsProper f›
  have : IsIntegral C := (‹IsCurve k f›).toIsIntegral
  have : IrreducibleSpace C := irreducibleSpace_of_isIntegral C
  have : GeometricallyIrreducible (B.inclusion.map f') :=
    geometricallyIrreducible_of_irreducibleSpace_of_isSepClosed k C f
  have : IsProjectiveVariety k (B.inclusion.map f') :=
    (isProjectiveVariety_iff_isProjectiveMorphism k f).2
      (isProjectiveMorphism_of_isProper_of_isCurve k f)
  have : Nonempty C := inferInstance
  obtain ⟨σ, hσ⟩ := Stacks.RigidifiedPicard.exists_section_of_smooth_of_isSepClosed k f
  have := Stacks.RigidifiedPicard.isRepresentable_picardFunctor_of_isSepClosed k B hX hk f'
    (isProjectiveMorphism_of_isProper_of_isCurve k f)
  by_cases hg : genus (B.inclusion.map f') = 0
  · exact fixedPointIntersection_eq_of_dimension_eq_zero_padic B hX hk f' σ hσ φ w hdim
      (by rw [abelianVarietyDimension_jacobian, hg]) ℓ hℓ
  · exact fixedPointIntersection_eq_of_genus_pos B hX hk f' σ hσ φ w hdim
      (Nat.pos_of_ne_zero hg) ℓ hℓ

/-- **Stacks Project, Tag 03U1 (Weil).** Let `C` be a smooth projective curve over an
algebraically closed field `k` and `φ : C ⟶ C` a `k`-endomorphism distinct from the identity.
Let `V(φ) = (Δ · Γ_φ)` be the intersection number of the diagonal and the graph of `φ` on
`C ×_k C`. Then `V(φ) = 1 - Tr_J(φ^*) + deg φ`, where `φ^*` is the endomorphism of the Jacobian
`J = Pic⁰_{C/k}` induced by pullback and `Tr_J(φ^*)` is its trace on the `ℓ`-adic Tate module of
`J`, for any prime `ℓ` invertible in `k` (an integer independent of `ℓ`, see
`AlgebraicGeometry.CurveGraph.existsUnique_jacobianTrace`). -/
@[stacks 03U1]
theorem fixedPointIntersection_eq {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsCurve k f] [Smooth f] [IsProper f]
    (hdim : topologicalKrullDim C ≤ 1) (φ : C ⟶ C) (w : φ ≫ f = f) (hφ : φ ≠ 𝟙 C)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : k)) :
    ((fixedPointIntersection f hdim φ w : ℤ) : ℤ_[ℓ]) =
      1 - jacobianTateTrace f hdim φ w ℓ + (curveMapDegree f φ w : ℤ_[ℓ]) :=
  fixedPointIntersection_eq_padic f hdim φ w ℓ hℓ

/-- **The trace of `φ^*` on the Tate module of the Jacobian is an integer independent of `ℓ`**:
`t = 1 + deg φ - V(φ)` is the unique integer whose image in `ℤ_ℓ` is the trace for every prime
`ℓ` invertible in `k`, so that `V(φ) = 1 - t + deg φ` in `ℤ`. -/
theorem existsUnique_jacobianTrace {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsCurve k f] [Smooth f] [IsProper f]
    (hdim : topologicalKrullDim C ≤ 1) (φ : C ⟶ C) (w : φ ≫ f = f) :
    ∃! t : ℤ, (∀ (ℓ : ℕ) [Fact ℓ.Prime], IsUnit (ℓ : k) →
        (t : ℤ_[ℓ]) = jacobianTateTrace f hdim φ w ℓ) ∧
      fixedPointIntersection f hdim φ w = 1 - t + curveMapDegree f φ w := by
  refine ⟨1 + curveMapDegree f φ w - fixedPointIntersection f hdim φ w, ⟨fun ℓ _ hℓ => ?_, by ring⟩,
    fun t ⟨_, ht⟩ => by rw [ht]; ring⟩
  have h := fixedPointIntersection_eq_padic f hdim φ w ℓ hℓ
  push_cast
  rw [h]
  ring

end AlgebraicGeometry.CurveGraph

end
