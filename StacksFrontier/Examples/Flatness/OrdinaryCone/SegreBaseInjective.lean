module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Tactic.ComputeDegree
public import StacksFrontier.Examples.Flatness.OrdinaryCone.Segre

/-!
# The map from the polynomial ring to the Segre product is injective

Over a field `k`, the map `k[X₀, X₁, X₂] → Γ` of `Stacks.Examples.OrdinaryCone.segreBase`,
sending `X₀ ↦ xs`, `X₁ ↦ yt` and `X₂ ↦ xt + ys`, is injective. Let `L` be an algebraic closure of
the fraction field of `k[X₀, X₁, X₂]`. Choose a root `t ∈ L` of `X₀ T² - X₂ T + X₁`, put
`y = X₂ - X₀ t` and choose a root `z ∈ L` of `T³ + (y² + X₀ y) T + X₀³`. Sending
`x ↦ X₀, y ↦ y, z ↦ z, s ↦ 1, t ↦ t` defines a map `G[s, t] → L` whose composite with
`k[X₀, X₁, X₂] → Γ ⊆ G[s, t]` sends `X₀ ↦ X₀`, `X₁ ↦ yt = X₂ t - X₀ t² = X₁` and
`X₂ ↦ X₀ t + y = X₂`: it is the inclusion of `k[X₀, X₁, X₂]` into `L`, which is injective.

## Main results

* `Stacks.Examples.OrdinaryCone.segreBase_injective`: `segreBase k` is injective.
* `Stacks.Examples.OrdinaryCone.segre.faithfulSMul_base`: the corresponding `FaithfulSMul`
  instance.
-/

@[expose] public section

namespace Stacks.Examples.OrdinaryCone

open MvPolynomial

variable (k : Type*) [Field k]

/-- Over a field, the map `k[X₀, X₁, X₂] → Γ`, `X₀ ↦ xs`, `X₁ ↦ yt`, `X₂ ↦ xt + ys`, is
injective. -/
theorem segreBase_injective : Function.Injective (segreBase k) := by
  set P := MvPolynomial (Fin 3) k
  set L := AlgebraicClosure (FractionRing P)
  set ι : P →+* L := (algebraMap (FractionRing P) L).comp (algebraMap P (FractionRing P))
  have hι : Function.Injective ι :=
    (algebraMap (FractionRing P) L).injective.comp (IsFractionRing.injective P (FractionRing P))
  set a := ι (X 0)
  set b := ι (X 1)
  set c := ι (X 2)
  have ha : a ≠ 0 := (map_ne_zero_iff ι hι).mpr (X_ne_zero 0)
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_root
    (Polynomial.C a * Polynomial.X ^ 2 - Polynomial.C c * Polynomial.X + Polynomial.C b) (by
      rw [show Polynomial.C a * Polynomial.X ^ 2 - Polynomial.C c * Polynomial.X +
        Polynomial.C b = Polynomial.C a * Polynomial.X ^ 2 + Polynomial.C (-c) *
          Polynomial.X + Polynomial.C b by simp [sub_eq_add_neg],
        Polynomial.degree_quadratic ha]
      decide)
  have ht' : a * t ^ 2 - c * t + b = 0 := by simpa using ht
  set y := c - a * t
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root
    (Polynomial.X ^ 3 + Polynomial.C (y ^ 2 + a * y) * Polynomial.X + Polynomial.C (a ^ 3)) (by
      have : (Polynomial.X ^ 3 + Polynomial.C (y ^ 2 + a * y) * Polynomial.X +
          Polynomial.C (a ^ 3)).degree = 3 := by compute_degree!
      rw [this]
      decide)
  have hz' : z ^ 3 + (y ^ 2 + a * y) * z + a ^ 3 = 0 := by simpa using hz
  let g : Cone k →ₐ[k] L := Cone.lift k a y z hz'
  have hx : g (Ideal.Quotient.mk _ (X 0)) = a := Cone.lift_x a y z hz'
  have hy : g (Ideal.Quotient.mk _ (X 1)) = y := Cone.lift_y a y z hz'
  let ψ : segre k →+* L := (eval₂Hom g.toRingHom ![1, t]).comp (segre k).val.toRingHom
  have hψ : ψ.comp (segreBase k).toRingHom = ι := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) fun i => ?_
    · change ψ (segreBase k (algebraMap k P r)) = ι (algebraMap k P r)
      rw [AlgHom.commutes, show ι (algebraMap k P r) = algebraMap k L r by
        simp only [ι, RingHom.comp_apply, ← IsScalarTower.algebraMap_apply]]
      change eval₂ g.toRingHom ![1, t] (algebraMap k (MvPolynomial (Fin 2) (Cone k)) r) = _
      rw [MvPolynomial.algebraMap_apply, eval₂_C]
      exact g.commutes r
    have hseg (i : Fin 3) (j : Fin 2) : ψ (segreElem k i j) =
        g (Ideal.Quotient.mk _ (X i)) * ![1, t] j := by
      simp [ψ, segreGen]
    fin_cases i
    · change ψ (segreBase k (X 0)) = ι (X 0)
      rw [segreBase_X_zero, hseg]
      simp only [Fin.isValue, Matrix.cons_val_zero, hx, mul_one]
      rfl
    · change ψ (segreBase k (X 1)) = ι (X 1)
      rw [segreBase_X_one, hseg]
      simp only [Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero, hy]
      change (c - a * t) * t = b
      linear_combination (-1 : L) * ht'
    · change ψ (segreBase k (X 2)) = ι (X 2)
      rw [segreBase_X_two, map_add, hseg, hseg]
      simp only [Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero, hx, hy]
      change a * t + (c - a * t) * 1 = c
      ring
  rw [← hψ, RingHom.coe_comp] at hι
  exact hι.of_comp

/-- Over a field, `k[X₀, X₁, X₂]` acts faithfully on the Segre product. -/
instance segre.faithfulSMul_base : FaithfulSMul (MvPolynomial (Fin 3) k) (segre k) :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr (segreBase_injective k)

end Stacks.Examples.OrdinaryCone
