module

public import StacksFrontier.NumberTheory.Adeles.GeneralLinear.AlgebraicEigenvaluesDegree

/-!
# Base change and twists of Hecke eigenforms on `GL_n`

Let `K` be a function field over a finite field `k`. This file collects three operations on
functions on `GL_n(A)`.

* **Base change**: composing with an injective homomorphism `φ : Λ → Λ'` preserves unramified cusp
  forms, and Hecke eigenforms with eigenvalues `t` become eigenforms with eigenvalues `φ ∘ t`.
* **Twist by the degree**: for `c ∈ Λ^×`, `x ↦ c ^ {deg x} f(x)` (with `deg x` the degree of the
  divisor of `det x`) is again an eigenform, with eigenvalues `t_{v,i} c ^ {-i deg v}`.
* **The operator `T_{v,n}`**: on a left `GL_n(O)`-invariant function it is translation by the
  central element `ϖ_v⁻¹`, `T_{v,n} F (x) = F (ϖ_v⁻¹ x)`; the unique lattice `L'` with
  `m_v L_v ⊆ L'_v ⊆ L_v` of index `q_v ^ n` is `m_v L_v`.

## Main results

* `Stacks.Adeles.IsUnramifiedCuspFormGL.comp`,
  `Stacks.Adeles.IsHeckeEigenformGL.comp` — base change.
* `Stacks.Adeles.IsHeckeEigenformGL.twistGL` — twist by the degree.
* `Stacks.Adeles.GeneralLinear.heckeOperatorGL_top` — `T_{v,n}` is translation by `ϖ_v⁻¹`.
-/

@[expose] public noncomputable section

open Matrix

universe u w

namespace Stacks.Adeles.GeneralLinear

open Stacks.Adeles.GlobalFunctionField Stacks.Drinfeld.Lattice

section BaseChange

variable {K : Type u} [Field K] {n : ℕ}

/-- **Base change of cusp forms**: composing an unramified cusp form with an injective additive
map gives an unramified cusp form. -/
public theorem _root_.Stacks.Adeles.IsUnramifiedCuspFormGL.comp {Λ Λ' : Type*} [AddCommMonoid Λ]
    [AddCommMonoid Λ']
    {f : GL (Fin n) (AdeleRing K) → Λ} (hf : IsUnramifiedCuspFormGL n f) (φ : Λ →+ Λ')
    (hφ : Function.Injective φ) : IsUnramifiedCuspFormGL n (φ ∘ f) where
  right_invariant x γ := by simp only [Function.comp_apply, hf.right_invariant]
  left_invariant x u := by simp only [Function.comp_apply, hf.left_invariant]
  vanishing_constant_term r hr hrn x U hU hinv s hs := by
    have := hf.vanishing_constant_term r hr hrn x U hU (fun z y hy => hφ (hinv z y hy)) s hs
    simp only [Function.comp_apply, ← map_sum, this, map_zero]

/-- The Hecke operators commute with an injective additive map. -/
public theorem heckeOperatorGL_comp {Λ Λ' : Type*} [AddCommMonoid Λ] [AddCommMonoid Λ']
    (φ : Λ →+ Λ') (hφ : Function.Injective φ) (v : Place K) (i : ℕ)
    (f : GL (Fin n) (AdeleRing K) → Λ) (x : GL (Fin n) (AdeleRing K)) :
    heckeOperatorGL v i (φ ∘ f) x = φ (heckeOperatorGL v i f x) :=
  (AddMonoidHom.map_finsum_of_injective φ hφ _).symm

/-- **Base change of eigenforms**: composing a Hecke eigenform with eigenvalues `t` with an
injective ring homomorphism `φ` gives an eigenform with eigenvalues `φ ∘ t`. -/
public theorem _root_.Stacks.Adeles.IsHeckeEigenformGL.comp {Λ Λ' : Type*} [CommRing Λ]
    [CommRing Λ']
    {f : GL (Fin n) (AdeleRing K) → Λ} {t : Place K → ℕ → Λ} (hf : IsHeckeEigenformGL f t)
    (φ : Λ →+* Λ') (hφ : Function.Injective φ) :
    IsHeckeEigenformGL (φ ∘ f) (fun v i => φ (t v i)) where
  ne_zero := by
    intro h
    apply hf.ne_zero
    funext x
    apply hφ
    rw [Pi.zero_apply, map_zero]
    exact congrFun h x
  hecke v i hi hin x := by
    have := Stacks.Adeles.GeneralLinear.heckeOperatorGL_comp φ.toAddMonoidHom hφ v i f x
    change heckeOperatorGL v i (φ ∘ f) x = _ at this
    rw [this]
    change φ (heckeOperatorGL v i f x) = _
    rw [hf.hecke v i hi hin x, map_mul]
    rfl

end BaseChange

variable (k : Type u) [Field k] [Finite k] {K : Type u} [Field K] [Algebra k K]
  [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K] {n : ℕ}

section Twist

variable {Λ : Type w} [Field Λ]

variable (K) in
/-- The twist `x ↦ c ^ {deg x} f(x)` of `f` by the degree of `det x`. -/
public def twistGL (c : Λ) (f : GL (Fin n) (AdeleRing K) → Λ) (x : GL (Fin n) (AdeleRing K)) :
    Λ :=
  c ^ degGL k K x * f x

/-- The twist of a left `GL_n(O)`-invariant function is left `GL_n(O)`-invariant. -/
public theorem twistGL_mapO_mul (c : Λ) {f : GL (Fin n) (AdeleRing K) → Λ}
    (hf : IsUnramifiedCuspFormGL n f) (κ : GL (Fin n) (integralAdeles K))
    (x : GL (Fin n) (AdeleRing K)) :
    twistGL k K c f (mapO K n κ * x) = twistGL k K c f x := by
  rw [twistGL, twistGL, degGL_mul, degGL_mapO, zero_add, hf.left_invariant]

/-- The twist of a right `GL_n(K)`-invariant function is right `GL_n(K)`-invariant. -/
public theorem twistGL_mul_mapK (c : Λ) {f : GL (Fin n) (AdeleRing K) → Λ}
    (hf : IsUnramifiedCuspFormGL n f) (x : GL (Fin n) (AdeleRing K))
    (γ : GL (Fin n) (principalAdeles K)) :
    twistGL k K c f (x * mapK K n γ) = twistGL k K c f x := by
  rw [twistGL, twistGL, degGL_mul, degGL_mapK, add_zero, hf.right_invariant]

/-- The Hecke operator `T_{v,i}` on a twist: the degree is shifted by `-i deg v` on every lattice
summed over. -/
public theorem heckeOperatorGL_twistGL (c : Λ) (f : GL (Fin n) (AdeleRing K) → Λ) (v : Place K)
    (i : ℕ) (x : GL (Fin n) (AdeleRing K)) :
    heckeOperatorGL v i (twistGL k K c f) x =
      c ^ (degGL k K x - (i : ℤ) * (Stacks.Drinfeld.placeDegree k K v : ℤ)) *
        heckeOperatorGL v i f x := by
  rw [heckeOperatorGL, heckeOperatorGL, mul_finsum]
  refine finsum_congr fun L' => ?_
  rw [twistGL, degGL_latticeRep_inv k x L'.2]

/-- **Twist of an eigenform**: for `c ≠ 0`, the twist `x ↦ c ^ {deg x} f(x)` of an eigenform with
eigenvalues `t` is an eigenform with eigenvalues `t_{v,i} c ^ {-i deg v}`. -/
public theorem _root_.Stacks.Adeles.IsHeckeEigenformGL.twistGL {c : Λ} (hc : c ≠ 0)
    {f : GL (Fin n) (AdeleRing K) → Λ} {t : Place K → ℕ → Λ} (hf : IsHeckeEigenformGL f t) :
    IsHeckeEigenformGL (twistGL k K c f)
      (fun v i => t v i * c ^ (-((i : ℤ) * (Stacks.Drinfeld.placeDegree k K v : ℤ)))) where
  ne_zero := by
    intro h
    apply hf.ne_zero
    funext x
    have := congrFun h x
    simpa only [Stacks.Adeles.GeneralLinear.twistGL, Pi.zero_apply, mul_eq_zero,
      zpow_ne_zero _ hc, false_or] using this
  hecke v i hi hin x := by
    rw [Stacks.Adeles.GeneralLinear.heckeOperatorGL_twistGL, hf.hecke v i hi hin x,
      Stacks.Adeles.GeneralLinear.twistGL, sub_eq_add_neg,
      zpow_add₀ hc]
    ring

end Twist

end Stacks.Adeles.GeneralLinear

end
