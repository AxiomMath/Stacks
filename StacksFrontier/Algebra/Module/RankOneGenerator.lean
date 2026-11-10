module

public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Basis.SMul

/-!
# Generators of a free module of rank one

Four small facts about a free module `N` of rank one over a commutative ring `R`.

* A linear equivalence `M ≃ₗ[R] N` carrying `x` to a unit multiple of a basis element makes `M`
  free of rank one with basis element `x`.
* Two maps `α β : M → N` out of a set carrying an action of `R`, both compatible with that
  action, with `α` bijective, differ by a scalar: `β = t • α`. This is how two comparison maps
  that are not known to agree, but are both linear, are compared.
* If `t • y` is a basis element then `t` is a unit.
* Two such maps `α β`, with `α` bijective, take unit multiples of each other's values at a point
  where `β` is detected as a basis element by a linear map.

## Main results

* `Module.Basis.exists_basis_of_linearEquiv_eq_unit_smul`: the first fact.
* `exists_smul_eq_of_bijective_of_semilinear`: the second fact.
* `Module.Basis.exists_unit_of_smul_eq`: the third fact.
* `exists_unit_smul_eq_of_bijective_of_semilinear`: the fourth fact.
-/

@[expose] public section

universe u v w

variable {R : Type u} [CommRing R] {M : Type v} {N : Type w}

/-- **A linear equivalence carrying `x` to a unit multiple of a basis element of a free module of
rank one makes its source free of rank one with basis element `x`.** -/
theorem Module.Basis.exists_basis_of_linearEquiv_eq_unit_smul [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) (b : Module.Basis (Fin 1) R N) (x : M)
    (ε : Rˣ) (h : e x = ε • b 0) : ∃ b' : Module.Basis (Fin 1) R M, b' 0 = x := by
  refine ⟨(b.unitsSMul fun _ => ε).map e.symm, ?_⟩
  rw [Module.Basis.map_apply, Module.Basis.unitsSMul_apply, ← h, LinearEquiv.symm_apply_apply]

/-- Every element of a free module of rank one is a multiple of the basis element. -/
theorem Module.Basis.eq_repr_smul [AddCommGroup N] [Module R N] (b : Module.Basis (Fin 1) R N)
    (n : N) : n = b.repr n 0 • b 0 := by
  conv_lhs => rw [← b.linearCombination_repr n]
  rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (fun i => by simp)]
  simp

/-- **Two maps compatible with an action of `R`, one of them bijective, into a free module of rank
one differ by a scalar.** Let `τ` be an action of `R` on a set `M` and let `α β : M → N` satisfy
`α (τ r m) = r • α m` and `β (τ r m) = r • β m`. If `α` is bijective, then `β = t • α` for some
`t : R`. -/
theorem exists_smul_eq_of_bijective_of_semilinear [AddCommGroup N] [Module R N]
    (b : Module.Basis (Fin 1) R N) (τ : R → M → M) (α β : M → N) (hα : Function.Bijective α)
    (hτα : ∀ r m, α (τ r m) = r • α m) (hτβ : ∀ r m, β (τ r m) = r • β m) :
    ∃ t : R, ∀ m, β m = t • α m := by
  obtain ⟨y, hy⟩ := hα.2 (b 0)
  refine ⟨b.repr (β y) 0, fun m => ?_⟩
  set r := b.repr (α m) 0
  have hm : m = τ r y := hα.1 (by rw [hτα, hy]; exact b.eq_repr_smul (α m))
  rw [hm, hτβ, hτα, hy, b.eq_repr_smul (β y), smul_smul, smul_smul, mul_comm,
    ← b.eq_repr_smul (β y)]

/-- If `t • y` is the basis element of a free module of rank one, then `t` times the coordinate of
`y` is `1`. -/
private theorem mul_repr_eq_one_of_smul_eq [AddCommGroup N] [Module R N]
    (b : Module.Basis (Fin 1) R N) (t : R) (y : N) (h : t • y = b 0) : t * b.repr y 0 = 1 := by
  have hst : (t * b.repr y 0) • b 0 = b 0 := by rw [mul_smul, ← b.eq_repr_smul y, h]
  simpa using congrArg (fun n => b.repr n 0) hst

/-- **If `t • y` is a basis element of a free module of rank one, then `t` is a unit**, and `y` is
the inverse unit multiple of that basis element. -/
theorem Module.Basis.exists_unit_of_smul_eq [AddCommGroup N] [Module R N]
    (b : Module.Basis (Fin 1) R N) (t : R) (y : N) (h : t • y = b 0) :
    ∃ ε : Rˣ, y = ε • b 0 := by
  have hone := mul_repr_eq_one_of_smul_eq b t y h
  exact ⟨⟨_, t, by rw [mul_comm]; exact hone, hone⟩, b.eq_repr_smul y⟩

/-- **Two maps compatible with an action of `R`, one of them bijective, into a free module of rank
one take unit multiples of each other's values at a point detected by a linear map**: let
`α β : M → N₁` be compatible with an action `τ` of `R` on `M`, with `α` bijective, let `N₁` be free
of rank one, and let `L : N₁ → N` commute with the action of `R`, into a free module of rank one
with basis element `b 0`. If `L (β m₀) = b 0`, then `α m₀ = ε • β m₀` for a unit `ε`. -/
theorem exists_unit_smul_eq_of_bijective_of_semilinear {N₁ : Type*} [AddCommGroup N₁]
    [Module R N₁] [AddCommGroup N] [Module R N] (b₁ : Module.Basis (Fin 1) R N₁)
    (b : Module.Basis (Fin 1) R N) (L : N₁ → N) (hL : ∀ (r : R) y, L (r • y) = r • L y)
    (τ : R → M → M) (α β : M → N₁)
    (hα : Function.Bijective α) (hτα : ∀ r m, α (τ r m) = r • α m)
    (hτβ : ∀ r m, β (τ r m) = r • β m) (m₀ : M) (h : L (β m₀) = b 0) :
    ∃ ε : Rˣ, α m₀ = ε • β m₀ := by
  obtain ⟨t, ht⟩ := exists_smul_eq_of_bijective_of_semilinear b₁ τ α β hα hτα hτβ
  have h' : t • L (α m₀) = b 0 := by rw [← hL, ← ht, h]
  set s := b.repr (L (α m₀)) 0
  have hone := mul_repr_eq_one_of_smul_eq b t _ h'
  refine ⟨⟨s, t, by rw [mul_comm]; exact hone, hone⟩, ?_⟩
  rw [Units.smul_def, ht, smul_smul]
  change α m₀ = (s * t) • α m₀
  rw [mul_comm, hone, one_smul]
