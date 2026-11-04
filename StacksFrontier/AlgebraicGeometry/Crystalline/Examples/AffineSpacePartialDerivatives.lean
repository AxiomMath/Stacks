module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Examples.AffineSpaceDeRham

/-!
# The formal partial derivatives of `D = 𝐙_p[x_1, …, x_r]^∧`

In the setup of the example of [Stacks, Tag 07LK] the thickening is the `p`-adic completion
`D = P^∧` of the polynomial ring `P = 𝐙_p[x_1, …, x_r]`.  This module constructs the `r` formal
partial derivatives

`∂/∂x_k : D → D`,

as `𝐙_p`-derivations, by completing `MvPolynomial.pderiv k`.  They are the functionals that read
off the coefficients of a one-form in the basis `dx_1, …, dx_r`, and so they are what identifies
the complex `D → Ω¹_D → ⋯ → Ω^r_D` displayed in the source with an explicit complex of
coefficients.

## Why the completion is immediate

`MvPolynomial.pderiv k` is `𝐙_p`-linear and carries `p^n P` into `p^n P`, `p` being a constant,
so it descends to each level `P/p^n P` of the filtration defining `D`
(`Crystalline.AffineSpaceCrystallineSetup.pderivLevel`) compatibly with the transition maps, and
the resulting family assembles into a map on the inverse limit.  The level maps are formed with
`Submodule.mapQ` over `𝐙_p` applied to `(p^n P).restrictScalars 𝐙_p`, whose quotient is the same
type as the quotient by the `P`-submodule `p^n P` appearing in `AdicCompletion`.

## Main definitions

* `Crystalline.AffineSpaceCrystallineSetup.levelFiltration` — the submodule `p^n P` of the
  filtration defining `D`, with `mem_levelFiltration_iff` its membership criterion.
* `Crystalline.AffineSpaceCrystallineSetup.pderivLevel` — `∂/∂x_k` modulo `p^n`.
* `Crystalline.AffineSpaceCrystallineSetup.pderiv` — the `k`-th formal partial derivative of `D`,
  as a `𝐙_p`-derivation `D → D`.

## Main results

* `Crystalline.AffineSpaceCrystallineSetup.pderiv_algebraMap` — on the dense image of `P` the
  derivation is the formal partial derivative of a polynomial.
* `Crystalline.AffineSpaceCrystallineSetup.pderiv_coordinate` — `∂x_j/∂x_k` is `1` for `j = k`
  and `0` otherwise.

## References

* [Stacks Project, Tag 07LK](https://stacks.math.columbia.edu/tag/07LK)
* [Stacks Project, Tag 07HZ](https://stacks.math.columbia.edu/tag/07HZ)
-/

@[expose] public noncomputable section

namespace Crystalline

namespace AffineSpaceCrystallineSetup

variable (T : AffineSpaceCrystallineSetup)

/-! ### The filtration levels of the completion -/

/-- The `n`-th level `p^n P` of the `p`-adic filtration of the polynomial lift, in the shape in
which it appears in the definition of the completion `D = P^∧`. -/
public abbrev levelFiltration (n : ℕ) : Submodule T.P T.P :=
  DividedPowers.pAdicIdeal (A := T.P) T.p ^ n • ⊤

/-- `p^n P` consists of the multiples of `p^n`. -/
public theorem mem_levelFiltration_iff (n : ℕ) (x : T.P) :
    x ∈ T.levelFiltration n ↔ ∃ y : T.P, x = (T.p : T.P) ^ n * y := by
  rw [levelFiltration, show DividedPowers.pAdicIdeal (A := T.P) T.p ^ n =
      Ideal.span {(T.p : T.P) ^ n} from Ideal.span_singleton_pow _ _,
    Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨y, -, hy⟩
    exact ⟨y, by rw [← hy, smul_eq_mul]⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, Submodule.mem_top, by rw [smul_eq_mul, ← hy]⟩

/-- The formal partial derivative carries `p^n P` into `p^n P`, since `p^n` is a constant. -/
public theorem pderiv_mem_levelFiltration (k : Fin T.r) (n : ℕ) {x : T.P}
    (hx : x ∈ T.levelFiltration n) : MvPolynomial.pderiv k x ∈ T.levelFiltration n := by
  obtain ⟨y, rfl⟩ := (T.mem_levelFiltration_iff n x).mp hx
  refine (T.mem_levelFiltration_iff n _).mpr ⟨MvPolynomial.pderiv k y, ?_⟩
  have hC : ((T.p : T.P) ^ n) = MvPolynomial.C ((T.p : T.A) ^ n) := by
    rw [map_pow, map_natCast]
  rw [hC, MvPolynomial.pderiv_C_mul, ← hC]

/-! ### The partial derivatives of `D` -/

/-- The formal partial derivative `∂/∂x_k` read on the level `P/p^n P` of the filtration
defining `D`. -/
public def pderivLevel (k : Fin T.r) (n : ℕ) :
    T.P ⧸ T.levelFiltration n →ₗ[T.A] T.P ⧸ T.levelFiltration n :=
  Submodule.mapQ ((T.levelFiltration n).restrictScalars T.A)
    ((T.levelFiltration n).restrictScalars T.A) (MvPolynomial.pderiv k).toLinearMap
    (fun _ hx ↦ T.pderiv_mem_levelFiltration k n hx)

/-- The level map is the formal partial derivative on representatives. -/
@[simp]
public theorem pderivLevel_mkQ (k : Fin T.r) (n : ℕ) (x : T.P) :
    T.pderivLevel k n ((T.levelFiltration n).mkQ x) =
      (T.levelFiltration n).mkQ (MvPolynomial.pderiv k x) := rfl

/-- The formal partial derivative `∂/∂x_k` of `D = P^∧`, as a `𝐙_p`-linear map: the family of
level maps `Crystalline.AffineSpaceCrystallineSetup.pderivLevel` is compatible with the
transition maps of the filtration, so it assembles into a map on the inverse limit. -/
public def pderivHom (k : Fin T.r) : T.D →ₗ[T.A] T.D where
  toFun a := ⟨fun n ↦ T.pderivLevel k n (a.val n), by
    intro m n hmn
    obtain ⟨x, hx⟩ := Submodule.mkQ_surjective (T.levelFiltration n) (a.val n)
    have hval : a.val m = (T.levelFiltration m).mkQ x := by
      rw [← AdicCompletion.transitionMap_comp_eval_apply _ _ hmn a, ← hx]
      rfl
    change AdicCompletion.transitionMap (DividedPowers.pAdicIdeal (A := T.P) T.p) T.P hmn
        (T.pderivLevel k n (a.val n)) = T.pderivLevel k m (a.val m)
    rw [← hx, hval, T.pderivLevel_mkQ, T.pderivLevel_mkQ]
    rfl⟩
  map_add' a b := by
    apply AdicCompletion.ext
    intro n
    change T.pderivLevel k n ((a + b).val n) =
      T.pderivLevel k n (a.val n) + T.pderivLevel k n (b.val n)
    rw [AdicCompletion.val_add_apply, map_add]
  map_smul' c a := by
    apply AdicCompletion.ext
    intro n
    change T.pderivLevel k n ((c • a).val n) = c • T.pderivLevel k n (a.val n)
    rw [AdicCompletion.val_smul_apply, map_smul]

/-- The partial derivative of `D` is computed level by level. -/
@[simp]
public theorem val_pderivHom (k : Fin T.r) (a : T.D) (n : ℕ) :
    (T.pderivHom k a).val n = T.pderivLevel k n (a.val n) := rfl

/-- The value of the partial derivative at a level, computed from any polynomial representing
the element at that level. -/
public theorem val_pderivHom_of_mkQ (k : Fin T.r) (a : T.D) (n : ℕ) (x : T.P)
    (hx : (T.levelFiltration n).mkQ x = a.val n) :
    (T.pderivHom k a).val n = (T.levelFiltration n).mkQ (MvPolynomial.pderiv k x) := by
  rw [T.val_pderivHom, ← hx, T.pderivLevel_mkQ]

/-- **The `k`-th formal partial derivative of `D = 𝐙_p[x_1, …, x_r]^∧`**, as a derivation over
the crystalline base `A = 𝐙_p`. -/
public def pderiv (k : Fin T.r) : Derivation T.A T.D T.D where
  __ := T.pderivHom k
  map_one_eq_zero' := by
    apply AdicCompletion.ext
    intro n
    change (T.pderivHom k 1).val n = (0 : T.D).val n
    rw [T.val_pderivHom_of_mkQ k 1 n 1 rfl, Derivation.map_one_eq_zero, map_zero,
      AdicCompletion.val_zero_apply]
  leibniz' a b := by
    apply AdicCompletion.ext
    intro n
    obtain ⟨x, hx⟩ := Submodule.mkQ_surjective (T.levelFiltration n) (a.val n)
    obtain ⟨y, hy⟩ := Submodule.mkQ_surjective (T.levelFiltration n) (b.val n)
    have hab : (T.levelFiltration n).mkQ (x * y) = (a * b).val n := by
      rw [AdicCompletion.val_mul, ← hx, ← hy]
      rfl
    change (T.pderivHom k (a * b)).val n =
      (a * T.pderivHom k b + b * T.pderivHom k a).val n
    rw [T.val_pderivHom_of_mkQ k (a * b) n (x * y) hab,
      AdicCompletion.val_add_apply, AdicCompletion.val_mul, AdicCompletion.val_mul,
      T.val_pderivHom_of_mkQ k b n y hy, T.val_pderivHom_of_mkQ k a n x hx, ← hx, ← hy,
      Derivation.leibniz, map_add]
    rfl

/-- The derivation and the linear map underlying it agree. -/
@[simp]
public theorem pderiv_apply (k : Fin T.r) (a : T.D) : T.pderiv k a = T.pderivHom k a := rfl

/-- On the dense image of `P` in `D` the derivation is the formal partial derivative of a
polynomial. -/
@[simp]
public theorem pderiv_algebraMap (k : Fin T.r) (f : T.P) :
    T.pderiv k (algebraMap T.P T.D f) = algebraMap T.P T.D (MvPolynomial.pderiv k f) := by
  apply AdicCompletion.ext
  intro n
  rw [T.pderiv_apply, T.val_pderivHom_of_mkQ k _ n f rfl]
  rfl

/-- `∂x_j/∂x_k` is `1` for `j = k` and `0` otherwise. -/
public theorem pderiv_coordinate (k j : Fin T.r) :
    T.pderiv k (algebraMap T.P T.D (MvPolynomial.X j)) = if j = k then 1 else 0 := by
  rw [T.pderiv_algebraMap]
  by_cases h : j = k
  · subst h
    rw [MvPolynomial.pderiv_X_self, if_pos rfl, map_one]
  · rw [MvPolynomial.pderiv_X_of_ne h, if_neg h, map_zero]

end AffineSpaceCrystallineSetup

end Crystalline

end
