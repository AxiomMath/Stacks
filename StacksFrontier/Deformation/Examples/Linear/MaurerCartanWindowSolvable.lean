module

public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# The window `m = 1` of the nilpotent dévissage is solvable whenever the kernel is complemented

By `Deformation.Obligation.curvature_add_sub_mem_of_two_le` the whole nonlinearity of the
dévissage of the nilpotent form of Stacks 0DZ2 sits in the single window `m = 1`: a correction
valued in `𝔞^m · L` has Yoneda square valued in `𝔞^(2m) ⊆ 𝔞^(m+2)` once `2 ≤ m`, and at `m = 0`
the lifted differential is given. This file solves that window for the structured instance below.

## The instance

    A' = 𝔽₂[t]/t³,  R = 𝔽₂[y],  P' = A'[y, x]/(x² - t·x),  J' = (y)·P',  Q' = P'[1/(1 + y)]

`P'` is free over `A'[y]` on `{1, x}`, hence flat over `A'`, and Noetherian; `Q'` is flat over
`P'`; and `P'/J' ≅ Q'/J'Q'` because `1 + y` is a unit modulo `y`. Reducing modulo `t` gives
`P = R[x]/(x²)`, and `A = 𝔽₂` is a field, so every `P`-module is `A`-flat.

## The classification of the lifts, and its verification

Let `M = R^n` with `x` acting by `X₀ ∈ Mₙ(R)`, `X₀² = 0`. An `A'`-flat `P'`-module lift `M'` of
`M` is free over `A'[y] = R[t]/t³` of rank `n`: a generator-lifting surjection
`(A'[y])^n → M'` has kernel `K` with `K/tK = 0` — because `M'` is `A'`-flat, so
`Tor₁^{A'}(A, M') = 0` and the reduction of the surjection is the identity — hence `K = tK` and
`K = 0` by nilpotence of `t`. The action of `x` is therefore a matrix `Ξ` over `R[t]/t³` with
`Ξ ≡ X₀ mod t` and `Ξ² = t·Ξ`, the relation of `P'`. Writing `Ξ = X₀ + t·α + t²·β` and comparing
coefficients of `t⁰, t¹, t²` (there is no `t³`):

* `X₀² = 0`;
* `X₀·α + α·X₀ = X₀`;
* `X₀·β + β·X₀ + α² = α`, that is `α² + α + X₀·β + β·X₀ = 0` in characteristic two.

So the lifts are **exactly** the pairs `(α, β)` of matrices over `R` satisfying the last two
equations. That coefficient comparison is `lift3_sq_eq_tau_smul_iff`, with
`cst_add_tau_eq_zero_iff` and `exists_cst_add_tau` supplying the two halves of the fact that
`1, t, t²` are an `R`-basis of `R[t]/t³`, so that the comparison is an equivalence and the
pairs are in bijection with the matrices `Ξ`.

## The window is always solvable here

Read the first equation as `X₀ ∘ α = (1 - α) ∘ X₀`. If `α` is an **idempotent** whose image is
`ker X₀` then `α ∘ X₀ = X₀` (because `im X₀ ⊆ ker X₀`, as `X₀² = 0`) and `X₀ ∘ α = 0`, so the
first equation holds; and `α² - α = 0`, so the second holds with `β = 0`. Such an `α` exists as
soon as `ker X₀` is a *direct summand*, i.e. as soon as `M/ker X₀ ≅ im X₀` is projective
(`hasWindowSolution_of_projective_quotient`).

Over `R = 𝔽₂[y]` — a principal ideal domain — `im X₀` is a submodule of a finite free module,
hence free, hence projective. So **the window is solvable for every `n` and every `X₀`**:
`exists_flat_lift_system`: every `M = R^n` has an `A'`-flat `P'`-module lift.

In particular the `n = 4` instance `X₀ = J_y ⊕ J_{1+y}` lifts, with the explicit witness
`α = diag(1, 0, 1, 0)`, `β = 0`: `jordanPair_flat_lift_system`. Since `α` is idempotent,
`α² - α` vanishes identically.

The window is not solvable in general: a square-zero element of a commutative ring solving the
window is zero (`Deformation.Examples.MaurerCartanWindow.eq_zero_of_hasWindowSolution`), so the
window fails at `M = R` over `R = k[s]/(s²)` with `x` acting by `s`, where `im X₀ = (s)` is not
projective.

## Main definitions

* `Deformation.Examples.MaurerCartanWindow.HasWindowSolution`: the Maurer–Cartan system of the
  window `m = 1`, `x·a + a·x = x` and `x·b + b·x + a² = a`, in an arbitrary ring.
* `Deformation.Examples.MaurerCartanWindow.Trunc3`: the ring `R[t]/t³`, which is `A'[y]` for
  `R = 𝔽₂[y]`.
* `Deformation.Examples.MaurerCartanWindow.lift3`: the lifted matrix `Ξ = X₀ + t·α + t²·β`.
* `Deformation.Examples.MaurerCartanWindow.jordanPair`: the designated `X₀ = J_y ⊕ J_{1+y}`.

## Main results

* `Deformation.Examples.MaurerCartanWindow.hasWindowSolution_of_isIdempotentElem`: an idempotent
  `a` with `x·a = 0` and `a·x = x` solves the window with `b = 0`.
* `Deformation.Examples.MaurerCartanWindow.hasWindowSolution_of_projective_quotient`:
  **the window is solvable whenever `M ⧸ ker X` is projective.** The idempotent is `1 - s ∘ π`
  for a splitting `s` of the quotient map `π`, so its image is `ker X`.
* `Deformation.Examples.MaurerCartanWindow.hasWindowSolution_of_sq_eq_zero`: **over a principal
  ideal domain the window is always solvable**, for any square-zero endomorphism of a finite
  free module: `im X` is free, hence projective.
* `Deformation.Examples.MaurerCartanWindow.exists_flat_lift_system`: **the designated family is
  uniformly liftable.** For every `n` and every `X₀` over `𝔽₂[y]` with `X₀² = 0` there are
  matrices `α, β` with `X₀·α + α·X₀ = X₀` and `α² + α + X₀·β + β·X₀ = 0`.
* `Deformation.Examples.MaurerCartanWindow.jordanPair_flat_lift_system`: the explicit witness at
  the designated `n = 4`, `X₀ = J_y ⊕ J_{1+y}`.
* `Deformation.Examples.MaurerCartanWindow.lift3_sq_eq_tau_smul_iff`: **the classification.**
  `Ξ = X₀ + t·α + t²·β` satisfies the relation `Ξ² = t·Ξ` of `P'` if and only if the three
  coefficient equations hold.
* `Deformation.Examples.MaurerCartanWindow.exists_lift3` and
  `Deformation.Examples.MaurerCartanWindow.lift3_inj`: every matrix over `R[t]/t³` is
  `X₀ + t·α + t²·β` for a unique triple, so the classification is a bijection.

## References

* [Stacks Project, Tag 0DZ2](https://stacks.math.columbia.edu/tag/0DZ2)
* [Stacks Project, Tag 0DZ1](https://stacks.math.columbia.edu/tag/0DZ1)
* [Stacks Project, Tag 05EC](https://stacks.math.columbia.edu/tag/05EC)
-/

@[expose] public section

universe u

namespace Deformation.Examples.MaurerCartanWindow

/-! ### The window system -/

/-- The Maurer–Cartan system of the window `m = 1`. -/
def HasWindowSolution {S : Type*} [Ring S] (x : S) : Prop :=
  ∃ a b : S, x * a + a * x = x ∧ x * b + b * x + a * a = a

/-- **An idempotent solves the window.** If `a² = a`, `x·a = 0` and `a·x = x` then `(a, 0)`
solves the Maurer–Cartan system of the window: the first equation is `0 + x = x` and the second
is `0 + 0 + a = a`. -/
theorem hasWindowSolution_of_isIdempotentElem {S : Type*} [Ring S] {x a : S}
    (ha : a * a = a) (hxa : x * a = 0) (hax : a * x = x) : HasWindowSolution x :=
  ⟨a, 0, by rw [hxa, hax, zero_add], by simp [ha]⟩

/-- Solvability of the window transports along a ring isomorphism. -/
theorem HasWindowSolution.map {S T : Type*} [Ring S] [Ring T] (e : S ≃+* T) {x : S}
    (h : HasWindowSolution x) : HasWindowSolution (e x) := by
  obtain ⟨a, b, h1, h2⟩ := h
  refine ⟨e a, e b, ?_, ?_⟩
  · rw [← map_mul, ← map_mul, ← map_add, h1]
  · rw [← map_mul, ← map_mul, ← map_mul, ← map_add, ← map_add, h2]

/-! ### Solvability from a complemented kernel -/

variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]

/-- **The window is solvable whenever the kernel is a direct summand.** Let `X` be an
endomorphism with `X ∘ X = 0` and suppose `M ⧸ ker X` is projective, so that the quotient map
`π` admits a splitting `s`. Then `a = 1 - s ∘ π` is an idempotent with image `ker X`, so
`X ∘ a = 0`, and `a ∘ X = X` because `im X ⊆ ker X`; hence `(a, 0)` solves the window. -/
theorem hasWindowSolution_of_projective_quotient {X : M →ₗ[R] M}
    (hX : ∀ v : M, X (X v) = 0)
    [Module.Projective R (M ⧸ LinearMap.ker X)] :
    HasWindowSolution (X : Module.End R M) := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property
    (LinearMap.ker X).mkQ LinearMap.id (LinearMap.ker X).mkQ_surjective
  have hsapp : ∀ z, (LinearMap.ker X).mkQ (s z) = z := fun z => LinearMap.congr_fun hs z
  set a : Module.End R M := 1 - s ∘ₗ (LinearMap.ker X).mkQ
  have hav : ∀ v : M, a v = v - s ((LinearMap.ker X).mkQ v) := fun _ => rfl
  have h0 : ∀ v : M, (LinearMap.ker X).mkQ (a v) = 0 := fun v => by
    rw [hav, map_sub, hsapp, sub_self]
  have hXrange : ∀ v : M, (LinearMap.ker X).mkQ (X v) = 0 := by
    intro v
    rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
    exact LinearMap.mem_ker.2 (hX v)
  refine hasWindowSolution_of_isIdempotentElem (a := a) ?_ ?_ ?_ <;>
    refine LinearMap.ext fun v => ?_
  · change a (a v) = a v
    rw [hav (a v), h0, map_zero, sub_zero]
  · change X (a v) = 0
    have hv := LinearMap.mem_ker.2 (h0 v)
    rwa [Submodule.ker_mkQ, LinearMap.mem_ker] at hv
  · change a (X v) = X v
    rw [hav, hXrange, map_zero, sub_zero]

/-! ### Over a principal ideal domain the window is always solvable -/

/-- **Over a principal ideal domain the window is always solvable.** For a square-zero
endomorphism `X` of a finite free module, `im X` is a submodule of a finite free module over a
principal ideal domain, hence free, hence projective; so `M ⧸ ker X ≅ im X` is projective and
`Deformation.Examples.MaurerCartanWindow.hasWindowSolution_of_projective_quotient` applies. -/
theorem hasWindowSolution_of_sq_eq_zero [IsDomain R] [IsPrincipalIdealRing R] [Module.Free R M]
    [Module.Finite R M] {X : M →ₗ[R] M} (hX : ∀ v : M, X (X v) = 0) :
    HasWindowSolution (X : Module.End R M) := by
  obtain ⟨k, bk⟩ := Submodule.basisOfPid (Module.Free.chooseBasis R M) (LinearMap.range X)
  have : Module.Free R (LinearMap.range X) := Module.Free.of_basis bk
  have : Module.Projective R (M ⧸ LinearMap.ker X) :=
    Module.Projective.of_equiv (X.quotKerEquivRange).symm
  exact hasWindowSolution_of_projective_quotient hX

/-! ### The matrix form -/

/-- The matrix form of
`Deformation.Examples.MaurerCartanWindow.hasWindowSolution_of_sq_eq_zero`, transported along the
algebra isomorphism between `Mₙ(R)` and the endomorphisms of `Rⁿ`. -/
theorem hasWindowSolution_matrix {n : Type u} [Fintype n] [DecidableEq n] [IsDomain R]
    [IsPrincipalIdealRing R] {X : Matrix n n R} (hX : X * X = 0) : HasWindowSolution X := by
  classical
  set e : Matrix n n R ≃+* Module.End R (n → R) :=
    (Matrix.toLinAlgEquiv' (R := R) (n := n)).toRingEquiv with he
  have hsq : ∀ v : n → R, (e X) ((e X) v) = 0 := by
    intro v
    have h : e X * e X = 0 := by rw [← map_mul, hX, map_zero]
    have := LinearMap.congr_fun h v
    simpa [Module.End.mul_apply] using this
  have h := (hasWindowSolution_of_sq_eq_zero (R := R) (M := n → R) hsq).map e.symm
  rwa [e.symm_apply_apply] at h

/-! ### The designated instance: `R = 𝔽₂[y]` -/

/-- A matrix over `𝔽₂[y]`, indexed by an arbitrary (possibly empty) type, is its own additive
inverse. -/
theorem add_self_eq_zero {n : Type u} (a : Matrix n n (Polynomial (ZMod 2))) : a + a = 0 := by
  funext i j
  exact CharTwo.add_self_eq_zero _

/-- **The family `M = (𝔽₂[y])^n` is uniformly liftable.** For every `n` and every
`X₀ ∈ Mₙ(𝔽₂[y])` with `X₀² = 0` there are matrices `α, β` over `𝔽₂[y]` with

`X₀·α + α·X₀ = X₀` and `α² + α + X₀·β + β·X₀ = 0`,

which by the classification of the module docstring is exactly an `A'`-flat `P'`-module lift of
`M = (𝔽₂[y])^n` with `x` acting by `X₀`. -/
theorem exists_flat_lift_system (n : ℕ)
    (X : Matrix (Fin n) (Fin n) (Polynomial (ZMod 2))) (hX : X * X = 0) :
    ∃ a b : Matrix (Fin n) (Fin n) (Polynomial (ZMod 2)),
      X * a + a * X = X ∧ a * a + a + (X * b + b * X) = 0 := by
  obtain ⟨a, b, h1, h2⟩ := hasWindowSolution_matrix hX
  refine ⟨a, b, h1, ?_⟩
  calc a * a + a + (X * b + b * X)
      = (X * b + b * X + a * a) + a := by abel
    _ = a + a := by rw [h2]
    _ = 0 := add_self_eq_zero a

/-! ### The designated `n = 4` instance, explicitly -/

/-- `X₀ = J_y ⊕ J_{1+y}`. -/
noncomputable def jordanPair : Matrix (Fin 4) (Fin 4) (Polynomial (ZMod 2)) :=
  Matrix.of ![![0, Polynomial.X, 0, 0], ![0, 0, 0, 0],
    ![0, 0, 0, 1 + Polynomial.X], ![0, 0, 0, 0]]

/-- The idempotent `α = diag(1, 0, 1, 0)`. -/
noncomputable def jordanPairIdem : Matrix (Fin 4) (Fin 4) (Polynomial (ZMod 2)) :=
  Matrix.of ![![1, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 0]]

/-- `X₀² = 0`: the two Jordan blocks have square zero. -/
theorem jordanPair_mul_self : jordanPair * jordanPair = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [jordanPair, Matrix.mul_apply, Fin.sum_univ_four]

/-- `α` is idempotent. -/
theorem jordanPairIdem_mul_self : jordanPairIdem * jordanPairIdem = jordanPairIdem := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [jordanPairIdem, Matrix.mul_apply, Fin.sum_univ_four]

/-- The first window equation at the designated `n = 4` instance: `α` is the identity on
`im X₀` and its image `span(e₁, e₃)` is `ker X₀`, so `X₀·α = 0` and `α·X₀ = X₀`. -/
theorem jordanPair_window :
    jordanPair * jordanPairIdem + jordanPairIdem * jordanPair = jordanPair := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [jordanPair, jordanPairIdem]

/-- **The designated `n = 4` instance lifts, explicitly.** For `X₀ = J_y ⊕ J_{1+y}` the pair
`α = diag(1, 0, 1, 0)`, `β = 0` solves the window system; the quadratic term `α² + α` vanishes
identically. -/
theorem jordanPair_flat_lift_system :
    jordanPair * jordanPairIdem + jordanPairIdem * jordanPair = jordanPair ∧
      jordanPairIdem * jordanPairIdem + jordanPairIdem
        + (jordanPair * 0 + 0 * jordanPair) = 0 := by
  refine ⟨jordanPair_window, ?_⟩
  rw [jordanPairIdem_mul_self, mul_zero, zero_mul, add_zero, add_zero]
  exact add_self_eq_zero _

/-! ### The classification: `Ξ² = tΞ` is the window system -/

section Classification

variable (R) in
/-- `R[t]/t³`: the ring `A'[y] = 𝔽₂[t]/t³ [y]` of the designated instance, for `R = 𝔽₂[y]`. -/
abbrev Trunc3 : Type u := Polynomial R ⧸ Ideal.span {(Polynomial.X : Polynomial R) ^ 3}

variable (R) in
/-- The class of `t` in `R[t]/t³`. -/
noncomputable def tau : Trunc3 R := Ideal.Quotient.mk _ Polynomial.X

variable (R) in
/-- The structure map `R → R[t]/t³`. -/
noncomputable def cst : R →+* Trunc3 R :=
  (Ideal.Quotient.mk _).comp (Polynomial.C : R →+* Polynomial R)

/-- `t³ = 0`. -/
theorem tau_cube : tau R * tau R * tau R = 0 := by
  rw [tau, ← map_mul, ← map_mul, Ideal.Quotient.eq_zero_iff_mem,
    show (Polynomial.X * Polynomial.X * Polynomial.X : Polynomial R) = Polynomial.X ^ 3 by ring]
  exact Ideal.mem_span_singleton_self _

/-- `t³ = 0`, right-associated. -/
theorem tau_cube' : tau R * (tau R * tau R) = 0 := by
  rw [← mul_assoc]; exact tau_cube

/-- `t⁴ = 0`. -/
theorem tau_sq_mul_tau_sq : tau R * tau R * (tau R * tau R) = 0 := by
  rw [show tau R * tau R * (tau R * tau R) = tau R * tau R * tau R * tau R by ring, tau_cube,
    zero_mul]

/-- The degree-`< 3` representative `a + t b + t² c`. -/
noncomputable def poly3 (a b c : R) : Polynomial R :=
  Polynomial.C a + Polynomial.X * Polynomial.C b
    + Polynomial.X * Polynomial.X * Polynomial.C c

/-- The class of the degree-`< 3` representative, written in terms of `1`, `t`, `t²`. -/
theorem mk_poly3 (a b c : R) :
    Ideal.Quotient.mk (Ideal.span {(Polynomial.X : Polynomial R) ^ 3}) (poly3 a b c) =
      cst R a + tau R * cst R b + tau R * tau R * cst R c := by
  simp only [poly3, map_add, map_mul, cst, tau, RingHom.coe_comp, Function.comp_apply]

/-- The constant coefficient of `a + t b + t² c`. -/
theorem poly3_coeff_zero (a b c : R) : (poly3 a b c).coeff 0 = a := by simp [poly3]

/-- The linear coefficient of `a + t b + t² c`. -/
theorem poly3_coeff_one (a b c : R) : (poly3 a b c).coeff 1 = b := by simp [poly3]

/-- The quadratic coefficient of `a + t b + t² c`. -/
theorem poly3_coeff_two (a b c : R) : (poly3 a b c).coeff 2 = c := by simp [poly3]

/-- **`1`, `t`, `t²` are an `R`-basis of `R[t]/t³`: independence.** -/
theorem cst_add_tau_eq_zero_iff {a b c : R} :
    cst R a + tau R * cst R b + tau R * tau R * cst R c = 0 ↔ a = 0 ∧ b = 0 ∧ c = 0 := by
  constructor
  · intro h
    rw [← mk_poly3, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h
    obtain ⟨g, hg⟩ := h
    have hcoeff : ∀ d, d < 3 → (poly3 a b c).coeff d = 0 := by
      intro d hd
      rw [hg, mul_comm, Polynomial.coeff_mul_X_pow', ite_eq_right (by lia)]
    exact ⟨(poly3_coeff_zero a b c).symm.trans (hcoeff 0 (by lia)),
      (poly3_coeff_one a b c).symm.trans (hcoeff 1 (by lia)),
      (poly3_coeff_two a b c).symm.trans (hcoeff 2 (by lia))⟩
  · rintro ⟨rfl, rfl, rfl⟩
    simp

/-- **`1`, `t`, `t²` are an `R`-basis of `R[t]/t³`: spanning.** -/
theorem exists_cst_add_tau (z : Trunc3 R) :
    ∃ a b c : R, z = cst R a + tau R * cst R b + tau R * tau R * cst R c := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective z
  induction f using Polynomial.induction_on' with
  | add p q hp hq =>
      obtain ⟨a, b, c, hpe⟩ := hp
      obtain ⟨a', b', c', hqe⟩ := hq
      refine ⟨a + a', b + b', c + c', ?_⟩
      rw [map_add, hpe, hqe]
      simp only [map_add, mul_add]
      abel
  | monomial k a =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow]
      have hc : (Ideal.Quotient.mk (Ideal.span {(Polynomial.X : Polynomial R) ^ 3}))
          (Polynomial.C a) = cst R a := rfl
      have ht : (Ideal.Quotient.mk (Ideal.span {(Polynomial.X : Polynomial R) ^ 3}))
          Polynomial.X = tau R := rfl
      rw [hc, ht]
      match k with
      | 0 => exact ⟨a, 0, 0, by simp⟩
      | 1 => exact ⟨0, a, 0, by simp [mul_comm]⟩
      | 2 => exact ⟨0, 0, a, by simp [pow_succ, mul_comm, mul_assoc]⟩
      | (m + 3) =>
          refine ⟨0, 0, 0, ?_⟩
          have h0 : tau R ^ (m + 3) = 0 := by
            rw [pow_add, show tau R ^ 3 = tau R * tau R * tau R by ring, tau_cube, mul_zero]
          rw [h0, mul_zero]
          simp

variable {n : Type u} [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
/-- `R → R[t]/t³` is additive on matrices. -/
theorem map_cst_add (U V : Matrix n n R) :
    (U + V).map (cst R) = U.map (cst R) + V.map (cst R) :=
  Matrix.map_add _ (map_add _) U V

omit [Fintype n] [DecidableEq n] in
/-- `R → R[t]/t³` respects differences of matrices. -/
theorem map_cst_sub (U V : Matrix n n R) :
    (U - V).map (cst R) = U.map (cst R) - V.map (cst R) :=
  Matrix.map_sub _ (map_sub _) U V

omit [DecidableEq n] in
/-- `R → R[t]/t³` is multiplicative on matrices. -/
theorem map_cst_mul (U V : Matrix n n R) :
    (U * V).map (cst R) = U.map (cst R) * V.map (cst R) :=
  Matrix.map_mul

omit [Fintype n] [DecidableEq n] in
/-- `R → R[t]/t³` sends the zero matrix to the zero matrix. -/
theorem map_cst_zero : (0 : Matrix n n R).map (cst R) = 0 :=
  Matrix.map_zero _ (map_zero _)

/-- `Ξ = X₀ + t·α + t²·β`, a matrix over `R[t]/t³ = A'[y]`. -/
noncomputable def lift3 (X A B : Matrix n n R) : Matrix n n (Trunc3 R) :=
  X.map (cst R) + tau R • A.map (cst R) + (tau R * tau R) • B.map (cst R)

omit [Fintype n] [DecidableEq n] in
/-- The entries of `Ξ = X₀ + t·α + t²·β`. -/
theorem lift3_apply (X A B : Matrix n n R) (i j : n) :
    lift3 X A B i j = cst R (X i j) + tau R * cst R (A i j)
      + tau R * tau R * cst R (B i j) := by
  simp [lift3, mul_assoc]

omit [Fintype n] [DecidableEq n] in
/-- `Ξ = X₀ + t·α + t²·β` vanishes only if all three matrices do. -/
theorem lift3_eq_zero_iff (X A B : Matrix n n R) :
    lift3 X A B = 0 ↔ X = 0 ∧ A = 0 ∧ B = 0 := by
  constructor
  · intro h
    have hent : ∀ i j, X i j = 0 ∧ A i j = 0 ∧ B i j = 0 := by
      intro i j
      refine cst_add_tau_eq_zero_iff.1 ?_
      rw [← lift3_apply, h]
      rfl
    exact ⟨by ext i j; exact (hent i j).1, by ext i j; exact (hent i j).2.1,
      by ext i j; exact (hent i j).2.2⟩
  · rintro ⟨rfl, rfl, rfl⟩
    simp [lift3]

omit [Fintype n] [DecidableEq n] in
/-- `(X₀, α, β) ↦ Ξ` respects differences. -/
theorem lift3_sub (X A B X' A' B' : Matrix n n R) :
    lift3 X A B - lift3 X' A' B' = lift3 (X - X') (A - A') (B - B') := by
  simp only [lift3, map_cst_sub, smul_sub]
  abel

omit [Fintype n] [DecidableEq n] in
/-- `(X₀, α, β) ↦ Ξ` is injective: the three matrices are the coefficients of `Ξ`. -/
theorem lift3_inj {X A B X' A' B' : Matrix n n R} (h : lift3 X A B = lift3 X' A' B') :
    X = X' ∧ A = A' ∧ B = B' := by
  have h0 : lift3 (X - X') (A - A') (B - B') = 0 := by rw [← lift3_sub, h, sub_self]
  obtain ⟨h1, h2, h3⟩ := (lift3_eq_zero_iff _ _ _).1 h0
  exact ⟨sub_eq_zero.1 h1, sub_eq_zero.1 h2, sub_eq_zero.1 h3⟩

omit [Fintype n] [DecidableEq n] in
/-- Every matrix over `R[t]/t³` is `X₀ + t·α + t²·β` for unique matrices over `R`. -/
theorem exists_lift3 (Xi : Matrix n n (Trunc3 R)) :
    ∃ X A B : Matrix n n R, Xi = lift3 X A B := by
  choose fa fb fc hf using fun ij : n × n => exists_cst_add_tau (Xi ij.1 ij.2)
  refine ⟨Matrix.of fun i j => fa (i, j), Matrix.of fun i j => fb (i, j),
    Matrix.of fun i j => fc (i, j), ?_⟩
  ext i j
  rw [lift3_apply]
  exact hf (i, j)

omit [DecidableEq n] in
/-- **The square of the lifted matrix.** `Ξ² = X₀² + t(X₀α + αX₀) + t²(X₀β + βX₀ + α²)`; the
terms of order `t³` and `t⁴` vanish. -/
theorem lift3_mul_self (X A B : Matrix n n R) :
    lift3 X A B * lift3 X A B =
      lift3 (X * X) (X * A + A * X) (X * B + B * X + A * A) := by
  simp only [lift3, map_cst_add, map_cst_mul, Matrix.add_mul, Matrix.mul_add,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_add, tau_cube, tau_cube', tau_sq_mul_tau_sq,
    zero_smul]
  abel

omit [Fintype n] [DecidableEq n] in
/-- `t·Ξ = t·X₀ + t²·α`. -/
theorem tau_smul_lift3 (X A B : Matrix n n R) :
    tau R • lift3 X A B = lift3 0 X A := by
  simp only [lift3, smul_add, smul_smul, map_cst_zero, tau_cube', zero_smul]
  abel

omit [DecidableEq n] in
/-- **The Maurer–Cartan window system is exactly the lifting equation.** The matrix
`Ξ = X₀ + t·α + t²·β` over `A'[y] = R[t]/t³` satisfies `Ξ² = t·Ξ` — the relation
`x² = t·x` of `P' = A'[y, x]/(x² - t·x)` — if and only if the three coefficient equations
hold. -/
theorem lift3_sq_eq_tau_smul_iff (X A B : Matrix n n R) :
    lift3 X A B * lift3 X A B = tau R • lift3 X A B ↔
      (X * X = 0 ∧ X * A + A * X = X ∧ X * B + B * X + A * A = A) := by
  rw [lift3_mul_self, tau_smul_lift3]
  constructor
  · intro h
    exact lift3_inj h
  · rintro ⟨h1, h2, h3⟩
    rw [h1, h2, h3]

end Classification

end Deformation.Examples.MaurerCartanWindow

end
