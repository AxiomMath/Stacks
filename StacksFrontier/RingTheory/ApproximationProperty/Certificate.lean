module

public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.Tactic.DeriveFintype

/-!
# Certificates for singular points

Let `R` be a regular local ring, `𝔮 ⊆ 𝔭` primes of `R` such that `(R/𝔮)_𝔭` is not regular, and
`R₀ → R` a ring map whose image contains elements `y_1, …, y_e` generating an ideal primary to
the maximal ideal. Rotthaus' proof that the approximation property forces geometrically regular
formal fibres (Rotthaus, Section 2) describes such a situation by a finite system of polynomial
equations over `R₀` whose unknowns are generators of `𝔭` and of `𝔮`, a few further elements of
`R`, and the coefficients witnessing finitely many ideal memberships:

* `S · Q_σ ∈ (V_1, …, V_l)` for every generator `Q_σ` of `𝔭`, where `V_1, …, V_l` are among the
  `Q_σ` (so that `S ∉ 𝔭` makes `(V)` generate `𝔭` locally);
* `y_i ^ N ∈ (V_1, …, V_l, L_1, …, L_{k_v})` (so that the `V`'s are part of a system of
  parameters);
* `T · Q_{j_J} ∈ (Q_σ Q_τ) + (Q_λ : λ ∈ J ∖ {j_J})` for every set `J` of `r` generators of `𝔮`
  (so that `(R/𝔮)_𝔭` is singular, `r` being the height of `𝔮`);
* `y_i ^ N ∈ (Q_σ) + (T·C) + (L'_1, …, L'_{k_z})` (so that `T` and `C` avoid the prime).

This file sets up the shape of the system, its unknowns and relations, and the finitely presented
`R₀`-algebra it defines: its `R₀`-algebra maps to an `R₀`-algebra `T` are exactly the assignments
of the unknowns in `T` satisfying the relations.

## Main definitions

* `Stacks.ApproximationProperty.Certificate.Shape`: the combinatorial shape of the system.
* `Stacks.ApproximationProperty.Certificate.Var`, `…Certificate.Rel`: its unknowns and relations.
* `Stacks.ApproximationProperty.Certificate.rel`: the relations evaluated at an assignment.
* `Stacks.ApproximationProperty.Certificate.Alg`: the finitely presented algebra of the system.

## Main results

* `Stacks.ApproximationProperty.Certificate.rel_comp`: the relations are compatible with algebra
  maps.
* `Stacks.ApproximationProperty.Certificate.lift`, `…Certificate.eval`: algebra maps out of `Alg`
  correspond to solutions of the system.

## References

* [C. Rotthaus, *Rings with approximation property*, Math. Ann. 287 (1990), 455–466][Rotthaus]
-/

@[expose] public section

universe u v w

namespace Stacks.ApproximationProperty.Certificate

/-- The combinatorial shape of a certificate: `a` generators of `𝔮`, `l` elements `V_i`, `c`
further generators of `𝔭`, `kv` complementary parameters for the `V`'s, `kz` parameters for the
non-membership relation, `e` elements `y_i`, the height `r` of `𝔮`, the exponent `N`, and for every
set `J` of `r` generators of `𝔮` the index `pick J` of the generator expressed by the others. -/
structure Shape where
  /-- The number of generators of `𝔮`. -/
  a : ℕ
  /-- The number of elements `V_i`. -/
  l : ℕ
  /-- The number of further generators of `𝔭`. -/
  c : ℕ
  /-- The number of parameters completing the `V`'s. -/
  kv : ℕ
  /-- The number of parameters in the non-membership relation. -/
  kz : ℕ
  /-- The number of elements `y_i`. -/
  e : ℕ
  /-- The height of `𝔮`. -/
  r : ℕ
  /-- The exponent of the `y_i` in the parameter relations. -/
  N : ℕ
  /-- For a set `J` of `r` generators of `𝔮`, the generator expressed by the others. -/
  pick : {J : Finset (Fin a) // J.card = r} → Fin a

variable (s : Shape)

/-- The index set of the generators `Q_σ` of `𝔭`: those of `𝔮`, the `V`'s, and the others. -/
abbrev Gen : Type := Fin s.a ⊕ Fin s.l ⊕ Fin s.c

/-- The sets of `r` generators of `𝔮`. -/
abbrev Subs : Type := {J : Finset (Fin s.a) // J.card = s.r}

/-- The generator `Q_σ` corresponding to `V_i`. -/
abbrev vIdx (i : Fin s.l) : Gen s := .inr (.inl i)

/-- The generator `Q_σ` corresponding to the `λ`-th generator of `𝔮`. -/
abbrev qIdx (i : Fin s.a) : Gen s := .inl i

/-- The unknowns of the system. -/
inductive Var : Type
  /-- The generators of `𝔭` (the first `a` of them generate `𝔮`). -/
  | Q : Gen s → Var
  /-- The element `S`. -/
  | S : Var
  /-- The coefficients of `S · Q_σ ∈ (V)`. -/
  | F : Gen s → Fin s.l → Var
  /-- The parameters completing the `V`'s. -/
  | Lv : Fin s.kv → Var
  /-- The coefficients of `y_i ^ N` on the `V`'s. -/
  | Gv : Fin s.e → Fin s.l → Var
  /-- The coefficients of `y_i ^ N` on the `Lv`'s. -/
  | Hv : Fin s.e → Fin s.kv → Var
  /-- The element `T`. -/
  | T : Var
  /-- The coefficients of `T · Q_{pick J}` on the products `Q_σ Q_τ`. -/
  | A : Subs s → Gen s → Gen s → Var
  /-- The coefficients of `T · Q_{pick J}` on the other generators of `𝔮` in `J`. -/
  | CJ : Subs s → Fin s.a → Var
  /-- The element `C`. -/
  | C : Var
  /-- The parameters of the non-membership relation. -/
  | Lz : Fin s.kz → Var
  /-- The coefficients of `y_i ^ N` on the `Q`'s in the non-membership relation. -/
  | Gz : Fin s.e → Gen s → Var
  /-- The coefficient of `y_i ^ N` on `T · C`. -/
  | Hz : Fin s.e → Var
  /-- The coefficients of `y_i ^ N` on the `Lz`'s. -/
  | Kz : Fin s.e → Fin s.kz → Var
  deriving DecidableEq, Fintype

/-- The relations of the system. -/
inductive Rel : Type
  /-- `S · Q_σ = Σ_i F_{σ i} V_i`. -/
  | S : Gen s → Rel
  /-- `y_i ^ N = Σ_j Gv_{i j} V_j + Σ_j Hv_{i j} Lv_j`. -/
  | V : Fin s.e → Rel
  /-- `T · Q_{pick J} = Σ_{σ τ} A_{J σ τ} Q_σ Q_τ + Σ_{λ ∈ J ∖ pick J} CJ_{J λ} Q_λ`. -/
  | T : Subs s → Rel
  /-- `y_i ^ N = Σ_σ Gz_{i σ} Q_σ + Hz_i T C + Σ_j Kz_{i j} Lz_j`. -/
  | Z : Fin s.e → Rel
  deriving DecidableEq, Fintype

variable {R₀ : Type u} [CommRing R₀] (y : Fin s.e → R₀)

section Relations

variable {A : Type v} [CommRing A] [Algebra R₀ A]

/-- The relations of the system, evaluated at an assignment `p` of its unknowns; a solution is an
assignment at which all of them vanish. -/
noncomputable def rel (p : Var s → A) : Rel s → A
  | .S σ => p .S * p (.Q σ) - ∑ i, p (.F σ i) * p (.Q (vIdx s i))
  | .V i => algebraMap R₀ A (y i) ^ s.N -
      (∑ j, p (.Gv i j) * p (.Q (vIdx s j)) + ∑ j, p (.Hv i j) * p (.Lv j))
  | .T J => p .T * p (.Q (qIdx s (s.pick J))) -
      (∑ σ, ∑ τ, p (.A J σ τ) * (p (.Q σ) * p (.Q τ)) +
        ∑ i ∈ J.1.erase (s.pick J), p (.CJ J i) * p (.Q (qIdx s i)))
  | .Z i => algebraMap R₀ A (y i) ^ s.N -
      (∑ σ, p (.Gz i σ) * p (.Q σ) + p (.Hz i) * (p .T * p .C) + ∑ j, p (.Kz i j) * p (.Lz j))

/-- The relations commute with algebra maps. -/
theorem rel_comp {A' : Type w} [CommRing A'] [Algebra R₀ A'] (f : A →ₐ[R₀] A')
    (p : Var s → A) (k : Rel s) : rel s y (f ∘ p) k = f (rel s y p k) := by
  cases k <;> simp [rel, map_sub, map_sum, map_mul, map_pow, map_add, AlgHom.commutes]

end Relations

/-- The finitely presented `R₀`-algebra defined by the system: polynomials in its unknowns modulo
its relations. -/
abbrev Alg : Type u :=
  MvPolynomial (Var s) R₀ ⧸
    Ideal.span (Set.range (rel s y (MvPolynomial.X : Var s → MvPolynomial (Var s) R₀)))

/-- The algebra of the system is finitely presented: finitely many unknowns and relations. -/
instance : Algebra.FinitePresentation R₀ (Alg s y) := by
  have hfg : (Ideal.span (Set.range
      (rel s y (MvPolynomial.X : Var s → MvPolynomial (Var s) R₀)))).FG :=
    Submodule.fg_span (Set.finite_range _)
  exact Algebra.FinitePresentation.quotient hfg

variable {A : Type v} [CommRing A] [Algebra R₀ A]

/-- Evaluating the relations at `p` is the image of the generic relations under any algebra map
sending each unknown to `p`. -/
private theorem rel_eq_map_rel_X (f : MvPolynomial (Var s) R₀ →ₐ[R₀] A) (p : Var s → A)
    (hf : ∀ v, f (MvPolynomial.X v) = p v) (k : Rel s) :
    rel s y p k = f (rel s y (MvPolynomial.X : Var s → MvPolynomial (Var s) R₀) k) := by
  rw [← rel_comp, show f ∘ MvPolynomial.X = p from funext hf]

/-- A solution of the system kills the relation ideal. -/
theorem lift_aux (p : Var s → A) (hp : ∀ k, rel s y p k = 0) :
    ∀ x ∈ Ideal.span (Set.range (rel s y (MvPolynomial.X : Var s → MvPolynomial (Var s) R₀))),
      MvPolynomial.aeval p x = 0 := by
  intro x hx
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨k, rfl⟩
    rw [← rel_eq_map_rel_X s y _ p (by simp)]
    exact hp k
  · exact map_zero _
  · intro x y _ _ hx hy
    rw [map_add, hx, hy, add_zero]
  · intro a x _ hx
    rw [smul_eq_mul, map_mul, hx, mul_zero]

/-- A solution of the system in `A` gives an `R₀`-algebra map out of `Alg`. -/
noncomputable def lift (p : Var s → A) (hp : ∀ k, rel s y p k = 0) : Alg s y →ₐ[R₀] A :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval p) (lift_aux s y p hp)

/-- The value of `lift` on an unknown. -/
@[simp]
theorem lift_mk_X (p : Var s → A) (hp : ∀ k, rel s y p k = 0) (v : Var s) :
    lift s y p hp (Ideal.Quotient.mk _ (MvPolynomial.X v)) = p v := by
  have h := DFunLike.congr_fun (Ideal.Quotient.liftₐ_comp (R₁ := R₀)
    (Ideal.span (Set.range (rel s y (MvPolynomial.X : Var s → MvPolynomial (Var s) R₀))))
    (MvPolynomial.aeval p) (lift_aux s y p hp)) (MvPolynomial.X v)
  rw [MvPolynomial.aeval_X] at h
  exact h

/-- The assignment of the unknowns defined by an algebra map out of `Alg`. -/
noncomputable def eval (φ : Alg s y →ₐ[R₀] A) : Var s → A :=
  fun v => φ (Ideal.Quotient.mk _ (MvPolynomial.X v))

/-- The assignment defined by an algebra map out of `Alg` is a solution of the system. -/
theorem rel_eval (φ : Alg s y →ₐ[R₀] A) (k : Rel s) : rel s y (eval s y φ) k = 0 := by
  have h := rel_eq_map_rel_X s y (φ.comp (Ideal.Quotient.mkₐ R₀ _)) (eval s y φ) (fun _ => rfl) k
  have hmem : rel s y (MvPolynomial.X : Var s → MvPolynomial (Var s) R₀) k ∈
      Ideal.span (Set.range (rel s y (MvPolynomial.X : Var s → MvPolynomial (Var s) R₀))) :=
    Ideal.subset_span ⟨k, rfl⟩
  rw [h, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem.2 hmem,
    map_zero]

/-- Evaluating the lift of a solution recovers the solution. -/
@[simp]
theorem eval_lift (p : Var s → A) (hp : ∀ k, rel s y p k = 0) : eval s y (lift s y p hp) = p := by
  funext v
  simp [eval]

end Stacks.ApproximationProperty.Certificate

end
