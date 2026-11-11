module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.WeilTraceFormula

/-!
# Weil's trace formula in the étale cohomology of a curve modulo a prime power

Let `C` be a nonsingular projective curve over an algebraically closed field `k`, let
`φ : C → C` be a `k`-endomorphism of `C` distinct from the identity, and let `ℓ` be a prime
invertible in `k`. Then

  `∑_{i=0}^{2} (-1)^i Tr(φ^* | H^i(C, Z/ℓ^n Z)) = V(φ) mod ℓ^n`,

where `V(φ) = Δ_C · Γ_φ` is the intersection number on `C × C` of the diagonal with the graph of
`φ`.

The statement makes sense because each `H^i(C, Z/ℓ^n Z)` is a free `Z/ℓ^n Z`-module, so `φ^*`
acts on it by a square matrix and has a trace. The source computes the three traces one degree
at a time. In degree zero the action is trivial and the trace is `1`. The choice of a primitive
`ℓ^n`-th root of unity in `k` identifies `H^i(C, Z/ℓ^n Z)` with `H^i(C, μ_{ℓ^n})` compatibly
with the geometric Frobenius; since `H^1(C, μ_{ℓ^n}) = J[ℓ^n]` for `J` the jacobian of `C`, the
trace in degree one is `Tr_J(φ^*)` modulo `ℓ^n`; and since
`H^2(C, μ_{ℓ^n}) = Pic(C)/ℓ^n Pic(C) ≅ Z/ℓ^n Z` with `φ^*` acting as multiplication by
`deg φ`, the trace in degree two is `deg φ`. The alternating sum is therefore
`1 - Tr_J(φ^*) + deg φ`, and Weil's trace formula, Tag 03U1, identifies that with `V(φ)`.

The situation of Tag 03U1 is the datum `Stacks.EtaleCohomology.JacobianCorrespondence` together
with an endomorphism datum, exactly as Weil's formula itself is stated in this development: the
intersection pairing on the divisor classes of `C × C`, the trace form of `End(J)`, the classes
of the diagonal, of the two fibres through a base point and of the graph of `φ`, and the degree
of `φ`. Relative to that datum the three degreewise traces are the fields of
`Stacks.EtaleCohomology.JacobianCorrespondence.EtaleFrobeniusAction`, and the alternating sum is
computed here from Weil's formula.

This file is the abstract form of the computation. Tag 03U3 itself, for the étale cohomology of the
constant sheaf on an actual smooth proper curve with the freeness of the cohomology and the three
degreewise traces proved, is
`Stacks.EtaleCohomology.sum_trace_etaleConstantCohomologyPullback_eq_fixedPointIntersection` in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.WeilFormulaEtaleCohomologyCurve`.

## Main definitions

* `Stacks.EtaleCohomology.JacobianCorrespondence.EtaleFrobeniusAction` — the matrices of `φ^*`
  on the free `Z/ℓ^n Z`-modules `H^i(C, Z/ℓ^n Z)` for `i = 0, 1, 2`, together with the
  identification of their traces with `1`, with `Tr_J(φ^*)` and with `deg φ`.
* `Stacks.EtaleCohomology.JacobianCorrespondence.EtaleFrobeniusAction.trace` — the traces
  `Tr(φ^* | H^i(C, Z/ℓ^n Z))`.
* `Stacks.EtaleCohomology.JacobianCorrespondence.EtaleFrobeniusAction.alternatingTrace` — the
  alternating sum `∑_{i=0}^{2} (-1)^i Tr(φ^* | H^i(C, Z/ℓ^n Z))`.

## Main results

* `Stacks.EtaleCohomology.JacobianCorrespondence.EtaleFrobeniusAction.alternatingTrace_eq` —
  the alternating sum is `V(φ)` modulo `ℓ^n`.
* `Stacks.EtaleCohomology.projectiveLineEtaleFrobeniusAction` and
  `Stacks.EtaleCohomology.projectiveLine_alternatingTrace` — the data realised on the
  projective line, where `H^0` and `H^2` are free of rank one and `H^1` vanishes, for an
  endomorphism of every degree, and the value of the alternating sum there.

## Implementation notes

The cohomology in degree `i` is recorded by its rank over `Z/ℓ^n Z` and by the matrix of `φ^*`
in a basis, so the traces of the statement are *computed* from the data and not assumed; what is
assumed is their values, which are the three degreewise computations of the source. The
primality of `ℓ` is a field as well, since it is a hypothesis of the source: it is what makes
`μ_{ℓ^n}` étale over `k` and the cohomology free, the facts on which the three computations rest.
It is not used in the derivation of the alternating sum from Weil's formula.

The universes of the divisor classes and of `End(J)` are independent, as in the statement of
Weil's formula.

## References

* [Stacks Project, Tag 03U3](https://stacks.math.columbia.edu/tag/03U3)
* [Stacks Project, Tag 03U1](https://stacks.math.columbia.edu/tag/03U1)
-/

@[expose] public noncomputable section

universe u v

namespace Stacks.EtaleCohomology

namespace JacobianCorrespondence

variable {A : Type u} [AddCommGroup A] {E : Type v} [Ring E] (W : JacobianCorrespondence A E)

/-- The action of `φ^*` on the étale cohomology `H^i(C, Z/ℓ^n Z)` of a nonsingular projective
curve with coefficients in `Z/ℓ^n Z`, for `ℓ` a prime invertible in the base field: each
cohomology module is free, so `φ^*` acts on it by a square matrix, and the traces of those
matrices are the three degreewise values the source computes — `1` in degree zero,
`Tr_J(φ^*)` modulo `ℓ^n` in degree one, where `H^1(C, μ_{ℓ^n}) = J[ℓ^n]`, and `deg φ` in degree
two, where `H^2(C, μ_{ℓ^n}) = Pic(C)/ℓ^n Pic(C) ≅ Z/ℓ^n Z`.

See [Stacks Project, Tag 03U3](https://stacks.math.columbia.edu/tag/03U3). -/
public structure EtaleFrobeniusAction (D : W.EndomorphismData) (ℓ n : ℕ) where
  /-- The number `ℓ` is prime. This abstract datum has no base field, so the invertibility of
  `ℓ` in `k` is not recorded here; the curve statement
  `Stacks.EtaleCohomology.sum_trace_etaleConstantCohomologyPullback_eq_fixedPointIntersection`
  takes it as its argument `hℓ`. -/
  prime : Nat.Prime ℓ
  /-- The rank of the free `Z/ℓ^n Z`-module `H^0(C, Z/ℓ^n Z)`. -/
  rank₀ : ℕ
  /-- The rank of the free `Z/ℓ^n Z`-module `H^1(C, Z/ℓ^n Z)`. -/
  rank₁ : ℕ
  /-- The rank of the free `Z/ℓ^n Z`-module `H^2(C, Z/ℓ^n Z)`. -/
  rank₂ : ℕ
  /-- The matrix of `φ^*` on `H^0(C, Z/ℓ^n Z)` in a basis. -/
  matrix₀ : Matrix (Fin rank₀) (Fin rank₀) (ZMod (ℓ ^ n))
  /-- The matrix of `φ^*` on `H^1(C, Z/ℓ^n Z)` in a basis. -/
  matrix₁ : Matrix (Fin rank₁) (Fin rank₁) (ZMod (ℓ ^ n))
  /-- The matrix of `φ^*` on `H^2(C, Z/ℓ^n Z)` in a basis. -/
  matrix₂ : Matrix (Fin rank₂) (Fin rank₂) (ZMod (ℓ ^ n))
  /-- In degree zero the action of `φ^*` is trivial, so its trace is `1`. -/
  trace_matrix₀ : matrix₀.trace = 1
  /-- In degree one `H^1(C, μ_{ℓ^n}) = J[ℓ^n]`, so the trace of `φ^*` is the trace `Tr_J(φ^*)`
  of the induced endomorphism of the jacobian, reduced modulo `ℓ^n`. -/
  trace_matrix₁ : matrix₁.trace = (W.trace D.pullback : ZMod (ℓ ^ n))
  /-- In degree two `H^2(C, μ_{ℓ^n}) = Pic(C)/ℓ^n Pic(C) ≅ Z/ℓ^n Z` with `φ^*` acting as
  multiplication by `deg φ`, so the trace of `φ^*` is `deg φ`. -/
  trace_matrix₂ : matrix₂.trace = (D.degree : ZMod (ℓ ^ n))

namespace EtaleFrobeniusAction

variable {W} {D : W.EndomorphismData} {ℓ n : ℕ} (T : W.EtaleFrobeniusAction D ℓ n)

/-- The traces `Tr(φ^* | H^i(C, Z/ℓ^n Z))` of the action of `φ^*` on the étale cohomology of
`C`, in the degrees `i = 0, 1, 2`. -/
public def trace : Fin 3 → ZMod (ℓ ^ n) :=
  ![T.matrix₀.trace, T.matrix₁.trace, T.matrix₂.trace]

/-- The trace of `φ^*` in degree zero. -/
@[simp]
public theorem trace_zero : T.trace 0 = T.matrix₀.trace := rfl

/-- The trace of `φ^*` in degree one. -/
@[simp]
public theorem trace_one : T.trace 1 = T.matrix₁.trace := rfl

/-- The trace of `φ^*` in degree two. -/
@[simp]
public theorem trace_two : T.trace 2 = T.matrix₂.trace := rfl

/-- The alternating sum `∑_{i=0}^{2} (-1)^i Tr(φ^* | H^i(C, Z/ℓ^n Z))` of the traces of `φ^*`
on the étale cohomology of `C` with coefficients in `Z/ℓ^n Z`. -/
public def alternatingTrace : ZMod (ℓ ^ n) :=
  ∑ i : Fin 3, (-1) ^ (i : ℕ) * T.trace i

/-- **Weil's trace formula modulo `ℓ^n`, relative to the abstract datum.** In the situation of
Weil's theorem, Tag 03U1, let `ℓ` be a prime invertible in `k`. Then

  `∑_{i=0}^{2} (-1)^i Tr(φ^* | H^i(C, Z/ℓ^n Z)) = V(φ) mod ℓ^n`,

the alternating sum of the traces of `φ^*` on the étale cohomology of `C` with coefficients in
`Z/ℓ^n Z` being `1 - Tr_J(φ^*) + deg φ` by the three degreewise values recorded in the fields of
`Stacks.EtaleCohomology.JacobianCorrespondence.EtaleFrobeniusAction`, and that being `V(φ)` by
Weil's formula.

This is the computation relative to the abstract datum; the statement for the étale cohomology of
an actual curve, with the degreewise traces proved, is
`Stacks.EtaleCohomology.sum_trace_etaleConstantCohomologyPullback_eq_fixedPointIntersection`. -/
public theorem alternatingTrace_eq :
    T.alternatingTrace = (W.fixedPointNumber D : ZMod (ℓ ^ n)) := by
  rw [alternatingTrace, W.fixedPointNumber_eq, Fin.sum_univ_three]
  simp only [trace_zero, trace_one, trace_two, T.trace_matrix₀, T.trace_matrix₁,
    T.trace_matrix₂, Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one]
  push_cast
  ring

end EtaleFrobeniusAction

end JacobianCorrespondence

/-- The action of `φ^*` on the étale cohomology of the projective line, for an endomorphism of
degree `d`: the jacobian is trivial, so `H^1` vanishes, while `H^0` and `H^2` are free of rank
one with `φ^*` acting by `1` and by `d`. This exhibits the hypotheses of
`Stacks.EtaleCohomology.JacobianCorrespondence.EtaleFrobeniusAction` as consistent. -/
public def projectiveLineEtaleFrobeniusAction (ℓ n : ℕ) (hℓ : Nat.Prime ℓ) (d : ℤ) :
    projectiveLineJacobianCorrespondence.EtaleFrobeniusAction
      (projectiveLineEndomorphismData d) ℓ n where
  prime := hℓ
  rank₀ := 1
  rank₁ := 0
  rank₂ := 1
  matrix₀ := 1
  matrix₁ := 0
  matrix₂ := Matrix.of fun _ _ => (d : ZMod (ℓ ^ n))
  trace_matrix₀ := by simp
  trace_matrix₁ := by simp [projectiveLineJacobianCorrespondence]
  trace_matrix₂ := by simp [Matrix.trace_fin_one, projectiveLineEndomorphismData]

/-- On the projective line the alternating sum of the traces of `φ^*` on the étale cohomology is
`1 + d` for an endomorphism of degree `d`, which is the number of fixed points of such an
endomorphism, modulo `ℓ^n`. -/
public theorem projectiveLine_alternatingTrace (ℓ n : ℕ) (hℓ : Nat.Prime ℓ) (d : ℤ) :
    (projectiveLineEtaleFrobeniusAction ℓ n hℓ d).alternatingTrace
      = ((1 + d : ℤ) : ZMod (ℓ ^ n)) := by
  rw [JacobianCorrespondence.EtaleFrobeniusAction.alternatingTrace_eq,
    projectiveLine_fixedPointNumber]

end Stacks.EtaleCohomology

end
