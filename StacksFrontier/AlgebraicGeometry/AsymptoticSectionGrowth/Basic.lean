module

public import Mathlib.Analysis.Polynomial.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.AsymptoticRiemannRoch

/-!
# Sections of an ample module grow without bound in positive dimension

[Stacks, Tag 0BJ8] (asymptotic Riemann–Roch) says that for `X` proper over a field `k` of
dimension `d` and `𝓛` ample and invertible,

`dim_k Γ(X, 𝓛^{⊗ n}) = deg_𝓛(X)/d! ⬝ n^d + (lower order terms)`

for all large `n`, with `deg_𝓛(X)/d! > 0`.  When `d ≥ 1` the right-hand side is a rational
polynomial in `n` of degree `d ≥ 1` with positive leading coefficient, so it tends to `+∞`.  This
file draws that conclusion.

It is the form in which asymptotic Riemann–Roch is used in [Stacks, Tag 0FD8]: there one needs
only that `dim_k Γ(Z, 𝓛|_Z^{⊗ n})` eventually exceeds any given bound, for `Z` the reduced closure
of a non-closed point (which has `d ≥ 1` by
`AlgebraicGeometry.Scheme.IdealSheafData.exists_topologicalKrullDim_subscheme_closure_eq`).

## Main results

* `AlgebraicGeometry.tendsto_finrank_globalSectionsOverField_atTop`: the dimensions of the twisted
  global sections tend to infinity.
* `AlgebraicGeometry.exists_forall_le_finrank_globalSectionsOverField`: the `∃ n₀, ∀ n ≥ n₀`
  restatement, which is the shape a caller wants.

## Implementation notes

The hypothesis `1 ≤ d` is necessary, not merely convenient: for `d = 0` asymptotic Riemann–Roch
gives `dim_k Γ(X, 𝓛^{⊗ n}) = deg_𝓛(X)/0!` eventually, a *constant*, and the conclusion is false.

The polynomial fed to `Polynomial.tendsto_atTop_of_leadingCoeff_nonneg` is `P + C a ⬝ X^d`, with
`a = deg_𝓛(X)/d!` and `P` the lower order terms supplied by
`AlgebraicGeometry.exists_degree_lt_eventually_finrank_globalSections_eq`.  Writing the leading
term on the *right* is what lets `Polynomial.degree_add_eq_right_of_degree_lt` and
`Polynomial.leadingCoeff_add_of_degree_lt` apply directly to `P.degree < d`.

The dimension hypothesis is the equality `topologicalKrullDim X = (d : WithBot ℕ∞)` rather than an
inequality because that is what `AlgebraicGeometry.asymptotic_riemann_roch` takes, and the degree
`AlgebraicGeometry.degreeWithRespectTo` appearing in its statement is indexed by it.

## References

* [Stacks Project, Tag 0BJ8](https://stacks.math.columbia.edu/tag/0BJ8)
* [Stacks Project, Tag 0FD8](https://stacks.math.columbia.edu/tag/0FD8)
-/

@[expose] public noncomputable section

open CategoryTheory Filter Polynomial
open Stacks.SheafOfModules.Invertible (tensorPower)

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
  (d : ℕ) (hdim : topologicalKrullDim X = (d : WithBot ℕ∞)) (hd : 1 ≤ d) (L : X.Modules)
  [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
  (hL : Scheme.Modules.IsAmple X L)

include hdim hd hL in
/-- **The dimensions of the twisted global sections tend to infinity.**  By [Stacks, Tag 0BJ8] they
are eventually the values at `n` of the rational polynomial `P + C a ⬝ X^d`, where `a =
deg_𝓛(X)/d!` is positive and `P` has degree `< d`; that polynomial has degree `d ≥ 1` and positive
leading coefficient `a`, so it tends to `+∞`. -/
public theorem tendsto_finrank_globalSectionsOverField_atTop :
    Tendsto (fun n : ℕ => Module.finrank k
      (globalSectionsOverField k f (tensorPower X.presheaf X.ringCatSheaf.2 L (n : ℤ))))
      atTop atTop := by
  obtain ⟨hpos, P, hdeg, heq⟩ := asymptotic_riemann_roch k f d hdim L hL
  set a : ℚ := (degreeWithRespectTo k f (𝟙 X) d hdim L hL : ℚ) / (d.factorial : ℚ) with ha
  set Q : Polynomial ℚ := P + Polynomial.C a * Polynomial.X ^ d with hQ
  have hane : a ≠ 0 := ne_of_gt hpos
  have hdegX : (Polynomial.C a * Polynomial.X ^ d).degree = (d : WithBot ℕ) :=
    Polynomial.degree_C_mul_X_pow d hane
  have hlt : P.degree < (Polynomial.C a * Polynomial.X ^ d).degree := hdegX ▸ hdeg
  have hdegQ : Q.degree = (d : WithBot ℕ) :=
    (Polynomial.degree_add_eq_right_of_degree_lt hlt).trans hdegX
  have hleadQ : Q.leadingCoeff = a :=
    (Polynomial.leadingCoeff_add_of_degree_lt hlt).trans (Polynomial.leadingCoeff_C_mul_X_pow a d)
  have hdegpos : 0 < Q.degree := by
    rw [hdegQ]
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hd
  have hQtendsto : Tendsto (fun x : ℚ => Q.eval x) atTop atTop :=
    Q.tendsto_atTop_of_leadingCoeff_nonneg hdegpos (hleadQ ▸ hpos.le)
  have hNat : Tendsto (fun n : ℕ => Q.eval (n : ℚ)) atTop atTop :=
    hQtendsto.comp tendsto_natCast_atTop_atTop
  have hRat : Tendsto (fun n : ℕ => (Module.finrank k
      (globalSectionsOverField k f
        (tensorPower X.presheaf X.ringCatSheaf.2 L (n : ℤ))) : ℚ)) atTop atTop := by
    refine hNat.congr' (heq.mono fun n hn => ?_)
    simp only [hn, hQ, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
    ring
  refine tendsto_atTop.mpr fun c => (hRat.eventually_ge_atTop (c : ℚ)).mono fun n hn => ?_
  exact_mod_cast hn

include hdim hd hL in
/-- **The `∃ n₀, ∀ n ≥ n₀` form of `tendsto_finrank_globalSectionsOverField_atTop`.**  For every
bound `c` the dimension of `Γ(X, 𝓛^{⊗ n})` exceeds `c` from some degree on. -/
public theorem exists_forall_le_finrank_globalSectionsOverField (c : ℕ) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → c ≤ Module.finrank k
      (globalSectionsOverField k f (tensorPower X.presheaf X.ringCatSheaf.2 L (n : ℤ))) :=
  eventually_atTop.mp
    ((tendsto_finrank_globalSectionsOverField_atTop k f d hdim hd L hL).eventually_ge_atTop c)

end AlgebraicGeometry

end
