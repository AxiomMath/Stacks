module

public import Mathlib.Algebra.Module.RingHom
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Ring.Equiv
public import StacksFrontier.Cotangent.Biderivation

/-!
# The Stacks 09CF erratum: a bimodule and values admitting no biderivation

Stacks tag 09CF asserts that for a polynomial ring `P = A[S]`, a `(P, P)`-bimodule `M` over `A`
and *arbitrary* prescribed values `m s ∈ M` there is a unique `A`-biderivation `D : P → M` with
`D (X s) = m s`. The existence half of that assertion is a Stacks erratum: it fails as soon as
the two actions of `P` on `M` differ. Uniqueness survives, and
`Biderivation.existsUnique_mvPolynomial` is the corrected statement, which adds the hypothesis
`Biderivation.IsCompatibleOnVars` that commutativity of the variables forces.

This file is the machine-checked refutation. The counterexample is

`P = k[x, y]` and `M = k`, the left action of `P` being evaluation at `(1, 0)` and the right
action evaluation at `(0, 0)`, with the prescribed values `m x = 0` and `m y = 1`.

The Leibniz rule reads `D (p * q) = p • D q + MulOpposite.op q • D p`, so a biderivation with
these values would have `D (x * y) = x • 1 + MulOpposite.op y • 0 = 1` and
`D (y * x) = y • 0 + MulOpposite.op x • 1 = 0`, while `x * y = y * x` in `k[x, y]`.

## Main definitions

* `Biderivation.ErratumModule`: a copy of `k` carrying the two actions above. It must be a type
  synonym, since these are two *different* `k[x, y]`-module structures on `k`.
* `Biderivation.erratumValues`: the prescribed values `m x = 0`, `m y = 1`.

## Main results

* `Biderivation.not_exists_biderivation_erratum`: no biderivation `k[x, y] → ErratumModule k`
  sends `x` to `0` and `y` to `1`. This refutes the existence claim of Stacks 09CF.
* `Biderivation.not_exists_biderivation_erratumValues`: the same refutation phrased for the
  family `Biderivation.erratumValues` of prescribed values.
* `Biderivation.not_isCompatibleOnVars_erratumValues`: the compatibility equations that the
  corrected statement adds as a hypothesis do fail for these values, so the obstruction is real.
* `Biderivation.existsUnique_biderivation_erratumModule_zero`: the counterexample bimodule is
  not degenerate — biderivations into it do exist.
* `Biderivation.not_forall_existsUnique_mvPolynomial_erratumModule`: the negation of the
  unrestricted assertion of the source, quantified over the prescribed values.

## References

* [Stacks Project, Tag 09CF](https://stacks.math.columbia.edu/tag/09CF)
-/

@[expose] public section

universe u

namespace Biderivation

open MvPolynomial

/-- The underlying type of the bimodule refuting the existence claim of Stacks 09CF: a copy of
`k`, which carries two *different* `k[x, y]`-module structures — evaluation at `(1, 0)` on the
left and evaluation at `(0, 0)` on the right — and so cannot be the bare type `k`. -/
def ErratumModule (k : Type u) : Type u := k

namespace ErratumModule

/-- The point `(1, 0)` of `k²`, at which the left action of `k[x, y]` on `ErratumModule k`
evaluates. -/
def leftPoint (k : Type u) [CommRing k] : Fin 2 → k := fun i ↦ if i = 0 then 1 else 0

/-- The point `(0, 0)` of `k²`, at which the right action of `k[x, y]` on `ErratumModule k`
evaluates. -/
def rightPoint (k : Type u) [CommRing k] : Fin 2 → k := fun _ ↦ 0

variable {k : Type u} [CommRing k]

/-- The first coordinate of `leftPoint k` is `1`. -/
@[simp]
theorem leftPoint_zero : leftPoint k 0 = 1 := if_pos rfl

/-- The second coordinate of `leftPoint k` is `0`. -/
@[simp]
theorem leftPoint_one : leftPoint k 1 = 0 := if_neg (by decide)

/-- Every coordinate of `rightPoint k` is `0`. -/
@[simp]
theorem rightPoint_apply (i : Fin 2) : rightPoint k i = 0 := rfl

/-- `ErratumModule k` is the commutative ring `k`. -/
instance : CommRing (ErratumModule k) := inferInstanceAs (CommRing k)

/-- `ErratumModule k` is nontrivial when `k` is. -/
instance [Nontrivial k] : Nontrivial (ErratumModule k) := inferInstanceAs (Nontrivial k)

/-- `ErratumModule k` is a `k`-module through the multiplication of `k`. -/
instance : Module k (ErratumModule k) := inferInstanceAs (Module k k)

/-- The left action of `k[x, y]` on `ErratumModule k`: evaluation at `(1, 0)`. -/
noncomputable instance : Module (MvPolynomial (Fin 2) k) (ErratumModule k) :=
  Module.compHom (ErratumModule k) (MvPolynomial.eval (leftPoint k))

/-- The right action of `k[x, y]` on `ErratumModule k`: evaluation at `(0, 0)`, written as a
left action of the opposite ring. -/
noncomputable instance : Module (MvPolynomial (Fin 2) k)ᵐᵒᵖ (ErratumModule k) :=
  Module.compHom (ErratumModule k)
    ((MvPolynomial.eval (rightPoint k)).comp
      (RingEquiv.toOpposite (MvPolynomial (Fin 2) k)).symm.toRingHom)

/-- The left action of `p : k[x, y]` on `ErratumModule k` is multiplication by the value of `p`
at `(1, 0)`. -/
theorem smul_def (p : MvPolynomial (Fin 2) k) (x : ErratumModule k) :
    p • x = MvPolynomial.eval (leftPoint k) p • x := rfl

/-- The right action of `q : k[x, y]ᵐᵒᵖ` on `ErratumModule k` is multiplication by the value of
`q.unop` at `(0, 0)`. -/
theorem op_smul_def (q : (MvPolynomial (Fin 2) k)ᵐᵒᵖ) (x : ErratumModule k) :
    q • x = MvPolynomial.eval (rightPoint k) q.unop • x := rfl

/-- The left `k[x, y]`-action on `ErratumModule k` is compatible with the `k`-action. -/
instance : IsScalarTower k (MvPolynomial (Fin 2) k) (ErratumModule k) where
  smul_assoc a p x := by
    simp only [smul_def, MvPolynomial.smul_eq_C_mul, MvPolynomial.eval_C, mul_smul]

/-- The right `k[x, y]`-action on `ErratumModule k` is compatible with the `k`-action. -/
instance : IsScalarTower k (MvPolynomial (Fin 2) k)ᵐᵒᵖ (ErratumModule k) where
  smul_assoc a q x := by
    simp only [op_smul_def, MulOpposite.unop_smul, MvPolynomial.smul_eq_C_mul, map_mul,
      MvPolynomial.eval_C, mul_smul]

/-- The left and right actions of `k[x, y]` on `ErratumModule k` commute, so `ErratumModule k`
is a `(k[x, y], k[x, y])`-bimodule. -/
instance : SMulCommClass (MvPolynomial (Fin 2) k) (MvPolynomial (Fin 2) k)ᵐᵒᵖ
    (ErratumModule k) where
  smul_comm p q x := by
    simp only [smul_def, op_smul_def, smul_smul, mul_comm]

end ErratumModule

section Erratum

open ErratumModule

variable (k : Type u) [CommRing k]

/-- The values of the Stacks 09CF counterexample prescribed on the variables of `k[x, y]`:
`m x = 0` and `m y = 1`. -/
def erratumValues : Fin 2 → ErratumModule k := fun i ↦ if i = 0 then 0 else 1

/-- The value prescribed on `x` is `0`. -/
@[simp]
theorem erratumValues_zero : erratumValues k 0 = 0 := if_pos rfl

/-- The value prescribed on `y` is `1`. -/
@[simp]
theorem erratumValues_one : erratumValues k 1 = 1 := if_neg (by decide)

/-- The counterexample bimodule is not degenerate: the zero family of prescribed values is
compatible, so biderivations `k[x, y] → ErratumModule k` do exist, and the failure below is a
failure for the particular values `erratumValues k` and not for lack of any biderivation. -/
theorem existsUnique_biderivation_erratumModule_zero :
    ∃! D : Biderivation k (MvPolynomial (Fin 2) k) (ErratumModule k), ∀ s, D (X s) = 0 :=
  existsUnique_mvPolynomial _ fun _ _ ↦ by simp

variable [Nontrivial k]

/-- **The Stacks 09CF erratum, refuted.** For the bimodule `ErratumModule k` — a copy of `k` on
which `k[x, y]` acts by evaluation at `(1, 0)` on the left and at `(0, 0)` on the right — there
is *no* `k`-biderivation sending `x` to `0` and `y` to `1`, although the source asserts that
every family of prescribed values on the variables is realized.

Indeed the Leibniz rule gives `D (x * y) = x • D y + MulOpposite.op y • D x = 1` and
`D (y * x) = y • D x + MulOpposite.op x • D y = 0`, while `x * y = y * x`. -/
theorem not_exists_biderivation_erratum :
    ¬ ∃ D : Biderivation k (MvPolynomial (Fin 2) k) (ErratumModule k),
      D (X 0) = 0 ∧ D (X 1) = 1 := by
  rintro ⟨D, h0, h1⟩
  have hc := isCompatibleOnVars_X D 0 1
  simp only [h0, h1, smul_def, op_smul_def, MulOpposite.unop_op, MvPolynomial.eval_X,
    leftPoint_zero, rightPoint_apply, one_smul, zero_smul, smul_zero, add_zero] at hc
  exact one_ne_zero hc

/-- **The Stacks 09CF erratum, refuted**, phrased for the family `erratumValues` of prescribed
values on the variables: no biderivation realizes it. -/
theorem not_exists_biderivation_erratumValues :
    ¬ ∃ D : Biderivation k (MvPolynomial (Fin 2) k) (ErratumModule k),
      ∀ s, D (X s) = erratumValues k s := by
  rintro ⟨D, hD⟩
  exact not_exists_biderivation_erratum k
    ⟨D, (hD 0).trans (erratumValues_zero k), (hD 1).trans (erratumValues_one k)⟩

/-- The compatibility equations of `Biderivation.IsCompatibleOnVars` — the hypothesis the
corrected `Biderivation.existsUnique_mvPolynomial` adds, absent from the source — really do fail
for the counterexample, so the obstruction is not vacuous. -/
theorem not_isCompatibleOnVars_erratumValues :
    ¬ IsCompatibleOnVars k (erratumValues k) := by
  intro hc
  obtain ⟨D, hD, -⟩ := existsUnique_mvPolynomial (erratumValues k) hc
  exact not_exists_biderivation_erratumValues k ⟨D, hD⟩

/-- **The Stacks 09CF erratum, refuted** in the exact shape the source asserts: it is not the
case that every family of prescribed values on the variables of `k[x, y]` is realized by a
unique biderivation into `ErratumModule k`. -/
theorem not_forall_existsUnique_mvPolynomial_erratumModule :
    ¬ ∀ m : Fin 2 → ErratumModule k,
      ∃! D : Biderivation k (MvPolynomial (Fin 2) k) (ErratumModule k), ∀ s, D (X s) = m s := by
  intro h
  obtain ⟨D, hD, -⟩ := h (erratumValues k)
  exact not_exists_biderivation_erratumValues k ⟨D, hD⟩

end Erratum

end Biderivation

end
