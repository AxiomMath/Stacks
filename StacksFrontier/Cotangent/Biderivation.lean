module

public import Mathlib.Algebra.Module.Bimodule
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Data.Finsupp.Multiset
public import StacksCore.Tactic.StacksAttribute

/-!
# Biderivations

Let `B` be an algebra over a commutative semiring `A`, and let `M` be a `(B, B)`-bimodule over
`A`. An `A`-biderivation from `B` to `M` is an `A`-linear map satisfying the Leibniz rule, with
the two terms using the left and right actions of `B` on `M` respectively.

A biderivation of a polynomial algebra `A[S]` is determined by its values on the variables,
and every family of values which is *compatible* — meaning that the two readings of the
Leibniz rule for `X s * X t = X t * X s` agree — is realized by exactly one biderivation.

## Main definitions

* `Biderivation`: the type of `A`-biderivations from `B` to a bimodule `M`.
* `Biderivation.IsCompatibleOnVars`: the compatibility equations that commutativity of the
  polynomial variables forces on a family of prescribed values.

## Main results

* `Biderivation.leibniz`: the defining Leibniz rule.
* `Biderivation.ext_mvPolynomial`: a biderivation of a polynomial algebra is determined by its
  values on the variables.
* `Biderivation.existsUnique_mvPolynomial`: the existence and uniqueness of a biderivation of
  `A[S]` with prescribed compatible values on the variables.
* `Biderivation.existsUnique_mvPolynomial_iff`: compatibility is also necessary.

## Implementation notes

The right `B`-action is represented in Mathlib as a left action of `Bᵐᵒᵖ`. The two
`IsScalarTower` assumptions say that both `B`-actions extend the given `A`-module structure,
while `SMulCommClass` says that they commute. The definition is stated for semirings and
additive commutative monoids, since additive inverses play no role; the rings of the source are
a specialization.

The source states the existence and uniqueness of a biderivation of `A[S]` with arbitrary
prescribed values on the variables. For a bimodule whose two actions differ that is **false**:
commutativity of the variables forces the equations of `Biderivation.IsCompatibleOnVars` on the
values, and `Biderivation.existsUnique_mvPolynomial_iff` shows they are exactly the obstruction.
`Biderivation.existsUnique_mvPolynomial_of_op_smul_eq` recovers the source's unrestricted
assertion when the two actions agree, which is the case in which the source applies it.

The falsity of the existence half is a Stacks erratum, and the
refutation is machine-checked in `StacksFrontier.Cotangent.BiderivationErratum`: the counterexample
takes `P = k[x, y]` acting on `M = k` by evaluation at `(1, 0)` on the left and at `(0, 0)` on
the right, with prescribed values `m x = 0` and `m y = 1`, for which the Leibniz rule forces
`D (x * y) = 1` and `D (y * x) = 0` although `x * y = y * x`. The theorem is
`Biderivation.not_exists_biderivation_erratum`; the negation of the source's assertion read as a
statement about all prescribed values is
`Biderivation.not_forall_existsUnique_mvPolynomial_erratumModule`. Everything in the present
file is the corrected statement, which that counterexample does not touch.

The biderivation is built by prescribing its value on a word `s₁ ⋯ sₙ` in the variables by
iterating the Leibniz rule, checking that the value is invariant under permuting the word —
this is where compatibility enters, through the transposition case — and then reading a monomial
as the word given by its exponents.

## References

* [Stacks Project, Tag 09CE](https://stacks.math.columbia.edu/tag/09CE)
* [Stacks Project, Tag 09CF](https://stacks.math.columbia.edu/tag/09CF)
-/

@[expose] public section

universe u v w

/-- An `A`-biderivation from an `A`-algebra `B` to a `(B, B)`-bimodule `M` is
an `A`-linear map satisfying the Leibniz rule for the left and right actions. -/
@[ext, stacks 09CE, ega "0 20.1.2", ega "0 20.1.1"]
structure Biderivation (A : Type u) (B : Type v) (M : Type w)
    [CommSemiring A] [Semiring B] [AddCommMonoid M] [Algebra A B]
    [Module A M] [Module B M] [Module Bᵐᵒᵖ M]
    [IsScalarTower A B M] [IsScalarTower A Bᵐᵒᵖ M]
    [SMulCommClass B Bᵐᵒᵖ M]
    extends B →ₗ[A] M where
  protected leibniz (x y : B) :
    toLinearMap (x * y) = x • toLinearMap y + MulOpposite.op y • toLinearMap x

namespace Biderivation

variable {A : Type u} {B : Type v} {M : Type w}
variable [CommSemiring A] [Semiring B] [AddCommMonoid M] [Algebra A B]
variable [Module A M] [Module B M] [Module Bᵐᵒᵖ M]
variable [IsScalarTower A B M] [IsScalarTower A Bᵐᵒᵖ M]
variable [SMulCommClass B Bᵐᵒᵖ M]

/-- A biderivation is a function from `B` to `M`, via its underlying linear map. -/
instance : FunLike (Biderivation A B M) B M where
  coe D := D.toLinearMap
  coe_injective D E h := by
    have h' : D.toLinearMap = E.toLinearMap := LinearMap.ext fun x => congrFun h x
    cases D
    cases E
    cases h'
    rfl

/-- A biderivation is additive and sends `0` to `0`. -/
instance : AddMonoidHomClass (Biderivation A B M) B M where
  map_add D := D.toLinearMap.map_add'
  map_zero D := D.toLinearMap.map_zero

/-- The `A`-linear map underlying a biderivation. -/
instance : Coe (Biderivation A B M) (B →ₗ[A] M) :=
  ⟨Biderivation.toLinearMap⟩

end Biderivation

/-! ## Biderivations of a polynomial algebra -/

namespace Biderivation

open MvPolynomial

/-- **Stacks 09CF.** The equations that commutativity of the polynomial variables forces on the
values of a biderivation of `A[S]`: the Leibniz rule applied to the two readings of
`X s * X t = X t * X s`. For a bimodule whose two actions agree they hold automatically.

The source imposes no such condition; that omission is a Stacks erratum, and these equations
really can fail, as
`Biderivation.not_isCompatibleOnVars_erratumValues` shows for the counterexample of
`StacksFrontier.Cotangent.BiderivationErratum`. -/
@[stacks 09CF "the compatibility equations the values on the variables must satisfy"]
def IsCompatibleOnVars (A : Type u) {S : Type v} {M : Type w} [CommSemiring A]
    [AddCommGroup M] [Module (MvPolynomial S A) M] [Module (MvPolynomial S A)ᵐᵒᵖ M]
    (m : S → M) : Prop :=
  ∀ s t : S,
    (X s : MvPolynomial S A) • m t + MulOpposite.op (X t : MvPolynomial S A) • m s =
      (X t : MvPolynomial S A) • m s + MulOpposite.op (X s : MvPolynomial S A) • m t

section MvPolynomial

variable {A : Type u} {S : Type v} {M : Type w}
variable [CommSemiring A] [AddCommGroup M]
variable [Module A M] [Module (MvPolynomial S A) M] [Module (MvPolynomial S A)ᵐᵒᵖ M]
variable [IsScalarTower A (MvPolynomial S A) M] [IsScalarTower A (MvPolynomial S A)ᵐᵒᵖ M]
variable [SMulCommClass (MvPolynomial S A) (MvPolynomial S A)ᵐᵒᵖ M]

/-- The values of a biderivation on the variables satisfy the compatibility equations, so those
equations are necessary and not merely sufficient for `existsUnique_mvPolynomial`. -/
theorem isCompatibleOnVars_X (D : Biderivation A (MvPolynomial S A) M) :
    IsCompatibleOnVars A fun s ↦ D (X s) := by
  intro s t
  have h := D.leibniz (X s : MvPolynomial S A) (X t : MvPolynomial S A)
  rw [mul_comm (X s : MvPolynomial S A)] at h
  exact h.symm.trans (D.leibniz _ _)

/-- A biderivation of a polynomial algebra is determined by its values on the variables. -/
theorem ext_mvPolynomial (D E : Biderivation A (MvPolynomial S A) M)
    (hX : ∀ s, D (X s) = E (X s)) : D = E := by
  apply Biderivation.ext
  ext p
  induction p using MvPolynomial.induction_on with
  | C a =>
      have h (F : Biderivation A (MvPolynomial S A) M) : F.toLinearMap 1 = 0 := by
        simpa using F.leibniz 1 1
      show D.toLinearMap (C a) = E.toLinearMap (C a)
      simp [MvPolynomial.C_eq_smul_one, h D, h E]
  | add p q hp hq =>
      show D.toLinearMap (p + q) = E.toLinearMap (p + q)
      change D.toLinearMap p = E.toLinearMap p at hp
      change D.toLinearMap q = E.toLinearMap q at hq
      rw [D.toLinearMap.map_add, E.toLinearMap.map_add, hp, hq]
  | mul_X p s hp =>
      show D.toLinearMap (p * X s) = E.toLinearMap (p * X s)
      rw [D.leibniz, E.leibniz]
      change D.toLinearMap p = E.toLinearMap p at hp
      rw [show D.toLinearMap (X s) = E.toLinearMap (X s) from hX s, hp]

end MvPolynomial

noncomputable section Construction

/-- The product of the variables of a word in the index set, as a polynomial. -/
private def wordProduct {A S : Type*} [CommSemiring A] (l : List S) : MvPolynomial S A :=
  (l.map (X (R := A))).prod

/-- The value that iterating the Leibniz rule forces on the product of the variables of a word,
given prescribed values on the variables. -/
private def wordValue {A S M : Type*} [CommSemiring A] [AddCommGroup M] [Module A M]
    [Module (MvPolynomial S A) M] [Module (MvPolynomial S A)ᵐᵒᵖ M] (m : S → M) : List S → M
  | [] => 0
  | s :: l => (X s : MvPolynomial S A) • wordValue (A := A) (S := S) (M := M) m l +
      MulOpposite.op (wordProduct (A := A) (S := S) l) • m s

private theorem wordProduct_append {A S : Type*} [CommSemiring A] (l r : List S) :
    wordProduct (A := A) (S := S) (l ++ r) = wordProduct (A := A) l * wordProduct (A := A) r := by
  simp [wordProduct, List.map_append, List.prod_append]

private theorem wordValue_append
    {A S M : Type*} [CommSemiring A] [AddCommGroup M] [Module A M]
    [Module (MvPolynomial S A) M] [Module (MvPolynomial S A)ᵐᵒᵖ M]
    [SMulCommClass (MvPolynomial S A) (MvPolynomial S A)ᵐᵒᵖ M] (m : S → M) (l r : List S) :
    wordValue (A := A) (S := S) (M := M) m (l ++ r) =
      wordProduct (A := A) (S := S) l • wordValue (A := A) (S := S) (M := M) m r +
        MulOpposite.op (wordProduct (A := A) (S := S) r) •
          wordValue (A := A) (S := S) (M := M) m l := by
  induction l with
  | nil => simp [wordValue, wordProduct]
  | cons s l ih =>
      simp only [List.cons_append, wordValue]
      rw [ih, wordProduct_append, smul_add, smul_comm (X s) (MulOpposite.op (wordProduct r))]
      simp [wordProduct, List.map_cons, List.prod_cons, MulOpposite.op_mul,
        smul_smul, mul_comm, add_assoc]

private theorem wordValue_perm
    {A S M : Type*} [CommSemiring A] [AddCommGroup M] [Module A M]
    [Module (MvPolynomial S A) M] [Module (MvPolynomial S A)ᵐᵒᵖ M]
    [SMulCommClass (MvPolynomial S A) (MvPolynomial S A)ᵐᵒᵖ M]
    (m : S → M) (hcomm : IsCompatibleOnVars A m) {l r : List S} (h : l.Perm r) :
    wordValue (A := A) (S := S) (M := M) m l = wordValue (A := A) (S := S) (M := M) m r := by
  induction h with
  | nil => rfl
  | cons a h ih =>
      simp only [wordValue]
      rw [ih]
      congr 1
      exact congrArg (fun p : MvPolynomial S A ↦
          (MulOpposite.op p : (MvPolynomial S A)ᵐᵒᵖ) • m a) <|
        by simpa [wordProduct] using (h.map fun s ↦ (X s : MvPolynomial S A)).prod_eq
  | swap a b l =>
      simp only [wordValue, wordProduct, List.map_cons, List.prod_cons,
        smul_add, smul_smul, MulOpposite.op_mul]
      simp only [mul_comm (X a) (X b : MvPolynomial S A)]
      have h2 := congrArg (fun z : M ↦
          (MulOpposite.op (wordProduct (A := A) (S := S) l) :
            (MvPolynomial S A)ᵐᵒᵖ) • z) (hcomm a b)
      simp only [smul_add] at h2
      have hba := smul_comm (X b : MvPolynomial S A)
        (MulOpposite.op (wordProduct (A := A) (S := S) l)) (m a)
      have hab := smul_comm (X a : MvPolynomial S A)
        (MulOpposite.op (wordProduct (A := A) (S := S) l)) (m b)
      simp only [wordProduct] at h2 hba hab
      rw [hba, hab, ← smul_smul, ← smul_smul, ← smul_smul]
      simpa [add_assoc] using congrArg (fun z : M ↦
        ((X b : MvPolynomial S A) • ((X a : MvPolynomial S A) •
            wordValue (A := A) (S := S) (M := M) m l)) + z) h2.symm
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

/-- A word in the variables whose product is the given monomial. -/
private def monomialWord {S : Type*} (e : S →₀ ℕ) : List S := e.toMultiset.toList

private theorem monomialWord_product {A S : Type*} [CommSemiring A] (e : S →₀ ℕ) :
    wordProduct (monomialWord e) = monomial e (1 : A) := by
  classical
  unfold wordProduct monomialWord
  rw [Multiset.prod_map_toList, Finset.prod_multiset_map_count, Finsupp.toFinset_toMultiset]
  simp_rw [Finsupp.count_toMultiset]
  exact MvPolynomial.prod_X_pow_eq_monomial

private theorem monomialWord_add_perm {S : Type*} (e f : S →₀ ℕ) :
    List.Perm (monomialWord (e + f)) (monomialWord e ++ monomialWord f) := by
  apply Multiset.coe_eq_coe.mp
  show ((Finsupp.toMultiset (e + f)).toList : Multiset S) =
    ((Finsupp.toMultiset e).toList ++ (Finsupp.toMultiset f).toList : List S)
  rw [Multiset.coe_toList, ← Multiset.coe_add, Multiset.coe_toList, Multiset.coe_toList,
    Finsupp.toMultiset_add]

private theorem wordValue_monomialWord_add
    {A S M : Type*} [CommSemiring A] [AddCommGroup M] [Module A M]
    [Module (MvPolynomial S A) M] [Module (MvPolynomial S A)ᵐᵒᵖ M]
    [SMulCommClass (MvPolynomial S A) (MvPolynomial S A)ᵐᵒᵖ M]
    (m : S → M) (hcomm : IsCompatibleOnVars A m) (e f : S →₀ ℕ) :
    wordValue (A := A) (S := S) (M := M) m (monomialWord (e + f)) =
      monomial e (1 : A) • wordValue (A := A) (S := S) (M := M) m (monomialWord f) +
        MulOpposite.op (monomial f (1 : A)) •
          wordValue (A := A) (S := S) (M := M) m (monomialWord e) := by
  simpa only [monomialWord_product] using
    (wordValue_perm m hcomm (monomialWord_add_perm e f)).trans
      (wordValue_append m (monomialWord e) (monomialWord f))

/-- The `A`-linear map prescribed by the values on the variables, monomial by monomial. -/
private def mvPolynomialLinearMap
    {A S M : Type*} [CommSemiring A] [AddCommGroup M] [Module A M]
    [Module (MvPolynomial S A) M] [Module (MvPolynomial S A)ᵐᵒᵖ M]
    [SMulCommClass (MvPolynomial S A) (MvPolynomial S A)ᵐᵒᵖ M]
    (m : S → M) : MvPolynomial S A →ₗ[A] M :=
  Finsupp.lsum A (fun e : S →₀ ℕ ↦
    (LinearMap.ringLmapEquivSelf A A M).symm
      (wordValue (A := A) (S := S) (M := M) m (monomialWord e))) ∘ₗ
      (AddMonoidAlgebra.coeffLinearEquiv A).toLinearMap

private theorem mvPolynomialLinearMap_monomial
    {A S M : Type*} [CommSemiring A] [AddCommGroup M] [Module A M]
    [Module (MvPolynomial S A) M] [Module (MvPolynomial S A)ᵐᵒᵖ M]
    [SMulCommClass (MvPolynomial S A) (MvPolynomial S A)ᵐᵒᵖ M]
    (m : S → M) (e : S →₀ ℕ) (a : A) :
    mvPolynomialLinearMap m (monomial e a) =
      a • wordValue (A := A) (S := S) (M := M) m (monomialWord e) :=
  MvPolynomial.sum_monomial_eq (map_zero _)

private theorem mvPolynomialLinearMap_monomial_mul_monomial
    {A S M : Type*} [CommSemiring A] [AddCommGroup M] [Module A M]
    [Module (MvPolynomial S A) M] [Module (MvPolynomial S A)ᵐᵒᵖ M]
    [IsScalarTower A (MvPolynomial S A) M] [IsScalarTower A (MvPolynomial S A)ᵐᵒᵖ M]
    [SMulCommClass (MvPolynomial S A) (MvPolynomial S A)ᵐᵒᵖ M]
    (m : S → M) (hcomm : IsCompatibleOnVars A m) (e f : S →₀ ℕ) (a b : A) :
    mvPolynomialLinearMap m (monomial e a * monomial f b) =
      monomial e a • mvPolynomialLinearMap m (monomial f b) +
        MulOpposite.op (monomial f b) • mvPolynomialLinearMap m (monomial e a) := by
  have h (g : S →₀ ℕ) (c : A) : monomial g c = c • monomial g (1 : A) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [monomial_mul_monomial, mvPolynomialLinearMap_monomial, mvPolynomialLinearMap_monomial,
    mvPolynomialLinearMap_monomial, wordValue_monomialWord_add (m := m) hcomm, h e a, h f b]
  simp only [MulOpposite.op_smul, smul_assoc, smul_add, mul_smul,
    smul_comm b (monomial e (1 : A)), smul_comm (MulOpposite.op (monomial f (1 : A))) a,
    smul_comm a b]

private theorem mvPolynomialLinearMap_leibniz
    {A S M : Type*} [CommSemiring A] [AddCommGroup M] [Module A M]
    [Module (MvPolynomial S A) M] [Module (MvPolynomial S A)ᵐᵒᵖ M]
    [IsScalarTower A (MvPolynomial S A) M] [IsScalarTower A (MvPolynomial S A)ᵐᵒᵖ M]
    [SMulCommClass (MvPolynomial S A) (MvPolynomial S A)ᵐᵒᵖ M]
    (m : S → M) (hcomm : IsCompatibleOnVars A m) (p q : MvPolynomial S A) :
    mvPolynomialLinearMap m (p * q) =
      p • mvPolynomialLinearMap m q + MulOpposite.op q • mvPolynomialLinearMap m p := by
  induction p using MvPolynomial.induction_on' with
  | monomial e a =>
      induction q using MvPolynomial.induction_on' with
      | monomial f b => exact mvPolynomialLinearMap_monomial_mul_monomial m hcomm e f a b
      | add q r hq hr =>
          simp only [mul_add, map_add, hq, hr, add_smul, smul_add, MulOpposite.op_add]
          abel
  | add p r hp hr =>
      simp only [add_mul, map_add, hp, hr, add_smul, smul_add]
      abel

end Construction

section MvPolynomial

variable {A : Type u} {S : Type v} {M : Type w}
variable [CommSemiring A] [AddCommGroup M]
variable [Module A M] [Module (MvPolynomial S A) M] [Module (MvPolynomial S A)ᵐᵒᵖ M]
variable [IsScalarTower A (MvPolynomial S A) M] [IsScalarTower A (MvPolynomial S A)ᵐᵒᵖ M]
variable [SMulCommClass (MvPolynomial S A) (MvPolynomial S A)ᵐᵒᵖ M]

/-- **Stacks 09CF.** Let `P = A[S]` be a polynomial ring over `A` and let `M` be a `(P, P)`
bimodule over `A`. Given `m s ∈ M` for `s ∈ S` satisfying the compatibility equations that
commutativity of the variables forces, there is a unique `A`-biderivation `P → M` sending
`X s` to `m s`.

This is the corrected form of the tag. The source prescribes the values `m s` with no condition
at all, and the existence half of that unrestricted claim is false: it is a Stacks erratum,
refuted by `Biderivation.not_exists_biderivation_erratum` in
`StacksFrontier.Cotangent.BiderivationErratum`, which exhibits `k[x, y]` acting on `k` by
evaluation at `(1, 0)` on the left and at `(0, 0)` on the right and prescribed values `0` and
`1` admitting no biderivation. Uniqueness is unaffected, and by
`Biderivation.existsUnique_mvPolynomial_iff` the compatibility hypothesis below is not merely
sufficient but exactly the obstruction. -/
@[stacks 09CF "existence and uniqueness of the biderivation with prescribed values"]
theorem existsUnique_mvPolynomial (m : S → M) (hcomm : IsCompatibleOnVars A m) :
    ∃! D : Biderivation A (MvPolynomial S A) M, ∀ s, D (X s) = m s := by
  let D : Biderivation A (MvPolynomial S A) M :=
    { toLinearMap := mvPolynomialLinearMap m
      leibniz := mvPolynomialLinearMap_leibniz m hcomm }
  have hD : ∀ s, D (X s) = m s := by
    intro s
    show mvPolynomialLinearMap m (monomial (Finsupp.single s 1) (1 : A)) = m s
    rw [mvPolynomialLinearMap_monomial]
    classical
    simp [monomialWord, wordValue, wordProduct]
  exact ⟨D, hD, fun E hE ↦ ext_mvPolynomial E D fun s ↦ (hE s).trans (hD s).symm⟩

/-- Compatibility of the prescribed values is not only sufficient but necessary for the
existence and uniqueness asserted by Stacks 09CF. -/
theorem existsUnique_mvPolynomial_iff (m : S → M) :
    (∃! D : Biderivation A (MvPolynomial S A) M, ∀ s, D (X s) = m s) ↔
      IsCompatibleOnVars A m := by
  constructor
  · rintro ⟨D, hD, -⟩
    simpa only [IsCompatibleOnVars, hD] using isCompatibleOnVars_X D
  · exact existsUnique_mvPolynomial m

/-- **Stacks 09CF**, in the case the source applies it: when the two actions of the polynomial
ring on `M` agree, the compatibility equations hold for every family of prescribed values, and
the source's unrestricted assertion is recovered.

This hypothesis cannot be dropped: stated for an arbitrary bimodule the source's assertion is a
Stacks erratum, refuted by
`Biderivation.not_forall_existsUnique_mvPolynomial_erratumModule` in
`StacksFrontier.Cotangent.BiderivationErratum`, whose bimodule is a copy of `k` carrying the two
different actions evaluation at `(1, 0)` and evaluation at `(0, 0)`. -/
@[stacks 09CF "the unrestricted assertion of the source, for a bimodule whose two actions agree"]
theorem existsUnique_mvPolynomial_of_op_smul_eq
    (h : ∀ (q : MvPolynomial S A) (x : M), MulOpposite.op q • x = q • x) (m : S → M) :
    ∃! D : Biderivation A (MvPolynomial S A) M, ∀ s, D (X s) = m s :=
  existsUnique_mvPolynomial m fun s t ↦ by rw [h, h, add_comm]

end MvPolynomial

end Biderivation

end
