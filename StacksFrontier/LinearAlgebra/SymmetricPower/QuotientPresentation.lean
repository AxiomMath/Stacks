module

public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# The symmetric algebra of a finite free module modulo one relation

Let `A` be a commutative ring and `v : Fin n → A`. Then

`Sym_A(Aⁿ / A v) = A[x₀, …, x_{n-1}] / (Σᵢ vᵢ xᵢ)`,

the polynomial ring modulo the linear form of `v`. Both sides are presented by the same
generators and the same single relation, and the isomorphism matches the class of the `i`-th
basis vector with `xᵢ`.

This is the computation Stacks 01OC performs to make its example concrete: there `n = 2`,
`v = (ū, v̄)`, and the displayed identity reads `Sym(M) = A[x, y] / (ū x + v̄ y)`.

## Main definitions

* `SymmetricAlgebra.relationForm`: the linear form `Σᵢ vᵢ xᵢ`.
* `SymmetricAlgebra.quotientModule`, `SymmetricAlgebra.quotientAlgebra`: the module `Aⁿ / A v`
  and the algebra `A[xᵢ] / (Σᵢ vᵢ xᵢ)`.
* `SymmetricAlgebra.toQuotientAlgebra`: the canonical `A`-linear map
  `Aⁿ / A v → A[xᵢ] / (Σᵢ vᵢ xᵢ)`.

## Main results

* `SymmetricAlgebra.isSymmetricAlgebra_toQuotientAlgebra`: **`A[xᵢ] / (Σᵢ vᵢ xᵢ)` is the
  symmetric algebra of `Aⁿ / A v`**, via `SymmetricAlgebra.toQuotientAlgebra`. In Mathlib's
  idiom `IsSymmetricAlgebra f` says that the algebra map `Sym_A(M) → B` extending `f` is
  bijective, so this is the displayed identity of the source;
  `SymmetricAlgebra.quotientAlgebraEquiv` is the resulting algebra isomorphism.

## Implementation notes

The inverse is built by hand rather than from a general "symmetric algebra of a quotient"
lemma: the polynomial ring maps to `Sym_A(Aⁿ / A v)` by `MvPolynomial.aeval` on the classes of
the basis vectors, this kills the linear form of `v` because `v` itself becomes zero in the
quotient module, and the two composites are checked on generators — on `X i` for the map out of
the polynomial ring (`MvPolynomial.algHom_ext`), and on `SymmetricAlgebra.ι` of a class for the
map out of the symmetric algebra (`SymmetricAlgebra.algHom_ext`).

The index type is `Fin n` rather than an arbitrary `Fintype`, so that the decidable equality
that `Pi.single` needs comes from an instance rather than from a hypothesis that the statement
does not mention.

Everything is stated for an abstract `A` with `[CommRing A]`. That is what makes the statement
usable when `A` is itself a quotient ring, as it is in Stacks 01OC: writing the quotient types
out at such an `A` picks mismatched `Semiring` instance paths and the `HasQuotient` instance is
then not found, whereas instantiating this statement derives every instance from the single
`CommRing` instance found at the application site.

## References

* [Stacks Project, Tag 01OC](https://stacks.math.columbia.edu/tag/01OC)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public noncomputable section

namespace SymmetricAlgebra

open MvPolynomial

variable (A : Type*) [CommRing A] {n : ℕ} (v : Fin n → A)

/-- The linear form `Σᵢ vᵢ xᵢ` of `v` in the polynomial ring `A[xᵢ]`. -/
public def relationForm : MvPolynomial (Fin n) A :=
  Fintype.linearCombination A (fun i => (X i : MvPolynomial (Fin n) A)) v

/-- The module `Aⁿ / A v`: the finite free module modulo the single relation `v`. -/
public abbrev quotientModule := (Fin n → A) ⧸ Submodule.span A {v}

/-- The algebra `A[xᵢ] / (Σᵢ vᵢ xᵢ)`. -/
public abbrev quotientAlgebra := MvPolynomial (Fin n) A ⧸ Ideal.span {relationForm A v}

section Combination

variable {A} {M N : Type*} [AddCommMonoid M] [Module A M] [AddCommMonoid N] [Module A N]

private lemma map_linearCombination (f : M →ₗ[A] N) (g : Fin n → M) (w : Fin n → A) :
    f (Fintype.linearCombination A g w) = Fintype.linearCombination A (fun i => f (g i)) w := by
  rw [Fintype.linearCombination_apply, Fintype.linearCombination_apply, map_sum]
  exact Finset.sum_congr rfl fun i _ => map_smul f (w i) (g i)

private lemma linearCombination_pi_single (f : Fin n → M) (i : Fin n) :
    Fintype.linearCombination A f (Pi.single i 1) = f i := by
  rw [Fintype.linearCombination_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj, zero_smul]
  · simp

end Combination

variable {A}

private lemma linearCombination_pi_single_self (w : Fin n → A) :
    Fintype.linearCombination A (fun i : Fin n => (Pi.single i 1 : Fin n → A)) w = w := by
  ext j
  rw [Fintype.linearCombination_apply]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hk
    rw [Pi.single_eq_of_ne (Ne.symm hk), mul_zero]
  · simp

variable (A)

/-- `Aⁿ → A[xᵢ] / (Σᵢ vᵢ xᵢ)`, sending `w` to the class of `Σᵢ wᵢ xᵢ`. -/
public def freeToQuotientAlgebra : (Fin n → A) →ₗ[A] quotientAlgebra A v :=
  (Ideal.Quotient.mkₐ A (Ideal.span {relationForm A v})).toLinearMap ∘ₗ
    Fintype.linearCombination A (fun i => (X i : MvPolynomial (Fin n) A))

/-- `freeToQuotientAlgebra A v` sends `w` to the class of `Σᵢ wᵢ xᵢ`. -/
public theorem freeToQuotientAlgebra_apply (w : Fin n → A) :
    freeToQuotientAlgebra A v w =
      Ideal.Quotient.mk (Ideal.span {relationForm A v})
        (Fintype.linearCombination A (fun i => (X i : MvPolynomial (Fin n) A)) w) := rfl

/-- `freeToQuotientAlgebra A v` kills `v`: the class of `Σᵢ vᵢ xᵢ` is zero. -/
public theorem freeToQuotientAlgebra_self : freeToQuotientAlgebra A v v = 0 := by
  rw [freeToQuotientAlgebra_apply, ← relationForm, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span rfl

/-- **The canonical `A`-linear map `Aⁿ / A v → A[xᵢ] / (Σᵢ vᵢ xᵢ)`**, sending the class of the
`i`-th basis vector to the class of `xᵢ`. -/
public def toQuotientAlgebra : quotientModule A v →ₗ[A] quotientAlgebra A v :=
  (Submodule.span A {v}).liftQ (freeToQuotientAlgebra A v) <| by
    rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, LinearMap.mem_ker]
    exact freeToQuotientAlgebra_self A v

/-- `toQuotientAlgebra A v` sends the class of `w` to `freeToQuotientAlgebra A v w`. -/
@[simp] public theorem toQuotientAlgebra_mkQ (w : Fin n → A) :
    toQuotientAlgebra A v ((Submodule.span A {v}).mkQ w) = freeToQuotientAlgebra A v w := rfl

/-- `Aⁿ → Sym_A(Aⁿ / A v)`: the class in the quotient module, then into the symmetric
algebra. -/
private def symGenMap : (Fin n → A) →ₗ[A] SymmetricAlgebra A (quotientModule A v) :=
  (SymmetricAlgebra.ι A (quotientModule A v)).comp (Submodule.span A {v}).mkQ

/-- The classes of the basis vectors in `Sym_A(Aⁿ / A v)`, which are the images of `xᵢ`. -/
private def symGenerator (i : Fin n) : SymmetricAlgebra A (quotientModule A v) :=
  symGenMap A v (Pi.single i 1)

private lemma symGenMap_self : symGenMap A v v = 0 := by
  rw [symGenMap, LinearMap.comp_apply, Submodule.mkQ_apply,
    (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.mem_span_singleton_self v), map_zero]

private lemma linearCombination_symGenerator (w : Fin n → A) :
    Fintype.linearCombination A (symGenerator A v) w = symGenMap A v w := by
  rw [show symGenerator A v = fun i => symGenMap A v (Pi.single i 1) from rfl,
    ← map_linearCombination, linearCombination_pi_single_self]

/-- Evaluating `Σᵢ wᵢ xᵢ` at the classes of the basis vectors gives the class of `w`. -/
private lemma aeval_linearCombination_X (w : Fin n → A) :
    aeval (symGenerator A v)
        (Fintype.linearCombination A (fun i => (X i : MvPolynomial (Fin n) A)) w) =
      symGenMap A v w := by
  rw [show aeval (symGenerator A v)
        (Fintype.linearCombination A (fun i => (X i : MvPolynomial (Fin n) A)) w) =
      (aeval (symGenerator A v)).toLinearMap
        (Fintype.linearCombination A (fun i => (X i : MvPolynomial (Fin n) A)) w) from rfl,
    map_linearCombination]
  simp only [AlgHom.toLinearMap_apply, aeval_X]
  rw [linearCombination_symGenerator]

private lemma aeval_relationForm : aeval (symGenerator A v) (relationForm A v) = 0 := by
  rw [relationForm, aeval_linearCombination_X, symGenMap_self]

/-- The algebra map `A[xᵢ] / (Σᵢ vᵢ xᵢ) → Sym_A(Aⁿ / A v)` inverse to the canonical one. -/
private def quotientAlgebraToSym :
    quotientAlgebra A v →ₐ[A] SymmetricAlgebra A (quotientModule A v) :=
  Ideal.Quotient.liftₐ _ (aeval (symGenerator A v)) <| by
    intro p hp
    rw [Ideal.mem_span_singleton] at hp
    obtain ⟨c, rfl⟩ := hp
    rw [map_mul, aeval_relationForm, zero_mul]

private lemma quotientAlgebraToSym_mk (p : MvPolynomial (Fin n) A) :
    quotientAlgebraToSym A v (Ideal.Quotient.mk (Ideal.span {relationForm A v}) p) =
      aeval (symGenerator A v) p := rfl

private lemma lift_symGenerator (i : Fin n) :
    SymmetricAlgebra.lift (toQuotientAlgebra A v) (symGenerator A v i) =
      Ideal.Quotient.mk (Ideal.span {relationForm A v}) (X i) := by
  rw [symGenerator, symGenMap, LinearMap.comp_apply, lift_ι_apply, toQuotientAlgebra_mkQ,
    freeToQuotientAlgebra_apply, linearCombination_pi_single]

private lemma lift_comp_quotientAlgebraToSym (z : quotientAlgebra A v) :
    SymmetricAlgebra.lift (toQuotientAlgebra A v) (quotientAlgebraToSym A v z) = z := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  have key : ((SymmetricAlgebra.lift (toQuotientAlgebra A v)).comp
        (quotientAlgebraToSym A v)).comp (Ideal.Quotient.mkₐ A (Ideal.span {relationForm A v}))
      = Ideal.Quotient.mkₐ A (Ideal.span {relationForm A v}) :=
    MvPolynomial.algHom_ext fun i => by
      show SymmetricAlgebra.lift (toQuotientAlgebra A v)
        (quotientAlgebraToSym A v (Ideal.Quotient.mk _ (X i))) = _
      rw [quotientAlgebraToSym_mk, aeval_X, lift_symGenerator]
      rfl
  exact congr($key p)

private lemma quotientAlgebraToSym_comp_lift (x : SymmetricAlgebra A (quotientModule A v)) :
    quotientAlgebraToSym A v (SymmetricAlgebra.lift (toQuotientAlgebra A v) x) = x := by
  have key : (quotientAlgebraToSym A v).comp (SymmetricAlgebra.lift (toQuotientAlgebra A v))
      = AlgHom.id A (SymmetricAlgebra A (quotientModule A v)) := by
    refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun m => ?_)
    obtain ⟨w, rfl⟩ := (Submodule.span A {v}).mkQ_surjective m
    show quotientAlgebraToSym A v (SymmetricAlgebra.lift (toQuotientAlgebra A v)
      (SymmetricAlgebra.ι A _ ((Submodule.span A {v}).mkQ w))) = symGenMap A v w
    rw [lift_ι_apply, toQuotientAlgebra_mkQ, freeToQuotientAlgebra_apply,
      quotientAlgebraToSym_mk, aeval_linearCombination_X]
  exact congr($key x)

/-- **`A[xᵢ] / (Σᵢ vᵢ xᵢ)` is the symmetric algebra of `Aⁿ / A v`.** For `n = 2` and
`v = (ū, v̄)` this is the identity `Sym(M) = A[x, y] / (ū x + v̄ y)` displayed in Stacks 01OC. -/
public theorem isSymmetricAlgebra_toQuotientAlgebra :
    IsSymmetricAlgebra (toQuotientAlgebra A v) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨quotientAlgebraToSym A v, quotientAlgebraToSym_comp_lift A v,
      lift_comp_quotientAlgebraToSym A v⟩

/-- The algebra isomorphism `Sym_A(Aⁿ / A v) ≃ A[xᵢ] / (Σᵢ vᵢ xᵢ)` of Stacks 01OC. -/
public def quotientAlgebraEquiv :
    SymmetricAlgebra A (quotientModule A v) ≃ₐ[A] quotientAlgebra A v :=
  (isSymmetricAlgebra_toQuotientAlgebra A v).equiv

end SymmetricAlgebra

end
