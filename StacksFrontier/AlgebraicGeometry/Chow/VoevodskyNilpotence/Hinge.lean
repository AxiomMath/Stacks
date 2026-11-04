module

public import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.TensorChernClasses
public import StacksFrontier.AlgebraicGeometry.Chow.VoevodskyNilpotence.SquareZeroSumPow

/-!
# The hinge of the Voevodsky nilpotence argument

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let `X` be locally of
finite type over `S`. For invertible modules `ℒ₁, …, ℒₙ` on `X` and an invertible module `𝒩'`
whose first Chern class is `m` times the sum of theirs, this file proves

  `c₁(𝒩')ⁿ ∩ α = (mⁿ · n!) · (c₁(ℒ₁) ∩ … ∩ c₁(ℒₙ) ∩ α)`

for every class `α`, the computation in first Chern class cap operations by which the proof of
Stacks 0FH9 compares the zero cycles `αₙ = c₁(ℒ₁) ∩ … ∩ c₁(ℒₙ) ∩ [Xⁿ]` and
`βₙ = c₁(𝒩)ⁿ ∩ [Sⁿ(X)]` along `π : Xⁿ ⟶ Sⁿ(X)`.

A product of first Chern classes is a product in the ring `AddMonoid.End` of the graded product
`Stacks.Chow.ChowGradedProduct` of all the `A_{d-i}(X)`, in which `Stacks.Chow.firstChernShift`
is the endomorphism `c₁(ℒ) ∩ -` (as in Stacks 0FA6, see
`StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.TensorChernClasses`), and
`Stacks.Chow.evalChowGraded` reads off the component of the result in a chosen degree.

The hypotheses on the family are:

* `hM`, that the shift of `𝒩'` is `m` times the sum of the shifts of the `ℒᵢ`; for
  `𝒩' ≅ (ℒ₁ ⊗ … ⊗ ℒₙ)^{⊗ m}` this is Stacks 02SP
  (`Stacks.Chow.firstChernShift_eq_add_of_iso_tensorObj`);
* `hsq`, that each shift squares to zero; for `ℒᵢ = prᵢ^*ℒ` pulled back from a curve this is
  Stacks 0FDX, `Stacks.Chow.firstChernShift_mul_self_eq_zero_of_topologicalKrullDim_le_one`;
* `hcomm`, Stacks 02TJ for each pair, in the form `Stacks.Chow.FirstChernCapStepsCommute`.

## Main results

* `Stacks.Chow.evalChowGraded_firstChernShift_mul`: a product of shift operators, read one degree
  further along, is a first Chern class cap step.
* `Stacks.Chow.firstChernShift_pow_eq_nsmul_listProd`: **the hinge, in the operator ring**.
* `Stacks.Chow.evalChowGraded_firstChernShift_pow`: **the hinge, as an identity of Chow
  classes**.
* `Stacks.Chow.isOfFinAddOrder_evalChowGraded_listProd`: if `c₁(𝒩')ⁿ ∩ α = 0` and `m ≠ 0`, then
  `c₁(ℒ₁) ∩ … ∩ c₁(ℒₙ) ∩ α` is torsion.

## References

* [Stacks Project, Tag 0FH9](https://stacks.math.columbia.edu/tag/0FH9)
* [Stacks Project, Tag 0FDX](https://stacks.math.columbia.edu/tag/0FDX)
* [Stacks Project, Tag 02SP](https://stacks.math.columbia.edu/tag/02SP)
* [Stacks Project, Tag 02TJ](https://stacks.math.columbia.edu/tag/02TJ)
* [Stacks Project, Tag 0FA6](https://stacks.math.columbia.edu/tag/0FA6)
-/


@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Finset Nat

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (deg : ℤ)

/-! ### Reading a product of shift operators as an iterated cap product -/

/-- **A product of shift operators is an iterated cap product.** Multiplying an operator on the
left by the shift of `A` and reading the result one degree further along applies
`Stacks.Chow.firstChernCapStep` of `A` to what the operator read there. -/
theorem evalChowGraded_firstChernShift_mul (A : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property A]
    (hA : InvertibleChernCapDescends C p A)
    (f : AddMonoid.End (ChowGradedProduct C p deg)) (α : chowGroup C p deg) (k : ℕ) :
    evalChowGraded C p deg α (k + 1) (firstChernShift C p deg A hA * f) =
      firstChernCapStep C p deg A hA k (evalChowGraded C p deg α k f) :=
  rfl

/-! ### The expansion -/

variable {n : ℕ} (L : Fin n → X.Modules)
  [∀ i, AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property (L i)]
  (hfac : ∀ i, InvertibleChernCapDescends C p (L i))
  (M : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M]
  (hfacM : InvertibleChernCapDescends C p M)

/-- **The hinge of Stacks 0FH9, in the operator ring.** Let `ℒ₁, …, ℒₙ` be invertible modules
whose first Chern class cap operations pairwise commute (Stacks 02TJ) and square to zero
(Stacks 0FDX), and let `𝒩'` be an invertible module whose cap operation is `m` times their sum
(Stacks 02SP, for `𝒩' ≅ (ℒ₁ ⊗ ⋯ ⊗ ℒₙ)^{⊗ m}`). Then

  `c₁(𝒩')ⁿ = (mⁿ · n!) · c₁(ℒ₁) ⋯ c₁(ℒₙ)`

as endomorphisms of the graded product of the Chow groups. -/
theorem firstChernShift_pow_eq_nsmul_listProd (m : ℕ)
    (hM : firstChernShift C p deg M hfacM = m • ∑ i, firstChernShift C p deg (L i) (hfac i))
    (hsq : ∀ i, firstChernShift C p deg (L i) (hfac i) *
      firstChernShift C p deg (L i) (hfac i) = 0)
    (hcomm : ∀ i j, FirstChernCapStepsCommute C p deg (L i) (L j) (hfac i) (hfac j)) :
    firstChernShift C p deg M hfacM ^ n =
      (m ^ n * n !) • (List.ofFn fun i ↦ firstChernShift C p deg (L i) (hfac i)).prod := by
  have hc : ∀ i j, Commute (firstChernShift C p deg (L i) (hfac i))
      (firstChernShift C p deg (L j) (hfac j)) := fun i j ↦
    commute_firstChernShift C p deg (L i) (L j) (hfac i) (hfac j) (hcomm i j)
  have hexp := sum_pow_eq_factorial_nsmul_listProd_of_commute
    (fun i ↦ firstChernShift C p deg (L i) (hfac i)) hc hsq
  rw [hM, nsmul_eq_mul, (Nat.cast_commute m
      (∑ i, firstChernShift C p deg (L i) (hfac i))).mul_pow, hexp, nsmul_eq_mul, nsmul_eq_mul,
    ← mul_assoc, ← Nat.cast_pow, ← Nat.cast_mul]

/-- **The hinge of Stacks 0FH9, as an identity of Chow classes.** The hypotheses are those of
`Stacks.Chow.firstChernShift_pow_eq_nsmul_listProd`; the conclusion is that identity evaluated on
the class `α`, read in degree `n`. Unfolding the right-hand side with
`Stacks.Chow.evalChowGraded_firstChernShift_mul` `n` times, it says

  `c₁(𝒩')ⁿ ∩ α = (mⁿ · n!) · (c₁(ℒ₁) ∩ ⋯ ∩ c₁(ℒₙ) ∩ α)`  in  `A_{deg-n}(X)`. -/
theorem evalChowGraded_firstChernShift_pow (α : chowGroup C p deg) (m : ℕ)
    (hM : firstChernShift C p deg M hfacM = m • ∑ i, firstChernShift C p deg (L i) (hfac i))
    (hsq : ∀ i, firstChernShift C p deg (L i) (hfac i) *
      firstChernShift C p deg (L i) (hfac i) = 0)
    (hcomm : ∀ i j, FirstChernCapStepsCommute C p deg (L i) (L j) (hfac i) (hfac j)) :
    evalChowGraded C p deg α n (firstChernShift C p deg M hfacM ^ n) =
      (m ^ n * n !) • evalChowGraded C p deg α n
        (List.ofFn fun i ↦ firstChernShift C p deg (L i) (hfac i)).prod := by
  rw [firstChernShift_pow_eq_nsmul_listProd C p deg L hfac M hfacM m hM hsq hcomm, map_nsmul]

/-! ### Closing the chain -/

/-- **Torsion passes down a nonzero multiple.** If `c • α` has finite additive order and `c ≠ 0`,
then so does `α`. -/
theorem isOfFinAddOrder_of_nsmul_of_ne_zero {A : Type*} [AddCommGroup A] {c : ℕ} (hc : c ≠ 0)
    {α : A} (h : IsOfFinAddOrder (c • α)) : IsOfFinAddOrder α :=
  h.of_nsmul hc

/-- **The step of Stacks 0FH9 that makes the zero cycle torsion.** Under the hypotheses of
`Stacks.Chow.firstChernShift_pow_eq_nsmul_listProd`, and with `m ≠ 0`, the vanishing of
`c₁(𝒩')ⁿ ∩ α` forces the iterated cap product `c₁(ℒ₁) ∩ ⋯ ∩ c₁(ℒₙ) ∩ α` to be torsion. -/
theorem isOfFinAddOrder_evalChowGraded_listProd (α : chowGroup C p deg) (m : ℕ) (hm : m ≠ 0)
    (hM : firstChernShift C p deg M hfacM = m • ∑ i, firstChernShift C p deg (L i) (hfac i))
    (hsq : ∀ i, firstChernShift C p deg (L i) (hfac i) *
      firstChernShift C p deg (L i) (hfac i) = 0)
    (hcomm : ∀ i j, FirstChernCapStepsCommute C p deg (L i) (L j) (hfac i) (hfac j))
    (hzero : evalChowGraded C p deg α n (firstChernShift C p deg M hfacM ^ n) = 0) :
    IsOfFinAddOrder (evalChowGraded C p deg α n
      (List.ofFn fun i ↦ firstChernShift C p deg (L i) (hfac i)).prod) := by
  refine isOfFinAddOrder_of_nsmul_of_ne_zero
    (Nat.mul_ne_zero (pow_ne_zero n hm) n.factorial_ne_zero) ?_
  rw [← evalChowGraded_firstChernShift_pow C p deg L hfac M hfacM α m hM hsq hcomm, hzero]
  exact IsOfFinAddOrder.zero

end Stacks.Chow

end
