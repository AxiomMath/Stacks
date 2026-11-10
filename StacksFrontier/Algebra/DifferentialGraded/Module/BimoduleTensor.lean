module
public import StacksFrontier.Algebra.DifferentialGraded.Endomorphism.BimoduleDefs
public import StacksFrontier.Algebra.DifferentialGraded.Endomorphism.BimoduleTotalization
public import StacksFrontier.Algebra.DifferentialGraded.Module.ComplexesHomotopySquare
public import StacksFrontier.Algebra.DifferentialGraded.Module.DGCategoryComp
public import StacksFrontier.Algebra.DifferentialGraded.Module.DGCategoryHomotopyCategory
public import StacksFrontier.Algebra.DirectSum.RangeGrading

/-!
# Tensoring with a differential graded bimodule

Let `A` and `B` be differential graded algebras over a commutative ring `R`, let `M` be a right
differential graded `A`-module and let `N` be a differential graded `(A, B)`-bimodule. The
relative tensor product `M ⊗_A N` is then a right differential graded `B`-module, and the
construction is a functor of differential graded categories from right differential graded
`A`-modules to right differential graded `B`-modules. It therefore induces a functor on the
ordinary categories of differential graded modules and a functor on their homotopy categories,
and the square relating those two induced functors to the passage to homotopy classes commutes
up to natural isomorphism.

## Main definitions

* `DifferentialGraded.Bimodule.BalancedBilinearMap`: a balanced, right `B`-linear bilinear chain
  map out of `M` and `N`.
* `DifferentialGraded.Bimodule.TensorDGFunctorData`: the tensor functor of differential graded
  categories, together with its universal pure tensors.

## Main results

* `DifferentialGraded.Bimodule.tensorDGFunctor`: the tensor functor of differential graded
  categories.
* `DifferentialGraded.Bimodule.tensorCompFunctor` and
  `DifferentialGraded.Bimodule.tensorHomotopyFunctor`: the induced functors on differential
  graded modules and on homotopy categories.
* `DifferentialGraded.Bimodule.tensorCompFunctor_quotient`: passing the ordinary tensor functor
  to homotopy classes gives the tensor functor on homotopy categories.

## Implementation notes

*The tensor product is characterized, not named.* `TensorDGFunctorData` records a differential
graded functor together with the universal balanced bilinear map into each of its values and the
pure-tensor formula for its action on homogeneous morphisms. That is what pins the functor down:
the underlying module of `M ⊗_A N` is built here as a direct sum of quotients, but no consumer
should depend on that presentation, so the construction is private and only the data is public.

*The underlying module is assembled degree by degree.* The degree-`k` piece of `M ⊗_A N` is the
quotient of `⨁_{p + q = k} M^p ⊗_R N^q` by the homogeneous balancing relations
`(x a) ⊗ y - x ⊗ (a y)`; `tensorFiberEquiv` identifies `M ⊗_R N` with the direct sum of those
spaces, which is what lets the ungraded relative tensor product and the graded one be compared
(`tensorQuotientEquiv`) and hence lets the universal property be proved on the ungraded quotient
while the grading and differential are read off the graded one.

*The left action is taken from the totalization API, and given a degree-correct name.* The left
action of a homogeneous `a : A^n` on the whole of `N` is
`DifferentialGraded.leftActionTotal`, with its multiplicativity, unitality, Leibniz rule and
commutation with the right `B`-action. Beside it, `leftAct` names the action on a homogeneous
element with the degree-`q + n` piece in its *declared* type. That is load-bearing rather than
cosmetic: written through `Cochain.v`, the value only lies in `N^{q + n}` after unfolding
`DifferentialGradedModule.toCochainComplex`, and a rewrite whose pattern mentions it then fails
to match. Naming it is what removes the need to relax definitional-unfolding transparency, and
with it the need for `erw`.

*Bidegrees are packaged.* `tensorComponentInclusion_of_tmul` is
`tensorComponentInclusion_tmul` with the bidegree carried as a single subtype element rather than
as a pair of integers with a proof, so that rewriting with it requires no arithmetic unification
on the index; this is what lets the graded Leibniz computation for the balancing relations run as
a plain `rw`.

## References

* [Stacks Project, Tag 09LM](https://stacks.math.columbia.edu/tag/09LM)
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct DirectSum
open CochainComplex.HomComplex

namespace DifferentialGraded.Bimodule

universe u

variable {R : Type u} [CommRing R]
variable {A B : DifferentialGradedAlgebra.{u, u} R}

open DifferentialGradedModule

/-- A balanced bilinear chain map from a right differential graded `A`-module `M` and a
differential graded `(A, B)`-bimodule `N` to a right differential graded `B`-module `P`. -/
structure BalancedBilinearMap (M : DifferentialGradedModule A) (N : Bimodule A B)
    (P : DifferentialGradedModule B) where
  /-- The underlying `R`-bilinear map. -/
  toLinearMap : M.M →ₗ[R] N.rightModule.M →ₗ[R] P.M
  /-- It adds degrees. -/
  map_grading (p q : ℤ) (x : M.grading p) (y : N.rightModule.grading q) :
    toLinearMap x y ∈ P.grading (p + q)
  /-- It satisfies the graded Leibniz rule. -/
  map_d (p : ℤ) (x : M.grading p) (y : N.rightModule.M) :
    P.d (toLinearMap x y) =
      toLinearMap (M.d x) y + (p.negOnePow : ℤ) • toLinearMap x (N.rightModule.d y)
  /-- It is balanced over `A`. -/
  balance (p q n : ℤ) (x : M.grading p) (y : N.rightModule.grading q) (a : A.grading n) :
    toLinearMap (MulOpposite.op (a : A.A) • (x : M.M)) y =
      toLinearMap x
        ((show N.rightModule.grading (q + n) from
          (N.leftAction.1.action n a).v q (q + n) (by omega) y) : N.rightModule.M)
  /-- It is right `B`-linear in the second variable. -/
  map_right (x : M.M) (y : N.rightModule.M) (b : B.A) :
    toLinearMap x (MulOpposite.op b • y) = MulOpposite.op b • toLinearMap x y

/-! ### The left action of `A` on the bimodule -/

/-- The left action of a homogeneous `a : A^n` on a homogeneous element of the bimodule, as an
element of the degree-shifted piece. Giving this its own name keeps the degree-`q + n` piece in
the *declared* type, so that rewriting with it does not depend on unfolding
`DifferentialGradedModule.toCochainComplex`. -/
private noncomputable def leftAct (N : Bimodule A B) {n q : ℤ} (a : A.grading n)
    (y : N.rightModule.grading q) : N.rightModule.grading (q + n) :=
  (N.leftAction.1.action n a).v q (q + n) (by omega) y

/-- The left action of `A` on the whole of the bimodule. -/
private noncomputable def leftTot (N : Bimodule A B) (a : A.A) :
    N.rightModule.M →ₗ[R] N.rightModule.M :=
  leftActionTotal A B N.rightModule N.leftAction.1 a

private theorem leftTot_coe (N : Bimodule A B) {n q : ℤ} (a : A.grading n)
    (y : N.rightModule.grading q) :
    leftTot N (a : A.A) (y : N.rightModule.M) = (leftAct N a y : N.rightModule.M) := by
  change leftActionTotal A B N.rightModule N.leftAction.1 (a : A.A)
    (y : N.rightModule.M) = _
  rw [leftActionTotal_apply A B N.rightModule N.leftAction.1 n a,
    totalizeCochain_apply_of_eq B N.rightModule n q (q + n) rfl
      (N.leftAction.1.action n a) y]
  rfl

private theorem leftTot_op_smul_coe (N : Bimodule A B) {n : ℤ} (a : A.grading n) (b : B.A)
    (y : N.rightModule.M) :
    leftTot N (a : A.A) (MulOpposite.op b • y) = MulOpposite.op b • leftTot N (a : A.A) y := by
  change leftActionTotal A B N.rightModule N.leftAction.1 (a : A.A) _ = _
  induction b using DirectSum.Decomposition.inductionOn B.grading with
  | zero => simp
  | @homogeneous r b =>
    exact leftActionTotal_commutes A B N.rightModule N.leftAction.1
      N.leftAction.2 a b y
  | add b c hb hc => simp only [MulOpposite.op_add, add_smul, map_add, hb, hc]

private theorem leftTot_op_smul (N : Bimodule A B) {n : ℤ} (a : A.grading n) (b : B.Aᵐᵒᵖ)
    (y : N.rightModule.M) :
    leftTot N (a : A.A) (b • y) = b • leftTot N (a : A.A) y := by
  rw [← MulOpposite.op_unop b]
  exact leftTot_op_smul_coe N a b.unop y

private theorem leftTot_leibniz (N : Bimodule A B) {n : ℤ} (a : A.grading n)
    (y : N.rightModule.M) :
    N.rightModule.d (leftTot N (a : A.A) y) =
      leftTot N (A.d a) y + (n.negOnePow : ℤ) • leftTot N (a : A.A) (N.rightModule.d y) :=
  leftActionTotal_leibniz A B N.rightModule N.leftAction.1 a y

/-- The balance condition of a balanced bilinear map, phrased through `leftAct`. This is the
shape `tensorQuotientLift` consumes, and it differs from the field `balance` only in how the
degree-shifted element is spelled. -/
private theorem balanced_leftAct {M : DifferentialGradedModule A} {N : Bimodule A B}
    {P : DifferentialGradedModule B} (t : BalancedBilinearMap M N P)
    (p q n : ℤ) (x : M.grading p) (y : N.rightModule.grading q) (a : A.grading n) :
    t.toLinearMap (MulOpposite.op (a : A.A) • (x : M.M)) y =
      t.toLinearMap x (leftAct N a y : N.rightModule.M) :=
  t.balance p q n x y a

private theorem leftTot_d (N : Bimodule A B) {n : ℤ} (a : A.grading n) (y : N.rightModule.M) :
    leftTot N (A.d a) y =
      N.rightModule.d (leftTot N (a : A.A) y) +
        (((n + 1).negOnePow : ℤ)) • leftTot N (a : A.A) (N.rightModule.d y) := by
  have h := leftTot_leibniz N a y
  rw [show (((n + 1).negOnePow : ℤ)) = -(n.negOnePow : ℤ) by rw [Int.negOnePow_add]; simp,
    neg_zsmul, ← sub_eq_add_neg, h]
  abel

/-! ### The relative tensor product, degree by degree -/

private def tensorBalanceRelations (M : DifferentialGradedModule A) (N : Bimodule A B) :
    Submodule R (M.M ⊗[R] N.rightModule.M) :=
  Submodule.span R {z | ∃ (p q n : ℤ) (x : M.grading p)
      (y : N.rightModule.grading q) (a : A.grading n),
      z = ((MulOpposite.op (a : A.A) • (x : M.M)) ⊗ₜ[R] (y : N.rightModule.M)) -
        ((x : M.M) ⊗ₜ[R] (leftAct N a y : N.rightModule.M))}

private abbrev tensorGradedPair (M : DifferentialGradedModule A) (N : Bimodule A B) (p q : ℤ) :=
  M.grading p ⊗[R] N.rightModule.grading q

@[reducible] private noncomputable def tensorGradedPairAddCommGroup
    (M : DifferentialGradedModule A) (N : Bimodule A B) (p q : ℤ) :
    AddCommGroup (tensorGradedPair M N p q) := by
  unfold tensorGradedPair
  infer_instance

attribute [local instance] tensorGradedPairAddCommGroup

@[reducible] private noncomputable def tensorGradedPairAddCommMonoid
    (M : DifferentialGradedModule A) (N : Bimodule A B) (p q : ℤ) :
    AddCommMonoid (tensorGradedPair M N p q) :=
  (tensorGradedPairAddCommGroup M N p q).toAddCommMonoid

attribute [local instance 2000] tensorGradedPairAddCommMonoid

private abbrev tensorComponents (M : DifferentialGradedModule A) (N : Bimodule A B) (n : ℤ) :=
  ⨁ pq : {pq : ℤ × ℤ // pq.1 + pq.2 = n},
    (M.grading pq.val.1 ⊗[R] N.rightModule.grading pq.val.2)

@[reducible] private noncomputable def tensorComponentsAddCommGroup
    (M : DifferentialGradedModule A) (N : Bimodule A B) (n : ℤ) :
    AddCommGroup (tensorComponents M N n) := by
  classical
  unfold tensorComponents
  infer_instance

attribute [local instance] tensorComponentsAddCommGroup

@[reducible] private noncomputable def tensorComponentsAddCommMonoid
    (M : DifferentialGradedModule A) (N : Bimodule A B) (n : ℤ) :
    AddCommMonoid (tensorComponents M N n) :=
  (tensorComponentsAddCommGroup M N n).toAddCommMonoid

attribute [local instance 2000] tensorComponentsAddCommMonoid

private noncomputable def tensorFiberEquiv (M : DifferentialGradedModule A) (N : Bimodule A B) :
    (M.M ⊗[R] N.rightModule.M) ≃ₗ[R] ⨁ n : ℤ, tensorComponents M N n := by
  let eFiber :
      (⨁ pq : ℤ × ℤ, M.grading pq.1 ⊗[R] N.rightModule.grading pq.2) ≃ₗ[R]
        (⨁ n : ℤ, tensorComponents M N n) := by
    let e₁ :
        (⨁ k : (n : ℤ) × {pq : ℤ × ℤ // pq.1 + pq.2 = n},
          M.grading k.2.val.1 ⊗[R] N.rightModule.grading k.2.val.2) ≃ₗ[R]
          (⨁ pq : ℤ × ℤ, M.grading pq.1 ⊗[R] N.rightModule.grading pq.2) :=
      DirectSum.lequivCongrLeft R (Equiv.sigmaFiberEquiv (fun pq : ℤ × ℤ ↦ pq.1 + pq.2))
    exact e₁.symm.trans (DirectSum.sigmaLcurryEquiv R
      (δ := fun (n : ℤ) (pq : {pq : ℤ × ℤ // pq.1 + pq.2 = n}) ↦
        M.grading pq.val.1 ⊗[R] N.rightModule.grading pq.val.2))
  exact ((TensorProduct.congr
      (DirectSum.decomposeLinearEquiv M.grading)
      (DirectSum.decomposeLinearEquiv N.rightModule.grading)).trans
      (TensorProduct.directSum R R (fun p ↦ M.grading p)
        (fun q ↦ N.rightModule.grading q))).trans eFiber

private theorem tensorFiberEquiv_tmul (M : DifferentialGradedModule A) (N : Bimodule A B)
    (p q : ℤ) (x : M.grading p) (y : N.rightModule.grading q) :
    tensorFiberEquiv M N ((x : M.M) ⊗ₜ[R] (y : N.rightModule.M)) =
      DirectSum.of (tensorComponents M N) (p + q)
        (DirectSum.of _ ⟨(p, q), rfl⟩ (x ⊗ₜ[R] y)) := by
  simp only [tensorFiberEquiv, LinearEquiv.trans_apply, TensorProduct.congr_tmul,
    DirectSum.decomposeLinearEquiv_apply_coe]
  have hTensor := TensorProduct.directSum_lof_tmul_lof R R
    (M₁ := fun p ↦ M.grading p) (M₂ := fun q ↦ N.rightModule.grading q) p x q y
  rw [show TensorProduct.directSum R R (fun p ↦ M.grading p)
      (fun q ↦ N.rightModule.grading q)
      (DirectSum.lof R ℤ (fun p ↦ M.grading p) p x ⊗ₜ[R]
        DirectSum.lof R ℤ (fun q ↦ N.rightModule.grading q) q y) =
      DirectSum.of (fun pq : ℤ × ℤ ↦ M.grading pq.1 ⊗[R]
        N.rightModule.grading pq.2) (p, q) (x ⊗ₜ[R] y) by
    simpa only [DirectSum.lof_eq_of] using hTensor]
  change DirectSum.sigmaFiberAddEquiv (fun pq : ℤ × ℤ ↦ pq.1 + pq.2)
      (DirectSum.of (fun pq : ℤ × ℤ ↦ M.grading pq.1 ⊗[R] N.rightModule.grading pq.2)
        (p, q) (x ⊗ₜ[R] y)) = _
  exact DirectSum.sigmaFiberAddEquiv_of
    (β := fun pq : ℤ × ℤ ↦ M.grading pq.1 ⊗[R] N.rightModule.grading pq.2)
    (fun pq : ℤ × ℤ ↦ pq.1 + pq.2) (p, q) (x ⊗ₜ[R] y)

private noncomputable def tensorComponentInclusion (M : DifferentialGradedModule A)
    (N : Bimodule A B) (k : ℤ) :
    tensorComponents M N k →ₗ[R] M.M ⊗[R] N.rightModule.M :=
  (tensorFiberEquiv M N).symm.toLinearMap.comp
    (DirectSum.lof R ℤ (tensorComponents M N) k)

private theorem tensorComponentInclusion_injective (M : DifferentialGradedModule A)
    (N : Bimodule A B) (k : ℤ) :
    Function.Injective (tensorComponentInclusion M N k) :=
  (tensorFiberEquiv M N).symm.injective.comp (DirectSum.of_injective k)

private theorem tensorComponentInclusion_tmul (M : DifferentialGradedModule A)
    (N : Bimodule A B) (k p q : ℤ) (h : p + q = k)
    (x : M.grading p) (y : N.rightModule.grading q) :
    tensorComponentInclusion M N k
      (DirectSum.of (fun pq : {pq : ℤ × ℤ // pq.1 + pq.2 = k} =>
        M.grading pq.val.1 ⊗[R] N.rightModule.grading pq.val.2)
        ⟨(p, q), h⟩ (x ⊗ₜ[R] y)) =
        (x : M.M) ⊗ₜ[R] (y : N.rightModule.M) := by
  subst k
  apply (tensorFiberEquiv M N).injective
  simp only [tensorComponentInclusion, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, DirectSum.lof_eq_of,
    tensorFiberEquiv_tmul]


/-- `tensorComponentInclusion_tmul` with the bidegree packaged as a single index, so that
rewriting with it needs no arithmetic unification on the index. -/
private theorem tensorComponentInclusion_of_tmul (M : DifferentialGradedModule A)
    (N : Bimodule A B) (k : ℤ) (idx : {pq : ℤ × ℤ // pq.1 + pq.2 = k})
    (u : M.grading idx.val.1) (v : N.rightModule.grading idx.val.2) :
    tensorComponentInclusion M N k
        (DirectSum.of (fun pq : {pq : ℤ × ℤ // pq.1 + pq.2 = k} =>
          M.grading pq.val.1 ⊗[R] N.rightModule.grading pq.val.2) idx (u ⊗ₜ[R] v)) =
      (u : M.M) ⊗ₜ[R] (v : N.rightModule.M) := by
  obtain ⟨⟨p, q⟩, h⟩ := idx
  exact tensorComponentInclusion_tmul M N k p q h u v

private noncomputable def tensorBalanceGeneratorAt (M : DifferentialGradedModule A)
    (N : Bimodule A B) (k p q n : ℤ) (h : p + n + q = k)
    (x : M.grading p) (y : N.rightModule.grading q) (a : A.grading n) :
    tensorComponents M N k :=
  DirectSum.of
      (fun pq : {pq : ℤ × ℤ // pq.1 + pq.2 = k} =>
        M.grading pq.val.1 ⊗[R] N.rightModule.grading pq.val.2)
      ⟨(p + n, q), by omega⟩
      ((⟨MulOpposite.op (a : A.A) • (x : M.M),
        M.smul_mem p n (x : M.M) (a : A.A) x.property a.property⟩ :
        M.grading (p + n)) ⊗ₜ[R] y) -
    DirectSum.of
      (fun pq : {pq : ℤ × ℤ // pq.1 + pq.2 = k} =>
        M.grading pq.val.1 ⊗[R] N.rightModule.grading pq.val.2)
      ⟨(p, q + n), by omega⟩
      ((x : M.grading p) ⊗ₜ[R] leftAct N a y)

private noncomputable def tensorBalanceRelationsAt (M : DifferentialGradedModule A)
    (N : Bimodule A B) (k : ℤ) : Submodule R (tensorComponents M N k) :=
  Submodule.span R {z | ∃ (p q n : ℤ) (x : M.grading p)
      (y : N.rightModule.grading q) (a : A.grading n),
      ∃ (_h : p + n + q = k),
      z = tensorBalanceGeneratorAt M N k p q n _h x y a }

private abbrev tensorQuotientPiece (M : DifferentialGradedModule A) (N : Bimodule A B) (n : ℤ) :=
  tensorComponents M N n ⧸ tensorBalanceRelationsAt M N n

private abbrev tensorQuotientTotal (M : DifferentialGradedModule A) (N : Bimodule A B) :=
  ⨁ n : ℤ, tensorQuotientPiece M N n

@[reducible] private noncomputable def tensorQuotientTotalAddCommGroup
    (M : DifferentialGradedModule A) (N : Bimodule A B) :
    AddCommGroup (tensorQuotientTotal M N) := by
  classical
  unfold tensorQuotientTotal tensorQuotientPiece
  infer_instance

attribute [local instance] tensorQuotientTotalAddCommGroup

@[reducible] private noncomputable def tensorQuotientTotalAddCommMonoid
    (M : DifferentialGradedModule A) (N : Bimodule A B) :
    AddCommMonoid (tensorQuotientTotal M N) :=
  (tensorQuotientTotalAddCommGroup M N).toAddCommMonoid

attribute [local instance 2000] tensorQuotientTotalAddCommMonoid

private noncomputable def tensorQuotientPureAt (M : DifferentialGradedModule A)
    (N : Bimodule A B) (k p q : ℤ) (h : p + q = k)
    (x : M.grading p) (y : N.rightModule.grading q) : tensorQuotientTotal M N :=
  DirectSum.of _ k (Submodule.Quotient.mk (DirectSum.of _ ⟨(p, q), h⟩ (x ⊗ₜ[R] y)))

private theorem tensorQuotientClass_heq (M : DifferentialGradedModule A) (N : Bimodule A B)
    (i j r s : ℤ) (hi : r + s = i) (hj : r + s = j)
    (x : M.grading r ⊗[R] N.rightModule.grading s) :
    HEq
      ((Submodule.Quotient.mk (DirectSum.of
        (fun pq : {pq : ℤ × ℤ // pq.1 + pq.2 = i} =>
          M.grading pq.val.1 ⊗[R] N.rightModule.grading pq.val.2)
        ⟨(r, s), hi⟩ x) : tensorQuotientPiece M N i))
      ((Submodule.Quotient.mk (DirectSum.of
        (fun pq : {pq : ℤ × ℤ // pq.1 + pq.2 = j} =>
          M.grading pq.val.1 ⊗[R] N.rightModule.grading pq.val.2)
        ⟨(r, s), hj⟩ x) : tensorQuotientPiece M N j)) := by
  subst i
  subst j
  rfl

private theorem tensorQuotientPureAt_balance (M : DifferentialGradedModule A)
    (N : Bimodule A B) (p q n : ℤ) (x : M.grading p) (y : N.rightModule.grading q)
    (a : A.grading n) :
    tensorQuotientPureAt M N (p + n + q) (p + n) q (by omega)
      ⟨MulOpposite.op (a : A.A) • (x : M.M),
        M.smul_mem p n (x : M.M) (a : A.A) x.property a.property⟩ y =
    tensorQuotientPureAt M N (p + n + q) p (q + n) (by omega) x (leftAct N a y) := by
  change DirectSum.of (fun i : ℤ ↦ tensorQuotientPiece M N i) (p + n + q)
      (Submodule.Quotient.mk
        (DirectSum.of
          (fun pq : {pq : ℤ × ℤ // pq.1 + pq.2 = p + n + q} =>
            M.grading pq.val.1 ⊗[R] N.rightModule.grading pq.val.2)
          ⟨(p + n, q), by omega⟩
          ((⟨MulOpposite.op (a : A.A) • (x : M.M),
            M.smul_mem p n (x : M.M) (a : A.A) x.property a.property⟩ :
              M.grading (p + n)) ⊗ₜ[R] y))) =
    DirectSum.of (fun i : ℤ ↦ tensorQuotientPiece M N i) (p + n + q)
      (Submodule.Quotient.mk
        (DirectSum.of
          (fun pq : {pq : ℤ × ℤ // pq.1 + pq.2 = p + n + q} =>
            M.grading pq.val.1 ⊗[R] N.rightModule.grading pq.val.2)
          ⟨(p, q + n), by omega⟩
          (x ⊗ₜ[R] leftAct N a y)))
  congr 1
  exact (Submodule.Quotient.eq (tensorBalanceRelationsAt M N (p + n + q))).mpr
    (Submodule.subset_span ⟨p, q, n, x, y, a, rfl, rfl⟩)

private noncomputable def tensorQuotientProjection (M : DifferentialGradedModule A)
    (N : Bimodule A B) :
    (⨁ n : ℤ, tensorComponents M N n) →ₗ[R] tensorQuotientTotal M N :=
  DirectSum.toModule R ℤ _ fun n =>
    (DirectSum.lof R ℤ (fun i : ℤ ↦ tensorQuotientPiece M N i) n).comp
      (tensorBalanceRelationsAt M N n).mkQ

private theorem tensorQuotientProjection_of (M : DifferentialGradedModule A)
    (N : Bimodule A B) (n : ℤ) (x : tensorComponents M N n) :
    tensorQuotientProjection M N (DirectSum.of (tensorComponents M N) n x) =
      DirectSum.of (fun i : ℤ ↦ tensorQuotientPiece M N i) n (Submodule.Quotient.mk x) := by
  change DirectSum.toModule R ℤ (tensorQuotientTotal M N)
      (fun i ↦ DirectSum.lof R ℤ (fun j : ℤ ↦ tensorQuotientPiece M N j) i ∘ₗ
        (tensorBalanceRelationsAt M N i).mkQ)
      (DirectSum.of (tensorComponents M N) n x) = _
  rw [← DirectSum.lof_eq_of R ℤ (tensorComponents M N) n x, DirectSum.toModule_lof]
  rfl

private noncomputable def tensorQuotientRawMap (M : DifferentialGradedModule A)
    (N : Bimodule A B) : M.M ⊗[R] N.rightModule.M →ₗ[R] tensorQuotientTotal M N :=
  (tensorQuotientProjection M N).comp (tensorFiberEquiv M N).toLinearMap

private noncomputable def tensorQuotientMap (M : DifferentialGradedModule A)
    (N : Bimodule A B) :
    (M.M ⊗[R] N.rightModule.M) ⧸ tensorBalanceRelations M N →ₗ[R] tensorQuotientTotal M N := by
  classical
  refine (tensorBalanceRelations M N).liftQ (τ₁₂ := RingHom.id R)
    (tensorQuotientRawMap M N) ?_
  intro z hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
      rcases hz with ⟨p, q, n, x, y, a, rfl⟩
      let xa : M.grading (p + n) :=
        ⟨MulOpposite.op (a : A.A) • (x : M.M),
          M.smul_mem p n (x : M.M) (a : A.A) x.property a.property⟩
      let ya : N.rightModule.grading (q + n) := leftAct N a y
      have hxa := tensorFiberEquiv_tmul M N (p + n) q xa y
      have hya := tensorFiberEquiv_tmul M N p (q + n) x ya
      simp only [LinearMap.mem_ker, map_sub, tensorQuotientRawMap, LinearMap.comp_apply]
      change tensorQuotientProjection M N
          (tensorFiberEquiv M N ((xa : M.M) ⊗ₜ[R] (y : N.rightModule.M))) -
        tensorQuotientProjection M N
          (tensorFiberEquiv M N ((x : M.M) ⊗ₜ[R] (ya : N.rightModule.M))) = 0
      rw [hxa, hya, tensorQuotientProjection_of, tensorQuotientProjection_of]
      apply sub_eq_zero.mpr
      set k₁ : ℤ := p + n + q with hk₁
      set k₂ : ℤ := p + (q + n) with hk₂
      have hidx : k₁ = k₂ := by omega
      let c₁ : tensorQuotientPiece M N k₁ :=
        Submodule.Quotient.mk <| DirectSum.of
          (fun pq : {pq : ℤ × ℤ // pq.1 + pq.2 = k₁} =>
            M.grading pq.val.1 ⊗[R] N.rightModule.grading pq.val.2)
          ⟨(p + n, q), by omega⟩ (xa ⊗ₜ[R] y)
      let c₂ : tensorQuotientPiece M N k₁ :=
        Submodule.Quotient.mk <| DirectSum.of
          (fun pq : {pq : ℤ × ℤ // pq.1 + pq.2 = k₁} =>
            M.grading pq.val.1 ⊗[R] N.rightModule.grading pq.val.2)
          ⟨(p, q + n), by omega⟩ (x ⊗ₜ[R] ya)
      let c₂' : tensorQuotientPiece M N k₂ :=
        Submodule.Quotient.mk <| DirectSum.of
          (fun pq : {pq : ℤ × ℤ // pq.1 + pq.2 = k₂} =>
            M.grading pq.val.1 ⊗[R] N.rightModule.grading pq.val.2)
          ⟨(p, q + n), by omega⟩ (x ⊗ₜ[R] ya)
      have hbal := tensorQuotientPureAt_balance M N p q n x y a
      dsimp [tensorQuotientPureAt] at hbal
      change DirectSum.of (fun i : ℤ ↦ tensorQuotientPiece M N i) k₁ c₁ =
        DirectSum.of (fun i : ℤ ↦ tensorQuotientPiece M N i) k₂ c₂'
      calc
        DirectSum.of (fun i : ℤ ↦ tensorQuotientPiece M N i) k₁ c₁ =
            DirectSum.of (fun i : ℤ ↦ tensorQuotientPiece M N i) k₁ c₂ := by
              simpa [c₁, c₂, xa, ya] using hbal
        _ = DirectSum.of (fun i : ℤ ↦ tensorQuotientPiece M N i) k₂ c₂' :=
          DirectSum.of_eq_of_gradedMonoid_eq (Sigma.ext hidx (tensorQuotientClass_heq M N k₁ k₂ p
            (q + n) (by omega) (by omega) (x ⊗ₜ[R] ya)))
  | zero => simp
  | add x y _ _ hx hy =>
      simp only [LinearMap.mem_ker] at hx hy ⊢
      simp [map_add, hx, hy]
  | smul r x _ hx =>
      simp only [LinearMap.mem_ker] at hx ⊢
      simp [map_smul, hx]

private theorem tensorQuotientMap_mk_tmul (M : DifferentialGradedModule A) (N : Bimodule A B)
    (p q : ℤ) (x : M.grading p) (y : N.rightModule.grading q) :
    tensorQuotientMap M N (Submodule.Quotient.mk ((x : M.M) ⊗ₜ[R] (y : N.rightModule.M))) =
      tensorQuotientPureAt M N (p + q) p q rfl x y := by
  change tensorQuotientProjection M N
      (tensorFiberEquiv M N ((x : M.M) ⊗ₜ[R] (y : N.rightModule.M))) = _
  rw [tensorFiberEquiv_tmul, tensorQuotientProjection_of]
  rfl

private theorem tensorQuotientMap_surjective (M : DifferentialGradedModule A)
    (N : Bimodule A B) : Function.Surjective (tensorQuotientMap M N) := by
  intro z
  induction z using DirectSum.induction_on with
  | zero => exact ⟨0, by simp [tensorQuotientMap]⟩
  | add x y hx hy =>
      rcases hx with ⟨x', hx'⟩
      rcases hy with ⟨y', hy'⟩
      exact ⟨x' + y', by simp [map_add, hx', hy']⟩
  | of k x =>
      induction x using Submodule.Quotient.induction_on with
      | _ x =>
          induction x using DirectSum.induction_on with
          | zero => exact ⟨0, by simp [tensorQuotientMap]⟩
          | add x y hx hy =>
              rcases hx with ⟨x', hx'⟩
              rcases hy with ⟨y', hy'⟩
              exact ⟨x' + y', by simp [map_add, hx', hy']⟩
          | of i x =>
              induction x using TensorProduct.inductionOn with
              | add x y hx hy =>
                  rcases hx with ⟨x', hx'⟩
                  rcases hy with ⟨y', hy'⟩
                  exact ⟨x' + y', by simp [map_add, hx', hy']⟩
              | tmul x y =>
                  rcases i with ⟨⟨p, q⟩, h⟩
                  subst k
                  refine ⟨Submodule.Quotient.mk ((x : M.M) ⊗ₜ[R] (y : N.rightModule.M)), ?_⟩
                  simpa [tensorQuotientPureAt] using tensorQuotientMap_mk_tmul M N p q x y

private noncomputable def tensorQuotientInversePiece (M : DifferentialGradedModule A)
    (N : Bimodule A B) (k : ℤ) :
    tensorQuotientPiece M N k →ₗ[R]
      (M.M ⊗[R] N.rightModule.M) ⧸ tensorBalanceRelations M N := by
  refine (tensorBalanceRelationsAt M N k).liftQ
    ((tensorBalanceRelations M N).mkQ.comp (tensorComponentInclusion M N k)) ?_
  apply Submodule.span_le.mpr
  rintro z ⟨p, q, n, x, y, a, h, rfl⟩
  change (tensorBalanceRelations M N).mkQ
    (tensorComponentInclusion M N k (tensorBalanceGeneratorAt M N k p q n h x y a)) = 0
  simp only [tensorBalanceGeneratorAt, map_sub]
  rw [tensorComponentInclusion_of_tmul, tensorComponentInclusion_of_tmul, ← map_sub]
  exact (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.subset_span ⟨p, q, n, x, y, a, rfl⟩)

private noncomputable def tensorQuotientInverse (M : DifferentialGradedModule A)
    (N : Bimodule A B) :
    tensorQuotientTotal M N →ₗ[R]
      (M.M ⊗[R] N.rightModule.M) ⧸ tensorBalanceRelations M N :=
  DirectSum.toModule R ℤ _ (tensorQuotientInversePiece M N)

/-- The inverse map sends the class of a degree-`k` component to the class of its image in the
ungraded tensor product. -/
private theorem tensorQuotientInverse_of (M : DifferentialGradedModule A) (N : Bimodule A B)
    (k : ℤ) (z : tensorComponents M N k) :
    tensorQuotientInverse M N (DirectSum.of _ k (Submodule.Quotient.mk z)) =
      (tensorBalanceRelations M N).mkQ (tensorComponentInclusion M N k z) := by
  change DirectSum.toModule R ℤ _ (tensorQuotientInversePiece M N)
    (DirectSum.lof R ℤ _ k (Submodule.Quotient.mk z)) = _
  rw [DirectSum.toModule_lof]
  rfl

private theorem tensorQuotientInverse_pure (M : DifferentialGradedModule A)
    (N : Bimodule A B) (k p q : ℤ) (h : p + q = k)
    (x : M.grading p) (y : N.rightModule.grading q) :
    tensorQuotientInverse M N (tensorQuotientPureAt M N k p q h x y) =
      Submodule.Quotient.mk ((x : M.M) ⊗ₜ[R] (y : N.rightModule.M)) := by
  rw [tensorQuotientPureAt, tensorQuotientInverse_of, tensorComponentInclusion_tmul]
  rfl

/-- Two bilinear maps out of `M × N` that agree on homogeneous elements are equal. -/
private theorem bilinear_ext_homogeneous (M : DifferentialGradedModule A) (N : Bimodule A B)
    {P : Type*} [AddCommGroup P] [Module R P] (f g : M.M →ₗ[R] N.rightModule.M →ₗ[R] P)
    (h : ∀ (p q : ℤ) (x : M.grading p) (y : N.rightModule.grading q),
      f (x : M.M) (y : N.rightModule.M) = g (x : M.M) (y : N.rightModule.M)) : f = g := by
  ext x y
  induction x using DirectSum.Decomposition.inductionOn M.grading with
  | zero => simp
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz]
  | @homogeneous p x =>
    induction y using DirectSum.Decomposition.inductionOn N.rightModule.grading with
    | zero => simp
    | add y z hy hz => simp only [map_add, hy, hz]
    | @homogeneous q y => exact h p q x y

private theorem tensorQuotientInverse_map (M : DifferentialGradedModule A) (N : Bimodule A B) :
    tensorQuotientInverse M N ∘ₗ tensorQuotientMap M N = LinearMap.id := by
  apply (tensorBalanceRelations M N).linearMap_qext
  apply TensorProduct.ext
  apply bilinear_ext_homogeneous
  intro p q x y
  change tensorQuotientInverse M N
    (tensorQuotientMap M N (Submodule.Quotient.mk
      ((x : M.M) ⊗ₜ[R] (y : N.rightModule.M)))) = _
  rw [tensorQuotientMap_mk_tmul, tensorQuotientInverse_pure]
  rfl

private theorem tensorQuotient_ext (M : DifferentialGradedModule A) (N : Bimodule A B)
    {P : Type*} [AddCommGroup P] [Module R P]
    (f g : tensorQuotientTotal M N →ₗ[R] P)
    (h : ∀ x y, f (tensorQuotientRawMap M N (x ⊗ₜ[R] y)) =
      g (tensorQuotientRawMap M N (x ⊗ₜ[R] y))) : f = g := by
  apply LinearMap.ext
  intro z
  obtain ⟨z, rfl⟩ := tensorQuotientMap_surjective M N z
  induction z using Submodule.Quotient.induction_on with
  | _ z =>
    induction z using TensorProduct.inductionOn with
    | add x y hx hy =>
      simpa only [Submodule.Quotient.mk_add, map_add] using congrArg₂ (· + ·) hx hy
    | tmul x y => exact h x y

private noncomputable def tensorQuotientLift (M : DifferentialGradedModule A)
    (N : Bimodule A B) {P : Type*} [AddCommGroup P] [Module R P]
    (t : M.M →ₗ[R] N.rightModule.M →ₗ[R] P)
    (h : ∀ (p q n : ℤ) (x : M.grading p) (y : N.rightModule.grading q)
      (a : A.grading n), t (MulOpposite.op (a : A.A) • (x : M.M)) y =
        t x (leftAct N a y : N.rightModule.M)) :
    tensorQuotientTotal M N →ₗ[R] P := by
  refine ((tensorBalanceRelations M N).liftQ (TensorProduct.lift t) ?_).comp
    (tensorQuotientInverse M N)
  apply Submodule.span_le.mpr
  rintro z ⟨p, q, n, x, y, a, rfl⟩
  change TensorProduct.lift t _ = 0
  rw [map_sub, TensorProduct.lift.tmul, TensorProduct.lift.tmul, h, sub_self]

private theorem tensorQuotientLift_tmul (M : DifferentialGradedModule A) (N : Bimodule A B)
    {P : Type*} [AddCommGroup P] [Module R P]
    (t : M.M →ₗ[R] N.rightModule.M →ₗ[R] P)
    (h : ∀ (p q n : ℤ) (x : M.grading p) (y : N.rightModule.grading q)
      (a : A.grading n), t (MulOpposite.op (a : A.A) • (x : M.M)) y =
        t x (leftAct N a y : N.rightModule.M))
    (x : M.M) (y : N.rightModule.M) :
    tensorQuotientLift M N t h (tensorQuotientRawMap M N (x ⊗ₜ[R] y)) = t x y := by
  have hinv := LinearMap.congr_fun (tensorQuotientInverse_map M N)
    ((tensorBalanceRelations M N).mkQ (x ⊗ₜ[R] y))
  change tensorQuotientInverse M N (tensorQuotientRawMap M N (x ⊗ₜ[R] y)) =
    (tensorBalanceRelations M N).mkQ (x ⊗ₜ[R] y) at hinv
  simp only [tensorQuotientLift, LinearMap.comp_apply, hinv]
  rfl


/-! ### The differential on the relative tensor product -/

private noncomputable def tensorComponentDifferentialPair (M : DifferentialGradedModule A)
    (N : Bimodule A B) (k p q : ℤ) (h : p + q = k) :
    (M.grading p ⊗[R] N.rightModule.grading q) →ₗ[R] tensorComponents M N (k + 1) := by
  let d₁ := (DirectSum.lof R ({pq : ℤ × ℤ // pq.1 + pq.2 = k + 1})
      (fun pq => (M.grading pq.val.1 ⊗[R] N.rightModule.grading pq.val.2))
      ⟨(p + 1, q), by omega⟩).comp
    (TensorProduct.map (M.gradedDifferential p)
      (LinearMap.id : N.rightModule.grading q →ₗ[R] N.rightModule.grading q))
  let d₂ := (DirectSum.lof R ({pq : ℤ × ℤ // pq.1 + pq.2 = k + 1})
      (fun pq => (M.grading pq.val.1 ⊗[R] N.rightModule.grading pq.val.2))
      ⟨(p, q + 1), by omega⟩).comp
    (TensorProduct.map (LinearMap.id : M.grading p →ₗ[R] M.grading p)
      (N.rightModule.gradedDifferential q))
  exact d₁ + (p.negOnePow : R) • d₂

private noncomputable def tensorComponentsDifferential (M : DifferentialGradedModule A)
    (N : Bimodule A B) (k : ℤ) :
    tensorComponents M N k →ₗ[R] tensorComponents M N (k + 1) :=
  DirectSum.toModule R _ _ fun pq =>
    tensorComponentDifferentialPair M N k pq.val.1 pq.val.2 pq.property

private theorem tensorComponentsDifferential_of (M : DifferentialGradedModule A)
    (N : Bimodule A B) (k p q : ℤ) (h : p + q = k)
    (x : M.grading p) (y : N.rightModule.grading q) :
    tensorComponentsDifferential M N k
        (DirectSum.of (fun pq : {pq : ℤ × ℤ // pq.1 + pq.2 = k} =>
          (M.grading pq.val.1 ⊗[R] N.rightModule.grading pq.val.2)) ⟨(p, q), h⟩ (x ⊗ₜ[R] y)) =
      DirectSum.of (fun pq : {pq : ℤ × ℤ // pq.1 + pq.2 = k + 1} =>
          (M.grading pq.val.1 ⊗[R] N.rightModule.grading pq.val.2)) ⟨(p + 1, q), by omega⟩
          (M.gradedDifferential p x ⊗ₜ[R] y) +
        (p.negOnePow : R) •
          DirectSum.of (fun pq : {pq : ℤ × ℤ // pq.1 + pq.2 = k + 1} =>
              (M.grading pq.val.1 ⊗[R] N.rightModule.grading pq.val.2)) ⟨(p, q + 1), by omega⟩
            (x ⊗ₜ[R] N.rightModule.gradedDifferential q y) := by
  rw [← DirectSum.lof_eq_of (R := R)
    (ι := {pq : ℤ × ℤ // pq.1 + pq.2 = k})
    (M := fun pq => (M.grading pq.val.1 ⊗[R] N.rightModule.grading pq.val.2))
    (i := ⟨(p, q), h⟩) (b := x ⊗ₜ[R] y)]
  rw [tensorComponentsDifferential, DirectSum.toModule_lof]
  simp [tensorComponentDifferentialPair, LinearMap.comp_apply,
    LinearMap.add_apply, LinearMap.smul_apply, TensorProduct.map_tmul]
  simp only [DirectSum.lof_eq_of]

private theorem tensorBalanceGeneratorAt_differential (M : DifferentialGradedModule A)
    (N : Bimodule A B) (k p q n : ℤ) (h : p + n + q = k)
    (x : M.grading p) (y : N.rightModule.grading q) (a : A.grading n) :
    tensorComponentsDifferential M N k (tensorBalanceGeneratorAt M N k p q n h x y a) =
      tensorBalanceGeneratorAt M N (k + 1) (p + 1) q n (by omega)
        (M.gradedDifferential p x) y a +
      (p.negOnePow : R) •
        tensorBalanceGeneratorAt M N (k + 1) p q (n + 1) (by omega) x y
          ⟨A.d a, A.d_mem n a a.property⟩ +
      ((p + n).negOnePow : R) •
        tensorBalanceGeneratorAt M N (k + 1) p (q + 1) n (by omega) x
          (N.rightModule.gradedDifferential q y) a := by
  apply tensorComponentInclusion_injective M N (k + 1)
  simp only [tensorBalanceGeneratorAt, map_sub, map_add, map_smul]
  rw [tensorComponentsDifferential_of M N k (p + n) q (by omega) _ y,
    tensorComponentsDifferential_of M N k p (q + n) (by omega) x _]
  simp only [map_add, map_smul]
  repeat rw [tensorComponentInclusion_of_tmul]
  simp only [← leftTot_coe]
  have hleft := leftTot_d N a (y : N.rightModule.M)
  simp only [gradedDifferential_apply, ← leftTot_coe]
  rw [M.leibniz p n (x : M.M) (a : A.A) x.property a.property]
  simp only [TensorProduct.add_tmul, ← Int.cast_smul_eq_zsmul R, TensorProduct.smul_tmul,
    TensorProduct.tmul_smul, smul_sub]
  rw [hleft]
  simp only [TensorProduct.tmul_add, ← Int.cast_smul_eq_zsmul R,
    TensorProduct.tmul_smul, smul_add, smul_smul,
    Int.negOnePow_add, Units.val_mul, Int.cast_mul]
  norm_num only [Int.negOnePow_one, Units.val_neg, Units.val_one,
    Int.cast_neg, Int.cast_one, mul_neg, mul_one, neg_smul]
  abel


private theorem tensorComponentsDifferential_sq (M : DifferentialGradedModule A)
    (N : Bimodule A B) (k : ℤ) :
    tensorComponentsDifferential M N (k + 1) ∘ₗ tensorComponentsDifferential M N k = 0 := by
  apply LinearMap.ext
  intro z
  change tensorComponentsDifferential M N (k + 1) (tensorComponentsDifferential M N k z) = 0
  induction z using DirectSum.induction_on with
  | zero => simp
  | add x y hx hy => simp [map_add, hx, hy]
  | of pq x =>
      rcases pq with ⟨⟨p, q⟩, hpq⟩
      induction x using TensorProduct.inductionOn with
      | add x y hx hy => simp [map_add, hx, hy]
      | tmul x y =>
          rw [tensorComponentsDifferential_of M N k p q hpq x y, map_add, map_smul,
            tensorComponentsDifferential_of M N (k + 1) (p + 1) q (by omega)
              (M.gradedDifferential p x) y,
            tensorComponentsDifferential_of M N (k + 1) p (q + 1) (by omega)
              x (N.rightModule.gradedDifferential q y)]
          have hM := LinearMap.congr_fun M.d_comp_d (x : M.M)
          have hN := LinearMap.congr_fun N.rightModule.d_comp_d (y : N.rightModule.M)
          simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hM hN
          have hM' : M.gradedDifferential (p + 1) (M.gradedDifferential p x) = 0 :=
            Subtype.ext hM
          have hN' : N.rightModule.gradedDifferential (q + 1)
              (N.rightModule.gradedDifferential q y) = 0 := Subtype.ext hN
          simp only [hM', hN', map_zero, TensorProduct.zero_tmul,
            TensorProduct.tmul_zero, zero_add]
          have hsign : (Int.negOnePow 1 : R) = -1 := by norm_num
          have hp1 : ((p + 1).negOnePow : R) + (p.negOnePow : R) = 0 := by
            rw [Int.negOnePow_add]
            push_cast
            rw [hsign]
            ring
          simp only [smul_zero, add_zero]
          rw [← add_smul, hp1, zero_smul]

private theorem tensorComponentsDifferential_mem (M : DifferentialGradedModule A)
    (N : Bimodule A B) (k : ℤ) :
    tensorBalanceRelationsAt M N k ≤
      (tensorBalanceRelationsAt M N (k + 1)).comap (tensorComponentsDifferential M N k) := by
  apply Submodule.span_le.mpr
  rintro z ⟨p, q, n, x, y, a, h, rfl⟩
  change tensorComponentsDifferential M N k _ ∈ tensorBalanceRelationsAt M N (k + 1)
  rw [tensorBalanceGeneratorAt_differential]
  apply Submodule.add_mem
  · apply Submodule.add_mem
    · exact Submodule.subset_span ⟨p + 1, q, n, M.gradedDifferential p x, y, a, by omega, rfl⟩
    · apply Submodule.smul_mem
      exact Submodule.subset_span ⟨p, q, n + 1, x, y,
        ⟨A.d a, A.d_mem n a a.property⟩, by omega, rfl⟩
  · apply Submodule.smul_mem
    exact Submodule.subset_span ⟨p, q + 1, n, x, N.rightModule.gradedDifferential q y,
      a, by omega, rfl⟩

private noncomputable def tensorQuotientDifferential (M : DifferentialGradedModule A)
    (N : Bimodule A B) (k : ℤ) :
    tensorQuotientPiece M N k →ₗ[R] tensorQuotientPiece M N (k + 1) :=
  (tensorBalanceRelationsAt M N k).mapQ (tensorBalanceRelationsAt M N (k + 1))
    (tensorComponentsDifferential M N k) (tensorComponentsDifferential_mem M N k)

private theorem tensorQuotientDifferential_sq (M : DifferentialGradedModule A)
    (N : Bimodule A B) (k : ℤ) :
    tensorQuotientDifferential M N (k + 1) ∘ₗ tensorQuotientDifferential M N k = 0 := by
  apply (tensorBalanceRelationsAt M N k).linearMap_qext
  apply LinearMap.ext
  intro x
  change (tensorBalanceRelationsAt M N (k + 1 + 1)).mkQ
    (tensorComponentsDifferential M N (k + 1) (tensorComponentsDifferential M N k x)) = 0
  have hd := LinearMap.congr_fun (tensorComponentsDifferential_sq M N k) x
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hd
  rw [hd, map_zero]

private noncomputable def tensorTotalDifferential (M : DifferentialGradedModule A)
    (N : Bimodule A B) : tensorQuotientTotal M N →ₗ[R] tensorQuotientTotal M N :=
  DirectSum.toModule R ℤ _ fun k =>
    (DirectSum.lof R ℤ (tensorQuotientPiece M N) (k + 1)).comp
      (tensorQuotientDifferential M N k)

private theorem tensorTotalDifferential_of (M : DifferentialGradedModule A)
    (N : Bimodule A B) (k : ℤ) (x : tensorQuotientPiece M N k) :
    tensorTotalDifferential M N (DirectSum.of _ k x) =
      DirectSum.of _ (k + 1) (tensorQuotientDifferential M N k x) := by
  change DirectSum.toModule R ℤ _ _ (DirectSum.lof R ℤ _ k x) = _
  rw [DirectSum.toModule_lof]
  rfl

private theorem tensorTotalDifferential_sq (M : DifferentialGradedModule A)
    (N : Bimodule A B) :
    tensorTotalDifferential M N ∘ₗ tensorTotalDifferential M N = 0 := by
  apply LinearMap.ext
  intro x
  change tensorTotalDifferential M N (tensorTotalDifferential M N x) = 0
  induction x using DirectSum.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]
  | of k x =>
    rw [tensorTotalDifferential_of, tensorTotalDifferential_of]
    have hd := LinearMap.congr_fun (tensorQuotientDifferential_sq M N k) x
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hd
    rw [hd, map_zero]

private theorem tensorQuotientInverse_injective (M : DifferentialGradedModule A)
    (N : Bimodule A B) : Function.Injective (tensorQuotientInverse M N) := by
  intro x y h
  obtain ⟨x, rfl⟩ := tensorQuotientMap_surjective M N x
  obtain ⟨y, rfl⟩ := tensorQuotientMap_surjective M N y
  have hx := LinearMap.congr_fun (tensorQuotientInverse_map M N) x
  have hy := LinearMap.congr_fun (tensorQuotientInverse_map M N) y
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at hx hy
  rw [hx, hy] at h
  exact congrArg (tensorQuotientMap M N) h

private theorem tensorQuotientInverse_rawMap (M : DifferentialGradedModule A)
    (N : Bimodule A B) (z : M.M ⊗[R] N.rightModule.M) :
    tensorQuotientInverse M N (tensorQuotientRawMap M N z) =
      (tensorBalanceRelations M N).mkQ z :=
  LinearMap.congr_fun (tensorQuotientInverse_map M N) ((tensorBalanceRelations M N).mkQ z)

private theorem tensorQuotientRawMap_tmul (M : DifferentialGradedModule A) (N : Bimodule A B)
    (p q : ℤ) (x : M.grading p) (y : N.rightModule.grading q) :
    tensorQuotientRawMap M N ((x : M.M) ⊗ₜ[R] (y : N.rightModule.M)) =
      tensorQuotientPureAt M N (p + q) p q rfl x y :=
  tensorQuotientMap_mk_tmul M N p q x y

private theorem tensorTotalDifferential_tmul (M : DifferentialGradedModule A)
    (N : Bimodule A B) (p q : ℤ) (x : M.grading p) (y : N.rightModule.grading q) :
    tensorTotalDifferential M N
      (tensorQuotientRawMap M N ((x : M.M) ⊗ₜ[R] (y : N.rightModule.M))) =
      tensorQuotientRawMap M N (M.d x ⊗ₜ[R] (y : N.rightModule.M)) +
        (p.negOnePow : R) • tensorQuotientRawMap M N
          ((x : M.M) ⊗ₜ[R] N.rightModule.d y) := by
  apply tensorQuotientInverse_injective M N
  rw [map_add, map_smul, tensorQuotientInverse_rawMap, tensorQuotientInverse_rawMap,
    tensorQuotientRawMap_tmul]
  unfold tensorQuotientPureAt
  rw [tensorTotalDifferential_of]
  change tensorQuotientInverse M N (DirectSum.of _ (p + q + 1) (Submodule.Quotient.mk
    (tensorComponentsDifferential M N (p + q) (DirectSum.of _ ⟨(p, q), rfl⟩ (x ⊗ₜ[R] y))))) = _
  rw [tensorQuotientInverse_of]
  rw [tensorComponentsDifferential_of M N (p + q) p q rfl x y]
  simp only [map_add, map_smul]
  repeat rw [tensorComponentInclusion_of_tmul]
  simp only [gradedDifferential_apply]

private theorem tensorQuotientRawMap_balance (M : DifferentialGradedModule A)
    (N : Bimodule A B) (p n : ℤ) (x : M.grading p) (a : A.grading n) (y : N.rightModule.M) :
    tensorQuotientRawMap M N ((MulOpposite.op (a : A.A) • (x : M.M)) ⊗ₜ[R] y) =
      tensorQuotientRawMap M N ((x : M.M) ⊗ₜ[R] leftTot N (a : A.A) y) := by
  induction y using DirectSum.Decomposition.inductionOn N.rightModule.grading with
  | zero => simp
  | add y z hy hz => simp only [map_add, TensorProduct.tmul_add, hy, hz]
  | @homogeneous q y =>
    rw [leftTot_coe N a y]
    change tensorQuotientMap M N (Submodule.Quotient.mk _) =
      tensorQuotientMap M N (Submodule.Quotient.mk _)
    congr 1
    apply (Submodule.Quotient.eq _).mpr
    exact Submodule.subset_span ⟨p, q, n, x, y, a, rfl⟩


/-! ### The right `B`-module structure and the grading -/

private noncomputable def tensorRightMap (M : DifferentialGradedModule A) (N : Bimodule A B)
    (b : B.Aᵐᵒᵖ) : tensorQuotientTotal M N →ₗ[R] tensorQuotientTotal M N := by
  let t := (TensorProduct.mk R M.M N.rightModule.M).compr₂ₛₗ
    ((tensorQuotientRawMap M N).comp
      (TensorProduct.map LinearMap.id (DistribSMul.toLinearMap R N.rightModule.M b)))
  refine tensorQuotientLift M N t ?_
  intro p q n x y a
  change tensorQuotientRawMap M N ((MulOpposite.op (a : A.A) • (x : M.M)) ⊗ₜ[R]
    (b • (y : N.rightModule.M))) =
      tensorQuotientRawMap M N ((x : M.M) ⊗ₜ[R] (b • (leftAct N a y : N.rightModule.M)))
  rw [tensorQuotientRawMap_balance, leftTot_op_smul, ← leftTot_coe]

private theorem tensorRightMap_tmul (M : DifferentialGradedModule A) (N : Bimodule A B)
    (b : B.Aᵐᵒᵖ) (x : M.M) (y : N.rightModule.M) :
    tensorRightMap M N b (tensorQuotientRawMap M N (x ⊗ₜ[R] y)) =
      tensorQuotientRawMap M N (x ⊗ₜ[R] (b • y)) := by
  unfold tensorRightMap
  rw [tensorQuotientLift_tmul]
  rfl

@[instance_reducible] private noncomputable def tensorRightModule
    (M : DifferentialGradedModule A) (N : Bimodule A B) :
    Module B.Aᵐᵒᵖ (tensorQuotientTotal M N) where
  smul b x := tensorRightMap M N b x
  one_smul x := by
    have h : tensorRightMap M N 1 = LinearMap.id := by
      apply tensorQuotient_ext M N
      intro x y
      simp only [tensorRightMap_tmul, one_smul, LinearMap.id_apply]
    exact LinearMap.congr_fun h x
  mul_smul b c x := by
    have h : tensorRightMap M N (b * c) = tensorRightMap M N b ∘ₗ tensorRightMap M N c := by
      apply tensorQuotient_ext M N
      intro x y
      simp only [LinearMap.comp_apply, tensorRightMap_tmul, mul_smul]
    exact LinearMap.congr_fun h x
  smul_zero b := map_zero _
  smul_add b x y := map_add _ _ _
  add_smul b c x := by
    have h : tensorRightMap M N (b + c) = tensorRightMap M N b + tensorRightMap M N c := by
      apply tensorQuotient_ext M N
      intro x y
      simp only [LinearMap.add_apply, tensorRightMap_tmul, add_smul,
        TensorProduct.tmul_add, map_add]
    exact LinearMap.congr_fun h x
  zero_smul x := by
    have h : tensorRightMap M N 0 = 0 := by
      apply tensorQuotient_ext M N
      intro x y
      simp only [tensorRightMap_tmul, zero_smul, TensorProduct.tmul_zero,
        map_zero, LinearMap.zero_apply]
    exact LinearMap.congr_fun h x

attribute [local instance] tensorRightModule

private theorem tensorRight_smul_tmul (M : DifferentialGradedModule A) (N : Bimodule A B)
    (b : B.Aᵐᵒᵖ) (x : M.M) (y : N.rightModule.M) :
    b • tensorQuotientRawMap M N (x ⊗ₜ[R] y) = tensorQuotientRawMap M N (x ⊗ₜ[R] (b • y)) :=
  tensorRightMap_tmul M N b x y

private theorem tensorRightScalarTower (M : DifferentialGradedModule A) (N : Bimodule A B) :
    IsScalarTower R B.Aᵐᵒᵖ (tensorQuotientTotal M N) where
  smul_assoc r b x := by
    have h : tensorRightMap M N (r • b) = r • tensorRightMap M N b := by
      apply tensorQuotient_ext M N
      intro x y
      simp only [tensorRightMap_tmul, LinearMap.smul_apply, smul_assoc,
        TensorProduct.tmul_smul, map_smul]
    exact LinearMap.congr_fun h x

attribute [local instance] tensorRightScalarTower

private noncomputable abbrev tensorGrading (M : DifferentialGradedModule A) (N : Bimodule A B)
    (k : ℤ) : Submodule R (tensorQuotientTotal M N) :=
  DirectSum.rangeGrading R (tensorQuotientPiece M N) k

@[instance_reducible] private noncomputable def tensorGradingDecomposition
    (M : DifferentialGradedModule A) (N : Bimodule A B) :
    DirectSum.Decomposition (tensorGrading M N) :=
  DirectSum.rangeGradingDecomposition R (tensorQuotientPiece M N)

attribute [local instance] tensorGradingDecomposition

private theorem tensorGrading_tmul (M : DifferentialGradedModule A) (N : Bimodule A B)
    (p q : ℤ) (x : M.grading p) (y : N.rightModule.grading q) :
    tensorQuotientRawMap M N ((x : M.M) ⊗ₜ[R] (y : N.rightModule.M)) ∈
      tensorGrading M N (p + q) := by
  rw [tensorQuotientRawMap_tmul]
  exact ⟨_, rfl⟩

private theorem tensorGrading_induction (M : DifferentialGradedModule A) (N : Bimodule A B)
    (k : ℤ) {C : tensorQuotientTotal M N → Prop}
    (hzero : C 0) (hadd : ∀ x y, C x → C y → C (x + y))
    (hpure : ∀ (p q : ℤ), p + q = k → ∀ (x : M.grading p) (y : N.rightModule.grading q),
      C (tensorQuotientRawMap M N ((x : M.M) ⊗ₜ[R] (y : N.rightModule.M))))
    (z : tensorQuotientTotal M N) (hz : z ∈ tensorGrading M N k) : C z := by
  obtain ⟨z, rfl⟩ := hz
  induction z using Submodule.Quotient.induction_on with
  | _ z =>
    induction z using DirectSum.induction_on with
    | zero => simpa only [Submodule.Quotient.mk_zero, map_zero] using hzero
    | add x y hx hy =>
      simpa only [Submodule.Quotient.mk_add, map_add] using hadd _ _ hx hy
    | of pq z =>
      induction z using TensorProduct.inductionOn with
      | add x y hx hy =>
        simpa only [map_add, Submodule.Quotient.mk_add] using hadd _ _ hx hy
      | tmul x y =>
        rcases pq with ⟨⟨p, q⟩, h⟩
        subst k
        simpa only [tensorQuotientRawMap_tmul, tensorQuotientPureAt,
          DirectSum.lof_eq_of] using hpure p q rfl x y

/-- A linear map on the tensor product lands in a submodule on the degree-`k` part once it does
so on pure tensors of that total degree. -/
private theorem tensorGrading_map_mem (M : DifferentialGradedModule A) (N : Bimodule A B)
    {P : Type*} [AddCommGroup P] [Module R P] (S : Submodule R P)
    (f : tensorQuotientTotal M N →ₗ[R] P) (k : ℤ)
    (h : ∀ (p q : ℤ), p + q = k → ∀ (x : M.grading p) (y : N.rightModule.grading q),
      f (tensorQuotientRawMap M N ((x : M.M) ⊗ₜ[R] (y : N.rightModule.M))) ∈ S)
    (z : tensorQuotientTotal M N) (hz : z ∈ tensorGrading M N k) : f z ∈ S :=
  tensorGrading_induction M N k (C := fun z => f z ∈ S) (by rw [map_zero]; exact S.zero_mem)
    (fun x y hx hy ↦ by simpa only [map_add] using add_mem hx hy) h z hz

private theorem tensorTotalDifferential_mem (M : DifferentialGradedModule A) (N : Bimodule A B)
    (k : ℤ) (x : tensorQuotientTotal M N) (hx : x ∈ tensorGrading M N k) :
    tensorTotalDifferential M N x ∈ tensorGrading M N (k + 1) := by
  obtain ⟨x, rfl⟩ := hx
  exact ⟨tensorQuotientDifferential M N k x, (tensorTotalDifferential_of M N k x).symm⟩

private theorem tensorRight_smul_mem (M : DifferentialGradedModule A) (N : Bimodule A B)
    (k n : ℤ) (z : tensorQuotientTotal M N) (b : B.A)
    (hz : z ∈ tensorGrading M N k) (hb : b ∈ B.grading n) :
    MulOpposite.op b • z ∈ tensorGrading M N (k + n) := by
  apply tensorGrading_induction M N k (C := fun z =>
    MulOpposite.op b • z ∈ tensorGrading M N (k + n))
    (by simp only [smul_zero]; exact Submodule.zero_mem _) ?_ ?_ z hz
  · intro x y hx hy
    rw [smul_add]
    exact Submodule.add_mem _ hx hy
  · intro p q h x y
    rw [tensorRight_smul_tmul]
    simpa only [← h, add_assoc] using tensorGrading_tmul M N p (q + n) x
      ⟨MulOpposite.op b • (y : N.rightModule.M), N.rightModule.smul_mem q n y b y.property hb⟩

private theorem tensorTotalDifferential_leibniz (M : DifferentialGradedModule A)
    (N : Bimodule A B) (k n : ℤ) (z : tensorQuotientTotal M N) (b : B.A)
    (hz : z ∈ tensorGrading M N k) (hb : b ∈ B.grading n) :
    tensorTotalDifferential M N (MulOpposite.op b • z) =
      MulOpposite.op b • tensorTotalDifferential M N z +
        (k.negOnePow : ℤ) • (MulOpposite.op (B.d b) • z) := by
  apply tensorGrading_induction M N k (C := fun z =>
    tensorTotalDifferential M N (MulOpposite.op b • z) =
      MulOpposite.op b • tensorTotalDifferential M N z +
        (k.negOnePow : ℤ) • (MulOpposite.op (B.d b) • z))
    (by simp) ?_ ?_ z hz
  · intro x y hx hy
    simp only [smul_add, map_add, hx, hy]
    abel
  · intro p q h x y
    subst k
    rw [tensorRight_smul_tmul]
    have hd := tensorTotalDifferential_tmul M N p (q + n) x
      ⟨MulOpposite.op b • (y : N.rightModule.M), N.rightModule.smul_mem q n y b y.property hb⟩
    rw [hd, tensorTotalDifferential_tmul, smul_add,
      smul_comm (MulOpposite.op b) (p.negOnePow : R),
      tensorRight_smul_tmul, tensorRight_smul_tmul, tensorRight_smul_tmul,
      N.rightModule.leibniz q n y b y.property hb]
    simp only [TensorProduct.tmul_add, ← Int.cast_smul_eq_zsmul R,
      TensorProduct.tmul_smul, map_add, map_smul, smul_add, smul_smul,
      Int.negOnePow_add, Units.val_mul, Int.cast_mul]
    abel

/-- The relative tensor product `M ⊗_A N` of a right differential graded `A`-module with a
differential graded `(A, B)`-bimodule, as a right differential graded `B`-module. -/
@[reducible] private noncomputable def tensorDGModule (M : DifferentialGradedModule A)
    (N : Bimodule A B) : DifferentialGradedModule B where
  M := tensorQuotientTotal M N
  grading := tensorGrading M N
  smul_mem := tensorRight_smul_mem M N
  d := tensorTotalDifferential M N
  d_comp_d := tensorTotalDifferential_sq M N
  d_mem := tensorTotalDifferential_mem M N
  leibniz := tensorTotalDifferential_leibniz M N


/-! ### The tensor functor of differential graded categories -/

private theorem tensorQuotient_ext_homogeneous (M : DifferentialGradedModule A)
    (N : Bimodule A B) {P : Type*} [AddCommGroup P] [Module R P]
    (f g : tensorQuotientTotal M N →ₗ[R] P)
    (h : ∀ (p q : ℤ) (x : M.grading p) (y : N.rightModule.grading q),
      f (tensorQuotientRawMap M N ((x : M.M) ⊗ₜ[R] (y : N.rightModule.M))) =
        g (tensorQuotientRawMap M N ((x : M.M) ⊗ₜ[R] (y : N.rightModule.M)))) : f = g := by
  apply tensorQuotient_ext M N
  intro x y
  exact LinearMap.congr_fun₂ (bilinear_ext_homogeneous M N
    ((TensorProduct.mk R _ _).compr₂ (f ∘ₗ tensorQuotientRawMap M N))
    ((TensorProduct.mk R _ _).compr₂ (g ∘ₗ tensorQuotientRawMap M N)) h) x y

private noncomputable def tensorHomLinear (N : Bimodule A B)
    {L M : DifferentialGradedModule A} {n : ℤ} (f : HomogeneousMap A L M n) :
    tensorQuotientTotal L N →ₗ[R] tensorQuotientTotal M N := by
  let t := (TensorProduct.mk R L.M N.rightModule.M).compr₂ₛₗ
    ((tensorQuotientRawMap M N).comp (TensorProduct.map f.1 LinearMap.id))
  refine tensorQuotientLift L N t ?_
  intro p q m x y a
  change tensorQuotientRawMap M N (f.1 (MulOpposite.op (a : A.A) • (x : L.M)) ⊗ₜ[R]
    (y : N.rightModule.M)) =
      tensorQuotientRawMap M N (f.1 x ⊗ₜ[R] (leftAct N a y : N.rightModule.M))
  rw [f.2.2, ← leftTot_coe]
  exact tensorQuotientRawMap_balance M N (p + n) m ⟨f.1 x, f.2.1 p x x.property⟩ a y

private theorem tensorHomLinear_tmul (N : Bimodule A B)
    {L M : DifferentialGradedModule A} {n : ℤ} (f : HomogeneousMap A L M n)
    (x : L.M) (y : N.rightModule.M) :
    tensorHomLinear N f (tensorQuotientRawMap L N (x ⊗ₜ[R] y)) =
      tensorQuotientRawMap M N (f.1 x ⊗ₜ[R] y) := by
  unfold tensorHomLinear
  rw [tensorQuotientLift_tmul]
  rfl

@[reducible] private noncomputable def tensorHomogeneousMap (N : Bimodule A B)
    {L M : DifferentialGradedModule A} {n : ℤ} (f : HomogeneousMap A L M n) :
    HomogeneousMap B (tensorDGModule L N) (tensorDGModule M N) n := by
  refine ⟨tensorHomLinear N f, ?_, ?_⟩
  · intro k z hz
    refine tensorGrading_map_mem L N _ _ k ?_ z hz
    intro p q h x y
    rw [tensorHomLinear_tmul]
    convert tensorGrading_tmul M N (p + n) q ⟨f.1 x, f.2.1 p x x.property⟩ y using 1
    congr 1
    omega
  · intro b z
    have h : tensorHomLinear N f ∘ₗ tensorRightMap L N (MulOpposite.op b) =
        tensorRightMap M N (MulOpposite.op b) ∘ₗ tensorHomLinear N f := by
      apply tensorQuotient_ext L N
      intro x y
      simp only [LinearMap.comp_apply, tensorHomLinear_tmul, tensorRightMap_tmul]
    exact LinearMap.congr_fun h z

private theorem tensorHomogeneousMap_d (N : Bimodule A B)
    {L M : DifferentialGradedModule A} {n : ℤ} (f : HomogeneousMap A L M n) :
    tensorHomogeneousMap N (homogeneousMapDifferential A f) =
      homogeneousMapDifferential B (tensorHomogeneousMap N f) := by
  apply Subtype.ext
  change tensorHomLinear N (homogeneousMapDifferential A f) =
    tensorTotalDifferential M N ∘ₗ tensorHomLinear N f -
      gradedSign R n • (tensorHomLinear N f ∘ₗ tensorTotalDifferential L N)
  apply tensorQuotient_ext_homogeneous L N
  intro p q x y
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    tensorHomLinear_tmul]
  have hd := tensorTotalDifferential_tmul M N (p + n) q ⟨f.1 x, f.2.1 p x x.property⟩ y
  rw [hd, tensorTotalDifferential_tmul]
  simp only [map_add, map_smul, tensorHomLinear_tmul, homogeneousMapDifferential_val,
    LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    TensorProduct.sub_tmul, TensorProduct.smul_tmul, TensorProduct.tmul_smul, map_sub, smul_add,
    smul_smul, Int.negOnePow_add, Units.val_mul, Int.cast_mul]
  rw [show gradedSign R n = ((n.negOnePow : ℤ) : R) from (intCast_negOnePow n).symm,
    mul_comm ((p.negOnePow : ℤ) : R) ((n.negOnePow : ℤ) : R)]
  abel

private noncomputable def tensorDGCategoryFunctor (N : Bimodule A B) :
    DGCategory.DGFunctor (dgCategory.{u, u, u} A) (dgCategory.{u, u, u} B) where
  obj M := tensorDGModule M N
  map := tensorHomogeneousMap N
  map_add := by
    intro X Y n f g
    apply Subtype.ext
    change tensorHomLinear N (f + g) = tensorHomLinear N f + tensorHomLinear N g
    apply tensorQuotient_ext _ N
    intro x y
    rw [tensorHomLinear_tmul, LinearMap.add_apply, tensorHomLinear_tmul, tensorHomLinear_tmul,
      ← map_add, ← TensorProduct.add_tmul]
    rfl
  map_smul := by
    intro X Y n r f
    apply Subtype.ext
    change tensorHomLinear N (r • f) = r • tensorHomLinear N f
    apply tensorQuotient_ext _ N
    intro x y
    rw [tensorHomLinear_tmul, LinearMap.smul_apply, tensorHomLinear_tmul,
      ← map_smul, TensorProduct.smul_tmul']
    rfl
  map_d := tensorHomogeneousMap_d N
  map_comp h g f := by
    apply Subtype.ext
    change tensorHomLinear N (homogeneousMapComp A h g f) =
      tensorHomLinear N g ∘ₗ tensorHomLinear N f
    apply tensorQuotient_ext _ N
    intro x y
    simp [tensorHomLinear_tmul, homogeneousMapComp_val]
  map_id M := by
    apply Subtype.ext
    change tensorHomLinear N (homogeneousMapId A M) = LinearMap.id
    apply tensorQuotient_ext M N
    intro x y
    simp [tensorHomLinear_tmul, homogeneousMapId_val]

/-- The tensor functor of differential graded categories attached to a differential graded
bimodule, together with the universal pure tensors that characterize it. -/
structure TensorDGFunctorData (N : Bimodule A B) where
  /-- The differential graded functor. -/
  functor : DGCategory.DGFunctor (dgCategory.{u, u, u} A) (dgCategory.{u, u, u} B)
  /-- The universal balanced bilinear map into its value. -/
  pure (M : DifferentialGradedModule.{u, u, u} A) : BalancedBilinearMap M N (functor.obj M)
  /-- Its universal property. -/
  universal (M : DifferentialGradedModule.{u, u, u} A) (P : DifferentialGradedModule.{u, u, u} B)
      (t : BalancedBilinearMap M N P) :
    ∃! g : DifferentialGradedModule.Hom (functor.obj M) P,
      ∀ (x : M.M) (y : N.rightModule.M),
        g.toFun ((pure M).toLinearMap x y) = t.toLinearMap x y
  /-- Its action on a homogeneous morphism, on pure tensors. -/
  map_pure {L M : DifferentialGradedModule.{u, u, u} A} {n : ℤ}
      (f : (dgCategory.{u, u, u} A).Hom L M n)
      (x : L.M) (y : N.rightModule.M) :
    (functor.map f).1 ((pure L).toLinearMap x y) = (pure M).toLinearMap (f.1 x) y

private noncomputable def tensorPureBalanced (M : DifferentialGradedModule A)
    (N : Bimodule A B) : BalancedBilinearMap M N (tensorDGModule M N) where
  toLinearMap := (TensorProduct.mk R M.M N.rightModule.M).compr₂ₛₗ (tensorQuotientRawMap M N)
  map_grading := tensorGrading_tmul M N
  map_d p x y := by
    change tensorTotalDifferential M N (tensorQuotientRawMap M N ((x : M.M) ⊗ₜ[R] y)) =
      tensorQuotientRawMap M N (M.d x ⊗ₜ[R] y) +
        (p.negOnePow : ℤ) • tensorQuotientRawMap M N ((x : M.M) ⊗ₜ[R] N.rightModule.d y)
    induction y using DirectSum.Decomposition.inductionOn N.rightModule.grading with
    | zero => simp
    | add y z hy hz =>
      simp only [TensorProduct.tmul_add, map_add, smul_add, hy, hz]
      abel
    | @homogeneous q y =>
      simpa only [Int.cast_smul_eq_zsmul] using tensorTotalDifferential_tmul M N p q x y
  balance p q n x y a := by
    change tensorQuotientRawMap M N
        ((MulOpposite.op (a : A.A) • (x : M.M)) ⊗ₜ[R] (y : N.rightModule.M)) =
      tensorQuotientRawMap M N ((x : M.M) ⊗ₜ[R] (leftAct N a y : N.rightModule.M))
    rw [← leftTot_coe]
    exact tensorQuotientRawMap_balance M N p n x a y
  map_right x y b := (tensorRight_smul_tmul M N (MulOpposite.op b) x y).symm

private noncomputable def tensorBalancedLift (M : DifferentialGradedModule A)
    (N : Bimodule A B) (P : DifferentialGradedModule B) (t : BalancedBilinearMap M N P) :
    DifferentialGradedModule.Hom (tensorDGModule M N) P where
  toFun := tensorQuotientLift M N t.toLinearMap (balanced_leftAct t)
  map_smul z b := by
    have h : tensorQuotientLift M N t.toLinearMap (balanced_leftAct t) ∘ₗ
        tensorRightMap M N (MulOpposite.op b) =
      (DistribSMul.toLinearMap R P.M (MulOpposite.op b)).comp
        (tensorQuotientLift M N t.toLinearMap (balanced_leftAct t)) := by
      apply tensorQuotient_ext M N
      intro x y
      simp only [LinearMap.comp_apply, tensorRightMap_tmul, tensorQuotientLift_tmul,
        DistribSMul.toLinearMap_apply, t.map_right]
    exact LinearMap.congr_fun h z
  map_grading k z hz := by
    refine tensorGrading_map_mem M N (P.grading k)
      (tensorQuotientLift M N t.toLinearMap (balanced_leftAct t)) k ?_ z hz
    intro p q h x y
    rw [tensorQuotientLift_tmul, ← h]
    exact t.map_grading p q x y
  map_d := by
    apply tensorQuotient_ext_homogeneous M N
    intro p q x y
    change tensorQuotientLift M N t.toLinearMap (balanced_leftAct t)
      (tensorTotalDifferential M N (tensorQuotientRawMap M N _)) =
        P.d (tensorQuotientLift M N t.toLinearMap (balanced_leftAct t) (tensorQuotientRawMap M N _))
    rw [tensorTotalDifferential_tmul, map_add, map_smul,
      tensorQuotientLift_tmul, tensorQuotientLift_tmul, tensorQuotientLift_tmul, t.map_d,
      Int.cast_smul_eq_zsmul]

private noncomputable def tensorFunctorData (N : Bimodule A B) : TensorDGFunctorData N := by
  refine ⟨tensorDGCategoryFunctor N, fun M => tensorPureBalanced M N, ?_, ?_⟩
  · intro M P t
    refine ⟨tensorBalancedLift M N P t, ?_, ?_⟩
    · exact tensorQuotientLift_tmul M N t.toLinearMap (balanced_leftAct t)
    · intro g hg
      apply DifferentialGradedModule.Hom.ext
      apply tensorQuotient_ext M N
      intro x y
      exact (hg x y).trans (tensorQuotientLift_tmul M N t.toLinearMap (balanced_leftAct t) x y).symm
  · exact fun f ↦ tensorHomLinear_tmul N f

/-- **Stacks 09LM.** Tensoring with a differential graded `(A, B)`-bimodule is a functor of
differential graded categories. -/
@[stacks 09LM "the DG functor", no_expose]
noncomputable def tensorDGFunctor (N : Bimodule A B) : TensorDGFunctorData N :=
  Classical.choice (show Nonempty (TensorDGFunctorData N) from ⟨tensorFunctorData N⟩)

/-- **Stacks 09LM.** The induced functor on the categories of differential graded modules. -/
@[stacks 09LM "the ordinary functor",
  stacks 09LQ "the functor Mod_(A,d) -> Mod_(B,d), M |-> M (x)_A N"]
noncomputable abbrev tensorCompFunctor (N : Bimodule A B) :
    DifferentialGradedModule A ⥤ DifferentialGradedModule B :=
  (dgCategoryCompEquivalence A).1.inverse ⋙
    (tensorDGFunctor N).functor.onComp ⋙ (dgCategoryCompEquivalence B).1.functor

/-- **Stacks 09LM.** The induced functor on the homotopy categories. -/
@[stacks 09LM "the homotopy functor"]
noncomputable def tensorHomotopyFunctor (N : Bimodule A B) :
    HomotopyCategory A ⥤ HomotopyCategory B :=
  (homotopyCategoryEquivalence A).functor ⋙
    (tensorDGFunctor N).functor.onK ⋙ (homotopyCategoryEquivalence B).inverse

private noncomputable def tensorQuotientIso (N : Bimodule A B) :
    (tensorCompFunctor N ⋙ toHomotopyCategory B) ≅
      (toHomotopyCategory A ⋙ tensorHomotopyFunctor N) := by
  let F := (tensorDGFunctor N).functor
  let E := (dgCategoryCompEquivalence A).1
  let H := (homotopyCategoryEquivalence B).inverse
  have hF := (DGCategory.dgFunctor_induces_functors F).2.2.2.2
  refine (Functor.isoWhiskerLeft (E.inverse ⋙ F.onComp) (complexesQuotientSquareIso B)) ≪≫ ?_
  refine (eqToIso ?_) ≪≫ Functor.isoWhiskerRight (modulesHomotopySquareIso A).symm (F.onK ⋙ H)
  change (E.inverse ⋙ F.onComp) ⋙ DGCategory.compToK (dgCategory.{u, u, u} B) ⋙ H =
    (E.inverse ⋙ DGCategory.compToK (dgCategory.{u, u, u} A)) ⋙ F.onK ⋙ H
  simpa only [Functor.assoc] using congrArg (fun G => E.inverse ⋙ G ⋙ H) hF.symm

/-- **Stacks 09LM.** Passing the ordinary tensor functor to homotopy classes yields the tensor
functor on the homotopy categories. -/
@[stacks 09LM "compatibility with the quotient", no_expose]
noncomputable def tensorCompFunctor_quotient (N : Bimodule A B) :
    (tensorCompFunctor N ⋙ toHomotopyCategory B) ≅
      (toHomotopyCategory A ⋙ tensorHomotopyFunctor N) :=
  Classical.choice (show Nonempty ((tensorCompFunctor N ⋙ toHomotopyCategory B) ≅
    (toHomotopyCategory A ⋙ tensorHomotopyFunctor N)) from ⟨tensorQuotientIso N⟩)

end DifferentialGraded.Bimodule
