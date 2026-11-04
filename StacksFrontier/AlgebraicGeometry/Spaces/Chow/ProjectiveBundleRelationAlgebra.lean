module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Group.Equiv.Basic
public import Mathlib.Algebra.Group.Pi.Lemmas
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Data.Int.Basic

/-!
# The relation defining Chern classes through the projective bundle formula, formally

In Situation 0EDT let `X/B` be good, `ℰ` a finite locally free `𝒪_X`-module of rank `r` and
`(π : P → X, 𝒪_P(1))` its projective bundle. Stacks 0ERY characterizes the Chern classes of `ℰ`
by the relation

`∑_{i = 0}^{r} (-1)^i c₁(𝒪_P(1))^i ∩ π^*(c_{r - i}(ℰ) ∩ α) = 0`,  `c₀(ℰ) ∩ α = α`,

and its proof derives existence and uniqueness of the maps `c_j(ℰ) ∩ -` from the projective
bundle formula (Stacks 0ERV): the map `(α₀, …, α_{r-1}) ↦ ∑ c₁(𝒪_P(1))^i ∩ π^*α_i` is bijective.

That derivation uses nothing about Chow groups beyond their group structure, so it is carried out
here for two arbitrary `ℤ`-graded families of abelian groups `A` (the Chow groups of `X`) and `P`
(those of `P`), an additive "pullback" `A_m → P_{m + e}` (the flat pullback `π^*`, of relative
dimension `e = r - 1`) and additive "cap" maps `P_{m + s} → P_m` (the cap products with
`c₁(𝒪_P(1))^s`). The degrees of the operations are given as arguments together with an equation
between them, as for the flat pullback of cycles of this library, so that no transport between
Chow groups of propositionally equal degrees is needed except at one place, `c₀ = id`.

## Main definitions

* `AlgebraicGeometry.Space.ProjectiveBundleRelation.degreeCast`: the identification
  `A_a = A_b` for `a = b`.
* `AlgebraicGeometry.Space.ProjectiveBundleRelation.bundleSum`: the map
  `(α_i)_{i < r} ↦ ∑ c₁^i ∩ π^*α_i` of the projective bundle formula, with arbitrary source degrees
  `d i` subject to `d i + e = n + i`.
* `AlgebraicGeometry.Space.ProjectiveBundleRelation.relationSumAt`: the left-hand side
  `∑_{i=0}^{r} (-1)^i c₁^i ∩ π^*(b_{r-i})` of the relation, for a family `b_j ∈ A_{k - j}`.
* `AlgebraicGeometry.Space.ProjectiveBundleRelation.relationSum`: the same for the family
  `b_j = c_j ∩ α` of a family of maps `c_j : A_k → A_{k - j}`.

## Main results

* `AlgebraicGeometry.Space.ProjectiveBundleRelation.eq_of_relationSumAt_eq_zero`: **uniqueness,
  pointwise**: if `π^*`-and-cap is injective in the sense of the projective bundle formula, two
  families `b, b'` with `b₀ = b'₀` both satisfying the relation agree. This is the form the proof
  of bivariance uses: it compares `c_j ∩ h_*α` with `h_*(c_j ∩ α)`.
* `AlgebraicGeometry.Space.ProjectiveBundleRelation.eq_of_relationSum_eq_zero`: uniqueness of the
  maps `c_j`.
* `AlgebraicGeometry.Space.ProjectiveBundleRelation.exists_relationSum_eq_zero`: **existence**
  of additive maps `c_j : A_k → A_{k-j}`, `j = 0, …, r`, with `c₀ = id` satisfying the relation, if
  the map of the projective bundle formula is bijective in every degree.

## References

* [Stacks Project, Tag 0ERY](https://stacks.math.columbia.edu/tag/0ERY)
* [Stacks Project, Tag 0ERV](https://stacks.math.columbia.edu/tag/0ERV)
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry.Space.ProjectiveBundleRelation

open Finset

variable {A : ℤ → Type*} {P : ℤ → Type*} [∀ k, AddCommGroup (A k)] [∀ k, AddCommGroup (P k)]

/-! ### Transport between equal degrees -/

variable (A) in
/-- The identification `A_a = A_b` of the groups of two propositionally equal degrees. -/
def degreeCast {a b : ℤ} (h : a = b) : A a →+ A b := by
  subst h
  exact AddMonoidHom.id (A a)

/-- Transport along `rfl` is the identity. -/
@[simp]
theorem degreeCast_rfl (a : ℤ) (x : A a) : degreeCast A (rfl : a = a) x = x :=
  rfl

/-- Transport along `h` followed by transport along `h'` is transport along `h.trans h'`. -/
theorem degreeCast_degreeCast {a b c : ℤ} (h : a = b) (h' : b = c) (x : A a) :
    degreeCast A h' (degreeCast A h x) = degreeCast A (h.trans h') x := by
  subst h h'
  rfl

/-! ### The data: a pullback and powers of a cap product -/

variable (e : ℤ) (pull : ∀ m n : ℤ, m + e = n → A m →+ P n)
  (cap : ∀ (s : ℕ) (n m : ℤ), n = m + s → P n →+ P m)

/-- The pullback does not see a transport of its source along an equality of degrees. -/
theorem pull_degreeCast {a b n : ℤ} (h : a = b) (hb : b + e = n) (x : A a) :
    pull b n hb (degreeCast A h x) = pull a n (h ▸ hb) x := by
  subst h
  rfl

/-- The pullback of the `i`-th entry of a family does not depend on a rewriting of `i`. -/
private theorem pull_apply_congr {ι : Type*} (f : ι → ℤ) (a : ∀ i, A (f i)) {i i' : ι}
    (hi : i = i') {n : ℤ} (h : f i + e = n) (h' : f i' + e = n) :
    pull (f i) n h (a i) = pull (f i') n h' (a i') := by
  subst hi
  rfl

/-- The degree bookkeeping of the summand of index `i` of the relation. -/
theorem relationTerm_degree (r : ℕ) (k : ℤ) (i : Fin (r + 1)) :
    k - ((Fin.rev i : ℕ) : ℤ) + e = k - r + e + (i : ℕ) := by
  have hi := i.isLt
  rw [Fin.val_rev]
  omega

/-- The map `(α_i)_{i < r} ↦ ∑_{i < r} c₁^i ∩ π^*α_i` of the projective bundle formula
(Stacks 0ERV), from `∏_i A_{d i}` to `P_n`, for any source degrees `d i` with `d i + e = n + i`. -/
def bundleSum (r : ℕ) (n : ℤ) (d : Fin r → ℤ) (hd : ∀ i, d i + e = n + (i : ℕ)) :
    (∀ i, A (d i)) →+ P n where
  toFun a := ∑ i : Fin r, cap (i : ℕ) (n + (i : ℕ)) n rfl (pull (d i) (n + (i : ℕ)) (hd i) (a i))
  map_zero' := by simp
  map_add' a b := by simp [Finset.sum_add_distrib]

/-- The value of `bundleSum` on a family `a` is `∑_i c₁^i ∩ π^*a_i`. -/
@[simp]
theorem bundleSum_apply (r : ℕ) (n : ℤ) (d : Fin r → ℤ) (hd : ∀ i, d i + e = n + (i : ℕ))
    (a : ∀ i, A (d i)) :
    bundleSum e pull cap r n d hd a =
      ∑ i : Fin r, cap (i : ℕ) (n + (i : ℕ)) n rfl (pull (d i) (n + (i : ℕ)) (hd i) (a i)) :=
  rfl

/-- The summand `(-1)^i c₁^i ∩ π^*x` of index `i` of the relation, for `x ∈ A_{k - (r - i)}`. -/
def relationTerm (r : ℕ) (k : ℤ) (i : Fin (r + 1)) (x : A (k - ((Fin.rev i : ℕ) : ℤ))) :
    P (k - r + e) :=
  ((-1 : ℤ) ^ (i : ℕ)) • cap (i : ℕ) (k - r + e + (i : ℕ)) (k - r + e) rfl
    (pull (k - ((Fin.rev i : ℕ) : ℤ)) (k - r + e + (i : ℕ)) (relationTerm_degree e r k i) x)

/-- `relationTerm` is additive in `x`. -/
theorem relationTerm_add (r : ℕ) (k : ℤ) (i : Fin (r + 1)) (x y : A (k - ((Fin.rev i : ℕ) : ℤ))) :
    relationTerm e pull cap r k i (x + y) =
      relationTerm e pull cap r k i x + relationTerm e pull cap r k i y := by
  simp only [relationTerm, map_add, zsmul_add]

/-- `relationTerm` commutes with subtraction in `x`. -/
theorem relationTerm_sub (r : ℕ) (k : ℤ) (i : Fin (r + 1)) (x y : A (k - ((Fin.rev i : ℕ) : ℤ))) :
    relationTerm e pull cap r k i (x - y) =
      relationTerm e pull cap r k i x - relationTerm e pull cap r k i y := by
  simp only [relationTerm, map_sub, zsmul_sub]

/-- `relationTerm` sends `0` to `0`. -/
theorem relationTerm_zero (r : ℕ) (k : ℤ) (i : Fin (r + 1)) :
    relationTerm e pull cap r k i 0 = 0 := by
  simp [relationTerm]

/-- **The left-hand side of the relation of Stacks 0ERY** for a family `b_j ∈ A_{k - j}`,
`j = 0, …, r`: `∑_{i = 0}^{r} (-1)^i c₁^i ∩ π^*(b_{r - i}) ∈ P_{k - r + e}`. -/
def relationSumAt (r : ℕ) (k : ℤ) (b : ∀ j : Fin (r + 1), A (k - ((j : ℕ) : ℤ))) :
    P (k - r + e) :=
  ∑ i, relationTerm e pull cap r k i (b (Fin.rev i))

/-- **The left-hand side of the relation of Stacks 0ERY** for a family of maps
`c_j : A_k → A_{k - j}`, `j = 0, …, r`, at `α ∈ A_k`:
`∑_{i = 0}^{r} (-1)^i c₁^i ∩ π^*(c_{r - i} α)`. -/
def relationSum (r : ℕ) (c : ∀ (j : Fin (r + 1)) (k : ℤ), A k →+ A (k - ((j : ℕ) : ℤ)))
    (k : ℤ) (α : A k) : P (k - r + e) :=
  relationSumAt e pull cap r k fun j => c j k α

/-! ### Uniqueness -/

/-- Multiplication by the sign `(-1)^i` is injective. -/
theorem eq_zero_of_neg_one_pow_zsmul_eq_zero {M : Type*} [AddCommGroup M] (i : ℕ) {x : M}
    (h : ((-1 : ℤ) ^ i) • x = 0) : x = 0 := by
  rcases neg_one_pow_eq_or ℤ i with hi | hi
  · rwa [hi, one_zsmul] at h
  · rwa [hi, neg_one_zsmul, neg_eq_zero] at h

/-- Multiplying twice by the sign `(-1)^i` is the identity. -/
theorem neg_one_pow_zsmul_neg_one_pow_zsmul {M : Type*} [AddCommGroup M] (i : ℕ) (x : M) :
    ((-1 : ℤ) ^ i) • ((-1 : ℤ) ^ i) • x = x := by
  rcases neg_one_pow_eq_or ℤ i with hi | hi
  · rw [hi, one_zsmul, one_zsmul]
  · rw [hi, neg_one_zsmul, neg_one_zsmul, neg_neg]

/-- The summand of the relation at the last index `i = r`, where `b_{r - i} = b₀`. -/
theorem relationTerm_last_eq (r : ℕ) (k : ℤ) (b : ∀ j : Fin (r + 1), A (k - ((j : ℕ) : ℤ)))
    {x : A (k - ((0 : Fin (r + 1)) : ℕ))} (hx : b 0 = x) :
    relationTerm e pull cap r k (Fin.last r) (b (Fin.rev (Fin.last r))) =
      ((-1 : ℤ) ^ r) • cap r (k - r + e + r) (k - r + e) rfl
        (pull (k - ((0 : Fin (r + 1)) : ℕ)) (k - r + e + r) (by rw [Fin.val_zero]; omega) x) := by
  subst hx
  simp only [relationTerm, Fin.val_last]
  exact congrArg (fun y => ((-1 : ℤ) ^ r) • cap r (k - r + e + r) (k - r + e) rfl y)
    (pull_apply_congr e pull (fun j : Fin (r + 1) => k - ((j : ℕ) : ℤ)) b (Fin.rev_last r) _ _)

include e pull cap in
/-- **Uniqueness, pointwise (Stacks 0ERY).** If the map of the projective bundle formula is
injective in degree `k - r` (with arbitrary bookkeeping of the source degrees), two families
`b_j, b'_j ∈ A_{k - j}`, `j = 0, …, r`, with `b₀ = b'₀` which both satisfy the relation
`∑_{i} (-1)^i c₁^i ∩ π^*(b_{r - i}) = 0` are equal. -/
theorem eq_of_relationSumAt_eq_zero (r : ℕ) (k : ℤ)
    (hinj : ∀ (d : Fin r → ℤ) (hd : ∀ i, d i + e = k - r + e + (i : ℕ)) (a : ∀ i, A (d i)),
      bundleSum e pull cap r (k - r + e) d hd a = 0 → ∀ i, a i = 0)
    (b b' : ∀ j : Fin (r + 1), A (k - ((j : ℕ) : ℤ))) (h0 : b 0 = b' 0)
    (hb : relationSumAt e pull cap r k b = 0) (hb' : relationSumAt e pull cap r k b' = 0) :
    b = b' := by
  set δ : ∀ j : Fin (r + 1), A (k - ((j : ℕ) : ℤ)) := fun j => b j - b' j with hδ
  have hδ0 : δ 0 = 0 := by
    show b 0 - b' 0 = 0
    rw [h0, sub_self]
  have hrel : relationSumAt e pull cap r k δ = 0 := by
    simp only [relationSumAt, hδ, relationTerm_sub, Finset.sum_sub_distrib] at hb hb' ⊢
    rw [hb, hb', sub_zero]
  rw [relationSumAt, Fin.sum_univ_castSucc, relationTerm_last_eq e pull cap r k δ hδ0,
    map_zero, map_zero, smul_zero, add_zero] at hrel
  have ha := hinj _ (fun i => relationTerm_degree e r k (Fin.castSucc i))
      (fun i => ((-1 : ℤ) ^ (i : ℕ)) • δ (Fin.rev (Fin.castSucc i))) (by
    rw [bundleSum_apply, ← hrel]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [relationTerm, map_zsmul]
    rfl)
  have hall : ∀ j, δ j = 0 := by
    have transport : ∀ j j' : Fin (r + 1), j = j' → δ j = 0 → δ j' = 0 := by
      rintro j j' rfl h
      exact h
    intro j
    by_cases hj : j = 0
    · exact transport 0 j hj.symm hδ0
    · have hrev : Fin.rev j ≠ Fin.last r := by
        rwa [Ne, Fin.rev_eq_iff, Fin.rev_last]
      refine transport (Fin.rev (Fin.castSucc ((Fin.rev j).castPred hrev))) j
        (by rw [Fin.castSucc_castPred, Fin.rev_rev]) ?_
      exact eq_zero_of_neg_one_pow_zsmul_eq_zero _ (ha ((Fin.rev j).castPred hrev))
  funext j
  exact sub_eq_zero.1 (hall j)

include e pull cap in
/-- **Uniqueness (Stacks 0ERY).** If the map of the projective bundle formula is injective in
every degree, there is at most one family of maps `c_j : A_k → A_{k - j}`, `j = 0, …, r`, with
`c₀ = id` satisfying the relation. -/
theorem eq_of_relationSum_eq_zero (r : ℕ)
    (hinj : ∀ (n : ℤ) (d : Fin r → ℤ) (hd : ∀ i, d i + e = n + (i : ℕ)) (a : ∀ i, A (d i)),
      bundleSum e pull cap r n d hd a = 0 → ∀ i, a i = 0)
    (c c' : ∀ (j : Fin (r + 1)) (k : ℤ), A k →+ A (k - ((j : ℕ) : ℤ)))
    (h0 : ∀ k α, c 0 k α = c' 0 k α)
    (hc : ∀ k α, relationSum e pull cap r c k α = 0)
    (hc' : ∀ k α, relationSum e pull cap r c' k α = 0) :
    c = c' := by
  funext j k
  refine AddMonoidHom.ext fun α => ?_
  have := eq_of_relationSumAt_eq_zero e pull cap r k (hinj (k - r + e)) (fun j => c j k α)
    (fun j => c' j k α) (h0 k α) (hc k α) (hc' k α)
  exact congrFun this j

/-! ### Existence -/

/-- The degree bookkeeping of the existence proof: the component of index `i < r` of the
decomposition lives in degree `k - (r - i)`, which is the degree of `c_{r - i}`. -/
theorem existence_degree (r : ℕ) (k : ℤ) (j : Fin (r + 1)) (hj : Fin.rev j ≠ Fin.last r) :
    k - ((Fin.rev (Fin.castSucc ((Fin.rev j).castPred hj)) : ℕ) : ℤ) = k - ((j : ℕ) : ℤ) := by
  rw [Fin.castSucc_castPred, Fin.rev_rev]

include e pull cap in
/-- **Existence (Stacks 0ERY).** If the map of the projective bundle formula is bijective in
every degree, there are additive maps `c_j : A_k → A_{k - j}`, `j = 0, …, r`, with `c₀ = id`
satisfying the relation `∑_{i = 0}^{r} (-1)^i c₁^i ∩ π^*(c_{r - i} α) = 0` for every `α`. -/
theorem exists_relationSum_eq_zero (r : ℕ)
    (hbij : ∀ (n : ℤ) (d : Fin r → ℤ) (hd : ∀ i, d i + e = n + (i : ℕ)),
      Function.Bijective (bundleSum e pull cap r n d hd)) :
    ∃ c : ∀ (j : Fin (r + 1)) (k : ℤ), A k →+ A (k - ((j : ℕ) : ℤ)),
      (∀ k α, c 0 k α = degreeCast A (by simp) α) ∧
        ∀ k α, relationSum e pull cap r c k α = 0 := by
  classical
  -- the source degrees of the decomposition in degree `k - r + e`
  let d : ℤ → Fin r → ℤ := fun k i => k - ((Fin.rev (Fin.castSucc i) : ℕ) : ℤ)
  have hd : ∀ k i, d k i + e = k - r + e + (i : ℕ) := fun k i =>
    relationTerm_degree e r k (Fin.castSucc i)
  let Φ : ∀ k : ℤ, (∀ i, A (d k i)) ≃+ P (k - r + e) := fun k =>
    AddEquiv.ofBijective (bundleSum e pull cap r (k - r + e) (d k) (hd k))
      (hbij (k - r + e) (d k) (hd k))
  -- the element `-(-1)^r c₁^r ∩ π^*α` to decompose
  let y : ∀ k : ℤ, A k →+ P (k - r + e) := fun k =>
    -(((-1 : ℤ) ^ r) • (cap r (k - r + e + r) (k - r + e) rfl).comp
      (pull k (k - r + e + r) (by omega)))
  let ψ : ∀ k : ℤ, A k →+ ∀ i, A (d k i) := fun k => (Φ k).symm.toAddMonoidHom.comp (y k)
  have hψ : ∀ k α, bundleSum e pull cap r (k - r + e) (d k) (hd k) (ψ k α) = y k α := fun k α =>
    (Φ k).apply_symm_apply (y k α)
  let c : ∀ (j : Fin (r + 1)) (k : ℤ), A k →+ A (k - ((j : ℕ) : ℤ)) := fun j k =>
    if hj : Fin.rev j = Fin.last r then
      degreeCast A (by
        have : j = 0 := by rwa [Fin.rev_eq_iff, Fin.rev_last] at hj
        subst this
        simp)
    else
      ((-1 : ℤ) ^ (((Fin.rev j).castPred hj : Fin r) : ℕ)) •
        (degreeCast A (existence_degree r k j hj)).comp
          ((Pi.evalAddMonoidHom (fun i => A (d k i)) ((Fin.rev j).castPred hj)).comp (ψ k))
  have hlast : ∀ k α, c 0 k α = degreeCast A (by simp) α := fun k α => by
    have hj : Fin.rev (0 : Fin (r + 1)) = Fin.last r := Fin.rev_zero r
    simp only [c, dif_pos hj]
  refine ⟨c, hlast, fun k α => ?_⟩
  · -- the summands of index `i < r` reassemble `ψ k α`; the last one is `-y k α`
    rw [relationSum, relationSumAt, Fin.sum_univ_castSucc,
      relationTerm_last_eq e pull cap r k (fun j => c j k α) (hlast k α), pull_degreeCast]
    have hfirst : ∀ i : Fin r,
        relationTerm e pull cap r k (Fin.castSucc i) (c (Fin.rev (Fin.castSucc i)) k α) =
          cap (i : ℕ) (k - r + e + (i : ℕ)) (k - r + e) rfl
            (pull (d k i) (k - r + e + (i : ℕ)) (hd k i) (ψ k α i)) := by
      intro i
      have hrev : Fin.rev (Fin.rev (Fin.castSucc i)) ≠ Fin.last r := by
        rw [Fin.rev_rev]
        exact Fin.castSucc_ne_last i
      have hidx : (Fin.rev (Fin.rev (Fin.castSucc i))).castPred hrev = i := by
        simp
      -- unfold `c` at the index `r - i ≠ 0`
      have hc : c (Fin.rev (Fin.castSucc i)) k α =
          ((-1 : ℤ) ^ (((Fin.rev (Fin.rev (Fin.castSucc i))).castPred hrev : Fin r) : ℕ)) •
            degreeCast A (existence_degree r k _ hrev)
              (ψ k α ((Fin.rev (Fin.rev (Fin.castSucc i))).castPred hrev)) := by
        simp only [c, dif_neg hrev]
        rfl
      rw [relationTerm, hc, map_zsmul, pull_degreeCast, map_zsmul]
      have hpow : (((Fin.rev (Fin.rev (Fin.castSucc i))).castPred hrev : Fin r) : ℕ) =
          ((Fin.castSucc i : Fin (r + 1)) : ℕ) := by
        rw [hidx]
        rfl
      rw [hpow, neg_one_pow_zsmul_neg_one_pow_zsmul]
      exact congrArg (cap (i : ℕ) (k - r + e + (i : ℕ)) (k - r + e) rfl)
        (pull_apply_congr e pull (d k) (ψ k α) hidx _ _)
    rw [Finset.sum_congr rfl fun i _ => hfirst i, ← bundleSum_apply e pull cap r (k - r + e)
      (d k) (hd k), hψ]
    have hy : y k α = -(((-1 : ℤ) ^ r) • cap r (k - r + e + r) (k - r + e) rfl
        (pull k (k - r + e + r) (by omega) α)) := rfl
    rw [hy]
    exact neg_add_cancel _

end AlgebraicGeometry.Space.ProjectiveBundleRelation

end
