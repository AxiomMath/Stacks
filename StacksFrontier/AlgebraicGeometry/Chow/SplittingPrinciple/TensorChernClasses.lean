module

public import Mathlib.Algebra.Ring.Subring.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.ChernWhitney.FilteredAdditivity
public import StacksFrontier.AlgebraicGeometry.Chow.FirstChernClassTensor
public import StacksCore.Tactic.StacksAttribute

/-!
# Chern classes of a tensor product of finite locally free modules

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S` and let `ℰ` and `ℱ` be finite locally free `𝒪_X`-modules of ranks `r` and
`s`. [Stacks, Tag 0FA6](https://stacks.math.columbia.edu/tag/0FA6) is the pair of identities

  `c₁(ℰ ⊗ ℱ) = r·c₁(ℱ) + s·c₁(ℰ)`,

  `c₂(ℰ ⊗ ℱ) = r·c₂(ℱ) + s·c₂(ℰ) + C(r,2)·c₁(ℱ)² + (r·s − 1)·c₁(ℱ)·c₁(ℰ) + C(s,2)·c₁(ℰ)²`,

in `A^*(X)`, together with the remark "and so on". Both identities are proved here,
**componentwise, as identities between cap products on Chow groups**, in the vocabulary of
`StacksFrontier.AlgebraicGeometry.Chow.ChernWhitney.FilteredAdditivity`; the cross-term coefficient
is `r·s − 1`, not `r·s`, and that is what is proved. The trailing "and so on" is not a precise
assertion and nothing is claimed for it.

As in `StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.DualChernClasses`, this development
has no bivariant ring `A^*(X)` and no total Chern class — see the module documentation of
`StacksFrontier.AlgebraicGeometry.Chow.ChernWhitney.CapProductRelation` — so every identity of this
section of chapter 42 is read degree by degree against a fixed cycle `α`.

## The proof, and where it starts

The source argues as in [Stacks, Tag 0FA5](https://stacks.math.columbia.edu/tag/0FA5): choose
`π : P ⟶ X` as in [Stacks, Tag 02UL](https://stacks.math.columbia.edu/tag/02UL), use injectivity
of `π^*` to reduce to the case where `ℰ` and `ℱ` carry filtrations with invertible successive
quotients `ℒ_i` (`i = 1, …, r`) and `𝒩_j` (`j = 1, …, s`), order the pairs `(i, j)`
lexicographically to obtain a filtration of `ℰ ⊗ ℱ` with successive quotients
`ℒ_i ⊗ 𝒩_j`, read [Stacks, Tag 02UJ](https://stacks.math.columbia.edu/tag/02UJ) on the three
filtrations to get `c(ℰ) = ∏ (1 + x_i)`, `c(ℱ) = ∏ (1 + y_j)` and
`c(ℰ ⊗ ℱ) = ∏ (1 + x_i + y_j)`, and finish by "a formal computation which we omit".

**Everything after the reduction is proved below, in full.** The reduction itself is carried as
a hypothesis, for the two reasons recorded in the `@[stacks 0FA5]` clause of
`StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.DualChernClasses` and repeated in the
clauses below: the filtration Stacks 02UL delivers is an inductive `Prop`
(`Stacks.WeilCohomology.HasInvertibleFiltration`) from which the tower of modules and maps that
Stacks 02UJ consumes cannot be eliminated, and nothing in this repository states that the Chern
class cap product commutes with flat pullback, so injectivity of `π^*` has nothing to be applied
to. So the hypotheses below are exactly the three filtrations the source reduces to, presented as
the towers of short exact sequences that Stacks 02UJ consumes, together with the lexicographic
identification `hquot` of the quotients of the third with the tensor products of the quotients of
the first two.

## The formal computation the source omits

Writing `x_i` for the operation `c₁(ℒ_i) ∩ -` and `y_j` for `c₁(𝒩_j) ∩ -`, Stacks 02SP gives
`c₁(ℒ_i ⊗ 𝒩_j) ∩ - = x_i + y_j` (`Stacks.Chow.firstChernCapStep_eq_add_of_iso_tensorObj`), and
Stacks 02UJ turns the three total Chern classes into the elementary symmetric functions of the
families `(x_i)`, `(y_j)` and `(x_i + y_j)`. What remains is

  `e₁(x_i + y_j) = s·e₁(x) + r·e₁(y)`,

  `e₂(x_i + y_j) = s·e₂(x) + r·e₂(y) + C(r,2)·e₁(y)² + (r·s − 1)·e₁(x)·e₁(y) + C(s,2)·e₁(x)²`,

an identity between polynomials in `r + s` commuting variables. It is proved here by induction on
the number of blocks of the lexicographic order: `Stacks.Chow.block_increment` computes the
contribution of one block, and `Stacks.Chow.esymRec_two_block` iterates it. The `(r·s − 1)` of the
source appears exactly here: the coefficient of `x_i·e₁(y)` produced by the `i`-th block is
`s·(i+1) − 1`, which is not independent of `i`, and only after adding the contribution
`s·(r−1−i)` coming from the partial sums below block `i` does it become the constant `r·s − 1`.

## The operator ring

Chern class cap products of Stacks 02U5 go from cycles to Chow classes and so cannot be iterated,
and the descended operations of Stacks 02TI go from one Chow group to another; the source's
products `c₁(ℱ)²` and `c₁(ℱ)·c₁(ℰ)` are therefore composites of operations, not products of
classes. To do the formal computation once rather than degree by degree, the operations are
assembled into endomorphisms of the graded product `Stacks.Chow.ChowGradedProduct`, the product of
all the Chow groups `A_{n-i}(X)`: `Stacks.Chow.firstChernShift` sends the component in degree `i`
to its cap product in degree `i + 1`, so that the ring `AddMonoid.End` of the graded product
contains the composites as products, and the computation above is an identity in the commutative
subring generated by the shifts of the `ℒ_i` and `𝒩_j`. Commutativity of that subring is Stacks
02TJ, carried as the hypotheses `hcommLL`, `hcommNN`, `hcommLN`; it is needed only in degree two,
and the degree-one identity is proved without it, for an arbitrary ring.

## Main definitions

* `Stacks.Chow.ChowGradedProduct`, `Stacks.Chow.firstChernShift`,
  `Stacks.Chow.firstChernShiftSeq` — the graded product of the Chow groups of `X`, the
  degree-raising endomorphism given by the first Chern class cap product of an invertible module,
  and the sequence of such endomorphisms attached to a finite family.
* `Stacks.Chow.firstChernCapSum` — `c₁ ∩ -` of a bundle presented by a filtration with invertible
  quotients, as the sum of the first Chern class cap operations of the quotients.
* `Stacks.Chow.FirstChernCapStepsCommute` — Stacks 02TJ for two invertible modules, as an identity
  between the operations on Chow groups.
* `Stacks.Chow.esymRec` — the Pascal recursion for the elementary symmetric functions of a
  sequence in a ring.

## Main results

* `Stacks.Chow.firstChernCapStep_eq_add_of_iso_tensorObj` — Stacks 02SP for the descended
  operations: `c₁(ℒ ⊗ 𝒩) ∩ - = c₁(ℒ) ∩ - + c₁(𝒩) ∩ -`.
* `Stacks.Chow.sum_range_lexFamily` — the formal computation the source omits, in degree one;
  it needs no commutativity.
* `Stacks.Chow.esymRec_two_tensor`, `Stacks.Chow.esymRec_two_tensor_of_closure` — the formal
  computation the source omits, in degree two.
* `Stacks.Chow.firstChernCapSum_eq_chernClassCapExt_one` — the identification of
  `Stacks.Chow.firstChernCapSum` with `c₁ ∩ -`, by Stacks 02UJ.
* `Stacks.Chow.chernClassCapExt_tensorObj_one` — **Stacks 0FA6**, the first displayed identity.
* `Stacks.Chow.chernClassCapExt_tensorObj_two` — **Stacks 0FA6**, the second displayed identity.

## References

* [Stacks Project, Tag 0FA6](https://stacks.math.columbia.edu/tag/0FA6)
* [Stacks Project, Tag 0FA5](https://stacks.math.columbia.edu/tag/0FA5)
* [Stacks Project, Tag 02UJ](https://stacks.math.columbia.edu/tag/02UJ)
* [Stacks Project, Tag 02UL](https://stacks.math.columbia.edu/tag/02UL)
* [Stacks Project, Tag 02U5](https://stacks.math.columbia.edu/tag/02U5)
* [Stacks Project, Tag 02U0](https://stacks.math.columbia.edu/tag/02U0)
* [Stacks Project, Tag 02TJ](https://stacks.math.columbia.edu/tag/02TJ)
* [Stacks Project, Tag 02TI](https://stacks.math.columbia.edu/tag/02TI)
* [Stacks Project, Tag 02SP](https://stacks.math.columbia.edu/tag/02SP)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Finset

universe u

namespace Stacks.Chow

/-! ### Elementary symmetric functions of a sequence in a ring -/

section Algebra

variable {R : Type*} [Ring R]

/-- The `k`-th elementary symmetric function of `w 0, …, w (m-1)`, by the Pascal recursion
`e_{k+1}(w_0, …, w_m) = e_{k+1}(w_0, …, w_{m-1}) + w_m · e_k(w_0, …, w_{m-1})`, with `e_0 = 1`
and `e_{k+1}` of the empty family zero. The factors of a monomial are multiplied in decreasing
order of index. -/
def esymRec (w : ℕ → R) : ℕ → ℕ → R
  | _, 0 => 1
  | 0, _ + 1 => 0
  | m + 1, k + 1 => esymRec w m (k + 1) + w m * esymRec w m k

/-- In degree zero the elementary symmetric function is `1`. -/
theorem esymRec_degree_zero (w : ℕ → R) (m : ℕ) : esymRec w m 0 = 1 := by cases m <;> rfl

/-- The empty family has no elementary symmetric function in positive degree. -/
theorem esymRec_zero_succ (w : ℕ → R) (k : ℕ) : esymRec w 0 (k + 1) = 0 := rfl

/-- The Pascal recursion. -/
theorem esymRec_succ (w : ℕ → R) (m k : ℕ) :
    esymRec w (m + 1) (k + 1) = esymRec w m (k + 1) + w m * esymRec w m k := rfl

/-- In degree one the elementary symmetric function is the sum. -/
theorem esymRec_one (w : ℕ → R) (m : ℕ) : esymRec w m 1 = ∑ k ∈ range m, w k := by
  induction m with
  | zero => simp [esymRec_zero_succ]
  | succ m ih => rw [esymRec_succ, ih, esymRec_degree_zero, mul_one, Finset.sum_range_succ]

/-- In degree two the elementary symmetric function is the triangular sum. -/
theorem esymRec_two (w : ℕ → R) (m : ℕ) :
    esymRec w m 2 = ∑ k ∈ range m, w k * ∑ l ∈ range k, w l := by
  induction m with
  | zero => simp [esymRec_zero_succ]
  | succ m ih => rw [esymRec_succ, ih, esymRec_one, Finset.sum_range_succ]

end Algebra

/-! ### The degree-one half of the formal computation

The sum of the lexicographic family needs no commutativity, so it is proved here for an arbitrary
ring: the first displayed identity of Stacks 0FA6 does not need Stacks 02TJ. -/

section LexSum

variable {R : Type*} [Ring R]

/-- The partial sums of the lexicographic family inside the block of index `m`. -/
theorem sum_range_lexFamily_partial (x y w : ℕ → R) (s m : ℕ)
    (hm : ∀ j, j < s → w (m * s + j) = x m + y j) :
    ∀ j, j ≤ s → (∑ k ∈ range (m * s + j), w k)
      = (∑ k ∈ range (m * s), w k) + (j : R) * x m + ∑ l ∈ range j, y l := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
      intro hj
      rw [← Nat.add_assoc, Finset.sum_range_succ (n := m * s + j), ih (by omega),
        hm j (by omega), Finset.sum_range_succ (f := y)]
      push_cast
      noncomm_ring

/-- **The degree-one half of the formal computation the proof of Stacks 0FA6 omits.** The sum of
the lexicographic family `w_{i·s+j} = x_i + y_j` over all `r·s` of its members is `s` times the
sum of the `x_i` plus `r` times the sum of the `y_j`. No commutativity is used. -/
theorem sum_range_lexFamily (x y w : ℕ → R) (r s : ℕ)
    (hw : ∀ i, i < r → ∀ j, j < s → w (i * s + j) = x i + y j) :
    ∀ m, m ≤ r → (∑ k ∈ range (m * s), w k)
      = (s : R) * (∑ i ∈ range m, x i) + (m : R) * ∑ j ∈ range s, y j := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
      intro hm
      have hm' : m < r := by omega
      rw [Nat.succ_mul, sum_range_lexFamily_partial x y w s m (hw m hm') s le_rfl, ih (by omega),
        Finset.sum_range_succ (f := x)]
      push_cast
      noncomm_ring

/-- The degree-one identity with integer scalar multiplications, the shape the cap products are
stated with. -/
theorem sum_range_lexFamily_zsmul (x y w : ℕ → R) (r s : ℕ)
    (hw : ∀ i, i < r → ∀ j, j < s → w (i * s + j) = x i + y j) :
    (∑ k ∈ range (r * s), w k)
      = (s : ℤ) • (∑ i ∈ range r, x i) + (r : ℤ) • ∑ j ∈ range s, y j := by
  rw [sum_range_lexFamily x y w r s hw r le_rfl]
  simp only [zsmul_eq_mul]
  push_cast
  rfl

end LexSum

/-! ### The formal computation the source omits

The two displayed identities of Stacks 0FA6 reduce to a pair of identities between elementary
symmetric functions of `r + s` commuting variables, which are proved here. -/

section CommAlgebra

variable {R : Type*} [CommRing R]

/-- The Pascal step for `C(t,2)`. -/
private theorem choose_two_succ_cast (t : ℕ) :
    ((t + 1).choose 2 : R) = t.choose 2 + t := by
  simp [Nat.choose_succ_succ, add_comm]

/-- The sum of the first `t` natural numbers is the binomial coefficient `C(t,2)`. -/
private theorem sum_range_natCast_eq_choose_two (t : ℕ) :
    ∑ j ∈ range t, (j : R) = (t.choose 2 : R) := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [Finset.sum_range_succ, ih, choose_two_succ_cast]

/-- The partial sums of a sequence, plus the sequence weighted by its index, add up to `t - 1`
times the whole sum. This is the cancellation that makes the cross-term coefficient of Stacks
0FA6 independent of the block. -/
private theorem sum_partial_add_weighted (y : ℕ → R) (t : ℕ) :
    (∑ j ∈ range t, ∑ l ∈ range j, y l) + ∑ j ∈ range t, (j : R) * y j
      = ((t : R) - 1) * ∑ j ∈ range t, y j := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [Finset.sum_range_succ (f := fun j => ∑ l ∈ range j, y l),
        Finset.sum_range_succ (f := fun j => (j : R) * y j),
        Finset.sum_range_succ (f := y)]
      push_cast
      linear_combination ih

/-- The square of a sum, in terms of the sum of squares and the degree-two elementary symmetric
function. -/
private theorem sq_sum_range_eq_add (x : ℕ → R) (t : ℕ) :
    (∑ i ∈ range t, x i) ^ 2
      = (∑ i ∈ range t, x i * x i) + 2 * ∑ i ∈ range t, x i * ∑ i' ∈ range i, x i' := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [Finset.sum_range_succ (f := x), Finset.sum_range_succ (f := fun i => x i * x i),
        Finset.sum_range_succ (f := fun i => x i * ∑ i' ∈ range i, x i')]
      linear_combination ih

/-- The contribution of one block of the lexicographic order to the degree-two elementary
symmetric function. The coefficient `(s : R) - 1` of the cross term is where the cancellation of
`Stacks.Chow.sum_partial_add_weighted` happens. -/
theorem esymRec_block_increment (x y w : ℕ → R) (s m : ℕ) (b : R)
    (hb : (∑ k ∈ range (m * s), w k) = b)
    (hm : ∀ j, j < s → w (m * s + j) = x m + y j) :
    (∑ j ∈ range s, w (m * s + j) * ∑ l ∈ range (m * s + j), w l)
      = (s : R) * (x m * b) + (∑ j ∈ range s, y j) * b
        + (s.choose 2 : R) * (x m * x m)
        + ((s : R) - 1) * (x m * ∑ j ∈ range s, y j)
        + ∑ j ∈ range s, y j * ∑ l ∈ range j, y l := by
  have hterm : ∀ j ∈ range s, w (m * s + j) * ∑ l ∈ range (m * s + j), w l
      = (x m * b + (j : R) * (x m * x m) + x m * ∑ l ∈ range j, y l)
        + (y j * b + ((j : R) * y j) * x m + y j * ∑ l ∈ range j, y l) := by
    intro j hj
    rw [sum_range_lexFamily_partial x y w s m hm j (le_of_lt (Finset.mem_range.mp hj)), hb,
      hm j (Finset.mem_range.mp hj)]
    ring
  have e1 : ∑ _j ∈ range s, x m * b = (s : R) * (x m * b) := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have e2 : ∑ j ∈ range s, (j : R) * (x m * x m) = (s.choose 2 : R) * (x m * x m) := by
    rw [← Finset.sum_mul, sum_range_natCast_eq_choose_two]
  have e3 : ∑ j ∈ range s, x m * ∑ l ∈ range j, y l
      = x m * ∑ j ∈ range s, ∑ l ∈ range j, y l := by rw [Finset.mul_sum]
  have e4 : ∑ j ∈ range s, y j * b = (∑ j ∈ range s, y j) * b := by rw [Finset.sum_mul]
  have e5 : ∑ j ∈ range s, ((j : R) * y j) * x m
      = (∑ j ∈ range s, (j : R) * y j) * x m := by rw [Finset.sum_mul]
  rw [Finset.sum_congr rfl hterm]
  simp only [Finset.sum_add_distrib]
  rw [e1, e2, e3, e4, e5]
  linear_combination x m * sum_partial_add_weighted y s

/-- The degree-two elementary symmetric function of the lexicographic family over its first `m`
blocks. -/
theorem esymRec_two_block (x y w : ℕ → R) (r s : ℕ)
    (hw : ∀ i, i < r → ∀ j, j < s → w (i * s + j) = x i + y j) :
    ∀ m, m ≤ r → (∑ k ∈ range (m * s), w k * ∑ l ∈ range k, w l)
      = (s : R) ^ 2 * (∑ i ∈ range m, x i * ∑ i' ∈ range i, x i')
        + (s.choose 2 : R) * (∑ i ∈ range m, x i * x i)
        + (m : R) * (∑ j ∈ range s, y j * ∑ j' ∈ range j, y j')
        + (m.choose 2 : R) * ((∑ j ∈ range s, y j) * ∑ j ∈ range s, y j)
        + ((m : R) * s - 1) * ((∑ i ∈ range m, x i) * ∑ j ∈ range s, y j) := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
      intro hm
      have hm' : m < r := by omega
      have hsplit : (∑ k ∈ range ((m + 1) * s), w k * ∑ l ∈ range k, w l)
          = (∑ k ∈ range (m * s), w k * ∑ l ∈ range k, w l)
            + ∑ j ∈ range s, w (m * s + j) * ∑ l ∈ range (m * s + j), w l := by
        rw [Nat.succ_mul, Finset.sum_range_add]
      rw [hsplit, ih (by omega),
        esymRec_block_increment x y w s m
          ((s : R) * (∑ i ∈ range m, x i) + (m : R) * ∑ j ∈ range s, y j)
          (sum_range_lexFamily x y w r s hw m (by omega)) (hw m hm'),
        Finset.sum_range_succ (f := fun i => x i * ∑ i' ∈ range i, x i'),
        Finset.sum_range_succ (f := fun i => x i * x i),
        Finset.sum_range_succ (f := x), choose_two_succ_cast]
      push_cast
      ring

/-- **The formal computation the proof of Stacks 0FA6 omits, in degree two.** For commuting
variables `x_0, …, x_{r-1}` and `y_0, …, y_{s-1}` and the lexicographic family
`w_{i·s+j} = x_i + y_j`,

  `e₂(w) = s·e₂(x) + r·e₂(y) + C(r,2)·e₁(y)² + (r·s − 1)·e₁(x)·e₁(y) + C(s,2)·e₁(x)²`.

The cross-term coefficient is `r·s − 1`. -/
theorem esymRec_two_tensor (x y w : ℕ → R) (r s : ℕ)
    (hw : ∀ i, i < r → ∀ j, j < s → w (i * s + j) = x i + y j) :
    (∑ k ∈ range (r * s), w k * ∑ l ∈ range k, w l)
      = (s : R) * (∑ i ∈ range r, x i * ∑ i' ∈ range i, x i')
        + (r : R) * (∑ j ∈ range s, y j * ∑ j' ∈ range j, y j')
        + (r.choose 2 : R) * (∑ j ∈ range s, y j) ^ 2
        + ((r : R) * s - 1) * ((∑ i ∈ range r, x i) * ∑ j ∈ range s, y j)
        + (s.choose 2 : R) * (∑ i ∈ range r, x i) ^ 2 := by
  rw [esymRec_two_block x y w r s hw r le_rfl]
  have hsq := sq_sum_range_eq_add x r
  have hchoose : ∀ t : ℕ, (t.choose 2 : R) * 2 = (t : R) ^ 2 - t := by
    intro t
    induction t with
    | zero => simp
    | succ t iht =>
        rw [choose_two_succ_cast]
        push_cast
        linear_combination iht
  linear_combination (-(s.choose 2 : R)) * hsq
    - (∑ i ∈ range r, x i * ∑ i' ∈ range i, x i') * hchoose s

end CommAlgebra

/-! ### The two identities in a commutative subring of a ring

The operators the identities are applied to live in a possibly noncommutative ring of
endomorphisms; what is commutative is the subring generated by the operators themselves. -/

section Closure

variable {R : Type*} [Ring R]

open scoped IsMulCommutative in
/-- The degree-two identity of `Stacks.Chow.esymRec_two_tensor` for a lexicographic family lying
in a commutative subring of a possibly noncommutative ring. -/
theorem esymRec_two_tensor_of_closure (x y w : ℕ → R) (G : Set R)
    (hG : ∀ a ∈ G, ∀ b ∈ G, a * b = b * a)
    (hx : ∀ i, x i ∈ Subring.closure G) (hy : ∀ j, y j ∈ Subring.closure G)
    (hwS : ∀ k, w k ∈ Subring.closure G)
    (r s : ℕ) (hw : ∀ i, i < r → ∀ j, j < s → w (i * s + j) = x i + y j) :
    (∑ k ∈ range (r * s), w k * ∑ l ∈ range k, w l)
      = (s : ℤ) • (∑ i ∈ range r, x i * ∑ i' ∈ range i, x i')
        + (r : ℤ) • (∑ j ∈ range s, y j * ∑ j' ∈ range j, y j')
        + (r.choose 2 : ℤ) • (∑ j ∈ range s, y j) ^ 2
        + ((r : ℤ) * s - 1) • ((∑ i ∈ range r, x i) * ∑ j ∈ range s, y j)
        + (s.choose 2 : ℤ) • (∑ i ∈ range r, x i) ^ 2 := by
  have : IsMulCommutative (Subring.closure G) :=
    Subring.isMulCommutative_closure fun a ha b hb _ => hG a ha b hb
  have hw' : ∀ i, i < r → ∀ j, j < s →
      (fun k => (⟨w k, hwS k⟩ : Subring.closure G)) (i * s + j)
        = (fun i => (⟨x i, hx i⟩ : Subring.closure G)) i
          + (fun j => (⟨y j, hy j⟩ : Subring.closure G)) j :=
    fun i hi j hj => Subtype.ext (hw i hi j hj)
  have key := esymRec_two_tensor (fun i => (⟨x i, hx i⟩ : Subring.closure G))
    (fun j => (⟨y j, hy j⟩ : Subring.closure G))
    (fun k => (⟨w k, hwS k⟩ : Subring.closure G)) r s hw'
  have h2 := congrArg ((Subring.closure G).subtype : Subring.closure G →+* R) key
  simp only [map_add, map_mul, map_sum, map_pow, map_sub, map_natCast, map_one,
    Subring.coe_subtype] at h2
  rw [h2]
  simp only [zsmul_eq_mul]
  push_cast
  rfl

end Closure

/-! ### Transport of sums and of a module identification -/

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]

/-- The transport of `Stacks.Chow.chowGroupDegreeCast` along an equality of degrees is
additive. -/
theorem chowGroupDegreeCast_add {k l m : ℤ} (h : k = l)
    (F G : chowGroup C p l →+ chowGroup C p m) :
    chowGroupDegreeCast C p h (F + G) =
      chowGroupDegreeCast C p h F + chowGroupDegreeCast C p h G := by
  subst h; rfl

/-- The Chern class cap product of Stacks 02U5 depends on the module only through the module: two
equal modules of the same rank give the same operation, whichever proof of rank preservation is
supplied. -/
theorem chernClassCapExt_congr_module (n : ℤ) {A B : X.Modules} (hAB : A = B) (q : ℕ)
    (hA : PullbackPreservesRank A q) (hB : PullbackPreservesRank B q)
    (chern : ChernClassCycleRule C q) (i : ℕ) :
    chernClassCapExt C p n A q hA chern i = chernClassCapExt C p n B q hB chern i := by
  subst hAB; rfl

/-- The value of a finite sum of endomorphisms of an additive commutative monoid. -/
theorem addMonoidEnd_sum_apply {M : Type*} [AddCommMonoid M] {ι : Type*} (t : Finset ι)
    (f : ι → AddMonoid.End M) (z : M) : (∑ i ∈ t, f i) z = ∑ i ∈ t, f i z := by
  classical
  induction t using Finset.induction with
  | empty => simp
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]; rfl

/-! ### Stacks 02SP for the descended first Chern class cap products -/

section Tensor

variable (k : ℤ) (A B D : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property A]
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property B]
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property D]

/-- The descended first Chern class cap product of Stacks 02TI depends on the invertible module
only through its isomorphism class. -/
theorem firstChernClassCapOnChow_congr (e : A ≅ B)
    (hA : FirstChernClassCapFactorsThroughRationalEquivalence C p k
      (firstChernComponentCycleRule C p k A))
    (hB : FirstChernClassCapFactorsThroughRationalEquivalence C p k
      (firstChernComponentCycleRule C p k B)) :
    firstChernClassCapOnChow C p k (firstChernComponentCycleRule C p k A) hA =
      firstChernClassCapOnChow C p k (firstChernComponentCycleRule C p k B) hB := by
  refine QuotientAddGroup.addMonoidHom_ext _ (AddMonoidHom.ext fun α ↦ ?_)
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, firstChernClassCapOnChow_mk]
  exact firstChernClassCapOfInvertible_congr C p k A B e α

/-- **Stacks 02SP for the descended operations of Stacks 02TI.** If `D ≅ A ⊗_{𝒪_X} B` with `A`
and `B` invertible then `c₁(D) ∩ - = c₁(A) ∩ - + c₁(B) ∩ -` as operations `A_{k+1}(X) ⟶ A_k(X)`.

No hypothesis is needed for `A ⊗ B` itself: additivity
(`Stacks.Chow.firstChernClassCapOfInvertible_tensorObj`) and isomorphism invariance
(`Stacks.Chow.firstChernClassCapOfInvertible_congr`) are both available at the level of cycles,
where Stacks 02TI does not enter. -/
theorem firstChernClassCapOnChow_eq_add_of_iso_tensorObj (e : D ≅ Scheme.Modules.tensorObj A B)
    (hA : FirstChernClassCapFactorsThroughRationalEquivalence C p k
      (firstChernComponentCycleRule C p k A))
    (hB : FirstChernClassCapFactorsThroughRationalEquivalence C p k
      (firstChernComponentCycleRule C p k B))
    (hD : FirstChernClassCapFactorsThroughRationalEquivalence C p k
      (firstChernComponentCycleRule C p k D)) :
    firstChernClassCapOnChow C p k (firstChernComponentCycleRule C p k D) hD =
      firstChernClassCapOnChow C p k (firstChernComponentCycleRule C p k A) hA +
        firstChernClassCapOnChow C p k (firstChernComponentCycleRule C p k B) hB := by
  refine QuotientAddGroup.addMonoidHom_ext _ (AddMonoidHom.ext fun α ↦ ?_)
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.add_apply,
    firstChernClassCapOnChow_mk]
  rw [firstChernClassCapOfInvertible_congr C p k D (Scheme.Modules.tensorObj A B) e α]
  exact (firstChernClassCapOfInvertible_tensorObj C p k A B α).symm

variable (n : ℤ)

/-- `Stacks.Chow.firstChernCapStep` depends on the invertible module only through its isomorphism
class. -/
theorem firstChernCapStep_congr (e : A ≅ B) (hA : InvertibleChernCapDescends C p A)
    (hB : InvertibleChernCapDescends C p B) (i : ℕ) :
    firstChernCapStep C p n A hA i = firstChernCapStep C p n B hB i := by
  simp only [firstChernCapStep]
  rw [firstChernClassCapOnChow_congr C p _ A B e (hA _) (hB _)]

/-- **Stacks 02SP for `Stacks.Chow.firstChernCapStep`.** If `D ≅ A ⊗_{𝒪_X} B` then the
degree-raising operation of `D` is the sum of those of `A` and `B`. This is the one place Stacks
02SP enters the proof of Stacks 0FA6, and it is what turns the quotients `ℒ_i ⊗ 𝒩_j` of the
tensor filtration into the sums `x_i + y_j` of the source's computation. -/
theorem firstChernCapStep_eq_add_of_iso_tensorObj (e : D ≅ Scheme.Modules.tensorObj A B)
    (hA : InvertibleChernCapDescends C p A) (hB : InvertibleChernCapDescends C p B)
    (hD : InvertibleChernCapDescends C p D) (i : ℕ) :
    firstChernCapStep C p n D hD i =
      firstChernCapStep C p n A hA i + firstChernCapStep C p n B hB i := by
  simp only [firstChernCapStep]
  rw [firstChernClassCapOnChow_eq_add_of_iso_tensorObj C p _ A B D e (hA _) (hB _) (hD _),
    chowGroupDegreeCast_add]

end Tensor

/-! ### The graded product of the Chow groups, and the shift operators -/

variable (n : ℤ)

/-- The product of all the Chow groups `A_{n-i}(X)`, `i : ℕ`. The first Chern class cap products
of invertible modules act on it as degree-raising endomorphisms, so that their composites are
products in the ring `AddMonoid.End` and the formal computation of Stacks 0FA6 can be performed
once rather than degree by degree. -/
abbrev ChowGradedProduct : Type u := ∀ i : ℕ, chowGroup C p (n - (i : ℤ))

section Shift

variable (A B D : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property A]
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property B]
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property D]

/-- **`c₁(L) ∩ -` as a degree-raising endomorphism of the graded product.** It sends the
component in degree `i` to its first Chern class cap product, which lies in degree `i + 1`, and
kills the component in degree `0`. -/
def firstChernShift (hfac : InvertibleChernCapDescends C p A) :
    AddMonoid.End (ChowGradedProduct C p n) where
  toFun h := fun i => match i with
    | 0 => 0
    | j + 1 => firstChernCapStep C p n A hfac j (h j)
  map_zero' := by funext i; cases i <;> simp
  map_add' a b := by funext i; cases i <;> simp

/-- The shift operator raises degree by one. -/
@[simp] theorem firstChernShift_apply_succ (hfac : InvertibleChernCapDescends C p A)
    (h : ChowGradedProduct C p n) (j : ℕ) :
    firstChernShift C p n A hfac h (j + 1) = firstChernCapStep C p n A hfac j (h j) := rfl

/-- The shift operator kills degree zero. -/
@[simp] theorem firstChernShift_apply_zero (hfac : InvertibleChernCapDescends C p A)
    (h : ChowGradedProduct C p n) : firstChernShift C p n A hfac h 0 = 0 := rfl

/-- The shift operator depends on the invertible module only through its isomorphism class. -/
theorem firstChernShift_congr (e : A ≅ B) (hA : InvertibleChernCapDescends C p A)
    (hB : InvertibleChernCapDescends C p B) :
    firstChernShift C p n A hA = firstChernShift C p n B hB := by
  refine AddMonoidHom.ext fun h => funext fun i => ?_
  match i with
  | 0 => rfl
  | j + 1 =>
      show firstChernCapStep C p n A hA j (h j) = firstChernCapStep C p n B hB j (h j)
      rw [firstChernCapStep_congr C p A B n e hA hB j]

/-- **Stacks 02SP for the shift operators.** The shift of a module isomorphic to `A ⊗ B` is the
sum of the shifts of `A` and `B`. -/
theorem firstChernShift_eq_add_of_iso_tensorObj (e : D ≅ Scheme.Modules.tensorObj A B)
    (hA : InvertibleChernCapDescends C p A) (hB : InvertibleChernCapDescends C p B)
    (hD : InvertibleChernCapDescends C p D) :
    firstChernShift C p n D hD = firstChernShift C p n A hA + firstChernShift C p n B hB := by
  refine AddMonoidHom.ext fun h => funext fun i => ?_
  match i with
  | 0 => exact (zero_add (0 : chowGroup C p (n - ((0 : ℕ) : ℤ)))).symm
  | j + 1 =>
      show firstChernCapStep C p n D hD j (h j)
          = firstChernCapStep C p n A hA j (h j) + firstChernCapStep C p n B hB j (h j)
      rw [firstChernCapStep_eq_add_of_iso_tensorObj C p A B D n e hA hB hD j]
      rfl

/-- **Stacks 02TJ for two invertible modules**, as an identity between the degree-raising
operations `Stacks.Chow.firstChernCapStep` on Chow groups: the two iterated cap products agree in
every degree.

This repository proves Stacks 02TJ only with Stacks 02TH carried as a hypothesis
(`Stacks.Chow.firstChernClassCapOnChowOfInvertible_comm`), and at a different presentation of the
descended operation, so the statement is carried here. -/
def FirstChernCapStepsCommute (hA : InvertibleChernCapDescends C p A)
    (hB : InvertibleChernCapDescends C p B) : Prop :=
  ∀ (i : ℕ) (z : chowGroup C p (n - (i : ℤ))),
    firstChernCapStep C p n A hA (i + 1) (firstChernCapStep C p n B hB i z) =
      firstChernCapStep C p n B hB (i + 1) (firstChernCapStep C p n A hA i z)

/-- Stacks 02TJ is symmetric in the two invertible modules. -/
theorem firstChernCapStepsCommute_symm (hA : InvertibleChernCapDescends C p A)
    (hB : InvertibleChernCapDescends C p B)
    (h : FirstChernCapStepsCommute C p n A B hA hB) :
    FirstChernCapStepsCommute C p n B A hB hA := fun i z => (h i z).symm

/-- Stacks 02TJ makes the shift operators commute in the ring of endomorphisms of the graded
product. -/
theorem commute_firstChernShift (hA : InvertibleChernCapDescends C p A)
    (hB : InvertibleChernCapDescends C p B)
    (hc : FirstChernCapStepsCommute C p n A B hA hB) :
    Commute (firstChernShift C p n A hA) (firstChernShift C p n B hB) := by
  refine AddMonoidHom.ext fun h => funext fun i => ?_
  match i with
  | 0 => rfl
  | 1 =>
      exact (map_zero (firstChernCapStep C p n A hA 0)).trans
        (map_zero (firstChernCapStep C p n B hB 0)).symm
  | j + 2 => exact hc j (h j)

end Shift

/-- The class of a cycle, placed in degree zero of the graded product. -/
def chowGradedUnit (α : chowGroup C p n) : ChowGradedProduct C p n := fun i =>
  match i with
  | 0 => chowGroupDegreeCast C p (by simp)
      (AddMonoidHom.id (chowGroup C p (n - ((0 : ℕ) : ℤ)))) α
  | _ + 1 => 0

/-- In degree zero the graded unit of the class of a cycle is the cycle class of Stacks 02RW, in
the degree a degree-zero cap product lands in. -/
theorem chowGradedUnit_apply_zero (α : CycleGroup C p n) :
    chowGradedUnit C p n (QuotientAddGroup.mk' (rationalEquivalences C p n) α) 0
      = cycleClassDegreeZero C p n α := rfl

/-- Evaluation of an operator on the graded unit of a Chow class, in a fixed degree. -/
def evalChowGraded (α : chowGroup C p n) (i : ℕ) :
    AddMonoid.End (ChowGradedProduct C p n) →+ chowGroup C p (n - (i : ℤ)) where
  toFun f := f (chowGradedUnit C p n α) i
  map_zero' := rfl
  map_add' _ _ := rfl

/-! ### The sequence of shift operators of a finite family -/

section Family

variable {r : ℕ} (L : Fin r → X.Modules)
  [∀ j, AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property (L j)]
  (hfac : ∀ j, InvertibleChernCapDescends C p (L j))

/-- The sequence of shift operators of a finite family of invertible modules, extended by zero
beyond the family. -/
def firstChernShiftSeq (m : ℕ) : AddMonoid.End (ChowGradedProduct C p n) :=
  if h : m < r then firstChernShift C p n (L ⟨m, h⟩) (hfac ⟨m, h⟩) else 0

/-- Inside the range the sequence is the shift operator of the corresponding member. -/
theorem firstChernShiftSeq_of_lt (m : ℕ) (h : m < r) :
    firstChernShiftSeq C p n L hfac m = firstChernShift C p n (L ⟨m, h⟩) (hfac ⟨m, h⟩) :=
  dite_eq_left h

/-- Beyond the range the sequence is zero. -/
theorem firstChernShiftSeq_of_not_lt (m : ℕ) (h : ¬ m < r) :
    firstChernShiftSeq C p n L hfac m = 0 :=
  dite_eq_right h

/-- **`c₁ ∩ -` of a bundle presented by a filtration with invertible quotients**: the sum of the
first Chern class cap operations of the quotients, as a map `A_{n-i}(X) ⟶ A_{n-i-1}(X)`. By
Stacks 02UJ this is `c₁ ∩ -` of the bundle; see
`Stacks.Chow.firstChernCapSum_eq_chernClassCapExt_one`. -/
def firstChernCapSum (i : ℕ) :
    chowGroup C p (n - (i : ℤ)) →+ chowGroup C p (n - ((i + 1 : ℕ) : ℤ)) :=
  ∑ j : Fin r, firstChernCapStep C p n (L j) (hfac j) i

/-- The sum of the sequence over its range is the sum over the family. -/
theorem sum_range_firstChernShiftSeq :
    (∑ m ∈ range r, firstChernShiftSeq C p n L hfac m)
      = ∑ j : Fin r, firstChernShift C p n (L j) (hfac j) := by
  rw [← Fin.sum_univ_eq_sum_range (fun m => firstChernShiftSeq C p n L hfac m) r]
  exact Finset.sum_congr rfl fun j _ => dite_eq_left j.isLt

/-- The sum of the sequence, read in degree `i + 1`, is `c₁ ∩ -` applied to the component in
degree `i`. -/
theorem sum_range_firstChernShiftSeq_apply (h : ChowGradedProduct C p n) (i : ℕ) :
    (∑ m ∈ range r, firstChernShiftSeq C p n L hfac m) h (i + 1)
      = firstChernCapSum C p n L hfac i (h i) := by
  rw [sum_range_firstChernShiftSeq, addMonoidEnd_sum_apply, Finset.sum_apply]
  simp only [firstChernShift_apply_succ]
  rw [firstChernCapSum, AddMonoidHom.finsetSum_apply]

/-- Commutativity of two sequences of shift operators, granted Stacks 02TJ for every pair of
members of the two families. -/
theorem commute_firstChernShiftSeq {s : ℕ} (N : Fin s → X.Modules)
    [∀ j, AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property (N j)]
    (hfacN : ∀ j, InvertibleChernCapDescends C p (N j))
    (hc : ∀ (a : Fin r) (b : Fin s),
      FirstChernCapStepsCommute C p n (L a) (N b) (hfac a) (hfacN b)) (a b : ℕ) :
    Commute (firstChernShiftSeq C p n L hfac a) (firstChernShiftSeq C p n N hfacN b) := by
  by_cases ha : a < r
  · by_cases hb : b < s
    · rw [firstChernShiftSeq_of_lt C p n L hfac a ha, firstChernShiftSeq_of_lt C p n N hfacN b hb]
      exact commute_firstChernShift C p n _ _ _ _ (hc ⟨a, ha⟩ ⟨b, hb⟩)
    · rw [firstChernShiftSeq_of_not_lt C p n N hfacN b hb]
      exact Commute.zero_right _
  · rw [firstChernShiftSeq_of_not_lt C p n L hfac a ha]
    exact Commute.zero_left _

/-- **The elementary symmetric cap operations of Stacks 02UJ, read in the operator ring.** The
`k`-th elementary symmetric function of the first Chern class cap operations of a family of
invertible modules, applied to the class of a cycle, is the `k`-th component of the value of
`Stacks.Chow.esymRec` on the graded unit. -/
theorem elemSymmChernCap_eq_esymRec (α : chowGroup C p n) :
    ∀ (m : ℕ) (hm : m ≤ r) (k : ℕ),
      elemSymmChernCap C p n L hfac m hm k α
        = esymRec (firstChernShiftSeq C p n L hfac) m k (chowGradedUnit C p n α) k := by
  intro m
  induction m with
  | zero =>
      intro hm k
      cases k with
      | zero => rw [esymRec_degree_zero]; rfl
      | succ k => rw [esymRec_zero_succ]; rfl
  | succ m ih =>
      intro hm k
      have hm' : m < r := hm
      cases k with
      | zero => rw [esymRec_degree_zero]; rfl
      | succ k =>
          rw [esymRec_succ, firstChernShiftSeq_of_lt C p n L hfac m hm']
          show elemSymmChernCap C p n L hfac (m + 1) hm (k + 1) α = _
          rw [elemSymmChernCap_succ C p n L hfac m hm k]
          simp only [AddMonoidHom.add_apply, AddMonoidHom.coe_comp, Function.comp_apply]
          rw [ih (Nat.le_of_succ_le hm) (k + 1), ih (Nat.le_of_succ_le hm) k]
          rfl

end Family

/-! ### Stacks 02UJ, read in the operator ring -/

section Tower

variable {r : ℕ} (L : Fin r → X.Modules)
  [∀ j, AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property (L j)]
  (hfac : ∀ j, InvertibleChernCapDescends C p (L j))

/-- **Stacks 02UJ, read in the operator ring.** For a tower `Q` of length `r` with invertible
successive quotients `L`, the `k`-th Chern class cap product of its top is the degree-`k`
component of the `k`-th elementary symmetric function of the shift operators of the quotients,
evaluated on the class of `α`.

The hypotheses are exactly those of `Stacks.Chow.chernClassCapExt_eq_elemSymmChernCap_of_tower`,
which see for why each is carried. -/
theorem chernClassCapExt_eq_esymRec (Q : ℕ → X.Modules)
    (sub : ∀ j : Fin r, L j ⟶ Q ((j : ℕ) + 1)) (proj : ∀ j : Fin r, Q ((j : ℕ) + 1) ⟶ Q (j : ℕ))
    (hzero : ∀ j : Fin r, sub j ≫ proj j = 0)
    (hexact : ∀ j : Fin r, (ShortComplex.mk (sub j) (proj j) (hzero j)).ShortExact)
    (hrank : ∀ m : ℕ, m ≤ r → PullbackPreservesRank (Q m) m)
    (chern : ∀ m : ℕ, ChernClassCycleRule C m) (α : CycleGroup C p n)
    (hnorm : ∀ (m : ℕ) (hm : m ≤ r),
      chernClassCapExt C p n (Q m) m (hrank m hm) (chern m) 0 α = cycleClassDegreeZero C p n α)
    (hbinom : ∀ j : Fin r, ∀ i ≤ (j : ℕ) + 1,
      binomialTransform (inverseFirstChernCapStep C p n (L j) (hfac j)) ((j : ℕ) + 1)
          (chernCapFamily C p n (Q ((j : ℕ) + 1)) ((j : ℕ) + 1) (hrank ((j : ℕ) + 1) j.isLt)
            (chern ((j : ℕ) + 1)) α) i =
        binomialTransform (inverseFirstChernCapStep C p n (L j) (hfac j)) (j : ℕ)
          (chernCapFamily C p n (Q (j : ℕ)) (j : ℕ) (hrank (j : ℕ) j.isLt.le)
            (chern (j : ℕ)) α) i)
    (k : ℕ) :
    chernClassCapExt C p n (Q r) r (hrank r le_rfl) (chern r) k α
      = evalChowGraded C p n (QuotientAddGroup.mk' (rationalEquivalences C p n) α) k
          (esymRec (firstChernShiftSeq C p n L hfac) r k) := by
  rw [chernClassCapExt_eq_elemSymmChernCap_of_tower C p n L hfac Q sub proj hzero hexact hrank
    chern α hnorm hbinom r le_rfl k]
  exact elemSymmChernCap_eq_esymRec C p n L hfac _ r le_rfl k

/-- **The identification of `Stacks.Chow.firstChernCapSum` with `c₁ ∩ -`.** For a tower `Q` with
invertible quotients `L`, the sum of the first Chern class cap operations of the quotients, applied
to the cycle class of `α`, is `c₁(Q r) ∩ α`. This is Stacks 02UJ in degree one. -/
theorem firstChernCapSum_eq_chernClassCapExt_one (Q : ℕ → X.Modules)
    (sub : ∀ j : Fin r, L j ⟶ Q ((j : ℕ) + 1)) (proj : ∀ j : Fin r, Q ((j : ℕ) + 1) ⟶ Q (j : ℕ))
    (hzero : ∀ j : Fin r, sub j ≫ proj j = 0)
    (hexact : ∀ j : Fin r, (ShortComplex.mk (sub j) (proj j) (hzero j)).ShortExact)
    (hrank : ∀ m : ℕ, m ≤ r → PullbackPreservesRank (Q m) m)
    (chern : ∀ m : ℕ, ChernClassCycleRule C m) (α : CycleGroup C p n)
    (hnorm : ∀ (m : ℕ) (hm : m ≤ r),
      chernClassCapExt C p n (Q m) m (hrank m hm) (chern m) 0 α = cycleClassDegreeZero C p n α)
    (hbinom : ∀ j : Fin r, ∀ i ≤ (j : ℕ) + 1,
      binomialTransform (inverseFirstChernCapStep C p n (L j) (hfac j)) ((j : ℕ) + 1)
          (chernCapFamily C p n (Q ((j : ℕ) + 1)) ((j : ℕ) + 1) (hrank ((j : ℕ) + 1) j.isLt)
            (chern ((j : ℕ) + 1)) α) i =
        binomialTransform (inverseFirstChernCapStep C p n (L j) (hfac j)) (j : ℕ)
          (chernCapFamily C p n (Q (j : ℕ)) (j : ℕ) (hrank (j : ℕ) j.isLt.le)
            (chern (j : ℕ)) α) i) :
    firstChernCapSum C p n L hfac 0 (cycleClassDegreeZero C p n α)
      = chernClassCapExt C p n (Q r) r (hrank r le_rfl) (chern r) 1 α := by
  rw [chernClassCapExt_eq_esymRec C p n L hfac Q sub proj hzero hexact hrank chern α hnorm
    hbinom 1, esymRec_one]
  exact (sum_range_firstChernShiftSeq_apply C p n L hfac
    (chowGradedUnit C p n (QuotientAddGroup.mk' (rationalEquivalences C p n) α)) 0).symm

end Tower

/-! ### The lexicographic enumeration of the quotients of a tensor product -/

/-- The lexicographic index of the pair `(i, j)`: the position of the `j`-th member of the `i`-th
block in `Fin (r * s)`. -/
def finLexIndex {r s : ℕ} (i : Fin r) (j : Fin s) : Fin (r * s) :=
  ⟨(i : ℕ) * s + (j : ℕ), by
    have hi := i.isLt
    have hj := j.isLt
    calc (i : ℕ) * s + (j : ℕ) < (i : ℕ) * s + s := by omega
      _ = ((i : ℕ) + 1) * s := by ring
      _ ≤ r * s := by gcongr; omega⟩

section TensorFamily

variable {r s : ℕ} (L : Fin r → X.Modules)
  [∀ j, AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property (L j)]
  (hfacL : ∀ j, InvertibleChernCapDescends C p (L j))
  (N : Fin s → X.Modules)
  [∀ j, AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property (N j)]
  (hfacN : ∀ j, InvertibleChernCapDescends C p (N j))
  (M : Fin (r * s) → X.Modules)
  [∀ j, AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property (M j)]
  (hfacM : ∀ j, InvertibleChernCapDescends C p (M j))

/-- The generating set of the commutative operator subring: the shift operators of the two
families of quotients. -/
def firstChernShiftGenerators : Set (AddMonoid.End (ChowGradedProduct C p n)) :=
  Set.range (firstChernShiftSeq C p n L hfacL) ∪ Set.range (firstChernShiftSeq C p n N hfacN)

/-- **The lexicographic family is the sum of the two families.** If the `(i·s+j)`-th quotient of
the tensor filtration is `ℒ_i ⊗ 𝒩_j`, its shift operator is the sum of those of `ℒ_i` and
`𝒩_j`; this is Stacks 02SP. -/
theorem firstChernShiftSeq_tensor
    (hquot : ∀ (i : Fin r) (j : Fin s),
      M (finLexIndex i j) ≅ Scheme.Modules.tensorObj (L i) (N j))
    (i : ℕ) (hi : i < r) (j : ℕ) (hj : j < s) :
    firstChernShiftSeq C p n M hfacM (i * s + j)
      = firstChernShiftSeq C p n L hfacL i + firstChernShiftSeq C p n N hfacN j := by
  have hij : i * s + j < r * s := (finLexIndex (⟨i, hi⟩ : Fin r) (⟨j, hj⟩ : Fin s)).isLt
  rw [firstChernShiftSeq_of_lt C p n M hfacM _ hij,
    firstChernShiftSeq_of_lt C p n L hfacL i hi, firstChernShiftSeq_of_lt C p n N hfacN j hj]
  exact firstChernShift_eq_add_of_iso_tensorObj C p n (L ⟨i, hi⟩) (N ⟨j, hj⟩) (M ⟨i * s + j, hij⟩)
    (hquot ⟨i, hi⟩ ⟨j, hj⟩) (hfacL _) (hfacN _) (hfacM _)

/-- Every shift operator of the tensor filtration lies in the subring generated by the shift
operators of the two factors' filtrations. -/
theorem firstChernShiftSeq_tensor_mem
    (hquot : ∀ (i : Fin r) (j : Fin s),
      M (finLexIndex i j) ≅ Scheme.Modules.tensorObj (L i) (N j)) (k : ℕ) :
    firstChernShiftSeq C p n M hfacM k
      ∈ Subring.closure (firstChernShiftGenerators C p n L hfacL N hfacN) := by
  by_cases hk : k < r * s
  · have hs : 0 < s := Nat.pos_of_ne_zero fun h => by simp [h] at hk
    have hdiv : k / s < r := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hk)
    have hmod : k % s < s := Nat.mod_lt _ hs
    have heq : k / s * s + k % s = k := by rw [Nat.mul_comm]; exact Nat.div_add_mod k s
    have hstep := firstChernShiftSeq_tensor C p n L hfacL N hfacN M hfacM hquot
      (k / s) hdiv (k % s) hmod
    rw [heq] at hstep
    rw [hstep]
    exact add_mem (Subring.subset_closure (Or.inl ⟨k / s, rfl⟩))
      (Subring.subset_closure (Or.inr ⟨k % s, rfl⟩))
  · rw [firstChernShiftSeq_of_not_lt C p n M hfacM k hk]
    exact zero_mem _

/-- Granted Stacks 02TJ for every pair of quotients, the generating set of the operator subring
consists of pairwise commuting elements, so that subring is commutative. -/
theorem firstChernShiftGenerators_comm
    (hcommLL : ∀ a b : Fin r, FirstChernCapStepsCommute C p n (L a) (L b) (hfacL a) (hfacL b))
    (hcommNN : ∀ a b : Fin s, FirstChernCapStepsCommute C p n (N a) (N b) (hfacN a) (hfacN b))
    (hcommLN : ∀ (a : Fin r) (b : Fin s),
      FirstChernCapStepsCommute C p n (L a) (N b) (hfacL a) (hfacN b)) :
    ∀ a ∈ firstChernShiftGenerators C p n L hfacL N hfacN,
      ∀ b ∈ firstChernShiftGenerators C p n L hfacL N hfacN, a * b = b * a := by
  simp only [firstChernShiftGenerators, Set.mem_union, Set.mem_range]
  rintro a (⟨i, rfl⟩ | ⟨i, rfl⟩) b (⟨j, rfl⟩ | ⟨j, rfl⟩)
  · exact commute_firstChernShiftSeq C p n L hfacL L hfacL hcommLL i j
  · exact commute_firstChernShiftSeq C p n L hfacL N hfacN hcommLN i j
  · exact commute_firstChernShiftSeq C p n N hfacN L hfacL
      (fun a b => firstChernCapStepsCommute_symm C p n (L b) (N a) (hfacL b) (hfacN a)
        (hcommLN b a)) i j
  · exact commute_firstChernShiftSeq C p n N hfacN N hfacN hcommNN i j

/-- The lexicographic family satisfies the block hypothesis of the formal computation. -/
theorem firstChernShiftSeq_lexFamily
    (hquot : ∀ (i : Fin r) (j : Fin s),
      M (finLexIndex i j) ≅ Scheme.Modules.tensorObj (L i) (N j)) :
    ∀ i, i < r → ∀ j, j < s →
      firstChernShiftSeq C p n M hfacM (i * s + j)
        = firstChernShiftSeq C p n L hfacL i + firstChernShiftSeq C p n N hfacN j :=
  fun i hi j hj => firstChernShiftSeq_tensor C p n L hfacL N hfacN M hfacM hquot i hi j hj

end TensorFamily

/-! ### Evaluating a product of two operator sums -/

/-- The product of two sums of shift operators, evaluated in degree two on the graded unit of a
Chow class, is the iterated cap product. -/
theorem evalChowGraded_two_mul_sum (α : chowGroup C p n) {r s : ℕ} (L : Fin r → X.Modules)
    [∀ j, AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property (L j)]
    (hfacL : ∀ j, InvertibleChernCapDescends C p (L j)) (N : Fin s → X.Modules)
    [∀ j, AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property (N j)]
    (hfacN : ∀ j, InvertibleChernCapDescends C p (N j)) :
    evalChowGraded C p n α 2 ((∑ m ∈ range r, firstChernShiftSeq C p n L hfacL m) *
        ∑ m ∈ range s, firstChernShiftSeq C p n N hfacN m)
      = firstChernCapSum C p n L hfacL 1
          (firstChernCapSum C p n N hfacN 0 (chowGradedUnit C p n α 0)) := by
  have h1 := sum_range_firstChernShiftSeq_apply C p n N hfacN (chowGradedUnit C p n α) 0
  have h2 := sum_range_firstChernShiftSeq_apply C p n L hfacL
    ((∑ m ∈ range s, firstChernShiftSeq C p n N hfacN m) (chowGradedUnit C p n α)) 1
  exact h2.trans (congrArg _ h1)

/-! ### Stacks 0FA6 -/

section Main

variable {r s : ℕ} (L : Fin r → X.Modules)
  [∀ j, AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property (L j)]
  (hfacL : ∀ j, InvertibleChernCapDescends C p (L j))
  (N : Fin s → X.Modules)
  [∀ j, AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property (N j)]
  (hfacN : ∀ j, InvertibleChernCapDescends C p (N j))
  (M : Fin (r * s) → X.Modules)
  [∀ j, AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property (M j)]
  (hfacM : ∀ j, InvertibleChernCapDescends C p (M j))
  (E F T : ℕ → X.Modules)
  (subE : ∀ i : Fin r, L i ⟶ E ((i : ℕ) + 1)) (projE : ∀ i : Fin r, E ((i : ℕ) + 1) ⟶ E (i : ℕ))
  (hzeroE : ∀ i : Fin r, subE i ≫ projE i = 0)
  (hexactE : ∀ i : Fin r, (ShortComplex.mk (subE i) (projE i) (hzeroE i)).ShortExact)
  (hrankE : ∀ m : ℕ, m ≤ r → PullbackPreservesRank (E m) m)
  (subF : ∀ j : Fin s, N j ⟶ F ((j : ℕ) + 1)) (projF : ∀ j : Fin s, F ((j : ℕ) + 1) ⟶ F (j : ℕ))
  (hzeroF : ∀ j : Fin s, subF j ≫ projF j = 0)
  (hexactF : ∀ j : Fin s, (ShortComplex.mk (subF j) (projF j) (hzeroF j)).ShortExact)
  (hrankF : ∀ m : ℕ, m ≤ s → PullbackPreservesRank (F m) m)
  (subT : ∀ k : Fin (r * s), M k ⟶ T ((k : ℕ) + 1))
  (projT : ∀ k : Fin (r * s), T ((k : ℕ) + 1) ⟶ T (k : ℕ))
  (hzeroT : ∀ k : Fin (r * s), subT k ≫ projT k = 0)
  (hexactT : ∀ k : Fin (r * s), (ShortComplex.mk (subT k) (projT k) (hzeroT k)).ShortExact)
  (hrankT : ∀ m : ℕ, m ≤ r * s → PullbackPreservesRank (T m) m)
  (chernE chernF chernT : ∀ m : ℕ, ChernClassCycleRule C m) (α : CycleGroup C p n)

include hexactE hexactF hexactT in
/-- **Stacks 0FA6, the first displayed identity, componentwise on cap products.** Let `ℰ = E r`
be finite locally free of rank `r` with a filtration whose successive quotients are the invertible
modules `ℒ_i = L i`, let `ℱ = F s` be finite locally free of rank `s` with a filtration whose
successive quotients are the invertible modules `𝒩_j = N j`, and let the tower `T` be a filtration
of `ℰ ⊗_{𝒪_X} ℱ` of length `r·s` whose `(i·s+j)`-th successive quotient is `ℒ_i ⊗_{𝒪_X} 𝒩_j`,
which is the lexicographic filtration of the source. Then for every `n`-cycle `α`

  `c₁(ℰ ⊗ ℱ) ∩ α = s·(c₁(ℰ) ∩ α) + r·(c₁(ℱ) ∩ α)`

in `A_{n-1}(X)`, which is the identity `c₁(ℰ ⊗ ℱ) = r·c₁(ℱ) + s·c₁(ℰ)` of the source read against
`α`. The rank hypotheses enter as the lengths `r` and `s` of the two filtrations, as the rank
`r·s` of the tensor product, and as the two coefficients. -/
@[stacks 0FA6 "the first displayed identity, componentwise on cap products, and conditional.  \
CORRECTION OF FORM: the source states c_1(E tensor F) = r c_1(F) + s c_1(E) in the bivariant ring \
A^*(X).  This development has no bivariant ring and no total Chern class, for the reason recorded \
in the Stacks 02UH clause of \
StacksFrontier.AlgebraicGeometry.Chow.ChernWhitney.CapProductRelation, so -- exactly as for Stacks \
02UJ and Stacks 0FA5, which this result is read on top of -- the identity is stated degree by \
degree as cap products against a fixed cycle: for every n and every alpha in CycleGroup C p n, \
c_1(E tensor F) cap alpha = s times (c_1(E) cap alpha) plus r times (c_1(F) cap alpha) in \
A_{n-1}(X).  The module on the left is the library's canonical tensor product \
AlgebraicGeometry.Scheme.Modules.tensorObj of the two bundles, identified with the top of the \
tensor filtration by the hypothesis hTop.  WHAT IS CARRIED: the reduction of the source's proof \
to the filtered case, i.e. the three filtrations themselves, as the towers of short exact \
sequences that Stacks 02UJ consumes -- for E with invertible quotients L_i, for F with invertible \
quotients N_j, and for E tensor F with quotients M_k, together with hquot, the source's \
lexicographic identification M_{i*s+j} iso L_i tensor N_j.  The source gets these from Stacks \
02UL and the injectivity of pi^*, and that reduction CANNOT be performed in this repository, for \
the two independent reasons recorded in the Stacks 0FA5 clause of \
StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.DualChernClasses: Stacks 02UL is formalized as \
Stacks.Chow.exists_splittingMorphism and delivers \
Stacks.WeilCohomology.HasInvertibleFiltration, an inductive Prop from which the tower of modules \
and maps that Stacks 02UJ needs -- which is data -- cannot be eliminated; and nothing in this \
repository states that the Chern class cap product commutes with flat pullback (the clause of \
Stacks 02U0 quoted as Stacks 02U1), so injectivity of pi^* has no identity on P to descend to X.  \
ALSO CARRIED, each of them an input of Stacks 02UJ itself and carried there for the same reason: \
chernE, chernF, chernT, the Stacks 02U0 component data in every rank; hnormE, hnormF, hnormT, the \
Stacks 02U0 normalisation c_0 = 1 along each tower; hbinomE, hbinomF, hbinomT, the equality of \
binomial transforms that Stacks 02UD gives once Stacks 02UG is applied, neither of which is \
proved here; hfacL, hfacN, hfacM, Stacks 02TI for c_1 of each quotient; and hrankTensor, the \
rank-preservation of the tensor product in rank r*s, carried exactly as \
StacksFrontier.AlgebraicGeometry.Chow.ChernClassTwist carries hrankEL for a twist -- the rank \
multiplicativity of a tensor product has no library presence in the PullbackPreservesRank form \
the cap products need.  NOT \
CARRIED, i.e. proved here: Stacks 02SP for the descended operations, \
firstChernCapStep_eq_add_of_iso_tensorObj, giving c_1(L tensor N) cap - = c_1(L) cap - + c_1(N) \
cap -, which is absent from this repository before this file; and the degree-one half of the \
formal computation the source omits, namely that the sum over the lexicographic family of the \
r*s operations c_1(L_i) + c_1(N_j) is s times the sum of the c_1(L_i) plus r times the sum of the \
c_1(N_j), proved for every r and every s as sum_range_lexFamily.  Stacks 02TJ is NOT needed for \
this identity and is NOT carried: sum_range_lexFamily is proved for an arbitrary ring.  It is \
carried by the degree-two identity chernClassCapExt_tensorObj_two, where it is genuinely \
needed"]
theorem chernClassCapExt_tensorObj_one
    (hnormE : ∀ (m : ℕ) (hm : m ≤ r),
      chernClassCapExt C p n (E m) m (hrankE m hm) (chernE m) 0 α = cycleClassDegreeZero C p n α)
    (hbinomE : ∀ i : Fin r, ∀ t ≤ (i : ℕ) + 1,
      binomialTransform (inverseFirstChernCapStep C p n (L i) (hfacL i)) ((i : ℕ) + 1)
          (chernCapFamily C p n (E ((i : ℕ) + 1)) ((i : ℕ) + 1) (hrankE ((i : ℕ) + 1) i.isLt)
            (chernE ((i : ℕ) + 1)) α) t =
        binomialTransform (inverseFirstChernCapStep C p n (L i) (hfacL i)) (i : ℕ)
          (chernCapFamily C p n (E (i : ℕ)) (i : ℕ) (hrankE (i : ℕ) i.isLt.le)
            (chernE (i : ℕ)) α) t)
    (hnormF : ∀ (m : ℕ) (hm : m ≤ s),
      chernClassCapExt C p n (F m) m (hrankF m hm) (chernF m) 0 α = cycleClassDegreeZero C p n α)
    (hbinomF : ∀ j : Fin s, ∀ t ≤ (j : ℕ) + 1,
      binomialTransform (inverseFirstChernCapStep C p n (N j) (hfacN j)) ((j : ℕ) + 1)
          (chernCapFamily C p n (F ((j : ℕ) + 1)) ((j : ℕ) + 1) (hrankF ((j : ℕ) + 1) j.isLt)
            (chernF ((j : ℕ) + 1)) α) t =
        binomialTransform (inverseFirstChernCapStep C p n (N j) (hfacN j)) (j : ℕ)
          (chernCapFamily C p n (F (j : ℕ)) (j : ℕ) (hrankF (j : ℕ) j.isLt.le)
            (chernF (j : ℕ)) α) t)
    (hnormT : ∀ (m : ℕ) (hm : m ≤ r * s),
      chernClassCapExt C p n (T m) m (hrankT m hm) (chernT m) 0 α = cycleClassDegreeZero C p n α)
    (hbinomT : ∀ k : Fin (r * s), ∀ t ≤ (k : ℕ) + 1,
      binomialTransform (inverseFirstChernCapStep C p n (M k) (hfacM k)) ((k : ℕ) + 1)
          (chernCapFamily C p n (T ((k : ℕ) + 1)) ((k : ℕ) + 1) (hrankT ((k : ℕ) + 1) k.isLt)
            (chernT ((k : ℕ) + 1)) α) t =
        binomialTransform (inverseFirstChernCapStep C p n (M k) (hfacM k)) (k : ℕ)
          (chernCapFamily C p n (T (k : ℕ)) (k : ℕ) (hrankT (k : ℕ) k.isLt.le)
            (chernT (k : ℕ)) α) t)
    (hquot : ∀ (i : Fin r) (j : Fin s),
      M (finLexIndex i j) ≅ Scheme.Modules.tensorObj (L i) (N j))
    (hTop : T (r * s) = Scheme.Modules.tensorObj (E r) (F s))
    (hrankTensor : PullbackPreservesRank (Scheme.Modules.tensorObj (E r) (F s)) (r * s)) :
    chernClassCapExt C p n (Scheme.Modules.tensorObj (E r) (F s)) (r * s) hrankTensor
        (chernT (r * s)) 1 α
      = (s : ℤ) • chernClassCapExt C p n (E r) r (hrankE r le_rfl) (chernE r) 1 α
        + (r : ℤ) • chernClassCapExt C p n (F s) s (hrankF s le_rfl) (chernF s) 1 α := by
  rw [chernClassCapExt_congr_module C p n hTop.symm (r * s) hrankTensor
      (hrankT (r * s) le_rfl) (chernT (r * s)) 1,
    chernClassCapExt_eq_esymRec C p n M hfacM T subT projT hzeroT hexactT hrankT chernT α
      hnormT hbinomT 1,
    chernClassCapExt_eq_esymRec C p n L hfacL E subE projE hzeroE hexactE hrankE chernE α
      hnormE hbinomE 1,
    chernClassCapExt_eq_esymRec C p n N hfacN F subF projF hzeroF hexactF hrankF chernF α
      hnormF hbinomF 1]
  simp only [esymRec_one]
  rw [sum_range_lexFamily_zsmul (firstChernShiftSeq C p n L hfacL)
      (firstChernShiftSeq C p n N hfacN) (firstChernShiftSeq C p n M hfacM) r s
      (firstChernShiftSeq_lexFamily C p n L hfacL N hfacN M hfacM hquot)]
  simp only [map_add, map_zsmul]

include hexactE hexactF hexactT in
/-- **Stacks 0FA6, the second displayed identity, componentwise on cap products.** In the
situation of `Stacks.Chow.chernClassCapExt_tensorObj_one`, for every `n`-cycle `α`

  `c₂(ℰ ⊗ ℱ) ∩ α = s·(c₂(ℰ) ∩ α) + r·(c₂(ℱ) ∩ α) + C(r,2)·(c₁(ℱ) ∩ (c₁(ℱ) ∩ α))
      + (r·s − 1)·(c₁(ℰ) ∩ (c₁(ℱ) ∩ α)) + C(s,2)·(c₁(ℰ) ∩ (c₁(ℰ) ∩ α))`

in `A_{n-2}(X)`, which is the identity
`c₂(ℰ ⊗ ℱ) = r·c₂(ℱ) + s·c₂(ℰ) + C(r,2)·c₁(ℱ)² + (r·s − 1)·c₁(ℱ)·c₁(ℰ) + C(s,2)·c₁(ℰ)²` of the
source read against `α`, its five summands in a different order. The coefficient of the cross
term is `r·s − 1`.

The outer first Chern class of each of the three iterated terms is `Stacks.Chow.firstChernCapSum`,
the sum of the first Chern class cap operations of the quotients of the corresponding filtration,
which `Stacks.Chow.firstChernCapSum_eq_chernClassCapExt_one` identifies with `c₁ ∩ -`; the inner
one is the Chern class cap product of Stacks 02U5 itself. Writing the squares this way is forced:
the cap products of Stacks 02U5 go from cycles to Chow classes, so they cannot be iterated, and
this development has no bivariant ring in which `c₁(ℱ)²` would be a class. -/
@[stacks 0FA6 "the second displayed identity, componentwise on cap products, and conditional.  \
CORRECTION OF FORM: the source states c_2(E tensor F) = r c_2(F) + s c_2(E) + binom(r,2) \
c_1(F)^2 + (r*s - 1) c_1(F) c_1(E) + binom(s,2) c_1(E)^2 in the bivariant ring A^*(X).  This \
development has no bivariant ring and no total Chern class, for the reason recorded in the Stacks \
02UH clause of StacksFrontier.AlgebraicGeometry.Chow.ChernWhitney.CapProductRelation, so -- exactly \
as for Stacks 02UJ and Stacks 0FA5, which this result is read on top of -- the identity is stated \
degree by degree as cap products against a fixed cycle: for every n and every alpha in CycleGroup \
C p n, c_2(E tensor F) cap alpha = s times (c_2(E) cap alpha) plus r times (c_2(F) cap alpha) \
plus binom(r,2) times (c_1(F) cap (c_1(F) cap alpha)) plus (r*s - 1) times (c_1(E) cap (c_1(F) \
cap alpha)) plus binom(s,2) times (c_1(E) cap (c_1(E) cap alpha)) in A_{n-2}(X).  The cross-term \
coefficient is r*s - 1, as in the source, and NOT r*s.  The five summands appear in a different \
order from the source's; addition is commutative.  Each squared or mixed term is a COMPOSITE of \
operations rather than a product of classes, with the outer factor the descended operation \
firstChernCapSum -- the sum of the Stacks 02TI operations of the quotients of the relevant \
filtration, identified with c_1 cap - by firstChernCapSum_eq_chernClassCapExt_one -- and the \
inner factor the Stacks 02U5 cap product itself: the cap products of Stacks 02U5 go from cycles \
to Chow classes and so cannot be iterated, and there is no ring in which c_1(F)^2 would be a \
class.  The module on the left is the library's canonical tensor product \
AlgebraicGeometry.Scheme.Modules.tensorObj of the two bundles, identified with the top of the \
tensor filtration by the hypothesis hTop.  WHAT IS CARRIED: exactly what \
chernClassCapExt_tensorObj_one carries, and for the same reasons -- the three filtrations as the \
towers Stacks 02UJ consumes together with hquot, the source's lexicographic identification \
M_{i*s+j} iso L_i tensor N_j, because the reduction via Stacks 02UL and the injectivity of pi^* \
cannot be performed in this repository; the Stacks 02U0 data chern* and normalisations hnorm*; \
the binomial-transform agreements hbinom* that Stacks 02UD and Stacks 02UG would give; Stacks \
02TI for c_1 of each quotient as hfac*; and hrankTensor, the rank-preservation of the tensor \
product in rank r*s, which has no library presence in the PullbackPreservesRank form the cap \
products need and is carried exactly as StacksFrontier.AlgebraicGeometry.Chow.ChernClassTwist \
carries hrankEL for a twist.  ADDITIONALLY CARRIED here, and not by the degree-one identity: \
Stacks \
02TJ, as hcommLL, hcommNN and hcommLN, the commutativity of the first Chern class cap operations \
of the quotients.  This repository proves Stacks 02TJ only with Stacks 02TH carried as a \
hypothesis (Stacks.Chow.firstChernClassCapOnChowOfInvertible_comm) and at a different \
presentation of the descended operation, so the statement itself is carried.  It is genuinely \
needed: the source works in a commutative ring, and without commutativity the degree-two \
elementary symmetric function of the lexicographic family does not collapse -- the cancellation \
that turns the block-dependent coefficient s*(i+1) - 1 into the constant r*s - 1 is exactly a \
commutation.  NOT CARRIED, i.e. proved here: Stacks 02SP for the descended operations \
(firstChernCapStep_eq_add_of_iso_tensorObj), absent from this repository before this file; and \
the whole of the formal computation the source omits, in degree two and for every r and every s, \
as esymRec_block_increment, esymRec_two_block and esymRec_two_tensor"]
theorem chernClassCapExt_tensorObj_two
    (hnormE : ∀ (m : ℕ) (hm : m ≤ r),
      chernClassCapExt C p n (E m) m (hrankE m hm) (chernE m) 0 α = cycleClassDegreeZero C p n α)
    (hbinomE : ∀ i : Fin r, ∀ t ≤ (i : ℕ) + 1,
      binomialTransform (inverseFirstChernCapStep C p n (L i) (hfacL i)) ((i : ℕ) + 1)
          (chernCapFamily C p n (E ((i : ℕ) + 1)) ((i : ℕ) + 1) (hrankE ((i : ℕ) + 1) i.isLt)
            (chernE ((i : ℕ) + 1)) α) t =
        binomialTransform (inverseFirstChernCapStep C p n (L i) (hfacL i)) (i : ℕ)
          (chernCapFamily C p n (E (i : ℕ)) (i : ℕ) (hrankE (i : ℕ) i.isLt.le)
            (chernE (i : ℕ)) α) t)
    (hnormF : ∀ (m : ℕ) (hm : m ≤ s),
      chernClassCapExt C p n (F m) m (hrankF m hm) (chernF m) 0 α = cycleClassDegreeZero C p n α)
    (hbinomF : ∀ j : Fin s, ∀ t ≤ (j : ℕ) + 1,
      binomialTransform (inverseFirstChernCapStep C p n (N j) (hfacN j)) ((j : ℕ) + 1)
          (chernCapFamily C p n (F ((j : ℕ) + 1)) ((j : ℕ) + 1) (hrankF ((j : ℕ) + 1) j.isLt)
            (chernF ((j : ℕ) + 1)) α) t =
        binomialTransform (inverseFirstChernCapStep C p n (N j) (hfacN j)) (j : ℕ)
          (chernCapFamily C p n (F (j : ℕ)) (j : ℕ) (hrankF (j : ℕ) j.isLt.le)
            (chernF (j : ℕ)) α) t)
    (hnormT : ∀ (m : ℕ) (hm : m ≤ r * s),
      chernClassCapExt C p n (T m) m (hrankT m hm) (chernT m) 0 α = cycleClassDegreeZero C p n α)
    (hbinomT : ∀ k : Fin (r * s), ∀ t ≤ (k : ℕ) + 1,
      binomialTransform (inverseFirstChernCapStep C p n (M k) (hfacM k)) ((k : ℕ) + 1)
          (chernCapFamily C p n (T ((k : ℕ) + 1)) ((k : ℕ) + 1) (hrankT ((k : ℕ) + 1) k.isLt)
            (chernT ((k : ℕ) + 1)) α) t =
        binomialTransform (inverseFirstChernCapStep C p n (M k) (hfacM k)) (k : ℕ)
          (chernCapFamily C p n (T (k : ℕ)) (k : ℕ) (hrankT (k : ℕ) k.isLt.le)
            (chernT (k : ℕ)) α) t)
    (hquot : ∀ (i : Fin r) (j : Fin s),
      M (finLexIndex i j) ≅ Scheme.Modules.tensorObj (L i) (N j))
    (hcommLL : ∀ a b : Fin r, FirstChernCapStepsCommute C p n (L a) (L b) (hfacL a) (hfacL b))
    (hcommNN : ∀ a b : Fin s, FirstChernCapStepsCommute C p n (N a) (N b) (hfacN a) (hfacN b))
    (hcommLN : ∀ (a : Fin r) (b : Fin s),
      FirstChernCapStepsCommute C p n (L a) (N b) (hfacL a) (hfacN b))
    (hTop : T (r * s) = Scheme.Modules.tensorObj (E r) (F s))
    (hrankTensor : PullbackPreservesRank (Scheme.Modules.tensorObj (E r) (F s)) (r * s)) :
    chernClassCapExt C p n (Scheme.Modules.tensorObj (E r) (F s)) (r * s) hrankTensor
        (chernT (r * s)) 2 α
      = (s : ℤ) • chernClassCapExt C p n (E r) r (hrankE r le_rfl) (chernE r) 2 α
        + (r : ℤ) • chernClassCapExt C p n (F s) s (hrankF s le_rfl) (chernF s) 2 α
        + (r.choose 2 : ℤ) • firstChernCapSum C p n N hfacN 1
            (chernClassCapExt C p n (F s) s (hrankF s le_rfl) (chernF s) 1 α)
        + ((r : ℤ) * s - 1) • firstChernCapSum C p n L hfacL 1
            (chernClassCapExt C p n (F s) s (hrankF s le_rfl) (chernF s) 1 α)
        + (s.choose 2 : ℤ) • firstChernCapSum C p n L hfacL 1
            (chernClassCapExt C p n (E r) r (hrankE r le_rfl) (chernE r) 1 α) := by
  rw [← firstChernCapSum_eq_chernClassCapExt_one C p n N hfacN F subF projF hzeroF hexactF
      hrankF chernF α hnormF hbinomF,
    ← firstChernCapSum_eq_chernClassCapExt_one C p n L hfacL E subE projE hzeroE hexactE
      hrankE chernE α hnormE hbinomE,
    chernClassCapExt_congr_module C p n hTop.symm (r * s) hrankTensor
      (hrankT (r * s) le_rfl) (chernT (r * s)) 2,
    chernClassCapExt_eq_esymRec C p n M hfacM T subT projT hzeroT hexactT hrankT chernT α
      hnormT hbinomT 2,
    chernClassCapExt_eq_esymRec C p n L hfacL E subE projE hzeroE hexactE hrankE chernE α
      hnormE hbinomE 2,
    chernClassCapExt_eq_esymRec C p n N hfacN F subF projF hzeroF hexactF hrankF chernF α
      hnormF hbinomF 2]
  simp only [esymRec_two]
  rw [esymRec_two_tensor_of_closure (firstChernShiftSeq C p n L hfacL)
      (firstChernShiftSeq C p n N hfacN) (firstChernShiftSeq C p n M hfacM)
      (firstChernShiftGenerators C p n L hfacL N hfacN)
      (firstChernShiftGenerators_comm C p n L hfacL N hfacN hcommLL hcommNN hcommLN)
      (fun i => Subring.subset_closure (Or.inl ⟨i, rfl⟩))
      (fun j => Subring.subset_closure (Or.inr ⟨j, rfl⟩))
      (firstChernShiftSeq_tensor_mem C p n L hfacL N hfacN M hfacM hquot)
      r s (firstChernShiftSeq_lexFamily C p n L hfacL N hfacN M hfacM hquot)]
  simp only [map_add, map_zsmul, pow_two]
  rw [evalChowGraded_two_mul_sum C p n _ N hfacN N hfacN,
    evalChowGraded_two_mul_sum C p n _ L hfacL N hfacN,
    evalChowGraded_two_mul_sum C p n _ L hfacL L hfacL, chowGradedUnit_apply_zero]

end Main

end Stacks.Chow

end
