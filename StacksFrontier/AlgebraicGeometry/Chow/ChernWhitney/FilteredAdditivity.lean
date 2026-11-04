module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernWhitney.CapProductRelation
public import StacksCore.Tactic.StacksAttribute

/-!
# Chern classes of a filtration with invertible quotients, componentwise on Chow groups

Let `X` be a scheme locally of finite type over the base scheme `S` of chapter 42, let
`ℒ_1, …, ℒ_r` be invertible `𝒪_X`-modules and let `ℰ` be finite locally free of rank `r` with a
filtration `0 = ℰ_0 ⊂ ℰ_1 ⊂ … ⊂ ℰ_r = ℰ` whose successive quotients are
`ℰ_i/ℰ_{i-1} ≅ ℒ_i`. Writing `x_i = c₁(ℒ_i)`,
[Stacks, Tag 02UJ](https://stacks.math.columbia.edu/tag/02UJ) is the product formula
`c(ℰ) = ∏_{i=1}^r (1 + x_i)`. This file states and proves that formula **componentwise, as an
identity between cap products on Chow groups**: for every `n`, every `n`-cycle `α` and every
`k ≥ 1`,

  `c_k(ℰ) ∩ α = e_k(x_1, …, x_r) ∩ ⟦α⟧`,

with `e_k` the `k`-th elementary symmetric function of the operations `x_i ∩ -`.

## Why componentwise, and not as a product of total classes

The product form cannot be written in this repository, for the reason recorded at Stacks 02UH in
`StacksFrontier.AlgebraicGeometry.Chow.ChernWhitney.CapProductRelation`: there is no ring structure
on bivariant classes and no total Chern class here, because Chern classes are built as operations
`CycleGroup C p k ⟶ chowGroup C p (k - j)` on the cycles of `X` itself (Stacks 02U5) rather than
as bivariant classes over all `Y ⟶ X`, and the source's formulation needs proper pushforward on
Chow groups (Stacks 0GU8), which this repository does not have.

Expanding `∏_i (1 + x_i)` by degree is exactly what the product means: its degree-`k` coefficient
is the `k`-th elementary symmetric function of the `x_i`. So the identity above is the product
formula read coefficientwise, and nothing is lost. It is also the shape the source proof
produces, since the source proves 02UJ by iterating 02UH, which this repository carries only
componentwise.

Degree `0` of the product reads `1 = 1`. In this repository that is the statement
`c_0(ℰ) ∩ α = ⟦α⟧`, which is the normalisation clause of Stacks 02U0: an arbitrary
`Stacks.Chow.ChernClassCycleRule` pins nothing at `j = 0`. The assertion below is therefore made
in degrees `k ≥ 1`, which hold the whole content of the tag. Degrees `k > r` are included and say
`0 = 0` on both sides.

The normalisation is needed only at the **bottom** of the tower, for the rank-zero module `Q_0`.
In degree zero a binomial transform is its own zeroth entry, so the degree-zero clause of
`hbinom` already says that the degree-zero cap products of consecutive members of the tower
agree; the normalisation for `Q_m`, and in particular for `ℰ = Q_r`, follows from the one for
`Q_0` by induction along the tower. So no normalisation statement about `ℰ` itself is an input.

## The filtration, as the tower the one-step relation consumes

`Stacks.Chow.chernClassCapExt_succ_eq_add_firstChernCap` (Stacks 02UH) applies to a short exact
sequence whose **sub**module is invertible. The filtration of the source gives such sequences
through its quotients: with `Q_m = ℰ/ℰ_{r-m}`, which is finite locally free of rank `m`, one has
`Q_r = ℰ` and short exact sequences

  `0 ⟶ ℒ_{r-m} ⟶ Q_{m+1} ⟶ Q_m ⟶ 0`.

The hypothesis below is that tower: a family `Q : ℕ → X.Modules` of ranks `m ≤ r`, invertible
modules `L : Fin r → X.Modules` and morphisms `sub`, `proj` forming a short exact sequence at
every stage. The invertible modules occurring are the successive quotients of the filtration, so
the elementary symmetric function of their first Chern classes is the one in the source; the
enumeration runs from the top of the filtration down, which is immaterial since an elementary
symmetric function is symmetric. Quotients of modules are not constructed in this repository, so
the tower, rather than the chain of submodules, is the available form of the hypothesis.

## The inputs of the iteration

Each stage of the iteration takes the inputs Stacks 02UH takes, and for the same reasons:

* `hbinom`, at every stage: the equality of the binomial transform at `m + 1` with the one at `m`
  that Stacks 02UD gives for the twists of `Q_{m+1}` and `Q_m` by the inverse of the invertible
  subsheaf, once Stacks 02UG has identified the Chern classes of the two twisted sheaves. Neither
  Stacks 02UD nor Stacks 02UG is proved in this repository.
* `chern`, the component data of Stacks 02U0 in every rank, which `Stacks.Chow.chernClassCap`
  takes as an explicit argument because Stacks 02U0 and the projective bundle formula beneath it
  are not in this repository.
* `hfac`, Stacks 02TI for the first Chern class of each quotient, which
  `Stacks.Chow.firstChernClassCapOnChow` takes as an explicit argument.
* `hnorm`, the normalisation `c_0 = 1` of Stacks 02U0 at the rank-zero bottom `Q_0` of the
  tower, as explained above. The inductive form
  `Stacks.Chow.chernClassCapExt_eq_elemSymmChernCap_of_tower` consumes the normalisation at every
  stage, and Stacks 02UJ below produces those stages from the one at `Q_0`.

## Main definitions

* `Stacks.Chow.cycleClassDegreeZero` — the cycle class map of Stacks 02RW, read in the degree a
  degree-zero cap product lands in.
* `Stacks.Chow.elemSymmChernCap` — the `k`-th elementary symmetric function of the first Chern
  class cap operations of `L 0, …, L (m-1)`, as a map `A_n(X) ⟶ A_{n-k}(X)`.

## Main results

* `Stacks.Chow.chernClassCapExt_eq_elemSymmChernCap` — **Stacks 02UJ**, componentwise.

## References

* [Stacks Project, Tag 02UJ](https://stacks.math.columbia.edu/tag/02UJ)
* [Stacks Project, Tag 02UH](https://stacks.math.columbia.edu/tag/02UH)
* [Stacks Project, Tag 02UG](https://stacks.math.columbia.edu/tag/02UG)
* [Stacks Project, Tag 02UD](https://stacks.math.columbia.edu/tag/02UD)
* [Stacks Project, Tag 02U5](https://stacks.math.columbia.edu/tag/02U5)
* [Stacks Project, Tag 02U0](https://stacks.math.columbia.edu/tag/02U0)
* [Stacks Project, Tag 02TI](https://stacks.math.columbia.edu/tag/02TI)
* [Stacks Project, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

/-! ### The cycle class map in the degree a degree-zero cap product lands in -/

/-- The class of an `n`-cycle in `A_{n-0}(X)`: the cycle class map of Stacks 02RW followed by the
reindexing of the degree `n` as `n - 0`, which is the degree a cap product with the zeroth Chern
class lands in. -/
def cycleClassDegreeZero (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S)
    [LocallyOfFiniteType p] (n : ℤ) : CycleGroup C p n →+ chowGroup C p (n - ((0 : ℕ) : ℤ)) :=
  (chowGroupDegreeCast C p (by simp)
      (AddMonoidHom.id (chowGroup C p (n - ((0 : ℕ) : ℤ))))).comp
    (QuotientAddGroup.mk' (rationalEquivalences C p n))

/-! ### Elementary symmetric functions of first Chern class cap operations -/

/-- **The `k`-th elementary symmetric function of the first Chern class cap operations of
`L 0, …, L (m-1)`**, as a homomorphism `A_n(X) ⟶ A_{n-k}(X)`.

Writing `x_j` for the operation `c₁(L j) ∩ -` of `Stacks.Chow.firstChernCapStep`, this is

  `e_k(x_0, …, x_{m-1}) = ∑_{T ⊆ {0, …, m-1}, |T| = k} ∏_{j ∈ T} x_j`,

defined by the Pascal recursion `e_k(x_0, …, x_m) = e_k(x_0, …, x_{m-1}) + x_m e_{k-1}(x_0, …,
x_{m-1})` that characterises the elementary symmetric functions, with `e_0` the identity and
`e_{k}` zero for `k > m`. The composite in a term `∏_{j ∈ T} x_j` is taken in decreasing order of
`j`, a choice of order the source does not have to make because its classes lie in a commutative
ring; that the order is immaterial is the commutativity of Stacks 02TJ, which
`StacksFrontier.AlgebraicGeometry.Chow.ChernCapCommutativity` carries only together with an
identity on integral components, and nothing below needs it.

The recursion is on the number `m` of operations, with the degree `k` a parameter, so that each
summand is visibly a map into `A_{n-k}(X)` and no transport along a degree identity appears. -/
def elemSymmChernCap (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S)
    [LocallyOfFiniteType p] (n : ℤ) {r : ℕ} (L : Fin r → X.Modules)
    [∀ j, AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property (L j)]
    (hfac : ∀ j, InvertibleChernCapDescends C p (L j)) :
    ∀ (m : ℕ), m ≤ r → ∀ (k : ℕ), chowGroup C p n →+ chowGroup C p (n - (k : ℤ))
  | 0, _, 0 =>
      chowGroupDegreeCast C p (by simp) (AddMonoidHom.id (chowGroup C p (n - ((0 : ℕ) : ℤ))))
  | 0, _, _ + 1 => 0
  | _ + 1, _, 0 =>
      chowGroupDegreeCast C p (by simp) (AddMonoidHom.id (chowGroup C p (n - ((0 : ℕ) : ℤ))))
  | m + 1, hm, k + 1 =>
      elemSymmChernCap C p n L hfac m (Nat.le_of_succ_le hm) (k + 1) +
        (firstChernCapStep C p n (L ⟨m, hm⟩) (hfac ⟨m, hm⟩) k).comp
          (elemSymmChernCap C p n L hfac m (Nat.le_of_succ_le hm) k)

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (n : ℤ)
  {r : ℕ} (L : Fin r → X.Modules)
  [∀ j, AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property (L j)]
  (hfac : ∀ j, InvertibleChernCapDescends C p (L j))

/-- In degree zero the elementary symmetric cap operation sends the class of a cycle to itself:
`e_0 = 1`. -/
theorem elemSymmChernCap_degree_zero_apply (m : ℕ) (hm : m ≤ r) (α : CycleGroup C p n) :
    elemSymmChernCap C p n L hfac m hm 0
        (QuotientAddGroup.mk' (rationalEquivalences C p n) α) =
      cycleClassDegreeZero C p n α := by
  cases m <;> rfl

/-- With no operations there is no elementary symmetric function in positive degree. -/
theorem elemSymmChernCap_zero_succ (hm : 0 ≤ r) (k : ℕ) :
    elemSymmChernCap C p n L hfac 0 hm (k + 1) = 0 :=
  rfl

/-- **The Pascal recursion.** Adjoining the operation `x_m` adds to `e_{k+1}` the term
`x_m e_k`. -/
theorem elemSymmChernCap_succ (m : ℕ) (hm : m + 1 ≤ r) (k : ℕ) :
    elemSymmChernCap C p n L hfac (m + 1) hm (k + 1) =
      elemSymmChernCap C p n L hfac m (Nat.le_of_succ_le hm) (k + 1) +
        (firstChernCapStep C p n (L ⟨m, hm⟩) (hfac ⟨m, hm⟩) k).comp
          (elemSymmChernCap C p n L hfac m (Nat.le_of_succ_le hm) k) :=
  rfl

/-- An elementary symmetric function of degree larger than the number of operations vanishes. -/
theorem elemSymmChernCap_of_lt :
    ∀ (m : ℕ) (hm : m ≤ r) (k : ℕ), m < k → elemSymmChernCap C p n L hfac m hm k = 0 := by
  intro m
  induction m with
  | zero =>
      intro hm k hk
      obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
      exact elemSymmChernCap_zero_succ C p n L hfac hm i
  | succ m ih =>
      intro hm k hk
      obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
      rw [elemSymmChernCap_succ, ih (Nat.le_of_succ_le hm) (i + 1) (by omega),
        ih (Nat.le_of_succ_le hm) i (by omega), AddMonoidHom.comp_zero, add_zero]

/-! ### The product formula, componentwise -/

/-- **The iteration of Stacks 02UH along the tower.** Every member of the tower satisfies the
formula, in every degree: for `m ≤ r` and every `k`,

  `c_k(Q_m) ∩ α = e_k(x_0, …, x_{m-1}) ∩ ⟦α⟧`.

In degree `k = 0` this is the hypothesis `hnorm` itself, the normalisation `c_0 = 1` of Stacks
02U0; the content is in the positive degrees, where it is the `m`-fold iteration of
`Stacks.Chow.chernClassCapExt_succ_eq_add_firstChernCap`. -/
theorem chernClassCapExt_eq_elemSymmChernCap_of_tower (Q : ℕ → X.Modules)
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
    ∀ (m : ℕ) (hm : m ≤ r) (k : ℕ),
      chernClassCapExt C p n (Q m) m (hrank m hm) (chern m) k α =
        elemSymmChernCap C p n L hfac m hm k
          (QuotientAddGroup.mk' (rationalEquivalences C p n) α) := by
  have hbase : ∀ (m : ℕ) (hm : m ≤ r) (k : ℕ), k = 0 ∨ m < k →
      chernClassCapExt C p n (Q m) m (hrank m hm) (chern m) k α =
        elemSymmChernCap C p n L hfac m hm k
          (QuotientAddGroup.mk' (rationalEquivalences C p n) α) := by
    rintro m hm k (rfl | hk)
    · rw [hnorm m hm, elemSymmChernCap_degree_zero_apply]
    · rw [chernClassCapExt_of_gt C p n (Q m) m (hrank m hm) (chern m) k (not_le.2 hk),
        elemSymmChernCap_of_lt C p n L hfac m hm k hk]
      simp
  intro m
  induction m with
  | zero => intro hm k; exact hbase 0 hm k (by omega)
  | succ m ih =>
      intro hm k
      have hm' : m ≤ r := Nat.le_of_succ_le hm
      by_cases hk : k = 0 ∨ m + 1 < k
      · exact hbase _ hm k hk
      · obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
        rw [chernClassCapExt_succ_eq_add_firstChernCap C p n
          (ShortComplex.mk (sub ⟨m, hm⟩) (proj ⟨m, hm⟩) (hzero ⟨m, hm⟩)) (hexact ⟨m, hm⟩)
          m (hrank (m + 1) hm) (hrank m hm') (chern (m + 1)) (chern m) (hfac ⟨m, hm⟩)
          α i (by omega) (hbinom ⟨m, hm⟩), ih hm' (i + 1), ih hm' i, elemSymmChernCap_succ]
        rfl

/-- **Stacks 02UJ, componentwise on cap products.** Let `ℰ = Q_r` be finite locally free of rank
`r` with a filtration whose successive quotients are the invertible modules `L 0, …, L (r-1)`,
presented as the tower of short exact sequences `0 ⟶ L j ⟶ Q_{j+1} ⟶ Q_j ⟶ 0`. Then for every
`n`-cycle `α` and every `k ≥ 1`

  `c_k(ℰ) ∩ α = e_k(c₁(L 0), …, c₁(L (r-1))) ∩ ⟦α⟧`

in `A_{n-k}(X)`, the `k`-th elementary symmetric function of the first Chern class cap operations
of the quotients applied to the class of `α`. This is the coefficient of degree `k` in the
product formula `c(ℰ) = ∏_i (1 + c₁(ℒ_i))` of the source.

The normalisation `hnorm` is asked for only at the rank-zero bottom `Q_0` of the tower: in degree
zero a binomial transform is its own zeroth entry, so `hbinom` already identifies the degree-zero
cap products of consecutive members, and the normalisation at every stage — in particular at
`ℰ = Q_r` — follows by induction. See the module documentation for why the product itself cannot
be written here, for why the assertion is made in degrees `k ≥ 1`, and for the inputs `hbinom`,
`chern` and `hfac`. -/
@[stacks 02UJ "the degree-k coefficients of c(E) = prod (1 + c_1(L_i)), stated on the cap \
  products of 02U5 for k >= 1 rather than as a product in A^*(X), which has no multiplication \
  here; the filtration enters as the tower of its quotients; 02U0, 02TI, 02UD+02UG are inputs"]
theorem chernClassCapExt_eq_elemSymmChernCap (Q : ℕ → X.Modules)
    (sub : ∀ j : Fin r, L j ⟶ Q ((j : ℕ) + 1)) (proj : ∀ j : Fin r, Q ((j : ℕ) + 1) ⟶ Q (j : ℕ))
    (hzero : ∀ j : Fin r, sub j ≫ proj j = 0)
    (hexact : ∀ j : Fin r, (ShortComplex.mk (sub j) (proj j) (hzero j)).ShortExact)
    (hrank : ∀ m : ℕ, m ≤ r → PullbackPreservesRank (Q m) m)
    (chern : ∀ m : ℕ, ChernClassCycleRule C m) (α : CycleGroup C p n)
    (hnorm : chernClassCapExt C p n (Q 0) 0 (hrank 0 (Nat.zero_le r)) (chern 0) 0 α =
      cycleClassDegreeZero C p n α)
    (hbinom : ∀ j : Fin r, ∀ i ≤ (j : ℕ) + 1,
      binomialTransform (inverseFirstChernCapStep C p n (L j) (hfac j)) ((j : ℕ) + 1)
          (chernCapFamily C p n (Q ((j : ℕ) + 1)) ((j : ℕ) + 1) (hrank ((j : ℕ) + 1) j.isLt)
            (chern ((j : ℕ) + 1)) α) i =
        binomialTransform (inverseFirstChernCapStep C p n (L j) (hfac j)) (j : ℕ)
          (chernCapFamily C p n (Q (j : ℕ)) (j : ℕ) (hrank (j : ℕ) j.isLt.le)
            (chern (j : ℕ)) α) i)
    (k : ℕ) (_hk : 1 ≤ k) :
    chernClassCapExt C p n (Q r) r (hrank r le_rfl) (chern r) k α =
      elemSymmChernCap C p n L hfac r le_rfl k
        (QuotientAddGroup.mk' (rationalEquivalences C p n) α) := by
  have hstep : ∀ (m : ℕ) (hm : m + 1 ≤ r),
      chernClassCapExt C p n (Q (m + 1)) (m + 1) (hrank (m + 1) hm) (chern (m + 1)) 0 α =
        chernClassCapExt C p n (Q m) m (hrank m (Nat.le_of_succ_le hm)) (chern m) 0 α := by
    intro m hm
    have h := hbinom ⟨m, hm⟩ 0 (Nat.zero_le _)
    simpa only [binomialTransform_eq, zero_add, Finset.sum_range_one, Nat.sub_zero,
      Nat.choose_zero_right, one_nsmul, descentTower_diag, chernCapFamily] using h
  have hnorm' : ∀ (m : ℕ) (hm : m ≤ r),
      chernClassCapExt C p n (Q m) m (hrank m hm) (chern m) 0 α = cycleClassDegreeZero C p n α := by
    intro m
    induction m with
    | zero => intro _; exact hnorm
    | succ m ih => intro hm; exact (hstep m hm).trans (ih (Nat.le_of_succ_le hm))
  exact chernClassCapExt_eq_elemSymmChernCap_of_tower C p n L hfac Q sub proj hzero hexact hrank
    chern α hnorm' hbinom r le_rfl k

end Stacks.Chow

end
