module

public import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.TensorChernClasses
public import StacksCore.Tactic.StacksAttribute

/-!
# Power sums of Chern classes in a short exact sequence and in a tensor product

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, Stacks 02QL, let `X` be
locally of finite type over `S` and let `P_p` be the universal power-sum polynomial of
Stacks 0F9B. [Stacks, Tag 0F9C](https://stacks.math.columbia.edu/tag/0F9C) and
[Stacks, Tag 0F9D](https://stacks.math.columbia.edu/tag/0F9D) are, for finite locally free
`𝒪_X`-modules,

  `P_p(ℰ) = P_p(ℰ₁) + P_p(ℰ₂)`  for a short exact sequence `0 → ℰ₁ → ℰ → ℰ₂ → 0`,

  `P_p(ℰ₁ ⊗ ℰ₂) = ∑_{p₁ + p₂ = p} C(p, p₁) · P_{p₁}(ℰ₁) · P_{p₂}(ℰ₂)`,

in `A^p(X)`, whence `ch(ℰ) = ch(ℰ₁) + ch(ℰ₂)` and `ch(ℰ₁ ⊗ ℰ₂) = ch(ℰ₁) · ch(ℰ₂)` after dividing
by `p!`. Both are proved here **componentwise, as identities between cap products on Chow
groups**, in the vocabulary of
`StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.TensorChernClasses`, where Stacks 0FA6 is
proved: this development has no bivariant ring `A^*(X)` and no total Chern class — see the module
documentation of `StacksFrontier.AlgebraicGeometry.Chow.ChernWhitney.CapProductRelation` — so every
identity of this section of chapter 42 is read degree by degree against a fixed cycle `α`.

## How a power sum can be a cap product at all

`P_p` is a polynomial in the Chern classes, so the identities involve products of Chern classes,
and there is no ring in which such a product is a class. The device is the one Stacks 0FA6 uses
for `c₁(ℱ)²`: a product of classes is read as a **composite of operations** on Chow groups.
`Stacks.Chow.firstChernShift` makes `c₁(ℒ) ∩ -` an endomorphism of the graded product
`Stacks.Chow.ChowGradedProduct` of all the `A_{n-i}(X)`, so composites are products in the ring
`AddMonoid.End`, and `Stacks.Chow.chernClassCapExt_eq_esymRec` identifies the `k`-th elementary
symmetric function of the shifts of the quotients of a filtration with `c_k ∩ -` of its top,
which is Stacks 02UJ. In that ring the `p`-th power sum of the shifts is
`Stacks.Chow.powerSumShift`, and `Stacks.Chow.powerSumCap` evaluates it on the class of `α` in
degree `p`: this is `P_p(c_1(ℰ), …, c_p(ℰ)) ∩ α ∈ A_{n-p}(X)`. In degree one it is `c₁(ℰ) ∩ α`
on the nose, `Stacks.Chow.powerSumCap_one_eq_chernClassCapExt`, because `P_1 = c_1`.

## The proof, and what is carried

The source argues as in Stacks 0FA5 and Stacks 0FA6: choose `π : P ⟶ X` as in Stacks 02UL, use
injectivity of `π^*` to reduce to modules carrying filtrations with invertible successive
quotients, and compute with `x_i = c₁(ℒ_i)`. Everything after that reduction is proved here, in
full and in every degree `p ≥ 0`:

* for a short exact sequence the quotients of the filtration of `ℰ` are those of `ℰ₁` followed by
  those of `ℰ₂`, and `∑_{k < r + s} x_k^p = ∑_{i < r} x_i^p + ∑_{j < s} y_j^p`
  (`Stacks.Chow.powerSumRec_append`). No commutativity is used, as for the degree-one identity of
  Stacks 0FA6;
* for a tensor product the quotients are the lexicographic family `ℒ_i ⊗ 𝒩_j`, whose shifts are
  the sums `x_i + y_j` by Stacks 02SP, and
  `∑_{i,j} (x_i + y_j)^p = ∑_{p₁ + p₂ = p} C(p, p₁) (∑_i x_i^{p₁})(∑_j y_j^{p₂})`
  (`Stacks.Chow.powerSumRec_lexFamily`) by the binomial theorem for commuting elements followed
  by Fubini. Only `Commute (x_i, y_j)` is used, which is Stacks 02TJ across the two families,
  carried as `hcommLN` exactly as the degree-two identity of Stacks 0FA6 carries it.

The reduction is carried, in the shape Stacks 0FA6 carries it: the filtrations as the towers of
short exact sequences that Stacks 02UJ consumes, together with the identification of the
quotients — `hsub` and `hquot` for a short exact sequence, `hquot` for a tensor product, the
latter being the source's lexicographic `ℳ_{i·s+j} ≅ ℒ_i ⊗ 𝒩_j`. It cannot be performed in this
repository for the two independent reasons recorded in the Stacks 0FA5 clause of
`StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.DualChernClasses`: the filtration
delivered by `Stacks.Chow.exists_splittingMorphism` is an inductive `Prop`, from which the tower
of modules Stacks 02UJ needs cannot be eliminated, and no form of the compatibility of the Chern
class cap product with flat pullback is stated here, so injectivity of `π^*` has nothing to
descend.

## Consistency with Stacks 0FA6

In degree one the tensor identity reads `P_1(ℰ₁ ⊗ ℰ₂) = s·P_1(ℰ₁) + r·P_1(ℰ₂)`, since `P_0` is
the rank; as `P_1 = c_1` this is the first displayed identity of Stacks 0FA6,
`Stacks.Chow.chernClassCapExt_tensorObj_one`. In degree zero both identities read `r = r₁ + r₂`
and `r₁ · r₂ = r₁ · r₂`.

## Main definitions

* `Stacks.Chow.powerSumRec` — the `p`-th power sum of the first `m` members of a sequence in a
  ring, the companion of `Stacks.Chow.esymRec`.
* `Stacks.Chow.powerSumShift` — `P_p` of the first Chern class cap operations of the quotients of
  a filtration, in the operator ring.
* `Stacks.Chow.powerSumCap` — `P_p(c_1(ℰ), …, c_p(ℰ)) ∩ α ∈ A_{n-p}(X)`.

## Main results

* `Stacks.Chow.powerSumRec_append`, `Stacks.Chow.powerSumRec_lexFamily` — the formal computations
  the source omits, in every degree and for every pair of ranks.
* `Stacks.Chow.powerSumCap_one_eq_chernClassCapExt` — `P_1(ℰ) ∩ α = c₁(ℰ) ∩ α`, by Stacks 02UJ.
* `Stacks.Chow.powerSumCap_append`, `Stacks.Chow.chernClassCapExt_one_append` — **Stacks 0F9C**,
  in every degree and in degree one on the nose.
* `Stacks.Chow.powerSumShift_lexFamily`, `Stacks.Chow.powerSumCap_lexFamily` — **Stacks 0F9D**,
  in the operator ring and as cap products.

## References

* [Stacks Project, Tag 0F9C](https://stacks.math.columbia.edu/tag/0F9C)
* [Stacks Project, Tag 0F9D](https://stacks.math.columbia.edu/tag/0F9D)
* [Stacks Project, Tag 0F9B](https://stacks.math.columbia.edu/tag/0F9B)
* [Stacks Project, Tag 0FA6](https://stacks.math.columbia.edu/tag/0FA6)
* [Stacks Project, Tag 0FA5](https://stacks.math.columbia.edu/tag/0FA5)
* [Stacks Project, Tag 02UJ](https://stacks.math.columbia.edu/tag/02UJ)
* [Stacks Project, Tag 02UL](https://stacks.math.columbia.edu/tag/02UL)
* [Stacks Project, Tag 02TJ](https://stacks.math.columbia.edu/tag/02TJ)
* [Stacks Project, Tag 02SP](https://stacks.math.columbia.edu/tag/02SP)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Finset

universe u

namespace Stacks.Chow

/-! ### Power sums of a sequence in a ring -/

section Algebra

variable {R : Type*} [Ring R]

/-- The `p`-th power sum `w_0^p + ⋯ + w_{m-1}^p` of the first `m` members of a sequence, the
companion of `Stacks.Chow.esymRec`. -/
def powerSumRec (w : ℕ → R) (m p : ℕ) : R := ∑ k ∈ range m, w k ^ p

/-- The degree-zero power sum is the length of the family, which is the rank of the bundle it
comes from. -/
theorem powerSumRec_zero (w : ℕ → R) (m : ℕ) : powerSumRec w m 0 = (m : R) := by
  simp [powerSumRec]

/-- The degree-one power sum is the sum, which is the degree-one elementary symmetric
function. -/
theorem powerSumRec_one (w : ℕ → R) (m : ℕ) : powerSumRec w m 1 = ∑ k ∈ range m, w k := by
  simp [powerSumRec]

/-- **The formal computation the proof of Stacks 0F9C omits.** If the first `r` members of `w`
are the members of `x` and the next `s` are the members of `y`, then the `p`-th power sum of `w`
over all `r + s` of them is the sum of those of `x` and of `y`. No commutativity is used. -/
theorem powerSumRec_append (x y w : ℕ → R) (r s p : ℕ)
    (hx : ∀ i, i < r → w i = x i) (hy : ∀ j, j < s → w (r + j) = y j) :
    powerSumRec w (r + s) p = powerSumRec x r p + powerSumRec y s p := by
  simp only [powerSumRec, Finset.sum_range_add]
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun i hi => ?_)
    (Finset.sum_congr rfl fun j hj => ?_)
  · rw [hx i (Finset.mem_range.mp hi)]
  · rw [hy j (Finset.mem_range.mp hj)]

/-- A sum over `range (m * s)` is the sum of its `m` blocks of length `s`. -/
theorem sum_range_mul_eq_sum_blocks (v : ℕ → R) (s : ℕ) :
    ∀ m : ℕ, (∑ k ∈ range (m * s), v k) = ∑ i ∈ range m, ∑ j ∈ range s, v (i * s + j) := by
  intro m
  induction m with
  | zero => simp
  | succ m ih => rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]

/-- **The formal computation the proof of Stacks 0F9D omits.** If the lexicographic family
`w_{i·s+j}` is the sum `x_i + y_j`, and each `x_i` commutes with each `y_j`, then the `p`-th power
sum of `w` over all `r · s` of its members is the binomial convolution

  `∑_{p₁ + p₂ = p} C(p, p₁) · (∑_i x_i^{p₁}) · (∑_j y_j^{p₂})`.

The binomial theorem for commuting elements expands each `(x_i + y_j)^p`, and summing over `i`
and `j` separates the two factors of every term. Only the commutation of an `x_i` with a `y_j` is
used; the members of one family need not commute among themselves. -/
theorem powerSumRec_lexFamily (x y w : ℕ → R) (r s p : ℕ)
    (hcomm : ∀ i j : ℕ, Commute (x i) (y j))
    (hw : ∀ i, i < r → ∀ j, j < s → w (i * s + j) = x i + y j) :
    powerSumRec w (r * s) p
      = ∑ q ∈ Finset.antidiagonal p,
          p.choose q.1 • (powerSumRec x r q.1 * powerSumRec y s q.2) := by
  classical
  have hblock : ∀ i ∈ range r, (∑ j ∈ range s, w (i * s + j) ^ p)
      = ∑ q ∈ Finset.antidiagonal p,
          ∑ j ∈ range s, p.choose q.1 • (x i ^ q.1 * y j ^ q.2) := by
    intro i hi
    rw [← Finset.sum_comm]
    exact Finset.sum_congr rfl fun j hj => by
      rw [hw i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj), (hcomm i j).add_pow']
  rw [powerSumRec, sum_range_mul_eq_sum_blocks (fun k => w k ^ p) s r,
    Finset.sum_congr rfl hblock, Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [powerSumRec, powerSumRec, Finset.sum_mul, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum, Finset.smul_sum]

end Algebra

/-! ### The power sums of the first Chern class cap operations of a filtration -/

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (n : ℤ)

section Shifts

variable {r : ℕ} (L : Fin r → X.Modules)
  [∀ j, AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property (L j)]
  (hfac : ∀ j, InvertibleChernCapDescends C p (L j))

/-- **`P_p` of the Chern classes of a bundle presented by a filtration with invertible
quotients, in the operator ring**: the `p`-th power sum of the first Chern class cap operations of
the quotients. By Stacks 02UJ the `k`-th elementary symmetric function of those operations is
`c_k ∩ -` of the bundle, so this is the universal power-sum polynomial of Stacks 0F9B evaluated
at its Chern classes, the products of classes appearing as composites of operations. -/
def powerSumShift (k : ℕ) : AddMonoid.End (ChowGradedProduct C p n) :=
  powerSumRec (firstChernShiftSeq C p n L hfac) r k

/-- **`P_k(c_1(ℰ), …, c_k(ℰ)) ∩ α ∈ A_{n-k}(X)`** for a bundle presented by a filtration with
invertible quotients: the degree-`k` component of the value of `Stacks.Chow.powerSumShift` on the
graded unit of `α`. -/
def powerSumCap (k : ℕ) (α : chowGroup C p n) : chowGroup C p (n - (k : ℤ)) :=
  evalChowGraded C p n α k (powerSumShift C p n L hfac k)

/-- In degree one the power-sum operator is the degree-one elementary symmetric function of the
shift operators, since `P_1 = c_1`. -/
theorem powerSumShift_one :
    powerSumShift C p n L hfac 1 = esymRec (firstChernShiftSeq C p n L hfac) r 1 := by
  rw [powerSumShift, powerSumRec_one, esymRec_one]

end Shifts

/-! ### Stacks 02UJ in degree one: the power sum of degree one is the first Chern class -/

section Tower

variable {r : ℕ} (L : Fin r → X.Modules)
  [∀ j, AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property (L j)]
  (hfac : ∀ j, InvertibleChernCapDescends C p (L j))

/-- **`P_1(ℰ) ∩ α = c₁(ℰ) ∩ α`.** For a tower `Q` of length `r` with invertible successive
quotients `L`, the degree-one power-sum cap product of its top is the first Chern class cap
product of its top. This is Stacks 02UJ in degree one together with `P_1 = c_1`
(`AlgebraicGeometry.coe_powerSumPolynomial_one`), and it is what makes
`Stacks.Chow.powerSumCap` a statement about the module and not only about the filtration.

The hypotheses are exactly those of `Stacks.Chow.chernClassCapExt_eq_esymRec`, which see for why
each is carried. -/
theorem powerSumCap_one_eq_chernClassCapExt (Q : ℕ → X.Modules)
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
    powerSumCap C p n L hfac 1 (QuotientAddGroup.mk' (rationalEquivalences C p n) α)
      = chernClassCapExt C p n (Q r) r (hrank r le_rfl) (chern r) 1 α := by
  rw [chernClassCapExt_eq_esymRec C p n L hfac Q sub proj hzero hexact hrank chern α hnorm
    hbinom 1, powerSumCap, powerSumShift_one]

end Tower

/-! ### Stacks 0F9C -/

section ShortExact

variable {r s : ℕ} (L : Fin r → X.Modules)
  [∀ j, AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property (L j)]
  (hfacL : ∀ j, InvertibleChernCapDescends C p (L j))
  (N : Fin s → X.Modules)
  [∀ j, AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property (N j)]
  (hfacN : ∀ j, InvertibleChernCapDescends C p (N j))
  (M : Fin (r + s) → X.Modules)
  [∀ j, AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property (M j)]
  (hfacM : ∀ j, InvertibleChernCapDescends C p (M j))

/-- The shift operator of a member of a filtration depends only on its isomorphism class. -/
private theorem firstChernShiftSeq_eq_of_iso {a : ℕ} (K : Fin a → X.Modules)
    [∀ j, AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property (K j)]
    (hfacK : ∀ j, InvertibleChernCapDescends C p (K j)) (i : Fin a) (k : Fin (r + s))
    (e : M k ≅ K i) :
    firstChernShiftSeq C p n M hfacM k = firstChernShiftSeq C p n K hfacK i := by
  rw [firstChernShiftSeq_of_lt C p n M hfacM k k.2, firstChernShiftSeq_of_lt C p n K hfacK i i.2]
  exact firstChernShift_congr C p n _ _ e (hfacM _) (hfacK _)

/-- The first `r` shift operators of the filtration of `ℰ` are those of the filtration of
`ℰ₁`. -/
theorem firstChernShiftSeq_append_left
    (hsub : ∀ i : Fin r, M (Fin.castAdd s i) ≅ L i) (i : ℕ) (hi : i < r) :
    firstChernShiftSeq C p n M hfacM i = firstChernShiftSeq C p n L hfacL i :=
  firstChernShiftSeq_eq_of_iso C p n M hfacM L hfacL ⟨i, hi⟩ _ (hsub ⟨i, hi⟩)

/-- The last `s` shift operators of the filtration of `ℰ` are those of the filtration of
`ℰ₂`. -/
theorem firstChernShiftSeq_append_right
    (hquot : ∀ j : Fin s, M (Fin.natAdd r j) ≅ N j) (j : ℕ) (hj : j < s) :
    firstChernShiftSeq C p n M hfacM (r + j) = firstChernShiftSeq C p n N hfacN j :=
  firstChernShiftSeq_eq_of_iso C p n M hfacM N hfacN ⟨j, hj⟩ _ (hquot ⟨j, hj⟩)

/-- **Stacks 0F9C in the operator ring.** If the quotients of the filtration of `ℰ` are those of
the filtration of `ℰ₁` followed by those of the filtration of `ℰ₂`, then the power-sum operators
add, in every degree. -/
theorem powerSumShift_append (hsub : ∀ i : Fin r, M (Fin.castAdd s i) ≅ L i)
    (hquot : ∀ j : Fin s, M (Fin.natAdd r j) ≅ N j) (k : ℕ) :
    powerSumShift C p n M hfacM k
      = powerSumShift C p n L hfacL k + powerSumShift C p n N hfacN k :=
  powerSumRec_append _ _ _ r s k
    (firstChernShiftSeq_append_left C p n L hfacL M hfacM hsub)
    (firstChernShiftSeq_append_right C p n N hfacN M hfacM hquot)

/-- **Stacks 0F9C, componentwise on cap products.** Let `0 → ℰ₁ → ℰ → ℰ₂ → 0` be a short exact
sequence of finite locally free `𝒪_X`-modules, `ℰ₁` of rank `r` with a filtration whose
successive quotients are the invertible modules `ℒ_i = L i`, `ℰ₂` of rank `s` with quotients
`𝒩_j = N j`, and `ℰ` of rank `r + s` with the filtration obtained by juxtaposing them, whose
quotients `ℳ_k` are the `ℒ_i` followed by the `𝒩_j`. Then for every `n`-cycle `α` and every
`p ≥ 0`

  `P_p(ℰ) ∩ α = P_p(ℰ₁) ∩ α + P_p(ℰ₂) ∩ α`

in `A_{n-p}(X)`, which is the identity `P_p(ℰ) = P_p(ℰ₁) + P_p(ℰ₂)` of the source read against
`α`, and `ch(ℰ) = ch(ℰ₁) + ch(ℰ₂)` after dividing by `p!`. In degree one it is
`c₁(ℰ) ∩ α = c₁(ℰ₁) ∩ α + c₁(ℰ₂) ∩ α`, which is
`Stacks.Chow.chernClassCapExt_one_append`; in degree zero it is `r + s = r + s`. -/
@[stacks 0F9C "componentwise on cap products, and conditional.  CORRECTION OF FORM: the source \
states P_p(E) = P_p(E_1) + P_p(E_2) in A^p(X) for a short exact sequence 0 -> E_1 -> E -> E_2 -> \
0 of finite locally free O_X-modules, and ch(E) = ch(E_1) + ch(E_2) after dividing by p!.  There \
is no bivariant ring here, so the identity is read degree by degree against a fixed cycle: for \
every n, every alpha in CycleGroup C p n and every p >= 0, P_p(E) cap alpha = P_p(E_1) cap alpha \
+ P_p(E_2) cap alpha in A_{n-p}(X), each product of Chern classes being a COMPOSITE of \
operations on Chow groups, as Stacks 0FA6 reads c_1(F)^2.  The module documentation gives both \
reasons.  The division by p! is omitted only because it is a scalar.  CARRIED: the three \
filtrations with invertible quotients L_i, N_j, M_k, Stacks 02TI for each quotient (hfacL, \
hfacN, hfacM), and hsub, hquot identifying the M_k with the L_i followed by the N_j -- the \
source's reduction of the short exact sequence, which it gets from Stacks 02UL and the \
injectivity of pi^* and which cannot be performed here.  The Stacks 02UJ data needed to read the \
operator as P_p of the Chern classes of the module itself is carried not here but by \
Stacks.Chow.powerSumCap_one_eq_chernClassCapExt and Stacks.Chow.chernClassCapExt_one_append.  \
PROVED HERE: the formal computation the source omits, in every degree and for every pair of \
ranks, as Stacks.Chow.powerSumRec_append; no commutativity is used, so Stacks 02TJ is not \
carried"]
theorem powerSumCap_append (hsub : ∀ i : Fin r, M (Fin.castAdd s i) ≅ L i)
    (hquot : ∀ j : Fin s, M (Fin.natAdd r j) ≅ N j) (k : ℕ) (α : chowGroup C p n) :
    powerSumCap C p n M hfacM k α
      = powerSumCap C p n L hfacL k α + powerSumCap C p n N hfacN k α := by
  rw [powerSumCap, powerSumCap, powerSumCap,
    powerSumShift_append C p n L hfacL N hfacN M hfacM hsub hquot k, map_add]

/-- **Stacks 0F9C in degree one, entirely in Chern class cap products.** In the situation of
`Stacks.Chow.powerSumCap_append`, with `ℰ₁ = Q₁ r`, `ℰ₂ = Q₂ s` and `ℰ = Q (r + s)` the tops of
the three filtrations, for every `n`-cycle `α`

  `c₁(ℰ) ∩ α = c₁(ℰ₁) ∩ α + c₁(ℰ₂) ∩ α`

in `A_{n-1}(X)`. This is the degree-one case of Stacks 0F9C, `P_1` being `c_1`, with no
power-sum operator left in the statement: the three terms are the Chern class cap products of
Stacks 02U5 on the three modules themselves.

Each of the three sides is rewritten into its power-sum form by
`Stacks.Chow.powerSumCap_one_eq_chernClassCapExt`, which is Stacks 02UJ in degree one, and the
identity is then `Stacks.Chow.powerSumCap_append` in degree one. -/
@[stacks 0F9C "the degree-one case, entirely in Chern class cap products, and conditional.  P_1 \
being c_1 (AlgebraicGeometry.coe_powerSumPolynomial_one), the identity P_p(E) = P_p(E_1) + \
P_p(E_2) reads c_1(E) cap alpha = c_1(E_1) cap alpha + c_1(E_2) cap alpha in A_{n-1}(X), for \
every n and every alpha in CycleGroup C p n, where E_1, E, E_2 are the tops of the three \
filtrations and the three terms are the cap products of Stacks 02U5 on those modules themselves. \
 Read degree by degree for the reason given on Stacks.Chow.powerSumCap_append, of which this is \
the degree-one case and whose reduction it carries: the three filtrations as the towers Stacks \
02UJ consumes, with hsub and hquot.  ALSO CARRIED, each an input of Stacks 02UJ itself: chernE, \
chern1, chern2, the Stacks 02U0 component data; hnormE, hnorm1, hnorm2, the Stacks 02U0 \
normalisation c_0 = 1 along each tower; hbinomE, hbinom1, hbinom2, the equality of binomial \
transforms that Stacks 02UD gives once Stacks 02UG is applied; and hfacL, hfacN, hfacM, Stacks \
02TI for c_1 of each quotient.  Stacks 02TJ is NOT carried: the degree-one computation needs no \
commutativity"]
theorem chernClassCapExt_one_append (hsub : ∀ i : Fin r, M (Fin.castAdd s i) ≅ L i)
    (hquot : ∀ j : Fin s, M (Fin.natAdd r j) ≅ N j)
    (QE : ℕ → X.Modules) (subE : ∀ k : Fin (r + s), M k ⟶ QE ((k : ℕ) + 1))
    (projE : ∀ k : Fin (r + s), QE ((k : ℕ) + 1) ⟶ QE (k : ℕ))
    (hzeroE : ∀ k : Fin (r + s), subE k ≫ projE k = 0)
    (hexactE : ∀ k : Fin (r + s), (ShortComplex.mk (subE k) (projE k) (hzeroE k)).ShortExact)
    (hrankE : ∀ m : ℕ, m ≤ r + s → PullbackPreservesRank (QE m) m)
    (chernE : ∀ m : ℕ, ChernClassCycleRule C m)
    (Q₁ : ℕ → X.Modules) (sub₁ : ∀ i : Fin r, L i ⟶ Q₁ ((i : ℕ) + 1))
    (proj₁ : ∀ i : Fin r, Q₁ ((i : ℕ) + 1) ⟶ Q₁ (i : ℕ))
    (hzero₁ : ∀ i : Fin r, sub₁ i ≫ proj₁ i = 0)
    (hexact₁ : ∀ i : Fin r, (ShortComplex.mk (sub₁ i) (proj₁ i) (hzero₁ i)).ShortExact)
    (hrank₁ : ∀ m : ℕ, m ≤ r → PullbackPreservesRank (Q₁ m) m)
    (chern₁ : ∀ m : ℕ, ChernClassCycleRule C m)
    (Q₂ : ℕ → X.Modules) (sub₂ : ∀ j : Fin s, N j ⟶ Q₂ ((j : ℕ) + 1))
    (proj₂ : ∀ j : Fin s, Q₂ ((j : ℕ) + 1) ⟶ Q₂ (j : ℕ))
    (hzero₂ : ∀ j : Fin s, sub₂ j ≫ proj₂ j = 0)
    (hexact₂ : ∀ j : Fin s, (ShortComplex.mk (sub₂ j) (proj₂ j) (hzero₂ j)).ShortExact)
    (hrank₂ : ∀ m : ℕ, m ≤ s → PullbackPreservesRank (Q₂ m) m)
    (chern₂ : ∀ m : ℕ, ChernClassCycleRule C m) (α : CycleGroup C p n)
    (hnormE : ∀ (m : ℕ) (hm : m ≤ r + s),
      chernClassCapExt C p n (QE m) m (hrankE m hm) (chernE m) 0 α =
        cycleClassDegreeZero C p n α)
    (hbinomE : ∀ k : Fin (r + s), ∀ i ≤ (k : ℕ) + 1,
      binomialTransform (inverseFirstChernCapStep C p n (M k) (hfacM k)) ((k : ℕ) + 1)
          (chernCapFamily C p n (QE ((k : ℕ) + 1)) ((k : ℕ) + 1) (hrankE ((k : ℕ) + 1) k.isLt)
            (chernE ((k : ℕ) + 1)) α) i =
        binomialTransform (inverseFirstChernCapStep C p n (M k) (hfacM k)) (k : ℕ)
          (chernCapFamily C p n (QE (k : ℕ)) (k : ℕ) (hrankE (k : ℕ) k.isLt.le)
            (chernE (k : ℕ)) α) i)
    (hnorm₁ : ∀ (m : ℕ) (hm : m ≤ r),
      chernClassCapExt C p n (Q₁ m) m (hrank₁ m hm) (chern₁ m) 0 α =
        cycleClassDegreeZero C p n α)
    (hbinom₁ : ∀ i : Fin r, ∀ t ≤ (i : ℕ) + 1,
      binomialTransform (inverseFirstChernCapStep C p n (L i) (hfacL i)) ((i : ℕ) + 1)
          (chernCapFamily C p n (Q₁ ((i : ℕ) + 1)) ((i : ℕ) + 1) (hrank₁ ((i : ℕ) + 1) i.isLt)
            (chern₁ ((i : ℕ) + 1)) α) t =
        binomialTransform (inverseFirstChernCapStep C p n (L i) (hfacL i)) (i : ℕ)
          (chernCapFamily C p n (Q₁ (i : ℕ)) (i : ℕ) (hrank₁ (i : ℕ) i.isLt.le)
            (chern₁ (i : ℕ)) α) t)
    (hnorm₂ : ∀ (m : ℕ) (hm : m ≤ s),
      chernClassCapExt C p n (Q₂ m) m (hrank₂ m hm) (chern₂ m) 0 α =
        cycleClassDegreeZero C p n α)
    (hbinom₂ : ∀ j : Fin s, ∀ t ≤ (j : ℕ) + 1,
      binomialTransform (inverseFirstChernCapStep C p n (N j) (hfacN j)) ((j : ℕ) + 1)
          (chernCapFamily C p n (Q₂ ((j : ℕ) + 1)) ((j : ℕ) + 1) (hrank₂ ((j : ℕ) + 1) j.isLt)
            (chern₂ ((j : ℕ) + 1)) α) t =
        binomialTransform (inverseFirstChernCapStep C p n (N j) (hfacN j)) (j : ℕ)
          (chernCapFamily C p n (Q₂ (j : ℕ)) (j : ℕ) (hrank₂ (j : ℕ) j.isLt.le)
            (chern₂ (j : ℕ)) α) t) :
    chernClassCapExt C p n (QE (r + s)) (r + s) (hrankE (r + s) le_rfl) (chernE (r + s)) 1 α
      = chernClassCapExt C p n (Q₁ r) r (hrank₁ r le_rfl) (chern₁ r) 1 α
        + chernClassCapExt C p n (Q₂ s) s (hrank₂ s le_rfl) (chern₂ s) 1 α := by
  rw [← powerSumCap_one_eq_chernClassCapExt C p n M hfacM QE subE projE hzeroE hexactE hrankE
      chernE α hnormE hbinomE,
    ← powerSumCap_one_eq_chernClassCapExt C p n L hfacL Q₁ sub₁ proj₁ hzero₁ hexact₁ hrank₁
      chern₁ α hnorm₁ hbinom₁,
    ← powerSumCap_one_eq_chernClassCapExt C p n N hfacN Q₂ sub₂ proj₂ hzero₂ hexact₂ hrank₂
      chern₂ α hnorm₂ hbinom₂]
  exact powerSumCap_append C p n L hfacL N hfacN M hfacM hsub hquot 1 _

end ShortExact

/-! ### Stacks 0F9D -/

section Tensor

variable {r s : ℕ} (L : Fin r → X.Modules)
  [∀ j, AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property (L j)]
  (hfacL : ∀ j, InvertibleChernCapDescends C p (L j))
  (N : Fin s → X.Modules)
  [∀ j, AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property (N j)]
  (hfacN : ∀ j, InvertibleChernCapDescends C p (N j))
  (M : Fin (r * s) → X.Modules)
  [∀ j, AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property (M j)]
  (hfacM : ∀ j, InvertibleChernCapDescends C p (M j))

/-- **Stacks 0F9D in the operator ring.** If the `(i·s+j)`-th quotient of the filtration of
`ℰ₁ ⊗ ℰ₂` is `ℒ_i ⊗ 𝒩_j` — the source's lexicographic filtration — and Stacks 02TJ holds across
the two families of quotients, then the power-sum operator of the tensor product is the binomial
convolution of those of the factors, in every degree. -/
theorem powerSumShift_lexFamily
    (hquot : ∀ (i : Fin r) (j : Fin s),
      M (finLexIndex i j) ≅ Scheme.Modules.tensorObj (L i) (N j))
    (hcommLN : ∀ (a : Fin r) (b : Fin s),
      FirstChernCapStepsCommute C p n (L a) (N b) (hfacL a) (hfacN b)) (k : ℕ) :
    powerSumShift C p n M hfacM k
      = ∑ q ∈ Finset.antidiagonal k,
          k.choose q.1 • (powerSumShift C p n L hfacL q.1 * powerSumShift C p n N hfacN q.2) :=
  powerSumRec_lexFamily _ _ _ r s k
    (commute_firstChernShiftSeq C p n L hfacL N hfacN hcommLN)
    (firstChernShiftSeq_lexFamily C p n L hfacL N hfacN M hfacM hquot)

/-- **Stacks 0F9D, componentwise on cap products.** Let `ℰ₁` be finite locally free of rank `r`
with a filtration whose successive quotients are the invertible modules `ℒ_i = L i`, let `ℰ₂` be
finite locally free of rank `s` with quotients `𝒩_j = N j`, and let the filtration of
`ℰ₁ ⊗_{𝒪_X} ℰ₂` be the lexicographic one of the source, of length `r·s`, whose `(i·s+j)`-th
quotient is `ℒ_i ⊗ 𝒩_j`. Then for every `n`-cycle `α` and every `p ≥ 0`

  `P_p(ℰ₁ ⊗ ℰ₂) ∩ α = ∑_{p₁ + p₂ = p} C(p, p₁) · (P_{p₁}(ℰ₁) ∘ P_{p₂}(ℰ₂)) ∩ α`

in `A_{n-p}(X)`, which is the identity
`P_p(ℰ₁ ⊗ ℰ₂) = ∑_{p₁+p₂=p} C(p,p₁) P_{p₁}(ℰ₁) P_{p₂}(ℰ₂)` of the source read against `α`, and
`ch(ℰ₁ ⊗ ℰ₂) = ch(ℰ₁) · ch(ℰ₂)` after dividing by `p!`, the binomial coefficients being what
`p! = p₁! · p₂! · C(p, p₁)` absorbs. Each product `P_{p₁}(ℰ₁) · P_{p₂}(ℰ₂)` is a composite of
operations on Chow groups, as `c₁(ℱ)²` is in Stacks 0FA6. In degree one, `P_0` being the rank,
the identity is `s·(c₁(ℰ₁) ∩ α) + r·(c₁(ℰ₂) ∩ α)`, the first displayed identity of
Stacks 0FA6. -/
@[stacks 0F9D "componentwise on cap products, and conditional.  CORRECTION OF FORM: the source \
states P_p(E_1 tensor E_2) = sum over p_1 + p_2 = p of C(p, p_1) P_{p_1}(E_1) P_{p_2}(E_2) in \
A^p(X), and ch(E_1 tensor E_2) = ch(E_1) ch(E_2) after dividing by p!.  There is no bivariant \
ring here, so the identity is read degree by degree against a fixed cycle, in A_{n-p}(X) for \
every n, every alpha in CycleGroup C p n and every p >= 0; every product of classes -- \
P_{p_1}(E_1) P_{p_2}(E_2) and the products inside each P_p -- is a COMPOSITE of operations on \
Chow groups, as Stacks 0FA6 reads c_1(F)^2.  The module documentation gives both reasons.  The \
division by p! is omitted only because it is a scalar.  CARRIED: the three filtrations with \
invertible quotients, Stacks 02TI for each quotient (hfacL, hfacN, hfacM), and hquot, the \
source's lexicographic identification M_{i*s+j} iso L_i tensor N_j, which the source gets from \
Stacks 02UL and the injectivity of pi^* and which cannot be performed here; and Stacks 02TJ as \
hcommLN, genuinely needed because the binomial theorem applies to x_i + y_j only when those \
commute -- the members of one family need NOT commute among themselves, so hcommLL and hcommNN \
are not carried.  Reading the operator as P_p of the Chern classes of the module itself uses the \
Stacks 02UJ data, carried by Stacks.Chow.powerSumCap_one_eq_chernClassCapExt.  PROVED HERE: the \
formal computation the source omits, in every degree and for every pair of ranks, as \
Stacks.Chow.powerSumRec_lexFamily"]
theorem powerSumCap_lexFamily
    (hquot : ∀ (i : Fin r) (j : Fin s),
      M (finLexIndex i j) ≅ Scheme.Modules.tensorObj (L i) (N j))
    (hcommLN : ∀ (a : Fin r) (b : Fin s),
      FirstChernCapStepsCommute C p n (L a) (N b) (hfacL a) (hfacN b))
    (k : ℕ) (α : chowGroup C p n) :
    powerSumCap C p n M hfacM k α
      = ∑ q ∈ Finset.antidiagonal k, k.choose q.1 •
          evalChowGraded C p n α k
            (powerSumShift C p n L hfacL q.1 * powerSumShift C p n N hfacN q.2) := by
  rw [powerSumCap, powerSumShift_lexFamily C p n L hfacL N hfacN M hfacM hquot hcommLN k,
    map_sum]
  exact Finset.sum_congr rfl fun q _ => map_nsmul _ _ _

end Tensor

end Stacks.Chow

end
