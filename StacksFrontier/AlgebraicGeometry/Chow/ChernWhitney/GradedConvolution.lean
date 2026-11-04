module

public import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.Group.Equiv.TypeTags

/-!
# Convolution of graded families of cap operators

Let `G : ℤ → Type*` be a family of abelian groups — the Chow groups `A_k(X)` of a fixed scheme
are the case of interest — and let a *graded cap family* on `G` be a rule

  `a : ∀ (k : ℤ) (i : ℕ), G k ⟶ G (k - i)`

assigning to each degree `k` and each index `i` an additive map lowering the degree by `i`.
Intersection with the Chern classes `c_i(ℰ)` of a finite locally free module, extended by zero
above the rank, is such a family. The *convolution* of two graded cap families is

  `(a ∗ b)_k^m = ∑_{i + j = m} a_{k-j}^{i} ∘ b_k^{j}`,

the coefficientwise product of the two formal series `∑_i a^i` and `∑_j b^j`.

This file is the algebra of the Whitney sum formula
[Stacks, Tag 02UI](https://stacks.math.columbia.edu/tag/02UI): that `c(ℰ) = c(ℰ₁) c(ℰ₂)` for a
short exact sequence `0 → ℰ₁ → ℰ → ℰ₂ → 0`, read coefficientwise, says exactly that the Chern
cap family of `ℰ` is the convolution of those of `ℰ₁` and `ℰ₂`. The source proves it by
induction on the rank of `ℰ₁`, and the two steps of that induction that are pure algebra are
proved here:

* **associativity**, which is what turns `c(π^*ℰ) = c(ℱ) c(𝒬) = c(ℱ) c(ℒ) c(π^*ℰ₂)` and
  `c(π^*ℰ₁) = c(ℱ) c(ℒ)` into `c(π^*ℰ) = c(π^*ℰ₁) c(π^*ℰ₂)`;
* **descent along an injective intertwiner**, which is what carries that identity from the
  projective bundle back down to the base.

## Why a family of groups rather than a graded ring

The classes `c_i(ℰ)` are not available as elements of a ring in this repository: the bivariant
groups carry no multiplication, and `Stacks.Chow.nonhomogeneousBivariantGroup` is a direct sum
with no product on it. What *is* available is the cap product, an operation on Chow groups
lowering the delta-dimension by the degree. So the Whitney relation has to be read as an
identity between composites of such operations, and the convolution above is the coefficientwise
product written in those terms. The same choice is made, at the level of one invertible
subsheaf, by `StacksFrontier.AlgebraicGeometry.Chow.ChernWhitney.BinomialInversion`.

## Implementation notes

### Degree transports are unavoidable, and are confined to `Stacks.Chow.capTo`

A summand `a_{k-j}^{m-j} ∘ b_k^j` lands in `G (k - j - (m - j))`, which equals `k - m` only
because `j ≤ m`, the subtraction `m - j` being truncated. The transport along that equality is
packaged once, in `Stacks.Chow.capTo`, which applies a family in one degree and transports the
result to a prescribed degree. Three lemmas then absorb every transport that arises:
`Stacks.Chow.capTo_capTo` composes two of them, `Stacks.Chow.capTo_congr_index` changes the
index along an equality of natural numbers, and `Stacks.Chow.degreeCast_capTo` absorbs an outer
transport. After those rewrites both sides of the associativity are sums of one and the same
expression, and only the reindexing of the sum remains.

### The summand is total in its index

`Stacks.Chow.convolveTerm` is defined for every index `j`, as zero when `j > m`, rather than on
`Fin (m + 1)`. Summation over `Finset.range (m + 1)` then needs no `Fin` coercion, and the
reindexing of the double sum in the associativity proof — from pairs `(j, l)` with `l ≤ j ≤ m`
to pairs `(l, i)` with `l + i ≤ m` — is a bijection of plain sigma types.

## Main definitions

* `Stacks.Chow.gradedDegreeCast` — transport of an element along an equality of degrees.
* `Stacks.Chow.GradedCapFamily` — a rule `G k ⟶ G (k - i)` for every degree `k` and index `i`.
* `Stacks.Chow.capTo` — a family applied in one degree, transported to a prescribed degree.
* `Stacks.Chow.convolveTerm` and `Stacks.Chow.convolve` — the summands of the convolution and
  the convolution itself.
* `Stacks.Chow.Intertwines` — that a degree-shifting map carries one graded cap family to
  another; for Chern classes this is the flat pullback compatibility of Stacks 02U8.

## Main results

* `Stacks.Chow.convolve_assoc` — the convolution is associative.
* `Stacks.Chow.Intertwines.convolve` — an intertwiner of two pairs of families intertwines their
  convolutions.
* `Stacks.Chow.eq_of_intertwines` — **descent**: an identity between two families carried by an
  injective intertwiner to an identity upstairs holds downstairs.
* `Stacks.Chow.eq_convolve_of_intertwines` — descent for the convolution identity: if an
  injective intertwiner carries three families to three families for which the convolution
  identity holds, the identity holds downstairs.

## References

* [Stacks Project, Tag 02UI](https://stacks.math.columbia.edu/tag/02UI)
* [Stacks Project, Tag 02UH](https://stacks.math.columbia.edu/tag/02UH)
* [Stacks Project, Tag 02U8](https://stacks.math.columbia.edu/tag/02U8)
-/

@[expose] public noncomputable section

open Finset

namespace Stacks.Chow

universe v

variable {G H : ℤ → Type v} [∀ k, AddCommGroup (G k)] [∀ k, AddCommGroup (H k)]

/-! ### Transport along an equality of degrees -/

/-- Transport of an element of a graded family of abelian groups along an equality of degrees,
as an additive equivalence. The degrees of two summands of a convolution agree as integers but
not as terms, so some such transport is unavoidable. -/
def gradedDegreeCast (G : ℤ → Type v) [∀ k, AddCommGroup (G k)] {k l : ℤ} (h : k = l) :
    G k ≃+ G l :=
  AddEquiv.cast (M := G) h

/-- Transport along `rfl` is the identity. -/
@[simp]
theorem gradedDegreeCast_rfl {k : ℤ} (x : G k) : gradedDegreeCast G rfl x = x := rfl

/-- Two successive transports compose into the transport along the composite equality. -/
@[simp]
theorem gradedDegreeCast_gradedDegreeCast {k l m : ℤ} (h : k = l) (h' : l = m) (x : G k) :
    gradedDegreeCast G h' (gradedDegreeCast G h x) = gradedDegreeCast G (h.trans h') x := by
  subst h; subst h'; rfl

/-- A degree-shifting additive map commutes with transport along an equality of degrees. -/
theorem map_gradedDegreeCast {d : ℤ} (pull : ∀ k : ℤ, G k →+ H (k + d)) {k l : ℤ} (h : k = l)
    (x : G k) :
    pull l (gradedDegreeCast G h x) =
      gradedDegreeCast H (show k + d = l + d by rw [h]) (pull k x) := by
  subst h; rfl

/-! ### Graded cap families -/

/-- A *graded cap family* on `G`: an additive map `G k ⟶ G (k - i)` for every degree `k` and
every index `i`. The Chern class cap products of a finite locally free module, extended by zero
above the rank, form such a family. -/
abbrev GradedCapFamily (G : ℤ → Type v) [∀ k, AddCommGroup (G k)] : Type v :=
  ∀ (k : ℤ) (i : ℕ), G k →+ G (k - (i : ℤ))

/-- The family `a` applied in degree `k` at index `i`, with the result transported to the
degree `n`. Every degree transport occurring in a convolution is of this shape. -/
def capTo (a : GradedCapFamily G) {k n : ℤ} (i : ℕ) (h : k - (i : ℤ) = n) (x : G k) : G n :=
  gradedDegreeCast G h (a k i x)

/-- `Stacks.Chow.capTo a i h x` is the transport along `h` of `a k i x`. -/
theorem capTo_def (a : GradedCapFamily G) {k n : ℤ} (i : ℕ) (h : k - (i : ℤ) = n) (x : G k) :
    capTo a i h x = gradedDegreeCast G h (a k i x) :=
  rfl

/-- Changing the index along an equality of natural numbers. -/
theorem capTo_congr_index (a : GradedCapFamily G) {k n : ℤ} {i i' : ℕ} (hi : i = i')
    (h : k - (i : ℤ) = n) (x : G k) :
    capTo a i h x = capTo a i' (by rw [← hi]; exact h) x := by
  subst hi; rfl

/-- Two successive applications compose into one, with the inner transport absorbed. -/
theorem capTo_capTo (a b : GradedCapFamily G) {k n n' : ℤ} (i j : ℕ) (h : k - (j : ℤ) = n)
    (h' : n - (i : ℤ) = n') (x : G k) :
    capTo a i h' (capTo b j h x) = capTo a i (by rw [← h] at h'; exact h') (b k j x) := by
  subst h; rfl

/-- An outer transport is absorbed. -/
theorem gradedDegreeCast_capTo (a : GradedCapFamily G) {k n n' : ℤ} (i : ℕ)
    (h : k - (i : ℤ) = n) (h' : n = n') (x : G k) :
    gradedDegreeCast G h' (capTo a i h x) = capTo a i (h.trans h') x := by
  subst h'; rfl

/-- `Stacks.Chow.capTo` commutes with finite sums. -/
theorem capTo_sum (a : GradedCapFamily G) {k n : ℤ} (i : ℕ) (h : k - (i : ℤ) = n)
    {ι : Type*} (s : Finset ι) (f : ι → G k) :
    capTo a i h (∑ t ∈ s, f t) = ∑ t ∈ s, capTo a i h (f t) := by
  simp only [capTo, map_sum]

/-! ### The convolution -/

/-- The `j`-th summand `a_{k-j}^{m-j} ∘ b_k^{j}` of the convolution of `a` and `b` in degree `k`
at total index `m`, and zero for `j > m`. Defining it at every index rather than on
`Fin (m + 1)` keeps the sums below free of coercions. -/
def convolveTerm (a b : GradedCapFamily G) (k : ℤ) (m j : ℕ) : G k →+ G (k - (m : ℤ)) :=
  if h : j ≤ m then
    (gradedDegreeCast G
          (show k - (j : ℤ) - ((m - j : ℕ) : ℤ) = k - (m : ℤ) by omega)).toAddMonoidHom.comp
      ((a (k - (j : ℤ)) (m - j)).comp (b k j))
  else 0

/-- For `j ≤ m`, the `j`-th summand of the convolution is `a^{m-j}` applied to `b^{j} x`,
transported to degree `k - m`. -/
theorem convolveTerm_of_le (a b : GradedCapFamily G) (k : ℤ) {m j : ℕ} (hj : j ≤ m) (x : G k) :
    convolveTerm a b k m j x =
      capTo a (m - j) (show k - (j : ℤ) - ((m - j : ℕ) : ℤ) = k - (m : ℤ) by omega) (b k j x) := by
  rw [convolveTerm, dite_eq_left hj]; rfl

/-- For `j > m`, the `j`-th summand of the convolution vanishes. -/
theorem convolveTerm_of_gt (a b : GradedCapFamily G) (k : ℤ) {m j : ℕ} (hj : ¬ j ≤ m)
    (x : G k) : convolveTerm a b k m j x = 0 := by
  rw [convolveTerm, dite_eq_right hj]; rfl

/-- The convolution `(a ∗ b)_k^m = ∑_{i + j = m} a_{k-j}^{i} ∘ b_k^{j}` of two graded cap
families, again a graded cap family. Read on the Chern class cap products of two finite locally
free modules, this is the coefficientwise product of their total Chern classes. -/
def convolve (a b : GradedCapFamily G) : GradedCapFamily G :=
  fun k m => ∑ j ∈ range (m + 1), convolveTerm a b k m j

/-- The convolution evaluated at `x` is the sum of its summands evaluated at `x`. -/
theorem convolve_apply (a b : GradedCapFamily G) (k : ℤ) (m : ℕ) (x : G k) :
    convolve a b k m x = ∑ j ∈ range (m + 1), convolveTerm a b k m j x :=
  AddMonoidHom.finsetSum_apply _ _ _

/-! ### Associativity -/

/-- The common shape of the summands of both iterated convolutions: `a` after `b` after `c`,
at the indices `m - (l + i)`, `i` and `l`, with the single transport that makes the composite
land in degree `k - m`. -/
private def tripleTerm (a b c : GradedCapFamily G) (k : ℤ) (m l i : ℕ) (x : G k) :
    G (k - (m : ℤ)) :=
  if h : l + i ≤ m then
    capTo a (m - (l + i))
      (show k - (l : ℤ) - (i : ℤ) - ((m - (l + i) : ℕ) : ℤ) = k - (m : ℤ) by omega)
      (b (k - (l : ℤ)) i (c k l x))
  else 0

/-- **The convolution is associative**, degreewise. Both sides are the sum of
`a^{m-l-i} ∘ b^{i} ∘ c^{l}` over the triples `l + i ≤ m`, the left-hand side grouped by
`l + i` and the right-hand side by `l`. -/
theorem convolve_assoc_apply (a b c : GradedCapFamily G) (k : ℤ) (m : ℕ) (x : G k) :
    convolve a (convolve b c) k m x = convolve (convolve a b) c k m x := by
  classical
  have hL : convolve a (convolve b c) k m x =
      ∑ j ∈ range (m + 1), ∑ l ∈ range (j + 1), tripleTerm a b c k m l (j - l) x := by
    rw [convolve_apply]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjm : j ≤ m := mem_range_succ_iff.mp hj
    rw [convolveTerm_of_le a (convolve b c) k hjm, convolve_apply, capTo_sum]
    refine Finset.sum_congr rfl fun l hl => ?_
    have hlj : l ≤ j := mem_range_succ_iff.mp hl
    rw [convolveTerm_of_le b c k hlj, capTo_capTo, tripleTerm,
      dite_eq_left (show l + (j - l) ≤ m by omega)]
    exact capTo_congr_index a (show m - j = m - (l + (j - l)) by omega) _ _
  have hR : convolve (convolve a b) c k m x =
      ∑ l ∈ range (m + 1), ∑ i ∈ range (m - l + 1), tripleTerm a b c k m l i x := by
    rw [convolve_apply]
    refine Finset.sum_congr rfl fun l hl => ?_
    have hlm : l ≤ m := mem_range_succ_iff.mp hl
    rw [convolveTerm_of_le (convolve a b) c k hlm, capTo_def, convolve_apply, map_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have him : i ≤ m - l := mem_range_succ_iff.mp hi
    rw [convolveTerm_of_le a b _ him, gradedDegreeCast_capTo, tripleTerm,
      dite_eq_left (show l + i ≤ m by omega)]
    exact capTo_congr_index a (show m - l - i = m - (l + i) by omega) _ _
  rw [hL, hR, Finset.sum_sigma' (range (m + 1)) (fun j => range (j + 1))
      (fun j l => tripleTerm a b c k m l (j - l) x),
    Finset.sum_sigma' (range (m + 1)) (fun l => range (m - l + 1))
      (fun l i => tripleTerm a b c k m l i x)]
  refine Finset.sum_nbij' (fun p => (⟨p.2, p.1 - p.2⟩ : (_ : ℕ) × ℕ))
    (fun p => (⟨p.1 + p.2, p.1⟩ : (_ : ℕ) × ℕ)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨j, l⟩ hp
    simp only [Finset.mem_sigma, mem_range] at hp ⊢
    omega
  · rintro ⟨l, i⟩ hp
    simp only [Finset.mem_sigma, mem_range] at hp ⊢
    omega
  · rintro ⟨j, l⟩ hp
    simp only [Finset.mem_sigma, mem_range] at hp
    have h : l + (j - l) = j := by omega
    simp [h]
  · rintro ⟨l, i⟩ _
    simp
  · rintro ⟨j, l⟩ _
    rfl

/-- **The convolution is associative.** -/
theorem convolve_assoc (a b c : GradedCapFamily G) :
    convolve a (convolve b c) = convolve (convolve a b) c := by
  funext k m
  exact AddMonoidHom.ext fun x => convolve_assoc_apply a b c k m x

/-! ### Intertwining and descent -/

/-- That the degree-shifting map `pull` carries the graded cap family `a` on `G` to the graded
cap family `a'` on `H`: `pull (a^i x) = (a')^i (pull x)`, up to the transport comparing
`k + d - i` with `k - i + d`.

For the Chern class cap products this is
[Stacks, Tag 02U8](https://stacks.math.columbia.edu/tag/02U8), the compatibility of flat
pullback with the cap products, read for a module and its pullback. -/
def Intertwines {d : ℤ} (pull : ∀ k : ℤ, G k →+ H (k + d)) (a : GradedCapFamily G)
    (a' : GradedCapFamily H) : Prop :=
  ∀ (k : ℤ) (i : ℕ) (x : G k),
    pull (k - (i : ℤ)) (a k i x) =
      gradedDegreeCast H (show k + d - (i : ℤ) = k - (i : ℤ) + d by omega)
        (a' (k + d) i (pull k x))

/-- An intertwiner carries `Stacks.Chow.capTo` of one family to `Stacks.Chow.capTo` of the
other. -/
theorem Intertwines.capTo {d : ℤ} {pull : ∀ k : ℤ, G k →+ H (k + d)} {a : GradedCapFamily G}
    {a' : GradedCapFamily H} (ha : Intertwines pull a a') {k n : ℤ} (i : ℕ)
    (h : k - (i : ℤ) = n) (x : G k) :
    pull n (Stacks.Chow.capTo a i h x) =
      Stacks.Chow.capTo a' i (show k + d - (i : ℤ) = n + d by omega) (pull k x) := by
  rw [capTo_def, map_gradedDegreeCast, ha k i x, gradedDegreeCast_gradedDegreeCast, capTo_def]

/-- **An intertwiner of two pairs of families intertwines their convolutions.** -/
theorem Intertwines.convolve {d : ℤ} {pull : ∀ k : ℤ, G k →+ H (k + d)}
    {a b : GradedCapFamily G} {a' b' : GradedCapFamily H} (ha : Intertwines pull a a')
    (hb : Intertwines pull b b') :
    Intertwines pull (Stacks.Chow.convolve a b) (Stacks.Chow.convolve a' b') := by
  intro k m x
  rw [convolve_apply, map_sum, convolve_apply, map_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjm : j ≤ m := mem_range_succ_iff.mp hj
  rw [convolveTerm_of_le a b k hjm, ha.capTo (m - j) _ (b k j x),
    show b k j x = Stacks.Chow.capTo b j rfl x from rfl, hb.capTo j rfl x, capTo_capTo,
    convolveTerm_of_le a' b' (k + d) hjm, gradedDegreeCast_capTo]

/-- **Descent of an identity along an injective intertwiner.** If `pull` is injective in every
degree and carries `a` to `a'` and `b` to `b'`, then `a' = b'` upstairs forces `a = b`
downstairs.

This is the shape in which the splitting principle is used: an identity between graded cap
families is checked on the `P` of [Stacks, Tag 02UL](https://stacks.math.columbia.edu/tag/02UL),
where the modules acquire filtrations with invertible successive quotients, and carried down
because flat pullback along `π` is injective. -/
theorem eq_of_intertwines {d : ℤ} (pull : ∀ k : ℤ, G k →+ H (k + d))
    (hinj : ∀ k : ℤ, Function.Injective (pull k)) {a b : GradedCapFamily G}
    {a' b' : GradedCapFamily H} (ha : Intertwines pull a a') (hb : Intertwines pull b b')
    (h : a' = b') : a = b := by
  funext k m
  refine AddMonoidHom.ext fun x => hinj (k - (m : ℤ)) ?_
  rw [ha k m x, hb k m x, h]

/-- **Descent along an injective intertwiner.** If `pull` is injective in every degree and
carries `a`, `b`, `c` to `a'`, `b'`, `c'`, and `c'` is the convolution of `a'` and `b'`, then
`c` is the convolution of `a` and `b`.

This is the last step of the induction proving the Whitney sum formula: the relation is checked
on the projective bundle, where it follows from the rank-one case, and then carried down because
flat pullback along the projection is injective. -/
theorem eq_convolve_of_intertwines {d : ℤ} (pull : ∀ k : ℤ, G k →+ H (k + d))
    (hinj : ∀ k : ℤ, Function.Injective (pull k)) {a b c : GradedCapFamily G}
    {a' b' c' : GradedCapFamily H} (ha : Intertwines pull a a') (hb : Intertwines pull b b')
    (hc : Intertwines pull c c') (h : c' = convolve a' b') : c = convolve a b :=
  eq_of_intertwines pull hinj hc (ha.convolve hb) h

end Stacks.Chow

end
