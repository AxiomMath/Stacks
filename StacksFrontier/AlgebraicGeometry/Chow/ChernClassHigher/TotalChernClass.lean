module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.Basic
public import Mathlib.Algebra.DirectSum.Basic

/-!
# The total Chern class as a nonhomogeneous bivariant class

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be a scheme
locally of finite type over `S` and let `ℰ` be a finite locally free `O_X`-module of rank `r`.
Stacks 0B7H produces the Chern classes `c_j(ℰ) ∈ A^j(X)` for `0 ≤ j ≤ r`, each a bivariant class
of degree `j` for `𝟙 X`, and the *total Chern class* is their formal sum

  `c(ℰ) = c_0(ℰ) + c_1(ℰ) + … + c_r(ℰ)`,

read as a nonhomogeneous bivariant class on `X`, that is, as an element of the graded group
`A^*(X ⟶ X) = ⊕_p A^p(X ⟶ X)`.

This file constructs that formal sum. The sum of a finite family of homogeneous classes is
`Stacks.Chow.bivariantFormalSum`, defined for an arbitrary morphism and recording which
homogeneous class sits in which degree, and `Stacks.Chow.IsTotalChernClass` is the assertion that
a nonhomogeneous class on `X` is the total Chern class of a module: its degree-`j` component is
the `j`-th bivariant Chern class for `0 ≤ j ≤ r`, and it has no other component. The two fit
together: the formal sum of a family of bivariant Chern classes is a total Chern class, and the
total Chern class is unique.

## Main definitions

* `Stacks.Chow.nonhomogeneousBivariantGroup` — the graded group `⊕_p A^p(X ⟶ Y)`, whose elements
  are the nonhomogeneous bivariant classes of globally bounded degree.
* `Stacks.Chow.bivariantFormalSum` — the formal sum `c_0 + c_1 + … + c_r` of a family of
  bivariant classes with `c_j` of degree `j`.
* `Stacks.Chow.IsTotalChernClass` — the assertion that a nonhomogeneous bivariant class on `X` is
  the total Chern class of a finite locally free module of rank `r`.

## Main results

* `Stacks.Chow.bivariantFormalSum_apply_coe`, `Stacks.Chow.bivariantFormalSum_apply_eq_zero` —
  the components of the formal sum: `c_j` in degree `j` for `0 ≤ j ≤ r`, and `0` in every other
  degree.
* `Stacks.Chow.bivariantFormalSum_injective` — the formal sum determines the family, so no
  information is lost in passing to the nonhomogeneous class.
* `Stacks.Chow.isTotalChernClass_bivariantFormalSum` — the formal sum of a family of bivariant
  Chern classes of a module is a total Chern class of it.
* `Stacks.Chow.eq_of_isTotalChernClass` — **uniqueness of the total Chern class**: two
  nonhomogeneous classes that are both the total Chern class of the same module are equal.
* `Stacks.Chow.IsTotalChernClass.cap_eq` — the cap operation of each component of the total Chern
  class is forced: in degree `j` it is `Stacks.Chow.chernClassBivariantCap`.

## Implementation notes

### The graded group, and the completed group of Stacks 0FE0

The total Chern class of a module of rank `r` has components only in degrees `0, …, r`, a bound
that is uniform over `X`, so it already lies in the direct sum `⊕_p A^p(X ⟶ X)` and the
completion of Stacks 0FE0 — the product over the connected components of `X` of the graded groups
of the restricted morphisms, which requires the degree bound only on each component separately —
is not needed to hold it. Accordingly the group used here is the direct sum, with the same
`DirectSum ℤ` spelling that `Stacks.Chow.completedBivariantGroup` uses on each component.

### The individual Chern classes are a parameter

The construction of the Chern class operations on Chow groups, Stacks 0B7G, is not in this
repository; it enters `StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.Basic` as the
parameter `Stacks.Chow.HigherChernCapRule`, and everything below carries that parameter too.
The bivariant class Stacks 0B7H produces is
`Stacks.Chow.chernClassBivariant` of
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.BivariantClass`, which in addition to that
parameter carries the three naturality axioms of Stacks 0B76 for it; none of those is needed
below, where all that is used of a summand is that it satisfies the characterization
`Stacks.Chow.IsChernClassBivariant`. So the homogeneous classes summed below are a quantified
family together with that hypothesis. Under it the formal sum is the total Chern class, and
uniqueness is unconditional.

### No `@[stacks 0FE1]`

A formal sum of classes supplied as a parameter is not the definition of Stacks 0FE1, whose
summands are the classes constructed by Stacks 0B7H
(`Stacks.Chow.GenuineChern.chernClassBivariantClass`), so no `@[stacks]` attribute is placed in
this file.

## References

* [Stacks Project, Tag 0FE1](https://stacks.math.columbia.edu/tag/0FE1)
* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
* [Stacks Project, Tag 0B7H](https://stacks.math.columbia.edu/tag/0B7H)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### Nonhomogeneous bivariant classes -/

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Y : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y)
  [LocallyOfFiniteType f] (hf : f ≫ sY = sX)

/-- The graded group `A^*(X ⟶ Y) = ⊕_p A^p(X ⟶ Y)` of bivariant classes for `f : X ⟶ Y`, the
elements of which are the nonhomogeneous bivariant classes of globally bounded degree. -/
abbrev nonhomogeneousBivariantGroup : Type (u + 1) :=
  DirectSum ℤ fun p ↦ BivariantClass C G sX sY f hf p

variable (r : ℕ)

/-- The formal sum `c_0 + c_1 + … + c_r` of a family of bivariant classes for `f : X ⟶ Y` with
`c_j` of degree `j`, as a nonhomogeneous bivariant class. -/
def bivariantFormalSum (c : ∀ j : Fin (r + 1), BivariantClass C G sX sY f hf (j : ℤ)) :
    nonhomogeneousBivariantGroup C G sX sY f hf :=
  ∑ j : Fin (r + 1), DirectSum.of _ (j : ℤ) (c j)

/-- The degree-`j` component of the formal sum is `c_j`, for `0 ≤ j ≤ r`. -/
theorem bivariantFormalSum_apply_coe
    (c : ∀ j : Fin (r + 1), BivariantClass C G sX sY f hf (j : ℤ)) (j : Fin (r + 1)) :
    bivariantFormalSum C G sX sY f hf r c (j : ℤ) = c j := by
  rw [bivariantFormalSum, DirectSum.sum_apply, Finset.sum_eq_single j]
  · exact DirectSum.of_eq_same (i := (j : ℤ)) (c j)
  · intro b _ hb
    refine DirectSum.of_eq_of_ne _ _ _ ?_
    have hne : (j : ℕ) ≠ (b : ℕ) := fun h ↦ hb (Fin.val_injective h.symm)
    exact_mod_cast hne
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- The formal sum has no component in a degree outside `0, …, r`. -/
theorem bivariantFormalSum_apply_eq_zero
    (c : ∀ j : Fin (r + 1), BivariantClass C G sX sY f hf (j : ℤ)) (p : ℤ)
    (hp : p < 0 ∨ (r : ℤ) < p) : bivariantFormalSum C G sX sY f hf r c p = 0 := by
  rw [bivariantFormalSum, DirectSum.sum_apply, Finset.sum_eq_zero]
  intro b _
  refine DirectSum.of_eq_of_ne _ _ _ ?_
  have hb : (b : ℕ) ≤ r := Nat.lt_succ_iff.mp b.isLt
  omega

/-- The formal sum determines the family of homogeneous classes it is built from. -/
theorem bivariantFormalSum_injective :
    Function.Injective
      (bivariantFormalSum C G sX sY f hf r :
        (∀ j : Fin (r + 1), BivariantClass C G sX sY f hf (j : ℤ)) →
          nonhomogeneousBivariantGroup C G sX sY f hf) := by
  intro c d h
  funext j
  exact ((bivariantFormalSum_apply_coe C G sX sY f hf r c j).symm.trans
    (congrFun (congrArg DFunLike.coe h) (j : ℤ))).trans
      (bivariantFormalSum_apply_coe C G sX sY f hf r d j)

/-! ### The total Chern class -/

variable (F : X.Modules)

/-- **Stacks 0FE1.** The assertion that a nonhomogeneous bivariant class on `X` is the total
Chern class `c(F) = c_0(F) + … + c_r(F)` of a finite locally free module `F` of rank `r`: its
degree-`j` component is the `j`-th bivariant Chern class of `F` for `0 ≤ j ≤ r`, and it has no
component in any other degree. -/
def IsTotalChernClass (cap : HigherChernCapRule C r) (hrank : PullbackPreservesRank F r)
    (t : nonhomogeneousBivariantGroup C G sX sX (𝟙 X) (Category.id_comp sX)) : Prop :=
  (∀ j : Fin (r + 1), IsChernClassBivariant C sX F r G cap hrank j (t (j : ℤ))) ∧
    ∀ p : ℤ, p < 0 ∨ (r : ℤ) < p → t p = 0

/-- The formal sum of a family of bivariant Chern classes of `F` is a total Chern class of `F`. -/
theorem isTotalChernClass_bivariantFormalSum (cap : HigherChernCapRule C r)
    (hrank : PullbackPreservesRank F r)
    (c : ∀ j : Fin (r + 1), BivariantClass C G sX sX (𝟙 X) (Category.id_comp sX) (j : ℤ))
    (hc : ∀ j : Fin (r + 1), IsChernClassBivariant C sX F r G cap hrank j (c j)) :
    IsTotalChernClass C G sX r F cap hrank
      (bivariantFormalSum C G sX sX (𝟙 X) (Category.id_comp sX) r c) := by
  refine ⟨fun j ↦ ?_, fun p hp ↦
    bivariantFormalSum_apply_eq_zero C G sX sX (𝟙 X) (Category.id_comp sX) r c p hp⟩
  have h := bivariantFormalSum_apply_coe C G sX sX (𝟙 X) (Category.id_comp sX) r c j
  rw [h]
  exact @hc j

/-- **Uniqueness of the total Chern class.** Two nonhomogeneous bivariant classes that are both
the total Chern class of the same finite locally free module of rank `r` are equal. -/
theorem eq_of_isTotalChernClass (cap : HigherChernCapRule C r)
    (hrank : PullbackPreservesRank F r)
    {t t' : nonhomogeneousBivariantGroup C G sX sX (𝟙 X) (Category.id_comp sX)}
    (ht : IsTotalChernClass C G sX r F cap hrank t)
    (ht' : IsTotalChernClass C G sX r F cap hrank t') : t = t' := by
  refine DFunLike.ext _ _ fun p ↦ ?_
  by_cases hp : 0 ≤ p ∧ p ≤ (r : ℤ)
  · obtain ⟨j, hj⟩ : ∃ j : Fin (r + 1), (j : ℤ) = p :=
      ⟨⟨p.toNat, by omega⟩, by change ((p.toNat : ℕ) : ℤ) = p; omega⟩
    subst hj
    exact eq_of_isChernClassBivariant C sX F r G cap hrank j (ht.1 j) (ht'.1 j)
  · have hout : p < 0 ∨ (r : ℤ) < p := by omega
    exact (ht.2 p hout).trans (ht'.2 p hout).symm

/-- The cap operation of each component of the total Chern class is forced: in degree `j` it is
intersection with `c_j` on the test scheme, pushed forward to the chosen pullback. -/
theorem IsTotalChernClass.cap_eq {cap : HigherChernCapRule C r}
    {hrank : PullbackPreservesRank F r}
    {t : nonhomogeneousBivariantGroup C G sX sX (𝟙 X) (Category.id_comp sX)}
    (ht : IsTotalChernClass C G sX r F cap hrank t) (j : Fin (r + 1)) {T : Scheme.{u}}
    (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ) :
    (t (j : ℤ)).cap g k = chernClassBivariantCap C sX F r cap hrank j g k :=
  (isChernClassBivariant_iff C sX F r G cap hrank j (t (j : ℤ))).1 (ht.1 j) g k

end Stacks.Chow

end
