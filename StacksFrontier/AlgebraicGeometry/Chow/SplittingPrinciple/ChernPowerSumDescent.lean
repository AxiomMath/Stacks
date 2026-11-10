module

public import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.ChernPowerSumElem
public import StacksCore.Tactic.StacksAttribute

/-!
# `P_p` of the Chern classes descends along a flat pullback

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, Stacks 02QL. For
`π : P ⟶ X` flat of relative dimension `d` over `S`, flat pullback on Chow groups
`π^* : A_k(X) ⟶ A_{k+d}(P)` carries the total Chern class of a finite locally free module to the
total Chern class of its pullback: that is
[Stacks, Tag 02U8](https://stacks.math.columbia.edu/tag/02U8),
`Stacks.Chow.GenuineChern.intertwines_chernFamily`, read as `Stacks.Chow.Intertwines`.

This file shows that the relation `Stacks.Chow.Intertwines pull` is **closed under the ring
operations and under taking homogeneous components**, hence that it carries
`Stacks.Chow.powerSumChernElem` — the value `P_p(c_1(ℱ), …, c_p(ℱ))` of the universal power-sum
polynomial of Stacks 0F9B — to the same expression for the pullback:

  `π^*(P_p(ℱ) ∩ α) = P_p(π^*ℱ) ∩ π^*α`.

Together with `Stacks.Chow.eq_of_intertwines` — injectivity of `π^*`, clause (1) of Stacks 02UL —
this is the descent step of the splitting principle: an identity between power sums of Chern
classes proved on the `P` where the modules are filtered by invertible modules holds on `X`.

## How a relation between elements of two rings can be a ring homomorphism

`Stacks.Chow.Intertwines pull a a'` is a relation, not a map: `a'` is only determined on the
image of `π^*`. What *is* available is that the set of pairs `(a, a')` it relates is a subring of
the product, `Stacks.Chow.intertwinedChernPairs`, and that this subring is commutative because
both factors are. So `AlgebraicGeometry.powerSumOfChernClasses` — which needs a commutative ring
— can be evaluated *on pairs*, and `AlgebraicGeometry.powerSumOfChernClasses_map` applied to the
two projections says that the two components of the result are the two power sums. The pair of
power sums is then intertwined by construction.

## Main definitions

* `Stacks.Chow.intertwinedChernPairs` — the subring of pairs of Chern-class expressions related
  by an intertwiner.

## Main results

* `Stacks.Chow.Intertwines.zero`, `Stacks.Chow.Intertwines.one`, `Stacks.Chow.Intertwines.add`,
  `Stacks.Chow.Intertwines.neg`, `Stacks.Chow.Intertwines.mul`,
  `Stacks.Chow.Intertwines.natCast`, `Stacks.Chow.Intertwines.sum`,
  `Stacks.Chow.Intertwines.homComponent` — the relation is closed under the ring operations, under
  finite sums and under taking homogeneous components.
* `Stacks.Chow.intertwines_powerSumChernElem` — **flat pullback carries `P_p` of the Chern
  classes of a module to `P_p` of the Chern classes of its pullback.**

## References

* [Stacks Project, Tag 02U8](https://stacks.math.columbia.edu/tag/02U8)
* [Stacks Project, Tag 02UL](https://stacks.math.columbia.edu/tag/02UL)
* [Stacks Project, Tag 0F9B](https://stacks.math.columbia.edu/tag/0F9B)
* [Stacks Project, Tag 02QL](https://stacks.math.columbia.edu/tag/02QL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

/-! ### The intertwining relation is closed under the ring operations -/

section Algebra

universe v

variable {G H : ℤ → Type v} [∀ k, AddCommGroup (G k)] [∀ k, AddCommGroup (H k)] {d : ℤ}
  {pull : ∀ k : ℤ, G k →+ H (k + d)}

/-- An intertwiner carries `0` to `0`. -/
theorem Intertwines.zero : Intertwines pull (0 : GradedCapFamily G) (0 : GradedCapFamily H) :=
  fun _ _ _ => by simp

/-- An intertwiner carries `1` to `1`. -/
theorem Intertwines.one : Intertwines pull (1 : GradedCapFamily G) (1 : GradedCapFamily H) := by
  intro k i x
  match i with
  | 0 =>
      rw [gradedCap_one_apply_zero, gradedCap_one_apply_zero, map_gradedDegreeCast,
        gradedDegreeCast_gradedDegreeCast]
  | (n + 1) =>
      rw [gradedCap_one_of_ne (Nat.succ_ne_zero n), gradedCap_one_of_ne (Nat.succ_ne_zero n)]
      simp

/-- An intertwiner of two pairs of families intertwines their sums. -/
theorem Intertwines.add {a b : GradedCapFamily G} {a' b' : GradedCapFamily H}
    (ha : Intertwines pull a a') (hb : Intertwines pull b b') :
    Intertwines pull (a + b) (a' + b') := by
  intro k i x
  change pull _ (a k i x + b k i x) = gradedDegreeCast H _ (a' _ i _ + b' _ i _)
  rw [map_add, ha k i x, hb k i x, map_add]

/-- An intertwiner of two families intertwines their negatives. -/
theorem Intertwines.neg {a : GradedCapFamily G} {a' : GradedCapFamily H}
    (ha : Intertwines pull a a') : Intertwines pull (-a) (-a') := by
  intro k i x
  change pull _ (-a k i x) = gradedDegreeCast H _ (-a' _ i _)
  rw [map_neg, ha k i x, map_neg]

/-- An intertwiner of two pairs of families intertwines their products. -/
theorem Intertwines.mul {a b : GradedCapFamily G} {a' b' : GradedCapFamily H}
    (ha : Intertwines pull a a') (hb : Intertwines pull b b') :
    Intertwines pull (a * b) (a' * b') := by
  rw [gradedCap_mul_def, gradedCap_mul_def]
  exact ha.convolve hb

/-- An intertwiner carries the natural number `n` to `n`. -/
theorem Intertwines.natCast (n : ℕ) :
    Intertwines pull (n : GradedCapFamily G) (n : GradedCapFamily H) := by
  induction n with
  | zero => simpa using Intertwines.zero
  | succ n ih =>
      rw [Nat.cast_succ, Nat.cast_succ]
      exact ih.add Intertwines.one

/-- An intertwiner of two families of families intertwines their finite sums. -/
theorem Intertwines.sum {ι : Type*} (s : Finset ι) {f : ι → GradedCapFamily G}
    {f' : ι → GradedCapFamily H} :
    (∀ i ∈ s, Intertwines pull (f i) (f' i)) →
      Intertwines pull (∑ i ∈ s, f i) (∑ i ∈ s, f' i) := by
  classical
  induction s using Finset.induction_on with
  | empty => intro _; simpa using Intertwines.zero
  | insert a t ha ih =>
      intro h
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (h a (Finset.mem_insert_self a t)).add
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- An intertwiner of two families intertwines their homogeneous components of each index. -/
theorem Intertwines.homComponent {a : GradedCapFamily G} {a' : GradedCapFamily H}
    (ha : Intertwines pull a a') (i : ℕ) :
    Intertwines pull (homComponent i a) (homComponent i a') := by
  intro k j x
  obtain rfl | hj := eq_or_ne j i
  · simpa using ha k j x
  · rw [homComponent_apply_of_ne hj a, homComponent_apply_of_ne hj a']
    simp

end Algebra

/-! ### The subring of intertwined pairs of Chern-class expressions -/

section Pairs

variable (C : ChowSituation.{u}) {X P : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sP : P ⟶ C.S) [LocallyOfFiniteType sP] {d : ℤ}
  (pull : ∀ k : ℤ, chowGroup C sX k →+ chowGroup C sP (k + d))

/-- **The subring of pairs of Chern-class expressions related by an intertwiner.** It is a
subring of the product of the two commutative subrings generated by the Chern classes, hence a
commutative ring. -/
def intertwinedChernPairs : Subring (chernSubring C sX × chernSubring C sP) where
  carrier := {z | Intertwines pull (z.1 : GradedCapFamily (chowGroup C sX))
    (z.2 : GradedCapFamily (chowGroup C sP))}
  one_mem' := Intertwines.one
  mul_mem' ha hb := Intertwines.mul ha hb
  zero_mem' := Intertwines.zero
  add_mem' ha hb := Intertwines.add ha hb
  neg_mem' ha := Intertwines.neg ha

/-- Membership in `Stacks.Chow.intertwinedChernPairs` is the intertwining relation. -/
theorem mem_intertwinedChernPairs
    {z : chernSubring C sX × chernSubring C sP} :
    z ∈ intertwinedChernPairs C sX sP pull ↔
      Intertwines pull (z.1 : GradedCapFamily (chowGroup C sX))
        (z.2 : GradedCapFamily (chowGroup C sP)) :=
  Iff.rfl

/-- **Flat pullback carries `P_p` of the Chern classes of a module to `P_p` of the Chern classes
of its pullback.** The hypothesis is Stacks 02U8 for the total Chern classes, which is
`Stacks.Chow.GenuineChern.intertwines_chernFamily`. -/
theorem intertwines_powerSumChernElem (F : X.Modules) (F' : P.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F' r]
    (hchern : Intertwines pull (GenuineChern.chernFamily C sX F r)
      (GenuineChern.chernFamily C sP F' r)) (p : ℕ) :
    Intertwines pull (powerSumChernElem C sX F r p) (powerSumChernElem C sP F' r p) := by
  have hmem : ∀ i : ℕ+,
      ((chernClassSub C sX F r (i : ℕ), chernClassSub C sP F' r (i : ℕ)) :
        chernSubring C sX × chernSubring C sP) ∈ intertwinedChernPairs C sX sP pull :=
    fun i => hchern.homComponent (i : ℕ)
  have hfst : ((RingHom.fst (chernSubring C sX) (chernSubring C sP)).comp
        (Subring.subtype (intertwinedChernPairs C sX sP pull)))
      (AlgebraicGeometry.powerSumOfChernClasses r
        (fun i : ℕ+ => (⟨_, hmem i⟩ : intertwinedChernPairs C sX sP pull)) p)
      = AlgebraicGeometry.powerSumOfChernClasses (A := chernSubring C sX) r
          (fun i : ℕ+ => chernClassSub C sX F r (i : ℕ)) p :=
    AlgebraicGeometry.powerSumOfChernClasses_map _ r _ p
  have hsnd : ((RingHom.snd (chernSubring C sX) (chernSubring C sP)).comp
        (Subring.subtype (intertwinedChernPairs C sX sP pull)))
      (AlgebraicGeometry.powerSumOfChernClasses r
        (fun i : ℕ+ => (⟨_, hmem i⟩ : intertwinedChernPairs C sX sP pull)) p)
      = AlgebraicGeometry.powerSumOfChernClasses (A := chernSubring C sP) r
          (fun i : ℕ+ => chernClassSub C sP F' r (i : ℕ)) p :=
    AlgebraicGeometry.powerSumOfChernClasses_map _ r _ p
  simp only [powerSumChernElem]
  rw [← hfst, ← hsnd]
  exact (AlgebraicGeometry.powerSumOfChernClasses
    (A := intertwinedChernPairs C sX sP pull) r
    (fun i : ℕ+ => (⟨_, hmem i⟩ : intertwinedChernPairs C sX sP pull)) p).property

end Pairs

end Stacks.Chow

end
