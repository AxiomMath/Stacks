module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.TwistFormula
public import StacksFrontier.AlgebraicGeometry.Chow.ChernWhitney.GradedPowerSum

/-!
# Newton's recursion is additive on a product

`AlgebraicGeometry.newtonPowerSum` is Newton's recursion `P_p` of [Stacks, Tag 0F9B], read in an
arbitrary ring. This file proves `P_p(a b) = P_p(a) + P_p(b)`, the degree-zero terms adding, for
graded cap families and for total Chow cohomology classes `a` and `b` with degree-`0` component
`1` whose homogeneous components commute.

## Main results

* `Stacks.Chow.newtonPowerSum_mul_of_commute`: `P_p(a b) = P_p(a) + P_p(b)` for graded cap
  families with identity index-`0` components whose degree-zero terms add, when the logarithmic
  derivative of `a` commutes with `b`.
* `Stacks.Chow.newtonPowerSum_mul_of_commute_homComponent`: the same identity when the
  homogeneous components of `a` and `b` commute.
* `Stacks.Chow.TotalChowClass.newtonPowerSum_mul_of_commute_homComponent`: the identity in the
  ring `Stacks.Chow.TotalChowClass` of total Chow cohomology classes.

## References

* [Stacks Project, Tag 0F9B](https://stacks.math.columbia.edu/tag/0F9B)
* [Stacks Project, Tag 0F9C](https://stacks.math.columbia.edu/tag/0F9C)
* [Stacks Project, Tag 02UA](https://stacks.math.columbia.edu/tag/02UA)
-/

@[expose] public noncomputable section

open Finset AlgebraicGeometry CategoryTheory

namespace Stacks.Chow

universe v

variable {G : ℤ → Type v} [∀ k, AddCommGroup (G k)]

/-! ### Additivity in the ring of graded cap families -/

/-- **The Newton-additivity identity for Newton's recursion.** If `a` and `b` have identity
index-`0` components and the logarithmic derivative of `a` commutes with `b`, then Newton's
recursion of Stacks 0F9B applied to the homogeneous components of the product `a b`, with the
degree-zero terms adding, is the sum of the two recursions: `P_p(a b) = P_p(a) + P_p(b)`. -/
theorem newtonPowerSum_mul_of_commute {a b : GradedCapFamily G}
    (ha : ∀ k, a k 0 = (1 : GradedCapFamily G) k 0)
    (hb : ∀ k, b k 0 = (1 : GradedCapFamily G) k 0)
    (hcomm : Commute (logDerivFamily a) b) (r r' : GradedCapFamily G) (p : ℕ) :
    newtonPowerSum (r + r') (fun i : ℕ+ => homComponent (i : ℕ) (a * b)) p =
      newtonPowerSum r (fun i : ℕ+ => homComponent (i : ℕ) a) p +
        newtonPowerSum r' (fun i : ℕ+ => homComponent (i : ℕ) b) p := by
  rcases Nat.eq_zero_or_pos p with hp | hp
  · subst hp
    simp only [newtonPowerSum_zero]
  · rw [newtonPowerSum_eq_of_pos (r + r') 0 _ p hp, newtonPowerSum_eq_of_pos r 0 _ p hp,
      newtonPowerSum_eq_of_pos r' 0 _ p hp,
      ← powerSumFamily_eq_newtonPowerSum (mul_apply_zero ha hb),
      ← powerSumFamily_eq_newtonPowerSum ha, ← powerSumFamily_eq_newtonPowerSum hb,
      powerSumFamily_mul_of_commute ha hb hcomm]

/-- **The Newton-additivity identity with commutativity supplied componentwise.** If `a` and `b`
have identity index-`0` components and their homogeneous components commute, then
`P_p(a b) = P_p(a) + P_p(b)`, the degree-zero terms adding. -/
theorem newtonPowerSum_mul_of_commute_homComponent {a b : GradedCapFamily G}
    (ha : ∀ k, a k 0 = (1 : GradedCapFamily G) k 0)
    (hb : ∀ k, b k 0 = (1 : GradedCapFamily G) k 0)
    (h : ∀ i j, Commute (homComponent i a) (homComponent j b))
    (r r' : GradedCapFamily G) (p : ℕ) :
    newtonPowerSum (r + r') (fun i : ℕ+ => homComponent (i : ℕ) (a * b)) p =
      newtonPowerSum r (fun i : ℕ+ => homComponent (i : ℕ) a) p +
        newtonPowerSum r' (fun i : ℕ+ => homComponent (i : ℕ) b) p :=
  newtonPowerSum_mul_of_commute ha hb
    (commute_logDerivFamily_of_commute_homComponent ha h) r r' p

/-! ### Additivity in the ring of total Chow cohomology classes -/

namespace TotalChowClass

universe u

variable {C : ChowSituation.{u}} {Y : Scheme.{u}} {sY : Y ⟶ C.S} [LocallyOfFiniteType sY]

/-- The operation of a total class whose degree-`0` component is `1` has identity index-`0`
component on every test scheme. -/
theorem op_apply_zero {a : TotalChowClass C sY} (ha : a 0 = (1 : TotalChowClass C sY) 0)
    {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (k : ℤ) :
    a.op g k 0 = (1 : GradedCapFamily (fun k => chowGroup C (g ≫ sY) k)) k 0 := by
  have h : a.op g k 0 = (1 : TotalChowClass C sY).op g k 0 := by
    simp only [TotalChowClass.op, ha]
  rw [h, TotalChowClass.op_one]

/-- The operation carries Newton's recursion on the homogeneous components of a total class to
Newton's recursion on the homogeneous components of its operation. -/
theorem op_newtonPowerSum (s c : TotalChowClass C sY) {T : Scheme.{u}} (g : T ⟶ Y)
    [LocallyOfFiniteType g] (p : ℕ) :
    (newtonPowerSum s (fun i : ℕ+ => TotalChowClass.homComponent (i : ℕ) c) p).op g =
      newtonPowerSum (s.op g)
        (fun i : ℕ+ => Stacks.Chow.homComponent (i : ℕ) (c.op g)) p := by
  simpa only [TotalChowClass.opRingHom_apply, TotalChowClass.op_homComponent] using
    map_newtonPowerSum (TotalChowClass.opRingHom g) s
      (fun i : ℕ+ => TotalChowClass.homComponent (i : ℕ) c) p

/-- **The Newton-additivity identity in the ring of total Chow cohomology classes.** Let `a` and
`b` be total classes with degree-`0` component `1` whose homogeneous components commute. Then
Newton's recursion of Stacks 0F9B applied to the product, with the degree-zero terms adding, is
the sum of the two recursions:

  `P_p(a b) = P_p(a) + P_p(b)`. -/
theorem newtonPowerSum_mul_of_commute_homComponent {a b : TotalChowClass C sY}
    (ha : a 0 = (1 : TotalChowClass C sY) 0) (hb : b 0 = (1 : TotalChowClass C sY) 0)
    (h : ∀ i j, Commute (TotalChowClass.homComponent i a) (TotalChowClass.homComponent j b))
    (r r' : TotalChowClass C sY) (p : ℕ) :
    newtonPowerSum (r + r') (fun i : ℕ+ => TotalChowClass.homComponent (i : ℕ) (a * b)) p =
      newtonPowerSum r (fun i : ℕ+ => TotalChowClass.homComponent (i : ℕ) a) p +
        newtonPowerSum r' (fun i : ℕ+ => TotalChowClass.homComponent (i : ℕ) b) p := by
  refine TotalChowClass.ext_op fun g _ => ?_
  rw [TotalChowClass.op_add, op_newtonPowerSum, op_newtonPowerSum, op_newtonPowerSum,
    TotalChowClass.op_mul, TotalChowClass.op_add]
  refine Stacks.Chow.newtonPowerSum_mul_of_commute_homComponent (op_apply_zero ha g)
    (op_apply_zero hb g) (fun i j => ?_) _ _ p
  change Stacks.Chow.homComponent i (a.op g) * Stacks.Chow.homComponent j (b.op g) =
    Stacks.Chow.homComponent j (b.op g) * Stacks.Chow.homComponent i (a.op g)
  simpa only [TotalChowClass.op_mul, TotalChowClass.op_homComponent] using
    congrArg (fun c : TotalChowClass C sY => c.op g) (h i j)

end TotalChowClass

end Stacks.Chow

end
