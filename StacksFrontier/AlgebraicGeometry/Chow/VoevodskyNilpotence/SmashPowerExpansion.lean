module

public import StacksFrontier.AlgebraicGeometry.Chow.VoevodskyNilpotence.RationalPointExteriorProduct
public import StacksFrontier.AlgebraicGeometry.Chow.VoevodskyNilpotence.SmashPower

/-!
# The expansion of a smash power of a difference of rational points

Let `x, x'` be rational points of a scheme `X` locally of finite type over a field `k`. The
`n`-th exterior power `([x] - [x'])^{×n}` of Stacks 0FH9, `Stacks.Chow.smashPointDifference`,
lives on the `n`-fold fibre power `X^n`, and it is the signed sum

  `([x] - [x'])^{×n} = ∑_{s : Fin n → Bool} (-1)^{|s|} [P_s]`

of the classes of the `2^n` rational points `P_s` of `X^n` whose `i`-th coordinate is `x'` if
`s i` and `x` otherwise. This turns every compatibility of the smash power with an operation on
Chow groups that acts on rational points (base change along a field extension, pushforward along
a closed immersion) into a compatibility of points.

## Main definitions

* `Stacks.Chow.smashPoint`: the rational point `P_s` of `X^n`.

## Main results

* `Stacks.Chow.smashPointDifference_cycle_eq_sum`: the expansion above.

## Implementation notes

The fibre power is the one of `Stacks.Chow.smashPointDifference`, parenthesized from the left, so
the points are built by the same recursion: `P_{snoc s b} = (P_s, x or x')`. The induction step
is `Stacks.Chow.chowExteriorProduct_sum_tmul_rationalPointChowClass_sub`.

## References

* [Stacks Project, Tag 0FH9](https://stacks.math.columbia.edu/tag/0FH9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

open Stacks.WeilCohomology

attribute [local instance] SmashPowerData.finiteType

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ (fieldChowSituation k).S)
  [LocallyOfFiniteType f] (x x' : (fieldChowSituation k).S ⟶ X) (hx : x ≫ f = 𝟙 _)
  (hx' : x' ≫ f = 𝟙 _)

omit [LocallyOfFiniteType f] in
include hx hx' in
/-- Each of the two points `x`, `x'` is a section. -/
theorem cond_comp_eq_id (b : Bool) : cond b x' x ≫ f = 𝟙 _ := by
  cases b <;> assumption

/-- The rational points of the fibre power `X^n` with coordinates in `{x, x'}`, bundled with the
fact that they are sections of its structure morphism. -/
def smashPointAux : (n : ℕ) → (Fin n → Bool) →
    { p : (fieldChowSituation k).S ⟶ (smashPointDifference k f x x' hx hx' n).Y.left //
      p ≫ (smashPointDifference k f x x' hx hx' n).Y.hom = 𝟙 _ }
  | 0, _ => ⟨𝟙 _, Category.id_comp _⟩
  | n + 1, s =>
    let p := smashPointAux n (Fin.init s)
    ⟨pullback.lift p.1 (cond (s (Fin.last n)) x' x)
        (p.2.trans (cond_comp_eq_id k f x x' hx hx' _).symm), by
      change pullback.lift _ _ _ ≫ pullback.fst _ _ ≫ _ = _
      rw [pullback.lift_fst_assoc]
      exact p.2⟩

/-- **The rational point `P_s` of `X^n`** whose `i`-th coordinate is `x'` if `s i` and `x`
otherwise. -/
def smashPoint (n : ℕ) (s : Fin n → Bool) :
    (fieldChowSituation k).S ⟶ (smashPointDifference k f x x' hx hx' n).Y.left :=
  (smashPointAux k f x x' hx hx' n s).1

/-- `P_s` is a rational point of `X^n`. -/
theorem smashPoint_comp (n : ℕ) (s : Fin n → Bool) :
    smashPoint k f x x' hx hx' n s ≫ (smashPointDifference k f x x' hx hx' n).Y.hom = 𝟙 _ :=
  (smashPointAux k f x x' hx hx' n s).2

/-- The point of the empty fibre power is the base point. -/
theorem smashPoint_zero (s : Fin 0 → Bool) : smashPoint k f x x' hx hx' 0 s = 𝟙 _ :=
  rfl

/-- The recursion defining `P_s`: its last coordinate is `x'` or `x`, and the others form
`P_{init s}`. -/
theorem smashPoint_succ (n : ℕ) (s : Fin (n + 1) → Bool) :
    smashPoint k f x x' hx hx' (n + 1) s =
      pullback.lift (smashPoint k f x x' hx hx' n (Fin.init s)) (cond (s (Fin.last n)) x' x)
        ((smashPoint_comp k f x x' hx hx' n _).trans (cond_comp_eq_id k f x x' hx hx' _).symm) :=
  rfl

/-- All but the last coordinate of `P_s` form `P_{init s}`. -/
theorem smashPoint_succ_fst (n : ℕ) (s : Fin (n + 1) → Bool) :
    smashPoint k f x x' hx hx' (n + 1) s ≫
        pullback.fst (smashPointDifference k f x x' hx hx' n).Y.hom f =
      smashPoint k f x x' hx hx' n (Fin.init s) :=
  pullback.lift_fst _ _ _

/-- The last coordinate of `P_s` is `x'` or `x`. -/
theorem smashPoint_succ_snd (n : ℕ) (s : Fin (n + 1) → Bool) :
    smashPoint k f x x' hx hx' (n + 1) s ≫
        pullback.snd (smashPointDifference k f x x' hx hx' n).Y.hom f =
      cond (s (Fin.last n)) x' x :=
  pullback.lift_snd _ _ _

/-- **The expansion of a smash power of `[x] - [x']`.** The `n`-th exterior power of
`[x] - [x']` is the signed sum, over the `2^n` rational points `P_s` of `X^n` with coordinates in
`{x, x'}`, of their classes. -/
theorem smashPointDifference_cycle_eq_sum (n : ℕ) :
    (smashPointDifference k f x x' hx hx' n).cycle =
      ∑ s : Fin n → Bool, boolSign s • rationalPointChowClass k
        (smashPointDifference k f x x' hx hx' n).Y.hom (smashPoint k f x x' hx hx' n s)
        (smashPoint_comp k f x x' hx hx' n s) := by
  induction n with
  | zero =>
    rw [Fintype.sum_unique, boolSign_zero, one_smul]
    rfl
  | succ n ih =>
    show chowExteriorProduct (fieldChowSituation k)
      (fieldChowSituation_dimensionFunction_of_isClosed k) _ f 0 0
      ((smashPointDifference k f x x' hx hx' n).cycle ⊗ₜ
        (rationalPointChowClass k f x hx - rationalPointChowClass k f x' hx')) = _
    rw [ih]
    exact chowExteriorProduct_sum_tmul_rationalPointChowClass_sub k _ f x x' hx hx'
      (smashPoint k f x x' hx hx' n) (smashPoint_comp k f x x' hx hx' n)
      (cond_comp_eq_id k f x x' hx hx')

end Stacks.Chow

end
