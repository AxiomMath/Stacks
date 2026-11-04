module

public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.FurtherProperties.RationalPoints

/-!
# Smash powers of the difference of two rational points

Let `k` be a field, `X` a scheme locally of finite type over `k` and `x`, `x'` two `k`-rational
points of `X`. Stacks 0FH9 (Voevodsky) asserts that for `n` large the zero cycle

  `([x] - [x']) × ⋯ × ([x] - [x'])  ∈  CH_0(Xⁿ)`

is torsion. This file defines that class, over the base situation
`Stacks.Chow.fieldChowSituation k` and with the exterior product
`Stacks.Chow.chowExteriorProduct` of Stacks 0FBV, so that the definition compiles in the draft
tree and can be used by the proof.

## Main definitions

* `Stacks.Chow.pointDifference` — the class `[x] - [x']` in `CH_0(X)`, a difference of two
  `Stacks.WeilCohomology.rationalPointChowClass`es.
* `Stacks.Chow.SmashPowerData` — a scheme `Y` locally of finite type over `k` together with a
  class in `CH_0(Y)`.
* `Stacks.Chow.smashPointDifference` — the `n`-th exterior power of `[x] - [x']`, on the
  `n`-fold fibre power `Xⁿ` parenthesized from the left.

## Implementation notes

The zeroth power is the class of `𝟙 (Spec k)` as a closed subscheme of `Spec k`, and the
`(n+1)`-st power lives on `pullback Yₙ.hom f` with structure morphism `pullback.fst ≫ Yₙ.hom`, and
is the exterior product of the `n`-th power with `[x] - [x']`:

* the base situation is `Stacks.Chow.fieldChowSituation k`, with base `Spec k` and the zero
  dimension function;
* the exterior product is `Stacks.Chow.chowExteriorProduct` (Stacks 0FBV), whose value on a pure
  tensor of cycle classes is the class of `Stacks.Chow.exteriorProduct`
  (`chowExteriorProduct_tmul_mk`).

## References

* [Stacks Project, Tag 0FH9](https://stacks.math.columbia.edu/tag/0FH9)
* [Stacks Project, Tag 0FBV](https://stacks.math.columbia.edu/tag/0FBV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-- The class `[x] - [x']` in `CH_0(X)` of the difference of two `k`-rational points of a scheme
`X` locally of finite type over `k`. -/
def pointDifference (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType f]
    (x x' : (fieldChowSituation k).S ⟶ X)
    (hx : x ≫ f = 𝟙 _) (hx' : x' ≫ f = 𝟙 _) : chowGroup (fieldChowSituation k) f 0 :=
  Stacks.WeilCohomology.rationalPointChowClass k f x hx -
    Stacks.WeilCohomology.rationalPointChowClass k f x' hx'

/-- A scheme locally of finite type over `k` together with a zero-cycle class on it: the data an
iterated exterior power of a zero-cycle class consists of. -/
structure SmashPowerData (k : Type u) [Field k] where
  /-- The scheme, over `Spec k`. -/
  Y : Over (Spec (.of k))
  /-- The scheme is locally of finite type over `k`. -/
  finiteType : LocallyOfFiniteType Y.hom
  /-- The zero-cycle class. -/
  cycle : letI : LocallyOfFiniteType Y.hom := finiteType
    chowGroup (fieldChowSituation k) Y.hom 0

/-- **The `n`-th exterior power of `[x] - [x']`**, on the `n`-fold fibre power of `X` over `k`
parenthesized from the left. The zeroth power is the class of `Spec k`, and the `(n+1)`-st is
the exterior product of the `n`-th with `[x] - [x']`, on `pullback Yₙ.hom f`. -/
def smashPointDifference (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType f]
    (x x' : (fieldChowSituation k).S ⟶ X) (hx : x ≫ f = 𝟙 _) (hx' : x' ≫ f = 𝟙 _) :
    ℕ → SmashPowerData k
  | 0 => ⟨Over.mk (𝟙 _), inferInstanceAs (LocallyOfFiniteType (𝟙 (Spec (.of k)))),
      QuotientAddGroup.mk
        (cycleAssociatedToClosedSubscheme (fieldChowSituation k) (𝟙 _) (𝟙 _) 0)⟩
  | n + 1 =>
      let D := smashPointDifference k f x x' hx hx' n
      letI : LocallyOfFiniteType D.Y.hom := D.finiteType
      ⟨Over.mk (pullback.fst D.Y.hom f ≫ D.Y.hom),
        inferInstanceAs (LocallyOfFiniteType (pullback.fst D.Y.hom f ≫ D.Y.hom)),
        chowExteriorProduct (fieldChowSituation k) (fun _ _ ↦ rfl) D.Y.hom f 0 0
          (TensorProduct.tmul ℤ D.cycle (pointDifference k f x x' hx hx'))⟩

/-- The scheme carrying the zeroth smash power is `Spec k`. -/
@[simp]
theorem smashPointDifference_zero_Y (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType f]
    (x x' : (fieldChowSituation k).S ⟶ X) (hx : x ≫ f = 𝟙 _) (hx' : x' ≫ f = 𝟙 _) :
    (smashPointDifference k f x x' hx hx' 0).Y = Over.mk (𝟙 _) :=
  rfl

/-- The scheme carrying the `(n+1)`-st smash power is the fibre product of the one carrying the
`n`-th with `X`. -/
@[simp]
theorem smashPointDifference_succ_Y (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType f]
    (x x' : (fieldChowSituation k).S ⟶ X) (hx : x ≫ f = 𝟙 _) (hx' : x' ≫ f = 𝟙 _) (n : ℕ) :
    (smashPointDifference k f x x' hx hx' (n + 1)).Y =
      Over.mk (pullback.fst (smashPointDifference k f x x' hx hx' n).Y.hom f ≫
        (smashPointDifference k f x x' hx hx' n).Y.hom) :=
  rfl

end Stacks.Chow

end
