module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ClassicalKunnethTrace

/-!
# Pushforward of an exterior product along the second projection

Let `H^*` be a classical Weil cohomology theory over an algebraically closed field `k` and let
`X` and `Y` be smooth projective varieties over `k`. The pushforward
`pr_{2, *} : H^*(X × Y) → H^*(Y)` along the second projection sends `a ⊗ b = pr₁^*a ∪ pr₂^*b` to
`(∫_X a) b`.

## Main results

* `Stacks.WeilCohomology.ChowClassicalWeilCohomologyTheory.pushforward_mul_pullback`: for `a` of
  degree `i` on `X` and `b` on `Y`, `pr_{2, *}(pr₁^*a ∪ pr₂^*b)` is `(∫_X a) b` when `i = 2 dim X`
  and zero otherwise.

## Implementation notes

The theory is `Stacks.WeilCohomology.ChowClassicalWeilCohomologyTheory`, whose cycle class maps are
defined on the Chow groups of Chapter 42. The product `X × Y` is any smooth projective variety `P`
with morphisms `p : P ⟶ X` and `q : P ⟶ Y` exhibiting it as the fibre product of the structure
morphisms over `k`, as in the Künneth axiom; the Künneth isomorphism identifies `a ⊗ b` with
`p^*a ∪ q^*b`. The trace `∫_X` is a functional on the piece of degree `2 dim X`, so `(∫_X a) b`
for a homogeneous `a` of another degree is read as zero, and by linearity the statement for
homogeneous classes is the statement for all classes. The pushforward `q_*` is the one determined
by Poincaré duality; it lowers degree by `2 dim P - 2 dim Y = 2 dim X`, so it maps the degree
`2 dim X + j` to the degree `j`, which `ExternallyGraded.degreeCast` records.

The proof is the source's: by Poincaré duality on `Y` it suffices to pair with a class `v` of
complementary degree, and `∫_Y v ∪ q_*(p^*a ∪ q^*b) = ∫_P q^*v ∪ p^*a ∪ q^*b`, which Stacks 0FGX
(`ChowClassicalWeilCohomologyTheory.integration_mul_pullback`) evaluates as `∫_X a · ∫_Y v ∪ b`.

## References

* [Stacks Project, Tag 0FGY](https://stacks.math.columbia.edu/tag/0FGY)
-/

open AlgebraicGeometry

@[expose] public section

open CategoryTheory

universe u v w

namespace Stacks.WeilCohomology.ChowClassicalWeilCohomologyTheory

variable {k : Type u} [Field k] [IsAlgClosed k] {F : Type v} [Field F] [CharZero F]
  (T : ChowClassicalWeilCohomologyTheory.{u, v, w} k F)
  {X Y P : (SmoothProjective k).FullSubcategory}

/-- **Stacks Project, Tag 0FGY.** Let `H^*` be a classical Weil cohomology theory and let `P`,
with projections `p : P ⟶ X` and `q : P ⟶ Y`, be the product of smooth projective varieties `X`
and `Y`. For `a` of degree `i` on `X` and `b` of degree `j` on `Y`, the pushforward along the
second projection sends `a ⊗ b = p^*a ∪ q^*b` to `(∫_X a) b`: to `∫_X a • b` when `i = 2 dim X`,
and to zero otherwise, where `∫_X a` is zero. -/
@[stacks 0FGY]
theorem pushforward_mul_pullback (p : P ⟶ X) (q : P ⟶ Y)
    (hP : IsPullback p.hom.left q.hom.left X.obj.hom Y.obj.hom)
    (i j : ℤ) (a : (T.H X).piece i) (b : (T.H Y).piece j) :
    T.pushforward q (2 * (T.dimension P : ℤ) - (i + j))
        (ExternallyGraded.degreeCast (R := F) (X := (T.H P).piece)
          (show i + j = 2 * (T.dimension P : ℤ) - (2 * (T.dimension P : ℤ) - (i + j)) by omega)
          ((T.H P).mul i j (T.pullback p i a) (T.pullback q j b))) =
      if h : i = 2 * (T.dimension X : ℤ) then
        T.integration X (ExternallyGraded.degreeCast (R := F) (X := (T.H X).piece) h a) •
          ExternallyGraded.degreeCast (R := F) (X := (T.H Y).piece)
            (show j = 2 * (T.dimension Y : ℤ) - (2 * (T.dimension P : ℤ) - (i + j)) by
              rw [T.dimension_eq_add p q hP]; push_cast; omega) b
      else 0 :=
  T.pushforward_mul_pullback_of_trace_mul p q (T.dimension_eq_add p q hP)
    (T.integration_mul_pullback hP) i j a b

end Stacks.WeilCohomology.ChowClassicalWeilCohomologyTheory

end
