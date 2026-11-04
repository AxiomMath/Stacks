module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ProjectionFormula.Setup
public import StacksCore.Tactic.StacksAttribute

/-!
# The projection formula and functoriality of the Weil cohomology pushforward

For the pushforward determined by Poincaré duality, cup multiplication by a class pulled back
from the target can be moved across the pushforward,
`f_*(f^*b ∪ a) = b ∪ f_*a`, and the pushforward is covariantly functorial,
`g_* ∘ f_* = (g ∘ f)_*`.

## Main results

* `Stacks.WeilCohomology.PoincareDualityPushforwardSetup.pushforward_mul_pullback`: the
  projection formula, in every pair of cohomological degrees.
* `Stacks.WeilCohomology.PoincareDualityPushforwardSetup.pushforward_comp`: functoriality.

## Implementation notes

Degrees are indexed so that the pushforward in degree `i` maps the piece of degree `2d - i` to
the piece of degree `2e - i`; the identities `j + (2d - (i + j)) = 2d - i` and
`(i + j) + (2d - (i + j)) = 2d` are the same integer written two ways, so the statements carry
`ExternallyGraded.degreeCast` transports between the corresponding graded pieces.

## References

* [Stacks Project, Tag 0FGT](https://stacks.math.columbia.edu/tag/0FGT)
-/

open AlgebraicGeometry

@[expose] public section

open CategoryTheory

universe u v w

namespace ExternallyGradedAlgebra

/-- Transporting the right factor of a product along an equality of degrees does not change the
product, heterogeneously. -/
theorem mul_degreeCast_heq {R : Type v} [CommRing R] {A : ExternallyGradedAlgebra.{v, w} R}
    (i j j' : ℤ) (h : j = j') (x : A.piece i) (y : A.piece j) :
    A.mul i j' x (ExternallyGraded.degreeCast (R := R) h y) ≍ A.mul i j x y := by
  cases h
  rfl

/-- Associativity of the product, read as an equation between elements of the piece of degree
`d` after transporting both bracketings there. -/
theorem degreeCast_mul_mul {R : Type v} [CommRing R] {A : ExternallyGradedAlgebra.{v, w} R}
    (d i j : ℤ) (x : A.piece i) (y : A.piece j) (z : A.piece (d - (i + j))) :
    ExternallyGraded.degreeCast (R := R) (show i + (d - i) = d by omega)
        (A.mul i (d - i) x
          (ExternallyGraded.degreeCast (R := R)
            (show j + (d - (i + j)) = d - i by omega) (A.mul j (d - (i + j)) y z))) =
      ExternallyGraded.degreeCast (R := R) (show i + j + (d - (i + j)) = d by omega)
        (A.mul (i + j) (d - (i + j)) (A.mul i j x y) z) :=
  eq_of_heq <|
    (ExternallyGraded.degreeCast_heq (R := R) (X := A.piece)
          (show i + (d - i) = d by omega) _).trans <|
      (mul_degreeCast_heq i (j + (d - (i + j))) (d - i) (by omega) x
            (A.mul j (d - (i + j)) y z)).trans <|
        (A.mul_assoc i j (d - (i + j)) x y z).symm.trans
          (ExternallyGraded.degreeCast_heq (R := R) (X := A.piece)
            (show i + j + (d - (i + j)) = d by omega) _).symm

end ExternallyGradedAlgebra

namespace Stacks.WeilCohomology

variable {k : Type u} [Field k] [IsAlgClosed k] {F : Type v} [Field F] [CharZero F]
  (S : PoincareDualityPushforwardSetup.{u, v, w} k F)

/-- The projection formula `f_*(f^*b ∪ a) = b ∪ f_*a` for the pushforward determined by Poincaré
duality. -/
@[stacks 0FGT "projection_formula"]
theorem PoincareDualityPushforwardSetup.pushforward_mul_pullback
    {X Y : (SmoothProjective k).FullSubcategory} (f : X ⟶ Y) (i j : ℤ)
    (b : (S.H Y).piece j) (a : (S.H X).piece (2 * (S.dimension X : ℤ) - (i + j))) :
    S.pushforward f i
        (ExternallyGraded.degreeCast (R := F) (by omega)
          ((S.H X).mul j (2 * (S.dimension X : ℤ) - (i + j)) (S.pullback f j b) a)) =
      ExternallyGraded.degreeCast (R := F) (by omega)
        ((S.H Y).mul j (2 * (S.dimension Y : ℤ) - (i + j)) b (S.pushforward f (i + j) a)) := by
  have : ((S.H Y).tracePairing (S.dimension Y)
    (S.integration Y).toLinearMap i).IsPerfPair := S.perfect Y i
  refine (LinearMap.IsPerfPair.bijective_right ((S.H Y).tracePairing (S.dimension Y)
    (S.integration Y).toLinearMap i)).injective (LinearMap.ext fun c ↦ ?_)
  show (S.H Y).tracePairing (S.dimension Y) (S.integration Y).toLinearMap i c _ =
    (S.H Y).tracePairing (S.dimension Y) (S.integration Y).toLinearMap i c _
  rw [← S.integration_pullback_mul f i c]
  have hX := congrArg (S.integration X)
    (ExternallyGradedAlgebra.degreeCast_mul_mul (R := F) (A := S.H X)
      (2 * (S.dimension X : ℤ)) i j (S.pullback f i c) (S.pullback f j b) a)
  have hY := congrArg (S.integration Y)
    (ExternallyGradedAlgebra.degreeCast_mul_mul (R := F) (A := S.H Y)
      (2 * (S.dimension Y : ℤ)) i j c b (S.pushforward f (i + j) a))
  have hAdj := S.integration_pullback_mul f (i + j) ((S.H Y).mul i j c b) a
  change S.integration X
      (ExternallyGraded.degreeCast (R := F) (by omega)
        ((S.H X).mul (i + j) (2 * (S.dimension X : ℤ) - (i + j))
          (S.pullback f (i + j) ((S.H Y).mul i j c b)) a)) =
    S.integration Y
      (ExternallyGraded.degreeCast (R := F) (by omega)
        ((S.H Y).mul (i + j) (2 * (S.dimension Y : ℤ) - (i + j))
          ((S.H Y).mul i j c b) (S.pushforward f (i + j) a))) at hAdj
  show S.integration X
      (ExternallyGraded.degreeCast (R := F) (by omega)
        ((S.H X).mul i (2 * (S.dimension X : ℤ) - i) (S.pullback f i c)
          (ExternallyGraded.degreeCast (R := F) (by omega)
            ((S.H X).mul j (2 * (S.dimension X : ℤ) - (i + j))
              (S.pullback f j b) a)))) =
    S.integration Y
      (ExternallyGraded.degreeCast (R := F) (by omega)
        ((S.H Y).mul i (2 * (S.dimension Y : ℤ) - i) c
          (ExternallyGraded.degreeCast (R := F) (by omega)
            ((S.H Y).mul j (2 * (S.dimension Y : ℤ) - (i + j))
              b (S.pushforward f (i + j) a)))))
  rw [hX, ← S.pullback_mul f i j c b, hAdj, ← hY]

/-- The pushforward determined by Poincaré duality is covariantly functorial:
`g_* ∘ f_* = (g ∘ f)_*`. -/
@[stacks 0FGT "pushforward_functoriality"]
theorem PoincareDualityPushforwardSetup.pushforward_comp
    {X Y Z : (SmoothProjective k).FullSubcategory} (f : X ⟶ Y) (g : Y ⟶ Z) (i : ℤ) :
    (S.pushforward g i).comp (S.pushforward f i) = S.pushforward (f ≫ g) i := by
  refine (S.eq_pushforward_iff (f ≫ g) i _).2 fun b a ↦ ?_
  simpa only [S.pullback_comp, LinearMap.comp_apply] using
    (S.integration_pullback_mul f i (S.pullback g i b) a).trans
      (S.integration_pullback_mul g i b (S.pushforward f i a))

end Stacks.WeilCohomology

end
