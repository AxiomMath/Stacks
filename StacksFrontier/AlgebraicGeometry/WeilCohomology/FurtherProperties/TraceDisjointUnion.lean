module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.DisjointUnion
public import StacksCore.Tactic.StacksAttribute

/-!
# Additivity of the trace map over a disjoint union

Let `X` and `Y` be smooth projective schemes over `k`, equidimensional of the same dimension
`d`, and let `Z` be their disjoint union, with coprojections `i : X ⟶ Z` and `j : Y ⟶ Z`. Then

`∫_Z = ∫_X ∘ i^* + ∫_Y ∘ j^*`

as linear functionals on `H^{2d}(Z)`; this is the sense in which `∫_{X ⨿ Y} = ∫_X + ∫_Y`, since
`(i^*, j^*) : H^{2d}(Z) ⟶ H^{2d}(X) × H^{2d}(Y)` is an isomorphism by Stacks 0FHJ.

The proof is the source's: writing `e = γ([X]) = i_*1` and `f = γ([Y]) = j_*1` for the two
orthogonal idempotents of `H^0(Z)` summing to `1`, a class `a` of degree `2d` decomposes as
`a = a ∪ e + a ∪ f`, and the trace equation `∫_X i^*b ∪ a' = ∫_Z b ∪ i_*a'` defining the
Poincaré-duality pushforward, applied to `b = a` and `a' = 1`, identifies `∫_Z (a ∪ e)` with
`∫_X i^*a`.

## Main results

* `Stacks.WeilCohomology.PoincareDualityPushforwardSetup.integration_mul_pushforwardOne`:
  `∫_Z (a ∪ i_*1) = ∫_X i^*a`, the half of the argument supplied by Poincaré duality.
* `Stacks.WeilCohomology.PoincareDualityPushforwardSetup.integration_eq_integration_pullback_add`:
  `∫_Z a = ∫_X i^*a + ∫_Y j^*a` for a class `a` of degree `2d`.
* `Stacks.WeilCohomology.PoincareDualityPushforwardSetup.integration_eq_add_comp_pullback`: the
  same as an identity `∫_Z = ∫_X ∘ i^* + ∫_Y ∘ j^*` between linear functionals.

## Implementation notes

The cohomological data is the Poincaré duality package
`Stacks.WeilCohomology.PoincareDualityPushforwardSetup`, the data `(D1)`, `(D3)` and condition
`(A)` of Section 45.9, exactly as in
`StacksFrontier.AlgebraicGeometry.WeilCohomology.DisjointUnion`; degree arithmetic goes through
`ExternallyGraded.degreeCast`.

The input the source draws from the remaining conditions is the hypothesis `hone`, that the unit
of `H^0(Z)` is `γ([X]) + γ([Y]) = i_*1 + j_*1`; it is `1 = γ([X ⨿ Y]) = γ([X]) + γ([Y])` from
Stacks 0FHF, additivity of the cycle class map, and condition `(C)(c)`. The hypotheses
`hdX : dim X = dim Z` and `hdY : dim Y = dim Z` are the source's assumption that `X` and `Y` are
equidimensional of dimension `d`, together with `dim (X ⨿ Y) = d`. Nonemptiness of `X` and `Y` is
not needed: it enters the source only through those two statements about dimensions.

Since the trace maps of `X`, `Y` and `Z` are defined on cohomology in the respective top degrees
`2 dim X`, `2 dim Y` and `2 dim Z`, the two pullbacks are followed by the transport of degree
supplied by `hdX` and `hdY`.

## References

* [Stacks Project, Tag 0FHP](https://stacks.math.columbia.edu/tag/0FHP)
-/

open AlgebraicGeometry

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u v w

namespace ExternallyGradedAlgebra

/-- Transport of the degree of the right factor of a product may be moved out of the product:
both bracketings become the same element of the piece of degree `p`. -/
theorem degreeCast_mul_degreeCast {R : Type v} [CommRing R]
    {A : ExternallyGradedAlgebra.{v, w} R} {n m m' p : ℤ} (h : m = m') (h₁ : n + m' = p)
    (h₂ : n + m = p) (a : A.piece n) (y : A.piece m) :
    ExternallyGraded.degreeCast (R := R) (X := A.piece) h₁
        (A.mul n m' a (ExternallyGraded.degreeCast (R := R) (X := A.piece) h y)) =
      ExternallyGraded.degreeCast (R := R) (X := A.piece) h₂ (A.mul n m a y) :=
  eq_of_heq <|
    (ExternallyGraded.degreeCast_heq (R := R) (X := A.piece) h₁ _).trans <|
      (mul_degreeCast_heq n m m' h a y).trans
        (ExternallyGraded.degreeCast_heq (R := R) (X := A.piece) h₂ _).symm

/-- Cup product with the unit transported into degree `m` is the identity, after transporting
the degree `n + m` of the product back to `n`. -/
theorem degreeCast_mul_degreeCast_one {R : Type v} [CommRing R]
    {A : ExternallyGradedAlgebra.{v, w} R} {n m p : ℤ} (h : (0 : ℤ) = m) (h₁ : n + m = p)
    (h₂ : n = p) (a : A.piece n) :
    ExternallyGraded.degreeCast (R := R) (X := A.piece) h₁
        (A.mul n m a (ExternallyGraded.degreeCast (R := R) (X := A.piece) h A.one)) =
      ExternallyGraded.degreeCast (R := R) (X := A.piece) h₂ a := by
  subst h h₂
  exact A.degreeCast_mul_one n a

end ExternallyGradedAlgebra

namespace Stacks.WeilCohomology

variable {k : Type u} [Field k] [IsAlgClosed k] {F : Type v} [Field F] [CharZero F]

namespace PoincareDualityPushforwardSetup

variable (S : PoincareDualityPushforwardSetup.{u, v, w} k F)
  {X Y Z : (SmoothProjective k).FullSubcategory}

/-- **Stacks Project, Tag 0FHP.** The trace of a top-degree class cupped with the cycle class
`i_*1` of a component is the trace of its restriction to that component: `∫_Z a ∪ i_*1 = ∫_X i^*a`
for `i : X ⟶ Z` with `dim X = dim Z`. This is the trace equation
`∫_X i^*a ∪ 1 = ∫_Z a ∪ i_*1` defining the Poincaré-duality pushforward, evaluated on the unit of
`H^0(X)`. -/
theorem integration_mul_pushforwardOne (i : X ⟶ Z) (hd : S.dimension X = S.dimension Z)
    (a : (S.H Z).piece (2 * (S.dimension Z : ℤ))) :
    S.integration Z
        (ExternallyGraded.degreeCast (R := F) (X := (S.H Z).piece)
          (add_zero (2 * (S.dimension Z : ℤ)))
          ((S.H Z).mul (2 * (S.dimension Z : ℤ)) 0 a (S.pushforwardOne i hd))) =
      S.integration X
        (ExternallyGraded.degreeCast (R := F) (X := (S.H X).piece)
          (show 2 * (S.dimension Z : ℤ) = 2 * (S.dimension X : ℤ) by omega)
          (S.pullback i (2 * (S.dimension Z : ℤ)) a)) := by
  have key := S.integration_pullback_mul i (2 * (S.dimension Z : ℤ)) a
    (ExternallyGraded.degreeCast (R := F) (X := (S.H X).piece)
      (show (0 : ℤ) = 2 * (S.dimension X : ℤ) - 2 * (S.dimension Z : ℤ) by omega)
      (S.H X).one)
  have hA : ExternallyGraded.degreeCast (R := F) (X := (S.H Z).piece)
        (add_zero (2 * (S.dimension Z : ℤ)))
        ((S.H Z).mul (2 * (S.dimension Z : ℤ)) 0 a (S.pushforwardOne i hd)) =
      ExternallyGraded.degreeCast (R := F) (X := (S.H Z).piece)
        (show 2 * (S.dimension Z : ℤ) + (2 * (S.dimension Z : ℤ) -
          2 * (S.dimension Z : ℤ)) = 2 * (S.dimension Z : ℤ) by omega)
        ((S.H Z).mul (2 * (S.dimension Z : ℤ))
          (2 * (S.dimension Z : ℤ) - 2 * (S.dimension Z : ℤ)) a
          (S.pushforward i (2 * (S.dimension Z : ℤ))
            (ExternallyGraded.degreeCast (R := F) (X := (S.H X).piece)
              (show (0 : ℤ) = 2 * (S.dimension X : ℤ) - 2 * (S.dimension Z : ℤ) by omega)
              (S.H X).one))) :=
    ExternallyGradedAlgebra.degreeCast_mul_degreeCast (by omega) _ _ a _
  have hB : ExternallyGraded.degreeCast (R := F) (X := (S.H X).piece)
        (show 2 * (S.dimension Z : ℤ) + (2 * (S.dimension X : ℤ) -
          2 * (S.dimension Z : ℤ)) = 2 * (S.dimension X : ℤ) by omega)
        ((S.H X).mul (2 * (S.dimension Z : ℤ))
          (2 * (S.dimension X : ℤ) - 2 * (S.dimension Z : ℤ))
          (S.pullback i (2 * (S.dimension Z : ℤ)) a)
          (ExternallyGraded.degreeCast (R := F) (X := (S.H X).piece)
            (show (0 : ℤ) = 2 * (S.dimension X : ℤ) - 2 * (S.dimension Z : ℤ) by omega)
            (S.H X).one)) =
      ExternallyGraded.degreeCast (R := F) (X := (S.H X).piece)
        (show 2 * (S.dimension Z : ℤ) = 2 * (S.dimension X : ℤ) by omega)
        (S.pullback i (2 * (S.dimension Z : ℤ)) a) :=
    ExternallyGradedAlgebra.degreeCast_mul_degreeCast_one (by omega) _ _ _
  rw [hA, ← hB]
  exact key.symm

/-- **Stacks Project, Tag 0FHP.** Additivity of the trace map over a disjoint union, on a class:
if the unit of `H^0(Z)` is the sum of the cycle classes `i_*1` and `j_*1` of the two components,
both of the same dimension as `Z`, then `∫_Z a = ∫_X i^*a + ∫_Y j^*a`. -/
theorem integration_eq_integration_pullback_add (i : X ⟶ Z) (j : Y ⟶ Z)
    (hdX : S.dimension X = S.dimension Z) (hdY : S.dimension Y = S.dimension Z)
    (hone : (S.H Z).one = S.pushforwardOne i hdX + S.pushforwardOne j hdY)
    (a : (S.H Z).piece (2 * (S.dimension Z : ℤ))) :
    S.integration Z a =
      S.integration X
          (ExternallyGraded.degreeCast (R := F) (X := (S.H X).piece)
            (show 2 * (S.dimension Z : ℤ) = 2 * (S.dimension X : ℤ) by omega)
            (S.pullback i (2 * (S.dimension Z : ℤ)) a)) +
        S.integration Y
          (ExternallyGraded.degreeCast (R := F) (X := (S.H Y).piece)
            (show 2 * (S.dimension Z : ℤ) = 2 * (S.dimension Y : ℤ) by omega)
            (S.pullback j (2 * (S.dimension Z : ℤ)) a)) := by
  have hsplit : a =
      ExternallyGraded.degreeCast (R := F) (X := (S.H Z).piece)
          (add_zero (2 * (S.dimension Z : ℤ)))
          ((S.H Z).mul (2 * (S.dimension Z : ℤ)) 0 a (S.pushforwardOne i hdX)) +
        ExternallyGraded.degreeCast (R := F) (X := (S.H Z).piece)
          (add_zero (2 * (S.dimension Z : ℤ)))
          ((S.H Z).mul (2 * (S.dimension Z : ℤ)) 0 a (S.pushforwardOne j hdY)) := by
    have hmul : (S.H Z).mul (2 * (S.dimension Z : ℤ)) 0 a (S.pushforwardOne i hdX) +
        (S.H Z).mul (2 * (S.dimension Z : ℤ)) 0 a (S.pushforwardOne j hdY) =
          (S.H Z).mul (2 * (S.dimension Z : ℤ)) 0 a (S.H Z).one := by
      rw [hone, map_add]
    rw [← map_add, hmul, (S.H Z).degreeCast_mul_one (2 * (S.dimension Z : ℤ)) a]
  conv_lhs => rw [hsplit]
  rw [map_add, S.integration_mul_pushforwardOne i hdX a,
    S.integration_mul_pushforwardOne j hdY a]

/-- **Stacks Project, Tag 0FHP.** Additivity of the trace map over a disjoint union:
`∫_{X ⨿ Y} = ∫_X + ∫_Y`, as an identity between linear functionals on `H^{2d}(X ⨿ Y)`, the two
summands being the trace maps of the components precomposed with restriction along the
coprojections. -/
@[stacks 0FHP]
theorem integration_eq_add_comp_pullback (i : X ⟶ Z) (j : Y ⟶ Z)
    (hdX : S.dimension X = S.dimension Z) (hdY : S.dimension Y = S.dimension Z)
    (hone : (S.H Z).one = S.pushforwardOne i hdX + S.pushforwardOne j hdY) :
    (S.integration Z).toLinearMap =
      (S.integration X).toLinearMap.comp
          ((ExternallyGraded.degreeCast (R := F) (X := (S.H X).piece)
              (show 2 * (S.dimension Z : ℤ) = 2 * (S.dimension X : ℤ) by omega)).comp
            (S.pullback i (2 * (S.dimension Z : ℤ)))) +
        (S.integration Y).toLinearMap.comp
          ((ExternallyGraded.degreeCast (R := F) (X := (S.H Y).piece)
              (show 2 * (S.dimension Z : ℤ) = 2 * (S.dimension Y : ℤ) by omega)).comp
            (S.pullback j (2 * (S.dimension Z : ℤ)))) :=
  LinearMap.ext fun a => S.integration_eq_integration_pullback_add i j hdX hdY hone a

end PoincareDualityPushforwardSetup

end Stacks.WeilCohomology

end
