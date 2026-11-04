module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ClassicalTheory
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ProjectionFormula.Formula
public import StacksCore.Tactic.StacksAttribute

/-!
# Additivity of a Weil cohomology theory on a disjoint union

Let `X` and `Y` be smooth projective schemes over `k` and let `Z` be their disjoint union, with
coprojections `i : X ⟶ Z` and `j : Y ⟶ Z`. Then

`H^*(Z) ⟶ H^*(X) × H^*(Y)`, `a ↦ (i^*a, j^*a)`

is an isomorphism. Writing `e = γ([X])` and `f = γ([Y])` in `H^0(Z)`, the two halves of the
argument are as follows. The classes `e` and `f` are orthogonal idempotents summing to `1`, and
`e = i_*1`, `f = j_*1`, so the projection formula gives
`a = a ∪ 1 = a ∪ e + a ∪ f = i_*(i^*a) + j_*(j^*a)`, whence injectivity. For surjectivity,
`i^*e = 1`, `i^*f = 0`, `j^*e = 0` and `j^*f = 1`, so once each of `i^*` and `j^*` is surjective
the class `a ∪ e + a' ∪ f` restricts to `i^*a` on `X` and to `j^*a'` on `Y`.

## Main definitions

* `Stacks.WeilCohomology.PoincareDualityPushforwardSetup.pushforwardOne`: the class `i_*1` of
  `H^0(Z)`, which is `γ([X])`.
* `Stacks.WeilCohomology.PoincareDualityPushforwardSetup.pullbackPairEquiv`: the isomorphism
  `H^n(Z) ≃ H^n(X) × H^n(Y)` in each degree.

## Main results

* `Stacks.WeilCohomology.PoincareDualityPushforwardSetup.pushforward_degreeCast`: the
  Poincaré-duality pushforward is compatible with transport of its degree index.
* `Stacks.WeilCohomology.PoincareDualityPushforwardSetup.mul_pushforward_one`: cup product with
  `f_*1` is `f_* ∘ f^*`.
* `Stacks.WeilCohomology.PoincareDualityPushforwardSetup.pullbackPair_injective`: injectivity,
  from the decomposition of `1` into the two idempotents.
* `PoincareDualityPushforwardSetup.pullbackPair_injective_of_pushforward_one`: the same
  with the two pushforwards taken to be those of the Poincaré duality package.
* `Stacks.WeilCohomology.PoincareDualityPushforwardSetup.pullbackPair_surjective`: surjectivity,
  from the restrictions of the two idempotents and surjectivity of each `i^*`, `j^*`.
* `Stacks.WeilCohomology.PoincareDualityPushforwardSetup.pullbackPair_bijective`: the two
  together.

## Implementation notes

The cohomological data is the Poincaré duality package
`Stacks.WeilCohomology.PoincareDualityPushforwardSetup`, the data `(D1)`, `(D3)` and condition
`(A)` of a Weil cohomology theory; `X`, `Y` and `Z` are objects of
`(SmoothProjective k).FullSubcategory`, so smoothness and projectivity are part of their types.
Tate twists are carried inside the graded pieces, and a class of codimension `r` lives in the
piece of degree `2 * r`. Degree arithmetic goes through `ExternallyGraded.degreeCast`.

The inputs from the remaining conditions of a Weil cohomology theory are hypotheses:

* `hone`, that `1 = e + f`, which holds since `1 = γ([X ⨿ Y]) = γ([X]) + γ([Y])` by additivity of
  the cycle class map and condition `(C)(c)`.
* `hpushX` and `hpushY` of `pullbackPair_injective`, that cup product with `e`, resp. `f`, is
  `i_* ∘ i^*`, resp. `j_* ∘ j^*`, for given maps `i_*` and `j_*` in each degree.
  `pullbackPair_injective_of_pushforward_one` takes these maps to be the pushforwards of the
  package, for `X` and `Y` of the same dimension as `Z`, where the two hypotheses are
  `mul_pushforward_one`.
* `hie`, `hif`, `hje`, `hjf`, the restrictions of the two idempotents, which follow from
  condition `(C)(a)`.
* `hi` and `hj`, surjectivity of `i^*` and `j^*`: after a base change to a finite separable
  extension `k'/k` realised as the residue field of a closed point of `X` there is a morphism
  `Y × Spec k' ⟶ X × Spec k'`, hence a retraction of the coprojection.

## References

* [Stacks Project, Tag 0FHJ](https://stacks.math.columbia.edu/tag/0FHJ)
-/

open AlgebraicGeometry

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u v w

namespace ExternallyGradedAlgebra

/-- Cup product with the unit on the right is the identity, after transporting the degree `n + 0`
of the product back to `n`. -/
theorem degreeCast_mul_one {R : Type v} [CommRing R] (A : ExternallyGradedAlgebra.{v, w} R)
    (n : ℤ) (a : A.piece n) :
    ExternallyGraded.degreeCast (R := R) (X := A.piece) (add_zero n) (A.mul n 0 a A.one) = a :=
  eq_of_heq <|
    (ExternallyGraded.degreeCast_heq (R := R) (X := A.piece) (add_zero n) _).trans (A.mul_one n a)

end ExternallyGradedAlgebra

namespace Stacks.WeilCohomology

variable {k : Type u} [Field k] [IsAlgClosed k] {F : Type v} [Field F] [CharZero F]

namespace PoincareDualityPushforwardSetup

variable (S : PoincareDualityPushforwardSetup.{u, v, w} k F)
  {X Y Z : (SmoothProjective k).FullSubcategory}

omit [CharZero F] in
/-- Transport between graded pieces of equal degree composes. -/
private theorem degreeCast_degreeCast {P : ℤ → Type w} [∀ m, AddCommGroup (P m)]
    [∀ m, Module F (P m)] {p q r : ℤ} (h : p = q) (h' : q = r) (h'' : p = r) (x : P p) :
    ExternallyGraded.degreeCast (R := F) (X := P) h'
        (ExternallyGraded.degreeCast (R := F) (X := P) h x) =
      ExternallyGraded.degreeCast (R := F) (X := P) h'' x := by
  cases h
  cases h'
  rfl

/-- The Poincaré-duality pushforward is compatible with transport of its degree index: the
pushforwards in degrees `i` and `i'` agree whenever `i = i'`. -/
theorem pushforward_degreeCast (f : X ⟶ Y) {i i' : ℤ} (h : i = i')
    (h₁ : 2 * (S.dimension X : ℤ) - i = 2 * (S.dimension X : ℤ) - i')
    (h₂ : 2 * (S.dimension Y : ℤ) - i = 2 * (S.dimension Y : ℤ) - i')
    (x : (S.H X).piece (2 * (S.dimension X : ℤ) - i)) :
    S.pushforward f i' (ExternallyGraded.degreeCast (R := F) (X := (S.H X).piece) h₁ x) =
      ExternallyGraded.degreeCast (R := F) (X := (S.H Y).piece) h₂ (S.pushforward f i x) := by
  cases h
  rfl

/-- Cup product with the pushforward `f_*1` of the unit is `f_* ∘ f^*`, for a morphism
`f : X ⟶ Z` of smooth projective schemes over `k` of equal dimension:
`a ∪ f_*1 = f_*(f^*a ∪ 1) = f_*(f^*a)`. -/
@[stacks 0FGT "cup product with the pushforward of the unit"]
theorem mul_pushforward_one (f : X ⟶ Z) (hd : S.dimension X = S.dimension Z) (n : ℤ)
    (a : (S.H Z).piece n) :
    ExternallyGraded.degreeCast (R := F) (X := (S.H Z).piece) (add_zero n)
        ((S.H Z).mul n 0 a
          (ExternallyGraded.degreeCast (R := F) (X := (S.H Z).piece)
            (show 2 * (S.dimension Z : ℤ) - 2 * (S.dimension Z : ℤ) = 0 by omega)
            (S.pushforward f (2 * (S.dimension Z : ℤ))
              (ExternallyGraded.degreeCast (R := F) (X := (S.H X).piece)
                (show (0 : ℤ) = 2 * (S.dimension X : ℤ) - 2 * (S.dimension Z : ℤ) by omega)
                (S.H X).one)))) =
      ExternallyGraded.degreeCast (R := F) (X := (S.H Z).piece)
        (show 2 * (S.dimension Z : ℤ) - (2 * (S.dimension Z : ℤ) - n) = n by omega)
        (S.pushforward f (2 * (S.dimension Z : ℤ) - n)
          (ExternallyGraded.degreeCast (R := F) (X := (S.H X).piece)
            (show n = 2 * (S.dimension X : ℤ) - (2 * (S.dimension Z : ℤ) - n) by omega)
            (S.pullback f n a))) := by
  have hA1 : ExternallyGraded.degreeCast (R := F) (X := (S.H X).piece)
        (show n + (2 * (S.dimension X : ℤ) - (2 * (S.dimension Z : ℤ) - n + n)) =
          2 * (S.dimension X : ℤ) - (2 * (S.dimension Z : ℤ) - n) by omega)
        ((S.H X).mul n (2 * (S.dimension X : ℤ) - (2 * (S.dimension Z : ℤ) - n + n))
          (S.pullback f n a)
          (ExternallyGraded.degreeCast (R := F) (X := (S.H X).piece)
            (show (0 : ℤ) =
              2 * (S.dimension X : ℤ) - (2 * (S.dimension Z : ℤ) - n + n) by omega)
            (S.H X).one)) =
      ExternallyGraded.degreeCast (R := F) (X := (S.H X).piece)
        (show n = 2 * (S.dimension X : ℤ) - (2 * (S.dimension Z : ℤ) - n) by omega)
        (S.pullback f n a) := by
    refine eq_of_heq
      ((ExternallyGraded.degreeCast_heq (R := F) (X := (S.H X).piece) _ _).trans ?_)
    refine HEq.trans ?_
      (ExternallyGraded.degreeCast_heq (R := F) (X := (S.H X).piece) _ _).symm
    exact (ExternallyGradedAlgebra.mul_degreeCast_heq (A := S.H X) n 0
        (2 * (S.dimension X : ℤ) - (2 * (S.dimension Z : ℤ) - n + n)) (by omega)
        (S.pullback f n a) (S.H X).one).trans
      ((S.H X).mul_one n (S.pullback f n a))
  have hpush : S.pushforward f (2 * (S.dimension Z : ℤ) - n + n)
        (ExternallyGraded.degreeCast (R := F) (X := (S.H X).piece)
          (show (0 : ℤ) =
            2 * (S.dimension X : ℤ) - (2 * (S.dimension Z : ℤ) - n + n) by omega)
          (S.H X).one) =
      ExternallyGraded.degreeCast (R := F) (X := (S.H Z).piece)
        (show 2 * (S.dimension Z : ℤ) - 2 * (S.dimension Z : ℤ) =
          2 * (S.dimension Z : ℤ) - (2 * (S.dimension Z : ℤ) - n + n) by omega)
        (S.pushforward f (2 * (S.dimension Z : ℤ))
          (ExternallyGraded.degreeCast (R := F) (X := (S.H X).piece)
            (show (0 : ℤ) = 2 * (S.dimension X : ℤ) - 2 * (S.dimension Z : ℤ) by omega)
            (S.H X).one)) := by
    rw [← S.pushforward_degreeCast f
      (show 2 * (S.dimension Z : ℤ) = 2 * (S.dimension Z : ℤ) - n + n by omega)
      (by omega) (by omega)]
    exact congrArg (S.pushforward f (2 * (S.dimension Z : ℤ) - n + n))
      (degreeCast_degreeCast (F := F) (P := (S.H X).piece) _ _ _ _).symm
  have key := S.pushforward_mul_pullback f (2 * (S.dimension Z : ℤ) - n) n a
    (ExternallyGraded.degreeCast (R := F) (X := (S.H X).piece)
      (show (0 : ℤ) = 2 * (S.dimension X : ℤ) - (2 * (S.dimension Z : ℤ) - n + n) by omega)
      (S.H X).one)
  rw [hA1, hpush] at key
  refine Eq.trans ?_ (congrArg (ExternallyGraded.degreeCast (R := F) (X := (S.H Z).piece)
    (show 2 * (S.dimension Z : ℤ) - (2 * (S.dimension Z : ℤ) - n) = n by omega)) key).symm
  refine eq_of_heq
    ((ExternallyGraded.degreeCast_heq (R := F) (X := (S.H Z).piece) _ _).trans ?_)
  refine HEq.trans ?_
    (((ExternallyGraded.degreeCast_heq (R := F) (X := (S.H Z).piece) _ _).trans
      (ExternallyGraded.degreeCast_heq (R := F) (X := (S.H Z).piece) _ _)).symm)
  exact (ExternallyGradedAlgebra.mul_degreeCast_heq (A := S.H Z) n
      (2 * (S.dimension Z : ℤ) - 2 * (S.dimension Z : ℤ)) 0 (by omega) a _).trans
    (ExternallyGradedAlgebra.mul_degreeCast_heq (A := S.H Z) n
      (2 * (S.dimension Z : ℤ) - 2 * (S.dimension Z : ℤ))
      (2 * (S.dimension Z : ℤ) - (2 * (S.dimension Z : ℤ) - n + n)) (by omega) a _).symm

/-- Restriction to the two components of a disjoint union is injective in every degree: if
`1 = e + f` in `H^0(Z)` and cup product with `e`, resp. `f`, is `i_* ∘ i^*`, resp. `j_* ∘ j^*`,
then `a = i_*(i^*a) + j_*(j^*a)`, so a class restricting to zero on both components vanishes. -/
@[stacks 0FHJ "injectivity of restriction to the two components"]
theorem pullbackPair_injective (i : X ⟶ Z) (j : Y ⟶ Z) (e f : (S.H Z).piece 0)
    (hone : (S.H Z).one = e + f)
    (pushX : ∀ n : ℤ, (S.H X).piece n →ₗ[F] (S.H Z).piece n)
    (pushY : ∀ n : ℤ, (S.H Y).piece n →ₗ[F] (S.H Z).piece n)
    (hpushX : ∀ (n : ℤ) (a : (S.H Z).piece n),
      ExternallyGraded.degreeCast (R := F) (X := (S.H Z).piece) (add_zero n)
          ((S.H Z).mul n 0 a e) = pushX n (S.pullback i n a))
    (hpushY : ∀ (n : ℤ) (a : (S.H Z).piece n),
      ExternallyGraded.degreeCast (R := F) (X := (S.H Z).piece) (add_zero n)
          ((S.H Z).mul n 0 a f) = pushY n (S.pullback j n a))
    (n : ℤ) :
    Function.Injective ((S.pullback i n).prod (S.pullback j n)) := by
  have key : ∀ a : (S.H Z).piece n,
      a = pushX n (S.pullback i n a) + pushY n (S.pullback j n a) := by
    intro a
    rw [← hpushX, ← hpushY, ← map_add,
      show (S.H Z).mul n 0 a e + (S.H Z).mul n 0 a f = (S.H Z).mul n 0 a (S.H Z).one by
        rw [hone, map_add]]
    exact ((S.H Z).degreeCast_mul_one n a).symm
  intro a b hab
  have h1 : S.pullback i n a = S.pullback i n b := congrArg Prod.fst hab
  have h2 : S.pullback j n a = S.pullback j n b := congrArg Prod.snd hab
  rw [key a, key b, h1, h2]

/-- Restriction to the two components of a disjoint union is surjective in every degree: if the
idempotents `e`, `f` of `H^0(Z)` restrict to `1`, `0` on `X` and to `0`, `1` on `Y`, and each of
`i^*`, `j^*` is surjective, then `a ∪ e + a' ∪ f` restricts to `i^*a` on `X` and to `j^*a'` on
`Y`. -/
@[stacks 0FHJ "surjectivity of restriction to the two components"]
theorem pullbackPair_surjective (i : X ⟶ Z) (j : Y ⟶ Z) (e f : (S.H Z).piece 0)
    (hie : S.pullback i 0 e = (S.H X).one) (hif : S.pullback i 0 f = 0)
    (hje : S.pullback j 0 e = 0) (hjf : S.pullback j 0 f = (S.H Y).one)
    (hi : ∀ n : ℤ, Function.Surjective (S.pullback i n))
    (hj : ∀ n : ℤ, Function.Surjective (S.pullback j n))
    (n : ℤ) :
    Function.Surjective ((S.pullback i n).prod (S.pullback j n)) := by
  have hpull : ∀ {W : (SmoothProjective k).FullSubcategory} (g : W ⟶ Z)
      (a : (S.H Z).piece n) (u : (S.H Z).piece 0),
      S.pullback g n (ExternallyGraded.degreeCast (R := F) (X := (S.H Z).piece) (add_zero n)
          ((S.H Z).mul n 0 a u)) =
        ExternallyGraded.degreeCast (R := F) (X := (S.H W).piece) (add_zero n)
          ((S.H W).mul n 0 (S.pullback g n a) (S.pullback g 0 u)) := by
    intro W g a u
    rw [S.pullback_degreeCast, S.pullback_mul]
  rintro ⟨b, c⟩
  obtain ⟨a, ha⟩ := hi n b
  obtain ⟨a', ha'⟩ := hj n c
  set z : (S.H Z).piece n :=
    ExternallyGraded.degreeCast (R := F) (X := (S.H Z).piece) (add_zero n)
        ((S.H Z).mul n 0 a e) +
      ExternallyGraded.degreeCast (R := F) (X := (S.H Z).piece) (add_zero n)
        ((S.H Z).mul n 0 a' f) with hz
  have h1 : S.pullback i n z = b := by
    rw [hz, map_add, hpull i a e, hpull i a' f, hie, hif, ha]
    simp [(S.H X).degreeCast_mul_one n b]
  have h2 : S.pullback j n z = c := by
    rw [hz, map_add, hpull j a e, hpull j a' f, hje, hjf, ha']
    simp [(S.H Y).degreeCast_mul_one n c]
  exact ⟨z, Prod.ext h1 h2⟩

/-- The cycle class `γ([X]) = i_*1` of a component of a disjoint union, as a class in `H^0(Z)`:
the pushforward of the unit of `H^0(X)` along `i`, read in degree `0`. -/
noncomputable def pushforwardOne (i : X ⟶ Z) (hd : S.dimension X = S.dimension Z) :
    (S.H Z).piece 0 :=
  ExternallyGraded.degreeCast (R := F) (X := (S.H Z).piece)
    (show 2 * (S.dimension Z : ℤ) - 2 * (S.dimension Z : ℤ) = 0 by omega)
    (S.pushforward i (2 * (S.dimension Z : ℤ))
      (ExternallyGraded.degreeCast (R := F) (X := (S.H X).piece)
        (show (0 : ℤ) = 2 * (S.dimension X : ℤ) - 2 * (S.dimension Z : ℤ) by omega)
        (S.H X).one))

/-- Restriction to the two components of a disjoint union is injective in every degree, for
components of the same dimension as the union, given the decomposition
`1 = γ([X]) + γ([Y]) = i_*1 + j_*1` of the unit of `H^0(Z)` into orthogonal idempotents. -/
@[stacks 0FHJ "injectivity of restriction to the two components"]
theorem pullbackPair_injective_of_pushforward_one (i : X ⟶ Z) (j : Y ⟶ Z)
    (hdX : S.dimension X = S.dimension Z) (hdY : S.dimension Y = S.dimension Z)
    (hone : (S.H Z).one = S.pushforwardOne i hdX + S.pushforwardOne j hdY) (n : ℤ) :
    Function.Injective ((S.pullback i n).prod (S.pullback j n)) :=
  S.pullbackPair_injective i j _ _ hone
    (fun n => (ExternallyGraded.degreeCast (R := F) (X := (S.H Z).piece)
        (show 2 * (S.dimension Z : ℤ) - (2 * (S.dimension Z : ℤ) - n) = n by omega)).comp
      ((S.pushforward i (2 * (S.dimension Z : ℤ) - n)).comp
        (ExternallyGraded.degreeCast (R := F) (X := (S.H X).piece)
          (show n = 2 * (S.dimension X : ℤ) - (2 * (S.dimension Z : ℤ) - n) by omega))))
    (fun n => (ExternallyGraded.degreeCast (R := F) (X := (S.H Z).piece)
        (show 2 * (S.dimension Z : ℤ) - (2 * (S.dimension Z : ℤ) - n) = n by omega)).comp
      ((S.pushforward j (2 * (S.dimension Z : ℤ) - n)).comp
        (ExternallyGraded.degreeCast (R := F) (X := (S.H Y).piece)
          (show n = 2 * (S.dimension Y : ℤ) - (2 * (S.dimension Z : ℤ) - n) by omega))))
    (fun n a => S.mul_pushforward_one i hdX n a)
    (fun n a => S.mul_pushforward_one j hdY n a) n

/-- For `X` and `Y` smooth projective over `k` of the same dimension as their disjoint union `Z`,
with coprojections `i`, `j`, the map `H^n(Z) ⟶ H^n(X) × H^n(Y)`, `a ↦ (i^*a, j^*a)`, is bijective
in every degree, given the decomposition `1 = i_*1 + j_*1` of the unit of `H^0(Z)`, the
restrictions `i^*(i_*1) = 1`, `i^*(j_*1) = 0`, `j^*(i_*1) = 0`, `j^*(j_*1) = 1`, and surjectivity
of `i^*` and `j^*`. -/
@[stacks 0FHJ "restriction to the two components is bijective"]
theorem pullbackPair_bijective (i : X ⟶ Z) (j : Y ⟶ Z)
    (hdX : S.dimension X = S.dimension Z) (hdY : S.dimension Y = S.dimension Z)
    (hone : (S.H Z).one = S.pushforwardOne i hdX + S.pushforwardOne j hdY)
    (hie : S.pullback i 0 (S.pushforwardOne i hdX) = (S.H X).one)
    (hif : S.pullback i 0 (S.pushforwardOne j hdY) = 0)
    (hje : S.pullback j 0 (S.pushforwardOne i hdX) = 0)
    (hjf : S.pullback j 0 (S.pushforwardOne j hdY) = (S.H Y).one)
    (hi : ∀ n : ℤ, Function.Surjective (S.pullback i n))
    (hj : ∀ n : ℤ, Function.Surjective (S.pullback j n))
    (n : ℤ) :
    Function.Bijective ((S.pullback i n).prod (S.pullback j n)) :=
  ⟨S.pullbackPair_injective_of_pushforward_one i j hdX hdY hone n,
    S.pullbackPair_surjective i j _ _ hie hif hje hjf hi hj n⟩

/-- The isomorphism `H^n(X ⨿ Y) ≃ H^n(X) × H^n(Y)` given by restriction to the two
coprojections, in each degree `n`, under the hypotheses of `pullbackPair_bijective`. -/
@[stacks 0FHJ "the isomorphism onto the product of the cohomologies of the components"]
noncomputable def pullbackPairEquiv (i : X ⟶ Z) (j : Y ⟶ Z)
    (hdX : S.dimension X = S.dimension Z) (hdY : S.dimension Y = S.dimension Z)
    (hone : (S.H Z).one = S.pushforwardOne i hdX + S.pushforwardOne j hdY)
    (hie : S.pullback i 0 (S.pushforwardOne i hdX) = (S.H X).one)
    (hif : S.pullback i 0 (S.pushforwardOne j hdY) = 0)
    (hje : S.pullback j 0 (S.pushforwardOne i hdX) = 0)
    (hjf : S.pullback j 0 (S.pushforwardOne j hdY) = (S.H Y).one)
    (hi : ∀ n : ℤ, Function.Surjective (S.pullback i n))
    (hj : ∀ n : ℤ, Function.Surjective (S.pullback j n))
    (n : ℤ) :
    (S.H Z).piece n ≃ₗ[F] (S.H X).piece n × (S.H Y).piece n :=
  LinearEquiv.ofBijective _
    (S.pullbackPair_bijective i j hdX hdY hone hie hif hje hjf hi hj n)

end PoincareDualityPushforwardSetup

end Stacks.WeilCohomology

end
