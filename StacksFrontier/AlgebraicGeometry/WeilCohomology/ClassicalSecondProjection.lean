module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ClassicalTheory
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ProjectionFormula.SecondProjection

/-!
# Pushforward along the second projection in a classical Weil cohomology theory

Let `P` be a fibre product of smooth projective varieties `X` and `Y` over `k`, with projections
`p : P ⟶ X` and `q : P ⟶ Y`. The Poincaré-duality pushforward along `q` integrates the first
factor out of an exterior product: `q_*(p^*a ∪ q^*b) = (∫_X a) b`, where `∫_X`, a functional on
the top degree `2 dim X` only, is read as zero in every other degree.

## Main definitions

* `ExternallyGradedAlgebra.traceExtension`: a functional on the piece of degree `2d`, extended by
  zero to every other piece.

## Main results

* `Stacks.WeilCohomology.PoincareDualityPushforwardSetup.dimension_eq_add_of_bijective`: if the
  Künneth map of `P` is bijective then `dim P = dim X + dim Y`.
* `Stacks.WeilCohomology.ClassicalWeilCohomologyTheory.dimension_eq_add`: the fibre product of
  two smooth projective varieties has dimension `dim X + dim Y`, for the dimensions recorded by a
  classical Weil cohomology theory.
* `Stacks.WeilCohomology.PoincareDualityPushforwardSetup.pushforward_mul_pullback_of_trace_mul`:
  if the trace of `P` factors as `∫_P (p^*c ∪ q^*c') = ∫_X c · ∫_Y c'` on top classes, then
  `q_*(p^*a ∪ q^*b) = (∫_X a) b`.

## Implementation notes

The product is an arbitrary smooth projective variety `P` with two morphisms exhibiting it as the
fibre product of the structure morphisms, exactly as in the Künneth axiom of
`Stacks.WeilCohomology.ClassicalWeilCohomologyTheory`; no products are constructed inside the
category of smooth projective varieties. The trace extended by zero, `traceExtension`, absorbs
the degree bookkeeping: the trace pairing in complementary degrees is `traceExtension` of a cup
product, and `traceExtension` takes heterogeneously equal arguments of equal degrees to the same
value, so no transport between graded pieces survives into the computations.

## References

* [Stacks Project, Tag 0FGY](https://stacks.math.columbia.edu/tag/0FGY)
-/

open AlgebraicGeometry

@[expose] public section

open CategoryTheory DifferentialGraded

open scoped DirectSum TensorProduct

universe u v w t

namespace ExternallyGradedAlgebra

variable {F : Type v} [Field F] (A : ExternallyGradedAlgebra.{v, w} F) (d : ℕ)
  (integration : A.piece (2 * (d : ℤ)) →ₗ[F] F)

/-- A functional `∫` on the piece of degree `2d`, extended by zero to the piece of degree `n`:
it is `∫` on the piece of degree `2d` and zero on every other piece. -/
noncomputable def traceExtension (n : ℤ) : A.piece n →ₗ[F] F :=
  integration ∘ₗ DirectSum.component F ℤ A.piece (2 * (d : ℤ)) ∘ₗ DirectSum.lof F ℤ A.piece n

/-- On a piece of degree `n = 2d`, the extended trace is `∫` applied to the class transported to
the piece of degree `2d`. -/
theorem traceExtension_of_eq {n : ℤ} (h : n = 2 * (d : ℤ)) (a : A.piece n) :
    A.traceExtension d integration n a =
      integration (ExternallyGraded.degreeCast (R := F) (X := A.piece) h a) := by
  subst h
  simp [traceExtension, ExternallyGraded.degreeCast]

/-- On the piece of degree `2d`, the extended trace is `∫`. -/
@[simp]
theorem traceExtension_self (a : A.piece (2 * (d : ℤ))) :
    A.traceExtension d integration (2 * (d : ℤ)) a = integration a := by
  simp [traceExtension]

/-- On a piece of degree `n ≠ 2d`, the extended trace is zero. -/
theorem traceExtension_of_ne {n : ℤ} (h : n ≠ 2 * (d : ℤ)) (a : A.piece n) :
    A.traceExtension d integration n a = 0 := by
  simp [traceExtension, DirectSum.component.of, h]

/-- The extended trace takes heterogeneously equal classes of equal degrees to the same value. -/
theorem traceExtension_congr {n n' : ℤ} (h : n = n') {a : A.piece n} {a' : A.piece n'}
    (ha : a ≍ a') :
    A.traceExtension d integration n a = A.traceExtension d integration n' a' := by
  subst h
  rw [eq_of_heq ha]

/-- The trace pairing in complementary degrees is the extended trace of the cup product. -/
theorem tracePairing_eq_traceExtension (i : ℤ) (a : A.piece i) (b : A.piece (2 * (d : ℤ) - i)) :
    A.tracePairing d integration i a b =
      A.traceExtension d integration (i + (2 * (d : ℤ) - i)) (A.mul i (2 * (d : ℤ) - i) a b) := by
  rw [traceExtension_of_eq A d integration (by omega)]
  rfl

end ExternallyGradedAlgebra

namespace Stacks.WeilCohomology

/-- The Künneth map on a tensor product of two homogeneous classes is their exterior product,
placed in the summand of the sum of their degrees. -/
theorem kunnethMap_lof_tmul_lof {F : Type v} [Field F]
    (A B D : ExternallyGradedAlgebra.{v, w} F)
    (p : ∀ i : ℤ, A.piece i →ₗ[F] D.piece i) (q : ∀ j : ℤ, B.piece j →ₗ[F] D.piece j)
    (i j : ℤ) (a : A.piece i) (b : B.piece j) :
    kunnethMap A B D p q (DirectSum.lof F ℤ A.piece i a ⊗ₜ DirectSum.lof F ℤ B.piece j b) =
      DirectSum.lof F ℤ D.piece (i + j) (D.mul i j (p i a) (q j b)) := by
  simp [kunnethMap, TensorProduct.directSum_lof_tmul_lof]

variable {k : Type u} [Field k] [IsAlgClosed k] {F : Type v} [Field F] [CharZero F]
  {X Y P : (SmoothProjective k).FullSubcategory}

namespace PoincareDualityPushforwardSetup

variable (S : PoincareDualityPushforwardSetup.{u, v, w} k F)

/-- An exterior product `p^*a ∪ q^*b` vanishes if `a` or `b` lies above the top degree of its
own variety. -/
private theorem mul_pullback_eq_zero_of_or (p : P ⟶ X) (q : P ⟶ Y) {i j : ℤ}
    (h : 2 * (S.dimension X : ℤ) < i ∨ 2 * (S.dimension Y : ℤ) < j)
    (a : (S.H X).piece i) (b : (S.H Y).piece j) :
    (S.H P).mul i j (S.pullback p i a) (S.pullback q j b) = 0 := by
  rcases h with hi | hj
  · rw [S.bounded X i (.inr hi) a]
    simp
  · rw [S.bounded Y j (.inr hj) b]
    simp

/-- An exterior product `p^*a ∪ q^*b` of degree above `2 dim X + 2 dim Y` vanishes, since one of
its two factors lies above the top degree of its own variety. -/
theorem mul_pullback_eq_zero_of_lt (p : P ⟶ X) (q : P ⟶ Y) {i j : ℤ}
    (h : 2 * (S.dimension X : ℤ) + 2 * (S.dimension Y : ℤ) < i + j)
    (a : (S.H X).piece i) (b : (S.H Y).piece j) :
    (S.H P).mul i j (S.pullback p i a) (S.pullback q j b) = 0 :=
  S.mul_pullback_eq_zero_of_or p q (by omega) a b

/-- **The dimension of a product.** If the Künneth map `H^*(X) ⊗_F H^*(Y) → H^*(P)`,
`a ⊗ b ↦ p^*a ∪ q^*b`, is bijective, then `dim P = dim X + dim Y`: surjectivity forces the top
piece `H^{2 dim P}(P) ≅ F` into degrees at most `2 dim X + 2 dim Y`, and injectivity keeps the
exterior product of two top classes, of degree `2 dim X + 2 dim Y`, nonzero. -/
theorem dimension_eq_add_of_bijective (p : P ⟶ X) (q : P ⟶ Y)
    (hK : Function.Bijective
      (Stacks.WeilCohomology.kunnethMap (S.H X) (S.H Y) (S.H P) (fun i => S.pullback p i)
        fun j => S.pullback q j)) :
    S.dimension P = S.dimension X + S.dimension Y := by
  set K := Stacks.WeilCohomology.kunnethMap (S.H X) (S.H Y) (S.H P) (fun i => S.pullback p i)
    fun j => S.pullback q j
  have hle : 2 * (S.dimension P : ℤ) ≤ 2 * (S.dimension X : ℤ) + 2 * (S.dimension Y : ℤ) := by
    by_contra hlt
    have hzero : ∀ x,
        DirectSum.component F ℤ (S.H P).piece (2 * (S.dimension P : ℤ)) (K x) = 0 := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp [hx, hy]
      | tmul x y =>
        induction x using DirectSum.induction_on with
        | zero => simp
        | add x x' hx hx' => simp [TensorProduct.add_tmul, hx, hx']
        | of i a =>
          induction y using DirectSum.induction_on with
          | zero => simp
          | add y y' hy hy' => simp [TensorProduct.tmul_add, hy, hy']
          | of j b =>
            rw [← DirectSum.lof_eq_of F, ← DirectSum.lof_eq_of F, kunnethMap_lof_tmul_lof]
            by_cases hij : i + j = 2 * (S.dimension P : ℤ)
            · rw [S.mul_pullback_eq_zero_of_lt p q (by omega) a b]
              simp
            · simp [DirectSum.component.of, hij]
    obtain ⟨x, hx⟩ := hK.2 (DirectSum.lof F ℤ (S.H P).piece _ ((S.integration P).symm 1))
    have := hzero x
    rw [hx, DirectSum.component.lof_self] at this
    simpa using congrArg (S.integration P) this
  have hge : 2 * (S.dimension X : ℤ) + 2 * (S.dimension Y : ℤ) ≤ 2 * (S.dimension P : ℤ) := by
    by_contra hlt
    set c := (S.integration X).symm 1
    set c' := (S.integration Y).symm 1
    have hKc : K (DirectSum.lof F ℤ _ _ c ⊗ₜ DirectSum.lof F ℤ _ _ c') = K 0 := by
      rw [kunnethMap_lof_tmul_lof, S.bounded P _ (.inr (by omega)) (((S.H P).mul _ _) _ _)]
      simp
    have h0 := congrArg (TensorProduct.lift ((LinearMap.mul F F).compl₁₂
      ((S.integration X).toLinearMap ∘ₗ
        DirectSum.component F ℤ (S.H X).piece (2 * (S.dimension X : ℤ)))
      ((S.integration Y).toLinearMap ∘ₗ
        DirectSum.component F ℤ (S.H Y).piece (2 * (S.dimension Y : ℤ))))) (hK.1 hKc)
    simp [c, c'] at h0
  omega

/-- Moving a class pulled back from the second factor past the first factor of an exterior
product: `q^*v ∪ (p^*a ∪ q^*b) = (-1)^{ji} p^*a ∪ q^*(v ∪ b)` for `v` of degree `j` and `a` of
degree `i`, heterogeneously. -/
theorem mul_pullback_mul_heq (p : P ⟶ X) (q : P ⟶ Y) (j i l : ℤ) (v : (S.H Y).piece j)
    (a : (S.H X).piece i) (b : (S.H Y).piece l) :
    (S.H P).mul j (i + l) (S.pullback q j v)
        ((S.H P).mul i l (S.pullback p i a) (S.pullback q l b)) ≍
      gradedSign F (j * i) •
        (S.H P).mul i (j + l) (S.pullback p i a) (S.pullback q (j + l) ((S.H Y).mul j l v b)) := by
  rw [S.pullback_mul q j l v b]
  refine ((S.H P).mul_assoc j i l _ _ _).symm.trans ?_
  refine (ExternallyGradedAlgebra.mul_congr_left_heq (A := S.H P) (by ring)
    ((S.gradedComm P).graded_comm j i _ _) _).trans ?_
  rw [map_smul, LinearMap.smul_apply]
  exact ExternallyGraded.scalar_heq (by ring) rfl ((S.H P).mul_assoc i j l _ _ _)

/-- The factorisation `∫_P (p^*c ∪ q^*c') = ∫_X c · ∫_Y c'` of the trace on top classes, extended
to classes of all degrees: with each trace extended by zero off the top degree,
`∫_P (p^*a ∪ q^*b) = ∫_X a · ∫_Y b` for every `a` and `b`. -/
theorem traceExtension_mul_pullback (p : P ⟶ X) (q : P ⟶ Y)
    (hdim : S.dimension P = S.dimension X + S.dimension Y)
    (htrace : ∀ (c : (S.H X).piece (2 * (S.dimension X : ℤ)))
        (c' : (S.H Y).piece (2 * (S.dimension Y : ℤ))),
      S.integration P (ExternallyGraded.degreeCast (R := F) (X := (S.H P).piece)
          (show 2 * (S.dimension X : ℤ) + 2 * (S.dimension Y : ℤ) =
              2 * (S.dimension P : ℤ) by rw [hdim]; push_cast; ring)
          ((S.H P).mul _ _ (S.pullback p _ c) (S.pullback q _ c'))) =
        S.integration X c * S.integration Y c')
    (i j : ℤ) (a : (S.H X).piece i) (b : (S.H Y).piece j) :
    (S.H P).traceExtension (S.dimension P) (S.integration P).toLinearMap (i + j)
        ((S.H P).mul i j (S.pullback p i a) (S.pullback q j b)) =
      (S.H X).traceExtension (S.dimension X) (S.integration X).toLinearMap i a *
        (S.H Y).traceExtension (S.dimension Y) (S.integration Y).toLinearMap j b := by
  by_cases hi : i = 2 * (S.dimension X : ℤ)
  · subst hi
    by_cases hj : j = 2 * (S.dimension Y : ℤ)
    · subst hj
      rw [ExternallyGradedAlgebra.traceExtension_of_eq _ _ _ (by rw [hdim]; push_cast; ring)]
      simpa using htrace a b
    · rw [ExternallyGradedAlgebra.traceExtension_of_ne _ _ _ (by rw [hdim]; push_cast; omega),
        ExternallyGradedAlgebra.traceExtension_of_ne _ _ _ hj, mul_zero]
  · rw [ExternallyGradedAlgebra.traceExtension_of_ne _ _ _ hi, zero_mul]
    by_cases hij : i + j = 2 * (S.dimension P : ℤ)
    · rw [S.mul_pullback_eq_zero_of_or p q (by omega) a b]
      simp
    · exact ExternallyGradedAlgebra.traceExtension_of_ne _ _ _ hij _

/-- **Pushforward along the second projection.** Let `P` have morphisms `p : P ⟶ X` and
`q : P ⟶ Y` with `dim P = dim X + dim Y`, and suppose the trace of `P` factors on top classes as
`∫_P (p^*c ∪ q^*c') = ∫_X c · ∫_Y c'`. Then for `a` of degree `i` on `X` and `b` on `Y`,
`q_*(p^*a ∪ q^*b) = (∫_X a) b` when `i = 2 dim X`, and `q_*(p^*a ∪ q^*b) = 0` otherwise. -/
theorem pushforward_mul_pullback_of_trace_mul (p : P ⟶ X) (q : P ⟶ Y)
    (hdim : S.dimension P = S.dimension X + S.dimension Y)
    (htrace : ∀ (c : (S.H X).piece (2 * (S.dimension X : ℤ)))
        (c' : (S.H Y).piece (2 * (S.dimension Y : ℤ))),
      S.integration P (ExternallyGraded.degreeCast (R := F) (X := (S.H P).piece)
          (show 2 * (S.dimension X : ℤ) + 2 * (S.dimension Y : ℤ) =
              2 * (S.dimension P : ℤ) by rw [hdim]; push_cast; ring)
          ((S.H P).mul _ _ (S.pullback p _ c) (S.pullback q _ c'))) =
        S.integration X c * S.integration Y c')
    (i j : ℤ) (a : (S.H X).piece i) (b : (S.H Y).piece j) :
    S.pushforward q (2 * (S.dimension P : ℤ) - (i + j))
        (ExternallyGraded.degreeCast (R := F) (X := (S.H P).piece)
          (show i + j = 2 * (S.dimension P : ℤ) - (2 * (S.dimension P : ℤ) - (i + j)) by omega)
          ((S.H P).mul i j (S.pullback p i a) (S.pullback q j b))) =
      if h : i = 2 * (S.dimension X : ℤ) then
        S.integration X (ExternallyGraded.degreeCast (R := F) (X := (S.H X).piece) h a) •
          ExternallyGraded.degreeCast (R := F) (X := (S.H Y).piece)
            (show j = 2 * (S.dimension Y : ℤ) - (2 * (S.dimension P : ℤ) - (i + j)) by
              rw [hdim]; push_cast; omega) b
      else 0 := by
  set n := 2 * (S.dimension P : ℤ) - (i + j) with hn
  have := S.perfect Y n
  refine (LinearMap.IsPerfPair.bijective_right ((S.H Y).tracePairing (S.dimension Y)
    (S.integration Y).toLinearMap n)).injective (LinearMap.ext fun v ↦ ?_)
  show (S.H Y).tracePairing (S.dimension Y) (S.integration Y).toLinearMap n v _ =
    (S.H Y).tracePairing (S.dimension Y) (S.integration Y).toLinearMap n v _
  rw [← S.integration_pullback_mul q n v, ExternallyGradedAlgebra.tracePairing_eq_traceExtension,
    ExternallyGradedAlgebra.traceExtension_congr _ _ _ (show _ = i + (n + j) by omega)
      (((ExternallyGradedAlgebra.mul_degreeCast_heq _ _ _ _ _ _)).trans
        (S.mul_pullback_mul_heq p q n i j v a b)),
    map_smul, S.traceExtension_mul_pullback p q hdim htrace, smul_eq_mul]
  split_ifs with h
  · rw [map_smul, smul_eq_mul, ExternallyGradedAlgebra.tracePairing_eq_traceExtension,
      ExternallyGradedAlgebra.traceExtension_of_eq _ _ _ h,
      ExternallyGradedAlgebra.traceExtension_congr _ _ _ (show _ = n + j by omega)
        (ExternallyGradedAlgebra.mul_degreeCast_heq _ _ _ _ _ _),
      show n * i = 2 * (n * (S.dimension X : ℤ)) by rw [h]; ring, gradedSign_two_mul, one_mul]
    rfl
  · rw [ExternallyGradedAlgebra.traceExtension_of_ne _ _ _ h, map_zero, zero_mul,
      mul_zero]

end PoincareDualityPushforwardSetup

namespace ClassicalWeilCohomologyTheory

variable {Ch : ChowCycleData.{u, t} k} (T : ClassicalWeilCohomologyTheory.{u, v, w, t} k F Ch)

/-- **The dimension of a fibre product.** For `P` a fibre product of `X` and `Y` over `k`, the
dimensions recorded by a classical Weil cohomology theory satisfy `dim P = dim X + dim Y`; this
follows from the Künneth formula and Poincaré duality. -/
theorem dimension_eq_add (p : P ⟶ X) (q : P ⟶ Y)
    (hP : IsPullback p.hom.left q.hom.left X.obj.hom Y.obj.hom) :
    T.dimension P = T.dimension X + T.dimension Y :=
  T.dimension_eq_add_of_bijective p q (T.kunneth X Y P p q hP)

end ClassicalWeilCohomologyTheory

end Stacks.WeilCohomology

end
