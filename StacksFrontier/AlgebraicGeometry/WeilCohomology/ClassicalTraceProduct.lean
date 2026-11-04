module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ClassicalSecondProjection

/-!
# The trace map of a product in a classical Weil cohomology theory

Let `P` be a fibre product of smooth projective varieties `X` and `Y` over `k`, with projections
`p : P ⟶ X` and `q : P ⟶ Y`. Stacks 0FGX asserts `∫_P = ∫_X ⊗ ∫_Y`: on top classes,
`∫_P (p^*a ∪ q^*b) = ∫_X a · ∫_Y b`. Its proof has a cohomological half and a cycle-theoretic
half, and this file proves the cohomological half.

* Since `∫_X : H^{2 dim X}(X) → F` is an isomorphism, the top piece of `X` is a line, so the
  factorisation needs checking on one pair of classes only: if `∫_X u = 1`, `∫_Y v = 1` and
  `∫_P (p^*u ∪ q^*v) = 1`, then `∫_P (p^*a ∪ q^*b) = ∫_X a · ∫_Y b` for all top classes.
* The pushforward of the class of a point integrates to one: for a variety `Z` isomorphic to
  `Spec k` and a morphism `f : Z ⟶ X`, `∫_X γ(f_*[Z]) = 1`, by axiom `(C)(b)`, the trace equation
  defining `f_*`, and axiom `(C)(d)`. This holds for an arbitrary `ChowCycleData`.

What remains of the source's proof is the identity
`γ([x × y]) = p^*γ([x]) ∪ q^*γ([y])` for closed points `x`, `y`, which the source derives from
axioms `(C)(a)`, `(C)(c)` and the Chow identity `[x × y] = pr₁^![x] · pr₂^![y]`.
`Stacks.WeilCohomology.ClassicalWeilCohomologyTheory.integration_mul_pullback_of_cycleClass_point`
reduces Stacks 0FGX to that identity.

## Main results

* `PoincareDualityPushforwardSetup.integration_mul_pullback_of_eq_one`:
  the factorisation of the trace of `P` on top classes, from its value on one pair of classes.
* `ClassicalWeilCohomologyTheory.integration_cycleClass_pushforward_fundamental`:
  `∫_X γ(f_*[Z]) = 1` for `f : Z ⟶ X` out of a model `Z` of `Spec k`.
* `ClassicalWeilCohomologyTheory.integration_mul_pullback_of_cycleClass_point`:
  the factorisation of the trace of `P` on top classes, given points `x`, `y`, `z` of `X`, `Y`,
  `P` with `γ(z_*[Z]) = p^*γ(x_*[Z]) ∪ q^*γ(y_*[Z])`.

## Implementation notes

Over an arbitrary `ChowCycleData`, whose operations obey no laws, Stacks 0FGX is not a theorem:
rescaling `∫_X` by a nonzero constant depending on `X` and compensating in the cycle class map,
the Gysin pullback and the intersection product preserves every field of
`Stacks.WeilCohomology.ClassicalWeilCohomologyTheory` but not the multiplicativity of the trace.
That is why the identity on the class of a point is the hypothesis of the last result: on the
actual Chow groups it is a consequence of the axioms, on an arbitrary `ChowCycleData` it is not.

## References

* [Stacks Project, Tag 0FGX](https://stacks.math.columbia.edu/tag/0FGX)
* [Stacks Project, Tag 0FGW](https://stacks.math.columbia.edu/tag/0FGW)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u v w t

namespace Stacks.WeilCohomology

variable {k : Type u} [Field k] [IsAlgClosed k] {F : Type v} [Field F] [CharZero F]
  {X Y P : (SmoothProjective k).FullSubcategory}

namespace PoincareDualityPushforwardSetup

variable (S : PoincareDualityPushforwardSetup.{u, v, w} k F)

/-- **The trace of a product is determined by one value.** The top pieces of `X` and `Y` are
lines, so if `∫_X u = 1`, `∫_Y v = 1` and `∫_P (p^*u ∪ q^*v) = 1`, then
`∫_P (p^*a ∪ q^*b) = ∫_X a · ∫_Y b` for all classes `a`, `b` of top degree. -/
theorem integration_mul_pullback_of_eq_one (p : P ⟶ X) (q : P ⟶ Y)
    (hdim : S.dimension P = S.dimension X + S.dimension Y)
    (u : (S.H X).piece (2 * (S.dimension X : ℤ))) (v : (S.H Y).piece (2 * (S.dimension Y : ℤ)))
    (hu : S.integration X u = 1) (hv : S.integration Y v = 1)
    (huv : S.integration P (ExternallyGraded.degreeCast (R := F) (X := (S.H P).piece)
        (show 2 * (S.dimension X : ℤ) + 2 * (S.dimension Y : ℤ) = 2 * (S.dimension P : ℤ) by
          rw [hdim]; push_cast; ring)
        ((S.H P).mul _ _ (S.pullback p _ u) (S.pullback q _ v))) = 1)
    (a : (S.H X).piece (2 * (S.dimension X : ℤ))) (b : (S.H Y).piece (2 * (S.dimension Y : ℤ))) :
    S.integration P (ExternallyGraded.degreeCast (R := F) (X := (S.H P).piece)
        (show 2 * (S.dimension X : ℤ) + 2 * (S.dimension Y : ℤ) = 2 * (S.dimension P : ℤ) by
          rw [hdim]; push_cast; ring)
        ((S.H P).mul _ _ (S.pullback p _ a) (S.pullback q _ b))) =
      S.integration X a * S.integration Y b := by
  have ha : a = S.integration X a • u :=
    (S.integration X).injective (by rw [map_smul, hu, smul_eq_mul, mul_one])
  have hb : b = S.integration Y b • v :=
    (S.integration Y).injective (by rw [map_smul, hv, smul_eq_mul, mul_one])
  rw [ha, hb]
  simp only [map_smul, LinearMap.smul_apply, huv, hu, hv, smul_eq_mul, mul_one]
  ring

end PoincareDualityPushforwardSetup

namespace ClassicalWeilCohomologyTheory

variable {Ch : ChowCycleData.{u, t} k} (T : ClassicalWeilCohomologyTheory.{u, v, w, t} k F Ch)

/-- Multiplying a class, up to transport of degree, by the transported unit gives the class. -/
private theorem mul_degreeCast_one_heq {F : Type v} [Field F] (A : ExternallyGradedAlgebra.{v, w} F)
    {i m n : ℤ} (hi : i = 0) (hm : n = m) (c : A.piece n) :
    A.mul i m (ExternallyGraded.degreeCast (R := F) hi.symm A.one)
      (ExternallyGraded.degreeCast (R := F) hm c) ≍ c :=
  ((ExternallyGradedAlgebra.mul_congr_left_heq hi (ExternallyGraded.degreeCast_heq _ _) _).trans
    (A.one_mul _ _)).trans (ExternallyGraded.degreeCast_heq _ _)

/-- **The class of a point integrates to one.** Let `Z` be a model of `Spec k`, that is a
smooth projective variety whose structure morphism is an isomorphism and whose dimension is
zero, and let `f : Z ⟶ X`. Then `∫_X γ(f_*[Z]) = 1`. Indeed `γ(f_*[Z]) = f_*γ([Z])` by axiom
`(C)(b)`, the trace equation `∫_X 1 ∪ f_*c = ∫_Z f^*1 ∪ c` defining `f_*` gives
`∫_X f_*γ([Z]) = ∫_Z γ([Z])`, and the latter is `1` by axiom `(C)(d)`. -/
theorem integration_cycleClass_pushforward_fundamental (Z : (SmoothProjective k).FullSubcategory)
    (hZ : IsIso Z.obj.hom) (h0 : T.dimension Z = 0) (f : Z ⟶ X) :
    T.integration X (ExternallyGraded.degreeCast (R := F) (X := (T.H X).piece)
      (show 2 * (0 + (T.dimension X : ℤ) - (T.dimension Z : ℤ)) = 2 * (T.dimension X : ℤ) by
        rw [h0]; ring)
      (T.cycleClass X _ (Ch.pushforward f (T.dimension Z) (T.dimension X) (T.dimension_eq Z)
        (T.dimension_eq X) 0 (Ch.fundamental Z)))) = 1 := by
  have hi0 : (0 : ℤ) = 2 * (T.dimension Z : ℤ) - 2 * 0 := by rw [h0]; ring
  have key := T.integration_pullback_mul f (2 * (T.dimension Z : ℤ) - 2 * 0)
    (ExternallyGraded.degreeCast (R := F) (X := (T.H X).piece) hi0 (T.H X).one)
    (ExternallyGraded.degreeCast (R := F) (X := (T.H Z).piece)
      (show 2 * (0 : ℤ) = 2 * (T.dimension Z : ℤ) - (2 * (T.dimension Z : ℤ) - 2 * 0) by ring)
      (T.cycleClass Z 0 (Ch.fundamental Z)))
  rw [ExternallyGradedAlgebra.tracePairing_eq_traceExtension,
    ExternallyGradedAlgebra.tracePairing_eq_traceExtension,
    PoincareDualityPushforwardSetup.pullback_degreeCast, T.pullback_one,
    T.cycleClass_pushforward f 0 (Ch.fundamental Z)] at key
  refine Eq.trans ?_ (T.integration_cycleClass_fundamental Z hZ h0)
  refine (ExternallyGradedAlgebra.traceExtension_of_eq (T.H X) (T.dimension X)
    (T.integration X).toLinearMap (by rw [h0]; ring) _).symm.trans ?_
  refine Eq.trans ?_ (ExternallyGradedAlgebra.traceExtension_of_eq (T.H Z) (T.dimension Z)
    (T.integration Z).toLinearMap (by omega) _)
  refine (ExternallyGradedAlgebra.traceExtension_congr _ _ _ (by rw [h0]; ring) ?_).trans
    (key.symm.trans (ExternallyGradedAlgebra.traceExtension_congr _ _ _ (by rw [h0]; ring) ?_))
  · exact (mul_degreeCast_one_heq (T.H X) hi0.symm _ _).symm
  · exact mul_degreeCast_one_heq (T.H Z) hi0.symm _ _

/-- **The trace of a product, from the class of a point.** Let `P` be a fibre product of `X` and
`Y` over `k`, with projections `p` and `q`, and let `x : Z ⟶ X`, `y : Z ⟶ Y`, `z : Z ⟶ P` be
morphisms out of a model `Z` of `Spec k` with `γ(z_*[Z]) = p^*γ(x_*[Z]) ∪ q^*γ(y_*[Z])`. Then
`∫_P (p^*a ∪ q^*b) = ∫_X a · ∫_Y b` for all classes `a`, `b` of top degree.

This is the proof of Stacks 0FGX with its Chow-theoretic step left as the hypothesis `hz`: the
source obtains `hz` for `z = (x, y)` from axioms `(C)(a)` and `(C)(c)` and the identity
`[x × y] = pr₁^![x] · pr₂^![y]` of cycle classes. -/
theorem integration_mul_pullback_of_cycleClass_point (p : P ⟶ X) (q : P ⟶ Y)
    (hP : IsPullback p.hom.left q.hom.left X.obj.hom Y.obj.hom)
    (Z : (SmoothProjective k).FullSubcategory) (hZ : IsIso Z.obj.hom) (h0 : T.dimension Z = 0)
    (x : Z ⟶ X) (y : Z ⟶ Y) (z : Z ⟶ P)
    (hz : T.cycleClass P _ (Ch.pushforward z (T.dimension Z) (T.dimension P) (T.dimension_eq Z)
        (T.dimension_eq P) 0 (Ch.fundamental Z)) ≍
      (T.H P).mul _ _
        (T.pullback p _ (T.cycleClass X _ (Ch.pushforward x (T.dimension Z) (T.dimension X)
          (T.dimension_eq Z) (T.dimension_eq X) 0 (Ch.fundamental Z))))
        (T.pullback q _ (T.cycleClass Y _ (Ch.pushforward y (T.dimension Z) (T.dimension Y)
          (T.dimension_eq Z) (T.dimension_eq Y) 0 (Ch.fundamental Z)))))
    (a : (T.H X).piece (2 * (T.dimension X : ℤ))) (b : (T.H Y).piece (2 * (T.dimension Y : ℤ))) :
    T.integration P (ExternallyGraded.degreeCast (R := F) (X := (T.H P).piece)
        (show 2 * (T.dimension X : ℤ) + 2 * (T.dimension Y : ℤ) = 2 * (T.dimension P : ℤ) by
          rw [T.dimension_eq_add p q hP]; push_cast; ring)
        ((T.H P).mul _ _ (T.pullback p _ a) (T.pullback q _ b))) =
      T.integration X a * T.integration Y b := by
  have hdim := T.dimension_eq_add p q hP
  have hcast : ∀ {V : (SmoothProjective k).FullSubcategory} {n n' : ℤ} (h : n = n')
      (c : (T.H V).piece n), c ≍ ExternallyGraded.degreeCast (R := F) (X := (T.H V).piece) h c :=
    fun h c ↦ (ExternallyGraded.degreeCast_heq (R := F) h c).symm
  set u := ExternallyGraded.degreeCast (R := F) (X := (T.H X).piece)
    (show 2 * (0 + (T.dimension X : ℤ) - (T.dimension Z : ℤ)) = 2 * (T.dimension X : ℤ) by
      rw [h0]; ring)
    (T.cycleClass X _ (Ch.pushforward x (T.dimension Z) (T.dimension X) (T.dimension_eq Z)
      (T.dimension_eq X) 0 (Ch.fundamental Z))) with hu
  set v := ExternallyGraded.degreeCast (R := F) (X := (T.H Y).piece)
    (show 2 * (0 + (T.dimension Y : ℤ) - (T.dimension Z : ℤ)) = 2 * (T.dimension Y : ℤ) by
      rw [h0]; ring)
    (T.cycleClass Y _ (Ch.pushforward y (T.dimension Z) (T.dimension Y) (T.dimension_eq Z)
      (T.dimension_eq Y) 0 (Ch.fundamental Z))) with hv
  refine T.integration_mul_pullback_of_eq_one p q hdim u v
    (T.integration_cycleClass_pushforward_fundamental Z hZ h0 x)
    (T.integration_cycleClass_pushforward_fundamental Z hZ h0 y) ?_ a b
  rw [← T.integration_cycleClass_pushforward_fundamental Z hZ h0 z]
  congr 1
  refine eq_of_heq ((ExternallyGraded.degreeCast_heq (R := F) _ _).trans ?_)
  refine HEq.trans ?_ ((hz.symm).trans (hcast _ _))
  rw [hu, hv, PoincareDualityPushforwardSetup.pullback_degreeCast,
    PoincareDualityPushforwardSetup.pullback_degreeCast]
  exact (ExternallyGradedAlgebra.mul_congr_left_heq (A := T.H P) (by rw [h0]; ring)
    (ExternallyGraded.degreeCast_heq (R := F) _ _) _).trans
    (ExternallyGradedAlgebra.mul_degreeCast_heq _ _ _ _ _ _)

end ClassicalWeilCohomologyTheory

end Stacks.WeilCohomology

end
