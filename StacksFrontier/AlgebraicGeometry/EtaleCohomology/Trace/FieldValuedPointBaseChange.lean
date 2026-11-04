module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ArithmeticFrobeniusInverse
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FieldValuedPointSum
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.TraceFormulaDimensionOne

/-!
# `K`-valued points as rational points of the base change

For a scheme `X` over a field `k` and an extension `K` of `k`, the `K`-valued points of `X` over
`k` are the `K`-rational points of the base change `X_K = X ×_k K`: a section `s` of
`X_K ⟶ Spec K` gives `s ≫ pr₁ : Spec K ⟶ X` over `k`, and a `K`-valued point `y` gives the section
`(y, id)`.

## Main definitions

* `Stacks.EtaleCohomology.rationalPointsBaseChangeEquiv`: the rational points of `X ×_k K` as the
  `K`-valued points of `X`.

## Main results

* `Stacks.EtaleCohomology.finsum_rationalPoints_baseChange_eq_sum`: a sum over the rational
  points of `X_K` of a function of the image point in `X`, regrouped by closed points.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

open Stacks.Frobenius

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (K : Type u) [Field K]
  [Algebra k K]

/-- **The rational points of the base change `X ×_k K` are the `K`-valued points of `X`.** -/
def rationalPointsBaseChangeEquiv :
    rationalPoints (pullback.snd f (specAlgebraMap k K)) ≃ fieldValuedPoints f K where
  toFun s := ⟨s.1 ≫ pullback.fst f (specAlgebraMap k K), by
    rw [Category.assoc, pullback.condition, ← Category.assoc, s.2, Category.id_comp]⟩
  invFun y := ⟨pullback.lift y.1 (𝟙 _) (by rw [y.2, Category.id_comp]), pullback.lift_snd _ _ _⟩
  left_inv s := Subtype.ext (pullback.hom_ext (pullback.lift_fst _ _ _)
    (by rw [pullback.lift_snd]; exact s.2.symm))
  right_inv y := Subtype.ext (pullback.lift_fst _ _ _)

/-- `rationalPointsBaseChangeEquiv` sends a section `s` of `X ×_k K ⟶ Spec K` to `s ≫ pr₁`. -/
theorem rationalPointsBaseChangeEquiv_apply
    (s : rationalPoints (pullback.snd f (specAlgebraMap k K))) :
    (rationalPointsBaseChangeEquiv f K s).1 = s.1 ≫ pullback.fst f (specAlgebraMap k K) := rfl

variable [Finite K] [Finite k] [LocallyOfFiniteType f] [QuasiCompact f]

/-- **Regrouping a sum over the rational points of `X ×_k K` by closed points of `X`.** -/
theorem finsum_rationalPoints_baseChange_eq_sum {M : Type*} [AddCommMonoid M] (F : X → M) :
    ∑ᶠ s : rationalPoints (pullback.snd f (specAlgebraMap k K)),
        F ((s.1 ≫ pullback.fst f (specAlgebraMap k K)) (IsLocalRing.closedPoint K)) =
      ∑ x ∈ (closedPointsDegreeLE f (Module.finrank k K)).filter
        (fun x => residueDegree f x.1 ∣ Module.finrank k K), residueDegree f x.1 • F x.1 := by
  rw [← finsum_fieldValuedPoints_eq_sum f K F,
    ← finsum_comp_equiv (rationalPointsBaseChangeEquiv f K)]
  rfl

end Stacks.EtaleCohomology
