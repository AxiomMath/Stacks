module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.Topology.Sheaves.Sheafify
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.TotalQuotient

/-!
# A scheme whose structure sheaf is its sheaf of meromorphic functions

Let `A` be the complex polynomial algebra on `x` and one variable `y α` for each complex
number `α`, modulo the relations `(x - α) y α` and all products `y α * y β`. Every element of
`A` has a unique expression as a polynomial in `x` plus a finitely supported complex linear
combination of the `y α`. On every principal open of `Spec A` every nonzerodivisor is a unit,
so the structure sheaf of `Spec A` is canonically its sheaf of meromorphic functions. This is
the standard example showing that the sheaf of meromorphic functions can fail to be larger
than the structure sheaf even on a non-reduced scheme with embedded points.

## Main definitions

* `AlgebraicGeometry.NoChange.noChangeRing`: the quotient ring `A`.
* `AlgebraicGeometry.NoChange.x`, `AlgebraicGeometry.NoChange.y`: its displayed generators.
* `AlgebraicGeometry.NoChange.normalForm`: the displayed normal-form expression, as a map from
  pairs (polynomial, finitely supported family) to `A`.

## Main results

* `AlgebraicGeometry.NoChange.normalForm_bijective`: existence and uniqueness of the normal
  form.
* `AlgebraicGeometry.NoChange.isUnit_of_isRegular_localizationAway`: each localization `A_f` is
  its own total quotient ring.
* `AlgebraicGeometry.NoChange.isIso_toTotalQuotientSheaf`: the canonical map identifies the
  structure sheaf with the sheaf of meromorphic functions.

## Implementation notes

The variable type `Option ℂ` uses `none` for `x` and `some α` for `y α`. The family of
coefficients of the `y α` is a finitely supported function. The last result uses the canonical
morphism to the sheafification of the total quotient presheaf and checks that it is an
isomorphism on stalks.

## References

* [Stacks Project, Tag 01X3](https://stacks.math.columbia.edu/tag/01X3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry.NoChange

/-- The relations `(x - α)y_α = 0` and `y_α y_β = 0`. -/
def relationIdeal : Ideal (MvPolynomial (Option ℂ) ℂ) :=
  Ideal.span
    ((Set.range fun α : ℂ =>
      (MvPolynomial.X none - MvPolynomial.C α) * MvPolynomial.X (some α)) ∪
     (Set.range fun p : ℂ × ℂ =>
       MvPolynomial.X (some p.1) * MvPolynomial.X (some p.2)))

/-- The ring `ℂ[x, {y_α}]/((x-α)y_α, y_α y_β)`. -/
@[stacks 01X3 "the ring"]
abbrev noChangeRing := MvPolynomial (Option ℂ) ℂ ⧸ relationIdeal

/-- The class of `x` in the example ring. -/
def x : noChangeRing := Ideal.Quotient.mk relationIdeal (MvPolynomial.X none)

/-- The class of `y_α` in the example ring. -/
def y (α : ℂ) : noChangeRing :=
  Ideal.Quotient.mk relationIdeal (MvPolynomial.X (some α))

/-- Evaluate a polynomial and a finitely supported family of coefficients in the
displayed normal form. -/
def normalForm (v : Polynomial ℂ × (ℂ →₀ ℂ)) : noChangeRing :=
  Polynomial.eval₂ (algebraMap ℂ noChangeRing) x v.1 +
    v.2.sum (fun α c => algebraMap ℂ noChangeRing c * y α)

private abbrev normalFormModel := TrivSqZeroExt (Polynomial ℂ) (ℂ → ℂ)

private def evalPolynomialAtPoints : Polynomial ℂ →+* (ℂ → ℂ) :=
  RingHom.pi fun α => Polynomial.eval₂RingHom (RingHom.id ℂ) α

private def unopPolynomialRingHom : (Polynomial ℂ)ᵐᵒᵖ →+* Polynomial ℂ where
  toFun := MulOpposite.unop
  map_one' := rfl
  map_mul' a b := by simp [mul_comm]
  map_zero' := rfl
  map_add' a b := rfl

private instance : Module (Polynomial ℂ) (ℂ → ℂ) :=
  Module.compHom _ evalPolynomialAtPoints

private instance : Module (Polynomial ℂ)ᵐᵒᵖ (ℂ → ℂ) :=
  Module.compHom _ (evalPolynomialAtPoints.comp unopPolynomialRingHom)

private instance : IsCentralScalar (Polynomial ℂ) (ℂ → ℂ) := ⟨fun _ _ => rfl⟩

private noncomputable def normalFormModelEval :
    MvPolynomial (Option ℂ) ℂ →+* normalFormModel :=
  MvPolynomial.eval₂Hom ((TrivSqZeroExt.inlHom (Polynomial ℂ) (ℂ → ℂ)).comp
      Polynomial.C) (fun i =>
    match i with
    | none => TrivSqZeroExt.inl Polynomial.X
    | some α => TrivSqZeroExt.inr (fun β => if β = α then 1 else 0))

private lemma normalFormModelEval_relationIdeal_le_ker :
    relationIdeal ≤ RingHom.ker normalFormModelEval := by
  apply Ideal.span_le.mpr
  rintro _p (⟨α, rfl⟩ | ⟨⟨α, β⟩, rfl⟩)
  · change normalFormModelEval
      ((MvPolynomial.X none - MvPolynomial.C α) * MvPolynomial.X (some α)) = 0
    simp only [normalFormModelEval, map_mul, map_sub, MvPolynomial.eval₂Hom_X',
      MvPolynomial.eval₂Hom_C, RingHom.comp_apply, TrivSqZeroExt.inlHom_apply]
    rw [← TrivSqZeroExt.inl_sub, TrivSqZeroExt.inl_mul_inr]
    apply congrArg TrivSqZeroExt.inr
    ext γ
    change (evalPolynomialAtPoints (Polynomial.X - Polynomial.C α)) γ *
      (if γ = α then (1 : ℂ) else 0) = 0
    by_cases h : γ = α <;> simp [h, evalPolynomialAtPoints]
  · change normalFormModelEval
      (MvPolynomial.X (some α) * MvPolynomial.X (some β)) = 0
    simp only [normalFormModelEval, map_mul, MvPolynomial.eval₂Hom_X']
    rw [TrivSqZeroExt.inr_mul_inr]

private noncomputable def normalFormModelMap : noChangeRing →+* normalFormModel :=
  Ideal.Quotient.lift relationIdeal normalFormModelEval
    (fun _p hp => normalFormModelEval_relationIdeal_le_ker hp)

private lemma normalFormModelMap_coeff (c : ℂ) :
    normalFormModelMap (algebraMap ℂ noChangeRing c) =
      TrivSqZeroExt.inl (Polynomial.C c) := by
  change normalFormModelEval (MvPolynomial.C c) = _
  simp [normalFormModelEval]

private lemma normalFormModelMap_x : normalFormModelMap x =
    TrivSqZeroExt.inl Polynomial.X := by
  change normalFormModelEval (MvPolynomial.X none) = _
  simp [normalFormModelEval]

private lemma normalFormModelMap_y_gen (α : ℂ) :
    normalFormModelMap (y α) =
      TrivSqZeroExt.inr (fun β => if β = α then (1 : ℂ) else 0) := by
  change normalFormModelEval (MvPolynomial.X (some α)) = _
  simp [normalFormModelEval]

private lemma normalFormModelMap_poly (p : Polynomial ℂ) :
    normalFormModelMap (Polynomial.eval₂ (algebraMap ℂ noChangeRing) x p) =
      TrivSqZeroExt.inl p := by
  let f : Polynomial ℂ →+* normalFormModel :=
    normalFormModelMap.comp (Polynomial.eval₂RingHom (algebraMap ℂ noChangeRing) x)
  let g : Polynomial ℂ →+* normalFormModel := TrivSqZeroExt.inlHom _ _
  have hfg : f = g := by
    apply Polynomial.ringHom_ext
    · intro c
      change normalFormModelMap
        (Polynomial.eval₂ (algebraMap ℂ noChangeRing) x (Polynomial.C c)) = _
      rw [Polynomial.eval₂_C]
      exact normalFormModelMap_coeff c
    · change normalFormModelMap
        (Polynomial.eval₂ (algebraMap ℂ noChangeRing) x Polynomial.X) = _
      rw [Polynomial.eval₂_X]
      exact normalFormModelMap_x
  exact DFunLike.congr_fun hfg p

private lemma normalFormModelMap_y (c α : ℂ) :
    normalFormModelMap (algebraMap ℂ noChangeRing c * y α) =
      TrivSqZeroExt.inr (fun β => if β = α then c else 0) := by
  classical
  rw [map_mul, normalFormModelMap_coeff, normalFormModelMap_y_gen, TrivSqZeroExt.inl_mul_inr]
  apply congrArg TrivSqZeroExt.inr
  ext β
  change (evalPolynomialAtPoints (Polynomial.C c)) β *
    (if β = α then (1 : ℂ) else 0) = (if β = α then c else 0)
  by_cases h : β = α <;> simp [h, evalPolynomialAtPoints]

private lemma normalFormModelMap_nil_sum (s : ℂ →₀ ℂ) :
    normalFormModelMap (s.sum fun α c => algebraMap ℂ noChangeRing c * y α) =
      TrivSqZeroExt.inr (fun α => s α) := by
  classical
  change normalFormModelMap
    (∑ α ∈ s.support, algebraMap ℂ noChangeRing (s α) * y α) = _
  rw [map_sum]
  apply TrivSqZeroExt.ext
  · rw [TrivSqZeroExt.fst_sum]
    simp [normalFormModelMap_y]
  · rw [TrivSqZeroExt.snd_sum, TrivSqZeroExt.snd_inr]
    ext β
    simp [normalFormModelMap_y, Finsupp.mem_support_iff]
    all_goals simp_all

private lemma normalFormModelMap_normalForm (v : Polynomial ℂ × (ℂ →₀ ℂ)) :
    normalFormModelMap (normalForm v) = (v.1, fun α => v.2 α) := by
  classical
  rcases v with ⟨p, s⟩
  rw [normalForm, map_add, normalFormModelMap_poly, normalFormModelMap_nil_sum]
  apply TrivSqZeroExt.ext
  · rw [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr]
    simp
  · rw [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr]
    simp

private lemma normalForm_injective : Function.Injective normalForm := by
  intro v w hvw
  have hm := congrArg normalFormModelMap hvw
  rw [normalFormModelMap_normalForm, normalFormModelMap_normalForm] at hm
  rcases Prod.ext_iff.mp hm with ⟨hp, hs⟩
  exact Prod.ext (by simpa using hp) (Finsupp.ext fun α => congrFun hs α)

private lemma normalForm_add (v w : Polynomial ℂ × (ℂ →₀ ℂ)) :
    normalForm (v.1 + w.1, v.2 + w.2) = normalForm v + normalForm w := by
  classical
  let h : ℂ → ℂ → noChangeRing := fun α c => algebraMap ℂ noChangeRing c * y α
  have hsum : (v.2 + w.2).sum h = v.2.sum h + w.2.sum h := by
    apply Finsupp.sum_add_index
    · intro α hα
      simp [h]
    · intro α hα c d
      simp [h, map_add, add_mul]
  simp only [normalForm, Polynomial.eval₂_add]
  rw [hsum]
  ring

private lemma x_mul_y (α : ℂ) : x * y α = algebraMap ℂ noChangeRing α * y α := by
  have hrel : (x - algebraMap ℂ noChangeRing α) * y α = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Or.inl ⟨α, rfl⟩))
  linear_combination hrel

private lemma y_mul_y (α β : ℂ) : y α * y β = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Or.inr ⟨(α, β), rfl⟩))

private lemma polynomial_mul_y (p : Polynomial ℂ) (α : ℂ) :
    Polynomial.eval₂ (algebraMap ℂ noChangeRing) x p * y α =
      algebraMap ℂ noChangeRing (p.eval α) * y α := by
  obtain ⟨q, hq⟩ := Polynomial.X_sub_C_dvd_sub_C_eval (p := p) (a := α)
  have hEval := congrArg (Polynomial.eval₂ (algebraMap ℂ noChangeRing) x) hq
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_X,
    Polynomial.eval₂_C] at hEval
  have hrel : (x - algebraMap ℂ noChangeRing α) * y α = 0 := by
    rw [sub_mul, x_mul_y, sub_self]
  linear_combination y α * hEval + Polynomial.eval₂ (algebraMap ℂ noChangeRing) x q * hrel

private lemma normalForm_mul_y (v : Polynomial ℂ × (ℂ →₀ ℂ)) (α : ℂ) :
    normalForm v * y α =
      normalForm (0, Finsupp.single α ((v.1).eval α)) := by
  classical
  rcases v with ⟨p, s⟩
  unfold normalForm
  rw [add_mul, polynomial_mul_y]
  have hs : (s.sum fun β c => algebraMap ℂ noChangeRing c * y β) * y α = 0 := by
    simp only [Finsupp.sum]
    rw [Finset.sum_mul]
    apply Finset.sum_eq_zero
    intro β hβ
    rw [mul_assoc, y_mul_y, mul_zero]
  rw [hs, add_zero]
  simp [Finsupp.sum_single_index]

private noncomputable def xShift (s : ℂ →₀ ℂ) : ℂ →₀ ℂ :=
  Finsupp.onFinset s.support (fun α => α * s α)
    fun α hα => Finsupp.mem_support_iff.mpr fun hs => hα (by simp [hs])

private lemma xShift_support_subset (s : ℂ →₀ ℂ) :
    (xShift s).support ⊆ s.support := by
  classical
  intro α hα
  have hmem : α ∈ s.support.filter (fun a => a * s a ≠ 0) := by
    simpa only [xShift, Finsupp.support_onFinset] using hα
  exact (Finset.mem_filter.mp hmem).1

private lemma normalForm_mul_x (v : Polynomial ℂ × (ℂ →₀ ℂ)) :
    normalForm v * x = normalForm (v.1 * Polynomial.X, xShift v.2) := by
  classical
  rcases v with ⟨p, s⟩
  unfold normalForm
  rw [add_mul]
  have hp : Polynomial.eval₂ (algebraMap ℂ noChangeRing) x p * x =
      Polynomial.eval₂ (algebraMap ℂ noChangeRing) x (p * Polynomial.X) := by
    simp [Polynomial.eval₂_mul]
  rw [hp]
  have hs : (s.sum fun α c => algebraMap ℂ noChangeRing c * y α) * x =
      (xShift s).sum (fun α c => algebraMap ℂ noChangeRing c * y α) := by
    classical
    change (∑ α ∈ s.support, algebraMap ℂ noChangeRing (s α) * y α) * x = _
    rw [Finset.sum_mul]
    rw [Finsupp.sum_of_support_subset (f := xShift s) (xShift_support_subset s)
      (fun α c => algebraMap ℂ noChangeRing c * y α) (by simp)]
    apply Finset.sum_congr rfl
    intro α hα
    calc
      algebraMap ℂ noChangeRing (s α) * y α * x =
          algebraMap ℂ noChangeRing (s α) * (y α * x) := by rw [← mul_assoc]
      _ = algebraMap ℂ noChangeRing (s α) * (x * y α) := by ring
      _ = algebraMap ℂ noChangeRing (s α) *
          (algebraMap ℂ noChangeRing α * y α) := by rw [x_mul_y]
      _ = algebraMap ℂ noChangeRing ((xShift s) α) * y α := by
        simp [xShift, ← map_mul, mul_comm, mul_left_comm]
  rw [hs]

private lemma exists_normalForm_for_polynomial (p : MvPolynomial (Option ℂ) ℂ) :
    ∃ v, Ideal.Quotient.mk relationIdeal p = normalForm v := by
  induction p using MvPolynomial.induction_on with
  | C c =>
      refine ⟨(Polynomial.C c, 0), ?_⟩
      simp [normalForm, Polynomial.eval₂_C]
      rfl
  | add p q hp hq =>
      rcases hp with ⟨v, hv⟩
      rcases hq with ⟨w, hw⟩
      refine ⟨(v.1 + w.1, v.2 + w.2), ?_⟩
      rw [map_add, hv, hw, normalForm_add]
  | mul_X p i hp =>
      rcases hp with ⟨v, hv⟩
      cases i with
      | none =>
          refine ⟨(v.1 * Polynomial.X, xShift v.2), ?_⟩
          rw [map_mul, hv]
          change normalForm v * x = _
          exact normalForm_mul_x v
      | some α =>
          refine ⟨(0, Finsupp.single α (v.1.eval α)), ?_⟩
          rw [map_mul, hv]
          change normalForm v * y α = _
          exact normalForm_mul_y v α

private lemma polynomial_dvd_pow_of_root_subset {p q : Polynomial ℂ}
    (hp : p ≠ 0) (hq : q ≠ 0)
    (hroot : ∀ α, p.IsRoot α → q.IsRoot α) : p ∣ q ^ p.natDegree := by
  classical
  apply (IsAlgClosed.dvd_iff_roots_le_roots hp (pow_ne_zero _ hq)).2
  rw [Multiset.le_iff_count]
  intro α
  by_cases hα : p.IsRoot α
  · have hqα := hroot α hα
    have hpcount : p.roots.count α ≤ p.natDegree :=
      (Multiset.count_le_card α p.roots).trans IsAlgClosed.card_roots_eq_natDegree.le
    have hqcount : 0 < q.roots.count α :=
      Multiset.count_pos.mpr ((Polynomial.mem_roots hq).2 hqα)
    simpa [Polynomial.roots_pow, Multiset.count_nsmul,
      Polynomial.count_roots] using
      le_trans hpcount (Nat.le_mul_of_pos_right p.natDegree hqcount)
  · have hnot : α ∉ p.roots := fun h => hα ((Polynomial.mem_roots hp).1 h)
    simp [Multiset.count_eq_zero.mpr hnot]

private noncomputable def pointEval (α : ℂ) :
    noChangeRing →+* TrivSqZeroExt ℂ ℂ := by
  let F : MvPolynomial (Option ℂ) ℂ →+* TrivSqZeroExt ℂ ℂ :=
    MvPolynomial.eval₂Hom (TrivSqZeroExt.inlHom ℂ ℂ) fun i =>
      match i with
      | none => TrivSqZeroExt.inl α
      | some β => TrivSqZeroExt.inr (if β = α then 1 else 0)
  have hF : relationIdeal ≤ RingHom.ker F := by
    apply Ideal.span_le.mpr
    rintro _p (⟨β, rfl⟩ | ⟨⟨β, γ⟩, rfl⟩)
    · change F ((MvPolynomial.X none - MvPolynomial.C β) * MvPolynomial.X (some β)) = 0
      simp only [F, map_mul, map_sub, MvPolynomial.eval₂Hom_X',
        MvPolynomial.eval₂Hom_C]
      by_cases h : β = α <;> simp [h]
    · change F (MvPolynomial.X (some β) * MvPolynomial.X (some γ)) = 0
      simp only [F, map_mul, MvPolynomial.eval₂Hom_X']
      rw [TrivSqZeroExt.inr_mul_inr]
  exact Ideal.Quotient.lift relationIdeal F (fun p hp => hF hp)

private lemma pointEval_y (α β : ℂ) :
    pointEval α (y β) = TrivSqZeroExt.inr (if β = α then 1 else 0) := by
  change (MvPolynomial.eval₂Hom (TrivSqZeroExt.inlHom ℂ ℂ) _)
    (MvPolynomial.X (some β)) = _
  simp

private lemma pointEval_x (α : ℂ) :
    pointEval α x = TrivSqZeroExt.inl α := by
  change (MvPolynomial.eval₂Hom (TrivSqZeroExt.inlHom ℂ ℂ) _)
    (MvPolynomial.X none) = _
  simp

private lemma pointEval_coeff (α c : ℂ) :
    pointEval α (algebraMap ℂ noChangeRing c) = TrivSqZeroExt.inl c := by
  change (MvPolynomial.eval₂Hom (TrivSqZeroExt.inlHom ℂ ℂ) _)
    (MvPolynomial.C c) = _
  simp

private lemma pointEval_poly (α : ℂ) (p : Polynomial ℂ) :
    pointEval α (Polynomial.eval₂ (algebraMap ℂ noChangeRing) x p) =
      TrivSqZeroExt.inl (p.eval α) := by
  have hcomp : (pointEval α).comp (algebraMap ℂ noChangeRing) =
      TrivSqZeroExt.inlHom ℂ ℂ := by
    ext c
    · exact congrArg TrivSqZeroExt.fst (pointEval_coeff α c)
    · exact congrArg TrivSqZeroExt.snd (pointEval_coeff α c)
  rw [Polynomial.hom_eval₂, pointEval_x, hcomp]
  change Polynomial.eval₂ (TrivSqZeroExt.inlHom ℂ ℂ)
    ((TrivSqZeroExt.inlHom ℂ ℂ) α) p = _
  rw [Polynomial.eval₂_at_apply]
  rfl

private lemma pointEval_normalForm_fst (α : ℂ)
    (v : Polynomial ℂ × (ℂ →₀ ℂ)) :
    (pointEval α (normalForm v)).fst = v.1.eval α := by
  classical
  rcases v with ⟨p, s⟩
  unfold normalForm
  rw [map_add, TrivSqZeroExt.fst_add, pointEval_poly]
  have hs : (pointEval α (s.sum fun β c => algebraMap ℂ noChangeRing c * y β)).fst = 0 := by
    change (pointEval α (∑ β ∈ s.support, algebraMap ℂ noChangeRing (s β) * y β)).fst = 0
    rw [map_sum, TrivSqZeroExt.fst_sum]
    simp [pointEval_coeff, pointEval_y, TrivSqZeroExt.inl_mul_inr]
  rw [hs]
  simp [TrivSqZeroExt.fst_inl]

private lemma root_subset_of_localization_regular (f b : noChangeRing)
    (vf vb : Polynomial ℂ × (ℂ →₀ ℂ)) (hf : f = normalForm vf)
    (hb : b = normalForm vb)
    (hreg : IsRegular (algebraMap noChangeRing (Localization.Away f) b)) :
    ∀ α, vb.1.IsRoot α → vf.1.IsRoot α := by
  intro α hpα
  by_contra hq
  have hqne : vf.1.eval α ≠ 0 := fun h => hq (Polynomial.IsRoot.def.mpr h)
  have hpointunit : IsUnit (pointEval α f) := by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, hf, pointEval_normalForm_fst]
    exact isUnit_iff_ne_zero.mpr hqne
  let e : Localization.Away f →+* TrivSqZeroExt ℂ ℂ :=
    Localization.awayLift (pointEval α) f hpointunit
  have hecomp : e.comp (algebraMap noChangeRing (Localization.Away f)) = pointEval α :=
    IsLocalization.Away.lift_comp f hpointunit
  have hby : b * y α = 0 := by
    rw [hb, normalForm_mul_y]
    simp [Polynomial.IsRoot.def.mp hpα, normalForm]
  have hlocal : algebraMap noChangeRing (Localization.Away f) b *
      algebraMap noChangeRing (Localization.Away f) (y α) = 0 := by
    rw [← map_mul, hby, map_zero]
  have hy0 : algebraMap noChangeRing (Localization.Away f) (y α) = 0 :=
    (isLeftRegular_iff_right_eq_zero_of_mul.mp hreg.left) _ hlocal
  have he_y : e (algebraMap noChangeRing (Localization.Away f) (y α)) =
      TrivSqZeroExt.inr (1 : ℂ) := by
    rw [← RingHom.comp_apply, hecomp, pointEval_y]
    simp
  have hzero := congrArg e hy0
  rw [he_y] at hzero
  have hfalse := congrArg TrivSqZeroExt.snd hzero
  simp at hfalse

private lemma nilPart_sq (s : ℂ →₀ ℂ) :
    (s.sum fun α c => algebraMap ℂ noChangeRing c * y α) ^ 2 = 0 := by
  classical
  simp only [pow_two, Finsupp.sum]
  rw [Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro α hα
  rw [Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro β hβ
  rw [mul_mul_mul_comm, y_mul_y, mul_zero]

private lemma isUnit_add_sq_zero {R : Type*} [CommRing R] {u n : R}
    (hu : IsUnit u) (hn : n * n = 0) : IsUnit (u + n) := by
  obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.mp hu
  exact isUnit_iff_exists_inv.mpr
    ⟨v - v * n * v, by linear_combination (1 - n * v) * hv - v ^ 2 * hn⟩

private lemma isUnit_sub_sq_zero {R : Type*} [CommRing R] {u n : R}
    (hu : IsUnit u) (hn : n * n = 0) : IsUnit (u - n) := by
  rw [sub_eq_add_neg]
  exact isUnit_add_sq_zero hu (by simpa using hn)

private lemma exists_eval_ne_zero (q : Polynomial ℂ) (hq : q ≠ 0) :
    ∃ α, q.eval α ≠ 0 :=
  Polynomial.exists_eval_ne_zero_of_natDegree_lt_card q hq
    (Cardinal.natCast_lt_aleph0.trans_le (Cardinal.aleph0_le_mk ℂ))

/-- Every element of the example ring has a unique displayed normal form. -/
@[stacks 01X3 "unique normal form"]
theorem normalForm_bijective : Function.Bijective normalForm := by
  refine ⟨normalForm_injective, fun a => ?_⟩
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨v, hv⟩ := exists_normalForm_for_polynomial p
  exact ⟨v, hv.symm⟩

/-- On every principal open of `Spec A`, a nonzerodivisor is a unit. -/
@[stacks 01X3 "nonzerodivisors on principal opens"]
theorem isUnit_of_isRegular_localizationAway (f : noChangeRing)
    (a : Localization.Away f) (ha : IsRegular a) : IsUnit a := by
  classical
  obtain ⟨b, ⟨_, n, rfl⟩, rfl⟩ :=
    IsLocalization.exists_mk'_eq (Submonoid.powers f) a
  let L := Localization.Away f
  let den : (Submonoid.powers f) :=
    ⟨f ^ n, Submonoid.pow_mem _ (Submonoid.mem_powers f) n⟩
  have hdenUnit : IsUnit (algebraMap noChangeRing L (f ^ n)) :=
    IsLocalization.map_units L den
  have hspec : IsLocalization.mk' L b den * algebraMap noChangeRing L (f ^ n) =
      algebraMap noChangeRing L b := IsLocalization.mk'_spec L b den
  have hbreg : IsRegular (algebraMap noChangeRing L b) := by
    rw [← hspec]
    exact ha.mul hdenUnit.isRegular
  obtain ⟨vb, hb⟩ := normalForm_bijective.2 b
  obtain ⟨vf, hf⟩ := normalForm_bijective.2 f
  have hb : b = normalForm vb := hb.symm
  have hfUnit : IsUnit (algebraMap noChangeRing L f) :=
    IsLocalization.map_units L ⟨f, Submonoid.mem_powers f⟩
  have hnil (w : ℂ →₀ ℂ) :
      algebraMap noChangeRing L (w.sum fun α c => algebraMap ℂ noChangeRing c * y α) *
        algebraMap noChangeRing L (w.sum fun α c => algebraMap ℂ noChangeRing c * y α) = 0 := by
    rw [← map_mul, ← pow_two, nilPart_sq, map_zero]
  by_cases hq : vf.1 = 0
  · have hfSq : f * f = 0 := by
      rw [← hf]
      simpa [normalForm, hq, pow_two] using nilPart_sq vf.2
    have hfsq : algebraMap noChangeRing L f * algebraMap noChangeRing L f = 0 := by
      rw [← map_mul, hfSq, map_zero]
    have hfzero : algebraMap noChangeRing L f = 0 :=
      (isLeftRegular_iff_right_eq_zero_of_mul.mp hfUnit.isRegular.left) _ hfsq
    obtain ⟨u, hu⟩ := isUnit_iff_exists_inv.mp hfUnit
    have h01 : (0 : L) = 1 := by
      calc
        0 = algebraMap noChangeRing L f * u := by rw [hfzero]; simp
        _ = 1 := hu
    apply isUnit_iff_exists_inv.mpr
    refine ⟨0, ?_⟩
    calc
      (IsLocalization.mk' L b den) * 0 = 0 := mul_zero _
      _ = 1 := h01
  · let pA := Polynomial.eval₂ (algebraMap ℂ noChangeRing) x vb.1
    let qA := Polynomial.eval₂ (algebraMap ℂ noChangeRing) x vf.1
    let nilB := vb.2.sum fun α c => algebraMap ℂ noChangeRing c * y α
    let nilF := vf.2.sum fun α c => algebraMap ℂ noChangeRing c * y α
    have hroot := root_subset_of_localization_regular f b vf vb hf.symm hb hbreg
    obtain ⟨α, hα⟩ := exists_eval_ne_zero vf.1 hq
    have hpα : ¬ vb.1.IsRoot α := by
      intro hp
      have hqroot := hroot α hp
      exact hα (Polynomial.IsRoot.def.mp hqroot)
    have hp : vb.1 ≠ 0 := by
      intro hzero
      apply hpα
      rw [hzero]
      exact Polynomial.IsRoot.def.mpr (by simp)
    obtain ⟨r, hr⟩ := polynomial_dvd_pow_of_root_subset hp hq hroot
    have hfdecomp : f = qA + nilF := by
      rw [← hf]
      rfl
    have hbdecomp : b = pA + nilB := by
      rw [hb]
      rfl
    have hqUnit : IsUnit (algebraMap noChangeRing L qA) := by
      have hqEq : algebraMap noChangeRing L qA =
          algebraMap noChangeRing L f - algebraMap noChangeRing L nilF := by
        rw [← map_sub, show f - nilF = qA by rw [hfdecomp]; ring]
      rw [hqEq]
      exact isUnit_sub_sq_zero hfUnit (hnil vf.2)
    have hprod :
        (algebraMap noChangeRing L qA) ^ vb.1.natDegree =
          algebraMap noChangeRing L pA *
            algebraMap noChangeRing L
              (Polynomial.eval₂ (algebraMap ℂ noChangeRing) x r) := by
      rw [← map_pow, ← Polynomial.eval₂_pow, ← map_mul, ← Polynomial.eval₂_mul, hr]
    have hpUnit : IsUnit (algebraMap noChangeRing L pA) := by
      apply isUnit_of_mul_isUnit_left
      rw [← hprod]
      exact hqUnit.pow _
    have hbUnit : IsUnit (algebraMap noChangeRing L b) := by
      rw [hbdecomp, map_add]
      exact isUnit_add_sq_zero hpUnit (hnil vb.2)
    apply isUnit_of_mul_isUnit_left
    rw [IsLocalization.mk'_spec]
    exact hbUnit

private lemma totalQuotientSubmonoid_basicOpen
    (f : Γ(Spec (.of noChangeRing), ⊤)) :
    ((Spec (.of noChangeRing)).presheaf.submonoidPresheafOfStalk
      (fun z ↦ nonZeroDivisors ((Spec (.of noChangeRing)).presheaf.stalk z))).obj
        (Opposite.op ((Spec (.of noChangeRing)).basicOpen f)) =
      nonZeroDivisors Γ(Spec (.of noChangeRing), (Spec (.of noChangeRing)).basicOpen f) :=
  AlgebraicGeometry.submonoidPresheafOfStalk_obj_eq_nonZeroDivisors _ _
    ((isAffineOpen_top _).basicOpen f)

private lemma isRegular_symm_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) {s : S} (hs : IsRegular s) : IsRegular (e.symm s) :=
  ⟨fun a b hab => e.injective (hs.left (by simpa using congrArg e hab)),
    fun a b hab => e.injective (hs.right (by simpa using congrArg e hab))⟩

private lemma nonZeroDivisors_le_units_basicOpen
    (f : Γ(Spec (.of noChangeRing), ⊤)) :
    nonZeroDivisors Γ(Spec (.of noChangeRing), (Spec (.of noChangeRing)).basicOpen f) ≤
      IsUnit.submonoid Γ(Spec (.of noChangeRing), (Spec (.of noChangeRing)).basicOpen f) := by
  let X := Spec (.of noChangeRing)
  let U := X.basicOpen f
  have : IsLocalization.Away f Γ(X, U) := (isAffineOpen_top X).isLocalization_basicOpen f
  let e0 : noChangeRing ≃+* Γ(X, ⊤) :=
    (Scheme.ΓSpecIso (.of noChangeRing)).symm.commRingCatIsoToRingEquiv
  let r := e0.symm f
  have hr : e0 r = f := e0.apply_symm_apply f
  have hbij : Function.Bijective (Localization.awayMap e0.toRingHom r) := by
    constructor
    · rw [Localization.awayMap_injective_iff]
      intro a ha
      have ha0 : a = 0 := e0.injective (by simpa using ha)
      exact ⟨0, by simp [ha0]⟩
    · rw [Localization.awayMap_surjective_iff]
      intro a
      exact ⟨e0.symm a, 0, by simp⟩
  let eAway : Localization.Away r ≃+* Localization.Away f := by
    rw [← hr]
    exact RingEquiv.ofBijective (Localization.awayMap e0.toRingHom r) hbij
  let e1 := IsLocalization.algEquiv (Submonoid.powers f)
    (Localization.Away f) Γ(X, U)
  let e : Localization.Away r ≃+* Γ(X, U) := eAway.trans e1.toRingEquiv
  intro s hs
  change IsUnit s
  have hsreg : IsRegular s := isRegular_iff_mem_nonZeroDivisors.mpr hs
  have hreg : IsRegular (e.symm s) := isRegular_symm_ringEquiv e hsreg
  simpa using (isUnit_of_isRegular_localizationAway r (e.symm s) hreg).map e.toRingHom

private lemma totalQuotientMap_app_isIso_basicOpen
    (f : Γ(Spec (.of noChangeRing), ⊤)) :
    IsIso ((Spec (.of noChangeRing)).presheaf.toTotalQuotientPresheaf.app
      (Opposite.op ((Spec (.of noChangeRing)).basicOpen f))) := by
  let X := Spec (.of noChangeRing)
  let U := X.basicOpen f
  let S := X.presheaf.submonoidPresheafOfStalk
    (fun z ↦ nonZeroDivisors (X.presheaf.stalk z))
  have hS : S.obj (Opposite.op U) = nonZeroDivisors Γ(X, U) :=
    totalQuotientSubmonoid_basicOpen f
  let Astd : Algebra Γ(X, U) (S.localizationPresheaf.obj (Opposite.op U)) := inferInstance
  have hAlg : (X.presheaf.toTotalQuotientPresheaf.app (Opposite.op U)).hom.toAlgebra = Astd := by
    apply Algebra.algebra_ext
    intro r
    rfl
  let : Algebra Γ(X, U) (S.localizationPresheaf.obj (Opposite.op U)) :=
    (X.presheaf.toTotalQuotientPresheaf.app (Opposite.op U)).hom.toAlgebra
  have : IsLocalization (nonZeroDivisors Γ(X, U))
      (S.localizationPresheaf.obj (Opposite.op U)) := by
    change @IsLocalization (Γ(X, U)) _ (nonZeroDivisors Γ(X, U))
      (S.localizationPresheaf.obj (Opposite.op U)) _
      ((X.presheaf.toTotalQuotientPresheaf.app (Opposite.op U)).hom.toAlgebra)
    rw [← hS]
    exact hAlg.symm ▸ (inferInstance : @IsLocalization (Γ(X, U)) _
      (S.obj (Opposite.op U)) (S.localizationPresheaf.obj (Opposite.op U)) _ Astd)
  apply (ConcreteCategory.isIso_iff_bijective _).2
  change Function.Bijective
    (algebraMap Γ(X, U) (S.localizationPresheaf.obj (Opposite.op U)))
  exact (IsLocalization.atUnits Γ(X, U) (nonZeroDivisors Γ(X, U))
    (nonZeroDivisors_le_units_basicOpen f)).toEquiv.bijective

private lemma isIso_stalk_toTotalQuotientPresheaf
    (z : Spec (.of noChangeRing)) :
    IsIso ((TopCat.Presheaf.stalkFunctor CommRingCat z).map
      (Spec (.of noChangeRing)).presheaf.toTotalQuotientPresheaf) := by
  let X := Spec (.of noChangeRing)
  have hB := isBasis_basicOpen X
  apply (ConcreteCategory.isIso_iff_bijective _).2
  constructor
  · apply TopCat.Presheaf.stalkFunctor_map_injective_of_isBasis hB
    intro U hU
    obtain ⟨f, rfl⟩ := hU
    exact (ConcreteCategory.isIso_iff_bijective _).mp
      (totalQuotientMap_app_isIso_basicOpen f) |>.1
  · intro t
    obtain ⟨U, hzU, hU, s, hs⟩ :=
      TopCat.Presheaf.exists_mem_germ_eq_of_isBasis hB X.presheaf.totalQuotientPresheaf z t
    obtain ⟨f, rfl⟩ := hU
    obtain ⟨a, ha⟩ := ((ConcreteCategory.isIso_iff_bijective _).mp
      (totalQuotientMap_app_isIso_basicOpen f)).2 s
    refine ⟨X.presheaf.germ (X.basicOpen f) z hzU a, ?_⟩
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply, ha, hs]

/-- The canonical map from the structure sheaf of `Spec A` to its sheaf of
meromorphic functions is an isomorphism. -/
@[stacks 01X3 "equality of sheaves"]
theorem isIso_toTotalQuotientSheaf :
    IsIso (Scheme.toTotalQuotientSheaf
      (Spec (.of noChangeRing))) := by
  let X := Spec (.of noChangeRing)
  have hloc (z : X) : IsIso ((TopCat.Presheaf.stalkFunctor CommRingCat z).map
      X.presheaf.toTotalQuotientPresheaf) := isIso_stalk_toTotalQuotientPresheaf z
  have hsh (z : X) : IsIso ((TopCat.Presheaf.stalkFunctor CommRingCat z).map
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
        X.presheaf.totalQuotientPresheaf)) :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso z CommRingCat
      X.presheaf.totalQuotientPresheaf
  let : ∀ z : X, IsIso ((TopCat.Presheaf.stalkFunctor CommRingCat z).map
      ((Scheme.toTotalQuotientSheaf X).hom)) := by
    intro z
    change IsIso ((TopCat.Presheaf.stalkFunctor CommRingCat z).map
      (X.presheaf.toTotalQuotientPresheaf ≫
        CategoryTheory.toSheafify (Opens.grothendieckTopology X)
          X.presheaf.totalQuotientPresheaf))
    rw [Functor.map_comp]
    exact IsIso.comp_isIso' (hloc z) (hsh z)
  exact TopCat.Presheaf.isIso_of_stalkFunctor_map_iso _

end AlgebraicGeometry.NoChange
