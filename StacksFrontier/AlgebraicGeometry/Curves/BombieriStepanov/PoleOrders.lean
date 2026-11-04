module

public import StacksFrontier.AlgebraicGeometry.Curves.BombieriStepanov.Local
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.AffineOrProjective
public import StacksFrontier.AlgebraicGeometry.CurveLocalRing.Basic
public import StacksFrontier.NumberTheory.BombieriStepanov.Riemann

/-!
# Two functions with consecutive pole orders at a point of a proper curve

Let `X` be a proper curve over a field `k`, with a discrete valuation ring as local ring at every
closed point, and let `P₀` be a closed point of degree one. Then `X ∖ {P₀}` is affine
(`AlgebraicGeometry.isAffineOpen_compl_singleton_of_isCurve`), so the function field is the
fraction field of `A = Γ(X ∖ {P₀}, 𝒪_X)`. Write a uniformizer at `P₀` as `a / b` with `a, b ∈ A`.
Both have no pole outside `P₀`. Zeros are bounded by poles, so their orders at `P₀` are `≤ 0`;
they differ by one, so the pole orders are `e` and `e + 1` for some `e`. Riemann's inequality
`#L(o P₀) ≥ q ^ (o + 1 - e²)` follows (`Stacks.BombieriStepanov.pow_le_natCard_poleSpace`).

## Main results

* `Stacks.BombieriStepanov.zero_le_ord_germToFunctionField`: a section over an open `U` has no
  pole at the points of `U`.
* `Stacks.BombieriStepanov.exists_consecutive_poleOrders`: the two functions.
* `Stacks.BombieriStepanov.exists_pow_le_natCard_poleSpace`: Riemann's inequality at `P₀`, with
  some constant.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Order

universe u

namespace Stacks.BombieriStepanov

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- A section over an open `U` has no pole at the points of `U`. -/
theorem zero_le_ord_germToFunctionField {U : X.Opens} [Nonempty U] {x : X} (hxU : x ∈ U)
    (a : Γ(X, U)) : 0 ≤ X.ord (X.germToFunctionField U a) x := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  have h := Scheme.ord_le_smul hxU ha (1 : X.functionField)
  rw [scheme_ord_one] at h
  refine h.trans_eq ?_
  rw [Algebra.smul_def, mul_one]
  rfl

variable (hdvr : ∀ x : X, coheight x = 1 → IsDiscreteValuationRing (X.presheaf.stalk x))
  (k : Type u) [Field k] (p : X ⟶ Spec (.of k)) [IsProper p] [IsCurve k p]

/-- **Two functions of consecutive pole orders.** At a closed point `P₀` of degree one of a proper
curve, some `a` and `b` have no pole outside `P₀` and poles of orders `e` and `e + 1` at `P₀`. -/
theorem exists_consecutive_poleOrders (P₀ : CurvePlace X) (hP₀ : curveDeg k p P₀ = 1)
    (hcl : IsClosed ({P₀.1} : Set X)) :
    ∃ (e : ℕ) (a b : X.functionField),
      a ∈ poleSpace (curveVal hdvr) P₀ e ∧ a ≠ 0 ∧ ordZ (curveVal hdvr P₀) a = -e ∧
      b ∈ poleSpace (curveVal hdvr) P₀ (e + 1) ∧ b ≠ 0 ∧
        ordZ (curveVal hdvr P₀) b = -(e + 1) := by
  classical
  have := hdvr P₀.1 P₀.2
  set U : X.Opens := ⟨({P₀.1} : Set X)ᶜ, hcl.isOpen_compl⟩ with hUdef
  have hU : IsAffineOpen U := isAffineOpen_compl_singleton_of_isCurve k p inferInstance
    inferInstance hcl
  have hηU : genericPoint X ∈ U := by
    show genericPoint X ∉ ({P₀.1} : Set X)
    intro h
    have h' : genericPoint X = P₀.1 := h
    have key : ∀ y : X, y = P₀.1 → IsField (X.presheaf.stalk y) → False := by
      intro y hy hf
      subst hy
      exact IsDiscreteValuationRing.not_isField _ hf
    exact key _ h' (Field.toIsField X.functionField)
  have : Nonempty U := ⟨⟨_, hηU⟩⟩
  have := functionField_isFractionRing_of_isAffineOpen X U hU
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (X.presheaf.stalk P₀.1)
  set π' := algebraMap (X.presheaf.stalk P₀.1) X.functionField π with hπ'
  have hπ'0 : π' ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hπ.ne_zero
  have hπord : X.ord π' P₀.1 = 1 := ord_algebraMap_irreducible P₀.2 hπ
  obtain ⟨a', b', hb', hab⟩ := IsFractionRing.div_surjective (A := Γ(X, U)) π'
  have hb'0 : b' ≠ 0 := nonZeroDivisors.ne_zero hb'
  set a := algebraMap Γ(X, U) X.functionField a' with ha
  set b := algebraMap Γ(X, U) X.functionField b' with hb
  have hb0 : b ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hb'0
  have ha0 : a ≠ 0 := by
    intro h0
    rw [h0, zero_div] at hab
    exact hπ'0 hab.symm
  -- no poles outside `P₀`
  have hreg : ∀ (c : Γ(X, U)) (x : X), x ≠ P₀.1 →
      0 ≤ X.ord (algebraMap Γ(X, U) X.functionField c) x := by
    intro c x hx
    exact zero_le_ord_germToFunctionField (U := U) (show x ∈ U from hx) c
  have hD := hasDegreeFormula_curveVal hdvr k p
  have hle0 : ∀ c : Γ(X, U), algebraMap Γ(X, U) X.functionField c ≠ 0 →
      X.ord (algebraMap Γ(X, U) X.functionField c) P₀.1 ≤ 0 := by
    intro c hc
    have h := sum_ordZ_le_zero hD hc {P₀} fun P hP => by
      rw [ordZ_curveVal]
      exact hreg c P.1 fun h => hP (by simp [Subtype.ext h])
    simpa [ordZ_curveVal, hP₀] using h
  -- the orders at `P₀`
  have hrel : X.ord a P₀.1 = 1 + X.ord b P₀.1 := by
    have : a = π' * b := by rw [← hab]; field_simp
    rw [this, Scheme.ord_mul hπ'0 hb0, hπord]
  have hbneg : X.ord b P₀.1 ≤ 0 := hle0 b' hb0
  have hane : X.ord a P₀.1 ≤ 0 := hle0 a' ha0
  obtain ⟨β, hβ⟩ : ∃ β : ℕ, X.ord b P₀.1 = -((β : ℤ) + 1) :=
    ⟨(-(X.ord b P₀.1) - 1).toNat, by omega⟩
  have hmem : ∀ (c : Γ(X, U)) (n : ℕ), algebraMap Γ(X, U) X.functionField c ≠ 0 →
      -(n : ℤ) ≤ X.ord (algebraMap Γ(X, U) X.functionField c) P₀.1 →
      algebraMap Γ(X, U) X.functionField c ∈ poleSpace (curveVal hdvr) P₀ n := by
    intro c n hc hn
    refine ⟨?_, fun P hP => ?_⟩
    · rw [← le_ordZ_iff hc, ordZ_curveVal]
      exact hn
    · have := (le_ordZ_iff (w := curveVal hdvr P) hc 0).1 (by
        rw [ordZ_curveVal hdvr]; exact hreg c P.1 fun h => hP (Subtype.ext h))
      simpa using this
  refine ⟨β, a, b, hmem a' β ha0 (by rw [← ha]; omega), ha0, ?_,
    hmem b' (β + 1) hb0 (by rw [← hb]; push_cast; omega),
    hb0, ?_⟩
  · rw [ordZ_curveVal]
    omega
  · rw [ordZ_curveVal, hβ]

end Stacks.BombieriStepanov

end
