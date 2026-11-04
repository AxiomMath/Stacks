module

public import StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.MilnorKSymbols

/-!
# The grading involution of the Milnor K-ring

The tensor algebra on `kˣ` carries the algebra endomorphism determined by `ι a ↦ -ι a`, which is
multiplication by `(-1) ^ n` on the degree-`n` part. Steinberg elements are homogeneous of degree
two, so they are fixed, the Steinberg ideal is preserved, and the endomorphism descends to a ring
endomorphism `milnorKInvolution k` of `MilnorKRing k`. It is an involution, it preserves each
homogeneous subgroup `milnorKGrading k n`, and it fixes `{-1}`.

Moreover the involution is invisible against `{-1}`: `σ x · {-1} = x · {-1}` for every `x`, since
`σ x - x` is twice something while `{-1}` is killed by `2`.

## Main definitions

* `milnorKTensorInvolution` — the endomorphism `ι a ↦ -ι a` of the Milnor tensor algebra.
* `milnorKInvolution` — the induced involution of `MilnorKRing k`.

## Main results

* `milnorKInvolution_involutive` — it squares to the identity.
* `milnorKInvolution_mem_milnorKGrading` — it preserves the homogeneous subgroups.
* `milnorKInvolution_milnorKNegOne` — it fixes `{-1}`.
* `milnorKInvolution_mul_milnorKNegOne` — `σ x · {-1} = x · {-1}`.

## References

* [Stacks Project, Tag 0EAY](https://stacks.math.columbia.edu/tag/0EAY)
-/

@[expose] public noncomputable section

universe u

variable {k : Type u} [Field k]

/-! ### On the tensor algebra -/

/-- The algebra endomorphism `ι a ↦ -ι a` of the Milnor tensor algebra on `kˣ`. On the degree-`n`
homogeneous part it is multiplication by `(-1) ^ n`. -/
def milnorKTensorInvolution (k : Type u) [Field k] :
    MilnorKTensorAlgebra k →ₐ[ℤ] MilnorKTensorAlgebra k :=
  TensorAlgebra.lift ℤ (-(TensorAlgebra.ι ℤ : Additive kˣ →ₗ[ℤ] MilnorKTensorAlgebra k))

/-- `milnorKTensorInvolution k` sends `ι a` to `-ι a`. -/
@[simp]
theorem milnorKTensorInvolution_ι (a : Additive kˣ) :
    milnorKTensorInvolution k (TensorAlgebra.ι ℤ a) = -TensorAlgebra.ι ℤ a := by
  rw [milnorKTensorInvolution, TensorAlgebra.lift_ι_apply, LinearMap.neg_apply]

/-- `milnorKTensorInvolution k` fixes every Steinberg element. -/
theorem milnorKTensorInvolution_of_mem_milnorKSteinbergRelations
    {x : MilnorKTensorAlgebra k} (hx : x ∈ milnorKSteinbergRelations k) :
    milnorKTensorInvolution k x = x := by
  obtain ⟨a, rfl⟩ := hx
  rw [map_mul, milnorKTensorInvolution_ι, milnorKTensorInvolution_ι, neg_mul_neg]

/-- `milnorKTensorInvolution k` maps the Steinberg ideal into itself. -/
theorem milnorKTensorInvolution_mem_milnorKSteinbergIdeal
    {x : MilnorKTensorAlgebra k} (hx : x ∈ milnorKSteinbergIdeal k) :
    milnorKTensorInvolution k x ∈ milnorKSteinbergIdeal k := by
  induction hx using TwoSidedIdeal.span_induction with
  | mem x hx =>
      rw [milnorKTensorInvolution_of_mem_milnorKSteinbergRelations hx]
      exact TwoSidedIdeal.subset_span hx
  | zero => simpa only [map_zero] using (milnorKSteinbergIdeal k).zero_mem
  | add x y _ _ ihx ihy =>
      simpa only [map_add] using (milnorKSteinbergIdeal k).add_mem ihx ihy
  | neg x _ ihx => simpa only [map_neg] using (milnorKSteinbergIdeal k).neg_mem ihx
  | left_absorb a x _ ihx =>
      simpa only [map_mul] using (milnorKSteinbergIdeal k).mul_mem_left _ _ ihx
  | right_absorb b x _ ihx =>
      simpa only [map_mul] using (milnorKSteinbergIdeal k).mul_mem_right _ _ ihx

/-- `milnorKTensorInvolution k` maps the degree-`n` part `milnorKTensorGrading k n` into itself. -/
theorem milnorKTensorInvolution_mem_milnorKTensorGrading (n : ℕ)
    {x : MilnorKTensorAlgebra k} (hx : x ∈ milnorKTensorGrading k n) :
    milnorKTensorInvolution k x ∈ milnorKTensorGrading k n := by
  induction n generalizing x with
  | zero =>
      rw [milnorKTensorGrading, pow_zero, Submodule.one_eq_range] at hx ⊢
      obtain ⟨r, rfl⟩ := hx
      exact ⟨r, by simp⟩
  | succ n ih =>
      rw [milnorKTensorGrading, pow_succ] at hx
      rw [milnorKTensorGrading, pow_succ]
      refine Submodule.mul_induction_on hx ?_ ?_
      · intro a ha b hb
        rw [map_mul]
        refine Submodule.mul_mem_mul (ih ha) ?_
        obtain ⟨m, rfl⟩ := hb
        exact ⟨-m, by rw [map_neg, milnorKTensorInvolution_ι]⟩
      · intro a b ha hb
        simpa only [map_add] using add_mem ha hb

/-- `milnorKTensorInvolution k` composed with itself is the identity. -/
theorem milnorKTensorInvolution_comp_self :
    (milnorKTensorInvolution k).comp (milnorKTensorInvolution k) = AlgHom.id ℤ _ := by
  refine TensorAlgebra.hom_ext (LinearMap.ext fun a ↦ ?_)
  simp

/-! ### On the Milnor K-ring -/

/-- The grading involution of the Milnor K-ring: the endomorphism induced by `ι a ↦ -ι a`. It is
multiplication by `(-1) ^ n` on `K^M_n(k)`. -/
def milnorKInvolution (k : Type u) [Field k] : MilnorKRing k →+* MilnorKRing k :=
  (milnorKSteinbergIdeal k).ringCon.lift
    ((milnorKSteinbergIdeal k).ringCon.mk'.comp (milnorKTensorInvolution k).toRingHom)
    (by
      intro x y hxy
      rw [RingCon.ker_apply]
      have hmem : x - y ∈ milnorKSteinbergIdeal k :=
        ((milnorKSteinbergIdeal k).rel_iff x y).mp hxy
      have hsub : milnorKTensorInvolution k (x - y) ∈ milnorKSteinbergIdeal k :=
        milnorKTensorInvolution_mem_milnorKSteinbergIdeal hmem
      rw [map_sub] at hsub
      change (milnorKSteinbergIdeal k).ringCon.mk' (milnorKTensorInvolution k x) =
        (milnorKSteinbergIdeal k).ringCon.mk' (milnorKTensorInvolution k y)
      exact Quotient.sound' (((milnorKSteinbergIdeal k).rel_iff _ _).mpr hsub))

/-- On the class of `x` in `MilnorKRing k`, `milnorKInvolution k` is the class of
`milnorKTensorInvolution k x`. -/
@[simp]
theorem milnorKInvolution_mk' (x : MilnorKTensorAlgebra k) :
    milnorKInvolution k ((milnorKSteinbergIdeal k).ringCon.mk' x) =
      (milnorKSteinbergIdeal k).ringCon.mk' (milnorKTensorInvolution k x) :=
  rfl

/-- `milnorKInvolution k` sends the symbol `{u}` to `-{u}`. -/
@[simp]
theorem milnorKInvolution_milnorKSymbol (u : kˣ) :
    milnorKInvolution k (milnorKSymbol k u) = -milnorKSymbol k u := by
  rw [milnorKSymbol_eq_mk', milnorKInvolution_mk', milnorKTensorInvolution_ι, map_neg]

/-- `milnorKInvolution k` is an involution: `σ (σ x) = x`. -/
theorem milnorKInvolution_involutive (x : MilnorKRing k) :
    milnorKInvolution k (milnorKInvolution k x) = x := by
  obtain ⟨t, rfl⟩ := milnorKRing_mk'_surjective k x
  rw [milnorKInvolution_mk', milnorKInvolution_mk']
  exact congrArg _ (AlgHom.congr_fun milnorKTensorInvolution_comp_self t)

/-- `milnorKInvolution k` maps the homogeneous subgroup `milnorKGrading k n` into itself. -/
theorem milnorKInvolution_mem_milnorKGrading (n : ℕ) {x : MilnorKRing k}
    (hx : x ∈ milnorKGrading k n) : milnorKInvolution k x ∈ milnorKGrading k n := by
  obtain ⟨t, ht, rfl⟩ := hx
  refine ⟨milnorKTensorInvolution k t, ?_, rfl⟩
  simp only [SetLike.mem_coe, Submodule.mem_toAddSubgroup] at ht ⊢
  exact milnorKTensorInvolution_mem_milnorKTensorGrading n ht

/-- `milnorKInvolution k` fixes `{-1}`. -/
@[simp]
theorem milnorKInvolution_milnorKNegOne :
    milnorKInvolution k (milnorKNegOne k) = milnorKNegOne k := by
  rw [milnorKNegOne_eq, milnorKInvolution_milnorKSymbol, ← milnorKNegOne_eq,
    neg_eq_iff_add_eq_zero]
  exact milnorKNegOne_add_self

/-! ### The involution is invisible against `{-1}` -/

private theorem milnorKInvolution_mul_milnorKNegOne_mul_aux
    (t : MilnorKTensorAlgebra k) (y : MilnorKRing k) :
    milnorKInvolution k ((milnorKSteinbergIdeal k).ringCon.mk' t) * (milnorKNegOne k * y) =
      (milnorKSteinbergIdeal k).ringCon.mk' t * (milnorKNegOne k * y) := by
  induction t using TensorAlgebra.induction generalizing y with
  | algebraMap r => rw [milnorKInvolution_mk', AlgHom.commutes]
  | ι a =>
      have hval : (milnorKSteinbergIdeal k).ringCon.mk' (TensorAlgebra.ι ℤ a) =
          milnorKSymbol k (Additive.toMul a) := rfl
      rw [hval, milnorKInvolution_milnorKSymbol, neg_mul, neg_eq_iff_add_eq_zero, ← mul_assoc,
        ← add_mul, mul_milnorKNegOne_add_self, zero_mul]
  | mul a b ha hb =>
      rw [map_mul, map_mul, mul_assoc, hb y]
      have hmove : (milnorKSteinbergIdeal k).ringCon.mk' b * (milnorKNegOne k * y) =
          milnorKNegOne k * ((milnorKSteinbergIdeal k).ringCon.mk' b * y) := by
        rw [← mul_assoc, ← milnorKNegOne_mul_comm, mul_assoc]
      rw [hmove, ha, ← hmove, ← mul_assoc]
  | add a b ha hb =>
      rw [map_add, map_add, add_mul, add_mul, ha, hb]

/-- For all `x` and `y` in `MilnorKRing k`, `σ x · ({-1} y) = x · ({-1} y)`, where `σ` is
`milnorKInvolution k`. -/
theorem milnorKInvolution_mul_milnorKNegOne_mul (x y : MilnorKRing k) :
    milnorKInvolution k x * (milnorKNegOne k * y) = x * (milnorKNegOne k * y) := by
  obtain ⟨t, rfl⟩ := milnorKRing_mk'_surjective k x
  exact milnorKInvolution_mul_milnorKNegOne_mul_aux t y

/-- For every `x` in `MilnorKRing k`, `σ x · {-1} = x · {-1}`, where `σ` is
`milnorKInvolution k`. -/
theorem milnorKInvolution_mul_milnorKNegOne (x : MilnorKRing k) :
    milnorKInvolution k x * milnorKNegOne k = x * milnorKNegOne k := by
  simpa using milnorKInvolution_mul_milnorKNegOne_mul (k := k) x 1
