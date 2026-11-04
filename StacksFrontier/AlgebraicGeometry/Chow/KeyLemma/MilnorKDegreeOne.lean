module

public import StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.MilnorKTheory
public import StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.MilnorKTransport
public import StacksCore.Tactic.StacksAttribute

/-!
# The first Milnor K-group of a field

For a field `k`, the degree-one Milnor K-group is the multiplicative group of nonzero elements
of `k`.

## Main definitions

* `milnorKTheoryOneAddEquiv` identifies the first Milnor K-group with the additive avatar of
  `kˣ`.

## Implementation notes

Milnor K-groups are additive groups, so the multiplicative group `kˣ` is expressed as
`Additive kˣ`. The displayed equality in the source is represented by an additive equivalence.

The map from `Additive kˣ` is injective because the Steinberg relations are homogeneous of
degree two, so no element of the Steinberg ideal has a nonzero degree-one part.

## References

* [Stacks Project, Tag 0EAY](https://stacks.math.columbia.edu/tag/0EAY)
-/

public section

universe u

/-- Products of the degree-two Steinberg generators cannot contribute to degree one. -/
private lemma steinbergIdeal_decompose_lt_two (k : Type u) [Field k]
    {x : MilnorKTensorAlgebra k} (hx : x ∈ milnorKSteinbergIdeal k) :
    ∀ n : ℕ, n < 2 →
      ((DirectSum.decompose (milnorKTensorGrading k) x n : milnorKTensorGrading k n) :
        MilnorKTensorAlgebra k) = 0 := by
  induction hx using TwoSidedIdeal.span_induction with
  | mem x hx =>
      intro n hn
      rw [DirectSum.decompose_of_mem_ne (milnorKTensorGrading k)
        (steinbergRelation_mem_degree_two k hx) (by omega)]
  | zero =>
      intros; simp
  | add x y hx hy ihx ihy =>
      intro n hn
      simp [DirectSum.decompose_add, ihx n hn, ihy n hn]
  | neg x hx ih =>
      intro n hn
      rw [DirectSum.decompose_neg]
      change - (((DirectSum.decompose (milnorKTensorGrading k) x n :
        milnorKTensorGrading k n) : MilnorKTensorAlgebra k)) = 0
      simp [ih n hn]
  | left_absorb a x hx ih =>
      intro n hn
      rw [DirectSum.decompose_mul,
        DirectSum.coe_mul_apply_eq_sum_antidiagonal (milnorKTensorGrading k)]
      apply Finset.sum_eq_zero
      intro ij hij
      have hj : ij.2 < 2 := by have := Finset.mem_antidiagonal.mp hij; omega
      simp [ih ij.2 hj]
  | right_absorb a x hx ih =>
      intro n hn
      rw [DirectSum.decompose_mul,
        DirectSum.coe_mul_apply_eq_sum_antidiagonal (milnorKTensorGrading k)]
      apply Finset.sum_eq_zero
      intro ij hij
      have hi : ij.1 < 2 := by have := Finset.mem_antidiagonal.mp hij; omega
      simp [ih ij.1 hi]

/-- The map from the multiplicative group of `k` to the degree-one Milnor K-group, induced by
the canonical inclusion of generators into the tensor algebra. -/
private def milnorKTheoryOneMap (k : Type u) [Field k] :
    Additive kˣ →+ MilnorKTheory k 1 where
  toFun x := ⟨(milnorKSteinbergIdeal k).ringCon.mk'
      (TensorAlgebra.ι ℤ x), by
        refine ⟨TensorAlgebra.ι ℤ x, ?_, rfl⟩
        change TensorAlgebra.ι ℤ x ∈
          ((LinearMap.range
            (TensorAlgebra.ι ℤ : Additive kˣ →ₗ[ℤ] MilnorKTensorAlgebra k)) ^ 1).toAddSubgroup
        simpa only [pow_one, Submodule.mem_toAddSubgroup] using
          (LinearMap.mem_range_self
            (TensorAlgebra.ι ℤ : Additive kˣ →ₗ[ℤ] MilnorKTensorAlgebra k) x)⟩
  map_zero' := by ext; simp
  map_add' x y := by
    apply Subtype.ext
    change (milnorKSteinbergIdeal k).ringCon.mk'
        (TensorAlgebra.ι ℤ (x + y)) =
      (milnorKSteinbergIdeal k).ringCon.mk' (TensorAlgebra.ι ℤ x) +
        (milnorKSteinbergIdeal k).ringCon.mk' (TensorAlgebra.ι ℤ y)
    simp only [map_add]

/-- The map to the degree-one Milnor K-group is injective, since the Steinberg ideal has no
degree-one part. -/
private lemma milnorKTheoryOneMap_injective (k : Type u) [Field k] :
    Function.Injective (milnorKTheoryOneMap k) := by
  intro x y hxy
  have hzero : milnorKTheoryOneMap k (x - y) = 0 := by simp [map_sub, hxy]
  have hval := congrArg Subtype.val hzero
  change (milnorKSteinbergIdeal k).ringCon.mk'
      (TensorAlgebra.ι ℤ (x - y)) = 0 at hval
  have hI : TensorAlgebra.ι ℤ (x - y) ∈ milnorKSteinbergIdeal k := by
    rw [← TwoSidedIdeal.ker_ringCon_mk' (milnorKSteinbergIdeal k),
      TwoSidedIdeal.mem_ker]
    exact hval
  have hdegree : TensorAlgebra.ι ℤ (x - y) ∈ milnorKTensorGrading k 1 := by
    simpa only [pow_one] using LinearMap.mem_range_self
      (TensorAlgebra.ι ℤ : Additive kˣ →ₗ[ℤ] MilnorKTensorAlgebra k) (x - y)
  have hdecomp := steinbergIdeal_decompose_lt_two k hI 1 (by omega)
  rw [DirectSum.decompose_of_mem_same (milnorKTensorGrading k) hdegree] at hdecomp
  exact sub_eq_zero.mp ((TensorAlgebra.ι_inj ℤ (x - y) 0).mp
    (by simpa using hdecomp))

/-- The map to the degree-one Milnor K-group is surjective, since that group is by definition
the image of the degree-one part of the tensor algebra. -/
private lemma milnorKTheoryOneMap_surjective (k : Type u) [Field k] :
    Function.Surjective (milnorKTheoryOneMap k) := by
  rintro ⟨z, hz⟩
  change z ∈ milnorKGrading k 1 at hz
  obtain ⟨a, ha, rfl⟩ := AddSubgroup.mem_map.mp hz
  rw [pow_one, Submodule.mem_toAddSubgroup] at ha
  obtain ⟨x, hx⟩ := LinearMap.mem_range.mp ha
  refine ⟨x, Subtype.ext ?_⟩
  change (milnorKSteinbergIdeal k).ringCon.mk' (TensorAlgebra.ι ℤ x) =
    (milnorKSteinbergIdeal k).ringCon.mk' a
  rw [hx]

/-- The degree-one Milnor K-group of a field is its multiplicative group. -/
@[stacks 0EAY "milnor_k_one"]
public noncomputable def milnorKTheoryOneAddEquiv (k : Type u) [Field k] :
    MilnorKTheory k 1 ≃+ Additive kˣ :=
  (AddEquiv.ofBijective (milnorKTheoryOneMap k)
    ⟨milnorKTheoryOneMap_injective k, milnorKTheoryOneMap_surjective k⟩).symm

/-! ### Naturality in the field -/

/-- The map from `Additive kˣ` is natural: transporting the image of a generator along a
homomorphism of fields gives the image of the transported generator. -/
private theorem milnorKTransport_milnorKTheoryOneMap {k₁ k₂ : Type u} [Field k₁] [Field k₂]
    (φ : k₁ →+* k₂) (a : Additive k₁ˣ) :
    milnorKTransport φ 1 (milnorKTheoryOneMap k₁ a) =
      milnorKTheoryOneMap k₂ (milnorKUnitsMap φ a) := by
  refine Subtype.ext ?_
  change milnorKRingMap φ (milnorKTheoryOneMap k₁ a : MilnorKRing k₁) =
    (milnorKTheoryOneMap k₂ (milnorKUnitsMap φ a) : MilnorKRing k₂)
  have h1 : (milnorKTheoryOneMap k₁ a : MilnorKRing k₁) =
      (milnorKSteinbergIdeal k₁).ringCon.mk' (TensorAlgebra.ι ℤ a) := rfl
  have h2 : (milnorKTheoryOneMap k₂ (milnorKUnitsMap φ a) : MilnorKRing k₂) =
      (milnorKSteinbergIdeal k₂).ringCon.mk' (TensorAlgebra.ι ℤ (milnorKUnitsMap φ a)) := rfl
  rw [h1, h2, milnorKRingMap_mk', milnorKTensorMap_ι]

/-- The additive equivalence `MilnorKTheory k 1 ≃+ Additive kˣ` sends the image of a generator
under the comparison map back to that generator. -/
private theorem milnorKTheoryOneAddEquiv_milnorKTheoryOneMap (k : Type u) [Field k]
    (a : Additive kˣ) :
    milnorKTheoryOneAddEquiv k (milnorKTheoryOneMap k a) = a :=
  (AddEquiv.ofBijective (milnorKTheoryOneMap k)
    ⟨milnorKTheoryOneMap_injective k, milnorKTheoryOneMap_surjective k⟩).symm_apply_apply a

/-- The class in the degree-one Milnor K-group corresponding to a unit is the image of that unit
under the canonical inclusion of generators into the tensor algebra. -/
public theorem coe_milnorKTheoryOneAddEquiv_symm (k : Type u) [Field k] (a : Additive kˣ) :
    ((milnorKTheoryOneAddEquiv k).symm a : MilnorKRing k) =
      (milnorKSteinbergIdeal k).ringCon.mk' (TensorAlgebra.ι ℤ a) := by
  have h : (milnorKTheoryOneAddEquiv k).symm a = milnorKTheoryOneMap k a := by
    rw [AddEquiv.symm_apply_eq]
    exact (milnorKTheoryOneAddEquiv_milnorKTheoryOneMap k a).symm
  rw [h]
  rfl

/-- **Naturality of the degree-one identification with `Additive kˣ`.** Transporting a
degree-one Milnor K-group element along a homomorphism of fields and then identifying the
result with the unit group of the target agrees with identifying the original element with the
unit group of the source and then transporting along the induced map of unit groups. -/
public theorem milnorKTheoryOneAddEquiv_milnorKTransport {k₁ k₂ : Type u} [Field k₁] [Field k₂]
    (φ : k₁ →+* k₂) (y : MilnorKTheory k₁ 1) :
    milnorKTheoryOneAddEquiv k₂ (milnorKTransport φ 1 y) =
      milnorKUnitsMap φ (milnorKTheoryOneAddEquiv k₁ y) := by
  obtain ⟨a, rfl⟩ := milnorKTheoryOneMap_surjective k₁ y
  rw [milnorKTransport_milnorKTheoryOneMap, milnorKTheoryOneAddEquiv_milnorKTheoryOneMap,
    milnorKTheoryOneAddEquiv_milnorKTheoryOneMap]
