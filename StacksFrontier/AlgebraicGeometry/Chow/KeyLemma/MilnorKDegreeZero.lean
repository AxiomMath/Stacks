module

public import StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.MilnorKTheory
public import StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.MilnorKTransport
public import StacksCore.Tactic.StacksAttribute

/-!
# Degree zero Milnor K-theory

For every field `k`, the degree-zero part of its Milnor K-theory is isomorphic to `ℤ`.

## Main definitions

* `milnorKZeroMap` is the comparison map from `ℤ`.
* `milnorKTheoryZeroAddEquiv` is the additive equivalence between degree-zero Milnor K-theory
  and `ℤ`.

## Main results

* `milnorKZeroMap_injective` and `milnorKZeroMap_surjective` say that the comparison map is
  bijective.

## Implementation notes

The source writes this identification as an equality. Since `MilnorKTheory k 0` is represented
as an additive subgroup of the graded quotient ring, the identification is expressed as an
additive equivalence. Injectivity is proved by the augmentation homomorphism killing the
tensor generators, which therefore descends to the Steinberg quotient and inverts the
comparison map.

## References

* [Stacks Project, Tag 0EAY](https://stacks.math.columbia.edu/tag/0EAY)
-/

@[expose] public section

universe u

/-- The augmentation of the tensor algebra on `kˣ`, sending every generator to zero. -/
private noncomputable def milnorKAugmentation (k : Type u) [Field k] :
    TensorAlgebra ℤ (Additive kˣ) →+* ℤ :=
  (TensorAlgebra.lift ℤ (0 : Additive kˣ →ₗ[ℤ] ℤ)).toRingHom

/-- The augmentation kills the Steinberg relations, which are products of two generators. -/
private lemma milnorKAugmentation_eq_zero_on_relations (k : Type u) [Field k]
    {x : TensorAlgebra ℤ (Additive kˣ)} (hx : x ∈ milnorKSteinbergRelations k) :
    milnorKAugmentation k x = 0 := by
  rcases hx with ⟨a, rfl⟩
  simp [milnorKAugmentation, TensorAlgebra.lift_ι_apply]

/-- The augmentation is constant on the classes of the Steinberg congruence. -/
private lemma milnorKAugmentation_congruent (k : Type u) [Field k] :
    (milnorKSteinbergIdeal k).ringCon ≤ RingCon.ker (milnorKAugmentation k) := by
  change (milnorKSteinbergIdeal k).ringCon ≤
    (TwoSidedIdeal.ker (milnorKAugmentation k)).ringCon
  rw [← TwoSidedIdeal.ringCon_le_iff]
  exact (TwoSidedIdeal.span_le).mpr fun x hx ↦
    (TwoSidedIdeal.mem_ker (milnorKAugmentation k)).mpr
    (milnorKAugmentation_eq_zero_on_relations k hx)

/-- The augmentation, descended to the Milnor K-ring. -/
private noncomputable def milnorKAugmentationOnQuotient (k : Type u) [Field k] :
    MilnorKRing k →+* ℤ :=
  (milnorKSteinbergIdeal k).ringCon.lift
    (milnorKAugmentation k) (milnorKAugmentation_congruent k)

/-- The comparison map from `ℤ` to the degree-zero Milnor K-group, given by the structure map
of the tensor algebra followed by the quotient map. -/
def milnorKZeroMap (k : Type u) [Field k] : ℤ →+ MilnorKTheory k 0 :=
  (((milnorKSteinbergIdeal k).ringCon.mk'.toAddMonoidHom).comp
    (algebraMap ℤ (TensorAlgebra ℤ (Additive kˣ))).toAddMonoidHom).codRestrict _ (by
      intro n
      apply AddSubgroup.mem_map_of_mem
      change algebraMap ℤ (TensorAlgebra ℤ (Additive kˣ)) n ∈
        (LinearMap.range (TensorAlgebra.ι ℤ : Additive kˣ →ₗ[ℤ]
          TensorAlgebra ℤ (Additive kˣ)) ^ 0)
      rw [Submodule.pow_zero, Submodule.mem_one]
      exact ⟨n, rfl⟩)

/-- The comparison map is injective, because the augmentation inverts it. -/
lemma milnorKZeroMap_injective (k : Type u) [Field k] :
    Function.Injective (milnorKZeroMap k) := by
  intro a b hab
  have hq :
      (milnorKSteinbergIdeal k).ringCon.mk'
          (algebraMap ℤ (TensorAlgebra ℤ (Additive kˣ)) a) =
        (milnorKSteinbergIdeal k).ringCon.mk'
          (algebraMap ℤ (TensorAlgebra ℤ (Additive kˣ)) b) :=
    congrArg Subtype.val hab
  have h := congrArg (milnorKAugmentationOnQuotient k) hq
  simpa [milnorKAugmentationOnQuotient, milnorKAugmentation] using h

/-- The comparison map is surjective, because the degree-zero part of the tensor algebra is
the image of `ℤ`. -/
lemma milnorKZeroMap_surjective (k : Type u) [Field k] :
    Function.Surjective (milnorKZeroMap k) := by
  rintro ⟨y, hy⟩
  obtain ⟨x, hx, rfl⟩ := AddSubgroup.mem_map.mp hy
  change x ∈ (LinearMap.range (TensorAlgebra.ι ℤ : Additive kˣ →ₗ[ℤ]
    TensorAlgebra ℤ (Additive kˣ)) ^ 0) at hx
  rw [Submodule.pow_zero, Submodule.mem_one] at hx
  obtain ⟨n, rfl⟩ := hx
  exact ⟨n, rfl⟩

/-- The degree-zero Milnor K-group of a field is additively isomorphic to `ℤ`. -/
@[stacks 0EAY "milnor_k_zero"]
noncomputable def milnorKTheoryZeroAddEquiv (k : Type u) [Field k] :
    MilnorKTheory k 0 ≃+ ℤ :=
  (AddEquiv.ofBijective (milnorKZeroMap k)
    ⟨milnorKZeroMap_injective k, milnorKZeroMap_surjective k⟩).symm

/-! ### Naturality in the field -/

/-- The comparison map from `ℤ` is natural: transporting the image of `n` along a homomorphism
of fields gives the image of `n` in the target. -/
theorem milnorKTransport_milnorKZeroMap {k₁ k₂ : Type u} [Field k₁] [Field k₂]
    (φ : k₁ →+* k₂) (n : ℤ) :
    milnorKTransport φ 0 (milnorKZeroMap k₁ n) = milnorKZeroMap k₂ n := by
  refine Subtype.ext ?_
  change milnorKRingMap φ (milnorKZeroMap k₁ n : MilnorKRing k₁) =
    (milnorKZeroMap k₂ n : MilnorKRing k₂)
  have h : ∀ (k : Type u) [Field k] (n : ℤ), (milnorKZeroMap k n : MilnorKRing k) =
      (milnorKSteinbergIdeal k).ringCon.mk' (algebraMap ℤ (TensorAlgebra ℤ (Additive kˣ)) n) :=
    fun _ _ _ ↦ rfl
  rw [h, h, milnorKRingMap_mk', AlgHom.commutes]

/-- The additive equivalence `MilnorKTheory k 0 ≃+ ℤ` sends the image of `n` under the
comparison map back to `n`. -/
theorem milnorKTheoryZeroAddEquiv_milnorKZeroMap (k : Type u) [Field k] (n : ℤ) :
    milnorKTheoryZeroAddEquiv k (milnorKZeroMap k n) = n :=
  (AddEquiv.ofBijective (milnorKZeroMap k)
    ⟨milnorKZeroMap_injective k, milnorKZeroMap_surjective k⟩).symm_apply_apply n

/-- **Naturality of the degree-zero identification with `ℤ`.** Transporting a degree-zero
Milnor K-group element along a homomorphism of fields and then identifying the result with `ℤ`
agrees with identifying the original element with `ℤ` directly: the degree-zero Milnor K-group
of every field is canonically `ℤ`, independently of the field. -/
theorem milnorKTheoryZeroAddEquiv_milnorKTransport {k₁ k₂ : Type u} [Field k₁] [Field k₂]
    (φ : k₁ →+* k₂) (y : MilnorKTheory k₁ 0) :
    milnorKTheoryZeroAddEquiv k₂ (milnorKTransport φ 0 y) = milnorKTheoryZeroAddEquiv k₁ y := by
  obtain ⟨n, rfl⟩ := milnorKZeroMap_surjective k₁ y
  rw [milnorKTransport_milnorKZeroMap, milnorKTheoryZeroAddEquiv_milnorKZeroMap,
    milnorKTheoryZeroAddEquiv_milnorKZeroMap]
