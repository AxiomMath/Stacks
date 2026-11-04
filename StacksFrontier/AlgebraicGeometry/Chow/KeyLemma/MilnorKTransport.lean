module

public import StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.MilnorKTheory

/-!
# Functoriality of Milnor K-theory in the field

A homomorphism of fields `φ : k₁ →+* k₂` induces a homomorphism of Milnor K-groups
`K_n^M(k₁) ⟶ K_n^M(k₂)` in every degree, and an isomorphism of fields induces an isomorphism
of Milnor K-groups.

The construction is the only possible one. On the tensor algebra `φ` acts through the induced
map of unit groups `k₁ˣ →* k₂ˣ`; the Steinberg element attached to `x ≠ 0, 1` is sent to the
Steinberg element attached to `φ x`, which is again neither `0` nor `1` because a homomorphism
of fields is injective; hence the Steinberg ideal is sent into the Steinberg ideal and the map
descends to the quotient ring. The induced map carries the degree-`n` homogeneous part of the
tensor algebra into the degree-`n` homogeneous part, so it restricts to the degree-`n` Milnor
K-groups.

## Main definitions

* `milnorKTensorMap` — the map of tensor algebras induced by a homomorphism of fields.
* `milnorKRingMap` — the induced homomorphism of the full Milnor K-rings.
* `milnorKTransport` — the induced homomorphism `K_n^M(k₁) →+ K_n^M(k₂)` in degree `n`.
* `milnorKTransportEquiv` — the isomorphism `K_n^M(k₁) ≃+ K_n^M(k₂)` induced by an isomorphism
  of fields.

## Main results

* `milnorKTensorMap_mem_milnorKSteinbergIdeal` — the Steinberg ideal is preserved.
* `milnorKTensorMap_mem_milnorKTensorGrading` — the homogeneous degree is preserved.
* `milnorKTransport_comp` — the transports compose.
* `milnorKTransport_id` — the transport along the identity is the identity.

## References

* [Stacks Project, Tag 0EAY](https://stacks.math.columbia.edu/tag/0EAY)
-/

@[expose] public section

universe u

variable {k₁ k₂ k₃ : Type u} [Field k₁] [Field k₂] [Field k₃]

/-! ### The induced map of unit groups -/

/-- A homomorphism of fields induces a `ℤ`-linear map on the unit groups read additively, which
is the module the Milnor tensor algebra is built on. -/
def milnorKUnitsMap (φ : k₁ →+* k₂) : Additive k₁ˣ →ₗ[ℤ] Additive k₂ˣ :=
  AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive (Units.map (φ : k₁ →* k₂)))

/-- The induced map of unit groups sends `Additive.ofMul u` to `Additive.ofMul (φ u)`. -/
@[simp]
theorem milnorKUnitsMap_ofMul (φ : k₁ →+* k₂) (u : k₁ˣ) :
    milnorKUnitsMap φ (Additive.ofMul u) = Additive.ofMul (Units.map (φ : k₁ →* k₂) u) :=
  rfl

/-! ### The induced map of tensor algebras -/

/-- The map of Milnor tensor algebras induced by a homomorphism of fields. -/
noncomputable def milnorKTensorMap (φ : k₁ →+* k₂) :
    MilnorKTensorAlgebra k₁ →ₐ[ℤ] MilnorKTensorAlgebra k₂ :=
  TensorAlgebra.lift ℤ
    ((TensorAlgebra.ι ℤ : Additive k₂ˣ →ₗ[ℤ] MilnorKTensorAlgebra k₂).comp
      (milnorKUnitsMap φ))

/-- The induced map of tensor algebras sends the generator attached to a unit `a` to the
generator attached to its image under the induced map of unit groups. -/
@[simp]
theorem milnorKTensorMap_ι (φ : k₁ →+* k₂) (a : Additive k₁ˣ) :
    milnorKTensorMap φ (TensorAlgebra.ι ℤ a) = TensorAlgebra.ι ℤ (milnorKUnitsMap φ a) :=
  TensorAlgebra.lift_ι_apply _ _

/-- The Steinberg elements are preserved: a homomorphism of fields is injective, so the image of
a scalar different from `0` and `1` is again different from `0` and `1`, and the image of
`1 - x` is `1 - φ x`. -/
theorem milnorKTensorMap_milnorKSteinbergRelations (φ : k₁ →+* k₂)
    {x : MilnorKTensorAlgebra k₁} (hx : x ∈ milnorKSteinbergRelations k₁) :
    milnorKTensorMap φ x ∈ milnorKSteinbergRelations k₂ := by
  obtain ⟨a, rfl⟩ := hx
  have hne0 : φ a.1 ≠ 0 := by
    simpa only [ne_eq, map_eq_zero] using a.2.1
  have hne1 : φ a.1 ≠ 1 := fun h ↦ a.2.2 (φ.injective (by rw [h, map_one]))
  have h1 : milnorKUnitsMap φ (Additive.ofMul (Units.mk0 a.1 a.2.1)) =
      Additive.ofMul (Units.mk0 (φ a.1) hne0) :=
    congrArg Additive.ofMul (Units.ext rfl)
  have h2 : milnorKUnitsMap φ
        (Additive.ofMul (Units.mk0 (1 - a.1) (sub_ne_zero.mpr (Ne.symm a.2.2)))) =
      Additive.ofMul (Units.mk0 (1 - φ a.1) (sub_ne_zero.mpr (Ne.symm hne1))) := by
    refine congrArg Additive.ofMul (Units.ext ?_)
    show φ (1 - a.1) = 1 - φ a.1
    rw [map_sub, map_one]
  refine ⟨⟨φ a.1, hne0, hne1⟩, ?_⟩
  symm
  rw [map_mul, milnorKTensorMap_ι, milnorKTensorMap_ι, h1, h2]

/-- The Steinberg ideal is preserved. -/
theorem milnorKTensorMap_mem_milnorKSteinbergIdeal (φ : k₁ →+* k₂)
    {x : MilnorKTensorAlgebra k₁} (hx : x ∈ milnorKSteinbergIdeal k₁) :
    milnorKTensorMap φ x ∈ milnorKSteinbergIdeal k₂ := by
  induction hx using TwoSidedIdeal.span_induction with
  | mem x hx =>
      exact TwoSidedIdeal.subset_span (milnorKTensorMap_milnorKSteinbergRelations φ hx)
  | zero => simpa only [map_zero] using (milnorKSteinbergIdeal k₂).zero_mem
  | add x y _ _ ihx ihy =>
      simpa only [map_add] using (milnorKSteinbergIdeal k₂).add_mem ihx ihy
  | neg x _ ihx => simpa only [map_neg] using (milnorKSteinbergIdeal k₂).neg_mem ihx
  | left_absorb a x _ ihx =>
      simpa only [map_mul] using (milnorKSteinbergIdeal k₂).mul_mem_left _ _ ihx
  | right_absorb b x _ ihx =>
      simpa only [map_mul] using (milnorKSteinbergIdeal k₂).mul_mem_right _ _ ihx

/-- The homogeneous degree is preserved: the induced map sends a generator `ι a` of the
degree-one part to a generator, and is an algebra map, so it respects the powers of that
part. -/
theorem milnorKTensorMap_mem_milnorKTensorGrading (φ : k₁ →+* k₂) (n : ℕ)
    {x : MilnorKTensorAlgebra k₁} (hx : x ∈ milnorKTensorGrading k₁ n) :
    milnorKTensorMap φ x ∈ milnorKTensorGrading k₂ n := by
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
        exact ⟨milnorKUnitsMap φ m, (milnorKTensorMap_ι φ m).symm⟩
      · intro a b ha hb
        simpa only [map_add] using add_mem ha hb

/-! ### The induced map of Milnor K-rings -/

/-- The homomorphism of Milnor K-rings induced by a homomorphism of fields. -/
noncomputable def milnorKRingMap (φ : k₁ →+* k₂) : MilnorKRing k₁ →+* MilnorKRing k₂ :=
  (milnorKSteinbergIdeal k₁).ringCon.lift
    ((milnorKSteinbergIdeal k₂).ringCon.mk'.comp (milnorKTensorMap φ).toRingHom)
    (by
      intro x y hxy
      rw [RingCon.ker_apply]
      have hmem : x - y ∈ milnorKSteinbergIdeal k₁ :=
        ((milnorKSteinbergIdeal k₁).rel_iff x y).mp hxy
      have : milnorKTensorMap φ (x - y) ∈ milnorKSteinbergIdeal k₂ :=
        milnorKTensorMap_mem_milnorKSteinbergIdeal φ hmem
      rw [map_sub] at this
      change (milnorKSteinbergIdeal k₂).ringCon.mk' (milnorKTensorMap φ x) =
        (milnorKSteinbergIdeal k₂).ringCon.mk' (milnorKTensorMap φ y)
      exact Quotient.sound' (((milnorKSteinbergIdeal k₂).rel_iff _ _).mpr this))

/-- The induced map of Milnor K-rings sends the class of a tensor `x` to the class of its
image under the induced map of tensor algebras. -/
@[simp]
theorem milnorKRingMap_mk' (φ : k₁ →+* k₂) (x : MilnorKTensorAlgebra k₁) :
    milnorKRingMap φ ((milnorKSteinbergIdeal k₁).ringCon.mk' x) =
      (milnorKSteinbergIdeal k₂).ringCon.mk' (milnorKTensorMap φ x) :=
  rfl

/-! ### The induced map of Milnor K-groups -/

/-- **The degree-`n` Milnor K-group is functorial in the field.** The map induced by a
homomorphism of fields `φ : k₁ →+* k₂`. -/
noncomputable def milnorKTransport (φ : k₁ →+* k₂) (n : ℕ) :
    MilnorKTheory k₁ n →+ MilnorKTheory k₂ n where
  toFun y :=
    ⟨milnorKRingMap φ y.1, by
      obtain ⟨x, hx, hxy⟩ := y.2
      exact ⟨milnorKTensorMap φ x, milnorKTensorMap_mem_milnorKTensorGrading φ n hx,
        by rw [← hxy]; rfl⟩⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

/-- As an element of the Milnor K-ring, the transport of `y` is the image of `y` under the
induced map of Milnor K-rings. -/
@[simp]
theorem milnorKTransport_coe (φ : k₁ →+* k₂) (n : ℕ) (y : MilnorKTheory k₁ n) :
    (milnorKTransport φ n y : MilnorKRing k₂) = milnorKRingMap φ y.1 :=
  rfl

/-- The map of tensor algebras induced by a composite is the composite of the maps. -/
theorem milnorKTensorMap_comp (φ : k₁ →+* k₂) (ψ : k₂ →+* k₃) :
    (milnorKTensorMap ψ).comp (milnorKTensorMap φ) = milnorKTensorMap (ψ.comp φ) := by
  refine TensorAlgebra.hom_ext (LinearMap.ext fun a ↦ ?_)
  show milnorKTensorMap ψ (milnorKTensorMap φ (TensorAlgebra.ι ℤ a)) =
    milnorKTensorMap (ψ.comp φ) (TensorAlgebra.ι ℤ a)
  rw [milnorKTensorMap_ι, milnorKTensorMap_ι, milnorKTensorMap_ι]
  exact congrArg (TensorAlgebra.ι ℤ) (congrArg Additive.ofMul (Units.ext rfl))

/-- The map of tensor algebras induced by the identity is the identity. -/
private theorem milnorKTensorMap_id :
    milnorKTensorMap (RingHom.id k₁) = AlgHom.id ℤ (MilnorKTensorAlgebra k₁) := by
  refine TensorAlgebra.hom_ext (LinearMap.ext fun a ↦ ?_)
  change milnorKTensorMap (RingHom.id k₁) (TensorAlgebra.ι ℤ a) = TensorAlgebra.ι ℤ a
  rw [milnorKTensorMap_ι]
  exact congrArg (TensorAlgebra.ι ℤ) (congrArg Additive.ofMul (Units.ext rfl))

/-- The transport of `y` is the class of the image of any tensor `x` representing `y`. -/
private theorem milnorKTransport_coe_of_mk' (φ : k₁ →+* k₂) (n : ℕ) (y : MilnorKTheory k₁ n)
    (x : MilnorKTensorAlgebra k₁) (hxy : (milnorKSteinbergIdeal k₁).ringCon.mk' x = y.1) :
    (milnorKTransport φ n y : MilnorKRing k₂) =
      (milnorKSteinbergIdeal k₂).ringCon.mk' (milnorKTensorMap φ x) := by
  rw [milnorKTransport_coe, ← hxy]
  rfl

/-- The transport along a composite is the composite of the transports. -/
theorem milnorKTransport_comp (φ : k₁ →+* k₂) (ψ : k₂ →+* k₃) (n : ℕ) :
    (milnorKTransport ψ n).comp (milnorKTransport φ n) = milnorKTransport (ψ.comp φ) n := by
  refine AddMonoidHom.ext fun y ↦ Subtype.ext ?_
  obtain ⟨x, -, hxy⟩ := y.2
  have h := milnorKTransport_coe_of_mk' φ n y x hxy
  rw [AddMonoidHom.comp_apply, milnorKTransport_coe_of_mk' ψ n _ _ h.symm,
    milnorKTransport_coe_of_mk' _ n y x hxy, ← milnorKTensorMap_comp φ ψ]
  rfl

/-- The transport along the identity is the identity. -/
theorem milnorKTransport_id (n : ℕ) :
    milnorKTransport (RingHom.id k₁) n = AddMonoidHom.id (MilnorKTheory k₁ n) := by
  refine AddMonoidHom.ext fun y ↦ Subtype.ext ?_
  obtain ⟨x, -, hxy⟩ := y.2
  rw [AddMonoidHom.id_apply, milnorKTransport_coe_of_mk' _ n y x hxy, milnorKTensorMap_id]
  exact hxy

/-- **The degree-`n` Milnor K-group transported along an isomorphism of fields.** -/
noncomputable def milnorKTransportEquiv (φ : k₁ ≃+* k₂) (n : ℕ) :
    MilnorKTheory k₁ n ≃+ MilnorKTheory k₂ n where
  toFun := milnorKTransport (φ : k₁ →+* k₂) n
  invFun := milnorKTransport (φ.symm : k₂ →+* k₁) n
  left_inv y := by
    have h : milnorKTransport (φ.symm : k₂ →+* k₁) n (milnorKTransport (φ : k₁ →+* k₂) n y) =
        milnorKTransport ((φ.symm : k₂ →+* k₁).comp (φ : k₁ →+* k₂)) n y :=
      DFunLike.congr_fun (milnorKTransport_comp (φ : k₁ →+* k₂) (φ.symm : k₂ →+* k₁) n) y
    rw [h, show (φ.symm : k₂ →+* k₁).comp (φ : k₁ →+* k₂) = RingHom.id k₁ from
      RingHom.ext fun a ↦ φ.symm_apply_apply a, milnorKTransport_id]
    rfl
  right_inv y := by
    have h : milnorKTransport (φ : k₁ →+* k₂) n (milnorKTransport (φ.symm : k₂ →+* k₁) n y) =
        milnorKTransport ((φ : k₁ →+* k₂).comp (φ.symm : k₂ →+* k₁)) n y :=
      DFunLike.congr_fun (milnorKTransport_comp (φ.symm : k₂ →+* k₁) (φ : k₁ →+* k₂) n) y
    rw [h, show (φ : k₁ →+* k₂).comp (φ.symm : k₂ →+* k₁) = RingHom.id k₂ from
      RingHom.ext fun a ↦ φ.apply_symm_apply a, milnorKTransport_id]
    rfl
  map_add' _ _ := map_add (milnorKTransport (φ : k₁ →+* k₂) n) _ _

/-- The isomorphism induced by an isomorphism of fields acts as the transport along it. -/
@[simp]
theorem milnorKTransportEquiv_apply (φ : k₁ ≃+* k₂) (n : ℕ) (y : MilnorKTheory k₁ n) :
    milnorKTransportEquiv φ n y = milnorKTransport (φ : k₁ →+* k₂) n y :=
  rfl

/-- The transport along an isomorphism of fields is bijective. -/
theorem milnorKTransport_bijective (φ : k₁ ≃+* k₂) (n : ℕ) :
    Function.Bijective (milnorKTransport (φ : k₁ →+* k₂) n) :=
  (milnorKTransportEquiv φ n).bijective


/-- Transporting along an isomorphism of fields and then along its inverse is the identity. -/
@[simp]
theorem milnorKTransport_symm_milnorKTransport (φ : k₁ ≃+* k₂) (n : ℕ)
    (y : MilnorKTheory k₁ n) :
    milnorKTransport (φ.symm : k₂ →+* k₁) n (milnorKTransport (φ : k₁ →+* k₂) n y) = y :=
  (milnorKTransportEquiv φ n).symm_apply_apply y

/-- Transporting along the inverse of an isomorphism of fields and then along the isomorphism
is the identity. -/
@[simp]
theorem milnorKTransport_milnorKTransport_symm (φ : k₁ ≃+* k₂) (n : ℕ)
    (y : MilnorKTheory k₂ n) :
    milnorKTransport (φ : k₁ →+* k₂) n (milnorKTransport (φ.symm : k₂ →+* k₁) n y) = y :=
  (milnorKTransportEquiv φ n).apply_symm_apply y

/-- The transport along the identity ring homomorphism, applied to an element. -/
@[simp]
theorem milnorKTransport_id_apply (n : ℕ) (y : MilnorKTheory k₁ n) :
    milnorKTransport (RingHom.id k₁) n y = y :=
  DFunLike.congr_fun (milnorKTransport_id n) y

/-- Transports compose, applied to an element. -/
theorem milnorKTransport_comp_apply (φ : k₁ →+* k₂) (ψ : k₂ →+* k₃) (n : ℕ)
    (y : MilnorKTheory k₁ n) :
    milnorKTransport ψ n (milnorKTransport φ n y) = milnorKTransport (ψ.comp φ) n y :=
  DFunLike.congr_fun (milnorKTransport_comp φ ψ n) y

end
