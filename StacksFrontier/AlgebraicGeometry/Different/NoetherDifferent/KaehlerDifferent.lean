module

public import Mathlib.RingTheory.Kaehler.Basic
public import StacksFrontier.AlgebraicGeometry.Different.NoetherDifferent.Basic
public import StacksFrontier.RingTheory.Fitting.Basic

/-!
# The Kähler different is contained in the Noether different

Let `B` be an algebra essentially of finite type over a ring `A`, let `I` be the kernel of the
multiplication map `μ : B ⊗[A] B → B` and let `J ⊆ B ⊗[A] B` be its annihilator. Then the zeroth
Fitting ideal of `Ω_{B/A}` (the Kähler different) is contained in `μ(J)` (the Noether different).

## Main results

* `Stacks.Discriminant.fittingIdeal_kaehlerDifferential_le_noetherDifferent`: the inclusion.

## Implementation notes

The module `Ω_{B/A} = I/I²` is the base change of `I` along `μ`: the map `I → B ⊗_{B ⊗ B} I`,
`i ↦ 1 ⊗ i`, kills `I²` and induces a surjection `Ω_{B/A} → B ⊗_{B ⊗ B} I`. Fitting ideals grow
along surjections and commute with base change, so the Kähler different is contained in
`μ(Fitt₀(I))`, and `Fitt₀(I) ⊆ Ann(I) = J`.

## References

* [Stacks Project, Tag 0BVV](https://stacks.math.columbia.edu/tag/0BVV)
* [Stacks Project, Tag 0BVL](https://stacks.math.columbia.edu/tag/0BVL)
-/

@[expose] public section

open scoped TensorProduct

universe u v

namespace Stacks.Discriminant

variable (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]

/-- The `B`-linear map `I → B ⊗_{B ⊗ B} I`, `i ↦ 1 ⊗ i`, where `I` is the kernel of the
multiplication map and `B` is a `B ⊗[A] B`-algebra through multiplication. -/
noncomputable def kaehlerIdealToBaseChange :
    letI : Algebra (B ⊗[A] B) B := (Algebra.TensorProduct.lmul' A).toRingHom.toAlgebra
    KaehlerDifferential.ideal A B →ₗ[B] B ⊗[B ⊗[A] B] KaehlerDifferential.ideal A B :=
  letI : Algebra (B ⊗[A] B) B := (Algebra.TensorProduct.lmul' A).toRingHom.toAlgebra
  { toFun := fun x ↦ (1 : B) ⊗ₜ x
    map_add' := fun x y ↦ TensorProduct.tmul_add _ _ _
    map_smul' := fun b x ↦ by
      have hx : b • x = (b ⊗ₜ[A] (1 : B)) • x := Subtype.ext <| by
        rw [Submodule.coe_smul_of_tower, Submodule.coe_smul, Algebra.smul_def, smul_eq_mul]
        rfl
      rw [hx, ← TensorProduct.smul_tmul]
      change (Algebra.TensorProduct.lmul' A (b ⊗ₜ[A] (1 : B)) * 1) ⊗ₜ x = _
      rw [Algebra.TensorProduct.lmul'_apply_tmul, mul_one, mul_one, RingHom.id_apply,
        TensorProduct.smul_tmul', smul_eq_mul, mul_one] }

variable [Algebra.EssFiniteType A B]

/-- **The Kähler different is contained in the Noether different.** For an algebra `B`
essentially of finite type over `A`, the zeroth Fitting ideal of `Ω_{B/A}` is contained in the
image under multiplication of the annihilator of the kernel of `B ⊗[A] B → B`. -/
theorem fittingIdeal_kaehlerDifferential_le_noetherDifferent :
    fittingIdeal (R := B) (M := Ω[B⁄A]) 0 ≤ noetherDifferent A B := by
  let : Algebra (B ⊗[A] B) B := (Algebra.TensorProduct.lmul' A).toRingHom.toAlgebra
  let I := KaehlerDifferential.ideal A B
  have : Module.Finite (B ⊗[A] B) I :=
    Module.Finite.iff_fg.mpr (KaehlerDifferential.ideal_fg A B)
  let g := kaehlerIdealToBaseChange A B
  have hg : ∀ x y : I, g (x * y) = 0 := fun x y ↦ by
    change (1 : B) ⊗ₜ[B ⊗[A] B] ((x : B ⊗[A] B) • y) = 0
    rw [← TensorProduct.smul_tmul]
    change (Algebra.TensorProduct.lmul' A (x : B ⊗[A] B) * 1) ⊗ₜ[B ⊗[A] B] y = 0
    rw [show Algebra.TensorProduct.lmul' A (x : B ⊗[A] B) = 0 from x.2, zero_mul,
      TensorProduct.zero_tmul]
  have hsurj : Function.Surjective g := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul b x =>
      refine ⟨(b ⊗ₜ[A] (1 : B)) • x, ?_⟩
      change (1 : B) ⊗ₜ[B ⊗[A] B] ((b ⊗ₜ[A] (1 : B)) • x) = _
      rw [← TensorProduct.smul_tmul]
      change (Algebra.TensorProduct.lmul' A (b ⊗ₜ[A] (1 : B)) * 1) ⊗ₜ x = _
      rw [Algebra.TensorProduct.lmul'_apply_tmul, mul_one, mul_one]
    | add z₁ z₂ h₁ h₂ =>
      obtain ⟨x₁, rfl⟩ := h₁
      obtain ⟨x₂, rfl⟩ := h₂
      exact ⟨x₁ + x₂, map_add g x₁ x₂⟩
  let L : Ω[B⁄A] →ₗ[B] B ⊗[B ⊗[A] B] I := Ideal.Cotangent.lift g hg
  have hL : Function.Surjective L := (Ideal.Cotangent.lift_surjective_iff g hg).mpr hsurj
  have hle := (fittingIdeal_basic_properties.{v, v, v, v} (R := B) (M := Ω[B⁄A])).2.2.2.2.1 _ L 0 hL
  have hbc := (fittingIdeal_basic_properties.{v, v, v, v} (R := B ⊗[A] B) (M := I)).2.2.1 B 0
  have hann := (fittingIdeal_basic_properties.{v, v, v, v} (R := B ⊗[A] B) (M := I)).2.2.2.2.2.1
  refine hle.trans ?_
  rw [hbc]
  exact Ideal.map_mono (hann.trans fun t ht ↦ Submodule.mem_annihilator.mpr fun y hy ↦
    congrArg Subtype.val ((Module.mem_annihilator.mp ht) ⟨y, hy⟩))

end Stacks.Discriminant

end
