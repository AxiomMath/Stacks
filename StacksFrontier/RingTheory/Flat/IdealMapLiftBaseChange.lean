module

public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Ideal.Maps

/-!
# `Algebra.idealMap` after a flat base change

For `S` a flat `R`-algebra, the base change of `Algebra.idealMap S I` along `S` is bijective:
`I ⊗[R] S` is the ideal `I.map (algebraMap R S)`. Two modules proved this privately; it lives
here once.

## Main results

* `idealMap_liftBaseChange_bijective`
-/

@[expose] public section

/-- For a flat algebra `S`, the base change of `Algebra.idealMap S I` is bijective. -/
public theorem idealMap_liftBaseChange_bijective
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
    (I : Ideal R) : Function.Bijective ((Algebra.idealMap S I).liftBaseChange S) := by
  let f := (Algebra.idealMap S I).liftBaseChange S
  have hf : (I.map (algebraMap R S)).subtype ∘ₗ f =
      (TensorProduct.AlgebraTensorModule.rid R S S).toLinearMap ∘ₗ I.subtype.baseChange S := by
    ext x
    simp [f, Algebra.smul_def]
  constructor
  · apply Function.Injective.of_comp (f := (I.map (algebraMap R S)).subtype)
    change Function.Injective ((I.map (algebraMap R S)).subtype ∘ₗ f)
    rw [hf, LinearMap.coe_comp]
    exact (TensorProduct.AlgebraTensorModule.rid R S S).injective.comp
      (Module.Flat.lTensor_preserves_injective_linearMap I.subtype Subtype.val_injective)
  · rintro ⟨x, hx⟩
    change x ∈ Submodule.span S ((algebraMap R S) '' (I : Set R)) at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      exact ⟨1 ⊗ₜ ⟨y, hy⟩, by ext; simp [Algebra.idealMap_apply_coe]⟩
    | zero => exact ⟨0, by ext; simp⟩
    | add x y hx hy hx' hy' =>
      obtain ⟨a, ha⟩ := hx'
      obtain ⟨b, hb⟩ := hy'
      exact ⟨a + b, by rw [map_add, ha, hb]; rfl⟩
    | smul a x hx hx' =>
      obtain ⟨b, hb⟩ := hx'
      exact ⟨a • b, by rw [map_smul, hb]; rfl⟩
end
