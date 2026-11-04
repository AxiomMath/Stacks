module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The kernel of a square-zero surjection as a module over the quotient

Let `ψ : A →+* B` be a surjective ring map whose kernel `I` has square zero. Then `I` is killed by
`I`, so it is a module over `B = A/I`: an element `b` of `B` acts by multiplication by any lift
of `b` to `A`. This file packages it as an object of `ModuleCat B`, records that restricting it
back along `ψ` returns the `A`-module `I`, and that the maps between such kernels induced by a
commutative triangle of surjections are `B`-linear.

In the body of [Stacks Project, Tag 0D3X] these are the `R₁`-modules `Iₙ = Ker(Rₙ → R₁)`, for a
tower `(Rₙ)` of rings with surjective, square-zero transition maps, whose limit `lim Iₙ` enters the
base-ring tensor product `𝒪_{X₁} ⊗_{R₁} lim Iₙ` of [Stacks Project, Tag 0D3F].

## Main definitions

* `RingHom.squareZeroKerModule` and `RingHom.squareZeroKer`: the kernel of a surjective
  `ψ : A →+* B` with square-zero kernel, as a `B`-module.
* `RingHom.restrictScalarsSquareZeroKerIso`: its restriction along `ψ` is the `A`-module
  `Ker(ψ)`.
* `RingHom.squareZeroKerMap`: the `B`-linear map `Ker(ψ') ⟶ Ker(ψ)` induced by `τ : A' →+* A`
  with `ψ ∘ τ = ψ'`.

## References

* [Stacks Project, Tag 0D3X](https://stacks.math.columbia.edu/tag/0D3X)
-/

@[expose] public noncomputable section

universe u

namespace RingHom

variable {A B : Type u} [CommRing A] [CommRing B] (ψ : A →+* B)

/-- A square-zero ideal kills itself. -/
theorem isTorsionBySet_ker_of_sq_eq_bot (hsq : RingHom.ker ψ ^ 2 = ⊥) :
    Module.IsTorsionBySet A (RingHom.ker ψ) (RingHom.ker ψ : Set A) := fun x a => by
  refine Subtype.ext ?_
  have hmem := Ideal.mul_mem_mul a.2 x.2
  rw [← pow_two, hsq, Ideal.mem_bot] at hmem
  simpa only [Submodule.coe_smul, smul_eq_mul, ZeroMemClass.coe_zero] using hmem

/-- **The `B`-module structure on the kernel of a surjection `ψ : A →+* B` with square-zero
kernel.** `Ker(ψ)` is killed by `Ker(ψ)`, hence a module over `A ⧸ Ker(ψ) = B`; an element `b`
of `B` acts by multiplication by any lift of `b` to `A` (`RingHom.squareZeroKerModule_smul`). -/
@[instance_reducible]
def squareZeroKerModule (hψ : Function.Surjective ψ) (hsq : RingHom.ker ψ ^ 2 = ⊥) :
    Module B (RingHom.ker ψ) :=
  letI := (isTorsionBySet_ker_of_sq_eq_bot ψ hsq).module
  Module.compHom _ (RingHom.quotientKerEquivOfSurjective hψ).symm.toRingHom

/-- An element `ψ a` of `B` acts on the kernel of `ψ` as multiplication by `a`. -/
theorem squareZeroKerModule_smul (hψ : Function.Surjective ψ) (hsq : RingHom.ker ψ ^ 2 = ⊥)
    (a : A) (x : RingHom.ker ψ) :
    letI := squareZeroKerModule ψ hψ hsq
    ((ψ a • x : RingHom.ker ψ) : A) = a * (x : A) := by
  have he : (RingHom.quotientKerEquivOfSurjective hψ).symm (ψ a) = Ideal.Quotient.mk _ a :=
    (RingEquiv.symm_apply_eq _).2 (RingHom.quotientKerEquivOfSurjective_apply_mk hψ a).symm
  let := (isTorsionBySet_ker_of_sq_eq_bot ψ hsq).module
  show (((RingHom.quotientKerEquivOfSurjective hψ).symm (ψ a) • x : RingHom.ker ψ) : A) = _
  rw [he, Module.IsTorsionBySet.mk_smul]
  rfl

/-- **The kernel of a surjection with square-zero kernel, as a module over the target**, with
the module structure `RingHom.squareZeroKerModule`. -/
def squareZeroKer (hψ : Function.Surjective ψ) (hsq : RingHom.ker ψ ^ 2 = ⊥) :
    ModuleCat.{u} B :=
  letI := squareZeroKerModule ψ hψ hsq
  ModuleCat.of B (RingHom.ker ψ)

/-- **Restricting `Ker(ψ)` back along `ψ` returns the `A`-module `Ker(ψ)`.** -/
def restrictScalarsSquareZeroKerIso (hψ : Function.Surjective ψ)
    (hsq : RingHom.ker ψ ^ 2 = ⊥) :
    (ModuleCat.restrictScalars.{u} ψ).obj (squareZeroKer ψ hψ hsq) ≅
      ModuleCat.of A (RingHom.ker ψ) :=
  letI := squareZeroKerModule ψ hψ hsq
  { hom := ModuleCat.ofHom (X := (ModuleCat.restrictScalars.{u} ψ).obj (squareZeroKer ψ hψ hsq))
      { toFun := fun x => (show RingHom.ker ψ from x)
        map_add' := fun _ _ => rfl
        map_smul' := fun a x => Subtype.ext (squareZeroKerModule_smul ψ hψ hsq a x) }
    inv := ModuleCat.ofHom (Y := (ModuleCat.restrictScalars.{u} ψ).obj (squareZeroKer ψ hψ hsq))
      { toFun := fun x => (show (ModuleCat.restrictScalars.{u} ψ).obj (squareZeroKer ψ hψ hsq)
          from x)
        map_add' := fun _ _ => rfl
        map_smul' := fun a x => Subtype.ext (squareZeroKerModule_smul ψ hψ hsq a x).symm }
    hom_inv_id := rfl
    inv_hom_id := rfl }

variable (hψ : Function.Surjective ψ) (hsq : RingHom.ker ψ ^ 2 = ⊥)
  {A' : Type u} [CommRing A'] (ψ' : A' →+* B) (hψ' : Function.Surjective ψ')
  (hsq' : RingHom.ker ψ' ^ 2 = ⊥) (τ : A' →+* A) (hτ : ψ.comp τ = ψ')

/-- The map `Ker(ψ') ⟶ Ker(ψ)` induced by `τ : A' →+* A` with `ψ ∘ τ = ψ'`. -/
def squareZeroKerRestrict (x : RingHom.ker ψ') : RingHom.ker ψ :=
  ⟨τ x, by
    rw [RingHom.mem_ker, ← RingHom.comp_apply, hτ]
    exact x.2⟩

/-- **The `B`-linear map `Ker(ψ') ⟶ Ker(ψ)` induced by `τ : A' →+* A` with `ψ ∘ τ = ψ'`.** -/
def squareZeroKerMap : squareZeroKer ψ' hψ' hsq' ⟶ squareZeroKer ψ hψ hsq :=
  letI := squareZeroKerModule ψ hψ hsq
  letI := squareZeroKerModule ψ' hψ' hsq'
  ModuleCat.ofHom
    { toFun := squareZeroKerRestrict ψ ψ' τ hτ
      map_add' := fun x y => Subtype.ext (map_add τ x.1 y.1)
      map_smul' := fun b x => by
        obtain ⟨a, rfl⟩ := hψ' b
        refine Subtype.ext ?_
        change τ ((ψ' a • x : RingHom.ker ψ') : A') = ((ψ' a • _ : RingHom.ker ψ) : A)
        have h1 : ψ (τ a) = ψ' a := by rw [← hτ]; rfl
        rw [squareZeroKerModule_smul ψ' hψ' hsq' a x, map_mul, ← h1,
          squareZeroKerModule_smul ψ hψ hsq (τ a)]
        rfl }

/-- `RingHom.squareZeroKerMap` sends `x` to `τ x`. -/
theorem squareZeroKerMap_apply (x : RingHom.ker ψ') :
    (squareZeroKerMap ψ hψ hsq ψ' hψ' hsq' τ hτ).hom x = squareZeroKerRestrict ψ ψ' τ hτ x :=
  rfl

section Transport

variable {A B A' B' : Type u} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
  (ψ : A →+* B) (hψ : Function.Surjective ψ) (hsq : RingHom.ker ψ ^ 2 = ⊥)
  (ψ' : A' →+* B') (hψ' : Function.Surjective ψ') (hsq' : RingHom.ker ψ' ^ 2 = ⊥)
  (α : A ≃+* A') (β : B →+* B') (hαβ : ψ'.comp α.toRingHom = β.comp ψ)

include hαβ in
/-- `α` carries the kernel of `ψ` into the kernel of `ψ'`. -/
theorem map_mem_ker_of_ringEquiv_comp_eq (x : RingHom.ker ψ) : α x.1 ∈ RingHom.ker ψ' := by
  rw [RingHom.mem_ker]
  have h := congrArg (fun f => f x.1) hαβ
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom] at h
  rw [h, (RingHom.mem_ker).1 x.2, map_zero]

include hαβ in
/-- `α⁻¹` carries the kernel of `ψ'` into the kernel of `ψ`, when `β` is injective. -/
theorem symm_map_mem_ker_of_comp_eq (hβ : Function.Injective β) (y : RingHom.ker ψ') :
    α.symm y.1 ∈ RingHom.ker ψ := by
  rw [RingHom.mem_ker]
  refine hβ ?_
  have h := congrArg (fun f => f (α.symm y.1)) hαβ
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    RingEquiv.apply_symm_apply] at h
  rw [← h, (RingHom.mem_ker).1 y.2, map_zero]

/-- **Transport of square-zero kernels along a commutative square.** For a commutative square
`ψ' ∘ α = β ∘ ψ` of rings with `α` an isomorphism and `β` injective, `α` identifies the
`B`-module `Ker(ψ)` with the `B'`-module `Ker(ψ')` read over `B` through `β`. -/
def squareZeroKerRestrictScalarsIso (hβ : Function.Injective β) :
    squareZeroKer ψ hψ hsq ≅ (ModuleCat.restrictScalars.{u} β).obj (squareZeroKer ψ' hψ' hsq') :=
  letI := squareZeroKerModule ψ hψ hsq
  letI := squareZeroKerModule ψ' hψ' hsq'
  have hsmul : ∀ (b : B) (x : RingHom.ker ψ),
      α ((b • x : RingHom.ker ψ) : A) = ((β b • (⟨α x.1, map_mem_ker_of_ringEquiv_comp_eq (ψ := ψ)
        (ψ' := ψ') (α := α) (β := β) hαβ x⟩ : RingHom.ker ψ') : RingHom.ker ψ') : A') :=
    fun b x => by
    obtain ⟨a, rfl⟩ := hψ b
    have h := congrArg (fun f => f a) hαβ
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom] at h
    rw [squareZeroKerModule_smul ψ hψ hsq, ← h, squareZeroKerModule_smul ψ' hψ' hsq', map_mul]
  let L : squareZeroKer ψ hψ hsq ≃ₗ[B]
      (ModuleCat.restrictScalars.{u} β).obj (squareZeroKer ψ' hψ' hsq') :=
    { toFun := fun x => (show RingHom.ker ψ' from ⟨α x.1, map_mem_ker_of_ringEquiv_comp_eq (ψ := ψ)
        (ψ' := ψ') (α := α) (β := β) hαβ x⟩)
      map_add' := fun x y => Subtype.ext (map_add α x.1 y.1)
      map_smul' := fun b x => Subtype.ext (hsmul b x)
      invFun := fun y => (show RingHom.ker ψ from ⟨α.symm (show RingHom.ker ψ' from y).1,
        symm_map_mem_ker_of_comp_eq (ψ := ψ) (ψ' := ψ') (α := α) (β := β) hαβ hβ y⟩)
      left_inv := fun x => Subtype.ext (α.symm_apply_apply (show RingHom.ker ψ from x).1)
      right_inv := fun y => Subtype.ext (α.apply_symm_apply (show RingHom.ker ψ' from y).1) }
  L.toModuleIso

end Transport

end RingHom

end
