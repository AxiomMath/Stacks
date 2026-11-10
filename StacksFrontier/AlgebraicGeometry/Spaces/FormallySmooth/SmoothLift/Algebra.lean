module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# Faithfully flat descent of ranges and base change of hom modules

For a faithfully flat `A`-algebra `B'`, membership in the range of an `A`-linear map can be tested
after base change to `B'`. For a finite projective `P`-module `Ω`, forming `Hom_P(Ω, -)` commutes
with the base change `- ⊗_A B'`.

## Main results

* `Module.FaithfullyFlat.mem_range_of_tmul_one_mem_range`: for a faithfully flat `A`-algebra
  `B'` and an `A`-linear map `δ : M → N`, an element `n` of `N` lies in the range of `δ` as soon
  as `n ⊗ 1` lies in the range of `δ ⊗ B'`.
* `Stacks.SmoothLift.homTensorMap_bijective`: for a finite projective `P`-module `Ω`, the
  canonical map `Hom_P(Ω, N) ⊗_A B' → Hom_P(Ω, N ⊗_A B')` is bijective.

## References

* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
-/

@[expose] public section

open TensorProduct

namespace Module.FaithfullyFlat

/-- **An element whose base change lies in the range lies in the range.**  If `A → B'` is
faithfully flat, `δ : M → N` is `A`-linear and `n ⊗ 1` lies in the range of `δ ⊗ B'`, then `n`
lies in the range of `δ`. -/
theorem mem_range_of_tmul_one_mem_range {A B' : Type*} [CommRing A] [CommRing B'] [Algebra A B']
    [Module.FaithfullyFlat A B'] {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N]
    [Module A N] (δ : M →ₗ[A] N) (n : N)
    (h : n ⊗ₜ[A] (1 : B') ∈ LinearMap.range (δ.rTensor B')) : n ∈ LinearMap.range δ := by
  obtain ⟨x, hx⟩ := h
  set π := (LinearMap.range δ).mkQ
  have hπδ : π ∘ₗ δ = 0 := by
    ext m
    simp [π]
  have h0 : (π.rTensor B') (n ⊗ₜ[A] (1 : B')) = 0 := by
    rw [← hx, ← LinearMap.comp_apply, ← LinearMap.rTensor_comp, hπδ, LinearMap.rTensor_zero,
      LinearMap.zero_apply]
  rw [LinearMap.rTensor_tmul] at h0
  have h1 : (1 : B') ⊗ₜ[A] π n = 0 := by
    rw [← TensorProduct.comm_tmul A, h0, map_zero]
  rw [Module.FaithfullyFlat.one_tmul_eq_zero_iff] at h1
  exact (Submodule.Quotient.mk_eq_zero _).mp h1

end Module.FaithfullyFlat

namespace Stacks.SmoothLift

variable {A : Type*} [CommRing A] {P : Type*} [CommRing P]
variable {N : Type*} [AddCommGroup N] [Module A N] [Module P N] [SMulCommClass A P N]
  [SMulCommClass P A N]
variable (B' : Type*) [AddCommGroup B'] [Module A B']

/-- Tensoring on the right with a fixed `b : B'`, as a `P`-linear map `N → N ⊗_A B'`. -/
noncomputable def tmulRightP (b : B') : N →ₗ[P] N ⊗[A] B' where
  toFun n := n ⊗ₜ[A] b
  map_add' n n' := add_tmul n n' b
  map_smul' p n := (smul_tmul' p n b).symm

/-- The canonical map `Hom_P(Ω, N) ⊗_A B' → Hom_P(Ω, N ⊗_A B')`, `φ ⊗ b ↦ (ω ↦ φ ω ⊗ b)`. -/
noncomputable def homTensorMap (Ω : Type*) [AddCommGroup Ω] [Module P Ω] :
    (Ω →ₗ[P] N) ⊗[A] B' →ₗ[A] (Ω →ₗ[P] (N ⊗[A] B')) :=
  TensorProduct.lift (LinearMap.mk₂ A (fun φ b => (tmulRightP B' b).comp φ)
    (fun φ φ' b => by ext ω; simp [tmulRightP, add_tmul])
    (fun a φ b => by ext ω; simp [tmulRightP, smul_tmul'])
    (fun φ b b' => by ext ω; simp [tmulRightP, tmul_add])
    (fun a φ b => by ext ω; simp [tmulRightP]))

/-- `homTensorMap B' Ω` sends `φ ⊗ b` to the map `ω ↦ φ ω ⊗ b`. -/
theorem homTensorMap_tmul (Ω : Type*) [AddCommGroup Ω] [Module P Ω] (φ : Ω →ₗ[P] N) (b : B')
    (ω : Ω) : homTensorMap B' Ω (φ ⊗ₜ[A] b) ω = φ ω ⊗ₜ[A] b := rfl

/-- Precomposition with a `P`-linear map, as an `A`-linear map of hom modules. -/
noncomputable def precomp {Ω Ω' : Type*} [AddCommGroup Ω] [Module P Ω] [AddCommGroup Ω']
    [Module P Ω'] (L : Type*) [AddCommGroup L] [Module A L] [Module P L] [SMulCommClass P A L]
    (g : Ω' →ₗ[P] Ω) : (Ω →ₗ[P] L) →ₗ[A] (Ω' →ₗ[P] L) where
  toFun φ := φ.comp g
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Precomposing with a section `t` of `s` after precomposing with `s` is the identity. -/
theorem precomp_comp_precomp {Ω Ω' : Type*} [AddCommGroup Ω] [Module P Ω] [AddCommGroup Ω']
    [Module P Ω'] (L : Type*) [AddCommGroup L] [Module A L] [Module P L] [SMulCommClass P A L]
    {s : Ω' →ₗ[P] Ω} {t : Ω →ₗ[P] Ω'} (h : s ∘ₗ t = LinearMap.id) :
    precomp (A := A) L t ∘ₗ precomp (A := A) L s = LinearMap.id := by
  ext φ ω
  simp only [precomp, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply, LinearMap.id_apply]
  rw [← LinearMap.comp_apply s t, h, LinearMap.id_apply]

/-- `homTensorMap` is natural in `Ω`: it commutes with precomposition by a `P`-linear map
`g : Ω' → Ω`. -/
theorem homTensorMap_naturality {Ω Ω' : Type*} [AddCommGroup Ω] [Module P Ω] [AddCommGroup Ω']
    [Module P Ω'] (g : Ω' →ₗ[P] Ω) :
    homTensorMap (A := A) (P := P) (N := N) B' Ω' ∘ₗ (precomp (A := A) N g).rTensor B' =
      precomp (A := A) (N ⊗[A] B') g ∘ₗ homTensorMap B' Ω := by
  ext φ b ω
  rfl

/-- For the free module `Ω = Pⁿ`, the map `homTensorMap B' Ω` is bijective. -/
theorem homTensorMap_bijective_pi (n : ℕ) :
    Function.Bijective (homTensorMap (A := A) (P := P) (N := N) B' (Fin n → P)) := by
  let eN : ((Fin n → P) →ₗ[P] N) ≃ₗ[A] (Fin n → N) :=
    (LinearMap.lsum P (fun _ : Fin n => P) A).symm ≪≫ₗ
      LinearEquiv.piCongrRight (fun _ => LinearMap.ringLmapEquivSelf P A N)
  let eNB : ((Fin n → P) →ₗ[P] (N ⊗[A] B')) ≃ₗ[A] (Fin n → N ⊗[A] B') :=
    (LinearMap.lsum P (fun _ : Fin n => P) A).symm ≪≫ₗ
      LinearEquiv.piCongrRight (fun _ => LinearMap.ringLmapEquivSelf P A (N ⊗[A] B'))
  have key : eNB.toLinearMap ∘ₗ homTensorMap (A := A) (N := N) B' (Fin n → P) =
      (TensorProduct.piLeft A B' (fun _ : Fin n => N)).toLinearMap ∘ₗ
        eN.toLinearMap.rTensor B' := by
    ext φ b i
    simp [eN, eNB, homTensorMap_tmul]
  refine (EquivLike.comp_bijective _ eNB).mp ?_
  change Function.Bijective (eNB.toLinearMap ∘ₗ homTensorMap (A := A) (N := N) B' (Fin n → P))
  rw [key]
  exact (TensorProduct.piLeft A B' (fun _ : Fin n => N)).bijective.comp
    (LinearEquiv.rTensor B' eN).bijective

/-- **`Hom_P(Ω, -)` commutes with `- ⊗_A B'` for a finite projective `Ω`.** -/
theorem homTensorMap_bijective (Ω : Type*) [AddCommGroup Ω] [Module P Ω] [Module.Finite P Ω]
    [Module.Projective P Ω] :
    Function.Bijective (homTensorMap (A := A) (P := P) (N := N) B' Ω) := by
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin' P Ω
  obtain ⟨t, ht⟩ := Module.projective_lifting_property s LinearMap.id hs
  have ret : ∀ x, (precomp (A := A) N t).rTensor B' ((precomp (A := A) N s).rTensor B' x) = x :=
    fun x => by
      rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, precomp_comp_precomp N ht,
        LinearMap.rTensor_id, LinearMap.id_apply]
  have hF := homTensorMap_bijective_pi (A := A) (P := P) (N := N) B' n
  have nat_s := homTensorMap_naturality (A := A) (N := N) B' s
  refine ⟨fun x y hxy => ?_, fun ψ => ?_⟩
  · have h1 := hF.1 ((LinearMap.congr_fun nat_s x).trans
      ((congrArg (precomp (A := A) (N ⊗[A] B') s) hxy).trans (LinearMap.congr_fun nat_s y).symm))
    rw [← ret x, ← ret y, h1]
  · obtain ⟨z, hz⟩ := hF.2 (precomp (A := A) (N ⊗[A] B') s ψ)
    refine ⟨(precomp (A := A) N t).rTensor B' z, ?_⟩
    rw [← LinearMap.comp_apply, homTensorMap_naturality (A := A) (N := N) B' t,
      LinearMap.comp_apply, hz]
    exact LinearMap.congr_fun (precomp_comp_precomp (N ⊗[A] B') ht) ψ

end Stacks.SmoothLift
