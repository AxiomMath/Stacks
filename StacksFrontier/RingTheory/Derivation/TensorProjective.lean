module

public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.RingTheory.Kaehler.Basic

/-!
# Derivations into a tensor product, for finite projective differentials

Let `R → C` be a ring map whose module of differentials `Ω_{C/R}` is a finite projective
`C`-module, let `M` be a `C`-module and `B` an `R`-module. Then every `R`-derivation of `C` into
`M ⊗_R B` is a sum of derivations into `M` tensored with elements of `B`, uniquely:
```
Der_R(C, M) ⊗_R B ≅ Der_R(C, M ⊗_R B),   d ⊗ b ↦ (c ↦ d(c) ⊗ b).
```
Indeed `Der_R(C, N) = Hom_C(Ω_{C/R}, N)`, and `Hom_C(Ω, -)` commutes with `- ⊗_R B` for `Ω`
finite projective, being `Ω^∨ ⊗_C -`. This is used for smooth `R → C`, whose differentials are
finite projective.

## Main definitions

* `Derivation.rTensorHom`: the map `Der_R(C, M) ⊗_R B → Der_R(C, M ⊗_R B)`.
* `Derivation.along`: the derivations of `C` along an algebra map `ρ : C → A`, valued in an
  `A`-module `M`.
* `Derivation.alongRTensorHom`: the map `Der_ρ(C, M) ⊗_R B → Der_ρ(C, M ⊗_R B)`.

## Main results

* `Derivation.bijective_rTensorHom`: `rTensorHom` is bijective when `Ω_{C/R}` is finite
  projective.
* `Derivation.bijective_alongRTensorHom`: `alongRTensorHom` is bijective when `Ω_{C/R}` is finite
  projective.

## References

* [Stacks Project, Tag 00RM](https://stacks.math.columbia.edu/tag/00RM)
-/

@[expose] public noncomputable section

open TensorProduct

namespace Derivation

variable (R C : Type*) [CommRing R] [CommRing C] [Algebra R C]
  (M : Type*) [AddCommGroup M] [Module R M] [Module C M] [IsScalarTower R C M]
  (B : Type*) [AddCommGroup B] [Module R B]

/-- The map `Der_R(C, M) ⊗_R B → Der_R(C, M ⊗_R B)`, `d ⊗ b ↦ (c ↦ d(c) ⊗ b)`. -/
def rTensorHom : Derivation R C M ⊗[R] B →ₗ[R] Derivation R C (M ⊗[R] B) :=
  TensorProduct.lift
    { toFun := fun d =>
        { toFun := fun b => ((AlgebraTensorModule.mk R C M B).flip b).compDer d
          map_add' := fun b b' => by ext c; simp
          map_smul' := fun r b => by ext c; simp }
      map_add' := fun d d' => by ext b c; simp
      map_smul' := fun r d => by ext b c; simp [smul_tmul'] }

/-- `rTensorHom` sends `d ⊗ b` to the derivation `c ↦ d(c) ⊗ b`. -/
@[simp]
lemma rTensorHom_tmul_apply (d : Derivation R C M) (b : B) (c : C) :
    rTensorHom R C M B (d ⊗ₜ b) c = d c ⊗ₜ b := rfl

/-- The map `Hom_C(Ω, M) ⊗_R B → Hom_C(Ω, M ⊗_R B)`, `φ ⊗ b ↦ (ω ↦ φ(ω) ⊗ b)`. -/
def homRTensor (Ω : Type*) [AddCommGroup Ω] [Module C Ω] :
    (Ω →ₗ[C] M) ⊗[R] B →ₗ[R] (Ω →ₗ[C] M ⊗[R] B) :=
  TensorProduct.lift
    { toFun := fun φ =>
        { toFun := fun b => ((AlgebraTensorModule.mk R C M B).flip b) ∘ₗ φ
          map_add' := fun b b' => by ext ω; simp
          map_smul' := fun r b => by ext ω; simp }
      map_add' := fun φ φ' => by ext b ω; simp [add_tmul]
      map_smul' := fun r φ => by
        ext b ω
        simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.coe_comp, Function.comp_apply,
          LinearMap.smul_apply, RingHom.id_apply]
        exact LinearMap.map_smul_of_tower _ r (φ ω) }

/-- `homRTensor` sends `φ ⊗ b` to the linear map `ω ↦ φ(ω) ⊗ b`. -/
@[simp]
lemma homRTensor_tmul_apply (Ω : Type*) [AddCommGroup Ω] [Module C Ω] (φ : Ω →ₗ[C] M) (b : B)
    (ω : Ω) : homRTensor R C M B Ω (φ ⊗ₜ b) ω = φ ω ⊗ₜ b := rfl

variable {R C M B}

/-- `Hom_C(Ω, M) ⊗_R B → Hom_C(Ω, M ⊗_R B)` is bijective for a finite projective `Ω`. -/
lemma bijective_homRTensor (Ω : Type*) [AddCommGroup Ω] [Module C Ω] [Module.Finite C Ω]
    [Module.Projective C Ω] : Function.Bijective (homRTensor R C M B Ω) := by
  have hL : homRTensor R C M B Ω =
      ((dualTensorHomEquiv C Ω (M ⊗[R] B)).toLinearMap.restrictScalars R) ∘ₗ
        ((AlgebraTensorModule.assoc R C C (Module.Dual C Ω) M B).toLinearMap.restrictScalars R)
          ∘ₗ (LinearEquiv.rTensor B
            ((dualTensorHomEquiv C Ω M).symm.restrictScalars R)).toLinearMap := by
    apply TensorProduct.ext'
    intro φ b
    obtain ⟨t, rfl⟩ := (dualTensorHomEquiv C Ω M).surjective φ
    induction t using TensorProduct.inductionOn with
    | add s t hs ht =>
      simp only [map_add, add_tmul] at hs ht ⊢
      rw [hs, ht]
    | tmul f m =>
      ext ω
      simp [dualTensorHomEquiv, dualTensorHom_apply, smul_tmul']
  rw [hL]
  exact (dualTensorHomEquiv C Ω (M ⊗[R] B)).bijective.comp
    ((AlgebraTensorModule.assoc R C C (Module.Dual C Ω) M B).bijective.comp
      (LinearEquiv.rTensor B ((dualTensorHomEquiv C Ω M).symm.restrictScalars R)).bijective)

/-- Bijectivity transfers along `R`-linear equivalences on the left tensor factor and target. -/
private theorem bijective_of_apply_tmul_eq {R X Y X' Y' B : Type*} [CommRing R]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup X'] [AddCommGroup Y'] [AddCommGroup B]
    [Module R X] [Module R Y] [Module R X'] [Module R Y'] [Module R B]
    (e₁ : X ≃ₗ[R] X') (e₂ : Y ≃ₗ[R] Y') (f : X' ⊗[R] B →ₗ[R] Y') (g : X ⊗[R] B →ₗ[R] Y)
    (h : ∀ x b, g (x ⊗ₜ b) = e₂.symm (f (e₁ x ⊗ₜ b))) (hf : Function.Bijective f) :
    Function.Bijective g := by
  have : g = e₂.symm.toLinearMap ∘ₗ f ∘ₗ (LinearEquiv.rTensor B e₁).toLinearMap :=
    TensorProduct.ext' fun x b => by simpa using h x b
  rw [this]
  exact e₂.symm.bijective.comp (hf.comp (LinearEquiv.rTensor B e₁).bijective)

/-- **Derivations into `M ⊗_R B`**, for finite projective differentials: the map
`Der_R(C, M) ⊗_R B → Der_R(C, M ⊗_R B)` is bijective. -/
theorem bijective_rTensorHom [Module.Finite C Ω[C⁄R]] [Module.Projective C Ω[C⁄R]] :
    Function.Bijective (rTensorHom R C M B) := by
  refine bijective_of_apply_tmul_eq
    ((KaehlerDifferential.linearMapEquivDerivation R C).symm.restrictScalars R)
    ((KaehlerDifferential.linearMapEquivDerivation R C).symm.restrictScalars R) _ _ ?_
    (bijective_homRTensor (R := R) (C := C) (M := M) (B := B) Ω[C⁄R])
  intro d b
  ext c
  simp

/-! ### Derivations along an algebra map -/

section Along

variable {R C : Type*} [CommRing R] [CommRing C] [Algebra R C] {A : Type*} [CommRing A]
  [Algebra R A] (ρ : C →ₐ[R] A) (M : Type*) [AddCommGroup M] [Module A M] [Module R M]
  [IsScalarTower R A M]

/-- **The derivations of `C` along an algebra map `ρ : C → A`**, valued in an `A`-module `M`:
the `R`-linear maps `d : C → M` with `d(c c') = ρ(c) d(c') + ρ(c') d(c)`. -/
def along : Submodule R (C →ₗ[R] M) where
  carrier := {d | ∀ c c', d (c * c') = ρ c • d c' + ρ c' • d c}
  add_mem' {d d'} hd hd' c c' := by
    simp only [LinearMap.add_apply, hd c c', hd' c c', smul_add]; abel
  zero_mem' c c' := by simp
  smul_mem' r {d} hd c c' := by
    simp only [LinearMap.smul_apply, hd c c', smul_add]
    rw [smul_comm r (ρ c), smul_comm r (ρ c')]

variable (B : Type*) [AddCommGroup B] [Module R B]

variable {ρ M} in
/-- A derivation along `ρ` vanishes at `1`. -/
lemma along_map_one (d : along ρ M) : d.1 1 = 0 := by
  have h := d.2 1 1
  simp only [mul_one, map_one, one_smul] at h
  have h2 : d.1 1 + d.1 1 = d.1 1 + 0 := by rw [← h, add_zero]
  exact add_left_cancel h2

/-- For a derivation `d` along `ρ` valued in `M` and `b : B`, the map `c ↦ d(c) ⊗ b` is a
derivation along `ρ` valued in `M ⊗_R B`. -/
lemma along_rTensor_mem (d : along ρ M) (b : B) :
    ((AlgebraTensorModule.mk R A M B).flip b).restrictScalars R ∘ₗ d.1 ∈ along ρ (M ⊗[R] B) := by
  intro c c'
  change d.1 (c * c') ⊗ₜ b = ρ c • (d.1 c' ⊗ₜ[R] b) + ρ c' • (d.1 c ⊗ₜ[R] b)
  rw [d.2 c c', add_tmul, smul_tmul', smul_tmul']

/-- The map `Der_ρ(C, M) ⊗_R B → Der_ρ(C, M ⊗_R B)`, `d ⊗ b ↦ (c ↦ d(c) ⊗ b)`. -/
def alongRTensorHom : along ρ M ⊗[R] B →ₗ[R] along ρ (M ⊗[R] B) :=
  TensorProduct.lift
    { toFun := fun d =>
        { toFun := fun b => ⟨_, along_rTensor_mem ρ M B d b⟩
          map_add' := fun b b' => by ext c; simp
          map_smul' := fun r b => by ext c; simp }
      map_add' := fun d d' => by ext b c; simp [add_tmul]
      map_smul' := fun r d => by ext b c; simp [smul_tmul'] }

/-- `alongRTensorHom` sends `d ⊗ b` to the derivation along `ρ` given by `c ↦ d(c) ⊗ b`. -/
@[simp]
lemma alongRTensorHom_tmul_apply (d : along ρ M) (b : B) (c : C) :
    (alongRTensorHom ρ M B (d ⊗ₜ b)).1 c = d.1 c ⊗ₜ b := rfl

/-- **Derivations along `ρ` into `M ⊗_R B`**, for finite projective differentials: the map
`Der_ρ(C, M) ⊗_R B → Der_ρ(C, M ⊗_R B)` is bijective. -/
theorem bijective_alongRTensorHom [Module.Finite C Ω[C⁄R]] [Module.Projective C Ω[C⁄R]] :
    Function.Bijective (alongRTensorHom ρ M B) := by
  let : Module C M := Module.compHom M ρ.toRingHom
  have : IsScalarTower R C M := ⟨fun r c m => by
    change ρ (r • c) • m = r • (ρ c • m)
    rw [ρ.map_smul_of_tower, smul_assoc]⟩
  have hsmul : ∀ (c : C) (t : M ⊗[R] B), c • t = ρ c • t := fun c t => by
    induction t using TensorProduct.inductionOn with
    | add s t hs ht => rw [smul_add, smul_add, hs, ht]
    | tmul m b => rfl
  let e₁ : along ρ M ≃ₗ[R] Derivation R C M :=
    { toFun := fun d => ⟨d.1, along_map_one d, fun c c' => d.2 c c'⟩
      invFun := fun D => ⟨D.toLinearMap, fun c c' => D.leibniz c c'⟩
      map_add' := fun d d' => rfl
      map_smul' := fun r d => rfl
      left_inv := fun d => rfl
      right_inv := fun D => rfl }
  let e₂ : along ρ (M ⊗[R] B) ≃ₗ[R] Derivation R C (M ⊗[R] B) :=
    { toFun := fun d => ⟨d.1, along_map_one d, fun c c' => by
        change d.1 (c * c') = c • d.1 c' + c' • d.1 c
        rw [d.2 c c', hsmul, hsmul]⟩
      invFun := fun D => ⟨D.toLinearMap, fun c c' => by
        change D (c * c') = ρ c • D c' + ρ c' • D c
        rw [D.leibniz, hsmul, hsmul]⟩
      map_add' := fun d d' => rfl
      map_smul' := fun r d => rfl
      left_inv := fun d => rfl
      right_inv := fun D => rfl }
  refine bijective_of_apply_tmul_eq e₁ e₂ _ _ (fun d b => rfl)
    (Derivation.bijective_rTensorHom (R := R) (C := C) (M := M) (B := B))

end Along

end Derivation

end
