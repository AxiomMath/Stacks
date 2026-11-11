module

public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Derivations at a section are coordinates in a basis of the cotangent space

Let `R` be a local ring, `O` an `R`-algebra whose module of differentials `Ω[O⁄R]` is finite
projective, and `ε : O →ₐ[R] R` a section of the structure map. For an `R`-module `M`, made an
`O`-module through `ε`, an `R`-derivation `D : O → M` is an `R`-linear map with
`D (a * b) = ε a • D b + ε b • D a`. The cotangent space `R ⊗_O Ω[O⁄R]` at `ε` is finite
projective over the local ring `R`, hence free of some rank `g`, and its basis can be taken of
the form `1 ⊗ d vₖ`. The derivations `O → M` are then exactly the families of `g` elements of
`M`, through evaluation at `v₁, …, v_g`, for every `M` at once.

## Main results

* `KaehlerDifferential.exists_derivation_coordinates`: there are `g` and `v : Fin g → O` such
  that for every `R`-module `M` a derivation at `ε` vanishing at every `vₖ` vanishes, and every
  family of `g` elements of `M` is the family of values at the `vₖ` of a derivation at `ε`.
-/

@[expose] public noncomputable section

open TensorProduct

universe u w

namespace KaehlerDifferential

variable {R O : Type u} [CommRing R] [CommRing O] [Algebra R O] (ε : O →ₐ[R] R)

/-- Every element of the cotangent space `R ⊗_O Ω[O⁄R]` at a section `ε` is `1 ⊗ d a` for some
`a`, for the `O`-algebra structure of `R` given by `ε`. -/
theorem exists_one_tmul_D_eq (t : letI : Algebra O R := ε.toRingHom.toAlgebra; R ⊗[O] Ω[O⁄R]) :
    letI : Algebra O R := ε.toRingHom.toAlgebra
    ∃ a : O, (1 : R) ⊗ₜ[O] D R O a = t := by
  let : Algebra O R := ε.toRingHom.toAlgebra
  have key : ∀ (x : Ω[O⁄R]) (r : R), ∃ a : O, (1 : R) ⊗ₜ[O] D R O a = r ⊗ₜ[O] x := by
    intro x
    have hx : x ∈ Submodule.span O (Set.range (D R O)) := by
      rw [span_range_derivation]; trivial
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, rfl⟩ := hx
      intro r
      refine ⟨algebraMap R O r * b, ?_⟩
      rw [Derivation.leibniz, Derivation.map_algebraMap, smul_zero, add_zero, tmul_smul,
        smul_tmul', Algebra.smul_def, mul_one, RingHom.algebraMap_toAlgebra]
      congr 1
      exact ε.commutes r
    | zero => intro r; exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      intro r
      obtain ⟨a₁, h₁⟩ := hx r
      obtain ⟨a₂, h₂⟩ := hy r
      exact ⟨a₁ + a₂, by rw [map_add, tmul_add, h₁, h₂, tmul_add]⟩
    | smul o x _ hx =>
      intro r
      obtain ⟨a, ha⟩ := hx (o • r)
      exact ⟨a, by rw [ha, smul_tmul]⟩
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul r x => exact key x r
  | add t₁ t₂ h₁ h₂ =>
    obtain ⟨a₁, h₁⟩ := h₁
    obtain ⟨a₂, h₂⟩ := h₂
    exact ⟨a₁ + a₂, by rw [map_add, tmul_add, h₁, h₂]⟩

/-- **Derivations at a section are coordinates in a basis of the cotangent space.** Let `R` be
a local ring, `O` an `R`-algebra with `Ω[O⁄R]` finite projective, and `ε : O →ₐ[R] R` a section.
There are `g` and `v : Fin g → O` such that, for every `R`-module `M`, an `R`-linear map
`D : O → M` with `D (a * b) = ε a • D b + ε b • D a` vanishing at every `vₖ` vanishes, and every
family `m : Fin g → M` is `k ↦ D (vₖ)` for such a `D`. -/
theorem exists_derivation_coordinates [IsLocalRing R] [Module.Projective O Ω[O⁄R]]
    [Module.Finite O Ω[O⁄R]] :
    ∃ (g : ℕ) (v : Fin g → O), ∀ (M : Type w) [AddCommGroup M] [Module R M],
      (∀ D : O →ₗ[R] M, (∀ a b, D (a * b) = ε a • D b + ε b • D a) →
        (∀ k, D (v k) = 0) → D = 0) ∧
      (∀ m : Fin g → M, ∃ D : O →ₗ[R] M, (∀ a b, D (a * b) = ε a • D b + ε b • D a) ∧
        ∀ k, D (v k) = m k) := by
  let : Algebra O R := ε.toRingHom.toAlgebra
  have hε : ∀ r : R, ε (algebraMap R O r) = r := ε.commutes
  have hsmul : ∀ (o : O) (r : R), o • r = ε o * r := fun o r ↦ Algebra.smul_def o r
  -- the cotangent space at `ε` is free of finite rank
  have : Module.Flat R (R ⊗[O] Ω[O⁄R]) := inferInstance
  have : Module.Finite R (R ⊗[O] Ω[O⁄R]) := inferInstance
  have : Module.Free R (R ⊗[O] Ω[O⁄R]) := Module.free_of_flat_of_isLocalRing
  let b₀ := Module.Free.chooseBasis R (R ⊗[O] Ω[O⁄R])
  let b := b₀.reindex (Fintype.equivFin _)
  let g := Fintype.card (Module.Free.ChooseBasisIndex R (R ⊗[O] Ω[O⁄R]))
  choose v hv using fun k : Fin g ↦ exists_one_tmul_D_eq ε (b k)
  refine ⟨g, v, fun M _ _ ↦ ?_⟩
  let : Module O M := Module.compHom M ε.toRingHom
  have hOM : ∀ (o : O) (m : M), o • m = ε o • m := fun _ _ ↦ rfl
  have : IsScalarTower R O M := ⟨fun r o m ↦ by
    rw [hOM, hOM, map_smul, smul_eq_mul, mul_smul]⟩
  have : IsScalarTower O R M := ⟨fun o r m ↦ by
    rw [hOM, hsmul, mul_smul]⟩
  -- the value of a derivation at `a` is the value of its linear map on `1 ⊗ d a`
  have one_tmul_smul : ∀ (o : O) (x : Ω[O⁄R]),
      (1 : R) ⊗ₜ[O] (o • x) = ε o • ((1 : R) ⊗ₜ[O] x) := by
    intro o x
    rw [← smul_tmul, hsmul, mul_one, smul_tmul', smul_eq_mul, mul_one]
  refine ⟨fun δ hD hv0 ↦ ?_, fun m ↦ ?_⟩
  · let D' : Derivation R O M :=
      { δ with
        map_one_eq_zero' := by
          have h := hD 1 1
          simp only [mul_one, map_one, one_smul] at h
          simpa using h
        leibniz' := fun a c ↦ by
          change δ (a * c) = ε a • δ c + ε c • δ a
          exact hD a c }
    let L : R ⊗[O] Ω[O⁄R] →ₗ[R] M := D'.liftKaehlerDifferential.liftBaseChange R
    have hL : ∀ a, L ((1 : R) ⊗ₜ[O] D R O a) = δ a := fun a ↦ by
      simp only [L, LinearMap.liftBaseChange_one_tmul, Derivation.liftKaehlerDifferential_comp_D]
      rfl
    have hL0 : L = 0 := b.ext fun k ↦ by
      rw [← hv k, hL, hv0 k, LinearMap.zero_apply]
    ext a
    rw [← hL a, hL0, LinearMap.zero_apply, LinearMap.zero_apply]
  · let L : R ⊗[O] Ω[O⁄R] →ₗ[R] M := b.constr R m
    refine ⟨
      { toFun := fun a ↦ L ((1 : R) ⊗ₜ[O] D R O a)
        map_add' := fun a c ↦ by rw [map_add, tmul_add, map_add]
        map_smul' := fun r a ↦ by
          rw [RingHom.id_apply, Derivation.map_smul, ← algebraMap_smul O r (D R O a),
            one_tmul_smul, hε, map_smul] }, fun a c ↦ ?_, fun k ↦ ?_⟩
    · change L ((1 : R) ⊗ₜ[O] D R O (a * c)) =
        ε a • L ((1 : R) ⊗ₜ[O] D R O c) + ε c • L ((1 : R) ⊗ₜ[O] D R O a)
      rw [Derivation.leibniz, tmul_add, one_tmul_smul, one_tmul_smul, map_add, map_smul,
        map_smul]
    · change L ((1 : R) ⊗ₜ[O] D R O (v k)) = m k
      rw [hv k]
      exact b.constr_basis R m k

end KaehlerDifferential

end
