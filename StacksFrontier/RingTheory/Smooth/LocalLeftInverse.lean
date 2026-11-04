module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Algebra.Module.Torsion.Basic

/-!
# Left inverses of maps from a free module over a local ring

Let `A` be a local ring with maximal ideal `𝔪` and `N` a projective `A`-module. A linear map
`φ : Aʳ → N` whose reduction modulo `𝔪` is injective has a left inverse.
-/

@[expose] public section

open IsLocalRing

namespace Module

variable {A N : Type*} [CommRing A] [IsLocalRing A] [AddCommGroup N] [Module A N]

/-- **A map from `Aʳ` into a projective module over a local ring which is injective modulo the
maximal ideal has a left inverse.** -/
theorem exists_leftInverse_of_isLocalRing [Module.Projective A N] {r : ℕ}
    (φ : (Fin r → A) →ₗ[A] N)
    (hφ : ∀ a, φ a ∈ (maximalIdeal A) • (⊤ : Submodule A N) → ∀ i, a i ∈ maximalIdeal A) :
    ∃ l : N →ₗ[A] (Fin r → A), l ∘ₗ φ = LinearMap.id := by
  classical
  set m := maximalIdeal A
  let κ := A ⧸ m
  let : Field κ := Ideal.Quotient.field m
  let Nb := N ⧸ m • (⊤ : Submodule A N)
  let πN : N →ₗ[A] Nb := (m • (⊤ : Submodule A N)).mkQ
  -- the reduction of `φ`
  let φb : (Fin r → κ) →ₗ[κ] Nb := (Pi.basisFun κ (Fin r)).constr κ fun i => πN (φ (Pi.single i 1))
  have hφb : ∀ a : Fin r → A, φb (fun i => Ideal.Quotient.mk m (a i)) = πN (φ a) := by
    intro a
    rw [Basis.constr_apply_fintype]
    have : a = ∑ i, a i • (Pi.single i 1 : Fin r → A) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    conv_rhs => rw [this]
    simp only [map_sum, map_smul, Pi.basisFun_equivFun, LinearEquiv.refl_apply]
    rfl
  let q : (Fin r → A) →ₗ[A] (Fin r → κ) :=
    LinearMap.pi fun i => (Ideal.Quotient.mkₐ A m).toLinearMap ∘ₗ LinearMap.proj i
  have hq : Function.Surjective q := by
    intro v
    refine ⟨fun i => Function.surjInv Ideal.Quotient.mk_surjective (v i), ?_⟩
    ext i
    simp [q, Function.surjInv_eq]
  have hker : LinearMap.ker φb = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    obtain ⟨a, rfl⟩ : ∃ a : Fin r → A, (fun i => Ideal.Quotient.mk m (a i)) = v := hq v
    rw [LinearMap.mem_ker, hφb] at hv
    ext i
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hφ a ((Submodule.Quotient.mk_eq_zero _).1 hv) i)
  obtain ⟨ρb, hρb⟩ := LinearMap.exists_leftInverse_of_injective φb hker
  let g : N →ₗ[A] (Fin r → κ) := (ρb.restrictScalars A) ∘ₗ πN
  obtain ⟨ρ, hρ⟩ := Module.projective_lifting_property q g hq
  let M : Matrix (Fin r) (Fin r) A := Matrix.of fun i j => ρ (φ (Pi.single i 1)) j
  have hM : ∀ i j, M i j - (1 : Matrix (Fin r) (Fin r) A) i j ∈ m := by
    intro i j
    rw [← Ideal.Quotient.eq]
    have h1 : q (ρ (φ (Pi.single i 1))) = g (φ (Pi.single i 1)) := LinearMap.congr_fun hρ _
    have h2 : g (φ (Pi.single i 1)) = Pi.single i 1 := by
      show ρb (πN (φ (Pi.single i 1))) = _
      rw [← hφb]
      have : (fun k => Ideal.Quotient.mk m ((Pi.single i 1 : Fin r → A) k)) =
          (Pi.single i 1 : Fin r → κ) := by
        ext k
        simp [Pi.single_apply, apply_ite]
      rw [this]
      exact LinearMap.congr_fun hρb _
    have h3 := congrFun (h1.trans h2) j
    simp only [q, LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.proj_apply, AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk] at h3
    simp only [M, Matrix.of_apply, h3, Matrix.one_apply]
    simp [Pi.single_apply, eq_comm]
  have hdet : M.det - 1 ∈ m := by
    rw [← Ideal.Quotient.eq, map_one, RingHom.map_det]
    have : (Ideal.Quotient.mk m).mapMatrix M = 1 := by
      ext i j
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
      rw [Ideal.Quotient.eq.2 (hM i j)]
      simp [Matrix.one_apply, apply_ite]
    rw [this, Matrix.det_one]
  have hunit : IsUnit M.det := by
    by_contra hnu
    refine (maximalIdeal.isMaximal A).ne_top ((Ideal.eq_top_iff_one _).2 ?_)
    simpa only [sub_sub_cancel] using m.sub_mem ((mem_maximalIdeal _).2 hnu) hdet
  refine ⟨(Matrix.vecMulLinear M⁻¹) ∘ₗ ρ, ?_⟩
  refine LinearMap.pi_ext' fun i => LinearMap.ext_ring ?_
  ext k
  have := congrFun (congrFun (Matrix.mul_nonsing_inv M hunit) i) k
  simp only [Matrix.mul_apply, M, Matrix.of_apply] at this
  simp only [LinearMap.comp_apply, Matrix.vecMulLinear_apply, Matrix.vecMul, dotProduct,
    LinearMap.coe_single, LinearMap.id_apply]
  rw [this, Matrix.one_apply, Pi.single_apply]
  simp [eq_comm]

end Module
