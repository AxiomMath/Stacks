module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.ExteriorPower.Pairing
public import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dual.Lemmas
import StacksCore.Tactic.EgaSgaAttribute

/-!
# An eigenvalue of an exterior power

Let `f` be an endomorphism of a vector space `V`, `W ⊆ V` a finite-dimensional `f`-stable
subspace of dimension `d`, and `w ∉ W` an eigenvector of `f` with eigenvalue `μ`.  Then
`w ∧ e₁ ∧ ⋯ ∧ e_d`, for a basis `e` of `W`, is an eigenvector of `⋀^{d+1} f` with eigenvalue
`μ · det(f|_W)`.

## Main results

* `Stacks.EtaleCohomology.ιMulti_ne_zero_of_linearIndependent`: the exterior product of a linearly
  independent family is nonzero.
* `Stacks.EtaleCohomology.hasEigenvalue_exteriorPower_map_mul_det`: the eigenvalue
  `μ · det(f|_W)` of `⋀^{d+1} f`.
* `Stacks.EtaleCohomology.norm_le_div_of_exteriorPower`: the resulting bound on `|ι μ|`.

## References

* P. Deligne, *La conjecture de Weil II*, Publ. Math. IHÉS 52 (1980), 1.5.1.
* [Stacks Project, Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)
-/

@[expose] public noncomputable section

namespace Stacks.EtaleCohomology

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The exterior product of a linearly independent family is nonzero. -/
@[ega "0 5.5.4" "partial"]
theorem ιMulti_ne_zero_of_linearIndependent {n : ℕ} {v : Fin n → V}
    (hv : LinearIndependent K v) : exteriorPower.ιMulti K n v ≠ 0 := by
  let b : Module.Basis (Fin n) K (Submodule.span K (Set.range v)) := Module.Basis.span hv
  have hb : (Submodule.span K (Set.range v)).subtype ∘ b = v := by
    funext i
    simp [b, Module.Basis.span_apply]
  have h1 : exteriorPower.pairingDual K _ n (exteriorPower.ιMulti K n b.coord)
      (exteriorPower.ιMulti K n b) = 1 := by
    rw [exteriorPower.pairingDual_ιMulti_ιMulti, ← Matrix.det_one (n := Fin n)]
    congr 1
    ext i j
    simp [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply,
      Matrix.one_apply]
  have hne : exteriorPower.ιMulti K n b ≠ 0 := fun h => by simp [h] at h1
  rw [← hb, ← exteriorPower.map_apply_ιMulti]
  exact fun h => hne (exteriorPower.map_injective_field (Submodule.injective_subtype _)
    (by rw [h, map_zero]))

/-- **An eigenvalue of an exterior power.**  If `W` is a finite-dimensional `f`-stable subspace of
dimension `d` and `w ∉ W` satisfies `f w = μ • w`, then `μ · det(f|_W)` is an eigenvalue of
`⋀^{d+1} f`, with eigenvector `w ∧ e₁ ∧ ⋯ ∧ e_d` for a basis `e` of `W`. -/
theorem hasEigenvalue_exteriorPower_map_mul_det (f : Module.End K V) (W : Submodule K V)
    [FiniteDimensional K W] (hW : ∀ v ∈ W, f v ∈ W) {w : V} (hw : w ∉ W) {μ : K}
    (hfw : f w = μ • w) :
    Module.End.HasEigenvalue (exteriorPower.map (Module.finrank K W + 1) f)
      (μ * LinearMap.det (f.restrict hW)) := by
  set d := Module.finrank K W
  let e : Module.Basis (Fin d) K W := Module.finBasis K W
  let A : W [⋀^Fin d]→ₗ[K] ⋀[K]^(d + 1) V :=
    ((exteriorPower.ιMulti K (d + 1)).curryLeft w).compLinearMap W.subtype
  have hA : ∀ u : Fin d → W, A u = exteriorPower.ιMulti K (d + 1) (Fin.cons w (W.subtype ∘ u)) :=
    fun u => by
      simp only [A, AlternatingMap.compLinearMap_apply, AlternatingMap.curryLeft_apply_apply]
      rfl
  have hdet : A ((f.restrict hW) ∘ e) = LinearMap.det (f.restrict hW) • A e := by
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff K]
    intro φ
    have h := (φ.compAlternatingMap A).eq_smul_basis_det e
    have h1 := congrArg (fun g => g ((f.restrict hW) ∘ e)) h
    simp only [LinearMap.compAlternatingMap_apply, smul_apply, smul_eq_mul,
      Module.Basis.det_comp, Module.Basis.det_self, mul_one] at h1
    rw [map_sub, map_smul, h1, smul_eq_mul, mul_comm, sub_self]
  have hli : LinearIndependent K (Fin.cons w (W.subtype ∘ e) : Fin (d + 1) → V) := by
    rw [linearIndependent_finCons]
    refine ⟨(e.linearIndependent.map' W.subtype (Submodule.ker_subtype W)), ?_⟩
    rwa [Set.range_comp, ← Submodule.map_span, e.span_eq, Submodule.map_top,
      Submodule.range_subtype]
  have hx0 := ιMulti_ne_zero_of_linearIndependent hli
  refine Module.End.hasEigenvalue_of_hasEigenvector (x := A e) ⟨?_, by rwa [hA]⟩
  rw [Module.End.mem_eigenspace_iff, hA, exteriorPower.map_apply_ιMulti]
  have hfv : (f ∘ Fin.cons w (W.subtype ∘ e) : Fin (d + 1) → V) =
      Fin.cons (μ • w) (W.subtype ∘ ((f.restrict hW) ∘ e)) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [hfw]
    · simp [LinearMap.restrict_apply]
  have hs := (exteriorPower.ιMulti K (d + 1)).toMultilinearMap.cons_smul
    (W.subtype ∘ ((f.restrict hW) ∘ e)) μ w
  rw [AlternatingMap.coe_multilinearMap] at hs
  rw [hfv, hs, ← hA, hdet, smul_smul, hA]

/-- In the situation of `Stacks.EtaleCohomology.hasEigenvalue_exteriorPower_map_mul_det`, if
every eigenvalue of `⋀^{d+1} f` has absolute value at most `C` under `ι` and `det(f|_W)` has
absolute value `D > 0`, then `|ι μ| ≤ C / D`. -/
theorem norm_le_div_of_exteriorPower (ι : K →+* ℂ) (f : Module.End K V) (W : Submodule K V)
    [FiniteDimensional K W] (hW : ∀ v ∈ W, f v ∈ W) {w : V} (hw : w ∉ W) {μ : K}
    (hfw : f w = μ • w) {C D : ℝ}
    (hC : ∀ c, Module.End.HasEigenvalue (exteriorPower.map (Module.finrank K W + 1) f) c →
      ‖ι c‖ ≤ C)
    (hD : ‖ι (LinearMap.det (f.restrict hW))‖ = D) (hD0 : 0 < D) :
    ‖ι μ‖ ≤ C / D := by
  have h := hC _ (hasEigenvalue_exteriorPower_map_mul_det f W hW hw hfw)
  rw [map_mul, norm_mul, hD] at h
  rwa [le_div_iff₀ hD0]

end Stacks.EtaleCohomology
