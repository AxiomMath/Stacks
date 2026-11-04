module

public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.TensorProduct.Free
public import StacksFrontier.RingTheory.Koszul.Localization
public import StacksFrontier.RingTheory.Koszul.Quasiregular
public import StacksFrontier.RingTheory.Regular.ProdPowColon
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The wedge of the differentials of a regular system of equations is not a fraction boundary

Let `A → B` be a ring map with `B` Noetherian, and let `f₁, …, f_c ∈ B` be a Koszul-regular
sequence cutting out an `A`-rational point: they lie in a maximal ideal `𝔪` which they
generate after localizing at `𝔪`, and `A → B/𝔪` is surjective. Suppose `Ω_{B/A}` is free of
rank `c`. Then for every `n`,

`(f₁ ⋯ f_c)^n · d f₁ ∧ ⋯ ∧ d f_c ∉ (f₁^{n+1}, …, f_c^{n+1}) · ⋀^c Ω_{B/A}`.

## Main results

* `KaehlerDifferential.span_tmul_D_eq_top_of_surjective`: the differentials of the equations span
  `B/𝔪 ⊗_B Ω_{B/A}`.
* `KaehlerDifferential.prod_pow_smul_ιMulti_D_notMem`: the statement above.

## References

* [Stacks Project, Tag 0G8E](https://stacks.math.columbia.edu/tag/0G8E)
* [Stacks Project, Tag 09CC](https://stacks.math.columbia.edu/tag/09CC)
-/

@[expose] public section

open TensorProduct

universe u

namespace KaehlerDifferential

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- **The differentials of equations of an `A`-rational point span the cotangent space there.**
Let `𝔪 ⊆ B` be a maximal ideal with `A → B/𝔪` surjective, and let `f₁, …, f_c ∈ 𝔪` generate
`𝔪` after localizing at `𝔪`. Then the `1 ⊗ d f_j` span `B/𝔪 ⊗_B Ω_{B/A}` over `B/𝔪`. -/
@[sga "1 II 5.9" "(iv)"]
theorem span_tmul_D_eq_top_of_surjective (m : Ideal B) [m.IsMaximal] {c : ℕ} (f : Fin c → B)
    (hfm : ∀ j, f j ∈ m) (hgen : ∀ x ∈ m, ∃ h ∉ m, h * x ∈ Ideal.span (Set.range f))
    (hsurj : Function.Surjective (algebraMap A (B ⧸ m))) :
    Submodule.span (B ⧸ m) (Set.range fun j => (1 : B ⧸ m) ⊗ₜ[B] D A B (f j)) = ⊤ := by
  let : Field (B ⧸ m) := Ideal.Quotient.field m
  set Sp := Submodule.span (B ⧸ m) (Set.range fun j => (1 : B ⧸ m) ⊗ₜ[B] D A B (f j)) with hSp
  have hΩ : Subsingleton Ω[(B ⧸ m)⁄A] := subsingleton_of_surjective A (B ⧸ m) hsurj
  have hex := exact_kerCotangentToTensor_mapBaseChange A B (B ⧸ m) Ideal.Quotient.mk_surjective
  have hkill : ∀ b ∈ m, ∀ ω : Ω[B⁄A], b • ((1 : B ⧸ m) ⊗ₜ[B] ω) = 0 := by
    intro b hb ω
    rw [TensorProduct.smul_tmul', Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem.2 hb, TensorProduct.zero_tmul]
  have hleib : ∀ (a x : B), x ∈ m → (1 : B ⧸ m) ⊗ₜ[B] D A B (a * x) =
      a • ((1 : B ⧸ m) ⊗ₜ[B] D A B x) := fun a x hx => by
    rw [Derivation.leibniz, TensorProduct.tmul_add, TensorProduct.tmul_smul,
      TensorProduct.tmul_smul, hkill _ hx, add_zero]
  have key : ∀ ω : Ω[B⁄A], (1 : B ⧸ m) ⊗ₜ[B] ω ∈ Sp := by
    intro ω
    obtain ⟨y, hy⟩ := (hex ((1 : B ⧸ m) ⊗ₜ[B] ω)).1 (Subsingleton.elim _ _)
    obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective _ y
    rw [kerCotangentToTensor_toCotangent] at hy
    have hxm : (x : B) ∈ m := Ideal.Quotient.eq_zero_iff_mem.1 x.2
    obtain ⟨h, hhm, hhx⟩ := hgen x hxm
    obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun B).1 hhx
    have hh : algebraMap B (B ⧸ m) h ≠ 0 := fun h0 => hhm (Ideal.Quotient.eq_zero_iff_mem.1 h0)
    have hmem : algebraMap B (B ⧸ m) h • ((1 : B ⧸ m) ⊗ₜ[B] D A B (x : B)) ∈ Sp := by
      rw [algebraMap_smul, ← hleib _ _ hxm, ← hb, map_sum, TensorProduct.tmul_sum]
      refine Submodule.sum_mem _ fun j _ => ?_
      rw [smul_eq_mul, hleib _ _ (hfm j), ← algebraMap_smul (B ⧸ m)]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    rw [← hy]
    have h3 := Sp.smul_mem (algebraMap B (B ⧸ m) h)⁻¹ hmem
    rwa [smul_smul, inv_mul_cancel₀ hh, one_smul] at h3
  rw [eq_top_iff]
  rintro t -
  induction t using TensorProduct.induction_on with
  | zero => exact Sp.zero_mem
  | tmul a ω =>
    rw [show a ⊗ₜ[B] ω = a • ((1 : B ⧸ m) ⊗ₜ[B] ω) by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]]
    exact Sp.smul_mem a (key ω)
  | add t t' ht ht' => exact Sp.add_mem ht ht'

/-- **The wedge of the differentials of a regular system of equations of an `A`-rational point
is not a Čech boundary.** Let `A → B` be a ring map with `B` Noetherian, let `𝔪 ⊆ B` be a maximal
ideal with `A → B/𝔪` surjective, and let `f₁, …, f_c ∈ 𝔪` be a Koszul-regular sequence
generating `𝔪` after localizing at `𝔪`. If `Ω_{B/A}` is free of rank `c`, then for every `n`

`(f₁ ⋯ f_c)^n · d f₁ ∧ ⋯ ∧ d f_c ∉ (f₁^{n+1}, …, f_c^{n+1}) · ⋀^c Ω_{B/A}`. -/
theorem prod_pow_smul_ιMulti_D_notMem [IsNoetherianRing B] (m : Ideal B) [m.IsMaximal] {c : ℕ}
    (f : Fin c → B) (hf : Koszul.IsKoszulRegular f) (hfm : ∀ j, f j ∈ m)
    (hgen : ∀ x ∈ m, ∃ h ∉ m, h * x ∈ Ideal.span (Set.range f))
    (hsurj : Function.Surjective (algebraMap A (B ⧸ m))) (e : Module.Basis (Fin c) B Ω[B⁄A])
    (n : ℕ) :
    (∏ j, f j) ^ n • exteriorPower.ιMulti B c (fun j => D A B (f j)) ∉
      (Ideal.span (Set.range fun j => f j ^ (n + 1)) • ⊤ :
        Submodule B (⋀[B]^c Ω[B⁄A])) := by
  classical
  intro hmem
  let : Field (B ⧸ m) := Ideal.Quotient.field m
  set δ := e.det fun j => D A B (f j) with hδdef
  have hδ : δ ∉ m := by
    set eC := Algebra.TensorProduct.basis (B ⧸ m) e
    have hspan := span_tmul_D_eq_top_of_surjective m f hfm hgen hsurj
    have hli : LinearIndependent (B ⧸ m) fun j => (1 : B ⧸ m) ⊗ₜ[B] D A B (f j) :=
      linearIndependent_of_top_le_span_of_card_eq_finrank hspan.ge
        (by rw [Module.finrank_eq_card_basis eC])
    have hu := (Module.Basis.is_basis_iff_det eC).1 ⟨hli, hspan⟩
    have hdet : eC.det (fun j => (1 : B ⧸ m) ⊗ₜ[B] D A B (f j)) = Ideal.Quotient.mk m δ := by
      rw [hδdef, Module.Basis.det_apply, Module.Basis.det_apply, ← Ideal.Quotient.algebraMap_eq,
        RingHom.map_det]
      congr 1
      ext i j
      simp [eC, Module.Basis.toMatrix_apply, Algebra.TensorProduct.basis_repr_tmul]
    rw [hdet] at hu
    exact fun hδm => hu.ne_zero (Ideal.Quotient.eq_zero_iff_mem.2 hδm)
  set I : Ideal B := Ideal.span (Set.range fun j => f j ^ (n + 1)) with hI
  have h1 : (∏ j, f j) ^ n * δ ∈ I := by
    set Λ := exteriorPower.alternatingMapLinearEquiv e.det
    have h := Submodule.mem_map_of_mem (f := Λ) hmem
    rw [Submodule.map_smul''] at h
    have h' : (∏ j, f j) ^ n * δ ∈ (I • ⊤ : Submodule B B) :=
      (Submodule.smul_mono le_rfl le_top) (by
        simpa [Λ, map_smul, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, hδdef]
          using h)
    simpa [Ideal.smul_eq_mul, Ideal.mul_top] using h'
  let L := Localization.AtPrime m
  have hδL : IsUnit (algebraMap B L δ) := (IsLocalization.AtPrime.isUnit_to_map_iff L m δ).2 hδ
  set fL : Fin c → L := fun j => algebraMap B L (f j) with hfL
  have hKL : Koszul.IsKoszulRegular fL := Koszul.isKoszulRegular_map_of_flat f hf
  have hmaxL : ∀ j, fL j ∈ IsLocalRing.maximalIdeal L := fun j =>
    (IsLocalization.AtPrime.to_map_mem_maximal_iff L m (f j)).2 (hfm j)
  have hreg : RingTheory.Sequence.IsRegular L (List.ofFn fL) :=
    ((Koszul.regular_koszulRegular_h1Regular_quasiRegular_tfae (M := L) fL hmaxL).2.out 1 2).2 hKL
  have h2 : (∏ j, fL j) ^ n ∈ Ideal.span (Set.range fun j => fL j ^ (n + 1)) := by
    have h := Ideal.mem_map_of_mem (algebraMap B L) h1
    rw [hI, Ideal.map_span, map_mul, map_pow, map_prod] at h
    obtain ⟨u, hu⟩ := hδL
    have h' := Ideal.mul_mem_right (↑u⁻¹ : L) _ h
    rw [← hu, mul_assoc, Units.mul_inv, mul_one] at h'
    refine (Ideal.span_mono ?_) h'
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    exact ⟨j, by simp [fL]⟩
  have hmaxL' : ∀ r ∈ List.ofFn fL, r ∈ IsLocalRing.maximalIdeal L := by
    intro r hr
    obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 hr
    exact hmaxL j
  have hx : (List.ofFn fL).prod ^ n • (1 : L) ∈
      (Ideal.ofList ((List.ofFn fL).map (· ^ (n + 1))) • ⊤ : Submodule L L) := by
    rw [List.prod_ofFn, Ideal.smul_eq_mul, Ideal.mul_top, List.map_ofFn, smul_eq_mul, mul_one]
    refine (Ideal.span_mono ?_) h2
    rintro _ ⟨j, rfl⟩
    exact (List.mem_ofFn' _ _).2 ⟨j, rfl⟩
  have h3 := hreg.toIsWeaklyRegular.mem_ofList_smul_top_of_prod_pow_smul_mem hmaxL' n hx
  rw [Ideal.smul_eq_mul, Ideal.mul_top] at h3
  have h4 : Ideal.ofList (List.ofFn fL) ≤ IsLocalRing.maximalIdeal L := Ideal.span_le.2 hmaxL'
  exact (IsLocalRing.maximalIdeal.isMaximal L).ne_top
    ((Ideal.eq_top_iff_one _).2 (h4 h3))

end KaehlerDifferential

end
