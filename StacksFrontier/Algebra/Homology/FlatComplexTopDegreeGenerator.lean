module

public import StacksFrontier.Algebra.Homology.FlatComplexTopDegreeFibres
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A generator of top cohomology, detected modulo maximal ideals

Let `K` be a complex of flat `R`-modules vanishing in large degrees, whose cohomology vanishes
above degree `d = q + 1` and with `Hᵈ(K)` a finite `R`-module. Top cohomology commutes with base
change, `Hᵈ(K ⊗ R/𝔪) = Hᵈ(K) ⊗ R/𝔪` (`Stacks.FlatComplexTopDegree.range_lTensor_ker_subtype`),
so a cocycle `z` whose class generates `Hᵈ(K ⊗ R/𝔪)` for every maximal ideal `𝔪` generates
`Hᵈ(K)` modulo `𝔪 Hᵈ(K)` for every `𝔪`, hence generates `Hᵈ(K)` by Nakayama's lemma.

In [Stacks, Tag 0G8J] this shows that the class `ξ = γ^{0,0}(1)` of a section of a proper smooth
morphism of relative dimension `n` generates `Hⁿ(X, Ωⁿ)`: its image in every closed fibre is a
nonzero element of a one-dimensional vector space.

## Main results

* `Submodule.eq_top_of_forall_isMaximal_sup_smul_eq_top`: a submodule of a finite module which
  together with `𝔪 M` is everything, for every maximal ideal `𝔪`, is everything.
* `Stacks.FlatComplexTopDegree.exists_sub_smul_eq_d_of_forall_isMaximal`: the generator criterion
  for top cohomology of a flat complex.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ModuleCat
open scoped TensorProduct ChangeOfRings Pointwise

universe u

/-- **Nakayama's lemma, globally.** If `N` is a submodule of a finite `R`-module `M` with
`N + 𝔪 M = M` for every maximal ideal `𝔪`, then `N = M`. -/
@[ega "III 7.6.11" "partial"]
theorem Submodule.eq_top_of_forall_isMaximal_sup_smul_eq_top {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] (N : Submodule R M)
    (h : ∀ m : Ideal R, m.IsMaximal → N ⊔ m • (⊤ : Submodule R M) = ⊤) : N = ⊤ := by
  by_contra hN
  have hQ : Module.annihilator R (M ⧸ N) ≠ ⊤ := fun htop =>
    hN (Submodule.Quotient.subsingleton_iff.1 (Module.annihilator_eq_top_iff.1 htop))
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hQ
  have hle' : (⊤ : Submodule R (M ⧸ N)) ≤ m • (⊤ : Submodule R (M ⧸ N)) := by
    have h1 := congrArg (Submodule.map N.mkQ) (h m hm)
    rw [Submodule.map_sup, Submodule.mkQ_map_self, bot_sup_eq, Submodule.map_smul'',
      Submodule.map_top, Submodule.range_mkQ] at h1
    exact h1.ge
  obtain ⟨r, hr, hr0⟩ :=
    Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul m ⊤ Module.Finite.fg_top hle'
  exact hm.ne_top ((Ideal.eq_top_iff_one m).2 (sub_sub_cancel r 1 ▸
    m.sub_mem (hle (Module.mem_annihilator.2 fun q => hr0 q Submodule.mem_top)) hr))

namespace Stacks.FlatComplexTopDegree

variable {R : Type u} [CommRing R]

/-- **A generator of top cohomology is detected modulo maximal ideals.** Let `K` be a complex of
flat `R`-modules vanishing in degrees `≥ n`, whose cohomology vanishes above degree `q + 1`, with
`H^{q+1}(K)` finite. Let `z` be a `(q+1)`-cocycle of `K` such that for every maximal ideal `𝔪`
every `(q+1)`-cocycle of `K ⊗ R/𝔪` is, up to a coboundary, a multiple of `1 ⊗ z`. Then every
`(q+1)`-cocycle of `K` is, up to a coboundary, a multiple of `z`. -/
theorem exists_sub_smul_eq_d_of_forall_isMaximal {K : CochainComplex (ModuleCat.{u} R) ℕ}
    (q n : ℕ) [∀ i, Module.Flat R (K.X i)] (hKn : ∀ i, n ≤ i → Subsingleton (K.X i))
    (hK : ∀ i, q + 1 < i → IsZero (K.homology i)) [Module.Finite R (K.homology (q + 1))]
    (z : K.X (q + 1)) (hz : K.d (q + 1) (q + 1 + 1) z = 0)
    (hm : ∀ m : Ideal R, m.IsMaximal →
      ∀ w : (extendScalars (Ideal.Quotient.mk m)).obj (K.X (q + 1)),
      (extendScalars (Ideal.Quotient.mk m)).map (K.d (q + 1) (q + 1 + 1)) w = 0 →
      ∃ (c : R ⧸ m) (v : (extendScalars (Ideal.Quotient.mk m)).obj (K.X q)),
        (extendScalars (Ideal.Quotient.mk m)).map (K.d q (q + 1)) v =
          w - c • (show (extendScalars (Ideal.Quotient.mk m)).obj (K.X (q + 1)) from
            toRingModule (Ideal.Quotient.mk m) 1 ⊗ₜ[R] z))
    (y : K.X (q + 1)) (hy : K.d (q + 1) (q + 1 + 1) y = 0) :
    ∃ (a : R) (v : K.X q), K.d q (q + 1) v = y - a • z := by
  classical
  have hexK : ∀ i, q + 1 ≤ i →
      Function.Exact (K.d i (i + 1)).hom (K.d (i + 1) (i + 1 + 1)).hom :=
    fun i hi => exact_of_isZero_homology K i (hK (i + 1) (by lia))
  let S := K.sc' q (q + 1) (q + 1 + 1)
  let H := LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles
  have : Module.Finite R H :=
    Module.Finite.equiv ((K.homologyIsoSc' q (q + 1) (q + 1 + 1) (CochainComplex.prev_nat_succ q)
      (CochainComplex.next ℕ (q + 1))) ≪≫ S.moduleCatHomologyIso).toLinearEquiv
  let cz : LinearMap.ker S.g.hom := ⟨z, hz⟩
  -- the class of `z` and `𝔪 H` together are `H`, for every maximal ideal `𝔪`
  have hsup : ∀ m : Ideal R, m.IsMaximal →
      Submodule.span R {(Submodule.Quotient.mk cz : H)} ⊔ m • (⊤ : Submodule R H) = ⊤ := by
    intro m hm'
    rw [eq_top_iff]
    rintro x -
    obtain ⟨⟨w, hw⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    let w₁ : K.X (q + 1) := w
    obtain ⟨c, v, hv⟩ := hm m hm' (toRingModule (Ideal.Quotient.mk m) 1 ⊗ₜ[R] w₁)
      ((extendScalars_map_tmul (Ideal.Quotient.mk m) (K.d (q + 1) (q + 1 + 1))
        (toRingModule _ 1) w₁).trans
        ((congrArg _ (LinearMap.mem_ker.1 hw)).trans (TensorProduct.tmul_zero _ _)))
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
    obtain ⟨v', rfl⟩ := exists_one_tmul_eq (Ideal.Quotient.mk m) Ideal.Quotient.mk_surjective v
    rw [extendScalars_map_tmul, extendScalars_smul_tmul, mul_one] at hv
    have hv2 : toRingModule (Ideal.Quotient.mk m) 1 ⊗ₜ[R] (K.d q (q + 1) v') =
        toRingModule (Ideal.Quotient.mk m) 1 ⊗ₜ[R] w₁ -
          toRingModule (Ideal.Quotient.mk m) 1 ⊗ₜ[R] (a • z) := by
      rwa [TensorProduct.tmul_smul, TensorProduct.smul_tmul', smul_toRingModule, mul_one]
    have h1 : toRingModule (Ideal.Quotient.mk m) 1 ⊗ₜ[R]
        (⟨w, hw⟩ - a • cz - S.moduleCatToCycles v' : LinearMap.ker S.g.hom) = 0 := by
      refine lTensor_ker_subtype_injective (C := fun i => K.X i) (fun i => (K.d i (i + 1)).hom)
        (q + 1) n hKn hexK (ringModule (Ideal.Quotient.mk m))
        (((LinearMap.lTensor_tmul _ _ _ _).trans ?_).trans (map_zero _).symm)
      change toRingModule (Ideal.Quotient.mk m) 1 ⊗ₜ[R] (w₁ - a • z - K.d q (q + 1) v') = 0
      rw [TensorProduct.tmul_sub, TensorProduct.tmul_sub, hv2]
      abel
    have h3 : (Submodule.Quotient.mk ⟨w, hw⟩ : H) =
        a • Submodule.Quotient.mk cz +
          Submodule.Quotient.mk (⟨w, hw⟩ - a • cz - S.moduleCatToCycles v') := by
      have h0 : (Submodule.Quotient.mk (S.moduleCatToCycles v') : H) = 0 :=
        (Submodule.Quotient.mk_eq_zero _).2 (LinearMap.mem_range_self _ v')
      rw [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_sub, h0, sub_zero,
        Submodule.Quotient.mk_smul, add_sub_cancel]
    rw [h3]
    refine Submodule.add_mem_sup (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)) ?_
    refine Submodule.smul_induction_on (mem_smul_top_of_one_tmul_eq_zero m _ h1)
      (fun r hr t _ => ?_) (fun t t' ht ht' => ?_)
    · rw [Submodule.Quotient.mk_smul]
      exact Submodule.smul_mem_smul hr Submodule.mem_top
    · rw [Submodule.Quotient.mk_add]
      exact add_mem ht ht'
  have hyH : (Submodule.Quotient.mk (⟨y, hy⟩ : LinearMap.ker S.g.hom) : H) ∈
      Submodule.span R {(Submodule.Quotient.mk cz : H)} :=
    Submodule.eq_top_of_forall_isMaximal_sup_smul_eq_top _ hsup ▸ Submodule.mem_top
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hyH
  rw [← Submodule.Quotient.mk_smul, eq_comm, Submodule.Quotient.eq] at ha
  obtain ⟨v, hv⟩ := ha
  exact ⟨a, v, congrArg Subtype.val hv⟩

end Stacks.FlatComplexTopDegree
