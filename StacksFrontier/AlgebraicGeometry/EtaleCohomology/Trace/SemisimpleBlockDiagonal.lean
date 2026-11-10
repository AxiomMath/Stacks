module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CliffordSemisimple
public import Mathlib.Algebra.DirectSum.LinearMap
public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Data.Matrix.Block
public import Mathlib.Order.SupIndep

/-!
# A semisimple family of matrices is block diagonal with irreducible blocks

For a family of matrices `X : A → Matrix (Fin m) (Fin m) K` over a field such that every stable
subspace of `K^m` has a stable complement, `K^m` is the direct sum of finitely many irreducible
stable subspaces `Y₁, …, Y_r`; in a basis adapted to the decomposition every `X a` is block
diagonal with irreducible diagonal blocks. This is the splitting of the semisimple restriction of
an absolutely irreducible representation to an open subgroup of finite index into its
constituents (Kedlaya, *Fourier transforms and p-adic Weil II*, §6.4).

## Main results

* `Stacks.EtaleCohomology.exists_finset_supIndep_isIrreducibleUnder`: a decomposition into
  independent irreducible stable subspaces.
* `Stacks.EtaleCohomology.exists_blockDiagonal'_conj_irreducible`: the block diagonal form.
-/

@[expose] public noncomputable section

open Matrix Module

namespace Stacks.EtaleCohomology

section Decomposition

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- **A semisimple representation is a direct sum of irreducibles**: every stable subspace `W`
of a semisimple `V` is the independent supremum of finitely many irreducible stable subspaces. -/
public theorem exists_finset_supIndep_isIrreducibleUnder {S : Set (Module.End K V)}
    (hss : ∀ W, IsStableUnder S W → ∃ W', IsCompl W W' ∧ IsStableUnder S W')
    (W : Submodule K V) (hW : IsStableUnder S W) :
    ∃ s : Finset (Submodule K V), s.SupIndep id ∧ s.sup id = W ∧
      ∀ X ∈ s, IsIrreducibleUnder S X := by
  classical
  suffices H : ∀ (d : ℕ) (W : Submodule K V), finrank K W = d → IsStableUnder S W →
      ∃ s : Finset (Submodule K V), s.SupIndep id ∧ s.sup id = W ∧
        ∀ X ∈ s, IsIrreducibleUnder S X from H _ W rfl hW
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro W hd hW
  by_cases hW0 : W = ⊥
  · exact ⟨∅, Finset.supIndep_empty _, by simp [hW0], by simp⟩
  obtain ⟨X, hXW, hX⟩ := exists_isIrreducibleUnder_le hW0 hW
  obtain ⟨C, hXC, hC⟩ := hss X hX.2.1
  have hW'S : IsStableUnder S (W ⊓ C) := isStableUnder_inf hW hC
  have hlt : W ⊓ C < W := by
    refine lt_of_le_of_ne inf_le_left fun h => hX.1 ?_
    have hXC' : X ≤ X ⊓ C := le_inf le_rfl (hXW.trans (h ▸ inf_le_right))
    exact eq_bot_iff.mpr (hXC'.trans hXC.inf_eq_bot.le)
  obtain ⟨s, hs, hsup, hirr⟩ := ih _ (hd ▸ Submodule.finrank_lt_finrank_of_lt hlt) (W ⊓ C) rfl
    hW'S
  refine ⟨insert X s, hs.insert ?_, ?_, ?_⟩
  · rw [hsup]
    exact disjoint_iff.mpr (eq_bot_iff.mpr ((inf_le_inf_left X inf_le_right).trans
      hXC.inf_eq_bot.le))
  · rw [Finset.sup_insert, hsup, id, inf_comm, ← sup_inf_assoc_of_le C hXW, hXC.sup_eq_top,
      top_inf_eq]
  · intro Y hY
    rcases Finset.mem_insert.mp hY with rfl | h
    · exact hX
    · exact hirr Y h

end Decomposition

section Matrices

variable {K : Type*} [Field K] {A : Type*} {m : ℕ}

/-- **Block diagonal form of a semisimple family of matrices.** If every subspace of `K^m` stable
under the `X a` has a stable complement, there are a decomposition `Fin m ≃ Σ i, Fin (ms i)` and
an invertible `Q` such that every `Q (X a) Q⁻¹` is block diagonal and its diagonal blocks are
irreducible: a subspace of `K^{ms i}` stable under the `i`-th blocks is `0` or everything. -/
public theorem exists_blockDiagonal'_conj_irreducible (X : A → Matrix (Fin m) (Fin m) K)
    (hss : ∀ W : Submodule K (Fin m → K), (∀ a, ∀ v ∈ W, X a *ᵥ v ∈ W) →
      ∃ W', IsCompl W W' ∧ ∀ a, ∀ v ∈ W', X a *ᵥ v ∈ W') :
    ∃ (r : ℕ) (ms : Fin r → ℕ) (eqv : Fin m ≃ Σ i, Fin (ms i)) (Q : GL (Σ i, Fin (ms i)) K),
      (∀ a, (Q : Matrix (Σ i, Fin (ms i)) (Σ i, Fin (ms i)) K) * reindex eqv eqv (X a) *
          ((Q⁻¹ : GL (Σ i, Fin (ms i)) K) : Matrix (Σ i, Fin (ms i)) (Σ i, Fin (ms i)) K) =
        blockDiagonal' (blockDiag' ((Q : Matrix (Σ i, Fin (ms i)) (Σ i, Fin (ms i)) K) *
          reindex eqv eqv (X a) *
            ((Q⁻¹ : GL (Σ i, Fin (ms i)) K) : Matrix (Σ i, Fin (ms i)) (Σ i, Fin (ms i)) K)))) ∧
      ∀ i (W : Submodule K (Fin (ms i) → K)),
        (∀ a, ∀ v ∈ W, blockDiag' ((Q : Matrix (Σ i, Fin (ms i)) (Σ i, Fin (ms i)) K) *
          reindex eqv eqv (X a) *
            ((Q⁻¹ : GL (Σ i, Fin (ms i)) K) : Matrix (Σ i, Fin (ms i)) (Σ i, Fin (ms i)) K)) i *ᵥ
              v ∈ W) → W = ⊥ ∨ W = ⊤ := by
  classical
  set S : Set (Module.End K (Fin m → K)) := Set.range fun a => Matrix.toLin' (X a)
  have hstab : ∀ W : Submodule K (Fin m → K),
      IsStableUnder S W ↔ ∀ a, ∀ v ∈ W, X a *ᵥ v ∈ W := fun W =>
    ⟨fun h a _ hv => h _ ⟨a, rfl⟩ hv, by rintro h _ ⟨a, rfl⟩ v hv; exact h a v hv⟩
  obtain ⟨s, hs, hsup, hirr⟩ := exists_finset_supIndep_isIrreducibleUnder (S := S)
    (fun W hW => by
      obtain ⟨W', hc, hW'⟩ := hss W ((hstab W).mp hW)
      exact ⟨W', hc, (hstab W').mpr hW'⟩) ⊤ (fun _ _ => le_top)
  set r := s.card
  let e : Fin r ≃ s := s.equivFin.symm
  let Y : Fin r → Submodule K (Fin m → K) := fun i => (e i : Submodule K (Fin m → K))
  have hind : iSupIndep Y := (Finset.SupIndep.independent hs).comp e.injective
  have hYsup : iSup Y = ⊤ := by
    rw [← hsup, Finset.sup_eq_iSup]
    change (⨆ i, ((e i : s) : Submodule K (Fin m → K))) = _
    rw [e.iSup_comp (g := fun x : s => (x : Submodule K (Fin m → K))), iSup_subtype']
    rfl
  have hint : DirectSum.IsInternal Y :=
    (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top Y).mpr ⟨hind, hYsup⟩
  have hYirr : ∀ i, IsIrreducibleUnder S (Y i) := fun i => hirr _ (e i).2
  let ms : Fin r → ℕ := fun i => finrank K (Y i)
  let b : ∀ i, Basis (Fin (ms i)) K (Y i) := fun i => Module.finBasisOfFinrankEq K (Y i) rfl
  let cb : Basis (Σ i, Fin (ms i)) K (Fin m → K) := hint.collectedBasis b
  have hcard : Fintype.card (Σ i, Fin (ms i)) = m := by
    rw [← Module.finrank_eq_card_basis cb, Module.finrank_fin_fun]
  let eqv : Fin m ≃ Σ i, Fin (ms i) := (Fintype.equivFinOfCardEq hcard).symm
  let std : Basis (Σ i, Fin (ms i)) K (Fin m → K) := (Pi.basisFun K (Fin m)).reindex eqv
  let Q : GL (Σ i, Fin (ms i)) K :=
    ⟨cb.toMatrix std, std.toMatrix cb, Basis.toMatrix_mul_toMatrix_flip _ _,
      Basis.toMatrix_mul_toMatrix_flip _ _⟩
  have hstd : ∀ a, LinearMap.toMatrix std std (Matrix.toLin' (X a)) = reindex eqv eqv (X a) := by
    intro a
    ext i j
    simp [std, LinearMap.toMatrix_apply, Matrix.toLin'_apply, Matrix.reindex_apply]
  have hmaps : ∀ a i, Set.MapsTo (Matrix.toLin' (X a)) (Y i) (Y i) := fun a i v hv =>
    (hYirr i).2.1 _ ⟨a, rfl⟩ hv
  have hconj : ∀ a, (Q : Matrix (Σ i, Fin (ms i)) (Σ i, Fin (ms i)) K) * reindex eqv eqv (X a) *
      ((Q⁻¹ : GL (Σ i, Fin (ms i)) K) : Matrix (Σ i, Fin (ms i)) (Σ i, Fin (ms i)) K) =
      blockDiagonal' fun i => LinearMap.toMatrix (b i) (b i)
        ((Matrix.toLin' (X a)).restrict (hmaps a i)) := by
    intro a
    have h1 := LinearMap.toMatrix_directSum_collectedBasis_eq_blockDiagonal' (ι := Fin r) (R := K)
      (κ₁ := fun i => Fin (ms i)) (κ₂ := fun i => Fin (ms i)) hint hint b b (hmaps a)
    have h2 := basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix (b := cb) (b' := std)
      (c := cb) (c' := std) (Matrix.toLin' (X a))
    rw [← h1, ← h2, hstd a]
    rfl
  refine ⟨r, ms, eqv, Q, fun a => ?_, fun i W hW => ?_⟩
  · rw [hconj a, blockDiag'_blockDiagonal']
  simp only [hconj, blockDiag'_blockDiagonal'] at hW
  set W₂ : Submodule K (Fin m → K) :=
    (W.map ((b i).equivFun.symm : _ →ₗ[K] Y i)).map (Y i).subtype
  have hW₂le : W₂ ≤ Y i := Submodule.map_subtype_le _ _
  have hW₂st : IsStableUnder S W₂ := by
    rintro _ ⟨a, rfl⟩ _ ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    have key : (b i).equivFun ((Matrix.toLin' (X a)).restrict (hmaps a i)
        ((b i).equivFun.symm c)) = LinearMap.toMatrix (b i) (b i)
          ((Matrix.toLin' (X a)).restrict (hmaps a i)) *ᵥ c := by
      have h := LinearMap.toMatrix_mulVec_repr (b i) (b i)
        ((Matrix.toLin' (X a)).restrict (hmaps a i)) ((b i).equivFun.symm c)
      rw [Basis.equivFun_apply, ← h, ← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    rw [Submodule.mem_comap]
    refine ⟨(Matrix.toLin' (X a)).restrict (hmaps a i) ((b i).equivFun.symm c), ⟨_, hW a c hc, ?_⟩,
      rfl⟩
    apply (b i).equivFun.injective
    rw [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, key]
  rcases (hYirr i).2.2 W₂ hW₂le hW₂st with h | h
  · left
    rw [eq_bot_iff]
    intro c hc
    have hc' : (((b i).equivFun.symm c : Y i) : Fin m → K) ∈ W₂ := ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    rw [h, Submodule.mem_bot] at hc'
    rw [Submodule.mem_bot, ← (b i).equivFun.symm.map_eq_zero_iff]
    exact Subtype.ext hc'
  · right
    rw [eq_top_iff]
    intro c _
    have hc' : (((b i).equivFun.symm c : Y i) : Fin m → K) ∈ W₂ := by
      rw [h]
      exact ((b i).equivFun.symm c).2
    obtain ⟨_, ⟨c', hc', rfl⟩, hcc⟩ := hc'
    exact (b i).equivFun.symm.injective (Subtype.ext hcc) ▸ hc'

end Matrices

end Stacks.EtaleCohomology

end
