module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.StableFlagBasis
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.AbsolutelyIrreducible
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.RingTheory.Algebraic.Integral

/-!
# Block triangular forms over a finite extension with absolutely irreducible blocks

For a family of matrices `M : A → Matrix (Fin r) (Fin r) k` and an algebraically closed field
`K ⊇ k`, there are a finite extension `E` of `k` inside `K`, an invertible `P` over `E` and a
grading `d` such that every `P⁻¹ (M a) P` is graded upper triangular and its diagonal blocks
are irreducible over `K` (absolutely irreducible). Indeed a composition series over the
algebraic closure `k̄` of `k` in `K`
(`Stacks.EtaleCohomology.exists_isGradedUpper_irreducible_blocks`) has blocks irreducible over `K`
by Burnside's theorem (`Stacks.EtaleCohomology.eq_bot_or_eq_top_of_forall_mulVec_map_mem`), and
its finitely many entries, algebraic over `k`, generate a finite extension.

## Main definitions

* `Stacks.EtaleCohomology.blockExtend`: extension by zero from a block.

## Main results

* `Stacks.EtaleCohomology.forall_block_eq_bot_or_eq_top`,
  `Stacks.EtaleCohomology.eq_coordSubspace_of_forall_block`: irreducibility of a block of a block
  diagonal family, on the coordinate subspace and on the block itself.
* `Stacks.EtaleCohomology.exists_finiteDimensional_isGradedUpper_absolutelyIrreducible`.
-/

@[expose] public noncomputable section

open Matrix

namespace Stacks.EtaleCohomology

section BlockTransfer

variable {L : Type*} [Field L] {r : ℕ} {A : Type*}

/-- Extension by zero from the block `{i | d i = t}`. -/
public def blockExtend (d : Fin r → ℤ) (t : ℤ) : ({i // d i = t} → L) →ₗ[L] (Fin r → L) where
  toFun v i := if h : d i = t then v ⟨i, h⟩ else 0
  map_add' v w := by
    ext i
    by_cases h : d i = t <;> simp [h]
  map_smul' c v := by
    ext i
    by_cases h : d i = t <;> simp [h]

variable {d : Fin r → ℤ} {t : ℤ}

/-- The extension by zero of a vector on the block `t` lies in the coordinate subspace of `t`. -/
public theorem blockExtend_mem (v : {i // d i = t} → L) :
    blockExtend d t v ∈ coordSubspace (K := L) (fun i => d i = t) := fun i hi => by
  simp [blockExtend, hi]

/-- Extension by zero from a block is injective. -/
public theorem blockExtend_injective : Function.Injective (blockExtend (L := L) d t) := by
  intro v w h
  ext ⟨i, hi⟩
  simpa [blockExtend, hi] using congrFun h i

/-- A vector in the coordinate subspace of the block `t` is the extension by zero of its
restriction to the block. -/
public theorem blockExtend_restrict {c : Fin r → L}
    (hc : c ∈ coordSubspace (K := L) (fun i => d i = t)) :
    blockExtend d t (fun i => c i) = c := by
  ext i
  by_cases h : d i = t
  · simp [blockExtend, h]
  · simp [blockExtend, h, hc i h]

/-- A block diagonal matrix acts on a block through its diagonal block. -/
public theorem mulVec_blockExtend {X : Matrix (Fin r) (Fin r) L}
    (hX : ∀ i j, d i ≠ d j → X i j = 0) (v : {i // d i = t} → L) :
    X *ᵥ blockExtend d t v = blockExtend d t (X.toSquareBlock d t *ᵥ v) := by
  ext i
  rw [Matrix.mulVec, dotProduct, ← Fintype.sum_subtype_add_sum_subtype (fun j => d j = t)]
  have h2 : ∑ j : {j // ¬ d j = t}, X i j * blockExtend d t v j = 0 :=
    Finset.sum_eq_zero fun j _ => by simp [blockExtend, j.2]
  rw [h2, add_zero]
  by_cases hi : d i = t
  · simp only [blockExtend, LinearMap.coe_mk, AddHom.coe_mk, dif_pos hi, Matrix.mulVec,
      dotProduct, Matrix.toSquareBlock_def, Matrix.of_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [dif_pos j.2]
  · simp only [blockExtend, LinearMap.coe_mk, AddHom.coe_mk, dif_neg hi]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [hX i j (fun e => hi (e.trans j.2)), zero_mul]

/-- For a block diagonal family, irreducibility of a block on the coordinate subspace gives
irreducibility of the diagonal blocks on `L^{block}`. -/
public theorem forall_block_eq_bot_or_eq_top {X : A → Matrix (Fin r) (Fin r) L}
    (hX : ∀ a i j, d i ≠ d j → X a i j = 0)
    (hirr : ∀ W' : Submodule L (Fin r → L), W' ≤ coordSubspace (K := L) (fun i => d i = t) →
      W' ≠ ⊥ → (∀ a, ∀ v ∈ W', X a *ᵥ v ∈ W') → W' = coordSubspace (K := L) (fun i => d i = t))
    (W : Submodule L ({i // d i = t} → L))
    (hW : ∀ a, ∀ v ∈ W, (X a).toSquareBlock d t *ᵥ v ∈ W) : W = ⊥ ∨ W = ⊤ := by
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  set W' := W.map (blockExtend d t) with hW'_def
  have hle : W' ≤ coordSubspace (K := L) (fun i => d i = t) := by
    rintro _ ⟨v, -, rfl⟩
    exact blockExtend_mem v
  have hne : W' ≠ ⊥ := by
    intro h
    apply hbot
    rw [eq_bot_iff]
    intro v hv
    have hv' : blockExtend d t v ∈ W' := ⟨v, hv, rfl⟩
    rw [h, Submodule.mem_bot] at hv'
    exact (Submodule.mem_bot L).mpr (blockExtend_injective (hv'.trans (map_zero _).symm))
  have hst : ∀ a, ∀ v ∈ W', X a *ᵥ v ∈ W' := by
    rintro a _ ⟨v, hv, rfl⟩
    rw [mulVec_blockExtend (hX a)]
    exact ⟨_, hW a v hv, rfl⟩
  have heq := hirr W' hle hne hst
  refine eq_top_iff.mpr fun v _ => ?_
  have hv : blockExtend d t v ∈ W' := heq ▸ blockExtend_mem v
  obtain ⟨w, hw, hwv⟩ := hv
  rwa [blockExtend_injective hwv] at hw

/-- For a block diagonal family, irreducibility of the diagonal blocks on `L^{block}` gives
irreducibility of the block on the coordinate subspace. -/
public theorem eq_coordSubspace_of_forall_block {X : A → Matrix (Fin r) (Fin r) L}
    (hX : ∀ a i j, d i ≠ d j → X a i j = 0)
    (hirr : ∀ W : Submodule L ({i // d i = t} → L),
      (∀ a, ∀ v ∈ W, (X a).toSquareBlock d t *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤)
    (W' : Submodule L (Fin r → L)) (hle : W' ≤ coordSubspace (K := L) (fun i => d i = t))
    (hne : W' ≠ ⊥) (hst : ∀ a, ∀ v ∈ W', X a *ᵥ v ∈ W') :
    W' = coordSubspace (K := L) (fun i => d i = t) := by
  set res : (Fin r → L) →ₗ[L] ({i // d i = t} → L) :=
    LinearMap.funLeft L L (Subtype.val : {i // d i = t} → Fin r) with hres_def
  have hres : ∀ c ∈ coordSubspace (K := L) (fun i => d i = t), blockExtend d t (res c) = c :=
    fun c hc => blockExtend_restrict hc
  set W := W'.map res with hW_def
  have hst' : ∀ a, ∀ v ∈ W, (X a).toSquareBlock d t *ᵥ v ∈ W := by
    rintro a _ ⟨c, hc, rfl⟩
    refine ⟨X a *ᵥ c, hst a c hc, ?_⟩
    apply blockExtend_injective
    rw [hres _ (hle (hst a c hc)), ← mulVec_blockExtend (hX a), hres c (hle hc)]
  rcases hirr W hst' with h | h
  · exfalso
    apply hne
    rw [eq_bot_iff]
    intro c hc
    have hc' : res c ∈ W := ⟨c, hc, rfl⟩
    rw [h, Submodule.mem_bot] at hc'
    rw [Submodule.mem_bot, ← hres c (hle hc), hc', map_zero]
  · refine le_antisymm hle fun c hc => ?_
    obtain ⟨w, hw, hwc⟩ : res c ∈ W := h ▸ Submodule.mem_top
    rwa [← hres c hc, ← hwc, hres w (hle hw)]

end BlockTransfer

/-- The graded diagonal part commutes with maps of entries. -/
public theorem gradedDiag_map {ι R S : Type*} [CommRing R] [CommRing S] (d : ι → ℤ)
    (T : Matrix ι ι R) (f : R →+* S) : (gradedDiag d T).map f = gradedDiag d (T.map f) := by
  ext i j
  by_cases h : d i = d j <;> simp [gradedDiag, h]

section Descent

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [IsAlgClosed K] {r : ℕ} {A : Type*}

/-- **A block triangular form over a finite extension with absolutely irreducible blocks.**
For every family `M : A → Matrix (Fin r) (Fin r) k` and algebraically closed `K ⊇ k` there are a
finite extension `E` of `k` in `K`, an invertible `P` over `E` and a grading `d` such that every
`P⁻¹ (M a) P` is graded upper triangular and its diagonal blocks are irreducible over `K`: a
subspace of the coordinate subspace of the block `t` of `K^r` stable under the graded diagonal
parts is zero or the whole block. -/
public theorem exists_finiteDimensional_isGradedUpper_absolutelyIrreducible
    (M : A → Matrix (Fin r) (Fin r) k) :
    ∃ (E : IntermediateField k K) (_ : FiniteDimensional k E) (P : (Matrix (Fin r) (Fin r) E)ˣ)
      (d : Fin r → ℤ),
      (∀ a, IsGradedUpper d (((P⁻¹ : (Matrix (Fin r) (Fin r) E)ˣ) : Matrix (Fin r) (Fin r) E) *
        (M a).map (algebraMap k E) * (P : Matrix (Fin r) (Fin r) E))) ∧
      ∀ (t : ℤ) (W' : Submodule K (Fin r → K)),
        W' ≤ coordSubspace (K := K) (fun i => d i = t) → W' ≠ ⊥ →
        (∀ a, ∀ v ∈ W', (gradedDiag d (((P⁻¹ : (Matrix (Fin r) (Fin r) E)ˣ) :
          Matrix (Fin r) (Fin r) E) * (M a).map (algebraMap k E) *
            (P : Matrix (Fin r) (Fin r) E))).map (algebraMap E K) *ᵥ v ∈ W') →
        W' = coordSubspace (K := K) (fun i => d i = t) := by
  classical
  set Fb := algebraicClosure k K with hFb
  have : IsAlgClosure k Fb := algebraicClosure.isAlgClosure k K
  have : IsAlgClosed Fb := IsAlgClosure.isAlgClosed k
  obtain ⟨Pb, d, hupb, hirrb⟩ :=
    exists_isGradedUpper_irreducible_blocks (fun a => (M a).map (algebraMap k Fb))
  set Pm : Matrix (Fin r) (Fin r) Fb := (Pb : Matrix (Fin r) (Fin r) Fb) with hPm
  set Qm : Matrix (Fin r) (Fin r) Fb := ((Pb⁻¹ : (Matrix (Fin r) (Fin r) Fb)ˣ) :
    Matrix (Fin r) (Fin r) Fb) with hQm
  set S : Set K := Set.range (fun ij : Fin r × Fin r => ((Pm ij.1 ij.2 : Fb) : K)) ∪
    Set.range (fun ij : Fin r × Fin r => ((Qm ij.1 ij.2 : Fb) : K)) with hS
  have : Finite S := ((Set.finite_range _).union (Set.finite_range _)).to_subtype
  set E := IntermediateField.adjoin k S with hE
  have hint : ∀ x ∈ S, IsIntegral k x := by
    rintro x (⟨ij, rfl⟩ | ⟨ij, rfl⟩)
    · exact (mem_algebraicClosure_iff.mp (Pm ij.1 ij.2).2).isIntegral
    · exact (mem_algebraicClosure_iff.mp (Qm ij.1 ij.2).2).isIntegral
  have hfin : FiniteDimensional k E := IntermediateField.finiteDimensional_adjoin hint
  let PE : Matrix (Fin r) (Fin r) E := fun i j =>
    ⟨((Pm i j : Fb) : K), IntermediateField.subset_adjoin k S (Or.inl ⟨(i, j), rfl⟩)⟩
  let QE : Matrix (Fin r) (Fin r) E := fun i j =>
    ⟨((Qm i j : Fb) : K), IntermediateField.subset_adjoin k S (Or.inr ⟨(i, j), rfl⟩)⟩
  have hPE : PE.map (algebraMap E K) = Pm.map (algebraMap Fb K) := rfl
  have hQE : QE.map (algebraMap E K) = Qm.map (algebraMap Fb K) := rfl
  have hinj := Matrix.map_injective (m := Fin r) (n := Fin r) (algebraMap E K).injective
  have hmul : ∀ (U V : Matrix (Fin r) (Fin r) Fb) (U' V' : Matrix (Fin r) (Fin r) E),
      U'.map (algebraMap E K) = U.map (algebraMap Fb K) →
      V'.map (algebraMap E K) = V.map (algebraMap Fb K) → U * V = 1 → U' * V' = 1 := by
    intro U V U' V' hU hV h
    apply hinj
    dsimp only
    rw [Matrix.map_mul, hU, hV, ← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.map_one _ (map_zero _) (map_one _)]
  have h1 : PE * QE = 1 := hmul Pm Qm PE QE hPE hQE (Units.mul_inv _)
  have h2 : QE * PE = 1 := hmul Qm Pm QE PE hQE hPE (Units.inv_mul _)
  let P : (Matrix (Fin r) (Fin r) E)ˣ := ⟨PE, QE, h1, h2⟩
  set TE : A → Matrix (Fin r) (Fin r) E := fun a =>
    ((P⁻¹ : (Matrix (Fin r) (Fin r) E)ˣ) : Matrix (Fin r) (Fin r) E) *
      (M a).map (algebraMap k E) * (P : Matrix (Fin r) (Fin r) E) with hTE
  set Tb : A → Matrix (Fin r) (Fin r) Fb := fun a => Qm * (M a).map (algebraMap k Fb) * Pm
    with hTb
  have hT : ∀ a, (TE a).map (algebraMap E K) = (Tb a).map (algebraMap Fb K) := by
    intro a
    show (QE * (M a).map (algebraMap k E) * PE).map (algebraMap E K) = _
    rw [Matrix.map_mul, Matrix.map_mul, hQE, hPE, hTb, Matrix.map_mul, Matrix.map_mul,
      Matrix.map_map, Matrix.map_map, ← RingHom.coe_comp, ← RingHom.coe_comp,
      ← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]
  refine ⟨E, hfin, P, d, fun a i j hij => ?_, fun t W' hle hne hst => ?_⟩
  · have := congrFun (congrFun (hT a) i) j
    simp only [Matrix.map_apply] at this
    have h0 : Tb a i j = 0 := hupb a i j hij
    rw [h0, map_zero] at this
    exact (algebraMap E K).injective (this.trans (map_zero _).symm)
  set X : A → Matrix (Fin r) (Fin r) K := fun a => (gradedDiag d (Tb a)).map (algebraMap Fb K)
    with hX_def
  have hXE : ∀ a, (gradedDiag d (TE a)).map (algebraMap E K) = X a := by
    intro a
    rw [gradedDiag_map, hT]
    exact (gradedDiag_map d (Tb a) _).symm
  have hXbd : ∀ a i j, d i ≠ d j → X a i j = 0 := fun a i j h => by
    simp [hX_def, gradedDiag, h]
  have hbdb : ∀ a i j, d i ≠ d j → gradedDiag d (Tb a) i j = 0 := fun a i j h => by
    simp [gradedDiag, h]
  have hblockb := forall_block_eq_bot_or_eq_top (X := fun a => gradedDiag d (Tb a)) (t := t) hbdb
    (hirrb t)
  have hblockK := eq_bot_or_eq_top_of_forall_mulVec_map_mem
    (K := K) (fun a => (gradedDiag d (Tb a)).toSquareBlock d t) hblockb
  exact eq_coordSubspace_of_forall_block (X := X) hXbd
    (fun W hW => hblockK W fun a v hv => hW a v hv) W' hle hne fun a v hv => by
      rw [← hXE]; exact hst a v hv

end Descent

end Stacks.EtaleCohomology

end
