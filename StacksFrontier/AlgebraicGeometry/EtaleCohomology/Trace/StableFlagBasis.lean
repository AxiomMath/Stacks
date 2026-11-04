module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GradedTriangularMatrices
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CoordinateSubspaceBlocks
public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.RingTheory.Artinian.Module

/-!
# Composition series of a family of matrices in block triangular form

For a family `M : A → Matrix (Fin r) (Fin r) K` of matrices over a field, there is a maximal
chain `0 = V₀ < V₁ < ⋯ < V_m = Kʳ` of subspaces stable under every `M a` (a composition series of
`Kʳ` as a module over the algebra the `M a` generate).  A basis adapted to it conjugates every
`M a` into graded upper triangular form `P₀⁻¹ M a P₀` along the grading `d` (`d i = s` for the
basis vectors in `V_s ∖ V_{s-1}`), and the diagonal blocks (the graded diagonal part, the action on
the successive quotients `V_s / V_{s-1}`) are irreducible: a subspace of the coordinate subspace of
a block which is stable under the graded diagonal parts is zero or the whole block.

## Main results

All names are in the namespace `Stacks.EtaleCohomology`.

* `exists_minimal_stable_gt`: a minimal stable subspace above a given one.
* `exists_isGradedUpper_irreducible_blocks`: the block triangular form with irreducible diagonal
  blocks.
-/

@[expose] public noncomputable section

open Matrix Module

namespace Stacks.EtaleCohomology

variable {K : Type*} [Field K] {r : ℕ} {A : Type*} (M : A → Matrix (Fin r) (Fin r) K)

/-- Above every proper subspace `X` of `Kʳ` there is a subspace `Y > X` stable under every `M a`
and minimal with these properties. -/
public theorem exists_minimal_stable_gt {X : Submodule K (Fin r → K)} (hX : X ≠ ⊤) :
    ∃ Y : Submodule K (Fin r → K), (∀ a, ∀ v ∈ Y, M a *ᵥ v ∈ Y) ∧ X < Y ∧
      ∀ Z : Submodule K (Fin r → K), (∀ a, ∀ v ∈ Z, M a *ᵥ v ∈ Z) → X < Z → ¬ Z < Y := by
  set S := {Y : Submodule K (Fin r → K) | (∀ a, ∀ v ∈ Y, M a *ᵥ v ∈ Y) ∧ X < Y}
  have hne : S.Nonempty := ⟨⊤, fun _ _ _ => Submodule.mem_top, lt_top_iff_ne_top.mpr hX⟩
  obtain ⟨Y, hY, hmin⟩ := (wellFounded_lt (α := Submodule K (Fin r → K))).has_min S hne
  exact ⟨Y, hY.1, hY.2, fun Z hZ hXZ => hmin Z ⟨hZ, hXZ⟩⟩

/-- **Block triangular form along a composition series.**  For every family of matrices
`M : A → Matrix (Fin r) (Fin r) K` there are an invertible `P₀` and a grading `d` such that every
`P₀⁻¹ (M a) P₀` is graded upper triangular, and the diagonal blocks are irreducible: a subspace
of the coordinate subspace of the block `t` stable under all the graded diagonal parts is zero
or the whole block. -/
public theorem exists_isGradedUpper_irreducible_blocks :
    ∃ (P₀ : (Matrix (Fin r) (Fin r) K)ˣ) (d : Fin r → ℤ),
      (∀ a, IsGradedUpper d (((P₀⁻¹ : (Matrix (Fin r) (Fin r) K)ˣ) : Matrix (Fin r) (Fin r) K) *
        M a * (P₀ : Matrix (Fin r) (Fin r) K))) ∧
      ∀ (t : ℤ) (W' : Submodule K (Fin r → K)), W' ≤ coordSubspace (K := K) (fun i => d i = t) →
        W' ≠ ⊥ →
        (∀ a, ∀ v ∈ W', gradedDiag d (((P₀⁻¹ : (Matrix (Fin r) (Fin r) K)ˣ) :
          Matrix (Fin r) (Fin r) K) * M a * (P₀ : Matrix (Fin r) (Fin r) K)) *ᵥ v ∈ W') →
        W' = coordSubspace (K := K) (fun i => d i = t) := by
  classical
  let next : Submodule K (Fin r → K) → Submodule K (Fin r → K) := fun X =>
    if h : X ≠ ⊤ then (exists_minimal_stable_gt M h).choose else ⊤
  let V : ℕ → Submodule K (Fin r → K) := fun s => next^[s] ⊥
  have hVsucc : ∀ s, V (s + 1) = next (V s) := fun s => Function.iterate_succ_apply' _ _ _
  have hVst : ∀ s, ∀ a, ∀ v ∈ V s, M a *ᵥ v ∈ V s := by
    intro s
    induction s with
    | zero =>
      intro a v hv
      rw [(Submodule.mem_bot K).mp hv, Matrix.mulVec_zero]
      exact Submodule.zero_mem _
    | succ s _ =>
      rw [hVsucc]
      by_cases h : V s ≠ ⊤
      · simp only [next, dif_pos h]
        exact (exists_minimal_stable_gt M h).choose_spec.1
      · simp only [next, dif_neg h]
        exact fun _ _ _ => Submodule.mem_top
  have hVlt : ∀ s, V s ≠ ⊤ → V s < V (s + 1) ∧ ∀ Z : Submodule K (Fin r → K),
      (∀ a, ∀ v ∈ Z, M a *ᵥ v ∈ Z) → V s < Z → ¬ Z < V (s + 1) := by
    intro s h
    rw [hVsucc]
    simp only [next, dif_pos h]
    exact (exists_minimal_stable_gt M h).choose_spec.2
  have hVle : ∀ s, V s ≤ V (s + 1) := by
    intro s
    by_cases h : V s ≠ ⊤
    · exact (hVlt s h).1.le
    · rw [hVsucc]
      simp only [next, dif_neg h]
      exact le_top
  have hVmono : Monotone V := monotone_nat_of_le_succ hVle
  have hVtop : V r = ⊤ := by
    have key : ∀ s, V s = ⊤ ∨ s ≤ finrank K (V s) := by
      intro s
      induction s with
      | zero => exact Or.inr (Nat.zero_le _)
      | succ s ih =>
        by_cases h : V s = ⊤
        · left
          rw [hVsucc]
          simp only [next, h, ne_eq, not_true_eq_false, dif_neg, not_false_eq_true]
        · right
          exact (ih.resolve_left h).trans_lt (Submodule.finrank_lt_finrank_of_lt (hVlt s h).1)
    rcases key r with h | h
    · exact h
    · refine Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) ?_)
      rwa [finrank_fin_fun]
  let Bsub : (s : ℕ) → {B : Set (Fin r → K) // LinearIndepOn K id B ∧ B ⊆ V s ∧
      (V s : Set (Fin r → K)) ⊆ Submodule.span K B} := fun s =>
    Nat.rec (motive := fun s => {B : Set (Fin r → K) // LinearIndepOn K id B ∧ B ⊆ V s ∧
      (V s : Set (Fin r → K)) ⊆ Submodule.span K B})
      ⟨∅, linearIndepOn_empty K id, Set.empty_subset _, by
        intro v hv
        rw [(Submodule.mem_bot K).mp hv]
        exact Submodule.zero_mem _⟩
      (fun s B =>
        let h := exists_linearIndepOn_extension B.2.1 (B.2.2.1.trans (hVle s))
        ⟨h.choose, h.choose_spec.2.2.2, h.choose_spec.1, by
          simpa only [Set.image_id] using h.choose_spec.2.2.1⟩) s
  let B : ℕ → Set (Fin r → K) := fun s => (Bsub s).1
  have hBsucc : ∀ s, B s ⊆ B (s + 1) := fun s =>
    (exists_linearIndepOn_extension (Bsub s).2.1 ((Bsub s).2.2.1.trans (hVle s))).choose_spec.2.1
  have hBmono : Monotone B := monotone_nat_of_le_succ hBsucc
  have hBspan : ∀ s, Submodule.span K (B s) = V s := fun s =>
    le_antisymm (Submodule.span_le.mpr (Bsub s).2.2.1) (fun v hv => (Bsub s).2.2.2 hv)
  set T := B r with hT_def
  have hTli : LinearIndependent K ((↑) : T → Fin r → K) := (Bsub r).2.1
  have hTsp : ⊤ ≤ Submodule.span K (Set.range ((↑) : T → Fin r → K)) := by
    rw [Subtype.range_coe, hT_def, hBspan, hVtop]
  let b0 : Basis T K (Fin r → K) := Basis.mk hTli hTsp
  have : Finite T := Module.Finite.finite_basis b0
  have : Fintype T := Fintype.ofFinite T
  have hcard : Fintype.card T = r := by
    rw [← finrank_eq_card_basis b0, finrank_fin_fun]
  let e : T ≃ Fin r := Fintype.equivFinOfCardEq hcard
  let b : Basis (Fin r) K (Fin r → K) := b0.reindex e
  have hb : ∀ i, b i = ((e.symm i : T) : Fin r → K) := fun i => by
    simp only [b, Basis.reindex_apply, b0, Basis.mk_apply]
  have hbr : ∀ i, b i ∈ B r := fun i => by rw [hb]; exact (e.symm i).2
  have hex : ∀ i, ∃ s, b i ∈ B s := fun i => ⟨r, hbr i⟩
  let dn : Fin r → ℕ := fun i => Nat.find (hex i)
  have hdn : ∀ i s, b i ∈ B s ↔ dn i ≤ s := fun i s =>
    ⟨fun h => Nat.find_min' (hex i) h, fun h => hBmono h (Nat.find_spec (hex i))⟩
  have hBimage : ∀ s ≤ r, B s = b '' {i | dn i ≤ s} := by
    intro s hs
    ext x
    constructor
    · intro hx
      have hxT : x ∈ T := hBmono hs hx
      refine ⟨e ⟨x, hxT⟩, (hdn _ s).mp ?_, ?_⟩
      · rwa [hb, Equiv.symm_apply_apply]
      · rw [hb, Equiv.symm_apply_apply]
    · rintro ⟨i, hi, rfl⟩
      exact (hdn i s).mpr hi
  have hdnr : ∀ i, dn i ≤ r := fun i => Nat.find_min' (hex i) (hbr i)
  let P₀ : (Matrix (Fin r) (Fin r) K)ˣ :=
    ⟨(Pi.basisFun K (Fin r)).toMatrix b, b.toMatrix (Pi.basisFun K (Fin r)),
      Basis.toMatrix_mul_toMatrix_flip _ _, Basis.toMatrix_mul_toMatrix_flip _ _⟩
  let Pm : Matrix (Fin r) (Fin r) K := P₀
  have hP : ∀ c, Pm *ᵥ c = b.equivFun.symm c := by
    intro c
    ext i
    simp [Pm, P₀, Basis.toMatrix_apply, Matrix.mulVec, dotProduct, Basis.equivFun_symm_apply,
      Finset.sum_apply, mul_comm]
  have hΦ : ∀ s ≤ r, ∀ c, Pm *ᵥ c ∈ V s ↔
      ∀ i, ¬ dn i ≤ s → c i = 0 := by
    intro s hs c
    have hr : ∀ i, b.repr (b.equivFun.symm c) i = c i := fun i => by
      rw [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    rw [hP, ← hBspan, hBimage s hs, Basis.mem_span_image, Finsupp.support_subset_iff]
    simp only [Set.mem_setOf_eq, hr]
  set Tm : A → Matrix (Fin r) (Fin r) K := fun a =>
    ((P₀⁻¹ : (Matrix (Fin r) (Fin r) K)ˣ) : Matrix (Fin r) (Fin r) K) * M a *
      Pm with hTm_def
  have hkey : ∀ a c, M a *ᵥ (Pm *ᵥ c) =
      Pm *ᵥ (Tm a *ᵥ c) := by
    intro a c
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hTm_def]
    congr 1
    rw [← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul]
  set d : Fin r → ℤ := fun i => (dn i : ℤ) with hd_def
  have hup : ∀ a, IsGradedUpper d (Tm a) := by
    intro a i j hij
    change (dn j : ℤ) < dn i at hij
    have hij' : dn j < dn i := by exact_mod_cast hij
    have h1 : Pm *ᵥ Pi.single j 1 ∈ V (dn j) :=
      (hΦ _ (hdnr j) _).mpr fun i' hi' => by
        have : i' ≠ j := fun h => hi' (by rw [h])
        simp [this]
    have h2 := hVst _ a _ h1
    rw [hkey] at h2
    have h3 := (hΦ _ (hdnr j) _).mp h2 i (not_le.mpr hij')
    rwa [Matrix.mulVec_single_one, Matrix.col_apply] at h3
  refine ⟨P₀, d, hup, ?_⟩
  intro t W' hle hne hst
  obtain ⟨w0, hw0, hw0ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨i0, hi0⟩ := Function.ne_iff.mp hw0ne
  have hdi0 : (dn i0 : ℤ) = t := by
    by_contra h
    exact hi0 (hle hw0 i0 h)
  have hs0 : dn i0 ≠ 0 := by
    intro h
    have h' := Nat.find_spec (hex i0)
    change b i0 ∈ B (dn i0) at h'
    rw [h] at h'
    exact Set.notMem_empty _ h'
  obtain ⟨s₀, hs₀⟩ := Nat.exists_eq_succ_of_ne_zero hs0
  have hs₀r : s₀ + 1 ≤ r := by have := hdnr i0; omega
  have hblock : ∀ c ∈ coordSubspace (K := K) (fun i => d i = t),
      Pm *ᵥ c ∈ V (s₀ + 1) := by
    intro c hc
    refine (hΦ _ hs₀r c).mpr fun i hi => hc i ?_
    show ¬ (dn i : ℤ) = t
    omega
  have hΦ₀ := hΦ s₀ (by omega)
  have hVs₀ne : V s₀ ≠ ⊤ := by
    intro htop
    have h1 : Pm *ᵥ Pi.single i0 1 ∈ V s₀ := htop ▸ Submodule.mem_top
    have h2 := (hΦ₀ _).mp h1 i0 (by omega)
    simp at h2
  have hmin := (hVlt s₀ hVs₀ne).2
  set Z := V s₀ ⊔ W'.map (Matrix.toLin' Pm) with hZ_def
  have hmapZ : ∀ w ∈ W', Pm *ᵥ w ∈ Z := fun w hw =>
    Submodule.mem_sup_right ⟨w, hw, by rw [Matrix.toLin'_apply]⟩
  have hZst : ∀ a, ∀ v ∈ Z, M a *ᵥ v ∈ Z := by
    intro a v hv
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hv
    rw [Matrix.mulVec_add]
    refine Submodule.add_mem _ (Submodule.mem_sup_left (hVst s₀ a x hx)) ?_
    obtain ⟨w, hw, rfl⟩ := hy
    rw [Matrix.toLin'_apply, hkey]
    have hsplit :
        Tm a *ᵥ w = gradedDiag d (Tm a) *ᵥ w + (Tm a *ᵥ w - gradedDiag d (Tm a) *ᵥ w) := by
      abel
    rw [hsplit, Matrix.mulVec_add]
    refine Submodule.add_mem _ (hmapZ _ (hst a w hw)) (Submodule.mem_sup_left ?_)
    refine (hΦ₀ _).mpr fun i hi => ?_
    rw [← Matrix.sub_mulVec, Matrix.mulVec, dotProduct]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : d j = t
    · by_cases hij : d i = d j
      · simp [gradedDiag, hij]
      · have hlt : d j < d i := by
          show (dn j : ℤ) < dn i
          change (dn j : ℤ) = t at hj
          change ¬ (dn i : ℤ) = dn j at hij
          omega
        simp [gradedDiag, hij, hup a i j hlt]
    · rw [hle hw j hj, mul_zero]
  have hVZ : V s₀ < Z := by
    refine lt_of_le_of_ne le_sup_left fun h => ?_
    have h1 := hmapZ w0 hw0
    rw [← h] at h1
    exact hi0 ((hΦ₀ _).mp h1 i0 (by omega))
  have hZle : Z ≤ V (s₀ + 1) := by
    refine sup_le (hVle s₀) ?_
    rintro _ ⟨w, hw, rfl⟩
    rw [Matrix.toLin'_apply]
    exact hblock w (hle hw)
  have hZeq : Z = V (s₀ + 1) := by
    by_contra h
    exact hmin Z hZst hVZ (lt_of_le_of_ne hZle h)
  refine le_antisymm hle fun c hc => ?_
  have h1 : Pm *ᵥ c ∈ Z := hZeq ▸ hblock c hc
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp h1
  obtain ⟨w, hw, rfl⟩ := hy
  rw [Matrix.toLin'_apply] at hxy
  have hx' : Pm *ᵥ (c - w) ∈ V s₀ := by
    rwa [Matrix.mulVec_sub, ← hxy, add_sub_cancel_right]
  have h2 := (hΦ₀ _).mp hx'
  have hcw : c = w := by
    ext i
    by_cases hi : d i = t
    · have h3 := h2 i (by change (dn i : ℤ) = t at hi; omega)
      rwa [Pi.sub_apply, sub_eq_zero] at h3
    · rw [hc i hi, hle hw i hi]
  rwa [hcw]

end Stacks.EtaleCohomology

end
