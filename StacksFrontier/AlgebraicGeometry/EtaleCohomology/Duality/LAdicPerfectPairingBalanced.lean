module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LAdicLevelPairing

/-!
# Balanced Poincaré duality over `ℚ_p` from balanced pairings modulo every `pⁿ`

`Stacks.EtaleCohomology.LAdicPairing.exists_isPerfPair_of_forall_zmodPow` produces, from
Frobenius-equivariant pairings `e : M × M' → ℤ/pⁿ` with bounded kernels, a perfect equivariant
pairing over `ℚ_p`. This file adds a family of balance conditions: if every `e` satisfies
`e(φᵢ a, b) = e(a, ψᵢ b)` for endomorphisms `φᵢ` of `M` and `ψᵢ` of `M'`, the pairing over `ℚ_p`
can be chosen to satisfy them as well
(`Stacks.EtaleCohomology.LAdicPairing.exists_isPerfPair_of_forall_zmodPow_balanced`). The proof
is the one of the unbalanced case: the balance conditions modulo `pⁿ` on the matrix of the
pairing define closed subsets compatible with reduction, so they can be added to the decreasing
sequence of closed subsets of the compact space of matrices; they pass to the torsion-free
quotients and to the base change to `ℚ_p`.

The levels version
`Stacks.EtaleCohomology.LAdicPairing.exists_isPerfPair_extendScalars_of_levels_balanced` reads the
pairings on the levels `Hₙ` of a limit, with kernels killed by a fixed power of `p` (as in
finite-level Poincaré duality on a curve,
`Stacks.EtaleCohomology.LAdicSheaf.curveLevelPairing_bounds`). This is how the action of the
coefficient field `E` on `ℓ`-adic cohomology, balanced at every finite level by the adjointness of
intertwiners (`Stacks.EtaleCohomology.LAdicSheaf.curveLevelPairing_map`), becomes the balance of
the `ℚ_ℓ`-valued Poincaré pairing, in the purity half of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main results

* `Stacks.EtaleCohomology.LAdicPairing.exists_pairing_of_forall_zmodPow_of_basis_balanced`.
* `Stacks.EtaleCohomology.LAdicPairing.rationalPairing_baseChange_balanced`.
* `Stacks.EtaleCohomology.LAdicPairing.exists_isPerfPair_of_forall_zmodPow_balanced`.
* `Stacks.EtaleCohomology.LAdicPairing.exists_isPerfPair_extendScalars_of_levels_balanced`.
-/

@[expose] public noncomputable section

open Matrix

universe v

namespace Stacks.EtaleCohomology.LAdicPairing

variable {p : ℕ} [Fact p.Prime]

/-! ### The free case -/

section Free

variable {L L' : Type*} [AddCommGroup L] [Module ℤ_[p] L] [AddCommGroup L'] [Module ℤ_[p] L']
  {ι ι' : Type*} [Fintype ι] [Fintype ι'] [DecidableEq ι] [DecidableEq ι']
  (m : Module.Basis ι ℤ_[p] L) (m' : Module.Basis ι' ℤ_[p] L')
  {I : Type*} (φ : I → L →ₗ[ℤ_[p]] L) (ψ : I → L' →ₗ[ℤ_[p]] L')

/-- The bilinear form of the matrix `J` is balanced modulo `pⁿ` for the pairs `(φᵢ, ψᵢ)`. -/
def IsBalancedMod (n : ℕ) (J : Matrix ι ι' ℤ_[p]) : Prop :=
  ∀ i a b, PadicInt.toZModPow n (Matrix.toLinearMap₂ m m' J (φ i a) b) =
    PadicInt.toZModPow n (Matrix.toLinearMap₂ m m' J a (ψ i b))

/-- Balance modulo `pⁿ` depends only on the reduction of the matrix modulo `pⁿ`. -/
theorem isBalancedMod_congr {n : ℕ} {J J' : Matrix ι ι' ℤ_[p]}
    (hJ : J.map (PadicInt.toZModPow n) = J'.map (PadicInt.toZModPow n))
    (h : IsBalancedMod m m' φ ψ n J) : IsBalancedMod m m' φ ψ n J' := by
  have h' : ∀ a b, PadicInt.toZModPow n (Matrix.toLinearMap₂ m m' J a b) =
      PadicInt.toZModPow n (Matrix.toLinearMap₂ m m' J' a b) := fun a b => by
    rw [toZModPow_toLinearMap₂, toZModPow_toLinearMap₂, hJ]
  intro i a b
  rw [← h', ← h']
  exact h i a b

/-- Balance modulo `pⁿ⁺¹` implies balance modulo `pⁿ`. -/
theorem isBalancedMod_of_succ {n : ℕ} {J : Matrix ι ι' ℤ_[p]}
    (h : IsBalancedMod m m' φ ψ (n + 1) J) : IsBalancedMod m m' φ ψ n J := by
  intro i a b
  have hc := congrArg (ZMod.castHom (pow_dvd_pow p n.le_succ) (ZMod (p ^ n))) (h i a b)
  rwa [← RingHom.comp_apply, PadicInt.zmod_cast_comp_toZModPow _ _ n.le_succ,
    ← RingHom.comp_apply, PadicInt.zmod_cast_comp_toZModPow _ _ n.le_succ] at hc

variable (f : L →ₗ[ℤ_[p]] L) (g : L' →ₗ[ℤ_[p]] L') (c K : ℕ)

omit [Fintype ι] [Fintype ι'] [DecidableEq ι] [DecidableEq ι'] in
include m m' in
/-- **A balanced equivariant pairing over `ℤ_p` from balanced equivariant pairings modulo every
`pⁿ`**, for free modules with bases. -/
theorem exists_pairing_of_forall_zmodPow_of_basis_balanced [Finite ι] [Finite ι']
    (h : ∀ n : ℕ, ∃ e : L →+ L' →+ ZMod (p ^ n),
      (∀ a, (∀ b, e a b = 0) → ∃ a', (p : ℤ_[p]) ^ K • a = (p : ℤ_[p]) ^ n • a') ∧
      (∀ b, (∀ a, e a b = 0) → ∃ b', (p : ℤ_[p]) ^ K • b = (p : ℤ_[p]) ^ n • b') ∧
      (∀ a b, e (f a) (g b) = (c : ZMod (p ^ n)) * e a b) ∧
      ∀ i a b, e (φ i a) b = e a (ψ i b)) :
    ∃ β : L →ₗ[ℤ_[p]] L' →ₗ[ℤ_[p]] ℤ_[p], (∀ a, (∀ b, β a b = 0) → a = 0) ∧
      (∀ b, (∀ a, β a b = 0) → b = 0) ∧ (∀ a b, β (f a) (g b) = c * β a b) ∧
      ∀ i a b, β (φ i a) b = β a (ψ i b) := by
  have := Fintype.ofFinite ι
  have := Fintype.ofFinite ι'
  classical
  let t : ℕ → Set (Matrix ι ι' ℤ_[p]) := fun n =>
    {J | IsGoodMod m m' f g c K n J} ∩ {J | IsBalancedMod m m' φ ψ n J}
  have hcl : ∀ n, IsClosed (t n) := fun n =>
    (isClosed_setOf_of_map_eq n _ fun J J' hJ => isGoodMod_congr m m' f g c K hJ).inter
      (isClosed_setOf_of_map_eq n _ fun J J' hJ => isBalancedMod_congr m m' φ ψ hJ)
  have hdec : ∀ n, t (n + 1) ⊆ t n := fun n J hJ =>
    ⟨isGoodMod_of_succ m m' f g c K hJ.1, isBalancedMod_of_succ m m' φ ψ hJ.2⟩
  have hne : ∀ n, (t n).Nonempty := fun n => by
    obtain ⟨e, hl, hr, he, hb⟩ := h n
    have hs := ZMod.ringHom_surjective (PadicInt.toZModPow (p := p) n)
    let J : Matrix ι ι' ℤ_[p] := fun i j => Function.surjInv hs (e (m i) (m' j))
    have hJ : ∀ a b, PadicInt.toZModPow n (Matrix.toLinearMap₂ m m' J a b) = e a b := by
      intro a b
      rw [toZModPow_toLinearMap₂, pairing_eq_sum m m' n e a b]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.map_apply]
      exact congrArg _ (Function.surjInv_eq hs _)
    refine ⟨J, ⟨fun a ha => hl a fun b => (hJ a b).symm.trans (ha b),
      fun b hb' => hr b fun a => (hJ a b).symm.trans (hb' a), fun a b => ?_⟩, fun i a b => ?_⟩
    · rw [hJ, hJ, he]
    · rw [hJ, hJ, hb]
  have : CompactSpace (Matrix ι ι' ℤ_[p]) := inferInstanceAs (CompactSpace (ι → ι' → ℤ_[p]))
  obtain ⟨J, hJ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed t hdec hne
    (hcl 0).isCompact hcl
  rw [Set.mem_iInter] at hJ
  refine ⟨Matrix.toLinearMap₂ m m' J, fun a ha => ?_, fun b hb => ?_, fun a b => ?_,
    fun i a b => ?_⟩
  · exact eq_zero_of_forall_pow_smul m K a fun n => (hJ n).1.1 a fun b => by rw [ha b, map_zero]
  · exact eq_zero_of_forall_pow_smul m' K b fun n =>
      (hJ n).1.2.1 b fun a => by rw [hb a, map_zero]
  · rw [← PadicInt.ext_of_toZModPow]
    intro n
    rw [(hJ n).1.2.2 a b, map_mul, map_natCast]
  · rw [← PadicInt.ext_of_toZModPow]
    intro n
    exact (hJ n).2 i a b

end Free

/-! ### The base change to `ℚ_p` -/

section Rational

open TensorProduct

variable {M M' : Type*} [AddCommGroup M] [Module ℤ_[p] M] [AddCommGroup M'] [Module ℤ_[p] M']

/-- Balance passes to the rational pairing. -/
theorem rationalPairing_baseChange_balanced (β : M →ₗ[ℤ_[p]] M' →ₗ[ℤ_[p]] ℤ_[p])
    (φ : M →ₗ[ℤ_[p]] M) (ψ : M' →ₗ[ℤ_[p]] M') (h : ∀ a b, β (φ a) b = β a (ψ b))
    (v : ℚ_[p] ⊗[ℤ_[p]] M) (w : ℚ_[p] ⊗[ℤ_[p]] M') :
    rationalPairing β (φ.baseChange ℚ_[p] v) w = rationalPairing β v (ψ.baseChange ℚ_[p] w) := by
  induction v using TensorProduct.inductionOn with
  | add v v' hv hv' => simp only [map_add, LinearMap.add_apply, hv, hv']
  | tmul x a =>
    induction w using TensorProduct.inductionOn with
    | add w w' hw hw' => simp only [map_add, hw, hw']
    | tmul y b =>
      simp only [LinearMap.baseChange_tmul, rationalPairing_tmul, h]

/-- An element whose class in the torsion-free quotient vanishes is killed by a nonzero scalar. -/
theorem exists_ne_zero_smul_eq_zero_of_mkQ_eq_zero {a : M}
    (h : (Submodule.torsion ℤ_[p] M).mkQ a = 0) : ∃ s : ℤ_[p], s ≠ 0 ∧ s • a = 0 := by
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h
  obtain ⟨s, hs⟩ := (Submodule.mem_torsion_iff a).1 h
  exact ⟨s, nonZeroDivisors.ne_zero s.2, hs⟩

end Rational

/-! ### The perfect pairing on `ℚ_p ⊗ M` -/

section Main

open TensorProduct Submodule

variable {M M' : Type*} [AddCommGroup M] [Module ℤ_[p] M] [AddCommGroup M'] [Module ℤ_[p] M']
  [Module.Finite ℤ_[p] M] [Module.Finite ℤ_[p] M']

variable {k : ℕ} (hkM : ∀ t ∈ torsion ℤ_[p] M, (p : ℤ_[p]) ^ k • t = 0)
  (hkM' : ∀ t ∈ torsion ℤ_[p] M', (p : ℤ_[p]) ^ k • t = 0)

/-- The pairing `(x, y) ↦ e(pᵏ x̃, pᵏ ỹ)` on the torsion-free quotients, for any lifts `x̃`, `ỹ`,
where `pᵏ` kills the torsion. -/
def torsionQuotientPairing {n : ℕ} (e : M →+ M' →+ ZMod (p ^ n)) :
    M ⧸ torsion ℤ_[p] M →+ M' ⧸ torsion ℤ_[p] M' →+ ZMod (p ^ n) :=
  let σ := Function.surjInv (torsion ℤ_[p] M).mkQ_surjective
  let σ' := Function.surjInv (torsion ℤ_[p] M').mkQ_surjective
  have hσ : ∀ x, (torsion ℤ_[p] M).mkQ (σ x) = x := Function.surjInv_eq _
  have hσ' : ∀ y, (torsion ℤ_[p] M').mkQ (σ' y) = y := Function.surjInv_eq _
  AddMonoidHom.mk' (fun x => AddMonoidHom.mk'
    (fun y => e ((p : ℤ_[p]) ^ k • σ x) ((p : ℤ_[p]) ^ k • σ' y)) (fun y y' => by
      rw [← map_add, ← smul_add, pow_smul_eq_of_mkQ_eq hkM' (a := σ' (y + y'))
        (a' := σ' y + σ' y') (by rw [map_add, hσ', hσ', hσ'])]))
    (fun x x' => by
      ext y
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply]
      rw [← AddMonoidHom.add_apply, ← map_add, ← smul_add,
        pow_smul_eq_of_mkQ_eq hkM (a := σ (x + x')) (a' := σ x + σ x')
          (by rw [map_add, hσ, hσ, hσ])])

omit [Module.Finite ℤ_[p] M] [Module.Finite ℤ_[p] M'] in
/-- The value of `torsionQuotientPairing` on classes of elements. -/
theorem torsionQuotientPairing_mkQ {n : ℕ} (e : M →+ M' →+ ZMod (p ^ n)) (a : M) (b : M') :
    torsionQuotientPairing hkM hkM' e ((torsion ℤ_[p] M).mkQ a) ((torsion ℤ_[p] M').mkQ b) =
      e ((p : ℤ_[p]) ^ k • a) ((p : ℤ_[p]) ^ k • b) := by
  simp only [torsionQuotientPairing, AddMonoidHom.mk'_apply]
  rw [pow_smul_eq_of_mkQ_eq hkM (Function.surjInv_eq _ _),
    pow_smul_eq_of_mkQ_eq hkM' (Function.surjInv_eq _ _)]

omit [Module.Finite ℤ_[p] M] [Module.Finite ℤ_[p] M'] in
include hkM hkM' in
/-- A balanced equivariant pairing modulo `pⁿ` with bounded kernels descends to the torsion-free
quotients, with the kernel bound `K + 2k` for `pᵏ` killing the torsion. -/
theorem exists_torsionQuotient_pairing_balanced (f : M →ₗ[ℤ_[p]] M) (g : M' →ₗ[ℤ_[p]] M')
    (c K : ℕ) {I : Type*} (φ : I → M →ₗ[ℤ_[p]] M) (ψ : I → M' →ₗ[ℤ_[p]] M') {n : ℕ}
    (e : M →+ M' →+ ZMod (p ^ n))
    (hl : ∀ a, (∀ b, e a b = 0) → ∃ a', (p : ℤ_[p]) ^ K • a = (p : ℤ_[p]) ^ n • a')
    (hr : ∀ b, (∀ a, e a b = 0) → ∃ b', (p : ℤ_[p]) ^ K • b = (p : ℤ_[p]) ^ n • b')
    (he : ∀ a b, e (f a) (g b) = (c : ZMod (p ^ n)) * e a b)
    (hb : ∀ i a b, e (φ i a) b = e a (ψ i b)) :
    ∃ e' : M ⧸ torsion ℤ_[p] M →+ M' ⧸ torsion ℤ_[p] M' →+ ZMod (p ^ n),
      (∀ x, (∀ y, e' x y = 0) → ∃ x', (p : ℤ_[p]) ^ (K + 2 * k) • x = (p : ℤ_[p]) ^ n • x') ∧
      (∀ y, (∀ x, e' x y = 0) → ∃ y', (p : ℤ_[p]) ^ (K + 2 * k) • y = (p : ℤ_[p]) ^ n • y') ∧
      (∀ x y, e' ((torsion ℤ_[p] M).mapQ _ f (torsion_le_comap f) x)
        ((torsion ℤ_[p] M').mapQ _ g (torsion_le_comap g) y) = (c : ZMod (p ^ n)) * e' x y) ∧
      ∀ i x y, e' ((torsion ℤ_[p] M).mapQ _ (φ i) (torsion_le_comap (φ i)) x) y =
        e' x ((torsion ℤ_[p] M').mapQ _ (ψ i) (torsion_le_comap (ψ i)) y) := by
  have heL := torsionQuotientPairing_mkQ hkM hkM' e
  have hq : ∀ (u : M →ₗ[ℤ_[p]] M) a, (torsion ℤ_[p] M).mapQ _ u (torsion_le_comap u)
      ((torsion ℤ_[p] M).mkQ a) = (torsion ℤ_[p] M).mkQ (u a) := fun _ _ => rfl
  have hq' : ∀ (u : M' →ₗ[ℤ_[p]] M') b, (torsion ℤ_[p] M').mapQ _ u (torsion_le_comap u)
      ((torsion ℤ_[p] M').mkQ b) = (torsion ℤ_[p] M').mkQ (u b) := fun _ _ => rfl
  have hpk : ∀ (a : M) (b : M'), e ((p : ℤ_[p]) ^ k • a) ((p : ℤ_[p]) ^ k • b) =
      e ((p : ℤ_[p]) ^ k • (p : ℤ_[p]) ^ k • a) b := fun a b => by
    rw [map_smul_eq_toZModPow_mul (e _)]
    exact (map_smul_eq_toZModPow_mul (e.flip b) _ _).symm
  have hpk' : ∀ (a : M) (b : M'), e ((p : ℤ_[p]) ^ k • a) ((p : ℤ_[p]) ^ k • b) =
      e a ((p : ℤ_[p]) ^ k • (p : ℤ_[p]) ^ k • b) := fun a b => by
    rw [map_smul_eq_toZModPow_mul (e a) _ ((p : ℤ_[p]) ^ k • b)]
    exact map_smul_eq_toZModPow_mul (e.flip ((p : ℤ_[p]) ^ k • b)) _ a
  refine ⟨torsionQuotientPairing hkM hkM' e, fun x hx => ?_, fun y hy => ?_, fun x y => ?_,
    fun i x y => ?_⟩
  · obtain ⟨a, rfl⟩ := (torsion ℤ_[p] M).mkQ_surjective x
    obtain ⟨a', ha'⟩ := hl ((p : ℤ_[p]) ^ k • (p : ℤ_[p]) ^ k • a) fun b => by
      rw [← hpk, ← heL]
      exact hx _
    refine ⟨(torsion ℤ_[p] M).mkQ a', ?_⟩
    rw [← map_smul, ← map_smul, ← ha', smul_smul, smul_smul, ← pow_add, ← pow_add, two_mul,
      ← add_assoc]
  · obtain ⟨b, rfl⟩ := (torsion ℤ_[p] M').mkQ_surjective y
    obtain ⟨b', hb'⟩ := hr ((p : ℤ_[p]) ^ k • (p : ℤ_[p]) ^ k • b) fun a => by
      rw [← hpk', ← heL]
      exact hy _
    refine ⟨(torsion ℤ_[p] M').mkQ b', ?_⟩
    rw [← map_smul, ← map_smul, ← hb', smul_smul, smul_smul, ← pow_add, ← pow_add, two_mul,
      ← add_assoc]
  · obtain ⟨a, rfl⟩ := (torsion ℤ_[p] M).mkQ_surjective x
    obtain ⟨b, rfl⟩ := (torsion ℤ_[p] M').mkQ_surjective y
    rw [hq, hq', heL, heL, ← map_smul, ← map_smul, he]
  · obtain ⟨a, rfl⟩ := (torsion ℤ_[p] M).mkQ_surjective x
    obtain ⟨b, rfl⟩ := (torsion ℤ_[p] M').mkQ_surjective y
    rw [hq, hq', heL, heL, ← map_smul, ← map_smul, hb]

/-- **Balanced Poincaré duality over `ℚ_p` from balanced finite levels.** Let `M`, `M'` be
finitely generated `ℤ_p`-modules with endomorphisms `f`, `g` and families of endomorphisms `φᵢ`,
`ψᵢ`, and suppose that for every `n` there is a biadditive pairing `e : M × M' → ℤ/pⁿ` with
`e(f a, g b) = c e(a, b)`, `e(φᵢ a, b) = e(a, ψᵢ b)`, and left and right kernels contained in
`p^{n-K}`. Then there is a perfect pairing `B` on `(ℚ_p ⊗ M) × (ℚ_p ⊗ M')` with
`B(f v, g w) = c B(v, w)` and `B(φᵢ v, w) = B(v, ψᵢ w)`. -/
theorem exists_isPerfPair_of_forall_zmodPow_balanced (f : M →ₗ[ℤ_[p]] M) (g : M' →ₗ[ℤ_[p]] M')
    (c K : ℕ) {I : Type*} (φ : I → M →ₗ[ℤ_[p]] M) (ψ : I → M' →ₗ[ℤ_[p]] M')
    (h : ∀ n : ℕ, ∃ e : M →+ M' →+ ZMod (p ^ n),
      (∀ a, (∀ b, e a b = 0) → ∃ a', (p : ℤ_[p]) ^ K • a = (p : ℤ_[p]) ^ n • a') ∧
      (∀ b, (∀ a, e a b = 0) → ∃ b', (p : ℤ_[p]) ^ K • b = (p : ℤ_[p]) ^ n • b') ∧
      (∀ a b, e (f a) (g b) = (c : ZMod (p ^ n)) * e a b) ∧
      ∀ i a b, e (φ i a) b = e a (ψ i b)) :
    ∃ B : ℚ_[p] ⊗[ℤ_[p]] M →ₗ[ℚ_[p]] ℚ_[p] ⊗[ℤ_[p]] M' →ₗ[ℚ_[p]] ℚ_[p], B.IsPerfPair ∧
      (∀ v w, B (f.baseChange ℚ_[p] v) (g.baseChange ℚ_[p] w) = (c : ℚ_[p]) * B v w) ∧
      ∀ i v w, B ((φ i).baseChange ℚ_[p] v) w = B v ((ψ i).baseChange ℚ_[p] w) := by
  obtain ⟨k₁, hk₁⟩ := exists_pow_smul_eq_zero_of_mem_torsion (p := p) (M := M)
  obtain ⟨k₂, hk₂⟩ := exists_pow_smul_eq_zero_of_mem_torsion (p := p) (M := M')
  have hkM : ∀ t ∈ torsion ℤ_[p] M, (p : ℤ_[p]) ^ (k₁ + k₂) • t = 0 := fun t ht => by
    rw [pow_add, mul_comm, mul_smul, hk₁ t ht, smul_zero]
  have hkM' : ∀ t ∈ torsion ℤ_[p] M', (p : ℤ_[p]) ^ (k₁ + k₂) • t = 0 := fun t ht => by
    rw [pow_add, mul_smul, hk₂ t ht, smul_zero]
  set T := torsion ℤ_[p] M
  set T' := torsion ℤ_[p] M'
  obtain ⟨βbar, hβl, hβr, hβe, hβb⟩ :=
    exists_pairing_of_forall_zmodPow_of_basis_balanced (Module.Free.chooseBasis ℤ_[p] (M ⧸ T))
      (Module.Free.chooseBasis ℤ_[p] (M' ⧸ T'))
      (fun i => T.mapQ T (φ i) (torsion_le_comap (φ i)))
      (fun i => T'.mapQ T' (ψ i) (torsion_le_comap (ψ i)))
      (T.mapQ T f (torsion_le_comap f)) (T'.mapQ T' g (torsion_le_comap g)) c
      (K + 2 * (k₁ + k₂)) fun n => by
        obtain ⟨e, hl, hr, he, hb⟩ := h n
        exact exists_torsionQuotient_pairing_balanced hkM hkM' f g c K φ ψ e hl hr he hb
  let β : M →ₗ[ℤ_[p]] M' →ₗ[ℤ_[p]] ℤ_[p] := βbar.compl₁₂ T.mkQ T'.mkQ
  have hl : ∀ a, (∀ b, β a b = 0) → ∃ s : ℤ_[p], s ≠ 0 ∧ s • a = 0 := fun a ha =>
    exists_ne_zero_smul_eq_zero_of_mkQ_eq_zero (hβl (T.mkQ a) fun y => by
      obtain ⟨b, rfl⟩ := T'.mkQ_surjective y
      exact ha b)
  have hr : ∀ b, (∀ a, β.flip b a = 0) → ∃ s : ℤ_[p], s ≠ 0 ∧ s • b = 0 := fun b hb =>
    exists_ne_zero_smul_eq_zero_of_mkQ_eq_zero (hβr (T'.mkQ b) fun x => by
      obtain ⟨a, rfl⟩ := T.mkQ_surjective x
      exact hb a)
  refine ⟨rationalPairing β, ?_, ?_, ?_⟩
  · refine LinearMap.IsPerfPair.of_injective ?_ ?_
    · rw [injective_iff_map_eq_zero]
      exact fun v hv => eq_zero_of_rationalPairing_eq_zero β hl v (LinearMap.congr_fun hv)
    · rw [injective_iff_map_eq_zero, rationalPairing_flip]
      exact fun w hw => eq_zero_of_rationalPairing_eq_zero β.flip hr w (LinearMap.congr_fun hw)
  · intro v w
    refine rationalPairing_baseChange_baseChange β f g c (fun a b => ?_) v w
    rw [show β (f a) (g b) = c * β a b from hβe (T.mkQ a) (T'.mkQ b), map_mul, map_natCast]
  · exact fun i => rationalPairing_baseChange_balanced β (φ i) (ψ i) fun a b =>
      hβb i (T.mkQ a) (T'.mkQ b)

/-- **Balanced Poincaré duality over `ℚ_p` from finite levels with bounded kernels.** Let `M`,
`M'` be finitely generated `ℤ_p`-modules with projections `πₙ : M → Hₙ`, `π'ₙ : M' → H'ₙ` whose
kernels are `pⁿ⁺¹ M`, `pⁿ⁺¹ M'` and whose cokernels are killed by `p^K`, compatible with
endomorphisms `f`, `g` and families `φᵢ`, `ψᵢ`. Suppose pairings `εₙ : Hₙ × H'ₙ → ℤ/pⁿ⁺¹` have left
kernels killed by `p^{K₁}` and right kernels killed by `p^{K₂}`, satisfy
`εₙ(f x, g y) = c εₙ(x, y)` and `εₙ(φᵢ x, y) = εₙ(x, ψᵢ y)`. Then there is a perfect pairing `B` on
`ℚ_p ⊗ M` and `ℚ_p ⊗ M'` with `B(f v, g w) = c B(v, w)` and `B(φᵢ v, w) = B(v, ψᵢ w)`. -/
theorem exists_isPerfPair_extendScalars_of_levels_balanced {M M' : ModuleCat.{v} ℤ_[p]}
    [Module.Finite ℤ_[p] M] [Module.Finite ℤ_[p] M'] (f : M ⟶ M) (g : M' ⟶ M') (c K K₁ K₂ : ℕ)
    {H H' : ℕ → Type*} [∀ n, AddCommGroup (H n)] [∀ n, AddCommGroup (H' n)]
    (π : ∀ n, M →+ H n) (π' : ∀ n, M' →+ H' n)
    (fH : ∀ n, H n →+ H n) (gH : ∀ n, H' n →+ H' n)
    (hπ : ∀ n a, π n (f.hom a) = fH n (π n a)) (hπ' : ∀ n b, π' n (g.hom b) = gH n (π' n b))
    (hker : ∀ n a, π n a = 0 → ∃ a', a = (p ^ (n + 1)) • a')
    (hker' : ∀ n b, π' n b = 0 → ∃ b', b = (p ^ (n + 1)) • b')
    (hrange : ∀ n (y : H n), ∃ a, π n a = (p ^ K) • y)
    (hrange' : ∀ n (y : H' n), ∃ b, π' n b = (p ^ K) • y)
    {I : Type*} (φ : I → (M ⟶ M)) (ψ : I → (M' ⟶ M'))
    (φH : I → ∀ n, H n →+ H n) (ψH : I → ∀ n, H' n →+ H' n)
    (hφ : ∀ i n a, π n ((φ i).hom a) = φH i n (π n a))
    (hψ : ∀ i n b, π' n ((ψ i).hom b) = ψH i n (π' n b))
    (ε : ∀ n, H n →+ H' n →+ ZMod (p ^ (n + 1)))
    (hl : ∀ n x, (∀ y, ε n x y = 0) → (p ^ K₁) • x = 0)
    (hr : ∀ n y, (∀ x, ε n x y = 0) → (p ^ K₂) • y = 0)
    (hε : ∀ n x y, ε n (fH n x) (gH n y) = (c : ZMod (p ^ (n + 1))) * ε n x y)
    (hb : ∀ i n x y, ε n (φH i n x) y = ε n x (ψH i n y)) :
    ∃ B : (ModuleCat.extendScalars.{0, 0, v} (algebraMap ℤ_[p] ℚ_[p])).obj M →ₗ[ℚ_[p]]
        (ModuleCat.extendScalars.{0, 0, v} (algebraMap ℤ_[p] ℚ_[p])).obj M' →ₗ[ℚ_[p]] ℚ_[p],
      B.IsPerfPair ∧ (∀ v w,
        B (((ModuleCat.extendScalars.{0, 0, v} (algebraMap ℤ_[p] ℚ_[p])).map f).hom v)
          (((ModuleCat.extendScalars.{0, 0, v} (algebraMap ℤ_[p] ℚ_[p])).map g).hom w) =
          (c : ℚ_[p]) * B v w) ∧
      ∀ i v w,
        B (((ModuleCat.extendScalars.{0, 0, v} (algebraMap ℤ_[p] ℚ_[p])).map (φ i)).hom v) w =
          B v (((ModuleCat.extendScalars.{0, 0, v} (algebraMap ℤ_[p] ℚ_[p])).map (ψ i)).hom w) := by
  refine exists_isPerfPair_of_forall_zmodPow_balanced f.hom g.hom c (K + K₁ + K₂)
    (fun i => (φ i).hom) (fun i => (ψ i).hom) fun n => ?_
  cases n with
  | zero =>
    refine ⟨0, fun a _ => ⟨(p : ℤ_[p]) ^ (K + K₁ + K₂) • a, by rw [pow_zero, one_smul]⟩,
      fun b _ => ⟨(p : ℤ_[p]) ^ (K + K₁ + K₂) • b, by rw [pow_zero, one_smul]⟩,
      fun a b => ?_, fun i a b => rfl⟩
    simp only [AddMonoidHom.zero_apply, mul_zero]
  | succ m =>
    refine ⟨((ε m).compl₂ (π' m)).comp (π m), ?_, ?_, fun a b => ?_, fun i a b => ?_⟩
    · intro a ha
      have h1 : ∀ y, ε m ((p ^ K) • π m a) y = 0 := fun y => by
        obtain ⟨b, hb'⟩ := hrange' m y
        rw [map_nsmul, AddMonoidHom.nsmul_apply, ← map_nsmul (ε m (π m a)), ← hb']
        simpa only [AddMonoidHom.comp_apply, AddMonoidHom.compl₂_apply] using ha b
      have h2 : π m ((p ^ K₁) • (p ^ K) • a) = 0 := by
        rw [map_nsmul, map_nsmul]
        exact hl m _ h1
      obtain ⟨a', ha'⟩ := hker m _ h2
      simp only [← Nat.cast_smul_eq_nsmul ℤ_[p], Nat.cast_pow, smul_smul] at ha'
      refine ⟨(p : ℤ_[p]) ^ K₂ • a', ?_⟩
      rw [show (p : ℤ_[p]) ^ (K + K₁ + K₂) =
          (p : ℤ_[p]) ^ K₂ * ((p : ℤ_[p]) ^ K₁ * (p : ℤ_[p]) ^ K) by ring, mul_smul, ha',
        smul_comm]
    · intro b hb'
      have h1 : ∀ x, ε m x ((p ^ K) • π' m b) = 0 := fun x => by
        obtain ⟨a, ha⟩ := hrange m x
        rw [map_nsmul, ← AddMonoidHom.nsmul_apply, ← map_nsmul (ε m), ← ha]
        simpa only [AddMonoidHom.comp_apply, AddMonoidHom.compl₂_apply] using hb' a
      have h2 : π' m ((p ^ K₂) • (p ^ K) • b) = 0 := by
        rw [map_nsmul, map_nsmul]
        exact hr m _ h1
      obtain ⟨b', hb''⟩ := hker' m _ h2
      simp only [← Nat.cast_smul_eq_nsmul ℤ_[p], Nat.cast_pow, smul_smul] at hb''
      refine ⟨(p : ℤ_[p]) ^ K₁ • b', ?_⟩
      rw [show (p : ℤ_[p]) ^ (K + K₁ + K₂) =
          (p : ℤ_[p]) ^ K₁ * ((p : ℤ_[p]) ^ K₂ * (p : ℤ_[p]) ^ K) by ring, mul_smul, hb'',
        smul_comm]
    · simp only [AddMonoidHom.comp_apply, AddMonoidHom.compl₂_apply, hπ, hπ']
      exact hε m _ _
    · simp only [AddMonoidHom.comp_apply, AddMonoidHom.compl₂_apply, hφ, hψ]
      exact hb i m _ _

end Main

end Stacks.EtaleCohomology.LAdicPairing

end
