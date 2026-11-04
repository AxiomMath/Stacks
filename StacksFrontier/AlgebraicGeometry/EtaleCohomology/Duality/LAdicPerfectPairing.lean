module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LAdicGramMatrix
public import Mathlib.Topology.Algebra.Ring.Compact
public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# Poincaré duality over `ℚ_p` from equivariant pairings modulo every `pⁿ`

Let `M`, `M'` be finitely generated `ℤ_p`-modules with endomorphisms `f`, `g`, and suppose that
for every `n` there is a biadditive pairing `e : M × M' → ℤ/pⁿ` with `e(f a, g b) = c e(a, b)`,
whose left and right kernels are contained in `p^{n-K}` for a constant `K` (precisely:
`e(a, -) = 0` implies `p^K a ∈ pⁿ M`, and symmetrically). The pairings need not be compatible
with each other. Then there is a perfect pairing `B` on `(ℚ_p ⊗ M) × (ℚ_p ⊗ M')` with
`B(f v, g w) = c B(v, w)`.

For free modules the bilinear forms, given by matrices over `ℤ_p`, solving the conditions modulo
`pⁿ` form a decreasing sequence of nonempty closed subsets of a compact space; a point of the
intersection is an equivariant pairing over `ℤ_p`, nondegenerate on both sides. The general case
reduces to the torsion-free quotients, after multiplying the pairings by a power of `p` killing
the torsion.

## Main results

* `Stacks.EtaleCohomology.LAdicPairing.exists_pairing_of_forall_zmodPow`: the free case, over
  `ℤ_p`.
* `Stacks.EtaleCohomology.LAdicPairing.rationalPairing`: the base change of a pairing to `ℚ_p`,
  with `rationalPairing_baseChange_baseChange` (equivariance) and
  `eq_zero_of_rationalPairing_eq_zero` (nondegeneracy).
* `Stacks.EtaleCohomology.LAdicPairing.exists_isPerfPair_of_forall_zmodPow`: the perfect pairing
  over `ℚ_p`.
-/

@[expose] public noncomputable section

open Matrix

universe v

namespace Stacks.EtaleCohomology.LAdicPairing

variable {p : ℕ} [Fact p.Prime]

/-- The kernel of `ℤ_p → ℤ/pⁿ` is open. -/
theorem isOpen_ker_toZModPow (n : ℕ) :
    IsOpen ((RingHom.ker (PadicInt.toZModPow (p := p) n) : Ideal ℤ_[p]) : Set ℤ_[p]) := by
  rw [PadicInt.ker_toZModPow, ← Ideal.span_singleton_pow, ← PadicInt.maximalIdeal_eq_span_p]
  exact IsLocalRing.isOpen_maximalIdeal_pow ℤ_[p] n

/-- A property of matrices over `ℤ_p` depending only on the reduction modulo `pⁿ` defines a
closed set. -/
theorem isClosed_setOf_of_map_eq {ι ι' : Type*} [Finite ι] [Finite ι'] (n : ℕ)
    (P : Matrix ι ι' ℤ_[p] → Prop)
    (hP : ∀ J J', J.map (PadicInt.toZModPow n) = J'.map (PadicInt.toZModPow n) → P J → P J') :
    IsClosed {J | P J} := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro J hJ
  refine ⟨⋂ i, ⋂ j, (fun J' : Matrix ι ι' ℤ_[p] => J' i j - J i j) ⁻¹'
      ((RingHom.ker (PadicInt.toZModPow (p := p) n) : Ideal ℤ_[p]) : Set ℤ_[p]),
    fun J' hJ' hPJ' => hJ (hP J' J ?_ hPJ'), ?_, ?_⟩
  · ext i j
    have := Set.mem_iInter.1 (Set.mem_iInter.1 hJ' i) j
    simp only [Set.mem_preimage, SetLike.mem_coe, RingHom.mem_ker, map_sub, sub_eq_zero] at this
    exact this
  · exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      (isOpen_ker_toZModPow n).preimage ((continuous_id.matrix_elem i j).sub continuous_const)
  · simp

section Free

variable {L L' : Type*} [AddCommGroup L] [Module ℤ_[p] L] [AddCommGroup L'] [Module ℤ_[p] L']
  {ι ι' : Type*} [Fintype ι] [Fintype ι'] [DecidableEq ι] [DecidableEq ι']
  (m : Module.Basis ι ℤ_[p] L) (m' : Module.Basis ι' ℤ_[p] L')

/-- The reduction modulo `pⁿ` of the bilinear form of a matrix only depends on the reduction of
the matrix. -/
theorem toZModPow_toLinearMap₂ (n : ℕ) (J : Matrix ι ι' ℤ_[p]) (a : L) (b : L') :
    PadicInt.toZModPow n (Matrix.toLinearMap₂ m m' J a b) =
      ∑ i, ∑ j, PadicInt.toZModPow n (m.repr a i) * PadicInt.toZModPow n (m'.repr b j) *
        J.map (PadicInt.toZModPow n) i j := by
  rw [Matrix.toLinearMap₂_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [smul_eq_mul, map_mul, Matrix.map_apply]
  ring

omit [DecidableEq ι] [DecidableEq ι'] in
/-- An additive pairing to `ℤ/pⁿ` is determined by its values on the basis vectors. -/
theorem pairing_eq_sum (n : ℕ) (e : L →+ L' →+ ZMod (p ^ n)) (a : L) (b : L') :
    e a b = ∑ i, ∑ j, PadicInt.toZModPow n (m.repr a i) * PadicInt.toZModPow n (m'.repr b j) *
        e (m i) (m' j) := by
  conv_lhs => rw [← m.sum_repr a, ← m'.sum_repr b]
  rw [map_sum (e : L →+ L' →+ ZMod (p ^ n)), AddMonoidHom.finset_sum_apply]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul_eq_toZModPow_mul (e (m.repr a i • m i))]
  have : e (m.repr a i • m i) (m' j) = PadicInt.toZModPow n (m.repr a i) * e (m i) (m' j) :=
    map_smul_eq_toZModPow_mul (e.flip (m' j)) (m.repr a i) (m i)
  rw [this]
  ring

/-- The residue of `x` modulo `pⁿ` vanishes exactly when `x` is a multiple of `pⁿ`. -/
theorem toZModPow_eq_zero_iff (n : ℕ) (x : ℤ_[p]) :
    PadicInt.toZModPow n x = 0 ↔ ∃ t : ℤ_[p], x = t * (p : ℤ_[p]) ^ n := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton']
  exact ⟨fun ⟨t, ht⟩ => ⟨t, ht.symm⟩, fun ⟨t, ht⟩ => ⟨t, ht.symm⟩⟩

variable (f : L →ₗ[ℤ_[p]] L) (g : L' →ₗ[ℤ_[p]] L') (c K : ℕ)

/-- The bilinear form of the matrix `J` satisfies, modulo `pⁿ`, the equivariance relation with
factor `c`, and its left and right kernels modulo `pⁿ` lie in `p^{n-K}`. -/
def IsGoodMod (n : ℕ) (J : Matrix ι ι' ℤ_[p]) : Prop :=
  (∀ a, (∀ b, PadicInt.toZModPow n (Matrix.toLinearMap₂ m m' J a b) = 0) →
      ∃ a', (p : ℤ_[p]) ^ K • a = (p : ℤ_[p]) ^ n • a') ∧
  (∀ b, (∀ a, PadicInt.toZModPow n (Matrix.toLinearMap₂ m m' J a b) = 0) →
      ∃ b', (p : ℤ_[p]) ^ K • b = (p : ℤ_[p]) ^ n • b') ∧
  ∀ a b, PadicInt.toZModPow n (Matrix.toLinearMap₂ m m' J (f a) (g b)) =
    (c : ZMod (p ^ n)) * PadicInt.toZModPow n (Matrix.toLinearMap₂ m m' J a b)

/-- `IsGoodMod` only depends on the reduction of the matrix modulo `pⁿ`. -/
theorem isGoodMod_congr {n : ℕ} {J J' : Matrix ι ι' ℤ_[p]}
    (hJ : J.map (PadicInt.toZModPow n) = J'.map (PadicInt.toZModPow n))
    (hgood : IsGoodMod m m' f g c K n J) : IsGoodMod m m' f g c K n J' := by
  have h : ∀ a b, PadicInt.toZModPow n (Matrix.toLinearMap₂ m m' J a b) =
      PadicInt.toZModPow n (Matrix.toLinearMap₂ m m' J' a b) := fun a b => by
    rw [toZModPow_toLinearMap₂, toZModPow_toLinearMap₂, hJ]
  simpa only [IsGoodMod, h] using hgood

/-- In a free module, `p • x = p • y` implies `x = y`. -/
theorem eq_of_p_smul_eq {N : Type*} [AddCommGroup N] [Module ℤ_[p] N] {κ : Type*}
    (b : Module.Basis κ ℤ_[p] N) {x y : N} (h : (p : ℤ_[p]) • x = (p : ℤ_[p]) • y) : x = y := by
  have : Module.Free ℤ_[p] N := Module.Free.of_basis b
  exact smul_right_injective N (by exact_mod_cast (Fact.out : p.Prime).ne_zero) h

/-- In a free `ℤ_p`-module, an element `x` with `p^K x ∈ pⁿ N` for every `n` is zero. -/
theorem eq_zero_of_forall_pow_smul {N : Type*} [AddCommGroup N] [Module ℤ_[p] N] {κ : Type*}
    (b : Module.Basis κ ℤ_[p] N) (K : ℕ) (x : N)
    (hx : ∀ n : ℕ, ∃ x', (p : ℤ_[p]) ^ K • x = (p : ℤ_[p]) ^ n • x') : x = 0 := by
  have h0 : (p : ℤ_[p]) ^ K • x = 0 := by
    refine b.repr.injective (Finsupp.ext fun i => ?_)
    rw [map_zero, Finsupp.zero_apply, ← PadicInt.ext_of_toZModPow]
    intro n
    obtain ⟨x', hx'⟩ := hx n
    rw [hx', map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, map_zero, map_pow,
      map_natCast, ← Nat.cast_pow, ZMod.natCast_self, zero_mul]
  have : Module.Free ℤ_[p] N := Module.Free.of_basis b
  exact (smul_eq_zero.1 h0).resolve_left
    (pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero))

/-- In a free module, `p^K • p • a ∈ pⁿ⁺¹ N` implies `p^K • a ∈ pⁿ N`. -/
private theorem exists_pow_smul_eq_of_succ {N : Type*} [AddCommGroup N] [Module ℤ_[p] N]
    {κ : Type*} (b : Module.Basis κ ℤ_[p] N) {K n : ℕ} {a : N}
    (h : ∃ a', (p : ℤ_[p]) ^ K • (p : ℤ_[p]) • a = (p : ℤ_[p]) ^ (n + 1) • a') :
    ∃ a', (p : ℤ_[p]) ^ K • a = (p : ℤ_[p]) ^ n • a' := by
  obtain ⟨a', ha'⟩ := h
  exact ⟨a', eq_of_p_smul_eq b (by rw [smul_comm, ha', smul_smul, pow_succ'])⟩

/-- A matrix good modulo `pⁿ⁺¹` is good modulo `pⁿ`. -/
theorem isGoodMod_of_succ {n : ℕ} {J : Matrix ι ι' ℤ_[p]}
    (hgood : IsGoodMod m m' f g c K (n + 1) J) : IsGoodMod m m' f g c K n J := by
  obtain ⟨hl, hr, he⟩ := hgood
  refine ⟨fun a ha => ?_, fun b hb => ?_, fun a b => ?_⟩
  · refine exists_pow_smul_eq_of_succ m (hl ((p : ℤ_[p]) • a) fun b => ?_)
    obtain ⟨t, ht⟩ := (toZModPow_eq_zero_iff n _).1 (ha b)
    rw [toZModPow_eq_zero_iff]
    exact ⟨t, by rw [map_smul, LinearMap.smul_apply, smul_eq_mul, ht]; ring⟩
  · refine exists_pow_smul_eq_of_succ m' (hr ((p : ℤ_[p]) • b) fun a => ?_)
    obtain ⟨t, ht⟩ := (toZModPow_eq_zero_iff n _).1 (hb a)
    rw [toZModPow_eq_zero_iff]
    exact ⟨t, by rw [map_smul, smul_eq_mul, ht]; ring⟩
  · have hc := congrArg (ZMod.castHom (pow_dvd_pow p n.le_succ) (ZMod (p ^ n))) (he a b)
    simp only [map_mul, map_natCast] at hc
    rwa [← RingHom.comp_apply, PadicInt.zmod_cast_comp_toZModPow _ _ n.le_succ,
      ← RingHom.comp_apply, PadicInt.zmod_cast_comp_toZModPow _ _ n.le_succ] at hc

omit [DecidableEq ι] [DecidableEq ι'] in
include m m' in
/-- **An equivariant pairing over `ℤ_p` from equivariant pairings modulo every `pⁿ`.** -/
theorem exists_pairing_of_forall_zmodPow_of_basis
    (h : ∀ n : ℕ, ∃ e : L →+ L' →+ ZMod (p ^ n),
      (∀ a, (∀ b, e a b = 0) → ∃ a', (p : ℤ_[p]) ^ K • a = (p : ℤ_[p]) ^ n • a') ∧
      (∀ b, (∀ a, e a b = 0) → ∃ b', (p : ℤ_[p]) ^ K • b = (p : ℤ_[p]) ^ n • b') ∧
      ∀ a b, e (f a) (g b) = (c : ZMod (p ^ n)) * e a b) :
    ∃ β : L →ₗ[ℤ_[p]] L' →ₗ[ℤ_[p]] ℤ_[p], (∀ a, (∀ b, β a b = 0) → a = 0) ∧
      (∀ b, (∀ a, β a b = 0) → b = 0) ∧ ∀ a b, β (f a) (g b) = c * β a b := by
  classical
  let t : ℕ → Set (Matrix ι ι' ℤ_[p]) := fun n => {J | IsGoodMod m m' f g c K n J}
  have hcl : ∀ n, IsClosed (t n) := fun n =>
    isClosed_setOf_of_map_eq n _ fun J J' hJ => isGoodMod_congr m m' f g c K hJ
  have hdec : ∀ n, t (n + 1) ⊆ t n := fun n J hJ => isGoodMod_of_succ m m' f g c K hJ
  have hne : ∀ n, (t n).Nonempty := by
    intro n
    obtain ⟨e, hl, hr, he⟩ := h n
    have hs := ZMod.ringHom_surjective (PadicInt.toZModPow (p := p) n)
    let J : Matrix ι ι' ℤ_[p] := fun i j => Function.surjInv hs (e (m i) (m' j))
    have hJ : ∀ a b, PadicInt.toZModPow n (Matrix.toLinearMap₂ m m' J a b) = e a b := by
      intro a b
      rw [toZModPow_toLinearMap₂, pairing_eq_sum m m' n e a b]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.map_apply]
      exact congrArg _ (Function.surjInv_eq hs _)
    refine ⟨J, ?_, ?_, ?_⟩
    · intro a ha
      exact hl a fun b => by rw [← hJ]; exact ha b
    · intro b hb
      exact hr b fun a => by rw [← hJ]; exact hb a
    · intro a b
      rw [hJ, hJ]
      exact he a b
  have : CompactSpace (Matrix ι ι' ℤ_[p]) := inferInstanceAs (CompactSpace (ι → ι' → ℤ_[p]))
  obtain ⟨J, hJ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed t hdec hne
    (hcl 0).isCompact hcl
  rw [Set.mem_iInter] at hJ
  refine ⟨Matrix.toLinearMap₂ m m' J, fun a ha => ?_, fun b hb => ?_, fun a b => ?_⟩
  · exact eq_zero_of_forall_pow_smul m K a fun n => (hJ n).1 a fun b => by rw [ha b, map_zero]
  · exact eq_zero_of_forall_pow_smul m' K b fun n => (hJ n).2.1 b fun a => by rw [hb a, map_zero]
  · rw [← PadicInt.ext_of_toZModPow]
    intro n
    rw [(hJ n).2.2 a b, map_mul, map_natCast]

end Free

/-- **An equivariant pairing over `ℤ_p` from equivariant pairings modulo every `pⁿ`**, for free
`ℤ_p`-modules of finite rank. -/
theorem exists_pairing_of_forall_zmodPow {L L' : Type*} [AddCommGroup L] [Module ℤ_[p] L]
    [AddCommGroup L'] [Module ℤ_[p] L'] [Module.Free ℤ_[p] L] [Module.Finite ℤ_[p] L]
    [Module.Free ℤ_[p] L'] [Module.Finite ℤ_[p] L']
    (f : L →ₗ[ℤ_[p]] L) (g : L' →ₗ[ℤ_[p]] L') (c K : ℕ)
    (h : ∀ n : ℕ, ∃ e : L →+ L' →+ ZMod (p ^ n),
      (∀ a, (∀ b, e a b = 0) → ∃ a', (p : ℤ_[p]) ^ K • a = (p : ℤ_[p]) ^ n • a') ∧
      (∀ b, (∀ a, e a b = 0) → ∃ b', (p : ℤ_[p]) ^ K • b = (p : ℤ_[p]) ^ n • b') ∧
      ∀ a b, e (f a) (g b) = (c : ZMod (p ^ n)) * e a b) :
    ∃ β : L →ₗ[ℤ_[p]] L' →ₗ[ℤ_[p]] ℤ_[p], (∀ a, (∀ b, β a b = 0) → a = 0) ∧
      (∀ b, (∀ a, β a b = 0) → b = 0) ∧ ∀ a b, β (f a) (g b) = c * β a b := by
  classical
  exact exists_pairing_of_forall_zmodPow_of_basis (Module.Free.chooseBasis ℤ_[p] L)
    (Module.Free.chooseBasis ℤ_[p] L') f g c K h

/-! ### Finitely generated modules and the base change to `ℚ_p` -/

section Rational

open TensorProduct

variable {M M' : Type*} [AddCommGroup M] [Module ℤ_[p] M] [AddCommGroup M'] [Module ℤ_[p] M']

/-- The `ℚ_p`-linear form `ℚ_p ⊗ M' → ℚ_p` induced by `β(a, -)`, as a function of `a`. -/
def rationalPairingAux (β : M →ₗ[ℤ_[p]] M' →ₗ[ℤ_[p]] ℤ_[p]) :
    M →ₗ[ℤ_[p]] ℚ_[p] ⊗[ℤ_[p]] M' →ₗ[ℚ_[p]] ℚ_[p] where
  toFun a := (TensorProduct.AlgebraTensorModule.rid ℤ_[p] ℚ_[p] ℚ_[p]).toLinearMap ∘ₗ
    (β a).baseChange ℚ_[p]
  map_add' a a' := by
    rw [map_add, LinearMap.baseChange_add, LinearMap.comp_add]
  map_smul' x a := by
    rw [map_smul, LinearMap.baseChange_smul, LinearMap.comp_smul, RingHom.id_apply]

/-- **The rational pairing** `(ℚ_p ⊗ M) × (ℚ_p ⊗ M') → ℚ_p` of a `ℤ_p`-bilinear pairing. -/
def rationalPairing (β : M →ₗ[ℤ_[p]] M' →ₗ[ℤ_[p]] ℤ_[p]) :
    ℚ_[p] ⊗[ℤ_[p]] M →ₗ[ℚ_[p]] ℚ_[p] ⊗[ℤ_[p]] M' →ₗ[ℚ_[p]] ℚ_[p] :=
  TensorProduct.AlgebraTensorModule.lift
    (LinearMap.toSpanSingleton ℚ_[p] _ (rationalPairingAux β))

@[simp]
theorem rationalPairing_tmul (β : M →ₗ[ℤ_[p]] M' →ₗ[ℤ_[p]] ℤ_[p]) (x y : ℚ_[p]) (a : M)
    (b : M') : rationalPairing β (x ⊗ₜ a) (y ⊗ₜ b) = algebraMap ℤ_[p] ℚ_[p] (β a b) * (x * y) := by
  simp only [rationalPairing, TensorProduct.AlgebraTensorModule.lift_tmul,
    LinearMap.toSpanSingleton_apply, LinearMap.smul_apply, rationalPairingAux,
    LinearMap.coe_mk, AddHom.coe_mk, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.baseChange_tmul, LinearEquiv.coe_coe,
    TensorProduct.AlgebraTensorModule.rid_tmul, smul_eq_mul, Algebra.smul_def]
  ring

/-- Equivariance passes to the rational pairing. -/
theorem rationalPairing_baseChange_baseChange (β : M →ₗ[ℤ_[p]] M' →ₗ[ℤ_[p]] ℤ_[p])
    (f : M →ₗ[ℤ_[p]] M) (g : M' →ₗ[ℤ_[p]] M') (c : ℚ_[p])
    (h : ∀ a b, algebraMap ℤ_[p] ℚ_[p] (β (f a) (g b)) = c * algebraMap ℤ_[p] ℚ_[p] (β a b))
    (v : ℚ_[p] ⊗[ℤ_[p]] M)
    (w : ℚ_[p] ⊗[ℤ_[p]] M') :
    rationalPairing β (f.baseChange ℚ_[p] v) (g.baseChange ℚ_[p] w) =
      c * rationalPairing β v w := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | add v v' hv hv' => simp only [map_add, LinearMap.add_apply, hv, hv', mul_add]
  | tmul x a =>
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add w w' hw hw' => simp only [map_add, hw, hw', mul_add]
    | tmul y b =>
      simp only [LinearMap.baseChange_tmul, rationalPairing_tmul, h]
      ring

/-- An element of `ℚ_p ⊗ M` pairing to zero with all of `ℚ_p ⊗ M'` comes from an element `a` of
`M` with `β(a, -) = 0`, up to a nonzero scalar. -/
theorem eq_zero_of_rationalPairing_eq_zero (β : M →ₗ[ℤ_[p]] M' →ₗ[ℤ_[p]] ℤ_[p])
    (hβ : ∀ a, (∀ b, β a b = 0) → ∃ s : ℤ_[p], s ≠ 0 ∧ s • a = 0)
    (v : ℚ_[p] ⊗[ℤ_[p]] M) (hv : ∀ w, rationalPairing β v w = 0) : v = 0 := by
  obtain ⟨⟨a, s⟩, hv'⟩ := IsLocalizedModule.mk'_surjective (nonZeroDivisors ℤ_[p])
    (TensorProduct.mk ℤ_[p] ℚ_[p] M 1) v
  simp only [Function.uncurry_apply_pair] at hv'
  subst hv'
  have hs : algebraMap ℤ_[p] ℚ_[p] (s : ℤ_[p]) •
      IsLocalizedModule.mk' (TensorProduct.mk ℤ_[p] ℚ_[p] M 1) a s = (1 : ℚ_[p]) ⊗ₜ a := by
    rw [algebraMap_smul]
    exact IsLocalizedModule.mk'_cancel' (TensorProduct.mk ℤ_[p] ℚ_[p] M 1) a s
  have ha : ∀ b, β a b = 0 := by
    intro b
    have h2 : rationalPairing β ((1 : ℚ_[p]) ⊗ₜ a) ((1 : ℚ_[p]) ⊗ₜ b) = 0 := by
      rw [← hs, map_smul, LinearMap.smul_apply, hv, smul_zero]
    rw [rationalPairing_tmul, mul_one, mul_one] at h2
    exact (FaithfulSMul.algebraMap_injective ℤ_[p] ℚ_[p]) (by rw [h2, map_zero])
  obtain ⟨t, ht, hta⟩ := hβ a ha
  have h0 : (1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] a = 0 := by
    have h1 : algebraMap ℤ_[p] ℚ_[p] t • ((1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] a) = 0 := by
      rw [algebraMap_smul, ← TensorProduct.tmul_smul, hta, tmul_zero]
    have htq : (algebraMap ℤ_[p] ℚ_[p] t) ≠ 0 :=
      (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective ℤ_[p] ℚ_[p])).2 ht
    exact (smul_eq_zero.1 h1).resolve_left htq
  have hs0 : (algebraMap ℤ_[p] ℚ_[p] (s : ℤ_[p])) ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective ℤ_[p] ℚ_[p])).2
      (nonZeroDivisors.ne_zero s.2)
  rw [← hs] at h0
  exact (smul_eq_zero.1 h0).resolve_left hs0

/-- The flip of the rational pairing of `β` is the rational pairing of the flip of `β`. -/
theorem rationalPairing_flip (β : M →ₗ[ℤ_[p]] M' →ₗ[ℤ_[p]] ℤ_[p]) :
    (rationalPairing β).flip = rationalPairing β.flip := by
  refine TensorProduct.AlgebraTensorModule.ext fun y b => ?_
  refine TensorProduct.AlgebraTensorModule.ext fun x a => ?_
  rw [LinearMap.flip_apply, rationalPairing_tmul, rationalPairing_tmul, LinearMap.flip_apply,
    mul_comm x y]

end Rational

/-! ### The torsion-free quotient -/

section Torsion

open TensorProduct Submodule

variable {M M' : Type*} [AddCommGroup M] [Module ℤ_[p] M] [AddCommGroup M'] [Module ℤ_[p] M']

/-- The torsion of a finitely generated `ℤ_p`-module is killed by a power of `p`. -/
theorem exists_pow_smul_eq_zero_of_mem_torsion [Module.Finite ℤ_[p] M] :
    ∃ k : ℕ, ∀ t ∈ torsion ℤ_[p] M, (p : ℤ_[p]) ^ k • t = 0 := by
  classical
  obtain ⟨s, hs⟩ := IsNoetherian.noetherian (torsion ℤ_[p] M)
  have hk : ∀ x : s, ∃ k : ℕ, (p : ℤ_[p]) ^ k • (x : M) = 0 := by
    intro x
    have hxT : (x : M) ∈ torsion ℤ_[p] M := hs ▸ Submodule.subset_span x.2
    obtain ⟨⟨a, ha⟩, hax⟩ := (mem_torsion_iff (x : M)).1 hxT
    have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
    refine ⟨a.valuation, ?_⟩
    have hax' : (PadicInt.unitCoeff ha0 : ℤ_[p]) • ((p : ℤ_[p]) ^ a.valuation • (x : M)) = 0 := by
      rw [smul_smul, ← PadicInt.unitCoeff_spec ha0]
      exact hax
    have := congrArg (fun y => ((PadicInt.unitCoeff ha0)⁻¹ : ℤ_[p]ˣ) • y) hax'
    simpa [Units.smul_def, smul_smul] using this
  choose k hk using hk
  refine ⟨∑ x, k x, fun t ht => ?_⟩
  rw [← hs] at ht
  induction ht using Submodule.span_induction with
  | mem x hx =>
    have hle : k ⟨x, hx⟩ ≤ ∑ y, k y :=
      Finset.single_le_sum (fun y _ => Nat.zero_le (k y)) (Finset.mem_univ _)
    rw [← Nat.sub_add_cancel hle, pow_add, mul_smul, hk ⟨x, hx⟩, smul_zero]
  | zero => rw [smul_zero]
  | add x y _ _ hx hy => rw [smul_add, hx, hy, add_zero]
  | smul a x _ hx => rw [smul_comm, hx, smul_zero]

/-- An endomorphism maps torsion into torsion. -/
theorem torsion_le_comap (f : M →ₗ[ℤ_[p]] M) :
    torsion ℤ_[p] M ≤ (torsion ℤ_[p] M).comap f := by
  intro x hx
  obtain ⟨a, ha⟩ := (mem_torsion_iff x).1 hx
  refine (mem_torsion_iff _).2 ⟨a, ?_⟩
  rw [Submonoid.smul_def] at ha ⊢
  rw [← map_smul, ha, map_zero]

/-- An element of `M` with zero image in `M ⧸ torsion` is killed by a nonzero scalar. -/
private theorem exists_ne_zero_smul_eq_zero_of_mkQ_eq_zero {a : M}
    (h : (torsion ℤ_[p] M).mkQ a = 0) : ∃ s : ℤ_[p], s ≠ 0 ∧ s • a = 0 := by
  rw [mkQ_apply, Submodule.Quotient.mk_eq_zero] at h
  obtain ⟨s, hs⟩ := (mem_torsion_iff a).1 h
  exact ⟨s, nonZeroDivisors.ne_zero s.2, hs⟩

end Torsion

/-! ### The perfect pairing on `ℚ_p ⊗ M` -/

section Main

open TensorProduct Submodule

variable {M M' : Type*} [AddCommGroup M] [Module ℤ_[p] M] [AddCommGroup M'] [Module ℤ_[p] M']
  [Module.Finite ℤ_[p] M] [Module.Finite ℤ_[p] M']

omit [Module.Finite ℤ_[p] M] in
/-- Elements of `M` with the same image in `M ⧸ torsion` agree after multiplication by a power of
`p` killing the torsion. -/
theorem pow_smul_eq_of_mkQ_eq {k : ℕ} (hk : ∀ t ∈ torsion ℤ_[p] M, (p : ℤ_[p]) ^ k • t = 0)
    {a a' : M} (h : (torsion ℤ_[p] M).mkQ a = (torsion ℤ_[p] M).mkQ a') :
    (p : ℤ_[p]) ^ k • a = (p : ℤ_[p]) ^ k • a' := by
  rw [mkQ_apply, mkQ_apply, Submodule.Quotient.eq] at h
  rw [← sub_eq_zero, ← smul_sub]
  exact hk _ h

/-- **Poincaré duality over `ℚ_p` from finite levels.** Let `M`, `M'` be finitely generated
`ℤ_p`-modules with endomorphisms `f`, `g`, and suppose that for every `n` there is a biadditive
pairing `e : M × M' → ℤ/pⁿ` with `e(f a, g b) = c e(a, b)` whose left and right kernels are
contained in `p^{n-K}` (precisely: `e(a, -) = 0` implies `p^K a ∈ pⁿ M`, and symmetrically).
Then there is a perfect pairing `B` on `(ℚ_p ⊗ M) × (ℚ_p ⊗ M')` with
`B(f v, g w) = c B(v, w)`. The levels need not be compatible. -/
theorem exists_isPerfPair_of_forall_zmodPow (f : M →ₗ[ℤ_[p]] M) (g : M' →ₗ[ℤ_[p]] M')
    (c K : ℕ)
    (h : ∀ n : ℕ, ∃ e : M →+ M' →+ ZMod (p ^ n),
      (∀ a, (∀ b, e a b = 0) → ∃ a', (p : ℤ_[p]) ^ K • a = (p : ℤ_[p]) ^ n • a') ∧
      (∀ b, (∀ a, e a b = 0) → ∃ b', (p : ℤ_[p]) ^ K • b = (p : ℤ_[p]) ^ n • b') ∧
      ∀ a b, e (f a) (g b) = (c : ZMod (p ^ n)) * e a b) :
    ∃ B : ℚ_[p] ⊗[ℤ_[p]] M →ₗ[ℚ_[p]] ℚ_[p] ⊗[ℤ_[p]] M' →ₗ[ℚ_[p]] ℚ_[p], B.IsPerfPair ∧
      ∀ v w, B (f.baseChange ℚ_[p] v) (g.baseChange ℚ_[p] w) = (c : ℚ_[p]) * B v w := by
  obtain ⟨k₁, hk₁⟩ := exists_pow_smul_eq_zero_of_mem_torsion (p := p) (M := M)
  obtain ⟨k₂, hk₂⟩ := exists_pow_smul_eq_zero_of_mem_torsion (p := p) (M := M')
  set k := k₁ + k₂
  have hkM : ∀ t ∈ torsion ℤ_[p] M, (p : ℤ_[p]) ^ k • t = 0 := fun t ht => by
    rw [pow_add, mul_comm, mul_smul, hk₁ t ht, smul_zero]
  have hkM' : ∀ t ∈ torsion ℤ_[p] M', (p : ℤ_[p]) ^ k • t = 0 := fun t ht => by
    rw [pow_add, mul_smul, hk₂ t ht, smul_zero]
  set T := torsion ℤ_[p] M
  set T' := torsion ℤ_[p] M'
  let σ : M ⧸ T → M := Function.surjInv T.mkQ_surjective
  let σ' : M' ⧸ T' → M' := Function.surjInv T'.mkQ_surjective
  have hσ : ∀ x, T.mkQ (σ x) = x := Function.surjInv_eq T.mkQ_surjective
  have hσ' : ∀ y, T'.mkQ (σ' y) = y := Function.surjInv_eq T'.mkQ_surjective
  let fbar : M ⧸ T →ₗ[ℤ_[p]] M ⧸ T := T.mapQ T f (torsion_le_comap f)
  let gbar : M' ⧸ T' →ₗ[ℤ_[p]] M' ⧸ T' := T'.mapQ T' g (torsion_le_comap g)
  have hpk : ∀ {n : ℕ} (e : M →+ M' →+ ZMod (p ^ n)) (a : M) (b : M'),
      e ((p : ℤ_[p]) ^ k • a) ((p : ℤ_[p]) ^ k • b) =
        e ((p : ℤ_[p]) ^ k • (p : ℤ_[p]) ^ k • a) b := fun e a b => by
    rw [map_smul_eq_toZModPow_mul (e _)]
    exact (map_smul_eq_toZModPow_mul (e.flip b) _ _).symm
  have hpk' : ∀ {n : ℕ} (e : M →+ M' →+ ZMod (p ^ n)) (a : M) (b : M'),
      e ((p : ℤ_[p]) ^ k • a) ((p : ℤ_[p]) ^ k • b) =
        e a ((p : ℤ_[p]) ^ k • (p : ℤ_[p]) ^ k • b) := fun e a b => by
    have h1 : e ((p : ℤ_[p]) ^ k • a) ((p : ℤ_[p]) ^ k • b) =
        PadicInt.toZModPow _ ((p : ℤ_[p]) ^ k) * e a ((p : ℤ_[p]) ^ k • b) :=
      map_smul_eq_toZModPow_mul (e.flip _) _ _
    rw [h1, map_smul_eq_toZModPow_mul (e a) _ ((p : ℤ_[p]) ^ k • b)]
  have hlev : ∀ n : ℕ, ∃ e : M ⧸ T →+ M' ⧸ T' →+ ZMod (p ^ n),
      (∀ x, (∀ y, e x y = 0) → ∃ x', (p : ℤ_[p]) ^ (K + 2 * k) • x = (p : ℤ_[p]) ^ n • x') ∧
      (∀ y, (∀ x, e x y = 0) → ∃ y', (p : ℤ_[p]) ^ (K + 2 * k) • y = (p : ℤ_[p]) ^ n • y') ∧
      ∀ x y, e (fbar x) (gbar y) = (c : ZMod (p ^ n)) * e x y := by
    intro n
    obtain ⟨e, hl, hr, he⟩ := h n
    let eL : M ⧸ T →+ M' ⧸ T' →+ ZMod (p ^ n) :=
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
    have heL : ∀ a b, eL (T.mkQ a) (T'.mkQ b) =
        e ((p : ℤ_[p]) ^ k • a) ((p : ℤ_[p]) ^ k • b) := fun a b => by
      simp only [eL, AddMonoidHom.mk'_apply]
      rw [pow_smul_eq_of_mkQ_eq hkM (hσ _), pow_smul_eq_of_mkQ_eq hkM' (hσ' _)]
    refine ⟨eL, fun x hx => ?_, fun y hy => ?_, fun x y => ?_⟩
    · obtain ⟨a', ha'⟩ := hl ((p : ℤ_[p]) ^ k • (p : ℤ_[p]) ^ k • σ x) fun b => by
        rw [← hpk, ← heL, hσ]
        exact hx _
      refine ⟨T.mkQ a', ?_⟩
      rw [← hσ x, ← map_smul, ← map_smul, ← ha', smul_smul, smul_smul, ← pow_add, ← pow_add,
        two_mul, ← add_assoc]
    · obtain ⟨b', hb'⟩ := hr ((p : ℤ_[p]) ^ k • (p : ℤ_[p]) ^ k • σ' y) fun a => by
        rw [← hpk', ← heL, hσ']
        exact hy _
      refine ⟨T'.mkQ b', ?_⟩
      rw [← hσ' y, ← map_smul, ← map_smul, ← hb', smul_smul, smul_smul, ← pow_add, ← pow_add,
        two_mul, ← add_assoc]
    · rw [← hσ x, ← hσ' y]
      have h1 : fbar (T.mkQ (σ x)) = T.mkQ (f (σ x)) := rfl
      have h2 : gbar (T'.mkQ (σ' y)) = T'.mkQ (g (σ' y)) := rfl
      rw [h1, h2, heL, heL, ← map_smul, ← map_smul, he]
  obtain ⟨βbar, hβl, hβr, hβe⟩ :=
    exists_pairing_of_forall_zmodPow fbar gbar c (K + 2 * k) hlev
  let β : M →ₗ[ℤ_[p]] M' →ₗ[ℤ_[p]] ℤ_[p] := βbar.compl₁₂ T.mkQ T'.mkQ
  have hβ : ∀ a b, β a b = βbar (T.mkQ a) (T'.mkQ b) := fun a b => rfl
  have hl : ∀ a, (∀ b, β a b = 0) → ∃ s : ℤ_[p], s ≠ 0 ∧ s • a = 0 := by
    intro a ha
    exact exists_ne_zero_smul_eq_zero_of_mkQ_eq_zero
      (hβl _ fun y => by rw [← hσ' y, ← hβ]; exact ha _)
  have hr : ∀ b, (∀ a, β.flip b a = 0) → ∃ s : ℤ_[p], s ≠ 0 ∧ s • b = 0 := by
    intro b hb
    exact exists_ne_zero_smul_eq_zero_of_mkQ_eq_zero
      (hβr _ fun x => by rw [← hσ x, ← hβ]; exact hb _)
  refine ⟨rationalPairing β, ?_, ?_⟩
  · refine LinearMap.IsPerfPair.of_injective ?_ ?_
    · rw [injective_iff_map_eq_zero]
      intro v hv
      exact eq_zero_of_rationalPairing_eq_zero β hl v fun w => by rw [hv]; rfl
    · rw [injective_iff_map_eq_zero, rationalPairing_flip]
      intro w hw
      exact eq_zero_of_rationalPairing_eq_zero β.flip hr w fun v => by rw [hw]; rfl
  · intro v w
    refine rationalPairing_baseChange_baseChange β f g c (fun a b => ?_) v w
    have : β (f a) (g b) = c * β a b := by
      rw [hβ, hβ]
      exact hβe (T.mkQ a) (T'.mkQ b)
    rw [this, map_mul, map_natCast]

/-- **Poincaré duality over `ℚ_p` from finite levels**, on the extension of scalars
`ℚ_p ⊗ M = (ModuleCat.extendScalars (algebraMap ℤ_p ℚ_p)).obj M` of `ℤ_p`-modules. -/
theorem exists_isPerfPair_extendScalars_of_forall_zmodPow {M M' : ModuleCat.{v} ℤ_[p]}
    [Module.Finite ℤ_[p] M] [Module.Finite ℤ_[p] M'] (f : M ⟶ M) (g : M' ⟶ M') (c K : ℕ)
    (h : ∀ n : ℕ, ∃ e : M →+ M' →+ ZMod (p ^ n),
      (∀ a, (∀ b, e a b = 0) → ∃ a', (p : ℤ_[p]) ^ K • a = (p : ℤ_[p]) ^ n • a') ∧
      (∀ b, (∀ a, e a b = 0) → ∃ b', (p : ℤ_[p]) ^ K • b = (p : ℤ_[p]) ^ n • b') ∧
      ∀ a b, e (f.hom a) (g.hom b) = (c : ZMod (p ^ n)) * e a b) :
    ∃ B : (ModuleCat.extendScalars.{0, 0, v} (algebraMap ℤ_[p] ℚ_[p])).obj M →ₗ[ℚ_[p]]
        (ModuleCat.extendScalars.{0, 0, v} (algebraMap ℤ_[p] ℚ_[p])).obj M' →ₗ[ℚ_[p]] ℚ_[p],
      B.IsPerfPair ∧ ∀ v w,
        B (((ModuleCat.extendScalars.{0, 0, v} (algebraMap ℤ_[p] ℚ_[p])).map f).hom v)
          (((ModuleCat.extendScalars.{0, 0, v} (algebraMap ℤ_[p] ℚ_[p])).map g).hom w) =
          (c : ℚ_[p]) * B v w :=
  exists_isPerfPair_of_forall_zmodPow f.hom g.hom c K h

end Main

end Stacks.EtaleCohomology.LAdicPairing
