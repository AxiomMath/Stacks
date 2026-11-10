module

public import StacksFrontier.RingTheory.Flat.AdicFiltrationNilpotent
public import StacksFrontier.RingTheory.Flat.MaximalIdealGradedPiece
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public noncomputable section

universe u v

/-!
# Flatness from the graded pieces of the adic filtration

`StacksFrontier/RingTheory/Flat/MaximalIdealGradedPiece.lean` reads the graded pieces of the
`𝔪`-adic filtration of a **flat** module: for representatives `aᵢ ∈ 𝔪ⁿ` of a `κ`-basis of
`𝔪ⁿ/𝔪ⁿ⁺¹`, a tuple `(mᵢ)` with `∑ aᵢ mᵢ ∈ 𝔪ⁿ⁺¹M` has every `mᵢ` in `𝔪M`
(`Stacks.Flatness.mem_smul_top_of_sum_smul_mem`).

This file proves the **converse**: that condition, for `n = 1, …, N` and one `N` with
`𝔪ᴺ⁺¹ = 0`, forces `M` to be flat.  That is the direction an existence argument needs — the
graded pieces are what a filtration argument produces, and flatness is what it has to conclude.

The route is [Stacks, Tag 0AS8] in the form `Module.flat_of_pow_eq_bot_of_exact`, whose
hypothesis is the exactness of `M ⊗_R 𝔪ⁿ⁺¹ → M ⊗_R 𝔪ⁿ → M/𝔪ⁿ⁺¹M`.

## Main results

* `Stacks.Flatness.exact_rTensor_gradedMulMap_of_mem_smul_top`: the graded condition gives
  exactness of `(𝔪 • 𝔪ⁿ) ⊗_R M → 𝔪ⁿ ⊗_R M → M/𝔪ⁿ⁺¹M`.
* `Stacks.Flatness.flat_of_pow_eq_bot_of_mem_smul_top`: **the criterion.** Over a Noetherian ring
  with `𝔪` maximal and `𝔪ᴺ⁺¹ = 0`, a module whose graded pieces satisfy the condition above for
  `n = 1, …, N` is flat.

## Implementation notes

Only the inclusion `ker ⊆ range` has to be proved; the other one is
`Stacks.Flatness.range_rTensor_le_ker_gradedMulMap`, which holds for every module and is the
half of `Stacks.Flatness.ker_gradedMulMap` that does not use flatness.

No map out of `(𝔪ⁿ/𝔪ⁿ⁺¹) ⊗_R M` is constructed for that inclusion, and no identification of a
quotient of a tensor product is needed.  Right exactness is used only in the form `rTensor_exact`
applied to `𝔪 • ⊤ → 𝔪ⁿ → 𝔪ⁿ/𝔪ⁿ⁺¹`: it says that the range to be reached is the kernel of
`𝔪ⁿ ⊗ M → (𝔪ⁿ/𝔪ⁿ⁺¹) ⊗ M`.  An element `z` of `𝔪ⁿ ⊗ M` is then compared with a combination
`∑ aᵢ ⊗ mᵢ` having the same image there — such a combination exists because
`Stacks.Flatness.piQuotEquivTensor` presents `(𝔪ⁿ/𝔪ⁿ⁺¹) ⊗ M` as `k` copies of `M/𝔪M` and
classes lift.  If `z` is killed by the multiplication map then so is the combination, so
`∑ aᵢ mᵢ ∈ 𝔪ⁿ⁺¹M`, so the graded condition puts every `mᵢ` in `𝔪M`, so the tuple is zero and
with it the image of `z`.

Both tensor orders occur: `Stacks.Flatness.gradedMulMap` has the ideal on the left, 0AS8 has the
module on the left.  The two are exchanged by `TensorProduct.comm` at the end, through
`Function.Exact.of_ladder_linearEquiv_of_exact`, and the first map is replaced along the
bijection `Stacks.Flatness.inclusionSmulTop` between `𝔪ⁿ⁺¹` and the submodule `𝔪 • ⊤` of `𝔪ⁿ`.

`M/𝔪M` is flat over `κ = R/𝔪` for free, `κ` being a field, so 0AS8's base-case hypothesis is
discharged here and does not appear.

## References

* [Stacks Project, Tag 0AS8](https://stacks.math.columbia.edu/tag/0AS8)
* [Stacks Project, Tag 0EJU](https://stacks.math.columbia.edu/tag/0EJU)
-/

open TensorProduct LinearMap

namespace Stacks.Flatness

variable {R : Type u} [CommRing R] (𝔪 : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]

/-! ### The unconditional half of the kernel computation -/

/-- The image of `(𝔪 • 𝔪ⁿ) ⊗ M` in `𝔪ⁿ ⊗ M` is killed by multiplication into `M/𝔪ⁿ⁺¹M`.  This is
the inclusion `range ≤ ker` of `Stacks.Flatness.ker_gradedMulMap`, which needs no flatness: an
element of `𝔪ⁿ⁺¹` times an element of `M` lies in `𝔪ⁿ⁺¹M`. -/
theorem range_rTensor_le_ker_gradedMulMap (n : ℕ) :
    LinearMap.range ((𝔪 • (⊤ : Submodule R ↥(𝔪 ^ n))).subtype.rTensor M) ≤
      LinearMap.ker (gradedMulMap 𝔪 M n) := by
  rw [LinearMap.range_le_ker_iff]
  refine TensorProduct.ext' fun w m => ?_
  have hw : ((w : ↥(𝔪 ^ n)) : R) ∈ 𝔪 ^ (n + 1) := (mem_smul_top_pow_iff 𝔪 n _).1 w.2
  change (𝔪 ^ (n + 1) • (⊤ : Submodule R M)).mkQ (((w : ↥(𝔪 ^ n)) : R) • m) = 0
  exact (Submodule.Quotient.mk_eq_zero _).2 (Submodule.smul_mem_smul hw Submodule.mem_top)

/-! ### `k` copies of `M/𝔪M`, as `(𝔪ⁿ/𝔪ⁿ⁺¹) ⊗ M` -/

/-- **`k` copies of `M/𝔪M` is `(𝔪ⁿ/𝔪ⁿ⁺¹) ⊗ M`**, for `e` an identification of `𝔪ⁿ/𝔪ⁿ⁺¹` with
`κᵏ`.  This is the part of `Stacks.Flatness.piEquivSmulTopOfGradedPieceEquiv` that does not use
flatness of `M`: the last step there, which identifies `(𝔪ⁿ/𝔪ⁿ⁺¹) ⊗ M` with the graded piece
`𝔪ⁿM/𝔪ⁿ⁺¹M`, is exactly what flatness buys and is omitted here. -/
def piQuotEquivTensor {k : ℕ} (n : ℕ)
    (e : (↥(𝔪 ^ n) ⧸ (𝔪 • (⊤ : Submodule R ↥(𝔪 ^ n)))) ≃ₗ[R] (Fin k → (R ⧸ 𝔪))) :
    (Fin k → (M ⧸ (𝔪 • (⊤ : Submodule R M)))) ≃ₗ[R]
      ((↥(𝔪 ^ n) ⧸ (𝔪 • (⊤ : Submodule R ↥(𝔪 ^ n)))) ⊗[R] M) :=
  (LinearEquiv.piCongrRight fun _ : Fin k =>
        (TensorProduct.tensorQuotEquivQuotSMul M 𝔪).symm).trans
    ((TensorProduct.piRight R R M fun _ : Fin k => (R ⧸ 𝔪)).symm.trans
      ((LinearEquiv.lTensor M e.symm).trans (TensorProduct.comm R M _)))

/-- The value of `Stacks.Flatness.piQuotEquivTensor` on a tuple of classes: it is the sum of the
`aᵢ ⊗ mᵢ` for the chosen representatives `aᵢ`. -/
theorem piQuotEquivTensor_apply {k : ℕ} (n : ℕ)
    (e : (↥(𝔪 ^ n) ⧸ (𝔪 • (⊤ : Submodule R ↥(𝔪 ^ n)))) ≃ₗ[R] (Fin k → (R ⧸ 𝔪)))
    (x : Fin k → ↥(𝔪 ^ n))
    (hx : ∀ i, e.symm (Pi.single i (1 : R ⧸ 𝔪)) = Submodule.Quotient.mk (x i))
    (m : Fin k → M) :
    piQuotEquivTensor 𝔪 M n e (fun i => Submodule.Quotient.mk (m i)) =
      ∑ i, (Submodule.Quotient.mk (x i) :
        ↥(𝔪 ^ n) ⧸ (𝔪 • (⊤ : Submodule R ↥(𝔪 ^ n)))) ⊗ₜ[R] m i := by
  classical
  have hstep1 : (fun i : Fin k =>
      (TensorProduct.tensorQuotEquivQuotSMul M 𝔪).symm (Submodule.Quotient.mk (m i))) =
      fun i : Fin k => m i ⊗ₜ[R] (1 : R ⧸ 𝔪) :=
    funext fun i => TensorProduct.tensorQuotEquivQuotSMul_symm_mk 𝔪 (m i)
  have hstep2 : (TensorProduct.piRight R R M fun _ : Fin k => (R ⧸ 𝔪)).symm
        (fun i : Fin k => m i ⊗ₜ[R] (1 : R ⧸ 𝔪)) =
      ∑ i : Fin k, m i ⊗ₜ[R] Pi.single i (1 : R ⧸ 𝔪) := by
    have hv : (fun i : Fin k => m i ⊗ₜ[R] (1 : R ⧸ 𝔪)) =
        ∑ i : Fin k, Pi.single i (m i ⊗ₜ[R] (1 : R ⧸ 𝔪)) :=
      (Finset.univ_sum_single _).symm
    rw [hv, map_sum]
    exact Finset.sum_congr rfl fun i _ =>
      TensorProduct.piRight_symm_single R R M (fun _ : Fin k => (R ⧸ 𝔪)) (m i) i _
  change (TensorProduct.comm R M _) ((LinearEquiv.lTensor M e.symm)
    ((TensorProduct.piRight R R M fun _ : Fin k => (R ⧸ 𝔪)).symm
      (fun i => (TensorProduct.tensorQuotEquivQuotSMul M 𝔪).symm
        (Submodule.Quotient.mk (m i))))) = _
  rw [hstep1, hstep2, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  change (TensorProduct.comm R M _) (m i ⊗ₜ[R] e.symm (Pi.single i (1 : R ⧸ 𝔪))) = _
  rw [hx i]
  rfl

/-! ### The exactness 0AS8 consumes -/

/-- **The graded condition gives the exactness of `(𝔪 • 𝔪ⁿ) ⊗ M → 𝔪ⁿ ⊗ M → M/𝔪ⁿ⁺¹M`.**

For `ker ⊆ range`: by right exactness the range is the kernel of `𝔪ⁿ ⊗ M → (𝔪ⁿ/𝔪ⁿ⁺¹) ⊗ M`, and
every element `z` of `𝔪ⁿ ⊗ M` has the same image there as a combination `∑ aᵢ ⊗ mᵢ` of the chosen
representatives, because `Stacks.Flatness.piQuotEquivTensor` presents the target as `k` copies of
`M/𝔪M` and classes lift.  If `z` is killed by the multiplication map then so is the combination,
so `∑ aᵢ mᵢ ∈ 𝔪ⁿ⁺¹M`, so the hypothesis puts every `mᵢ` in `𝔪M`, so the tuple is zero and so is
the image of `z`. -/
theorem exact_rTensor_gradedMulMap_of_mem_smul_top {k : ℕ} (n : ℕ)
    (e : (↥(𝔪 ^ n) ⧸ (𝔪 • (⊤ : Submodule R ↥(𝔪 ^ n)))) ≃ₗ[R] (Fin k → (R ⧸ 𝔪)))
    (x : Fin k → ↥(𝔪 ^ n))
    (hx : ∀ i, e.symm (Pi.single i (1 : R ⧸ 𝔪)) = Submodule.Quotient.mk (x i))
    (hgr : ∀ m : Fin k → M, (∑ i, (x i : R) • m i) ∈ 𝔪 ^ (n + 1) • (⊤ : Submodule R M) →
      ∀ i, m i ∈ 𝔪 • (⊤ : Submodule R M)) :
    Function.Exact ((𝔪 • (⊤ : Submodule R ↥(𝔪 ^ n))).subtype.rTensor M)
      (gradedMulMap 𝔪 M n) := by
  classical
  have hRT : Function.Exact ((𝔪 • (⊤ : Submodule R ↥(𝔪 ^ n))).subtype.rTensor M)
      ((𝔪 • (⊤ : Submodule R ↥(𝔪 ^ n))).mkQ.rTensor M) :=
    rTensor_exact M (LinearMap.exact_subtype_mkQ _) (Submodule.mkQ_surjective _)
  rw [LinearMap.exact_iff]
  refine le_antisymm ?_ (range_rTensor_le_ker_gradedMulMap 𝔪 M n)
  intro z hz
  have hz' : gradedMulMap 𝔪 M n z = 0 := hz
  -- a tuple of classes whose combination has the same image in `(𝔪ⁿ/𝔪ⁿ⁺¹) ⊗ M`
  obtain ⟨v, hv⟩ := (piQuotEquivTensor 𝔪 M n e).surjective
    (((𝔪 • (⊤ : Submodule R ↥(𝔪 ^ n))).mkQ.rTensor M) z)
  choose m hm using fun i : Fin k =>
    Submodule.Quotient.mk_surjective (𝔪 • (⊤ : Submodule R M)) (v i)
  have hveq : v = fun i => Submodule.Quotient.mk (m i) := funext fun i => (hm i).symm
  have hv2 : (∑ i, (Submodule.Quotient.mk (x i) :
        ↥(𝔪 ^ n) ⧸ (𝔪 • (⊤ : Submodule R ↥(𝔪 ^ n)))) ⊗ₜ[R] m i) =
      ((𝔪 • (⊤ : Submodule R ↥(𝔪 ^ n))).mkQ.rTensor M) z := by
    rw [← piQuotEquivTensor_apply 𝔪 M n e x hx m, ← hveq]
    exact hv
  -- so `z` and the combination differ by an element of the range
  have hdiff : z - (∑ i, (x i : ↥(𝔪 ^ n)) ⊗ₜ[R] m i) ∈
      LinearMap.range ((𝔪 • (⊤ : Submodule R ↥(𝔪 ^ n))).subtype.rTensor M) := by
    refine (hRT _).1 ?_
    rw [map_sub, sub_eq_zero, map_sum]
    exact hv2.symm
  -- the combination is killed by the multiplication map too
  have hcomb : gradedMulMap 𝔪 M n (∑ i, (x i : ↥(𝔪 ^ n)) ⊗ₜ[R] m i) = 0 := by
    have h1 : gradedMulMap 𝔪 M n (z - ∑ i, (x i : ↥(𝔪 ^ n)) ⊗ₜ[R] m i) = 0 :=
      range_rTensor_le_ker_gradedMulMap 𝔪 M n hdiff
    rw [map_sub, hz', zero_sub, neg_eq_zero] at h1
    exact h1
  have hmem : (∑ i, (x i : R) • m i) ∈ 𝔪 ^ (n + 1) • (⊤ : Submodule R M) := by
    have hsum : ((𝔪 ^ (n + 1) • (⊤ : Submodule R M)).mkQ) (∑ i, (x i : R) • m i) =
        gradedMulMap 𝔪 M n (∑ i, (x i : ↥(𝔪 ^ n)) ⊗ₜ[R] m i) := by
      rw [map_sum, map_sum]
      exact Finset.sum_congr rfl fun i _ => rfl
    exact (Submodule.Quotient.mk_eq_zero _).1 (hsum.trans hcomb)
  -- hence the tuple is zero, hence so is the image of `z`
  have hvzero : v = 0 :=
    funext fun i => (hm i).symm.trans
      ((Submodule.Quotient.mk_eq_zero _).2 (hgr m hmem i))
  exact (hRT z).1 (by rw [← hv, hvzero, map_zero])

/-- **Flatness from the graded pieces of the adic filtration.**  Let `R` be a Noetherian
commutative ring, `𝔪 ⊆ R` a maximal ideal with `𝔪ᴺ⁺¹ = 0`, and `M` an `R`-module.  Suppose that
for every `n` with `1 ≤ n ≤ N`, every identification `e` of `𝔪ⁿ/𝔪ⁿ⁺¹` with `κᵏ` and every tuple
of representatives `aᵢ ∈ 𝔪ⁿ` of its basis, a tuple `(mᵢ)` in `M` with `∑ aᵢ mᵢ ∈ 𝔪ⁿ⁺¹M` has
every `mᵢ` in `𝔪M`.  Then `M` is flat over `R`.

This is the converse of `Stacks.Flatness.mem_smul_top_of_sum_smul_mem`, and it is the shape a
filtration argument over an Artinian local base produces: the graded pieces of the filtration are
what such an argument computes, and `𝔪ᴺ⁺¹ = 0` is the nilpotence of the maximal ideal. -/
@[ega "0 10.1.3" "(i)"]
theorem flat_of_pow_eq_bot_of_mem_smul_top [IsNoetherianRing R] [𝔪.IsMaximal] (N : ℕ)
    (hN : 𝔪 ^ (N + 1) = ⊥)
    (hgr : ∀ n, 1 ≤ n → n ≤ N →
      ∀ {k : ℕ} (e : (↥(𝔪 ^ n) ⧸ (𝔪 • (⊤ : Submodule R ↥(𝔪 ^ n)))) ≃ₗ[R] (Fin k → (R ⧸ 𝔪)))
        (x : Fin k → ↥(𝔪 ^ n)),
        (∀ i, e.symm (Pi.single i (1 : R ⧸ 𝔪)) = Submodule.Quotient.mk (x i)) →
        ∀ m : Fin k → M, (∑ i, (x i : R) • m i) ∈ 𝔪 ^ (n + 1) • (⊤ : Submodule R M) →
          ∀ i, m i ∈ 𝔪 • (⊤ : Submodule R M)) :
    Module.Flat R M := by
  classical
  let : Field (R ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  refine Module.flat_of_pow_eq_bot_of_exact 𝔪 M N hN inferInstance fun n hn1 hnN => ?_
  -- a basis of `𝔪ⁿ/𝔪ⁿ⁺¹` and representatives of it
  obtain ⟨k, ⟨e⟩⟩ := exists_pi_linearEquiv_gradedPiece 𝔪 n
  choose x hx using fun i : Fin k =>
    Submodule.Quotient.mk_surjective (𝔪 • (⊤ : Submodule R ↥(𝔪 ^ n)))
      (e.symm (Pi.single i (1 : R ⧸ 𝔪)))
  have hxs : ∀ i, e.symm (Pi.single i (1 : R ⧸ 𝔪)) = Submodule.Quotient.mk (x i) :=
    fun i => (hx i).symm
  have hex := exact_rTensor_gradedMulMap_of_mem_smul_top 𝔪 M n e x hxs
    (hgr n hn1 hnN e x hxs)
  -- replace `𝔪 • ⊤` by `𝔪ⁿ⁺¹`, the two being the same submodule of `𝔪ⁿ`
  have hsurj : Function.Surjective ((inclusionSmulTop 𝔪 n).rTensor M) :=
    LinearMap.rTensor_surjective M fun w =>
      ⟨⟨((w : ↥(𝔪 ^ n)) : R), (mem_smul_top_pow_iff 𝔪 n _).1 w.2⟩,
        Subtype.ext (Subtype.ext rfl)⟩
  have hcomp : ((𝔪 • (⊤ : Submodule R ↥(𝔪 ^ n))).subtype.rTensor M) ∘ₗ
      ((inclusionSmulTop 𝔪 n).rTensor M) =
      (Submodule.inclusion
        (Ideal.pow_le_pow_right n.le_succ : 𝔪 ^ (n + 1) ≤ 𝔪 ^ n)).rTensor M :=
    TensorProduct.ext' fun _ _ => rfl
  have hex2 : Function.Exact
      ((Submodule.inclusion
        (Ideal.pow_le_pow_right n.le_succ : 𝔪 ^ (n + 1) ≤ 𝔪 ^ n)).rTensor M)
      (gradedMulMap 𝔪 M n) := by
    rw [LinearMap.exact_iff, ← hcomp, LinearMap.range_comp, LinearMap.range_eq_top.mpr hsurj,
      Submodule.map_top]
    exact hex.linearMap_ker_eq
  -- and exchange the two tensor factors, 0AS8 having the module on the left
  refine Function.Exact.of_ladder_linearEquiv_of_exact
    (e₁ := TensorProduct.comm R ↥(𝔪 ^ (n + 1)) M) (e₂ := TensorProduct.comm R ↥(𝔪 ^ n) M)
    (e₃ := LinearEquiv.refl R _) ?_ ?_ hex2
  · exact TensorProduct.ext' fun _ _ => rfl
  · exact TensorProduct.ext' fun _ _ => rfl

/-! ### The filtration ladder -/

/-- **The ladder.**  Let `K` be a family of submodules of `M` with `K (N+1) = 0`, with
`𝔪ⁿM ≤ K n` for every `n`, and with each `K n` contained in `𝔪ⁿM + K (n+1)`.  If `𝔪ᴺ⁺¹ = 0`
then `K n = 𝔪ⁿM` for every `n ≤ N + 1`.

The induction runs downwards from `K (N+1) = 0 = 𝔪ᴺ⁺¹M`: once `K (n+1)` is known to be
`𝔪ⁿ⁺¹M`, the containment `K n ≤ 𝔪ⁿM + K (n+1)` has right-hand side `𝔪ⁿM`, and the reverse
containment is the hypothesis.

This is the inductive step of [Stacks, Tag 0E3X]'s "reading the references given above
backwards (and using induction)": the `K n` there are the sections of the ideal sheaves
`𝔪ⁿ𝒪_U` read on an affine open downstairs, the hypothesis `hsup` is what the graded pieces of
the filtration supply, and the conclusion identifies them with the powers of `𝔪` times the
sections. -/
theorem eq_pow_smul_top_of_le_sup (K : ℕ → Submodule R M) (N : ℕ) (hN : 𝔪 ^ (N + 1) = ⊥)
    (hKbot : K (N + 1) = ⊥)
    (hle : ∀ n, 𝔪 ^ n • (⊤ : Submodule R M) ≤ K n)
    (hsup : ∀ n, K n ≤ 𝔪 ^ n • (⊤ : Submodule R M) ⊔ K (n + 1)) :
    ∀ n, n ≤ N + 1 → K n = 𝔪 ^ n • (⊤ : Submodule R M) := by
  have key : ∀ j n, n + j = N + 1 → K n = 𝔪 ^ n • (⊤ : Submodule R M) := by
    intro j
    induction j with
    | zero =>
      intro n hn
      rw [Nat.add_zero] at hn
      subst hn
      rw [hKbot, hN, Submodule.bot_smul]
    | succ j ih =>
      intro n hn
      have hK1 : K (n + 1) = 𝔪 ^ (n + 1) • (⊤ : Submodule R M) := ih (n + 1) (by omega)
      refine le_antisymm (le_trans (hsup n) ?_) (hle n)
      rw [hK1]
      exact sup_le le_rfl (Submodule.smul_mono (Ideal.pow_le_pow_right n.le_succ) le_rfl)
  exact fun n hn => key (N + 1 - n) n (by omega)

/-- **Flatness, and the first step of the filtration, from the ladder and the graded condition.**

This is the form in which a filtration argument over an Artinian local base consumes the two
results above at once.  The family `K` is the filtration the argument produces — in
[Stacks, Tag 0E3X] the sections over an affine open of the ideal sheaves `𝔪ⁿ𝒪_U` pushed
downstairs — and both hypotheses about it are stated with `K` alone, so a consumer never has to
name `𝔪ⁿM`: the ladder identifies the two, and the graded condition is then exactly the
hypothesis of `Stacks.Flatness.flat_of_pow_eq_bot_of_mem_smul_top`.

The conclusion `K 1 = 𝔪M` is the "reduction" half of the source's *"`𝒪_V` is flat over `A` with
reduction `𝒪_V/𝔪_A𝒪_V = 𝒪_Y`"*, and `Module.Flat R M` is the flatness half. -/
theorem flat_and_eq_smul_top_of_ladder [IsNoetherianRing R] [𝔪.IsMaximal]
    (K : ℕ → Submodule R M) (N : ℕ) (hN : 𝔪 ^ (N + 1) = ⊥) (hKbot : K (N + 1) = ⊥)
    (hle : ∀ n, 𝔪 ^ n • (⊤ : Submodule R M) ≤ K n)
    (hsup : ∀ n, K n ≤ 𝔪 ^ n • (⊤ : Submodule R M) ⊔ K (n + 1))
    (hgr : ∀ n, 1 ≤ n → n ≤ N →
      ∀ {k : ℕ} (e : (↥(𝔪 ^ n) ⧸ (𝔪 • (⊤ : Submodule R ↥(𝔪 ^ n)))) ≃ₗ[R] (Fin k → (R ⧸ 𝔪)))
        (x : Fin k → ↥(𝔪 ^ n)),
        (∀ i, e.symm (Pi.single i (1 : R ⧸ 𝔪)) = Submodule.Quotient.mk (x i)) →
        ∀ m : Fin k → M, (∑ i, (x i : R) • m i) ∈ K (n + 1) → ∀ i, m i ∈ K 1) :
    Module.Flat R M ∧ K 1 = 𝔪 • (⊤ : Submodule R M) := by
  have hladder := eq_pow_smul_top_of_le_sup 𝔪 M K N hN hKbot hle hsup
  have hK1 : K 1 = 𝔪 • (⊤ : Submodule R M) := by
    rw [hladder 1 (by omega), pow_one]
  refine ⟨flat_of_pow_eq_bot_of_mem_smul_top 𝔪 M N hN ?_, hK1⟩
  intro n hn1 hnN k e x hx m hm
  rw [← hK1]
  refine hgr n hn1 hnN e x hx m ?_
  rw [hladder (n + 1) (by omega)]
  exact hm

end Stacks.Flatness

end
