module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedBaseChangeCancel
public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedDeRhamSquareZeroLevelwise
public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedFormsUnitZero
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.CosimplicialDeRhamDoubleComplex
public import StacksFrontier.AlgebraicGeometry.Crystalline.TaylorHorizontal

/-!
# The level-wise algebra of the horizontality of a completed Taylor map

Let `σ, δ : D → B` be two ring maps (in the application the two coprojections `D(0) → D(1)` of the
cosimplicial envelope) with coordinate differences `ξ_i = σ(x_i) - δ(x_i)` in the divided power
ideal of `B`, `(M, ∇)` a `D`-module with a completed connection with coordinate operators `θ_i`
and composites `θ_K`, and suppose `δ` acts on `M` by the completed Taylor series
`δ(m) = ∑_K ξ^{[K]} · σ(θ_K m)`.  Then `δ` is horizontal.  This is the completed form of
`Crystalline.nabla_taylorSum_eq`, the step the source's proof of
[Stacks, Lemma 60.17.5, Tag 07L5] omits; in the proof of [Stacks, Proposition 60.21.3, Tag 07LG]
it is the horizontality of the coface `⦋0⦌ ⟶ ⦋1⦌, 0 ↦ 1` for the connections of the double
complex, proved as
`Crystalline.CosimplicialCompletedModule.baseChangeConnection_map_delta_of_taylor`.  This module
proves the algebra that proof runs at each level.

## The argument

Everything is local at the levels `pⁿ`.  At a fixed level only finitely many `θ_K m` survive
(topological quasi-nilpotence), all of them below one multi-index `L`; the Taylor series of `T m`
and of the `T(θ_i m)` and the coordinate expansions of the `∇ θ_K m` become finite sums over the
box `K ≤ L` and the support of `L`, and the identity is the finite one of
`Crystalline.taylorDeriv_eq_sum`, read in the level quotient.

## Main results

* `Crystalline.taylorDeriv_eq_sum_of_map` — the differentiated Taylor series is the
  coordinate-shifted Taylor series, for any `φ` additive and compatible with scalars.
* `Crystalline.taylorDeriv_toCompletedTensor_val` — the same identity read at one level of a
  completed tensor product.
* `Crystalline.completedFormsDPDerivation` — the universal differential of the completion,
  restricted to the uncompleted ring, is a divided power derivation (the divided power chain rule
  `Crystalline.completedFormsDifferential_of_dpow`).
* `Crystalline.sum_add_val_eq_of_level` — the bookkeeping of the horizontality of a Taylor map at
  one level.

The horizontality itself, for the cosimplicial base-change connections, is
`Crystalline.CosimplicialCompletedModule.baseChangeConnection_map_delta_of_taylor`.

## References

* [Stacks Project, Lemma 60.17.5, Tag 07L5](https://stacks.math.columbia.edu/tag/07L5)
* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
-/

@[expose] public noncomputable section

universe u v uA uI

open DividedPowers
open scoped TensorProduct

namespace Crystalline

section Level

variable (p : ℕ) {R : Type*} [CommRing R] {X : Type*} [AddCommGroup X] [Module R X]

/-- **An element of `pⁿ X` vanishes at the level `n` of the completion.** -/
theorem val_of_eq_zero_of_mem (n : ℕ) {x : X}
    (hx : x ∈ (pAdicIdeal (A := R) p) ^ n • (⊤ : Submodule R X)) :
    (AdicCompletion.of (pAdicIdeal (A := R) p) X x).val n = 0 := by
  rwa [AdicCompletion.of_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]

/-- **A completed connection is local at the levels** when the derivation kills the powers of
`p`: it carries `pⁿ M` into elements vanishing at the level `n`. -/
theorem CompletedConnection.val_eq_zero_of_mem_pPowSmul {D : Type*} [CommRing D] {Om : Type*}
    [AddCommGroup Om] [Module D Om] {d : D → Om} {M : Type*} [AddCommGroup M] [Module D M]
    (nab : CompletedConnection p D Om d M) (hd : ∀ k : ℕ, d ((p : D) ^ k) = 0) (n : ℕ) {y : M}
    (hy : y ∈ pPowSmul p D M n) : (nab y).val n = 0 := by
  obtain ⟨z, rfl⟩ := (mem_pPowSmul_iff p D M).mp hy
  rw [CompletedConnection.leibniz, hd, TensorProduct.tmul_zero, map_zero, add_zero]
  exact val_pow_smul_eq_zero p n _

/-- A completed connection whose derivation kills the powers of `p`, read at the level `n`,
depends only on its argument modulo `pⁿ`. -/
theorem CompletedConnection.val_congr_of_sub_mem {D : Type*} [CommRing D] {Om : Type*}
    [AddCommGroup Om] [Module D Om] {d : D → Om} {M : Type*} [AddCommGroup M] [Module D M]
    (nab : CompletedConnection p D Om d M) (hd : ∀ k : ℕ, d ((p : D) ^ k) = 0) (n : ℕ)
    {y y' : M} (h : y - y' ∈ pPowSmul p D M n) : (nab y).val n = (nab y').val n := by
  rw [show y = (y - y') + y' by abel, CompletedConnection.map_add, AdicCompletion.val_add_apply,
    nab.val_eq_zero_of_mem_pPowSmul p hd n h, zero_add]

end Level

/-! ### The differentiated Taylor series in a quotient -/

section Reindex

variable {B : Type*} [CommRing B] {Q : Type*} [AddCommGroup Q] {ι : Type uI} [DecidableEq ι]
  {Om : Type*} [AddCommGroup Om] [Module B Om] {N : Type*}

/-- The multi-indices `K ≤ L` with `1 ≤ K i` are exactly the shifts `K' + single i 1` of the
multi-indices `K' ≤ L` with `K' + single i 1 ≤ L`. -/
theorem filter_Iic_one_le_eq_map_add_single (L : ι →₀ ℕ) (i : ι) :
    (Finset.Iic L).filter (fun K ↦ 1 ≤ K i) =
      Finset.map ⟨fun K ↦ K + Finsupp.single i 1, add_left_injective _⟩
        ((Finset.Iic L).filter (fun K ↦ K + Finsupp.single i 1 ≤ L)) := by
  ext K
  simp only [Finset.mem_filter, Finset.mem_Iic, Finset.mem_map, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨hKL, hKi⟩
    have hK := finsupp_sub_single_add_single hKi
    exact ⟨K - Finsupp.single i 1, ⟨(finsupp_sub_single_le K i).trans hKL, by rwa [hK]⟩, hK⟩
  · rintro ⟨K', ⟨-, hK'⟩, rfl⟩
    exact ⟨hK', finsupp_one_le_add_single K' i⟩

/-- **The differentiated Taylor series is the coordinate-shifted Taylor series**, for a
function `φ : B → N → Om → Q` additive in its last variable and compatible with scalars, and a
family `y : (ι →₀ ℕ) → N` vanishing (under `φ`) outside the box `K ≤ L`.  This is the identity of
`Crystalline.taylorDeriv_eq_sum`, with the tensor product replaced by `φ` and exact vanishing by
vanishing under `φ`. -/
theorem taylorDeriv_eq_sum_of_map (φ : B → N → Om → Q)
    (hadd : ∀ b y, ∀ ω η : Om, φ b y (ω + η) = φ b y ω + φ b y η)
    (hzero : ∀ b y, φ b y 0 = 0)
    (hsmul : ∀ (b c : B) (y : N) (ω : Om), φ b y (c • ω) = φ (c * b) y ω)
    (c : (ι →₀ ℕ) → B) (dB : B → Om) (xi : ι → B)
    (hmono : ∀ K, dB (c K) = ∑ i ∈ K.support, c (K - Finsupp.single i 1) • dB (xi i))
    (y : (ι →₀ ℕ) → N) (L : ι →₀ ℕ)
    (hvan : ∀ K, ¬ K ≤ L → ∀ (b : B) (ω : Om), φ b (y K) ω = 0)
    (t : Finset ι) (ht : L.support ⊆ t) :
    ∑ K ∈ Finset.Iic L, φ 1 (y K) (dB (c K)) =
      ∑ i ∈ t, ∑ K ∈ Finset.Iic L, φ (c K) (y (K + Finsupp.single i 1)) (dB (xi i)) := by
  classical
  have hsum : ∀ (b : B) (z : N) (s : Finset ι) (g : ι → Om),
      φ b z (∑ i ∈ s, g i) = ∑ i ∈ s, φ b z (g i) := by
    intro b z s g
    induction s using Finset.induction_on with
    | empty => simp [hzero]
    | insert a s ha ih => rw [Finset.sum_insert ha, hadd, ih, Finset.sum_insert ha]
  have hterm : ∀ K ∈ Finset.Iic L, φ 1 (y K) (dB (c K)) =
      ∑ i ∈ t, if 1 ≤ K i then φ (c (K - Finsupp.single i 1)) (y K) (dB (xi i)) else 0 := by
    intro K hK
    have hsub : K.support ⊆ t := fun i hi ↦ ht (Finsupp.support_mono (Finset.mem_Iic.mp hK) hi)
    rw [← Finset.sum_subset hsub (fun i _ hi ↦ by
        rw [ite_eq_right (by rw [Finsupp.notMem_support_iff.mp hi]; omega)]),
      hmono K, hsum]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [ite_eq_left (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)), hsmul, mul_one]
  rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← Finset.sum_filter, (Finset.sum_subset
    (Finset.filter_subset (fun K ↦ K + Finsupp.single i 1 ≤ L) (Finset.Iic L))
    (fun K hK hKn ↦ by
      rw [Finset.mem_filter] at hKn
      exact hvan _ (fun h ↦ hKn ⟨hK, h⟩) _ _)).symm]
  rw [filter_Iic_one_le_eq_map_add_single, Finset.sum_map]
  refine Finset.sum_congr rfl fun K _ ↦ ?_
  simp only [Function.Embedding.coeFn_mk]
  rw [finsupp_add_single_sub_single K i]

/-- **The differentiated Taylor series of a completed tensor product, at the level `n`**: the
identity of `Crystalline.taylorDeriv_eq_sum_of_map` for `φ b y ω = ((b • y) ⊗ ω)` read at the level
`n`, the family `y` vanishing modulo `pⁿ` outside the box `K ≤ L`. -/
theorem taylorDeriv_toCompletedTensor_val (p : ℕ) {R : Type*} [CommRing R] {Y Ω : Type*}
    [AddCommGroup Y] [Module R Y] [AddCommGroup Ω] [Module R Ω] {ι : Type uI} [DecidableEq ι]
    (n : ℕ) (c : (ι →₀ ℕ) → R) (dB : R → Ω) (xi : ι → R)
    (hmono : ∀ K, dB (c K) = ∑ i ∈ K.support, c (K - Finsupp.single i 1) • dB (xi i))
    (y : (ι →₀ ℕ) → Y) (L : ι →₀ ℕ) (hvan : ∀ K, ¬ K ≤ L → y K ∈ pPowSmul p R Y n)
    (t : Finset ι) (ht : L.support ⊆ t) :
    (∑ K ∈ Finset.Iic L, toCompletedTensor p R Ω Y (y K ⊗ₜ[R] dB (c K))).val n =
      (∑ i ∈ t, ∑ K ∈ Finset.Iic L,
        toCompletedTensor p R Ω Y ((c K • y (K + Finsupp.single i 1)) ⊗ₜ[R] dB (xi i))).val n := by
  have h := taylorDeriv_eq_sum_of_map
    (fun (b : R) (z : Y) (ω : Ω) => (toCompletedTensor p R Ω Y ((b • z) ⊗ₜ[R] ω)).val n)
    (fun b z ω η => by simp only [TensorProduct.tmul_add, map_add, AdicCompletion.val_add_apply])
    (fun b z => by simp only [TensorProduct.tmul_zero, map_zero, AdicCompletion.val_zero_apply])
    (fun b c z ω => by simp only [← TensorProduct.smul_tmul, mul_smul])
    c dB xi hmono y L
    (fun K hK b ω => CompletedDeRham.toCompletedTensor_tmul_val_eq_zero_of_mem_pPowSmul p R Ω Y n
      ω (Submodule.smul_mem _ b (hvan K hK)))
    t ht
  simp only [one_smul] at h
  rw [AdicCompletion.val_sum_apply, h, AdicCompletion.val_sum_apply]
  exact Finset.sum_congr rfl fun i _ => (AdicCompletion.val_sum_apply _ _ n).symm

/-- **The bookkeeping of the horizontality of a Taylor map, at one level.**  If `A_K` is
`∑_i Pσ_{i,K}`, the sum of the `T_K` is `∑_i ∑_K Pξ_{i,K}` and `R_i` is
`∑_K Pσ_{i,K} + Pξ_{i,K}`, all
at the level `n`, then `∑_K (A_K + T_K)` and `∑_i R_i` agree at the level `n`. -/
theorem sum_add_val_eq_of_level {R : Type*} [CommRing R] {I : Ideal R} {N : Type*}
    [AddCommGroup N] [Module R N] {α : Type*} {ι : Type uI} (n : ℕ) (B : Finset α)
    (t : Finset ι) (A T : α → AdicCompletion I N) (Ps Px : ι → α → AdicCompletion I N)
    (Rt : ι → AdicCompletion I N) (hA : ∀ K, (A K).val n = (∑ i ∈ t, Ps i K).val n)
    (hT : (∑ K ∈ B, T K).val n = (∑ i ∈ t, ∑ K ∈ B, Px i K).val n)
    (hR : ∀ i, (Rt i).val n = (∑ K ∈ B, Ps i K + ∑ K ∈ B, Px i K).val n) :
    (∑ K ∈ B, (A K + T K)).val n = (∑ i ∈ t, Rt i).val n := by
  have key : ∀ X : AdicCompletion I N, X.val n = AdicCompletion.eval I N n X := fun _ => rfl
  simp only [key, map_sum, map_add] at hA hT hR ⊢
  rw [Finset.sum_add_distrib, hT, Finset.sum_congr rfl fun K _ => hA K,
    Finset.sum_congr rfl fun i _ => hR i, Finset.sum_add_distrib, Finset.sum_comm]

end Reindex

/-! ### The divided power chain rule for the completed differential -/

section ChainRule

variable (p : ℕ) (A : Type u) [CommRing A] {B : Type v} [CommRing B] [Algebra A B]
  {J : Ideal B} (hJ : DividedPowers J)

/-- **The divided power chain rule for the universal differential of the completion**, on the
image of the uncompleted ring: `d(γ_{n+1}(x)) = γ_n(x) d x`. -/
theorem completedFormsDifferential_of_dpow (x : J) (n : ℕ) :
    completedFormsDifferential p A hJ
        (AdicCompletion.of (pAdicIdeal (A := B) p) B (hJ.dpow (n + 1) x)) =
      hJ.dpow n x •
        completedFormsDifferential p A hJ (AdicCompletion.of (pAdicIdeal (A := B) p) B x) := by
  rw [completedFormsDifferential_of, completedFormsDifferential_of, ← map_smul]
  congr 1
  show (exteriorPower.oneEquiv B (dividedPowerDifferentials (A := A) hJ)).symm
      (dividedPowerDifferential (A := A) hJ (hJ.dpow (n + 1) x)) =
    hJ.dpow n x • (exteriorPower.oneEquiv B (dividedPowerDifferentials (A := A) hJ)).symm
      (dividedPowerDifferential (A := A) hJ x)
  rw [dividedPowerDifferential_dpow, map_smul]

/-- The scalar action of the completion of the ring on a completion restricts to the action of
the ring. -/
theorem adicCompletion_algebraMap_smul (r : B) (z : completedDividedPowerForms p A hJ 1) :
    algebraMap B (completedDividedPowerRing p (B := B)) r • z = r • z :=
  algebraMap_smul _ r z

/-- **The universal differential of the completion, restricted to the uncompleted ring, is a
divided power derivation.** -/
def completedFormsDPDerivation :
    DividedPowerDerivation A (DividedPowerRing.of B J hJ) (algebraMap A B)
      (completedDividedPowerForms p A hJ 1) where
  toDerivation := Derivation.mk'
    (AddMonoidHom.toIntLinearMap (AddMonoidHom.mk'
      (fun b => completedFormsDifferential p A hJ
        (algebraMap B (completedDividedPowerRing p (B := B)) b))
      (fun b c => by rw [map_add, completedFormsDifferential_add])))
    (fun b c => by
      change completedFormsDifferential p A hJ
          (algebraMap B (completedDividedPowerRing p (B := B)) (b * c)) =
        b • completedFormsDifferential p A hJ
            (algebraMap B (completedDividedPowerRing p (B := B)) c) +
          c • completedFormsDifferential p A hJ
            (algebraMap B (completedDividedPowerRing p (B := B)) b)
      rw [map_mul, completedFormsDifferential_mul, adicCompletion_algebraMap_smul,
        adicCompletion_algebraMap_smul])
  map_ringHom' a := by
    change completedFormsDifferential p A hJ
        (algebraMap B (completedDividedPowerRing p (B := B)) (algebraMap A B a)) = 0
    rw [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      completedFormsDifferential_of]
    change AdicCompletion.of _ _ ((exteriorPower.oneEquiv B
      (dividedPowerDifferentials (A := A) hJ)).symm
      ((dividedPowerDifferentialRelations (A := A) hJ).mkQ
        (KaehlerDifferential.D A B (algebraMap A B a)))) = 0
    rw [Derivation.map_algebraMap, map_zero, map_zero, map_zero]
  map_dpow' n hn x hx := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hn
    change completedFormsDifferential p A hJ
        (algebraMap B (completedDividedPowerRing p (B := B)) (hJ.dpow (0 + m + 1) x)) =
      hJ.dpow (0 + m + 1 - 1) x • completedFormsDifferential p A hJ
        (algebraMap B (completedDividedPowerRing p (B := B)) x)
    simp only [zero_add, Nat.add_sub_cancel]
    rw [AdicCompletion.algebraMap_apply, AdicCompletion.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply, RingHom.id_apply]
    exact completedFormsDifferential_of_dpow p A hJ ⟨x, hx⟩ m

/-- The divided power derivation `completedFormsDPDerivation` sends `b : B` to the universal
differential of the image of `b` in the `p`-adic completion. -/
theorem completedFormsDPDerivation_apply (b : B) :
    completedFormsDPDerivation p A hJ b =
      completedFormsDifferential p A hJ (AdicCompletion.of (pAdicIdeal (A := B) p) B b) := rfl

end ChainRule

end Crystalline

end
