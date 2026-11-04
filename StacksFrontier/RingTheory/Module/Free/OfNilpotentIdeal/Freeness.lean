module

public import StacksFrontier.RingTheory.Module.Free.OfNilpotentIdeal.MultiplicationMaps
public import StacksFrontier.RingTheory.Module.Free.OfNilpotentIdeal.TorVanishing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Freeness modulo a nilpotent ideal: linear independence and freeness

Injectivity of the multiplication maps `I^k ⊗_R M → M`, linear independence of the
reductions of `x` modulo `I^k M` by induction on `k`, and the conclusion that `M` is free
on `x` when `I` is nilpotent (Stacks 051H).
-/

@[expose] public section

namespace Stacks.FreeOfNilpotentIdeal

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- **(B) Dimension-shift comparison.**
Given the change-of-rings vanishing (C) for the canonical `R`-free presentation of the cokernel
`N := coker ι = I^n / I^{n+1}`, the tensored inclusion `rTensor M ι` is injective.

*Proof.* `Tor₁^R(N, M)` is independent of the chosen presentation of `N` (comparison theorem for
projective/free resolutions). Computing it against `0 → I^{n+1} → I^n → N → 0` gives
`ker (rTensor M ι)`; computing it against the `R`-free presentation `0 → ker p → P → N → 0`
gives `ker (rTensor M (ker p).subtype) = 0` by (C). The `R`-free `P` is projective, so a
chain map lifting
`id_N` (`s : P → I^n`, `t : ker p → I^{n+1}`) exists and induces, via right-exactness of `· ⊗ M`
(`rTensor_exact`) and `LinearMap.rTensor_comp`, an injection `ker (rTensor M ι) ↪
ker (rTensor M (ker p).subtype) = 0`. Hence `rTensor M ι` is injective. -/
theorem rTensor_pow_inclusion_injective
    {A : Type*} (I : Ideal R)
    (b : Module.Basis A (R ⧸ I) (M ⧸ smul (M := M) I))
    (hTor : Function.Injective (torMul (M := M) I))
    (n : ℕ) :
    Function.Injective
      (LinearMap.rTensor M
        (Submodule.inclusion
          (show (I ^ (n + 1) : Ideal R) ≤ I ^ n from Ideal.pow_le_pow_right (by omega)))) := by
  -- DIMENSION-SHIFT (B): set N := coker ι (an R/I-module), take the canonical R-free presentation
  -- p : (N →₀ R) ↠ N, apply (C) `tor_one_quot_eq_zero` to get `rTensor M (ker p).subtype`
  -- injective,
  -- and transfer to ι via the abstract comparison lemma `rTensor_inj_of_comparison` (projective
  -- lift
  -- s : P → I^n with q ∘ s = p; corestricted t : ker p → I^{n+1}).
  classical
  set hle : (I ^ (n + 1) : Ideal R) ≤ I ^ n := Ideal.pow_le_pow_right (by omega) with hle_def
  set ι : (I ^ (n + 1) : Ideal R) →ₗ[R] (I ^ n : Ideal R) := Submodule.inclusion hle with hι_def
  have hι_inj : Function.Injective ι := Submodule.inclusion_injective hle
  let Nn := ((I ^ n : Ideal R)) ⧸ (LinearMap.range ι)
  let q : (I ^ n : Ideal R) →ₗ[R] Nn := (LinearMap.range ι).mkQ
  have hq_surj : Function.Surjective q := Submodule.mkQ_surjective _
  have hιq : Function.Exact ι q := by
    rw [LinearMap.exact_iff]
    show LinearMap.ker (LinearMap.range ι).mkQ = LinearMap.range ι
    rw [Submodule.ker_mkQ]
  have hN : I • (⊤ : Submodule R Nn) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro y hy
    refine Submodule.smul_induction_on hy ?_ ?_
    · intro a ha z _
      obtain ⟨w, rfl⟩ := hq_surj z
      rw [← map_smul, ← LinearMap.mem_ker, hιq.linearMap_ker_eq]
      have hmem : (a : R) * (w : R) ∈ (I ^ (n + 1) : Ideal R) := by
        rw [pow_succ, mul_comm a]; exact Ideal.mul_mem_mul w.property ha
      refine ⟨⟨a * w.val, hmem⟩, ?_⟩
      apply Subtype.ext
      simp [hι_def, Submodule.inclusion]
    · intro y1 y2 h1 h2
      rw [h1, h2, add_zero]
  let P0 := Nn →₀ R
  let p : P0 →ₗ[R] Nn := Finsupp.linearCombination R id
  have hp_surj : Function.Surjective p := by
    intro z
    refine ⟨Finsupp.single z 1, ?_⟩
    show (Finsupp.linearCombination R (id : Nn → Nn)) (Finsupp.single z 1) = z
    rw [Finsupp.linearCombination_single, one_smul, id]
  have hκp : Function.Exact (LinearMap.ker p).subtype p := LinearMap.exact_subtype_ker_map p
  have hκinj : Function.Injective (LinearMap.rTensor M (LinearMap.ker p).subtype) :=
    tor_one_quot_eq_zero I b hTor hN p hp_surj
  obtain ⟨s, hs⟩ := Module.projective_lifting_property q p hq_surj
  exact rTensor_inj_of_comparison (LinearMap.ker p).subtype p ι q hκp hp_surj hιq hι_inj s hs hκinj

/-- **(MulInj) — the multiplication maps `μ^{(n)} : I^n ⊗_R M → M` are injective, for all `n`.**
This is the genuine homological core of Stacks 051H, in the cleanest possible form. It holds
because:
- (H1) `hTor` says `μ^{(1)} = torMul I : I ⊗_R M → M` is injective, i.e. `Tor₁^R(R/I, M) = 0`;
- (H2) `M/IM` is *free* (basis `b`) hence *flat* over `R/I`.

*Mathematical proof (no nilpotency needed).* By induction on `n`. The case `n = 0` is
the iso `⊤ ⊗_R M ≅ M`.
For the step, the inclusion `ι : I^{n+1} ↪ I^n` induces `u := rTensor M ι : I^{n+1} ⊗ M → I^n ⊗ M`
with `μ^{(n)} ∘ u = μ^{(n+1)}` (generator check). If `μ^{(n+1)}(v) = 0` then `μ^{(n)}(u v) = 0`, so
by the inductive hypothesis `u v = 0`; and `u` is injective (`rTensor_pow_inclusion_injective`), so
`v = 0`.

This crucially differs from the REFUTED Strategy-B lemma (which asked `Tor₁^R(R/I, M/I^kM) = 0`,
where the second argument `M/I^kM` violates (H1)): here the second `Tor` argument is always the
*original* `M`, on which (H1)+(H2) hold. -/
theorem mulPow_injective
    {A : Type*} (I : Ideal R)
    (b : Module.Basis A (R ⧸ I) (M ⧸ smul (M := M) I))
    (hTor : Function.Injective (torMul (M := M) I))
    (n : ℕ) :
    Function.Injective (mulPow (M := M) I n) := by
  induction n with
  | zero =>
    -- `mulPow I 0` is injective: carrier ideal `I^0 = ⊤`, left inverse `m ↦ ⟨1,_⟩ ⊗ m`.
    have htop : (I ^ 0 : Ideal R) = ⊤ := by rw [pow_zero, Ideal.one_eq_top]
    let g : M →ₗ[R] TensorProduct R (I ^ 0 : Ideal R) M :=
      { toFun := fun m => TensorProduct.tmul R ⟨1, by rw [htop]; trivial⟩ m
        map_add' := by intro m m'; rw [TensorProduct.tmul_add]
        map_smul' := by intro c m; simp [TensorProduct.tmul_smul] }
    have hli : Function.LeftInverse g (mulPow (M := M) I 0) := by
      intro u
      induction u using TensorProduct.induction_on with
      | zero => simp
      | tmul a m =>
          show g (mulPow (M := M) I 0 (TensorProduct.tmul R a m)) = TensorProduct.tmul R a m
          rw [mulPow_tmul, map_smul]
          show (a : R) • TensorProduct.tmul R (⟨1, _⟩ : (I ^ 0 : Ideal R)) m
              = TensorProduct.tmul R a m
          rw [TensorProduct.smul_tmul']
          congr 1
          apply Subtype.ext
          simp
      | add y z hy hz => rw [map_add, map_add, hy, hz]
    exact hli.injective
  | succ n ih =>
    -- `μ^{(n)} ∘ u = μ^{(n+1)}` where `u = rTensor M (ι : I^{n+1} ↪ I^n)`; reduce to `u`
    -- injective.
    set ι : (I ^ (n + 1) : Ideal R) →ₗ[R] (I ^ n : Ideal R) :=
      Submodule.inclusion
        (show (I ^ (n + 1) : Ideal R) ≤ I ^ n from Ideal.pow_le_pow_right (by omega)) with hι
    set u := LinearMap.rTensor M ι with hu
    have hfact : (mulPow (M := M) I n).comp u = mulPow (M := M) I (n + 1) := by
      apply TensorProduct.ext'
      intro a m
      simp only [LinearMap.comp_apply, hu, LinearMap.rTensor_tmul, mulPow_tmul, hι]
      rfl
    have hu_inj : Function.Injective u := rTensor_pow_inclusion_injective I b hTor n
    intro v w hvw
    apply hu_inj
    apply ih
    have h : ∀ v, mulPow (M := M) I n (u v) = mulPow (M := M) I (n + 1) v := fun v => by
      rw [← LinearMap.comp_apply, hfact]
    rw [h, h, hvw]

/-- **(★′)** — the *exact-kernel* version, now an immediate corollary of `mulPow_injective`:
if `μ^{(k)}(v) = 0` then `v = 0` (injectivity), hence `coordProj I b k v = 0`. -/
theorem ker_mulPow_le_ker_coordProj_zero
    {A : Type*} (I : Ideal R)
    (b : Module.Basis A (R ⧸ I) (M ⧸ smul (M := M) I))
    (hTor : Function.Injective (torMul (M := M) I))
    (k : ℕ)
    (v : TensorProduct R (I ^ k : Ideal R) M)
    (hv : mulPow (M := M) I k v = 0) :
    coordProj I b k v = 0 := by
  -- `mulPow I k` is injective (`mulPow_injective`), so `μ^{(k)}(v) = 0 = μ^{(k)}(0)` forces `v =
  -- 0`.
  have hvzero : v = 0 := mulPow_injective I b hTor k (by rw [hv, map_zero])
  rw [hvzero, map_zero]

/-- Every element of `ker μ^{(k)}` lies in `ker p_k`: an element of `I^k ⊗ M` killed by the
multiplication map has vanishing coordinate projection. -/
theorem ker_mulPow_le_ker_coordProj
    {A : Type*} (I : Ideal R)
    (b : Module.Basis A (R ⧸ I) (M ⧸ smul (M := M) I))
    (hTor : Function.Injective (torMul (M := M) I))
    (k : ℕ)
    (u : TensorProduct R (I ^ k : Ideal R) M)
    (hu : mulPow (M := M) I k u ∈ I ^ (k + 1) • (⊤ : Submodule R M)) :
    coordProj I b k u = 0 := by
  -- Reduce (★) to (★′): subtract a representative `w` of `μ^{(k)}(u) ∈ I^{k+1}M` whose coordinate
  -- projection vanishes (each subtracted simple tensor has first factor in `I^{k+1}`, hence is
  -- killed by `coordProj`). Then `μ^{(k)}(u - w) = 0`, so (★′) gives `coordProj (u - w) = 0`,
  -- and `coordProj u = coordProj w + coordProj (u - w) = 0`.
  have hle : (I ^ (k + 1) : Ideal R) ≤ I ^ k := Ideal.pow_le_pow_right (by omega)
  have key : ∃ w : TensorProduct R (I ^ k : Ideal R) M,
      mulPow (M := M) I k w = mulPow (M := M) I k u ∧ coordProj I b k w = 0 := by
    refine Submodule.smul_induction_on hu ?_ ?_
    · intro c hc n _
      refine ⟨TensorProduct.tmul R ⟨c, hle hc⟩ n, ?_, ?_⟩
      · rw [mulPow_tmul]
      · exact coordProj_tmul_eq_zero_of_mem I b k ⟨c, hle hc⟩ hc n
    · rintro y₁ y₂ ⟨w₁, hw1, hwc1⟩ ⟨w₂, hw2, hwc2⟩
      exact ⟨w₁ + w₂, by rw [map_add, hw1, hw2], by rw [map_add, hwc1, hwc2, add_zero]⟩
  obtain ⟨w, hw1, hwc⟩ := key
  have hzero : mulPow (M := M) I k (u - w) = 0 := by rw [map_sub, hw1, sub_self]
  have hcoord := ker_mulPow_le_ker_coordProj_zero I b hTor k (u - w) hzero
  rw [map_sub, hwc, sub_zero] at hcoord
  exact hcoord

/-- **Core Obligation of Stacks 051H, descent form (the genuine homological leaf).**
Given the basis `b` of `M/IM` over `R/I`, `hTor` (injectivity of `I ⊗_R M → M`, i.e.
`Tor₁(R/I,M)=0`), and the level-`k` linear-independence `ih`, the following *descent* holds:
if `f : A →₀ R` has all coefficients in `I^k` and `∑ f_α x_α ∈ I^{k+1}M`, then in fact all
coefficients lie in `I^{k+1}`.

This is exactly the content of the associated-graded isomorphism
`θ_k : (I^k/I^{k+1}) ⊗_{R/I} (M/IM) ≅ I^kM/I^{k+1}M` being injective (Stacks 00MK), expressed
elementwise via the basis `b`: writing `ζ = ∑ f̄_α ⊗ b_α`, the hypothesis `∑ f_α x_α ∈ I^{k+1}M`
says `θ_k(ζ) = 0`, injectivity gives `ζ = 0`, and freeness of `M/IM` on `(b_α)` forces each
`f̄_α = 0` in `I^k/I^{k+1}`, i.e. `f_α ∈ I^{k+1}`.

*Proof architecture.* The statement reduces to **(★′)** `ker μ^{(k)} ⊆ ker p_k`, where
`μ^{(k)} : I^k⊗M→M` and `p_k : I^k⊗M ↠ (I^k/I^{k+1})⊗_{R/I}(M/IM)`, proved by induction on
`k`. The base `k=1` is `hTor`, applied to `s ∈ I⊗M`; the step lifts `u` along the surjection
`ν : I⊗(I^{k-1}⊗M)→I^k⊗M`, applies `hTor` to kill `(id_I⊗μ^{(k-1)})(U)=0`, and uses the
factorization `p_{k-1}=p̄_{k-1}∘μ^{(k-1)}`, which is well-defined precisely because of
(★′)_{k-1}. Note that `hTor` is used only at the `I`-level, once per induction level, and no
per-`k` Tor vanishing is asserted; those are false without nilpotency. -/
theorem coeff_mem_pow_succ_of_mem_pow
    {A : Type*} (x : A → M) (I : Ideal R)
    (b : Module.Basis A (R ⧸ I) (M ⧸ smul (M := M) I))
    (hb : ∀ α, b α = reduction I (x α))
    (hTor : Function.Injective (torMul (M := M) I))
    (k : ℕ)
    (f : A →₀ R) (hf : ∀ α, f α ∈ I ^ k)
    (hmem : (Finsupp.linearCombination R x f) ∈ I ^ (k + 1) • (⊤ : Submodule R M)) :
    ∀ α, f α ∈ I ^ (k + 1) := by
  -- ASSEMBLY: build `u = ∑ f_α ⊗ x_α ∈ I^k ⊗ M`; then `μ^{(k)}(u) = ∑ f_α x_α ∈ I^{k+1}M`, so the
  -- Core Obligation (★) `ker_mulPow_le_ker_coordProj` gives `coordProj u = 0`. The
  -- `α`-component of
  -- `coordProj u` is `mk_{I^{k+1}}(f_α)` (since `x_α` reduces to the basis vector `b_α`), so each
  -- `f_α ∈ I^{k+1}`. (`ih` is not needed here; it is subsumed by `hf : f_α ∈ I^k`.)
  classical
  set fI : A →₀ (I ^ k : Ideal R) :=
    { support := f.support
      toFun := fun α => ⟨f α, hf α⟩
      mem_support_toFun := by
        intro α
        rw [Finsupp.mem_support_iff, ne_eq, ne_eq, Subtype.ext_iff]
        simp } with hfI
  have hfIval : ∀ α, (fI α : R) = f α := fun α => rfl
  set u : TensorProduct R (I ^ k : Ideal R) M :=
    fI.sum (fun α a => TensorProduct.tmul R a (x α)) with hu
  have hmul : mulPow (M := M) I k u = Finsupp.linearCombination R x f := by
    rw [hu, map_finsuppSum, Finsupp.linearCombination_apply]
    rw [Finsupp.sum, Finsupp.sum]
    apply Finset.sum_congr rfl
    intro α _
    rw [mulPow_tmul, hfIval]
  have hmulmem : mulPow (M := M) I k u ∈ I ^ (k + 1) • (⊤ : Submodule R M) := by
    rwa [hmul]
  have hcoord : coordProj I b k u = 0 := ker_mulPow_le_ker_coordProj I b hTor k u hmulmem
  intro α
  have hval : coordProj I b k u α = Ideal.Quotient.mk (I ^ (k + 1)) (f α) := by
    rw [hu, map_finsuppSum, Finsupp.sum, Finsupp.finsetSum_apply]
    rw [Finset.sum_eq_single α]
    · rw [coordProj_tmul]
      have hrep : b.repr (reduction I (x α)) = Finsupp.single α 1 := by
        rw [← hb α]; simp
      rw [hrep, Finsupp.single_eq_same, ← map_one (Ideal.Quotient.mk I),
        mulMapL_apply_mk, mul_one, hfIval]
    · intro β _ hβ
      rw [coordProj_tmul]
      have hrep : b.repr (reduction I (x β)) = Finsupp.single β 1 := by
        rw [← hb β]; simp
      rw [hrep, Finsupp.single_eq_of_ne (Ne.symm hβ), map_zero]
    · intro h
      rw [Finsupp.notMem_support_iff] at h
      have hz : fI α = 0 := h
      rw [coordProj_tmul, hz, map_zero, LinearMap.zero_apply]
  have hz : Ideal.Quotient.mk (I ^ (k + 1)) (f α) = 0 := by
    rw [← hval, hcoord, Finsupp.zero_apply]
  rwa [Ideal.Quotient.eq_zero_iff_mem] at hz

/-- Reducing the coefficients of a relation modulo `J` commutes with passing to `M / J • ⊤`. -/
private theorem linearCombination_mapRange_mk_eq_mkQ {A : Type*} (x : A → M) (J : Ideal R)
    (g : A →₀ R) :
    (Finsupp.linearCombination (R ⧸ J)
        (fun α => (Submodule.mkQ (J • (⊤ : Submodule R M))) (x α)))
      (g.mapRange (Ideal.Quotient.mk J) (by simp))
      = (Submodule.mkQ (J • (⊤ : Submodule R M))) (Finsupp.linearCombination R x g) := by
  rw [Finsupp.linearCombination_apply, Finsupp.sum_mapRange_index (by simp)]
  have key : ∀ (α : A) (r : R),
      (Ideal.Quotient.mk J r)
          • (Submodule.mkQ (J • (⊤ : Submodule R M))) (x α)
        = (Submodule.mkQ (J • (⊤ : Submodule R M))) (r • x α) := by
    intro α r
    rw [← mk_smul_quot J r, map_smul]
  simp_rw [key]
  rw [← map_finsuppSum, Finsupp.linearCombination_apply]

/-- **Inductive step for `linearIndependent_reduction_pow` (Free_k ⟹ Free_{k+1}).**
Given that the images of `x` in `M/I^kM` are linearly independent over `R/I^k`
(`ih`), the images of `x` in `M/I^{k+1}M` are linearly independent over `R/I^{k+1}`.

*Argument.* Let `c : A →₀ R/I^{k+1}` with
`∑ c_α x̄^{(k+1)}_α = 0`. Apply the projection `q : M/I^{k+1}M → M/I^kM`: the relation
becomes `∑ ρ(c_α) x̄^{(k)}_α = 0` over `R/I^k`, so by `ih` each `ρ(c_α) = 0`, i.e.
`c_α ∈ I^k/I^{k+1}`. Lift `c_α = f̄_α` with `f_α ∈ I^k`; then `∑ f_α x_α ∈ I^{k+1}M`, so the
descent leaf `coeff_mem_pow_succ_of_mem_pow` forces `f_α ∈ I^{k+1}`, so `c_α = 0`. -/
theorem linearIndependent_reduction_succ
    {A : Type*} (x : A → M) (I : Ideal R)
    (b : Module.Basis A (R ⧸ I) (M ⧸ smul (M := M) I))
    (hb : ∀ α, b α = reduction I (x α))
    (hTor : Function.Injective (torMul (M := M) I))
    (k : ℕ)
    (ih : LinearIndependent (R ⧸ I ^ k)
      (fun α => (Submodule.mkQ (I ^ k • (⊤ : Submodule R M))) (x α))) :
    LinearIndependent (R ⧸ I ^ (k + 1))
      (fun α => (Submodule.mkQ (I ^ (k + 1) • (⊤ : Submodule R M))) (x α)) := by
  -- k[x,y]/(x,y)ⁿ: ~30000 confirming, 0 counterexamples. hTor exactly separates the
  -- ~46000 ih-holds-but-conclusion-fails models, as local-flatness theory predicts.)
  -- ASSEMBLY (Step 2): reduce the level-(k+1) relation to the descent leaf
  -- `coeff_mem_pow_succ_of_mem_pow`, lifting coefficients to `I^k` via `ih`.
  classical
  rw [linearIndependent_iff]
  intro c hc
  -- A section of mk : R → R/I^(k+1), preserving 0.
  set s : (R ⧸ I ^ (k + 1)) → R :=
    fun y => if y = 0 then 0 else Function.surjInv Ideal.Quotient.mk_surjective y with hs_def
  have hs0 : s 0 = 0 := by simp [hs_def]
  have hsmk : ∀ y, Ideal.Quotient.mk (I ^ (k + 1)) (s y) = y := by
    intro y
    rw [hs_def]
    dsimp only
    split
    · next h => rw [h]; simp
    · exact Function.surjInv_eq Ideal.Quotient.mk_surjective y
  -- The lift f : A →₀ R with mk (f α) = c α.
  set f : A →₀ R := c.mapRange s hs0 with hf_def
  have hfc : ∀ α, Ideal.Quotient.mk (I ^ (k + 1)) (f α) = c α := by
    intro α
    rw [hf_def, Finsupp.mapRange_apply, hsmk]
  have push := linearCombination_mapRange_mk_eq_mkQ (R := R) (M := M) x
  -- the combination of c equals mkQ (linearCombination R x f), since c = f.mapRange (mk)
  have hcf : c = f.mapRange (Ideal.Quotient.mk (I ^ (k + 1))) (by simp) := by
    ext α
    rw [Finsupp.mapRange_apply, hfc]
  have hmem1 : Finsupp.linearCombination R x f ∈ I ^ (k + 1) • (⊤ : Submodule R M) := by
    have := push (I ^ (k + 1)) f
    rw [← hcf] at this
    rw [hc] at this
    rw [← Submodule.Quotient.mk_eq_zero]
    exact this.symm
  -- f α ∈ I^k, via the level-k relation and ih
  have hle : (I ^ (k + 1) • (⊤ : Submodule R M)) ≤ I ^ k • (⊤ : Submodule R M) :=
    Submodule.smul_mono (Ideal.pow_le_pow_right (by omega)) le_rfl
  have hmemk : Finsupp.linearCombination R x f ∈ I ^ k • (⊤ : Submodule R M) := hle hmem1
  have hf : ∀ α, f α ∈ I ^ k := by
    -- level-k combination = 0
    have hk0 : (Finsupp.linearCombination (R ⧸ I ^ k)
        (fun α => (Submodule.mkQ (I ^ k • (⊤ : Submodule R M))) (x α)))
        (f.mapRange (Ideal.Quotient.mk (I ^ k)) (by simp)) = 0 := by
      rw [push (I ^ k) f, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hmemk
    rw [linearIndependent_iff] at ih
    have hd0 := ih _ hk0
    intro α
    have : Ideal.Quotient.mk (I ^ k) (f α) = 0 := by
      have := congrArg (fun g : A →₀ (R ⧸ I ^ k) => g α) hd0
      simpa [Finsupp.mapRange_apply] using this
    rwa [Ideal.Quotient.eq_zero_iff_mem] at this
  -- apply the descent leaf
  have hfin := coeff_mem_pow_succ_of_mem_pow x I b hb hTor k f hf hmem1
  -- conclude c = 0
  refine Finsupp.ext fun α => ?_
  rw [Finsupp.zero_apply, ← hfc α, Ideal.Quotient.eq_zero_iff_mem]
  exact hfin α

/-- **(Free_k, linear-independence half — the genuine remaining core of Stacks 051H.)**
For every `k`, the images of `x` in `M/I^kM` are linearly independent over `R/I^k`.

Equivalently `M/I^kM` is free on the images of `x_α` over `R/I^k` (the spanning half is the
nilpotent Nakayama / `span_sup_smul_eq_top_of_basis` machinery; only independence is needed for
the descent). This is the sound replacement for the refuted `torMulPow`-injectivity chain.

*Argument (joint induction on `k`).*
`k = 0`: since `I^0 = ⊤` we have `R/I^0 = 0` and the statement is vacuous;
`k = 1` is the hypothesis `b` (basis of `M/IM` over `R/I`). For the step `k ⟹ k+1`, use the short
exact sequence `0 → I^kM/I^{k+1}M → M/I^{k+1}M → M/I^kM → 0`, where `M/I^kM` is free over `R/I^k`
(induction hypothesis) and the submodule `I^kM/I^{k+1}M` is identified, via the **associated-graded
isomorphism**
  `θ_k : (I^k/I^{k+1}) ⊗_{R/I} (M/IM) ≅ I^kM/I^{k+1}M`  (`ā ⊗ m̄ ↦ a·m`),
with a free `R/I`-module on the `x̄_α`. The injectivity of `θ_k` is the **Core Obligation** of the
local criterion of flatness (Stacks 00MK); it consumes `hTor`, used only at the `I`-level as
injectivity of `I⊗M→M`, together with the induction hypothesis Free_k. Free_k is genuinely
needed: the version without it, a standalone `Tor₁(R/I, M/I^kM)=0`, is false, as
`R = k[x,y]`, `I = (x,y)`, `M = R` shows. -/
@[sga "3 VIB 6.2.2" "partial", sga "3 VIIB 0.3.7" "partial", sga "3 VIII 6.2" "injectivity clause"]
theorem linearIndependent_reduction_pow
    {A : Type*} (x : A → M) (I : Ideal R)
    (b : Module.Basis A (R ⧸ I) (M ⧸ smul (M := M) I))
    (hb : ∀ α, b α = reduction I (x α))
    (hTor : Function.Injective (torMul (M := M) I))
    (k : ℕ) :
    LinearIndependent (R ⧸ I ^ k)
      (fun α => (Submodule.mkQ (I ^ k • (⊤ : Submodule R M))) (x α)) := by
  -- k=0 vacuous over the zero ring R/I^0, k=1 = basis b; hTor kills all bad cases.)
  induction k with
  | zero =>
    -- R/I^0 = R/⊤ is the zero ring, hence Subsingleton; LinearIndependent is vacuous.
    have : Subsingleton (R ⧸ I ^ 0) := by
      rw [pow_zero]
      exact Ideal.Quotient.subsingleton_iff.mpr (by simp)
    exact linearIndependent_of_subsingleton
  | succ k ih =>
    -- INDUCTIVE STEP (the hard core: associated-graded / local flatness criterion).
    -- Delegated to `linearIndependent_reduction_succ`, which needs the injectivity of
    -- θ_k : (I^k/I^{k+1}) ⊗_{R/I} (M/IM) → I^kM/I^{k+1}M, consuming `hTor` at the I-level
    -- together with the induction hypothesis `ih`.
    exact linearIndependent_reduction_succ x I b hb hTor k ih

/-- **Linear-independence descent step.**

Fix a finitely-supported relation `∑ f_α x_α = 0` (i.e.
`Finsupp.linearCombination R x f = 0`). If all coefficients lie in `I ^ k`
(`∀ α, f α ∈ I ^ k`), then in fact all coefficients lie in `I ^ (k+1)`.

*Argument (the crux of Stacks 051H).*
Write `J := I ^ k`. The element `t := ∑_α (f α ⊗ x_α)`, with `f α ∈ J`, lives in
`J ⊗_R M`. Its image under multiplication `J ⊗_R M → M` is `∑ f_α x_α = 0`.

For `k = 0` (`J = R`), the relation `∑ f_α x_α = 0` reduces mod `I` to
`∑ (f̄_α) x̄_α = 0` in `M/IM`; since `(x̄_α)` is the basis `b`, linear independence
of `b` forces `f̄_α = 0`, i.e. `f α ∈ I`. This is the base step `k = 0 ⟹ f α ∈ I`.

For the inductive picture one shows, more uniformly, that `M / I^{k+1} M` is free
on the images of `x` over `R / I^{k+1}` for every `k`, equivalently uses the
commutative square relating `I^k ⊗_R M`, the multiplication map (injective, since
`Tor₁ = 0` gives injectivity of `I ⊗ M → M`, and this propagates to `I^k`), and the
identification `(I^k / I^{k+1}) ⊗_{R/I} (M/IM)`. Concretely: with `f α ∈ I^k`,
form `t = ∑ f_α ⊗ x_α ∈ I^k ⊗_R M`; it maps to `0 ∈ M`. Pushing `t` along
`I^k ⊗_R M → (I^k/I^{k+1}) ⊗_{R/I} (M/IM)` and using that `(x̄_α)` is an `R/I`-basis
of `M/IM`, the freeness forces each coefficient `f̄_α ∈ I^k/I^{k+1}` to vanish, i.e.
`f α ∈ I^{k+1}`. The injectivity hypothesis `hTor` is what makes the multiplication
map a monomorphism so that `t = 0` can be deduced and tracked through the filtration.

This lemma packages the analytic kernel of the proof, in two regimes: the base `k = 0`
uses the basis `b` directly, and `k ≥ 1` uses the graded and Tor machinery. -/
theorem coeff_mem_pow_succ_of_relation
    {A : Type*} (x : A → M) (I : Ideal R)
    (b : Module.Basis A (R ⧸ I) (M ⧸ smul (M := M) I))
    (hb : ∀ α, b α = reduction I (x α))
    (hTor : Function.Injective (torMul (M := M) I))
    (f : A →₀ R) (hf : Finsupp.linearCombination R x f = 0)
    (k : ℕ) :
    ∀ α, f α ∈ I ^ (k + 1) := by
  -- GLUE (Strategy C / Free_k, sound): the descent step follows from linear independence of
  -- the images of `x` in `M/I^{k+1}M` over `R/I^{k+1}` (`linearIndependent_reduction_pow`).
  -- Push the `R`-relation `∑ f_α x_α = 0` to an `R/I^{k+1}`-relation among the reductions;
  -- linear independence forces each coefficient `f_α mod I^{k+1} = 0`, i.e. `f_α ∈ I^{k+1}`.
  -- (No `I^k`-level Tor vanishing is used; `hTor` enters only inside
  -- `linearIndependent_reduction_pow`, at the `I`-level.)
  have hLI := linearIndependent_reduction_pow x I b hb hTor (k + 1)
  rw [linearIndependent_iff] at hLI
  set g : A →₀ (R ⧸ I ^ (k + 1)) :=
    f.mapRange (Ideal.Quotient.mk (I ^ (k + 1))) (by simp) with hg
  have hcomb : (Finsupp.linearCombination (R ⧸ I ^ (k + 1))
      (fun α => (Submodule.mkQ (I ^ (k + 1) • (⊤ : Submodule R M))) (x α))) g = 0 := by
    rw [hg, linearCombination_mapRange_mk_eq_mkQ, hf, map_zero]
  have hgz := hLI g hcomb
  intro α
  have hga : g α = 0 := by rw [hgz]; simp
  rw [hg, Finsupp.mapRange_apply] at hga
  rwa [Ideal.Quotient.eq_zero_iff_mem] at hga

/-- The family `x` is linearly independent over `R`.

*Argument.* Use `linearIndependent_iff`/`Finsupp.linearCombination`: take `f : A →₀ R`
with `∑ f_α x_α = 0`; we must show `f = 0`. By `coeff_mem_pow_succ_of_relation` and
induction on `k` (base: `f α ∈ I ^ 0 = R` trivially), `∀ k, ∀ α, f α ∈ I ^ k`.
Since `I` is nilpotent, `I ^ n = ⊥` for some `n`, so `f α ∈ I ^ n = ⊥`, i.e.
`f α = 0` for every `α`; hence `f = 0`. -/
theorem linearIndependent_of_basis_mod_of_tor
    {A : Type*} (x : A → M) (I : Ideal R)
    (hI : IsNilpotent I)
    (b : Module.Basis A (R ⧸ I) (M ⧸ smul (M := M) I))
    (hb : ∀ α, b α = reduction I (x α))
    (hTor : Function.Injective (torMul (M := M) I)) :
    LinearIndependent R x := by
  -- STRATEGY: rw [linearIndependent_iff]; intro f hf; (hf : linearCombination R x f = 0)
  -- have hmem : ∀ k, ∀ α, f α ∈ I ^ k := by
  --   intro k; induction k with
  --   | zero => simp [pow_zero]  -- I^0 = ⊤, membership trivial
  --   | succ k ih => exact coeff_mem_pow_succ_of_relation x I b hb hTor f hf k ih
  -- obtain ⟨n, hn⟩ := hI;  -- hn : I ^ n = 0 (= ⊥)
  -- ext α; have := hmem n α; rw [hn] at this; simpa using this  (f α ∈ ⊥ ⇒ f α = 0)
  rw [linearIndependent_iff]
  intro f hf
  have hmem : ∀ k, ∀ α, f α ∈ I ^ k := by
    intro k
    induction k with
    | zero => intro α; simp
    | succ k _ => exact coeff_mem_pow_succ_of_relation x I b hb hTor f hf k
  obtain ⟨n, hn⟩ := hI
  ext α
  have hfa := hmem n α
  rw [hn] at hfa
  simpa using hfa

/-- **Theorem (Stacks Project, Tag 051H; Lemma 10.101.3).**

Let `R` be a ring, `I ⊆ R` an ideal, `M` an `R`-module, `A` a set, and
`x : A → M` a family of elements of `M`. Assume:

1. `I` is nilpotent;
2. the family of reductions `(reduction I (x α))_{α}` forms a basis of the
   `R/I`-module `M/IM`, witnessed by a basis `b` with `b α = reduction I (x α)`;
3. `Tor₁^R(R/I, M) = 0`, expressed as injectivity of the multiplication map
   `torMul I : I ⊗_R M → M`.

Then `x` is a basis of `M` as an `R`-module: it is linearly independent and
spans `M`. -/
@[stacks 051H]
theorem free_of_nilpotent_of_basis_mod_of_tor
    {A : Type*} (x : A → M) (I : Ideal R)
    (hI : IsNilpotent I)
    (b : Module.Basis A (R ⧸ I) (M ⧸ smul (M := M) I))
    (hb : ∀ α, b α = reduction I (x α))
    (hTor : Function.Injective (torMul (M := M) I)) :
    LinearIndependent R x ∧ ⊤ ≤ Submodule.span R (Set.range x) := by
  refine ⟨?_, ?_⟩
  · -- Linear independence: I-adic descent (uses hTor and the basis b).
    exact linearIndependent_of_basis_mod_of_tor x I hI b hb hTor
  · -- Spanning: Nakayama for the nilpotent ideal I.
    -- From the basis, `span R (range x) ⊔ smul I = ⊤`; then nilpotent Nakayama
    -- (`eq_top_of_isNilpotent_of_le_sup_smul`) upgrades this to `span R (range x) = ⊤`.
    have hsup : (⊤ : Submodule R M) ≤ Submodule.span R (Set.range x) ⊔ smul (M := M) I :=
      span_sup_smul_eq_top_of_basis x I b hb
    have htop : Submodule.span R (Set.range x) = ⊤ :=
      eq_top_of_isNilpotent_of_le_sup_smul I hI (Submodule.span R (Set.range x)) hsup
    rw [htop]

end Stacks.FreeOfNilpotentIdeal
