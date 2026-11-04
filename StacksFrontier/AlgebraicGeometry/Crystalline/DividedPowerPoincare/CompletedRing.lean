module

public import StacksFrontier.AlgebraicGeometry.Crystalline.DividedPowerPoincare.AugmentedContraction
import all StacksFrontier.AlgebraicGeometry.Crystalline.DividedPowerPoincare.SquareZeroDerivations

/-!
# The divided power Poincaré lemma: exactness, and the completed ring

The fourth part of `StacksFrontier.AlgebraicGeometry.Crystalline.DividedPowerPoincare`: the
uncompleted assertion, exactness of `0 → M → M ⊗[A] P → M ⊗[A] Ω¹_{P/A,δ} → ⋯`
(`Crystalline.dividedPowerPolynomialDeRham_tensor_augmentation_injective`,
`Crystalline.dividedPowerPolynomialDeRham_tensor_exact`); then, for the completed assertion, the
completed tensor product, the `p`-adic completion `D` of `P`, the closure of the augmentation
ideal in `D`, and the existence and uniqueness of the continuous extension of the canonical
divided powers to it (`Crystalline.CompletedPoincare.exists_continuousDividedPowers`,
`Crystalline.CompletedPoincare.continuousDividedPowers_unique`).

## References

* [Stacks Project, Tag 07LC](https://stacks.math.columbia.edu/tag/07LC)
-/
@[expose] public section

universe u v w uA uW uM

namespace Crystalline

attribute [local implicit_reducible] RestrictScalars

open DividedPowers
open scoped TensorProduct

section OrdinaryExactness

open CategoryTheory
open scoped RightActions

variable (A : Type u) [CommRing A] (W : Type w)

attribute [local implicit_reducible] coefficientDividedPowerRing
  DividedPowers.setIndexedDividedPowerPolynomialDividedPowerRing
attribute [local instance low] setIndexedDividedPowerPolynomialCommRing
attribute [local instance low] coefficientDividedPowerRingAlgebra
attribute [local instance low] setIndexedDividedPowerPolynomialAlgebra'
attribute [local instance low] setIndexedDividedPowerPolynomialDividedPowerRingAlgebra
attribute [local instance low] indexedDividedPowerPolynomialFinsuppModule
attribute [local instance low] indexedDividedPowerPolynomialFinsuppModuleOp
attribute [local instance low] indexedDividedPowerPolynomialFinsuppCentral

open scoped ExteriorAlgebra
open Module

attribute [local implicit_reducible] augmentedDividedPowerDeRhamTerm
  augmentedDividedPowerDeRhamDifferential

private theorem augmentedDifferential_eq_complex_differential
    (A : Type u) [CommRing A] (W : Type w) (n : ℕ) :
    (augmentedDividedPowerDeRhamComplex A W).d n (n + 1) =
      augmentedDividedPowerDeRhamDifferential A W n := by
  simp [augmentedDividedPowerDeRhamComplex, CochainComplex.of_d]

/-- **The divided power Poincaré lemma, exactness at the coefficient module.**  For a ring `A`,
a family of variables `W` and the divided power polynomial algebra `P = A⟨x_w : w ∈ W⟩` with its
canonical divided powers, the first map `M → M ⊗[A] P` of the complex

`0 → M → M ⊗[A] P → M ⊗[A] Ω¹_{P/A,δ} → M ⊗[A] Ω²_{P/A,δ} → ⋯`

is injective for every `A`-module `M`; the degree-zero term of the complex is identified with
`M` by `Crystalline.coefficientLinearEquiv`. -/
@[stacks 07LC "ordinary_exactness"]
public theorem dividedPowerPolynomialDeRham_tensor_augmentation_injective
    (A : Type u) [CommRing A] (W : Type w)
    (M : Type v) [AddCommGroup M] [Module A M] :
    Function.Injective
      ((augmentedDividedPowerDeRhamDifferential A W 0).hom.lTensor M) := by
  let C := augmentedDividedPowerDeRhamComplex A W
  obtain ⟨H⟩ := augmentedDividedPowerDeRhamComplex_contractible A W
  rw [← augmentedDifferential_eq_complex_differential A W 0]
  have hcat : (𝟙 (C.X 0)) = C.d 0 (0 + 1) ≫ H.hom (0 + 1) 0 := by
    have hc := H.comm 0
    rw [dNext_eq H.hom (ComplexShape.up_mk 0 (0 + 1) rfl), prevD_nat C C 0 H.hom] at hc
    simpa using hc
  have hleft : (LinearMap.id : (C.X 0) →ₗ[A] (C.X 0)) =
      (H.hom (0 + 1) 0).hom.comp (C.d 0 (0 + 1)).hom := by
    simpa [ModuleCat.hom_id, ModuleCat.hom_comp] using
      congrArg (fun f => f.hom) hcat
  have ht := by
    simpa only [LinearMap.lTensor_id, LinearMap.lTensor_comp] using
      congrArg (fun f => f.lTensor M) hleft
  intro x y hxy
  have hx := congrArg (fun f => f x) ht
  have hy := congrArg (fun f => f y) ht
  change x = (H.hom (0 + 1) 0).hom.lTensor M ((C.d 0 (0 + 1)).hom.lTensor M x) at hx
  change y = (H.hom (0 + 1) 0).hom.lTensor M ((C.d 0 (0 + 1)).hom.lTensor M y) at hy
  exact hx.trans ((congrArg ((H.hom (0 + 1) 0).hom.lTensor M) hxy).trans hy.symm)

/-- **The divided power Poincaré lemma.**  For a ring `A`, a family of variables `W` and the
divided power polynomial algebra `P = A⟨x_w : w ∈ W⟩` with its canonical divided powers, the
complex

`0 → M → M ⊗[A] P → M ⊗[A] Ω¹_{P/A,δ} → M ⊗[A] Ω²_{P/A,δ} → ⋯`

is exact at every term after the first, for every `A`-module `M`.  Injectivity of the first map
is `Crystalline.dividedPowerPolynomialDeRham_tensor_augmentation_injective`. -/
@[stacks 07LC "ordinary_exactness"]
public theorem dividedPowerPolynomialDeRham_tensor_exact
    (A : Type u) [CommRing A] (W : Type w)
    (M : Type v) [AddCommGroup M] [Module A M] (n : ℕ) :
    Function.Exact
      ((augmentedDividedPowerDeRhamDifferential A W n).hom.lTensor M)
      ((augmentedDividedPowerDeRhamDifferential A W (n + 1)).hom.lTensor M) := by
  let C := augmentedDividedPowerDeRhamComplex A W
  obtain ⟨H⟩ := augmentedDividedPowerDeRhamComplex_contractible A W
  rw [← augmentedDifferential_eq_complex_differential A W n,
    ← augmentedDifferential_eq_complex_differential A W (n + 1)]
  have hcat : (𝟙 (C.X (n + 1))) =
      C.d (n + 1) ((n + 1) + 1) ≫ H.hom ((n + 1) + 1) (n + 1) +
        H.hom (n + 1) n ≫ C.d n (n + 1) := by
    have hc := H.comm (n + 1)
    rw [dNext_eq H.hom (ComplexShape.up_mk (n + 1) ((n + 1) + 1) rfl),
      prevD_nat C C (n + 1) H.hom] at hc
    simpa using hc
  have hcomm : (LinearMap.id : (C.X (n + 1)) →ₗ[A] (C.X (n + 1))) =
      (H.hom ((n + 1) + 1) (n + 1)).hom.comp (C.d (n + 1) ((n + 1) + 1)).hom +
        (C.d n (n + 1)).hom.comp (H.hom (n + 1) n).hom := by
    simpa [ModuleCat.hom_id, ModuleCat.hom_comp, ModuleCat.hom_add] using
      congrArg (fun f => f.hom) hcat
  have ht := congrArg (fun f : (C.X (n + 1)) →ₗ[A] (C.X (n + 1)) => f.lTensor M) hcomm
  have ht' := by
    simpa only [LinearMap.lTensor_id, LinearMap.lTensor_comp, LinearMap.lTensor_add] using ht
  rw [LinearMap.exact_iff]
  apply le_antisymm
  · intro x hx
    have hx0 : ((C.d (n + 1) ((n + 1) + 1)).hom.lTensor M) x = 0 :=
      LinearMap.mem_ker.mp hx
    have hval := congrArg (fun f => f x) ht'
    change x =
        ((H.hom ((n + 1) + 1) (n + 1)).hom.lTensor M)
            ((C.d (n + 1) ((n + 1) + 1)).hom.lTensor M x) +
          ((C.d n (n + 1)).hom.lTensor M)
            ((H.hom (n + 1) n).hom.lTensor M x) at hval
    rw [hx0, map_zero, zero_add] at hval
    exact ⟨(H.hom (n + 1) n).hom.lTensor M x, hval.symm⟩
  · intro x hx
    rcases hx with ⟨y, hy⟩
    rw [← hy]
    have hcomp0 := congrArg (fun f => f.hom)
      (augmentedDividedPowerDeRhamDifferential_comp A W n)
    have hcomp :
        ((C.d (n + 1) ((n + 1) + 1)).hom).comp ((C.d n (n + 1)).hom) = 0 := by
      rw [augmentedDifferential_eq_complex_differential A W (n + 1),
        augmentedDifferential_eq_complex_differential A W n]
      exact hcomp0
    have hcompT := congrArg (fun f => f.lTensor M) hcomp
    have hcompT' :
        ((C.d (n + 1) ((n + 1) + 1)).hom.lTensor M).comp
          ((C.d n (n + 1)).hom.lTensor M) = 0 := by
      simpa only [LinearMap.lTensor_comp, LinearMap.lTensor_zero] using hcompT
    exact LinearMap.mem_ker.mpr (LinearMap.congr_fun hcompT' y)

end OrdinaryExactness

/-! ### The completed divided power Poincaré lemma -/

namespace CompletedPoincare

section CompletedTensorProduct

variable (p : ℕ) (D : Type*) [CommRing D] (Omega : Type*) [AddCommGroup Omega] [Module D Omega]

/-- The completed tensor product `M ⊗̂_D Ω`: the `p`-adic completion of `M ⊗_D Ω`. -/
public abbrev completedTensor (M : Type*) [AddCommGroup M] [Module D M] :=
  AdicCompletion (pAdicIdeal (A := D) p) (M ⊗[D] Omega)

/-- The canonical map `M ⊗_D Ω → M ⊗̂_D Ω`. -/
public noncomputable abbrev toCompletedTensorOf (M : Type*) [AddCommGroup M] [Module D M] :
    (M ⊗[D] Omega) →ₗ[D] completedTensor p D Omega M :=
  AdicCompletion.of (pAdicIdeal (A := D) p) (M ⊗[D] Omega)

end CompletedTensorProduct

noncomputable section


variable (p : ℕ) (A : Type uA) [CommRing A] (W : Type uW)

/-! ### The divided power polynomial ring and its `p`-adic completion -/

/-- The divided power polynomial ring `P = A⟨x_w : w ∈ W⟩` of Tag 07H6. -/
public abbrev dividedPowerPolynomialRing : Type (max uA uW) :=
  setIndexedDividedPowerPolynomialAlgebra A W

/-- The augmentation ideal `P₊` of `P`, in the form in which it carries the canonical divided
powers: the divided power ideal `⊥ · P + P₊` of Tag 07H5 for `A` with the trivial divided
powers on its zero ideal. -/
public abbrev augmentationIdeal : Ideal (dividedPowerPolynomialRing A W) :=
  dividedPowerPolynomialIdeal (coefficientDividedPowerRing A).ideal W

/-- The canonical divided powers on the augmentation ideal of `P` (Tag 07H6). -/
public abbrev canonicalDividedPowers : DividedPowers (augmentationIdeal A W) :=
  polynomialDividedPowers A W

/-- The ring `D`, the `p`-adic completion of `P`. -/
public abbrev completedRing : Type (max uA uW) :=
  AdicCompletion (pAdicIdeal (A := dividedPowerPolynomialRing A W) p)
    (dividedPowerPolynomialRing A W)

/-- The canonical map `P → D`. -/
public abbrev toCompletedRing : dividedPowerPolynomialRing A W →+* completedRing p A W :=
  algebraMap _ _

/-- The closure `⋂ₙ (P₊ D + pⁿ D)` in `D` of the image of the augmentation ideal of `P`. -/
public def completedAugmentationIdeal : Ideal (completedRing p A W) :=
  ⨅ n : ℕ, Ideal.map (toCompletedRing p A W) (augmentationIdeal A W) ⊔
    pAdicIdeal (A := completedRing p A W) p ^ n

/-- An element of `D` lies in the closure of the augmentation ideal exactly when it is
congruent to an element of `P₊ D` modulo `pⁿ` for every `n`. -/
public theorem mem_completedAugmentationIdeal_iff (x : completedRing p A W) :
    x ∈ completedAugmentationIdeal p A W ↔
      ∀ n : ℕ, ∃ y ∈ Ideal.map (toCompletedRing p A W) (augmentationIdeal A W),
        x - y ∈ pAdicIdeal (A := completedRing p A W) p ^ n := by
  simp only [completedAugmentationIdeal, Submodule.mem_iInf, Submodule.mem_sup]
  refine forall_congr' fun n ↦ ⟨?_, ?_⟩
  · rintro ⟨y, hy, z, hz, rfl⟩
    exact ⟨y, hy, by simpa using hz⟩
  · rintro ⟨y, hy, hz⟩
    exact ⟨y, hy, x - y, hz, by ring⟩

/-- A uniformly `p`-adically continuous divided power structure on the closure of the
augmentation ideal of `P` in `D`, extending the canonical divided powers of `P`. -/
public structure ContinuousDividedPowers where
  /-- The divided power structure on the closure of the augmentation ideal. -/
  dividedPowers : DividedPowers (completedAugmentationIdeal p A W)
  /-- It extends the canonical divided powers of `P`. -/
  dpow_toCompletedRing : ∀ (n : ℕ) (x : dividedPowerPolynomialRing A W),
    x ∈ augmentationIdeal A W → ∀ xhat : completedAugmentationIdeal p A W,
      (xhat : completedRing p A W) = toCompletedRing p A W x →
        dividedPowers.dpow n (xhat : completedRing p A W) =
          toCompletedRing p A W ((canonicalDividedPowers A W).dpow n x)
  /-- Divided powers preserve congruences modulo each `p`-adic neighborhood. -/
  dpow_congr : ∀ (n e : ℕ) (x y : completedAugmentationIdeal p A W),
    (x : completedRing p A W) - y ∈
      pAdicIdeal (A := completedRing p A W) p ^ e →
    dividedPowers.dpow n (x : completedRing p A W) -
        dividedPowers.dpow n (y : completedRing p A W) ∈
      pAdicIdeal (A := completedRing p A W) p ^ e

private theorem completedRing_mem_pAdicPow_of_eval_eq_zero (e : ℕ)
    (x : completedRing p A W)
    (hx : AdicCompletion.evalₐ (pAdicIdeal p) e x = 0) :
    x ∈ pAdicIdeal (A := completedRing p A W) p ^ e := by
  let P := dividedPowerPolynomialRing A W
  let I : Ideal P := pAdicIdeal (A := P) p
  let J : Ideal (completedRing p A W) := pAdicIdeal p
  have hfg : I.FG := by
    dsimp [I, pAdicIdeal]
    exact Submodule.fg_span_singleton (p : P)
  have hfactor : I ^ e ≤ I ^ e • (⊤ : Submodule P P) := by
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
  have heval : AdicCompletion.eval I P e x = 0 := by
    have h := AdicCompletion.factor_evalₐ_eq_eval I x hfactor
    rw [hx, map_zero] at h
    exact h.symm
  have hmem : x ∈ I ^ e • (⊤ : Submodule P (completedRing p A W)) := by
    rw [AdicCompletion.pow_smul_top_eq_ker_eval hfg, LinearMap.mem_ker]
    exact heval
  have hmap : Ideal.map (algebraMap P (completedRing p A W)) I = J := by
    simp [I, J, pAdicIdeal, Ideal.map_span]
  have hmapPow : Ideal.map (algebraMap P (completedRing p A W)) (I ^ e) = J ^ e := by
    rw [Ideal.map_pow, hmap]
  let : IsScalarTower P (completedRing p A W) (completedRing p A W) :=
    IsScalarTower.of_algebraMap_smul (R := P) (A := completedRing p A W)
      (M := completedRing p A W) (fun r x => by
        change (algebraMap (completedRing p A W) (completedRing p A W)
          ((algebraMap P (completedRing p A W)) r)) * x =
            (algebraMap P (completedRing p A W) r) * x
        rfl)
  let Isub : Submodule P P := I ^ e
  let K : Submodule P (completedRing p A W) := Isub •
    (⊤ : Submodule P (completedRing p A W))
  have hsub : K ≤
      Submodule.restrictScalars P
        ((J ^ e : Ideal (completedRing p A W)) : Submodule (completedRing p A W)
          (completedRing p A W)) := by
    rw [Submodule.smul_le]
    intro r hr x hx
    have hr' : algebraMap P (completedRing p A W) r ∈ J ^ e := by
      rw [← hmapPow]
      exact Ideal.mem_map_of_mem _ hr
    change (algebraMap P (completedRing p A W) r) * x ∈ J ^ e
    exact (J ^ e).mul_mem_right x hr'
  change x ∈ J ^ e
  exact (Submodule.restrictScalars_mem P
    ((J ^ e : Ideal (completedRing p A W)) : Submodule (completedRing p A W)
      (completedRing p A W)) x).mp (hsub hmem)

private theorem completedRing_exists_polynomial_approximation
    (x : completedRing p A W) (e : ℕ) :
    ∃ a : dividedPowerPolynomialRing A W,
      x - toCompletedRing p A W a ∈
        pAdicIdeal (A := completedRing p A W) p ^ e := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective
    (AdicCompletion.evalₐ (pAdicIdeal (A := dividedPowerPolynomialRing A W) p) e x)
  refine ⟨a, completedRing_mem_pAdicPow_of_eval_eq_zero p A W e _ ?_⟩
  change AdicCompletion.evalₐ _ e (x - AdicCompletion.of _ _ a) = 0
  rw [map_sub, AdicCompletion.evalₐ_of, sub_eq_zero]
  exact ha.symm

private theorem completedRing_idealMap_exists_polynomial_approximation
    (x : completedRing p A W)
    (hx : x ∈ Ideal.map (toCompletedRing p A W) (augmentationIdeal A W))
    (e : ℕ) :
    ∃ a : dividedPowerPolynomialRing A W,
      a ∈ augmentationIdeal A W ∧
      x - toCompletedRing p A W a ∈
        pAdicIdeal (A := completedRing p A W) p ^ e := by
  rw [Ideal.map] at hx
  induction hx using Submodule.span_induction with
  | mem z hz =>
      rcases hz with ⟨a, ha, rfl⟩
      exact ⟨a, ha, by simp⟩
  | zero =>
      exact ⟨0, (augmentationIdeal A W).zero_mem, by simp⟩
  | add x y hx hy ihx ihy =>
      obtain ⟨a, ha, hxa⟩ := ihx
      obtain ⟨b, hb, hyb⟩ := ihy
      refine ⟨a + b, (augmentationIdeal A W).add_mem ha hb, ?_⟩
      rw [map_add]
      have : x + y - (toCompletedRing p A W a + toCompletedRing p A W b) =
          (x - toCompletedRing p A W a) + (y - toCompletedRing p A W b) := by ring
      rw [this]
      exact (pAdicIdeal (A := completedRing p A W) p ^ e).add_mem hxa hyb
  | smul r x hx ih =>
      obtain ⟨a, ha, hxa⟩ := ih
      obtain ⟨r₀, hr₀⟩ := completedRing_exists_polynomial_approximation p A W r e
      refine ⟨r₀ * a, (augmentationIdeal A W).mul_mem_left r₀ ha, ?_⟩
      change r * x - (toCompletedRing p A W r₀) * toCompletedRing p A W a ∈ _
      have : r * x - (toCompletedRing p A W r₀) * toCompletedRing p A W a =
          (r - toCompletedRing p A W r₀) * x +
            toCompletedRing p A W r₀ * (x - toCompletedRing p A W a) := by ring
      rw [this]
      exact (pAdicIdeal (A := completedRing p A W) p ^ e).add_mem
        ((pAdicIdeal (A := completedRing p A W) p ^ e).mul_mem_right x hr₀)
        ((pAdicIdeal (A := completedRing p A W) p ^ e).mul_mem_left
          (toCompletedRing p A W r₀) hxa)

private theorem augmentationIdeal_eq_augmentationKer :
    augmentationIdeal A W =
      RingHom.ker (dividedPowerPolynomialAugmentation A W).toRingHom := by
  change dividedPowerPolynomialIdeal (⊥ : Ideal A) W = _
  rw [dividedPowerPolynomialIdeal,
    dividedPowerPolynomialPositiveIdeal]
  rw [Ideal.map_bot, Ideal.add_eq_sup, bot_sup_eq]

private theorem augmentationIdeal_pAdic_smul
    {x : dividedPowerPolynomialRing A W} (hx : x ∈ augmentationIdeal A W)
    (e : ℕ) (hxpow : x ∈ pAdicIdeal
      (A := dividedPowerPolynomialRing A W) p ^ e) :
    x ∈ pAdicIdeal (A := dividedPowerPolynomialRing A W) p ^ e •
      (augmentationIdeal A W : Submodule (dividedPowerPolynomialRing A W)
        (dividedPowerPolynomialRing A W)) := by
  let P := dividedPowerPolynomialRing A W
  let ε := dividedPowerPolynomialAugmentation A W
  have hεx : ε.toRingHom x = 0 := by
    have hxker : x ∈ RingHom.ker ε.toRingHom := by
      rw [← augmentationIdeal_eq_augmentationKer (A := A) (W := W)]
      exact hx
    exact (RingHom.mem_ker).mp hxker
  have hprincipal : x ∈ (Ideal.span {(p : P) ^ e} : Ideal P) • (⊤ : Submodule P P) := by
    simpa [pAdicIdeal, Ideal.span_singleton_pow,
      Ideal.smul_eq_mul, Ideal.mul_top] using hxpow
  rw [Submodule.ideal_span_singleton_smul] at hprincipal
  obtain ⟨y, hy, hEq⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hprincipal
  have hEqmul : (p : P) ^ e * y = x := by simpa [smul_eq_mul] using hEq
  have hcoeff' : ε.toRingHom ((p : P) ^ e * y) = 0 := by
    rw [hEqmul]
    exact hεx
  have hcoeff : (p : A) ^ e * ε.toRingHom y = 0 := by
    simpa only [map_mul, map_pow, map_natCast] using hcoeff'
  let y' : P := y - algebraMap A P (ε.toRingHom y)
  have hy' : y' ∈ augmentationIdeal A W := by
    rw [augmentationIdeal_eq_augmentationKer (A := A) (W := W), RingHom.mem_ker]
    simp only [y', ε, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sub,
      AlgHom.commutes]
    exact sub_eq_zero.mpr rfl
  have hfactor : (p : P) ^ e * y' = x := by
    have hconst : (p : P) ^ e * algebraMap A P (ε.toRingHom y) = 0 := by
      calc
        _ = algebraMap A P ((p : A) ^ e * ε.toRingHom y) := by simp [map_mul, map_pow]
        _ = 0 := by rw [hcoeff]; simp
    rw [show y' = y - algebraMap A P (ε.toRingHom y) from rfl, mul_sub, hEqmul, hconst,
      sub_zero]
  have hp : (p : P) ^ e ∈ pAdicIdeal (A := P) p ^ e := by
    rw [pAdicIdeal, Ideal.span_singleton_pow]
    exact Ideal.mem_span_singleton_self _
  have hmem := Submodule.smul_mem_smul hp hy'
  rw [← hfactor]
  simpa [smul_eq_mul] using hmem

private theorem completedRing_eval_kills_pAdicPow (e : ℕ) :
    (pAdicIdeal (A := completedRing p A W) p) ^ e ≤
      RingHom.ker (AdicCompletion.evalₐ
        (pAdicIdeal (A := dividedPowerPolynomialRing A W) p) e) := by
  let P := dividedPowerPolynomialRing A W
  let I : Ideal P := pAdicIdeal (A := P) p
  change (Ideal.span {(p : completedRing p A W)} : Ideal (completedRing p A W)) ^ e ≤ _
  rw [Ideal.span_singleton_pow, Ideal.span_le]
  intro x hx
  rcases Set.mem_singleton_iff.mp hx with rfl
  change AdicCompletion.evalₐ I e ((p : completedRing p A W) ^ e) = 0
  change AdicCompletion.evalₐ I e (AdicCompletion.of I P ((p : P) ^ e)) = 0
  rw [AdicCompletion.evalₐ_of]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) e)

private noncomputable def completedAugmentationNear
    (x : completedAugmentationIdeal p A W) (n : ℕ) : completedRing p A W :=
  Classical.choose
    ((mem_completedAugmentationIdeal_iff p A W (x : completedRing p A W)).mp x.property n)

private noncomputable def completedAugmentationRepresentative
    (x : completedAugmentationIdeal p A W) (n : ℕ) : dividedPowerPolynomialRing A W :=
  Classical.choose <| completedRing_idealMap_exists_polynomial_approximation p A W
    (completedAugmentationNear p A W x n)
    (Classical.choose_spec
      ((mem_completedAugmentationIdeal_iff p A W (x : completedRing p A W)).mp x.property n)).1 n

private theorem completedAugmentationRepresentative_spec
    (x : completedAugmentationIdeal p A W) (n : ℕ) :
    completedAugmentationRepresentative p A W x n ∈ augmentationIdeal A W ∧
      (x : completedRing p A W) -
        toCompletedRing p A W (completedAugmentationRepresentative p A W x n) ∈
          pAdicIdeal (A := completedRing p A W) p ^ n := by
  let y := completedAugmentationNear p A W x n
  have hy : y ∈ Ideal.map (toCompletedRing p A W) (augmentationIdeal A W) ∧
      (x : completedRing p A W) - y ∈ pAdicIdeal p ^ n := by
    simpa [y, completedAugmentationNear] using Classical.choose_spec
      ((mem_completedAugmentationIdeal_iff p A W (x : completedRing p A W)).mp x.property n)
  have ha := Classical.choose_spec
    (completedRing_idealMap_exists_polynomial_approximation p A W y hy.1 n)
  refine ⟨ha.1, ?_⟩
  have hsum := (pAdicIdeal (A := completedRing p A W) p ^ n).add_mem hy.2 ha.2
  simpa [completedAugmentationRepresentative, completedAugmentationNear, y] using
    (show (x : completedRing p A W) - toCompletedRing p A W
        (Classical.choose (completedRing_idealMap_exists_polynomial_approximation
          p A W y hy.1 n)) ∈ _ by
      convert hsum using 1 ; ring)

private noncomputable def completedAugmentationRepSequence
    (x : completedAugmentationIdeal p A W) :
    AdicCompletion.AdicCauchySequence
      (pAdicIdeal (A := dividedPowerPolynomialRing A W) p)
      (augmentationIdeal A W) := by
  classical
  let J : Ideal (completedRing p A W) := pAdicIdeal p
  let rep := completedAugmentationRepresentative p A W x
  have rep_spec := completedAugmentationRepresentative_spec p A W x
  refine ⟨fun n => ⟨rep n, (rep_spec n).1⟩, ?_⟩
  intro m n hmn
  rw [SModEq.sub_mem]
  have hcloseM : (x : completedRing p A W) - toCompletedRing p A W (rep m) ∈ J ^ m :=
    (rep_spec m).2
  have hcloseN : (x : completedRing p A W) - toCompletedRing p A W (rep n) ∈ J ^ m :=
    (Ideal.pow_le_pow_right hmn) (rep_spec n).2
  have hmapdiff : toCompletedRing p A W (rep m - rep n) ∈ J ^ m := by
    have h := (J ^ m).sub_mem hcloseN hcloseM
    have heq : toCompletedRing p A W (rep m - rep n) =
        ((x : completedRing p A W) - toCompletedRing p A W (rep n)) -
          ((x : completedRing p A W) - toCompletedRing p A W (rep m)) := by
      simp only [map_sub]
      ring
    rw [heq]
    exact h
  have heval : AdicCompletion.evalₐ
      (pAdicIdeal (A := dividedPowerPolynomialRing A W) p) m
        (toCompletedRing p A W (rep m - rep n)) = 0 :=
    RingHom.mem_ker.mpr <| completedRing_eval_kills_pAdicPow p A W m hmapdiff
  have hpow : rep m - rep n ∈
    pAdicIdeal (A := dividedPowerPolynomialRing A W) p ^ m := by
    change AdicCompletion.evalₐ
      (pAdicIdeal (A := dividedPowerPolynomialRing A W) p) m
      (AdicCompletion.of
        (pAdicIdeal (A := dividedPowerPolynomialRing A W) p)
        (dividedPowerPolynomialRing A W) (rep m - rep n)) = 0 at heval
    rw [AdicCompletion.evalₐ_of] at heval
    exact Ideal.Quotient.eq_zero_iff_mem.mp heval
  have hdiffI : rep m - rep n ∈ augmentationIdeal A W :=
    (augmentationIdeal A W).sub_mem (rep_spec m).1 (rep_spec n).1
  have hsat := augmentationIdeal_pAdic_smul p A W hdiffI m hpow
  have hrel := (mem_ideal_smul_iff_subtype_mem_smul hdiffI).mp hsat
  have hsubseq : (⟨rep m, (rep_spec m).1⟩ : augmentationIdeal A W) -
      ⟨rep n, (rep_spec n).1⟩ = ⟨rep m - rep n, hdiffI⟩ := by
    apply Subtype.ext
    simp
  rw [hsubseq]
  exact hrel

private theorem completedAugmentationRepSequence_map_eq
    (x : completedAugmentationIdeal p A W) :
    AdicCompletion.map (pAdicIdeal (A := dividedPowerPolynomialRing A W) p)
      (augmentationIdeal A W).subtype
      (AdicCompletion.mk _ _ (completedAugmentationRepSequence p A W x)) =
        (x : completedRing p A W) := by
  classical
  let P := dividedPowerPolynomialRing A W
  let I : Ideal P := pAdicIdeal (A := P) p
  let c := completedAugmentationRepSequence p A W x
  have hcoord (e : ℕ) : (AdicCompletion.eval I P e) (x : completedRing p A W) =
      (I ^ e • (⊤ : Submodule P P)).mkQ
        (completedAugmentationRepresentative p A W x e) := by
    have hclose := (completedAugmentationRepresentative_spec p A W x e).2
    have hzero : AdicCompletion.evalₐ I e
        ((x : completedRing p A W) - toCompletedRing p A W
          (completedAugmentationRepresentative p A W x e)) = 0 := by
      apply RingHom.mem_ker.mpr
      exact completedRing_eval_kills_pAdicPow p A W e hclose
    have hEvalRep : AdicCompletion.evalₐ I e
        (toCompletedRing p A W (completedAugmentationRepresentative p A W x e)) =
          Ideal.Quotient.mk (I ^ e)
            (completedAugmentationRepresentative p A W x e) := by
      change AdicCompletion.evalₐ I e (AdicCompletion.of I P
        (completedAugmentationRepresentative p A W x e)) = _
      rw [AdicCompletion.evalₐ_of]
    rw [map_sub, hEvalRep, sub_eq_zero] at hzero
    have hfactor : I ^ e ≤ I ^ e • (⊤ : Submodule P P) := by
      rw [Ideal.smul_eq_mul, Ideal.mul_top]
    have h := congrArg (Ideal.Quotient.factor hfactor) hzero
    rw [AdicCompletion.factor_evalₐ_eq_eval I _ hfactor] at h
    simpa using h
  apply AdicCompletion.ext
  intro e
  change (AdicCompletion.map I (Submodule.subtype (augmentationIdeal A W))
      (AdicCompletion.mk I (augmentationIdeal A W) c)).val e = (x : completedRing p A W).val e
  rw [AdicCompletion.map_val_apply, AdicCompletion.mk_apply_coe]
  change (I ^ e • (⊤ : Submodule P P)).mkQ
      (completedAugmentationRepresentative p A W x e) = (x : completedRing p A W).val e
  have hc := hcoord e
  rw [AdicCompletion.eval_apply] at hc
  exact hc.symm

private theorem completedAugmentationMap_mk_mem
    (c : AdicCompletion.AdicCauchySequence
      (pAdicIdeal (A := dividedPowerPolynomialRing A W) p)
      (augmentationIdeal A W)) :
    AdicCompletion.map (pAdicIdeal
        (A := dividedPowerPolynomialRing A W) p)
        (augmentationIdeal A W).subtype
        (AdicCompletion.mk _ _ c) ∈ completedAugmentationIdeal p A W := by
  classical
  let P := dividedPowerPolynomialRing A W
  let I : Ideal P := pAdicIdeal (A := P) p
  apply (mem_completedAugmentationIdeal_iff p A W _).2
  intro e
  let y : completedRing p A W := toCompletedRing p A W (c e)
  refine ⟨y, Ideal.mem_map_of_mem _ (c e).property, ?_⟩
  let x := AdicCompletion.map I (augmentationIdeal A W).subtype
      (AdicCompletion.mk I (augmentationIdeal A W) c)
  have hEval : AdicCompletion.evalₐ I e x = Ideal.Quotient.mk (I ^ e) (c e : P) := by
    change AdicCompletion.evalₐ I e (AdicCompletion.map I
      (augmentationIdeal A W).subtype (AdicCompletion.mk I (augmentationIdeal A W) c)) = _
    rw [AdicCompletion.map_mk, AdicCompletion.evalₐ_mk]
    rfl
  have hEvalY : AdicCompletion.evalₐ I e y = Ideal.Quotient.mk (I ^ e) (c e : P) := by
    change AdicCompletion.evalₐ I e (AdicCompletion.of I P (c e)) = _
    rw [AdicCompletion.evalₐ_of]
  exact completedRing_mem_pAdicPow_of_eval_eq_zero p A W e _ (by
    rw [map_sub, hEval, hEvalY, sub_self])


private theorem augmentationIdeal_inf_isSubDPIdeal (e : ℕ) :
    (canonicalDividedPowers A W).IsSubDPIdeal
      (pAdicIdeal (A := dividedPowerPolynomialRing A W) p ^ e ⊓
        augmentationIdeal A W) := by
  refine ⟨inf_le_right, ?_⟩
  intro n hn x hx
  have hsat := augmentationIdeal_pAdic_smul p A W hx.2 e hx.1
  have hcont := dpow_congr_pAdic (augmentationIdeal A W)
    (canonicalDividedPowers A W) p n e (augmentationIdeal A W).zero_mem hx.2
    (by simpa using hsat)
  rw [(canonicalDividedPowers A W).dpow_eval_zero hn, sub_zero] at hcont
  refine ⟨?_, (canonicalDividedPowers A W).dpow_mem hn hx.2⟩
  have hle : pAdicIdeal (A := dividedPowerPolynomialRing A W) p ^ e •
      (augmentationIdeal A W : Submodule _ _) ≤
      pAdicIdeal (A := dividedPowerPolynomialRing A W) p ^ e •
        (⊤ : Submodule _ _) := smul_mono_right _ le_top
  simpa [Ideal.smul_eq_mul, Ideal.mul_top] using hle hcont

private def quotientAugmentationDividedPowers (e : ℕ) :=
  DividedPowers.Quotient.dividedPowers (canonicalDividedPowers A W)
    (augmentationIdeal_inf_isSubDPIdeal p A W e)

private def completedAugmentationDpow (n : ℕ) (x : completedRing p A W) :
    completedRing p A W := by
  classical
  exact if hx : x ∈ completedAugmentationIdeal p A W then
    AdicCompletion.mk _ _ (dividedPowerSequence (augmentationIdeal A W)
      (canonicalDividedPowers A W) p n (completedAugmentationRepSequence p A W ⟨x, hx⟩))
    else 0

private theorem completedAugmentationDpow_mem (n : ℕ) (hn : n ≠ 0)
    (x : completedRing p A W) (hx : x ∈ completedAugmentationIdeal p A W) :
    completedAugmentationDpow p A W n x ∈ completedAugmentationIdeal p A W := by
  classical
  rw [completedAugmentationDpow, dite_eq_left hx]
  rw [← map_dividedPowerSequenceInIdeal _ _ _ n hn]
  exact completedAugmentationMap_mk_mem p A W _

private theorem completedAugmentation_eval_mem (e : ℕ)
    (x : completedRing p A W) (hx : x ∈ completedAugmentationIdeal p A W) :
    AdicCompletion.evalₐ (pAdicIdeal p) e x ∈
      (augmentationIdeal A W).map (Ideal.Quotient.mk (pAdicIdeal p ^ e)) := by
  have h := completedAugmentationRepSequence_map_eq p A W ⟨x, hx⟩
  change _ = x at h
  rw [← h, AdicCompletion.map_mk, AdicCompletion.evalₐ_mk]
  exact Ideal.mem_map_of_mem _ (completedAugmentationRepSequence p A W ⟨x, hx⟩ e).property

private theorem completedAugmentationDpow_eval (n e : ℕ)
    (x : completedRing p A W) (hx : x ∈ completedAugmentationIdeal p A W) :
    AdicCompletion.evalₐ (pAdicIdeal p) e
      (completedAugmentationDpow p A W n x) =
      (quotientAugmentationDividedPowers p A W e).dpow n
        (AdicCompletion.evalₐ (pAdicIdeal p) e x) := by
  classical
  rw [completedAugmentationDpow, dite_eq_left hx, AdicCompletion.evalₐ_mk]
  have h := congrArg (AdicCompletion.evalₐ (pAdicIdeal p) e)
    (completedAugmentationRepSequence_map_eq p A W ⟨x, hx⟩)
  rw [AdicCompletion.map_mk, AdicCompletion.evalₐ_mk] at h
  rw [← h]
  exact (DividedPowers.Quotient.dpow_apply (canonicalDividedPowers A W)
    (augmentationIdeal_inf_isSubDPIdeal p A W e)
    (completedAugmentationRepSequence p A W ⟨x, hx⟩ e).property).symm

private def completedAugmentationDividedPowers :
    DividedPowers (completedAugmentationIdeal p A W) where
  dpow := completedAugmentationDpow p A W
  dpow_null := by
    intro n x hx
    simp [completedAugmentationDpow, hx]
  dpow_zero := by
    intro x hx
    apply AdicCompletion.ext_evalₐ
    intro e
    rw [completedAugmentationDpow_eval p A W 0 e x hx, map_one]
    exact (quotientAugmentationDividedPowers p A W e).dpow_zero
      (completedAugmentation_eval_mem p A W e x hx)
  dpow_one := by
    intro x hx
    apply AdicCompletion.ext_evalₐ
    intro e
    rw [completedAugmentationDpow_eval p A W 1 e x hx]
    exact (quotientAugmentationDividedPowers p A W e).dpow_one
      (completedAugmentation_eval_mem p A W e x hx)
  dpow_mem := by
    intro n x hn hx
    exact completedAugmentationDpow_mem p A W n hn x hx
  dpow_add := by
    intro n x y hx hy
    apply AdicCompletion.ext_evalₐ
    intro e
    rw [completedAugmentationDpow_eval p A W n e (x + y)
      ((completedAugmentationIdeal p A W).add_mem hx hy), map_add, map_sum]
    simp_rw [map_mul, completedAugmentationDpow_eval p A W _ e x hx,
      completedAugmentationDpow_eval p A W _ e y hy]
    exact (quotientAugmentationDividedPowers p A W e).dpow_add
      (completedAugmentation_eval_mem p A W e x hx)
      (completedAugmentation_eval_mem p A W e y hy)
  dpow_mul := by
    intro n a x hx
    apply AdicCompletion.ext_evalₐ
    intro e
    rw [completedAugmentationDpow_eval p A W n e (a * x)
      ((completedAugmentationIdeal p A W).mul_mem_left a hx)]
    rw [map_mul, map_mul, map_pow, completedAugmentationDpow_eval p A W n e x hx]
    exact (quotientAugmentationDividedPowers p A W e).dpow_mul
      (completedAugmentation_eval_mem p A W e x hx)
  mul_dpow := by
    intro m n x hx
    apply AdicCompletion.ext_evalₐ
    intro e
    simp_rw [map_mul, map_natCast, completedAugmentationDpow_eval p A W _ e x hx]
    exact (quotientAugmentationDividedPowers p A W e).mul_dpow
      (completedAugmentation_eval_mem p A W e x hx)
  dpow_comp := by
    intro m n x hn hx
    apply AdicCompletion.ext_evalₐ
    intro e
    rw [completedAugmentationDpow_eval p A W m e _
      (completedAugmentationDpow_mem p A W n hn x hx)]
    rw [map_mul, map_natCast, completedAugmentationDpow_eval p A W n e x hx,
      completedAugmentationDpow_eval p A W (m * n) e x hx]
    exact (quotientAugmentationDividedPowers p A W e).dpow_comp hn
      (completedAugmentation_eval_mem p A W e x hx)

/-- The canonical divided powers of `P` admit a continuous extension to the closure of its
augmentation ideal in `D`. -/
@[stacks 07LC "completed_exactness"]
public theorem exists_continuousDividedPowers :
    Nonempty (ContinuousDividedPowers p A W) := by
  refine ⟨⟨completedAugmentationDividedPowers p A W, ?_, ?_⟩⟩
  · intro n x hx xhat hhat
    apply AdicCompletion.ext_evalₐ
    intro e
    change AdicCompletion.evalₐ (pAdicIdeal p) e
      (completedAugmentationDpow p A W n xhat) = _
    rw [completedAugmentationDpow_eval p A W n e xhat xhat.property, hhat]
    exact DividedPowers.Quotient.dpow_apply (canonicalDividedPowers A W)
      (augmentationIdeal_inf_isSubDPIdeal p A W e) hx
  · intro n e x y hxy
    apply completedRing_mem_pAdicPow_of_eval_eq_zero p A W e
    change AdicCompletion.evalₐ (pAdicIdeal p) e
      (completedAugmentationDpow p A W n x - completedAugmentationDpow p A W n y) = 0
    rw [map_sub, completedAugmentationDpow_eval p A W n e x x.property,
      completedAugmentationDpow_eval p A W n e y y.property]
    have h := completedRing_eval_kills_pAdicPow p A W e hxy
    change AdicCompletion.evalₐ (pAdicIdeal p) e
      ((x : completedRing p A W) - (y : completedRing p A W)) = 0 at h
    rw [map_sub, sub_eq_zero] at h
    rw [h, sub_self]

private theorem completedRing_pAdic_isHausdorff :
    IsHausdorff (pAdicIdeal (A := completedRing p A W) p)
      (completedRing p A W) := by
  let P := dividedPowerPolynomialRing A W
  let I : Ideal P := pAdicIdeal (A := P) p
  let J : Ideal (completedRing p A W) := pAdicIdeal p
  have hsource : IsHausdorff I (completedRing p A W) := by
    dsimp [I, completedRing, P]
    infer_instance
  have hmap : Ideal.map (algebraMap P (completedRing p A W)) I = J := by
    simp [I, J, pAdicIdeal, Ideal.map_span]
  change IsHausdorff J (completedRing p A W)
  rw [← hmap]
  exact (IsHausdorff.map_algebraMap_iff (I := I) (S := completedRing p A W)
    (M := completedRing p A W)).2 hsource

/-- The continuous extension of the canonical divided powers is unique. -/
@[stacks 07LC "completed_exactness"]
public theorem continuousDividedPowers_unique
    (δ ε : ContinuousDividedPowers p A W) : δ = ε := by
  cases δ with
  | mk δ hδext hδcont =>
    cases ε with
    | mk ε hεext hεcont =>
      have hdp : δ = ε := by
        let := completedRing_pAdic_isHausdorff p A W
        apply DividedPowers.ext
        intro n x hx
        apply (IsHausdorff.eq_iff_smodEq
          (I := pAdicIdeal (A := completedRing p A W) p)).2
        intro e
        obtain ⟨y, hy, hxy⟩ := (mem_completedAugmentationIdeal_iff p A W x).mp hx e
        obtain ⟨z, hz, hzy⟩ :=
          completedRing_idealMap_exists_polynomial_approximation p A W y hy e
        let y' : completedAugmentationIdeal p A W :=
          ⟨toCompletedRing p A W z,
            (mem_completedAugmentationIdeal_iff p A W _).2 fun k =>
              ⟨toCompletedRing p A W z, Ideal.mem_map_of_mem _ hz, by simp⟩⟩
        let x' : completedAugmentationIdeal p A W := ⟨x, hx⟩
        have hxy' : (x : completedRing p A W) - (y' : completedRing p A W) ∈
            pAdicIdeal (A := completedRing p A W) p ^ e := by
          have hxysum := (pAdicIdeal (A := completedRing p A W) p ^ e).add_mem hxy hzy
          convert hxysum using 1 ; ring
        have hδ := hδcont n e x' y' hxy'
        have hε := hεcont n e x' y' hxy'
        have hδy : δ.dpow n (y' : completedRing p A W) =
            toCompletedRing p A W ((canonicalDividedPowers A W).dpow n z) :=
          hδext n z hz y' rfl
        have hεy : ε.dpow n (y' : completedRing p A W) =
            toCompletedRing p A W ((canonicalDividedPowers A W).dpow n z) :=
          hεext n z hz y' rfl
        have hdiff : δ.dpow n (x : completedRing p A W) -
            ε.dpow n (x : completedRing p A W) ∈
              pAdicIdeal (A := completedRing p A W) p ^ e := by
          have hsum :
              (δ.dpow n (x : completedRing p A W) - δ.dpow n (y' : completedRing p A W)) +
                (ε.dpow n (y' : completedRing p A W) - ε.dpow n (x : completedRing p A W)) ∈
                  pAdicIdeal (A := completedRing p A W) p ^ e :=
            (pAdicIdeal (A := completedRing p A W) p ^ e).add_mem hδ (by
              simpa [x'] using
                (pAdicIdeal (A := completedRing p A W) p ^ e).neg_mem hε)
          rw [hδy, hεy] at hsum
          convert hsum using 1 ; ring
        rw [SModEq.sub_mem]
        simpa [Ideal.smul_eq_mul, Ideal.mul_top] using hdiff
      subst ε
      rfl

end

end CompletedPoincare

end Crystalline

end
