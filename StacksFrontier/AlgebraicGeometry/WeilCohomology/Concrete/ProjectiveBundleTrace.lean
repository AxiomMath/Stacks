module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.BlowupPushforward
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.FirstChernClassSetup
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.BlowupTrace

/-!
# The candidate trace map of a projective bundle

Let (D0), (D1), (D2') be data satisfying axiom (A3), let `ℰ` be finite locally free of rank
`r + 1` on `X`, and let `p : P = 𝐏(ℰ) ⟶ X`, `ξ = c₁^H(𝒪_P(1))`. By (A3) every class of `H^*(P)`
is uniquely `∑_{i ≤ r} ξ^i ∪ p^*a_i`. For a linear map `∫_X` on `H^*(X)` the proof of Stacks
Lemma 0FIN uses the map

  `λ_P(∑_i ξ^i ∪ p^*a_i) = ∫_X(a_r)`

(`FirstChernClassData.bundleTrace`). This file develops its algebra:

* the abstract computation of the top coefficient of a cycle class map on a projective bundle,
  from the projective bundle formula and the projective space bundle formula for Chow groups
  (`eq_coeff_pushforward_of_sum_eq_coeff`);
* the projective bundle formula for `1 × p : P × P ⟶ P × X`, from (A3) for `p` and the Künneth
  isomorphisms of (A5) (`FirstChernClassData.prodBundleFormulaEquiv`);
* `(1 ⊗ λ_P)` read in the coordinates of that formula
  (`FirstChernClassData.tensorContractRight_bundleTrace_prodBundleFormulaEquiv`), and
  `λ_P(p^*b ∪ ∑ ξ^i ∪ p^*a_i) = ∫_X(b ∪ a_r)` (`FirstChernClassData.bundleTrace_pull_mul`).

## Main definitions

* `Stacks.WeilCohomology.FirstChernClassData.bundleFormulaEquiv`: (A3) as a linear equivalence.
* `Stacks.WeilCohomology.FirstChernClassData.bundleTrace`: the map `λ_P`.
* `Stacks.WeilCohomology.FirstChernClassData.prodBundleFormulaEquiv`: the formula for `P × P`.

## Main results

* `Stacks.WeilCohomology.eq_coeff_pushforward_of_sum_eq_coeff`.
* `FirstChernClassData.tensorContractRight_bundleTrace_prodBundleFormulaEquiv`.
* `Stacks.WeilCohomology.FirstChernClassData.bundleTrace_pull_mul`.

## References

* [Stacks Project, Tag 0FIN](https://stacks.math.columbia.edu/tag/0FIN)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry DirectSum
open scoped TensorProduct

universe u w

namespace Stacks.WeilCohomology

section TopCoefficient

variable {RQ RU AQ AU : Type*} [Ring RQ] [Ring RU] [Ring AQ] [Ring AU]
  (pullR : RU →+* RQ) (pushR : RQ →+ RU) (ΓQ : RQ →+* PowerSeries AQ)
  (ΓU : RU →+* PowerSeries AU) (pullA : AU →+* AQ) (D : RQ) (ξ : AQ) (n : ℕ)

omit [Ring AU] in
/-- `coeff_m((ξ X)^i f) = ξ^i coeff_{m-i}(f)` for `i ≤ m`, and `0` otherwise. -/
theorem coeff_monomial_one_pow_mul (i m : ℕ) (f : PowerSeries AQ) :
    PowerSeries.coeff m (PowerSeries.monomial 1 ξ ^ i * f) =
      if i ≤ m then ξ ^ i * PowerSeries.coeff (m - i) f else 0 := by
  have hpow : ∀ j : ℕ, PowerSeries.monomial 1 ξ ^ j = PowerSeries.monomial j (ξ ^ j) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ, ih, PowerSeries.monomial_mul_monomial, pow_succ]
  have hC : PowerSeries.monomial i (ξ ^ i) = PowerSeries.C (ξ ^ i) * PowerSeries.X ^ i := by
    rw [PowerSeries.X_pow_eq, ← PowerSeries.monomial_zero_eq_C_apply,
      PowerSeries.monomial_mul_monomial, zero_add, mul_one]
  rw [hpow, hC, mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
  split_ifs <;> simp

/-- **The top coefficient of the cycle class on a projective bundle**, abstractly. Let `D ∈ R_Q`
span `R_Q` over `q^! R_U` in degrees `≤ n` and push forward to `δ_{i,n}`, let `q_*` satisfy the
projection formula, and let `Γ` be compatible with pullback and send `D` to `ξ` in degree one.
If the classes `ξ^i ∪ q^*(-)` are independent in `H_Q ⊇ A_Q`, then the coefficient of `ξ^n` in
the degree `m` part of `Γ(x)` is the degree `m - n` part of `Γ(q_* x)`. -/
theorem eq_coeff_pushforward_of_sum_eq_coeff {HQ HU : Type*} [Ring HQ] [Ring HU]
    (ιQ : AQ →+* HQ) (ιU : AU →+* HU) (pullH : HU →+* HQ)
    (hι : ∀ a, pullH (ιU a) = ιQ (pullA a))
    (hproj : ∀ x y, pushR (x * pullR y) = pushR x * y)
    (hpush : ∀ i : Fin (n + 1), pushR (D ^ (i : ℕ)) = if i = Fin.last n then 1 else 0)
    (hspan : ∀ x, ∃ y : Fin (n + 1) → RU, x = ∑ i : Fin (n + 1), D ^ (i : ℕ) * pullR (y i))
    (hΓpull : ∀ y, ΓQ (pullR y) = PowerSeries.map pullA (ΓU y))
    (hΓD : ΓQ D = PowerSeries.monomial 1 ξ)
    (hinj : Function.Injective
      (fun a : Fin (n + 1) → HU => ∑ i : Fin (n + 1), ιQ ξ ^ (i : ℕ) * pullH (a i)))
    (x : RQ) (m : ℕ) (a : Fin (n + 1) → HU)
    (ha : ∑ i : Fin (n + 1), ιQ ξ ^ (i : ℕ) * pullH (a i) = ιQ (PowerSeries.coeff m (ΓQ x))) :
    a (Fin.last n) = ιU (if n ≤ m then PowerSeries.coeff (m - n) (ΓU (pushR x)) else 0) := by
  classical
  obtain ⟨y, rfl⟩ := hspan x
  set a' : Fin (n + 1) → AU := fun i =>
    if (i : ℕ) ≤ m then PowerSeries.coeff (m - i) (ΓU (y i)) else 0 with ha'
  have hcoeff : PowerSeries.coeff m (ΓQ (∑ i : Fin (n + 1), D ^ (i : ℕ) * pullR (y i))) =
      ∑ i : Fin (n + 1), ξ ^ (i : ℕ) * pullA (a' i) := by
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_pow, hΓD, hΓpull, coeff_monomial_one_pow_mul]
    simp only [ha']
    split_ifs <;> simp [PowerSeries.coeff_map]
  have heq : a = fun i => ιU (a' i) := hinj (by
    refine ha.trans ?_
    rw [hcoeff, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_pow, hι])
  have hpushx : pushR (∑ i : Fin (n + 1), D ^ (i : ℕ) * pullR (y i)) = y (Fin.last n) := by
    rw [map_sum, Fintype.sum_eq_single (Fin.last n)]
    · rw [hproj, hpush, ite_eq_left rfl, one_mul]
    · intro i hi
      rw [hproj, hpush, ite_eq_right hi, zero_mul]
  rw [heq, hpushx, ha']
  simp only [Fin.val_last]

end TopCoefficient

section Contraction

variable {F : Type*} [Field F] {A A' B B' : Type*} [AddCommGroup A] [Module F A]
  [AddCommGroup A'] [Module F A'] [AddCommGroup B] [Module F B] [AddCommGroup B'] [Module F B']

/-- Contraction of a sum of tensor maps. -/
theorem tensorContractRight_sum_map {ι : Type*} (s : Finset ι) (U : ι → A →ₗ[F] A')
    (M : ι → B →ₗ[F] B') (μ : B' →ₗ[F] F) (η : A ⊗[F] B) :
    tensorContractRight μ (∑ i ∈ s, TensorProduct.map (U i) (M i) η) =
      ∑ i ∈ s, U i (tensorContractRight (μ ∘ₗ M i) η) := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => tensorContractRight_map _ _ _ _

/-- Contraction against `0` vanishes. -/
theorem tensorContractRight_zero (η : A ⊗[F] B) :
    tensorContractRight (0 : B →ₗ[F] F) η = 0 := by
  simp [tensorContractRight]

end Contraction

namespace FirstChernClassData

open SmoothProjectiveScheme

variable {k : Type u} [Field k] {F : Type w} [Field F] (𝔇 : FirstChernClassData k F)
  (X : (SmoothProjectiveScheme k).FullSubcategory) (E : ((toScheme k).obj X).Modules) (r : ℕ)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1)]

/-- `a ↦ ξ^i ∪ p^*a`, with `ξ = c₁^H(𝒪_P(1))` in coordinates. -/
def bundleCupPull (i : ℕ) : 𝔇.H X →ₗ[F] 𝔇.H (bundle X E r) :=
  LinearMap.mulLeft F (𝔇.bundleClassU X E r ^ i) ∘ₗ (𝔇.pull (bundleProj X E r)).toLinearMap

/-- `bundleCupPull i a` is `ξ^i * p^*a`. -/
theorem bundleCupPull_apply (i : ℕ) (a : 𝔇.H X) :
    𝔇.bundleCupPull X E r i a = 𝔇.bundleClassU X E r ^ i * 𝔇.pull (bundleProj X E r) a := rfl

/-- `bundleCupPull i (x * a) = bundleCupPull i x * p^*a`. -/
theorem bundleCupPull_mul (i : ℕ) (x a : 𝔇.H X) :
    𝔇.bundleCupPull X E r i (x * a) =
      𝔇.bundleCupPull X E r i x * 𝔇.pull (bundleProj X E r) a := by
  simp [bundleCupPull_apply, map_mul, mul_assoc]

/-- The projective bundle formula as a linear map `H^*(X)^{r+1} → H^*(P)`. -/
def bundleFormulaLin : (Fin (r + 1) → 𝔇.H X) →ₗ[F] 𝔇.H (bundle X E r) :=
  ∑ i : Fin (r + 1), 𝔇.bundleCupPull X E r i ∘ₗ LinearMap.proj i

/-- `bundleFormulaLin a = ∑ i, ξ^i * p^*(a i)`. -/
theorem bundleFormulaLin_apply (a : Fin (r + 1) → 𝔇.H X) :
    𝔇.bundleFormulaLin X E r a =
      ∑ i : Fin (r + 1), 𝔇.bundleClassU X E r ^ (i : ℕ) * 𝔇.pull (bundleProj X E r) (a i) := by
  simp [bundleFormulaLin, bundleCupPull_apply]

/-- On `Pi.single i a`, `bundleFormulaLin` is `bundleCupPull i a`. -/
theorem bundleFormulaLin_single (i : Fin (r + 1)) (a : 𝔇.H X) :
    𝔇.bundleFormulaLin X E r (Pi.single i a) = 𝔇.bundleCupPull X E r i a := by
  classical
  rw [bundleFormulaLin_apply, Fintype.sum_eq_single i]
  · rw [Pi.single_eq_same, bundleCupPull_apply]
  · intro j hj
    rw [Pi.single_eq_of_ne hj, map_zero, mul_zero]

/-- Axiom (A3) as a linear equivalence. -/
def bundleFormulaEquiv (hA3 : 𝔇.ProjectiveBundleAxiom) :
    (Fin (r + 1) → 𝔇.H X) ≃ₗ[F] 𝔇.H (bundle X E r) :=
  LinearEquiv.ofBijective (𝔇.bundleFormulaLin X E r) (by
    have h := 𝔇.bijective_bundleFormulaU hA3 X E r
    convert h using 1
    funext a
    exact 𝔇.bundleFormulaLin_apply X E r a)

/-- The underlying map of `bundleFormulaEquiv` is `bundleFormulaLin`. -/
theorem bundleFormulaEquiv_apply (hA3 : 𝔇.ProjectiveBundleAxiom) (a : Fin (r + 1) → 𝔇.H X) :
    𝔇.bundleFormulaEquiv X E r hA3 a = 𝔇.bundleFormulaLin X E r a := rfl

/-- **The candidate trace of the projective bundle**:
`λ_P(∑ ξ^i ∪ p^*a_i) = ∫_X(a_r)`, read through axiom (A3). -/
def bundleTrace (hA3 : 𝔇.ProjectiveBundleAxiom) (intX : 𝔇.H X →ₗ[F] F) :
    𝔇.H (bundle X E r) →ₗ[F] F :=
  intX ∘ₗ LinearMap.proj (Fin.last r) ∘ₗ (𝔇.bundleFormulaEquiv X E r hA3).symm.toLinearMap

/-- `bundleTrace (∑ i, ξ^i * p^*(a i)) = intX (a r)`. -/
theorem bundleTrace_bundleFormula (hA3 : 𝔇.ProjectiveBundleAxiom) (intX : 𝔇.H X →ₗ[F] F)
    (a : Fin (r + 1) → 𝔇.H X) :
    𝔇.bundleTrace X E r hA3 intX (𝔇.bundleFormulaLin X E r a) = intX (a (Fin.last r)) := by
  rw [bundleTrace, ← bundleFormulaEquiv_apply _ _ _ _ hA3]
  simp

/-- `bundleTrace ∘ bundleCupPull i` is `intX` for `i = r` and `0` otherwise. -/
theorem bundleTrace_comp_bundleCupPull (hA3 : 𝔇.ProjectiveBundleAxiom) (intX : 𝔇.H X →ₗ[F] F)
    (i : Fin (r + 1)) :
    𝔇.bundleTrace X E r hA3 intX ∘ₗ 𝔇.bundleCupPull X E r i =
      if i = Fin.last r then intX else 0 := by
  classical
  ext a
  rw [LinearMap.comp_apply, ← bundleFormulaLin_single, bundleTrace_bundleFormula]
  split_ifs with h
  · subst h
    rw [Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne (Ne.symm h), map_zero, LinearMap.zero_apply]

/-- A power of a class of degree `2` has degree `2 * n`. -/
private theorem pow_mem_grade_two_mul {Y : (SmoothProjectiveScheme k).FullSubcategory}
    {x : 𝔇.H Y} (hx : x ∈ 𝔇.grade Y 2) (n : ℕ) : x ^ n ∈ 𝔇.grade Y (2 * (n : ℤ)) := by
  have := SetLike.pow_mem_graded n hx
  rwa [nsmul_eq_mul, mul_comm] at this

/-- The coefficients of a class of degree `m` under axiom (A3) are homogeneous: the `i`-th one has
degree `m - 2i`. -/
theorem bundleFormulaEquiv_symm_mem (hA3 : 𝔇.ProjectiveBundleAxiom) {m : ℤ}
    {y : 𝔇.H (bundle X E r)} (hy : y ∈ 𝔇.grade (bundle X E r) m) (i : Fin (r + 1)) :
    (𝔇.bundleFormulaEquiv X E r hA3).symm y i ∈ 𝔇.grade X (m - 2 * (i : ℕ)) := by
  classical
  set b := (𝔇.bundleFormulaEquiv X E r hA3).symm y with hb
  let b' : Fin (r + 1) → 𝔇.H X := fun j => decompose (𝔇.grade X) (b j) (m - 2 * (j : ℕ))
  have hyb : 𝔇.bundleFormulaLin X E r b = y := by
    rw [← bundleFormulaEquiv_apply _ _ _ _ hA3, hb, LinearEquiv.apply_symm_apply]
  have hb' : 𝔇.bundleFormulaLin X E r b' = y := by
    have h := congrArg (fun z => (decompose (𝔇.grade (bundle X E r)) z m : 𝔇.H (bundle X E r)))
      hyb
    simp only at h
    rw [decompose_of_mem_same _ hy, bundleFormulaLin_apply, decompose_sum,
      DFinsupp.finsetSum_apply, Submodule.coe_sum] at h
    rw [← h, bundleFormulaLin_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hdeg : m = 2 * ((j : ℕ) : ℤ) + (m - 2 * (j : ℕ)) := by ring
    conv_rhs => rw [hdeg]
    rw [coe_decompose_mul_add_of_left_mem (𝔇.grade (bundle X E r))
      (pow_mem_grade_two_mul 𝔇 (𝔇.bundleClassU_mem X E r) j),
      decompose_map (𝔇.grade X) (𝔇.grade (bundle X E r)) (𝔇.pull (bundleProj X E r))
        (𝔇.pull_grade _)]
  have : b' = b := (𝔇.bundleFormulaEquiv X E r hA3).injective (by
    rw [bundleFormulaEquiv_apply, bundleFormulaEquiv_apply, hb', hyb])
  rw [← this]
  exact (decompose (𝔇.grade X) (b i) _).2

/-- If `∫_X` vanishes off degree `N`, the candidate trace vanishes off degree `N + 2r`. -/
theorem bundleTrace_eq_zero_of_mem (hA3 : 𝔇.ProjectiveBundleAxiom) (intX : 𝔇.H X →ₗ[F] F)
    (N : ℤ) (hint : ∀ m, m ≠ N → ∀ a ∈ 𝔇.grade X m, intX a = 0) {m : ℤ} (hm : m ≠ N + 2 * r)
    {y : 𝔇.H (bundle X E r)} (hy : y ∈ 𝔇.grade (bundle X E r) m) :
    𝔇.bundleTrace X E r hA3 intX y = 0 := by
  have hmem := 𝔇.bundleFormulaEquiv_symm_mem X E r hA3 hy (Fin.last r)
  exact hint _ (by simp only [Fin.val_last]; omega) _ hmem

/-! ### The projective bundle `P × P ⟶ P × X` -/

section ProductBundle

variable (hA5 : 𝔇.KunnethAxiom) (hA3 : 𝔇.ProjectiveBundleAxiom)

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank E (r + 1)] in
/-- A class of even degree commutes with every class. -/
theorem commute_of_mem_grade_two_mul {Y : (SmoothProjectiveScheme k).FullSubcategory} {i : ℤ}
    {x : 𝔇.H Y} (hx : x ∈ 𝔇.grade Y (2 * i)) (y : 𝔇.H Y) : x * y = y * x := by
  classical
  rw [← DirectSum.sum_support_decompose (𝔇.grade Y) y, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [𝔇.graded_comm Y (2 * i) j x _ hx (Submodule.coe_mem _)]
  have : Int.negOnePow (2 * i * j) = 1 := by
    rw [mul_assoc, Int.negOnePow_two_mul]
  rw [this]
  simp

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank E (r + 1)] in
/-- The `i`-th component of `(piRight)⁻¹ s` is `s i`. -/
theorem lTensor_proj_piRight_symm {ι : Type*} [Fintype ι] [DecidableEq ι] {N M : Type*}
    [AddCommGroup N] [Module F N] [AddCommGroup M] [Module F M] (s : ι → N ⊗[F] M) (i : ι) :
    LinearMap.lTensor N (LinearMap.proj i) ((TensorProduct.piRight F F N fun _ : ι => M).symm s) =
      s i := by
  set x := (TensorProduct.piRight F F N fun _ : ι => M).symm s with hx
  have hs : s = TensorProduct.piRight F F N (fun _ : ι => M) x := by
    rw [hx, LinearEquiv.apply_symm_apply]
  rw [hs]
  clear hs hx
  induction x using TensorProduct.inductionOn with
  | tmul a b => simp
  | add a b ha hb => rw [map_add, ha, hb, map_add, Pi.add_apply]

/-- **The projective bundle formula for `1 × p : P × P ⟶ P × X`**, from (A3) for `p` and the
Künneth isomorphisms (A5): `(w_i) ↦ ∑_i pr₂^*ξ^i ∪ (1 × p)^*w_i` is an isomorphism
`H^*(P × X)^{r+1} ≅ H^*(P × P)`. -/
def prodBundleFormulaEquiv :
    (Fin (r + 1) → 𝔇.H (prod (bundle X E r) X)) ≃ₗ[F] 𝔇.H (prod (bundle X E r) (bundle X E r)) :=
  (LinearEquiv.piCongrRight fun _ => (𝔇.kunnethEquiv hA5 (bundle X E r) X).symm) ≪≫ₗ
    (TensorProduct.piRight F F (𝔇.H (bundle X E r)) fun _ : Fin (r + 1) => 𝔇.H X).symm ≪≫ₗ
    (𝔇.bundleFormulaEquiv X E r hA3).lTensor (𝔇.H (bundle X E r)) ≪≫ₗ
    𝔇.kunnethEquiv hA5 (bundle X E r) (bundle X E r)

/-- `prodBundleFormulaEquiv` read through the Künneth isomorphisms. -/
theorem symm_kunnethEquiv_prodBundleFormulaEquiv
    (w : Fin (r + 1) → 𝔇.H (prod (bundle X E r) X)) :
    (𝔇.kunnethEquiv hA5 (bundle X E r) (bundle X E r)).symm
        (𝔇.prodBundleFormulaEquiv X E r hA5 hA3 w) =
      ∑ i : Fin (r + 1), TensorProduct.map LinearMap.id (𝔇.bundleCupPull X E r i)
        ((𝔇.kunnethEquiv hA5 (bundle X E r) X).symm (w i)) := by
  classical
  change (𝔇.kunnethEquiv hA5 (bundle X E r) (bundle X E r)).symm
      (𝔇.kunnethEquiv hA5 (bundle X E r) (bundle X E r)
        (LinearMap.lTensor (𝔇.H (bundle X E r)) (𝔇.bundleFormulaLin X E r)
          ((TensorProduct.piRight F F (𝔇.H (bundle X E r)) fun _ : Fin (r + 1) => 𝔇.H X).symm
            fun i => (𝔇.kunnethEquiv hA5 (bundle X E r) X).symm (w i)))) = _
  rw [LinearEquiv.symm_apply_apply]
  unfold bundleFormulaLin
  have hsum : ∀ (t : Finset (Fin (r + 1))) (f : Fin (r + 1) → ((Fin (r + 1) → 𝔇.H X) →ₗ[F]
      𝔇.H (bundle X E r))), LinearMap.lTensor (𝔇.H (bundle X E r)) (∑ i ∈ t, f i) =
        ∑ i ∈ t, LinearMap.lTensor (𝔇.H (bundle X E r)) (f i) := by
    intro t f
    induction t using Finset.induction_on with
    | empty => simp
    | insert j t hj ih => rw [Finset.sum_insert hj, LinearMap.lTensor_add, ih, Finset.sum_insert hj]
  rw [hsum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.lTensor_comp, LinearMap.comp_apply, lTensor_proj_piRight_symm]
  rfl

/-- `prodBundleFormulaEquiv` is `(w_i) ↦ ∑_i pr₂^*ξ^i ∪ (1 × p)^*w_i`. -/
theorem prodBundleFormulaEquiv_apply (w : Fin (r + 1) → 𝔇.H (prod (bundle X E r) X)) :
    𝔇.prodBundleFormulaEquiv X E r hA5 hA3 w =
      ∑ i : Fin (r + 1),
        𝔇.pull (snd (bundle X E r) (bundle X E r)) (𝔇.bundleClassU X E r) ^ (i : ℕ) *
        𝔇.pull (prodMap (𝟙 (bundle X E r)) (bundleProj X E r)) (w i) := by
  rw [← (𝔇.kunnethEquiv hA5 (bundle X E r) (bundle X E r)).apply_symm_apply
    (𝔇.prodBundleFormulaEquiv X E r hA5 hA3 w), symm_kunnethEquiv_prodBundleFormulaEquiv, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => rw [← (𝔇.kunnethEquiv hA5 (bundle X E r) X).apply_symm_apply (w i)]
  generalize (𝔇.kunnethEquiv hA5 (bundle X E r) X).symm (w i) = t
  have hξ : 𝔇.pull (snd (bundle X E r) (bundle X E r)) (𝔇.bundleClassU X E r) ^ (i : ℕ) ∈
      𝔇.grade (prod (bundle X E r) (bundle X E r)) (2 * (i : ℕ)) := by
    exact pow_mem_grade_two_mul 𝔇
      (𝔇.pull_grade (snd (bundle X E r) (bundle X E r)) 2 _ (𝔇.bundleClassU_mem X E r)) i
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
    have hK : ∀ {Y Z : (SmoothProjectiveScheme k).FullSubcategory} (u : 𝔇.H Y ⊗[F] 𝔇.H Z),
        𝔇.kunnethEquiv hA5 Y Z u = 𝔇.kunnethMap Y Z u := fun _ => rfl
    rw [hK, hK, pull_prodMap_kunnethMap, TensorProduct.map_tmul, TensorProduct.map_tmul,
      kunnethMap_tmul, kunnethMap_tmul, LinearMap.id_apply, bundleCupPull_apply,
      AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply, pull_id, AlgHom.id_apply, map_mul,
      map_pow, ← mul_assoc, (𝔇.commute_of_mem_grade_two_mul hξ _).symm, mul_assoc]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add, mul_add]

/-- **The contraction against the candidate trace of `P`**, in the coordinates of
`prodBundleFormulaEquiv`: `(1 ⊗ λ_P)(∑ pr₂^*ξ^i ∪ (1 × p)^*w_i) = (1 ⊗ ∫_X)(w_r)`. -/
theorem tensorContractRight_bundleTrace_prodBundleFormulaEquiv (intX : 𝔇.H X →ₗ[F] F)
    (w : Fin (r + 1) → 𝔇.H (prod (bundle X E r) X)) :
    tensorContractRight (𝔇.bundleTrace X E r hA3 intX)
        ((𝔇.kunnethEquiv hA5 (bundle X E r) (bundle X E r)).symm
          (𝔇.prodBundleFormulaEquiv X E r hA5 hA3 w)) =
      tensorContractRight intX ((𝔇.kunnethEquiv hA5 (bundle X E r) X).symm (w (Fin.last r))) := by
  classical
  rw [symm_kunnethEquiv_prodBundleFormulaEquiv, map_sum, Fintype.sum_eq_single (Fin.last r)]
  · rw [tensorContractRight_map, bundleTrace_comp_bundleCupPull, ite_eq_left rfl]
    rfl
  · intro i hi
    rw [tensorContractRight_map, bundleTrace_comp_bundleCupPull, ite_eq_right hi,
      tensorContractRight_zero, map_zero]

/-- The class `c₁^H(𝒪_P(1))^i` has even degree. -/
theorem bundleClassU_pow_mem (i : ℕ) :
    𝔇.bundleClassU X E r ^ i ∈ 𝔇.grade (bundle X E r) (2 * (i : ℤ)) := by
  exact pow_mem_grade_two_mul 𝔇 (𝔇.bundleClassU_mem X E r) i

/-- `λ_P(p^*b ∪ (∑ ξ^i ∪ p^*a_i)) = ∫_X(b ∪ a_r)`. -/
theorem bundleTrace_pull_mul (intX : 𝔇.H X →ₗ[F] F) (b : 𝔇.H X) (a : Fin (r + 1) → 𝔇.H X) :
    𝔇.bundleTrace X E r hA3 intX (𝔇.pull (bundleProj X E r) b * 𝔇.bundleFormulaLin X E r a) =
      intX (b * a (Fin.last r)) := by
  have : 𝔇.pull (bundleProj X E r) b * 𝔇.bundleFormulaLin X E r a =
      𝔇.bundleFormulaLin X E r (fun i => b * a i) := by
    rw [bundleFormulaLin_apply, bundleFormulaLin_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_assoc, (𝔇.commute_of_mem_grade_two_mul (bundleClassU_pow_mem 𝔇 X E r i) _).symm,
      mul_assoc, map_mul]
  rw [this, bundleTrace_bundleFormula]

end ProductBundle

end FirstChernClassData

end Stacks.WeilCohomology

end
