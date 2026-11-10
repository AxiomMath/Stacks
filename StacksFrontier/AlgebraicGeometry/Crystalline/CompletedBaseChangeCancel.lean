module

public import Mathlib.RingTheory.AdicCompletion.Completeness
public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedConnectionBaseChange
public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedDeRhamPerturbation
public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedTensorCancelBaseChange
public import StacksFrontier.AlgebraicGeometry.Crystalline.ModuleDifferentials.CompletionFormsBijective

/-!
# The base-change form and the pushed form of a completed de Rham complex

Let `D → D'` be a ring map, `(M, ∇)` a `D`-module with a completed connection, and `Ω'^*` the
forms of `D'`.  There are two ways to write "the de Rham complex of `M` over `D'`":

* the **base-change form** `M' ⊗^∧_{D'} Ω'^*`, with `M' = (D' ⊗_D M)^∧` and the base-changed
  connection `Crystalline.CompletedConnection.baseChange`;
* the **pushed form** `M ⊗^∧_D Ω'^*`, with the connection `∇` pushed into `Ω'^1` along the
  comparison of forms, `Crystalline.CompletedDeRham.pushforwardConnection`.

The proof of [Stacks, Proposition 60.21.3, Tag 07LG] needs the first (it is the row of its double
complex) and [Stacks, Lemma 60.21.2, Tag 07LD] is proved in the library in the second.  This
module identifies them.

## Main definitions and results

* `Crystalline.completionTensorEquiv` — completing a module first does not change a completed
  tensor product: `(X^∧ ⊗ Ω)^∧ ≅ (X ⊗ Ω)^∧`.
* `Crystalline.completedBaseChangeCancel` — **`M' ⊗̂_{D'} Ω ≅ M ⊗̂_D Ω`**, pinned by
  `(d ⊗ m) ⊗ ω ↦ m ⊗ d ω` (`Crystalline.completedBaseChangeCancel_of_tmul`).
* `Crystalline.completedBaseChangeCancel_differential` — **it carries the de Rham differential of
  the base-changed connection to that of the pushed connection.**
* `Crystalline.completedBaseChangeCancel_baseChangeTerm` — it carries the base change map
  `m ⊗ ω ↦ (1 ⊗ m) ⊗ ψ ω` to `1_M ⊗ ψ`.

## References

* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Lemma 60.21.2, Tag 07LD](https://stacks.math.columbia.edu/tag/07LD)
-/

@[expose] public noncomputable section

open DividedPowers
open scoped TensorProduct Pointwise

universe u

namespace Crystalline

/-! ### Additive maps between `p`-adic completions are local at the levels -/

section Levels

/-- **An element of a `p`-adic completion vanishing at the level `k` is `p^k` times an element.**
-/
theorem exists_eq_pow_smul_of_val_eq_zero (p : ℕ) {R : Type*} [CommRing R] {X : Type*}
    [AddCommGroup X] [Module R X] (k : ℕ) (x : AdicCompletion (pAdicIdeal (A := R) p) X)
    (hx : x.val k = 0) : ∃ z, x = ((p : R) ^ k) • z := by
  have hmem : x ∈ (pAdicIdeal (A := R) p) ^ k •
      (⊤ : Submodule R (AdicCompletion (pAdicIdeal (A := R) p) X)) := by
    rw [AdicCompletion.pow_smul_top_eq_ker_eval (Submodule.fg_span_singleton _),
      LinearMap.mem_ker]
    exact hx
  have hmem' : x ∈ ((p : R) ^ k) •
      (⊤ : Submodule R (AdicCompletion (pAdicIdeal (A := R) p) X)) := by
    rw [← Submodule.ideal_span_singleton_smul, ← Ideal.span_singleton_pow]
    exact hmem
  obtain ⟨z, -, hz⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hmem'
  exact ⟨z, hz.symm⟩

/-- `p^k` times an element of a `p`-adic completion vanishes at the level `k`. -/
theorem val_pow_smul_eq_zero (p : ℕ) {R : Type*} [CommRing R] {X : Type*} [AddCommGroup X]
    [Module R X] (k : ℕ) (z : AdicCompletion (pAdicIdeal (A := R) p) X) :
    (((p : R) ^ k) • z).val k = 0 := by
  have hmem : ((p : R) ^ k) • z ∈ (pAdicIdeal (A := R) p) ^ k •
      (⊤ : Submodule R (AdicCompletion (pAdicIdeal (A := R) p) X)) :=
    Submodule.smul_mem_smul (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) k)
      Submodule.mem_top
  rw [AdicCompletion.pow_smul_top_eq_ker_eval (Submodule.fg_span_singleton _),
    LinearMap.mem_ker] at hmem
  exact hmem

/-- **Every additive map between `p`-adic completions is local at the levels**: the level-`k`
value of the image depends only on the level-`k` value of the argument.  A difference vanishing at
the level `k` is `p^k` times an element, an additive map commutes with multiplication by the
integer `p^k`, and `p^k` times anything vanishes at the level `k`. -/
theorem addMonoidHom_val_congr (p : ℕ) {R S : Type*} [CommRing R] [CommRing S] {X Y : Type*}
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module S Y]
    (f : AdicCompletion (pAdicIdeal (A := R) p) X →+ AdicCompletion (pAdicIdeal (A := S) p) Y)
    (k : ℕ) {x y : AdicCompletion (pAdicIdeal (A := R) p) X} (h : x.val k = y.val k) :
    (f x).val k = (f y).val k := by
  obtain ⟨z, hz⟩ := exists_eq_pow_smul_of_val_eq_zero p k (x - y)
    (by rw [AdicCompletion.val_sub_apply, h, sub_self])
  have hfz : f x - f y = ((p : S) ^ k) • f z := by
    rw [← map_sub, hz, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, map_nsmul,
      ← Nat.cast_smul_eq_nsmul S,
      Nat.cast_pow]
  rw [← sub_eq_zero, ← AdicCompletion.val_sub_apply, hfz, val_pow_smul_eq_zero]

end Levels

/-! ### Completing a module first does not change a completed tensor product -/

section CompletionTensor

variable (p : ℕ) {R : Type*} [CommRing R] (X : Type*) [AddCommGroup X] [Module R X]
  (Ω : Type*) [AddCommGroup Ω] [Module R Ω]

local notation "Ip" => pAdicIdeal (A := R) p

/-- The map `X ⊗ Ω → X^∧ ⊗ Ω` induced by the completion of `X`. -/
def completionTensorMap : X ⊗[R] Ω →ₗ[R] AdicCompletion Ip X ⊗[R] Ω :=
  TensorProduct.map (AdicCompletion.of Ip X) LinearMap.id

/-- The bilinear map `X × Ω → (X ⊗ Ω) / p^k` killing `p^k X` in the first variable. -/
def completionTensorLevelBilin (k : ℕ) :
    X ⧸ (Ip ^ k • (⊤ : Submodule R X)) →ₗ[R] Ω →ₗ[R]
      (X ⊗[R] Ω) ⧸ (Ip ^ k • (⊤ : Submodule R (X ⊗[R] Ω))) :=
  (Ip ^ k • (⊤ : Submodule R X)).liftQ
    ((TensorProduct.mk R X Ω).compr₂ (Ip ^ k • (⊤ : Submodule R (X ⊗[R] Ω))).mkQ)
    (by
      intro x hx
      refine Submodule.smul_induction_on hx (fun a ha x _ => ?_) (fun x y hx hy => ?_)
      · refine LinearMap.ext fun ω => ?_
        change (Ip ^ k • (⊤ : Submodule R (X ⊗[R] Ω))).mkQ ((a • x) ⊗ₜ ω) = 0
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, ← TensorProduct.smul_tmul']
        exact Submodule.smul_mem_smul ha Submodule.mem_top
      · rw [LinearMap.mem_ker] at hx hy ⊢
        rw [map_add, hx, hy, add_zero])

/-- The level-`k` inverse `X^∧ ⊗ Ω → (X ⊗ Ω) / p^k`, sending `x̂ ⊗ ω` to the class of `x ⊗ ω`
for any `x` agreeing with `x̂` at the level `k`. -/
def completionTensorLevelInv (k : ℕ) :
    AdicCompletion Ip X ⊗[R] Ω →ₗ[R] (X ⊗[R] Ω) ⧸ (Ip ^ k • (⊤ : Submodule R (X ⊗[R] Ω))) :=
  TensorProduct.lift ((completionTensorLevelBilin p X Ω k).comp (AdicCompletion.eval Ip X k))

/-- The level-`k` inverse kills `p^k (X^∧ ⊗ Ω)`, so it descends to the quotient. -/
def completionTensorLevelInvQ (k : ℕ) :
    (AdicCompletion Ip X ⊗[R] Ω) ⧸ (Ip ^ k • (⊤ : Submodule R (AdicCompletion Ip X ⊗[R] Ω))) →ₗ[R]
      (X ⊗[R] Ω) ⧸ (Ip ^ k • (⊤ : Submodule R (X ⊗[R] Ω))) :=
  (Ip ^ k • (⊤ : Submodule R (AdicCompletion Ip X ⊗[R] Ω))).liftQ
    (completionTensorLevelInv p X Ω k)
    (by
      intro x hx
      refine Submodule.smul_induction_on hx (fun a ha x _ => ?_) (fun x y hx hy => ?_)
      · rw [LinearMap.mem_ker, map_smul]
        obtain ⟨q, hq⟩ := Submodule.mkQ_surjective
          (Ip ^ k • (⊤ : Submodule R (X ⊗[R] Ω))) (completionTensorLevelInv p X Ω k x)
        rw [← hq, Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
        exact Submodule.smul_mem_smul ha Submodule.mem_top
      · rw [LinearMap.mem_ker] at hx hy ⊢
        rw [map_add, hx, hy, add_zero])

/-- The level-`k` inverse is a left inverse of the map `(X ⊗ Ω) / p^k → (X^∧ ⊗ Ω) / p^k` induced
by `completionTensorMap`. -/
theorem completionTensorLevelInvQ_adicQuotientMap (k : ℕ)
    (y : (X ⊗[R] Ω) ⧸ (Ip ^ k • (⊤ : Submodule R (X ⊗[R] Ω)))) :
    completionTensorLevelInvQ p X Ω k
        (adicQuotientMap (completionTensorMap p X Ω) (le_of_eq (Ideal.map_id Ip)) k y) = y := by
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ y
  change completionTensorLevelInv p X Ω k (completionTensorMap p X Ω y) =
    (Ip ^ k • (⊤ : Submodule R (X ⊗[R] Ω))).mkQ y
  induction y using TensorProduct.inductionOn with
  | tmul x ω =>
    rw [completionTensorMap, TensorProduct.map_tmul, completionTensorLevelInv,
      TensorProduct.lift.tmul]
    rfl
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add]

/-- For every `k`, the map `(X ⊗ Ω) / p^k → (X^∧ ⊗ Ω) / p^k` induced by `completionTensorMap` is
bijective. -/
theorem bijective_adicQuotientMap_completionTensorMap (k : ℕ) :
    Function.Bijective
      (adicQuotientMap (completionTensorMap p X Ω) (le_of_eq (Ideal.map_id Ip)) k) := by
  refine ⟨Function.LeftInverse.injective (completionTensorLevelInvQ_adicQuotientMap p X Ω k),
    fun z => ?_⟩
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ z
  induction z using TensorProduct.inductionOn with
  | tmul xh ω =>
    obtain ⟨x, hx⟩ := Submodule.mkQ_surjective (Ip ^ k • (⊤ : Submodule R X)) (xh.val k)
    refine ⟨(Ip ^ k • (⊤ : Submodule R (X ⊗[R] Ω))).mkQ (x ⊗ₜ ω), ?_⟩
    change (Ip ^ k • (⊤ : Submodule R (AdicCompletion Ip X ⊗[R] Ω))).mkQ
        (AdicCompletion.of Ip X x ⊗ₜ ω) = _
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, ← TensorProduct.sub_tmul]
    obtain ⟨w, hw⟩ := exists_eq_pow_smul_of_val_eq_zero p k (AdicCompletion.of Ip X x - xh)
      (by
        rw [AdicCompletion.val_sub_apply, AdicCompletion.of_apply, sub_eq_zero]
        exact hx)
    rw [hw, ← TensorProduct.smul_tmul']
    exact Submodule.smul_mem_smul (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) k)
      Submodule.mem_top
  | add a b ha hb =>
    obtain ⟨a', ha'⟩ := ha
    obtain ⟨b', hb'⟩ := hb
    exact ⟨a' + b', by rw [map_add, ha', hb', map_add]⟩

/-- **Completing a module first does not change a completed tensor product**:
`(X ⊗ Ω)^∧ ≅ (X^∧ ⊗ Ω)^∧`, the completion of `x ⊗ ω ↦ x̂ ⊗ ω`. -/
def completionTensorEquiv :
    AdicCompletion Ip (X ⊗[R] Ω) ≃ₗ[R] AdicCompletion Ip (AdicCompletion Ip X ⊗[R] Ω) :=
  LinearEquiv.ofBijective
    (adicCompletionMapₛₗ (completionTensorMap p X Ω) (le_of_eq (Ideal.map_id Ip)))
    (adicCompletionMapₛₗ_bijective_of_le _ _ 0
      (fun k _ => bijective_adicQuotientMap_completionTensorMap p X Ω k))

/-- On the image of `X ⊗ Ω` in its completion, `completionTensorEquiv` is the completion of
`completionTensorMap`. -/
theorem completionTensorEquiv_of (t : X ⊗[R] Ω) :
    completionTensorEquiv p X Ω (AdicCompletion.of Ip (X ⊗[R] Ω) t) =
      AdicCompletion.of Ip _ (completionTensorMap p X Ω t) :=
  adicCompletionMapₛₗ_of _ _ t

end CompletionTensor

/-! ### The completed cancellation along a completed base change -/

section Cancel

variable (p : ℕ) (D : Type*) [CommRing D] (D' : Type*) [CommRing D'] [Algebra D D']
  (Ω : Type*) [AddCommGroup Ω] [Module D Ω] [Module D' Ω] [IsScalarTower D D' Ω]
  (M : Type*) [AddCommGroup M] [Module D M]

/-- **`M' ⊗̂_{D'} Ω ≅ M ⊗̂_D Ω` for the completed base change `M' = (D' ⊗_D M)^∧`**: completing
`D' ⊗_D M` first does not change the completed tensor product
(`Crystalline.completionTensorEquiv`), and for the uncompleted base change this is
`Crystalline.completedTensorCancelBaseChange`. -/
def completedBaseChangeCancel :
    CompletedTensor p D' Ω (CompletedConnection.baseChangeCarrier p D D' M) ≃+
      CompletedTensor p D Ω M :=
  (completionTensorEquiv (R := D') p (D' ⊗[D] M) Ω).symm.toAddEquiv.trans
    (completedTensorCancelBaseChange p D D' Ω M)

/-- **The cancellation on a pure tensor**: `(d ⊗ m) ⊗ ω ↦ m ⊗ d ω`. -/
theorem completedBaseChangeCancel_of_tmul (d : D') (m : M) (ω : Ω) :
    completedBaseChangeCancel p D D' Ω M
        (toCompletedTensor p D' Ω _
          (AdicCompletion.of (pAdicIdeal (A := D') p) (D' ⊗[D] M) (d ⊗ₜ m) ⊗ₜ ω)) =
      toCompletedTensor p D Ω M (m ⊗ₜ (d • ω)) := by
  have h : (completionTensorEquiv (R := D') p (D' ⊗[D] M) Ω).symm
      (toCompletedTensor p D' Ω _
        (AdicCompletion.of (pAdicIdeal (A := D') p) (D' ⊗[D] M) (d ⊗ₜ m) ⊗ₜ[D'] ω)) =
      toCompletedTensor p D' Ω (D' ⊗[D] M) ((d ⊗ₜ m) ⊗ₜ ω) := by
    rw [LinearEquiv.symm_apply_eq]
    exact ((completionTensorEquiv_of (R := D') p (D' ⊗[D] M) Ω ((d ⊗ₜ m) ⊗ₜ ω)).trans
      (congrArg _ (TensorProduct.map_tmul _ _ _ _))).symm
  change completedTensorCancelBaseChange p D D' Ω M
    ((completionTensorEquiv (R := D') p (D' ⊗[D] M) Ω).symm _) = _
  rw [h, completedTensorCancelBaseChange_of_tmul]

/-- **The inverse cancellation on a pure tensor**: `m ⊗ ω ↦ (1 ⊗ m) ⊗ ω`. -/
theorem completedBaseChangeCancel_symm_of_tmul (m : M) (ω : Ω) :
    (completedBaseChangeCancel p D D' Ω M).symm (toCompletedTensor p D Ω M (m ⊗ₜ ω)) =
      toCompletedTensor p D' Ω _
        (CompletedConnection.baseChangeInclusion p D D' M m ⊗ₜ ω) := by
  rw [AddEquiv.symm_apply_eq, CompletedConnection.baseChangeInclusion_apply,
    completedBaseChangeCancel_of_tmul, one_smul]

end Cancel

/-! ### Additive maps out of a completed tensor product are determined on pure tensors -/

/-- Two additive maps between `p`-adic completions agree as soon as they agree on the image of
the module. -/
private theorem addMonoidHom_ext_of_forall_of (p : ℕ) {R : Type*} [CommRing R] {X : Type*}
    [AddCommGroup X] [Module R X] {S : Type*} [CommRing S] {Y : Type*} [AddCommGroup Y]
    [Module S Y]
    {f g : AdicCompletion (pAdicIdeal (A := R) p) X →+ AdicCompletion (pAdicIdeal (A := S) p) Y}
    (h : ∀ t : X, f (AdicCompletion.of _ X t) = g (AdicCompletion.of _ X t)) : f = g := by
  refine AddMonoidHom.ext fun x => AdicCompletion.ext fun k => ?_
  obtain ⟨t, ht⟩ := Submodule.mkQ_surjective
    ((pAdicIdeal (A := R) p) ^ k • (⊤ : Submodule R X)) (x.val k)
  have hx : x.val k = (AdicCompletion.of (pAdicIdeal (A := R) p) X t).val k := ht.symm
  rw [addMonoidHom_val_congr p f k hx, addMonoidHom_val_congr p g k hx, h]

/-- **Two additive maps out of a completed tensor product into a `p`-adic completion agree as soon
as they agree on the pure tensors**: both are local at the levels
(`Crystalline.addMonoidHom_val_congr`), and every level of an element is the level of the image
of an uncompleted tensor. -/
theorem completedTensor_addMonoidHom_ext (p : ℕ) {R : Type*} [CommRing R] {Ω M : Type*}
    [AddCommGroup Ω] [Module R Ω] [AddCommGroup M] [Module R M] {S : Type*} [CommRing S]
    {Y : Type*} [AddCommGroup Y] [Module S Y]
    {f g : CompletedTensor p R Ω M →+ AdicCompletion (pAdicIdeal (A := S) p) Y}
    (h : ∀ (m : M) (ω : Ω), f (toCompletedTensor p R Ω M (m ⊗ₜ ω)) =
      g (toCompletedTensor p R Ω M (m ⊗ₜ ω))) : f = g := by
  refine addMonoidHom_ext_of_forall_of p fun t => ?_
  induction t using TensorProduct.inductionOn with
  | tmul m ω => exact h m ω
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]

/-- **Two additive maps out of a `p`-adic completion into a `p`-adic completion agree as soon as
they agree on the image of the module.** -/
theorem adicCompletion_addMonoidHom_ext_of_of (p : ℕ) {R : Type*} [CommRing R] {X : Type*}
    [AddCommGroup X] [Module R X] {S : Type*} [CommRing S] {Y : Type*} [AddCommGroup Y]
    [Module S Y]
    {f g : AdicCompletion (pAdicIdeal (A := R) p) X →+ AdicCompletion (pAdicIdeal (A := S) p) Y}
    (h : ∀ t : X, f (AdicCompletion.of _ X t) = g (AdicCompletion.of _ X t)) : f = g :=
  addMonoidHom_ext_of_forall_of p h

/-! ### The cancellation carries the base-changed differential to the pushed one -/

section Differential

variable (p : ℕ) (D : Type u) [CommRing D] (D' : Type u) [CommRing D'] [Algebra D D']
  (M : Type u) [AddCommGroup M] [Module D M]
  (Om : ℕ → Type u) [∀ i, AddCommGroup (Om i)] [∀ i, Module D (Om i)]
  (Om' : ℕ → Type u) [∀ i, AddCommGroup (Om' i)] [∀ i, Module D' (Om' i)]
  [∀ i, Module D (Om' i)] [∀ i, IsScalarTower D D' (Om' i)]
  (wedge' : ∀ i, Om' i →ₗ[D'] Om' 1 →ₗ[D'] Om' (i + 1))
  (wedgeD : ∀ i, Om' i →ₗ[D] Om' 1 →ₗ[D] Om' (i + 1))
  (hwedgeD : ∀ (i : ℕ) (ω : Om' i) (η : Om' 1), wedgeD i ω η = wedge' i ω η)
  (deRham' : ∀ i, Om' i →+ Om' (i + 1))
  {d : D → Om 1} (d' : D' → Om' 1) (dD : D → Om' 1)
  (nabla : CompletedConnection p D (Om 1) d M)
  (psi : ∀ i, Om i →ₗ[D] Om' i)
  (hd'add : ∀ x y : D', d' (x + y) = d' x + d' y)
  (hd'leib : ∀ x y : D', d' (x * y) = x • d' y + y • d' x)
  (hleib' : CompletedDeRham.IsGradedLeibniz D' Om' wedge' deRham' d')
  (hleibD : CompletedDeRham.IsGradedLeibniz D Om' wedgeD deRham' dD)
  (nablaD : CompletedConnection p D (Om' 1) dD M)
  (hnablaD : ∀ m : M, nablaD m = CompletedDeRham.completedLTensor p D M (psi 1) (nabla m))

/-- A `D`-linear map into a module over the `D`-algebra `D'`, read as semilinear over
`D → D'`. -/
def semilinearOfScalarTower {X Y : Type*} [AddCommGroup X] [Module D X] [AddCommGroup Y]
    [Module D' Y] [Module D Y] [IsScalarTower D D' Y] (f : X →ₗ[D] Y) :
    X →ₛₗ[algebraMap D D'] Y where
  toFun := f
  map_add' := f.map_add
  map_smul' c x := by rw [f.map_smul, algebraMap_smul]

/-- The semilinear map `semilinearOfScalarTower D D' f` has the same values as `f`. -/
theorem semilinearOfScalarTower_apply {X Y : Type*} [AddCommGroup X] [Module D X]
    [AddCommGroup Y] [Module D' Y] [Module D Y] [IsScalarTower D D' Y] (f : X →ₗ[D] Y) (x : X) :
    semilinearOfScalarTower D D' f x = f x := rfl

variable (hpsi1 : ∀ x : D, semilinearOfScalarTower D D' (psi 1) (d x) = d' (algebraMap D D' x))

include hwedgeD in
/-- The wedge term of the base-changed differential, cancelled: for `z ∈ M ⊗̂_D Ω¹`,
`d ω ∧ ψ_*(z)` read back over `D` is `(d ω) ∧ (1_M ⊗ ψ)(z)`. -/
theorem completedBaseChangeCancel_smul_wedgeMap (i : ℕ) (c : D') (ω : Om' i)
    (z : CompletedTensor p D (Om 1) M) :
    completedBaseChangeCancel p D D' (Om' (i + 1)) M
        (c • CompletedDeRham.wedgeMap p D' Om' wedge'
          (CompletedConnection.baseChangeCarrier p D D' M) i ω
          (CompletedConnection.baseChangeValues p D D' M (Om 1) (Om' 1)
            (semilinearOfScalarTower D D' (psi 1)) z)) =
      CompletedDeRham.wedgeMap p D Om' wedgeD M i (c • ω)
        (CompletedDeRham.completedLTensor p D M (psi 1) z) := by
  let F : CompletedTensor p D (Om 1) M →+ CompletedTensor p D (Om' (i + 1)) M :=
    { toFun := fun z => completedBaseChangeCancel p D D' (Om' (i + 1)) M
        (c • CompletedDeRham.wedgeMap p D' Om' wedge'
          (CompletedConnection.baseChangeCarrier p D D' M) i ω
          (CompletedConnection.baseChangeValues p D D' M (Om 1) (Om' 1)
            (semilinearOfScalarTower D D' (psi 1)) z))
      map_zero' := by simp only [map_zero, smul_zero]
      map_add' := fun a b => by simp only [map_add, smul_add] }
  let G : CompletedTensor p D (Om 1) M →+ CompletedTensor p D (Om' (i + 1)) M :=
    (CompletedDeRham.wedgeMap p D Om' wedgeD M i (c • ω)).toAddMonoidHom.comp
      (CompletedDeRham.completedLTensor p D M (psi 1))
  have hFG : F = G := by
    refine completedTensor_addMonoidHom_ext p fun m η => ?_
    change completedBaseChangeCancel p D D' (Om' (i + 1)) M
        (c • CompletedDeRham.wedgeMap p D' Om' wedge'
          (CompletedConnection.baseChangeCarrier p D D' M) i ω
          (CompletedConnection.baseChangeValues p D D' M (Om 1) (Om' 1)
            (semilinearOfScalarTower D D' (psi 1)) (toCompletedTensor p D (Om 1) M (m ⊗ₜ η)))) =
      CompletedDeRham.wedgeMap p D Om' wedgeD M i (c • ω)
        (CompletedDeRham.completedLTensor p D M (psi 1) (toCompletedTensor p D (Om 1) M (m ⊗ₜ η)))
    rw [CompletedConnection.baseChangeValues_of_tmul, CompletedDeRham.wedgeMap_of_tmul,
      ← map_smul, ← TensorProduct.tmul_smul, ← completedBaseChangeCancel_symm_of_tmul,
      AddEquiv.apply_symm_apply, CompletedDeRham.completedLTensor_toCompletedTensor_tmul,
      CompletedDeRham.wedgeMap_of_tmul, hwedgeD, LinearMap.map_smul₂,
      semilinearOfScalarTower_apply]
  exact DFunLike.congr_fun hFG z

include hwedgeD hnablaD in
/-- **The cancellation carries the de Rham differential of the base-changed connection to that of
the pushed connection**: `M' ⊗̂_{D'} Ω'^*` and `M ⊗̂_D Ω'^*` are the same complex. -/
theorem completedBaseChangeCancel_differential (i : ℕ)
    (x : CompletedTensor p D' (Om' i) (CompletedConnection.baseChangeCarrier p D D' M)) :
    completedBaseChangeCancel p D D' (Om' (i + 1)) M
        (CompletedDeRham.differential p D' Om' wedge' deRham'
          (CompletedConnection.baseChangeCarrier p D D' M)
          (CompletedConnection.baseChange p D D' M (Om 1) (Om' 1) d'
            (semilinearOfScalarTower D D' (psi 1)) nabla hd'add hd'leib hpsi1) hleib' i x) =
      CompletedDeRham.differential p D Om' wedgeD deRham' M nablaD hleibD i
        (completedBaseChangeCancel p D D' (Om' i) M x) := by
  let F : CompletedTensor p D' (Om' i) (CompletedConnection.baseChangeCarrier p D D' M) →+
      CompletedTensor p D (Om' (i + 1)) M :=
    (completedBaseChangeCancel p D D' (Om' (i + 1)) M).toAddMonoidHom.comp
      (CompletedDeRham.differential p D' Om' wedge' deRham'
        (CompletedConnection.baseChangeCarrier p D D' M)
        (CompletedConnection.baseChange p D D' M (Om 1) (Om' 1) d'
          (semilinearOfScalarTower D D' (psi 1)) nabla hd'add hd'leib hpsi1) hleib' i)
  let G : CompletedTensor p D' (Om' i) (CompletedConnection.baseChangeCarrier p D D' M) →+
      CompletedTensor p D (Om' (i + 1)) M :=
    (CompletedDeRham.differential p D Om' wedgeD deRham' M nablaD hleibD i).comp
      (completedBaseChangeCancel p D D' (Om' i) M).toAddMonoidHom
  suffices hFG : F = G from DFunLike.congr_fun hFG x
  refine completedTensor_addMonoidHom_ext p fun xh ω => ?_
  let F' : CompletedConnection.baseChangeCarrier p D D' M →+ CompletedTensor p D (Om' (i + 1)) M :=
    F.comp ((toCompletedTensor p D' (Om' i) _).toAddMonoidHom.comp
      ((TensorProduct.mk D' _ (Om' i)).flip ω).toAddMonoidHom)
  let G' : CompletedConnection.baseChangeCarrier p D D' M →+ CompletedTensor p D (Om' (i + 1)) M :=
    G.comp ((toCompletedTensor p D' (Om' i) _).toAddMonoidHom.comp
      ((TensorProduct.mk D' _ (Om' i)).flip ω).toAddMonoidHom)
  suffices hFG' : F' = G' from DFunLike.congr_fun hFG' xh
  refine adicCompletion_addMonoidHom_ext_of_of p fun t => ?_
  induction t using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul c m =>
    change completedBaseChangeCancel p D D' (Om' (i + 1)) M
        (CompletedDeRham.differential p D' Om' wedge' deRham'
          (CompletedConnection.baseChangeCarrier p D D' M)
          (CompletedConnection.baseChange p D D' M (Om 1) (Om' 1) d'
            (semilinearOfScalarTower D D' (psi 1)) nabla hd'add hd'leib hpsi1) hleib' i
          (toCompletedTensor p D' (Om' i) _
            (AdicCompletion.of (pAdicIdeal (A := D') p) (D' ⊗[D] M) (c ⊗ₜ m) ⊗ₜ ω))) =
      CompletedDeRham.differential p D Om' wedgeD deRham' M nablaD hleibD i
        (completedBaseChangeCancel p D D' (Om' i) M (toCompletedTensor p D' (Om' i) _
          (AdicCompletion.of (pAdicIdeal (A := D') p) (D' ⊗[D] M) (c ⊗ₜ m) ⊗ₜ ω)))
    have hcorr : completedBaseChangeCancel p D D' (Om' (i + 1)) M
        (CompletedDeRham.wedgeMap p D' Om' wedge'
          (CompletedConnection.baseChangeCarrier p D D' M) i ω
          (CompletedConnection.correction p D D' M (Om' 1) (d' c)
            (CompletedConnection.baseChangeInclusion p D D' M m))) =
        toCompletedTensor p D (Om' (i + 1)) M (m ⊗ₜ wedge' i ω (d' c)) := by
      rw [CompletedConnection.correction_apply, CompletedDeRham.wedgeMap_of_tmul,
        ← completedBaseChangeCancel_symm_of_tmul, AddEquiv.apply_symm_apply]
    rw [completedBaseChangeCancel_of_tmul p D D' (Om' i) M c m ω,
      CompletedDeRham.differential_of_tmul, CompletedDeRham.differential_of_tmul,
      CompletedConnection.baseChange_of_tmul, map_add, map_add, map_smul, map_add, hcorr,
      completedBaseChangeCancel_of_tmul p D D' (Om' (i + 1)) M c m (deRham' i ω),
      completedBaseChangeCancel_smul_wedgeMap p D D' M Om Om' wedge' wedgeD hwedgeD psi,
      hnablaD, hleib' i c ω, TensorProduct.tmul_add, map_add]
    abel

/-- **The cancellation carries the base change map `m ⊗ ω ↦ (1 ⊗ m) ⊗ ψ ω` to `1_M ⊗ ψ`.** -/
theorem completedBaseChangeCancel_baseChangeTerm (i : ℕ) (z : CompletedTensor p D (Om i) M) :
    completedBaseChangeCancel p D D' (Om' i) M
        (CompletedDeRham.baseChangeTerm p D D' M Om Om'
          (fun j => semilinearOfScalarTower D D' (psi j)) i z) =
      CompletedDeRham.completedLTensor p D M (psi i) z := by
  let F : CompletedTensor p D (Om i) M →+ CompletedTensor p D (Om' i) M :=
    (completedBaseChangeCancel p D D' (Om' i) M).toAddMonoidHom.comp
      (CompletedDeRham.baseChangeTerm p D D' M Om Om'
        (fun j => semilinearOfScalarTower D D' (psi j)) i)
  suffices hF : F = CompletedDeRham.completedLTensor p D M (psi i) from DFunLike.congr_fun hF z
  refine completedTensor_addMonoidHom_ext p fun m ω => ?_
  change completedBaseChangeCancel p D D' (Om' i) M
      (CompletedDeRham.baseChangeTerm p D D' M Om Om'
        (fun j => semilinearOfScalarTower D D' (psi j)) i
        (toCompletedTensor p D (Om i) M (m ⊗ₜ ω))) =
    CompletedDeRham.completedLTensor p D M (psi i) (toCompletedTensor p D (Om i) M (m ⊗ₜ ω))
  rw [CompletedDeRham.baseChangeTerm_of_tmul, ← completedBaseChangeCancel_symm_of_tmul,
    AddEquiv.apply_symm_apply, CompletedDeRham.completedLTensor_toCompletedTensor_tmul,
    semilinearOfScalarTower_apply]

end Differential

end Crystalline

end
