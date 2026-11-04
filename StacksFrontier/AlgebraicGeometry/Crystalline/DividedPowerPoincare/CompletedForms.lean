module

public import StacksFrontier.AlgebraicGeometry.Crystalline.DividedPowerPoincare.CompletedRing
import all StacksFrontier.AlgebraicGeometry.Crystalline.DividedPowerPoincare.CompletedRing

/-!
# The divided power Poincaré lemma: the completed de Rham complex

The fifth part of `StacksFrontier.AlgebraicGeometry.Crystalline.DividedPowerPoincare`: the divided
power differentials and forms of the completed ring `D`, their `p`-adic completions `Ωⁱ_D`, the
completed de Rham differential and the completed tensor complex with coefficients in `M`, the
comparison of the differentials with those of the quotients `P/pᵉ`, and the exactness of a
completed tensor complex obtained from a splitting or a contraction.

## References

* [Stacks Project, Tag 07LC](https://stacks.math.columbia.edu/tag/07LC)
* [Stacks Project, Tag 07HZ](https://stacks.math.columbia.edu/tag/07HZ)
-/
@[expose] public section

universe u v w uA uW uM

namespace Crystalline

attribute [local implicit_reducible] RestrictScalars

open DividedPowers
open scoped TensorProduct

namespace CompletedPoincare

noncomputable section

variable (p : ℕ) (A : Type uA) [CommRing A] (W : Type uW)

/-- The canonical continuous extension of the divided powers on `P₊` to its closure in `D`. -/
public noncomputable def canonicalCompletedDividedPowers : ContinuousDividedPowers p A W :=
  Classical.choice (exists_continuousDividedPowers p A W)

variable (cdp : ContinuousDividedPowers p A W)

/-! ### The completed divided power de Rham complex of `D` -/

/-- The module `Ω_{D/A,δ}` of divided power differentials of `D` over `A` (Tag 07HZ). -/
public abbrev differentials : Type (max uA uW) :=
  dividedPowerDifferentials (A := A) cdp.dividedPowers

/-- `(D, δ)` as a divided power ring over `A` (Tag 07GU). -/
public abbrev completedDividedPowerRing : DividedPowerRing.{max uA uW} :=
  .of (completedRing p A W) (completedAugmentationIdeal p A W) cdp.dividedPowers

/-- The universal divided power derivation `d : D → Ω_{D/A,δ}` of Tag 07HR, by which the
complex of Tag 07LC differentiates: the universal divided power differential of Tag 07HZ. -/
public def dividedPowerDerivation :
    Crystalline.DividedPowerDerivation A (completedDividedPowerRing p A W cdp)
      (algebraMap A (completedRing p A W)) (differentials p A W cdp) where
  toDerivation :=
    Derivation.restrictScalars ℤ
      ((dividedPowerDifferentialRelations (A := A) cdp.dividedPowers).mkQ.compDer
        (KaehlerDifferential.D A (completedRing p A W)))
  map_ringHom' a := by
    change (dividedPowerDifferentialRelations (A := A) cdp.dividedPowers).mkQ
        (KaehlerDifferential.D A (completedRing p A W) (algebraMap A _ a)) = 0
    simp
  map_dpow' n hn x hx := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact dividedPowerDifferential_dpow (A := A) cdp.dividedPowers ⟨x, hx⟩ m

/-- The `i`-th exterior power `⋀^i Ω_{D/A,δ}`, viewed as an `A`-module. -/
public def forms (i : ℕ) : Type (max uA uW) :=
  RestrictScalars A (completedRing p A W)
    (dividedPowerDifferentialForms (A := A) cdp.dividedPowers i)

/-- The additive group of `⋀^i Ω_{D/A,δ}`. -/
public instance instAddCommGroupForms (i : ℕ) : AddCommGroup (forms p A W cdp i) :=
  inferInstanceAs (AddCommGroup (RestrictScalars A (completedRing p A W)
    (dividedPowerDifferentialForms (A := A) cdp.dividedPowers i)))

/-- The `A`-module structure of `⋀^i Ω_{D/A,δ}`, restricted along `A → D`. -/
public instance instModuleForms (i : ℕ) : Module A (forms p A W cdp i) :=
  inferInstanceAs (Module A (RestrictScalars A (completedRing p A W)
    (dividedPowerDifferentialForms (A := A) cdp.dividedPowers i)))

/-- The module `Ω^i_D`, the `p`-adic completion of `⋀^i Ω_{D/A,δ}`. -/
public def completedForms (i : ℕ) : Type (max uA uW) :=
  AdicCompletion (pAdicIdeal (A := A) p) (forms p A W cdp i)

/-- The additive group of `Ω^i_D`. -/
public instance instAddCommGroupCompletedForms (i : ℕ) :
    AddCommGroup (completedForms p A W cdp i) :=
  inferInstanceAs (AddCommGroup
    (AdicCompletion (pAdicIdeal (A := A) p) (forms p A W cdp i)))

/-- The `A`-module structure of `Ω^i_D`. -/
public instance instModuleCompletedForms (i : ℕ) : Module A (completedForms p A W cdp i) :=
  inferInstanceAs (Module A
    (AdicCompletion (pAdicIdeal (A := A) p) (forms p A W cdp i)))

/-- The divided power de Rham differential `⋀^i Ω_{D/A,δ} → ⋀^{i+1} Ω_{D/A,δ}` of Tag 07HZ,
which is `A`-linear but not `D`-linear. -/
public def deRhamDifferential (i : ℕ) :
    forms p A W cdp i →ₗ[A] forms p A W cdp (i + 1) :=
  (dividedPowerDeRhamComplex (A := A) cdp.dividedPowers).differential i

/-- The de Rham differential `Ω^i_D → Ω^{i+1}_D`, the `p`-adic completion of the divided power
de Rham differential of Tag 07HZ. -/
public def completedDeRhamDifferential (i : ℕ) :
    completedForms p A W cdp i →ₗ[A] completedForms p A W cdp (i + 1) :=
  (AdicCompletion.map (pAdicIdeal (A := A) p)
    (deRhamDifferential p A W cdp i)).restrictScalars A

/-! ### The complex with coefficients in a `p`-adically complete module -/

variable (M : Type uM) [AddCommGroup M] [Module A M]

/-- The term `M ⊗̂_A Ω^i_D` of the displayed complex, the completed tensor product of Tag 07JG
over the base ring `A`. -/
public abbrev completedTensorForms (i : ℕ) : Type (max uA uW uM) :=
  completedTensor p A (completedForms p A W cdp i) M

/-- The first map `M → M ⊗̂_A D` of the displayed complex, `m ↦ m ⊗ 1`, written through the
canonical identification of `Ω^0_D` with `D`. -/
public def augmentation : M →ₗ[A] completedTensorForms p A W cdp M 0 :=
  (toCompletedTensorOf p A (completedForms p A W cdp 0) M).comp
    ((TensorProduct.mk A M (completedForms p A W cdp 0)).flip
      (AdicCompletion.of (pAdicIdeal (A := A) p) (forms p A W cdp 0)
        ((exteriorPower.zeroEquiv (completedRing p A W) (differentials p A W cdp)).symm 1)))

/-- The map `M ⊗̂_A Ω^i_D → M ⊗̂_A Ω^{i+1}_D` of the displayed complex, the completion of
`1_M ⊗ d`. -/
public def differential (i : ℕ) :
    completedTensorForms p A W cdp M i →ₗ[A] completedTensorForms p A W cdp M (i + 1) :=
  (AdicCompletion.map (pAdicIdeal (A := A) p)
    ((completedDeRhamDifferential p A W cdp i).lTensor M)).restrictScalars A

/-! ### Completed exactness -/

/-- The linear map out of the divided power differentials induced by a derivation compatible with
the divided powers. -/
private noncomputable def liftDividedPowerDifferential
    {A B M : Type*} [CommRing A] [CommRing B] [Algebra A B] [AddCommGroup M] [Module A M]
    [Module B M] [IsScalarTower A B M] {J : Ideal B} (δ : DividedPowers J) (D : Derivation A B M)
    (hD : ∀ {n : ℕ}, 0 < n → ∀ {x : B}, x ∈ J → D (δ.dpow n x) = δ.dpow (n - 1) x • D x) :
    dividedPowerDifferentials (A := A) δ →ₗ[B] M :=
  (dividedPowerDifferentialRelations (A := A) δ).liftQ D.liftKaehlerDifferential (by
    apply Submodule.span_le.2
    rintro _ ⟨⟨x, m⟩, rfl⟩
    change D.liftKaehlerDifferential (KaehlerDifferential.D A B (δ.dpow (m + 1) x) -
      δ.dpow m x • KaehlerDifferential.D A B x) = 0
    rw [map_sub, map_smul, Derivation.liftKaehlerDifferential_comp_D,
      Derivation.liftKaehlerDifferential_comp_D]
    simp [hD (Nat.succ_pos m) x.property])

private theorem liftDividedPowerDifferential_apply
    {A B M : Type*} [CommRing A] [CommRing B] [Algebra A B] [AddCommGroup M] [Module A M]
    [Module B M] [IsScalarTower A B M] {J : Ideal B} (δ : DividedPowers J) (D : Derivation A B M)
    (hD : ∀ {n : ℕ}, 0 < n → ∀ {x : B}, x ∈ J → D (δ.dpow n x) = δ.dpow (n - 1) x • D x)
    (b : B) : liftDividedPowerDifferential δ D hD (dividedPowerDifferential (A := A) δ b) = D b :=
  Derivation.liftKaehlerDifferential_comp_D D b

-- The inverse maps are checked by span induction through two quotient modules.
private def dividedPowerDifferentialsQuotientInfEquiv
    {A : Type*} [CommRing A] (B : DividedPowerRing.{uW}) [Algebra A B]
    (K : Ideal B) (hK : DividedPowers.IsSubDPIdeal B.dividedPowers (K ⊓ B.ideal)) :
    let δ' := DividedPowers.Quotient.dividedPowers B.dividedPowers
      (J := K) hK
    { e :
        (TensorProduct B (B ⧸ K)
          (dividedPowerDifferentials (A := A) B.dividedPowers) ⧸
          Submodule.span (B ⧸ K)
            (Set.range fun k : K ↦ TensorProduct.tmul B (1 : B ⧸ K)
              (dividedPowerDifferential (A := A) B.dividedPowers k)))
          ≃ₗ[B ⧸ K]
          dividedPowerDifferentials (A := A) δ' //
      ∀ b : B,
        e (Submodule.Quotient.mk
          (TensorProduct.tmul B (1 : B ⧸ K)
            (dividedPowerDifferential (A := A) B.dividedPowers b))) =
          dividedPowerDifferential (A := A) δ' (Ideal.Quotient.mk K b) } := by
  classical
  let B' := B ⧸ K
  let q : B →+* B' := Ideal.Quotient.mk K
  let hIJ := hK
  let δ' := DividedPowers.Quotient.dividedPowers B.dividedPowers (J := K) hIJ
  let T₀ := dividedPowerDifferentials (A := A) B.dividedPowers
  let d₀ := dividedPowerDifferential (A := A) B.dividedPowers
  let N : Submodule B' (TensorProduct B B' T₀) :=
    Submodule.span B' (Set.range fun k : K ↦ TensorProduct.tmul B (1 : B') (d₀ k))
  let M := (TensorProduct B B' T₀) ⧸ N
  let tm : T₀ →ₗ[B] TensorProduct B B' T₀ := (TensorProduct.AlgebraTensorModule.mk B B' B' T₀) 1
  let dmap : T₀ →ₗ[B] M := (N.mkQ.restrictScalars B).comp tm
  let ψ : Ω[B⁄A] →ₗ[B] M := dmap.comp
    (dividedPowerDifferentialRelations (A := A) B.dividedPowers).mkQ
  let D : Derivation A B M := Derivation.llcomp ψ (KaehlerDifferential.D A B)
  have D_apply (b : B) : D b = Submodule.Quotient.mk
      (TensorProduct.tmul B (1 : B') (d₀ b)) := rfl
  have D_k (k : B) (hk : k ∈ K) : D k = 0 := by
    rw [D_apply]
    apply (Submodule.Quotient.mk_eq_zero N).2
    exact Submodule.subset_span ⟨⟨k, hk⟩, rfl⟩
  have D_dpow {n : ℕ} (hn : 0 < n) {b : B} (hb : b ∈ B.ideal) :
      D (B.dividedPowers.dpow n b) = B.dividedPowers.dpow (n - 1) b • D b := by
    obtain ⟨m, rfl⟩ := (Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn))
    have h := congrArg dmap (dividedPowerDifferential_dpow (A := A)
      (hJ := B.dividedPowers) ⟨b, hb⟩ m)
    rw [map_smul] at h
    change dmap (d₀ (B.dividedPowers.dpow (m + 1) b)) =
      B.dividedPowers.dpow m b • dmap (d₀ b)
    simpa [d₀] using h
  have hAlg : algebraMap A B' = q.comp (algebraMap A B) := IsScalarTower.algebraMap_eq A B B'
  let Dq : Derivation A B' M := derivationQuotient hAlg D (fun k hk ↦ D_k k hk)
  have Dq_mk (b : B) : Dq (q b) = D b := by
    have hN : K.toAddSubgroup ≤ D.toAddMonoidHom.ker :=
      fun k hk ↦ AddMonoidHom.mem_ker.mpr (D_k k hk)
    change (QuotientAddGroup.lift K.toAddSubgroup D.toAddMonoidHom hN)
      (Ideal.Quotient.mk K b) = D b
    exact QuotientAddGroup.lift_mk K.toAddSubgroup hN b
  have Dq_dpow {n : ℕ} (hn : 0 < n) {b : B} (hb : b ∈ B.ideal) :
      Dq (δ'.dpow n (q b)) = δ'.dpow (n - 1) (q b) • Dq (q b) := by
    rw [DividedPowers.Quotient.dpow_apply B.dividedPowers hIJ hb, Dq_mk,
      DividedPowers.Quotient.dpow_apply (n := n - 1) B.dividedPowers hIJ hb, Dq_mk,
      D_dpow hn hb, ← Ideal.Quotient.algebraMap_eq]
    exact (IsScalarTower.algebraMap_smul B' _ _).symm
  have Dq_dpow' {n : ℕ} (hn : 0 < n) {x : B'} (hx : x ∈ B.ideal.map q) :
      Dq (δ'.dpow n x) = δ'.dpow (n - 1) x • Dq x := by
    obtain ⟨b, hb, rfl⟩ := (Ideal.mem_map_iff_of_surjective q Ideal.Quotient.mk_surjective).mp hx
    exact Dq_dpow hn hb
  let T := dividedPowerDifferentials (A := A) δ'
  let Rq := dividedPowerDifferentialRelations (A := A) δ'
  let g : T →ₗ[B'] M := liftDividedPowerDifferential δ' Dq Dq_dpow'
  have g_apply (x : B') : g (dividedPowerDifferential (A := A) δ' x) = Dq x :=
    liftDividedPowerDifferential_apply δ' Dq Dq_dpow' x
  have hspanT := dividedPowerDifferentials_span (A := A) δ'
  let Dt : Derivation A B' T := Derivation.llcomp Rq.mkQ (KaehlerDifferential.D A B')
  have Dt_apply (x : B') : Dt x = dividedPowerDifferential (A := A) δ' x := rfl
  let Dc : Derivation A B T := Derivation.compAlgebraMap B Dt
  have Dc_apply (b : B) : Dc b = dividedPowerDifferential (A := A) δ' (q b) := rfl
  have Dc_dpow {n : ℕ} (hn : 0 < n) {b : B} (hb : b ∈ B.ideal) :
      Dc (B.dividedPowers.dpow n b) = B.dividedPowers.dpow (n - 1) b • Dc b := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    change dividedPowerDifferential (A := A) δ'
        (q (B.dividedPowers.dpow (m + 1) b)) =
      B.dividedPowers.dpow m b • dividedPowerDifferential (A := A) δ' (q b)
    calc
      _ = dividedPowerDifferential (A := A) δ' (δ'.dpow (m + 1) (q b)) := by
            rw [← DividedPowers.Quotient.dpow_apply B.dividedPowers hIJ hb]
      _ = δ'.dpow m (q b) • dividedPowerDifferential (A := A) δ' (q b) :=
        dividedPowerDifferential_dpow (A := A) (hJ := δ') ⟨q b, Ideal.mem_map_of_mem q hb⟩ m
      _ = q (B.dividedPowers.dpow m b) •
          dividedPowerDifferential (A := A) δ' (q b) := by
            rw [DividedPowers.Quotient.dpow_apply (n := m) B.dividedPowers hIJ hb]
      _ = B.dividedPowers.dpow m b •
          dividedPowerDifferential (A := A) δ' (q b) :=
            (@IsScalarTower.algebraMap_smul B B' T _ _ _ _ _ _
              (B.dividedPowers.dpow m b) _).symm
  let φ : T₀ →ₗ[B] T := liftDividedPowerDifferential B.dividedPowers Dc Dc_dpow
  have φ_apply (b : B) : φ (d₀ b) = dividedPowerDifferential (A := A) δ' (q b) :=
    liftDividedPowerDifferential_apply B.dividedPowers Dc Dc_dpow b
  let F0 : TensorProduct B B' T₀ →ₗ[B'] T := TensorProduct.AlgebraTensorModule.lift
    (LinearMap.smulRight (LinearMap.id : B' →ₗ[B'] B') φ)
  have hN : N ≤ F0.ker := by
    apply Submodule.span_le.2
    rintro _ ⟨k, rfl⟩
    change F0 (TensorProduct.tmul B (1 : B') (d₀ (k : B))) = 0
    dsimp [F0]
    simp only [one_smul]
    rw [φ_apply]
    have hk : q (k : B) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr k.property
    rw [hk]
    change Rq.mkQ (KaehlerDifferential.D A B' 0) = 0
    simp
  let F : M →ₗ[B'] T := N.liftQ F0 hN
  have F_apply (b : B) :
    F (Submodule.Quotient.mk (TensorProduct.tmul B (1 : B') (d₀ b))) =
        dividedPowerDifferential (A := A) δ' (q b) := by
    change F0 (TensorProduct.tmul B (1 : B') (d₀ b)) = _
    dsimp [F0]
    simp [φ_apply]
  have hspanT₀ : Submodule.span B (Set.range d₀) = ⊤ :=
    dividedPowerDifferentials_span (A := A) B.dividedPowers
  have hmapd : Submodule.map dmap (Submodule.span B (Set.range d₀)) ≤
      (Submodule.span B' (Set.range fun b : B ↦ N.mkQ
        (TensorProduct.tmul B (1 : B') (d₀ b)))).restrictScalars B := by
    rw [Submodule.map_span]
    apply Submodule.span_le.2
    rintro z ⟨x, ⟨b, rfl⟩, rfl⟩
    exact Submodule.subset_span ⟨b, rfl⟩
  have hspanM : Submodule.span B'
      (Set.range fun b : B ↦ N.mkQ
        (TensorProduct.tmul B (1 : B') (d₀ b))) = ⊤ := by
    apply le_antisymm le_top
    intro y hy
    obtain ⟨z, rfl⟩ := N.mkQ_surjective y
    clear hy
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simpa only [map_add] using add_mem hx hy
    | tmul b x =>
        have hx : x ∈ Submodule.span B (Set.range d₀) := by
          rw [hspanT₀]; exact Submodule.mem_top
        have hx' : dmap x ∈ Submodule.span B' (Set.range fun b : B ↦
            N.mkQ (TensorProduct.tmul B (1 : B') (d₀ b))) :=
          hmapd (Submodule.mem_map_of_mem hx)
        have hfactor : TensorProduct.tmul B b x =
            b • TensorProduct.tmul B (1 : B') x := by
          simpa using (TensorProduct.smul_tmul' b (1 : B') x).symm
        rw [hfactor, map_smul]
        change b • dmap x ∈ _
        exact Submodule.smul_mem _ _ hx'
  have hGFgen (b : B) :
      g (F (Submodule.Quotient.mk
        (TensorProduct.tmul B (1 : B') (d₀ b)))) =
        Submodule.Quotient.mk (TensorProduct.tmul B (1 : B') (d₀ b)) := by
    rw [F_apply, g_apply, Dq_mk, D_apply]
  have hGF : g.comp F = LinearMap.id := LinearMap.ext_on_range hspanM hGFgen
  have hFGgen (x : B') :
      F (g (dividedPowerDifferential (A := A) δ' x)) =
        dividedPowerDifferential (A := A) δ' x := by
    obtain ⟨b, rfl⟩ := q.surjective x
    rw [g_apply, Dq_mk, D_apply, F_apply]
  have hFG : F.comp g = LinearMap.id := LinearMap.ext_on_range hspanT hFGgen
  refine ⟨LinearEquiv.ofLinearMap F g hFG hGF, ?_⟩
  intro b; exact F_apply b

private def differentialsQuotientInfEquiv
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (J : Ideal B) (delta : DividedPowers J)
    (K : Ideal B) (hK : delta.IsSubDPIdeal (K ⊓ J))
    (hd : ∀ b ∈ K, dividedPowerDifferential (A := A) delta b ∈
      K • (⊤ : Submodule B (dividedPowerDifferentials (A := A) delta))) :
    let dq := DividedPowers.Quotient.dividedPowers delta
      hK
    { E : (dividedPowerDifferentials (A := A) delta ⧸
        K • (⊤ : Submodule B (dividedPowerDifferentials (A := A) delta))) ≃ₗ[B]
        dividedPowerDifferentials (A := A) dq //
      ∀ b, E (Submodule.Quotient.mk (dividedPowerDifferential (A := A) delta b)) =
        dividedPowerDifferential (A := A) dq (Ideal.Quotient.mk K b) } := by
  let M := dividedPowerDifferentials (A := A) delta
  let T := TensorProduct B (B ⧸ K) M
  let N : Submodule (B ⧸ K) T := Submodule.span (B ⧸ K)
    (Set.range fun k : K ↦ TensorProduct.tmul B (1 : B ⧸ K)
      (dividedPowerDifferential (A := A) delta k))
  let E := TensorProduct.quotTensorEquivQuotSMul M K
  have hN : N = ⊥ := by
    apply eq_bot_iff.mpr
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    apply E.injective
    rw [map_zero, TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul]
    exact (Submodule.Quotient.mk_eq_zero _).mpr (hd k k.property)
  let F := dividedPowerDifferentialsQuotientInfEquiv
    (A := A) (DividedPowerRing.of B J delta) K hK
  refine ⟨E.symm.trans (((N.quotEquivOfEqBot hN).symm.restrictScalars B).trans
    (F.val.restrictScalars B)), ?_⟩
  intro b
  have hE : E.symm (Submodule.Quotient.mk (dividedPowerDifferential (A := A) delta b)) =
      TensorProduct.tmul B (1 : B ⧸ K) (dividedPowerDifferential (A := A) delta b) := by
    apply E.injective
    rw [E.apply_symm_apply, TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul]
  have key : (N.quotEquivOfEqBot hN).symm (E.symm
      (Submodule.Quotient.mk (dividedPowerDifferential (A := A) delta b))) =
      Submodule.Quotient.mk (TensorProduct.tmul B (1 : B ⧸ K)
        (dividedPowerDifferential (A := A) delta b)) := by
    rw [hE, Submodule.quotEquivOfEqBot_symm_apply]
  exact (congrArg (fun x => F.val x) key).trans (F.property b)

private theorem differentialsQuotientInfEquiv_mk
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (J : Ideal B) (delta : DividedPowers J)
    (K : Ideal B) (hK : delta.IsSubDPIdeal (K ⊓ J))
    (hd : ∀ b ∈ K, dividedPowerDifferential (A := A) delta b ∈
      K • (⊤ : Submodule B (dividedPowerDifferentials (A := A) delta)))
    (x : dividedPowerDifferentials (A := A) delta) :
    (differentialsQuotientInfEquiv (A := A) J delta K hK hd).val (Submodule.Quotient.mk x) =
      mapDifferentialsOfDPMorphism (J := _) (delta := delta) _ (Ideal.Quotient.mkₐ A K)
        (DividedPowers.Quotient.isDPMorphism delta
          hK) x := by
  let E := (differentialsQuotientInfEquiv (A := A) J delta K hK hd).val
  apply DFunLike.congr_fun (differentials_hom_ext (J := _) (delta := delta) (Ideal.Quotient.mk K)
    (E.toAddMonoidHom.comp (K • (⊤ : Submodule B _)).mkQ.toAddMonoidHom) _ ?_ ?_ ?_) x
  · intro b x
    change E (Submodule.Quotient.mk (b • x)) = _
    rw [Submodule.Quotient.mk_smul, E.map_smul]
    exact (IsScalarTower.algebraMap_smul (B ⧸ K) b _).symm
  · intro b x
    exact mapDifferentialsOfDPMorphism_smul (A := A) (J := J) (delta := delta) _ _ _ b x
  · intro b
    change E _ = _
    exact ((differentialsQuotientInfEquiv (A := A) J delta K hK hd).property b).trans
      (mapDifferentialsOfDPMorphism_d (A := A) (J := J) (delta := delta)
        _ (Ideal.Quotient.mkₐ A K) _ b).symm

/-- The finite-level differential comparison along a surjection of divided-power algebras. -/
private def differentialsSurjectionInfEquiv
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (J : Ideal B) (delta : DividedPowers J)
    {C : Type*} [CommRing C] [Algebra A C] {L : Ideal C}
    (epsilon : DividedPowers L) (f : B →ₐ[A] C)
    (hf : delta.IsDPMorphism epsilon f.toRingHom)
    (hs : Function.Surjective f) (hJ : J.map f.toRingHom = L)
    (K : Ideal B) (hker : K = RingHom.ker f.toRingHom)
    (hd : ∀ b ∈ K, dividedPowerDifferential (A := A) delta b ∈
      K • (⊤ : Submodule B (dividedPowerDifferentials (A := A) delta))) :
    { E : (dividedPowerDifferentials (A := A) delta ⧸
        K • (⊤ : Submodule B (dividedPowerDifferentials (A := A) delta))) ≃+
        dividedPowerDifferentials (A := A) epsilon //
      ∀ x, E (Submodule.Quotient.mk x) =
        mapDifferentialsOfDPMorphism (J := _) (delta := delta) epsilon f hf x } := by
  have hK : delta.IsSubDPIdeal (K ⊓ J) := by
    have H := delta.isSubDPIdeal_ker epsilon hf
    change delta.IsSubDPIdeal (RingHom.ker f.toRingHom ⊓ J) at H
    simpa only [← hker] using H
  let dq := DividedPowers.Quotient.dividedPowers delta (J := K)
    hK
  let q : B →ₐ[A] B ⧸ K := Ideal.Quotient.mkₐ A K
  have hq : delta.IsDPMorphism dq q.toRingHom :=
    DividedPowers.Quotient.isDPMorphism delta _
  let e : (B ⧸ K) ≃ₐ[A] C := (Ideal.quotientEquivAlgOfEq A hker).trans
    (Ideal.quotientKerAlgEquivOfSurjective hs)
  have heq : e.toAlgHom.comp q = f := by
    ext b
    change (Ideal.quotientKerAlgEquivOfSurjective hs)
      (Ideal.quotientEquivAlgOfEq A hker (Ideal.Quotient.mk K b)) = f b
    rw [Ideal.quotientEquivAlgOfEq_mk]
    exact Ideal.quotientKerAlgEquivOfSurjective_mk hs b
  have he : dq.IsDPMorphism epsilon e.toAlgHom.toRingHom := by
    apply DividedPowers.IsDPMorphism.of_comp delta dq epsilon q.toRingHom
      e.toAlgHom.toRingHom rfl hq
    change delta.IsDPMorphism epsilon (e.toAlgHom.comp q).toRingHom
    rw [heq]
    exact hf
  have heJ : (J.map (Ideal.Quotient.mk K)).map e.toAlgHom.toRingHom = L := by
    rw [Ideal.map_map]
    change J.map (e.toAlgHom.comp q).toRingHom = L
    rw [heq, hJ]
  let E := differentialsQuotientInfEquiv (A := A) J delta K hK hd
  let F := differentialsEquivOfAlgEquiv (J := _) (delta := dq) epsilon e he heJ
  refine ⟨E.val.toAddEquiv.trans F.val, ?_⟩
  intro x
  change F.val (E.val (Submodule.Quotient.mk x)) = _
  rw [differentialsQuotientInfEquiv_mk]
  change F.val.toAddMonoidHom _ = _
  rw [F.property]
  have H := mapDifferentialsOfDPMorphism_comp (J := _) (delta := delta) dq epsilon q
    e.toAlgHom hq he
  have Hx := DFunLike.congr_fun H x
  simpa only [heq, AddMonoidHom.comp_apply] using Hx

private theorem toCompletedRing_mem_augmentationIdeal
    (x : dividedPowerPolynomialRing A W) (hx : x ∈ augmentationIdeal A W) :
    toCompletedRing p A W x ∈ completedAugmentationIdeal p A W := by
  apply (mem_completedAugmentationIdeal_iff p A W _).2
  intro e
  exact ⟨_, Ideal.mem_map_of_mem _ hx, by simp⟩

private theorem continuousDividedPowers_eval (n e : ℕ)
    (x : completedRing p A W) (hx : x ∈ completedAugmentationIdeal p A W) :
    (quotientAugmentationDividedPowers p A W e).dpow n
        (AdicCompletion.evalₐ (pAdicIdeal p) e x) =
      AdicCompletion.evalₐ (pAdicIdeal p) e (cdp.dividedPowers.dpow n x) := by
  let a := completedAugmentationRepresentative p A W ⟨x, hx⟩ e
  have ha := completedAugmentationRepresentative_spec p A W ⟨x, hx⟩ e
  let y : completedAugmentationIdeal p A W :=
    ⟨toCompletedRing p A W a, toCompletedRing_mem_augmentationIdeal p A W a ha.1⟩
  have hclose : x - (y : completedRing p A W) ∈
      pAdicIdeal (A := completedRing p A W) p ^ e := ha.2
  have hdp := cdp.dpow_congr n e ⟨x, hx⟩ y hclose
  have h₁ := completedRing_eval_kills_pAdicPow p A W e hclose
  have h₂ := completedRing_eval_kills_pAdicPow p A W e hdp
  change AdicCompletion.evalₐ (pAdicIdeal p) e
    (x - (y : completedRing p A W)) = 0 at h₁
  change AdicCompletion.evalₐ (pAdicIdeal p) e
    (cdp.dividedPowers.dpow n x - cdp.dividedPowers.dpow n (y : completedRing p A W)) = 0 at h₂
  rw [map_sub, sub_eq_zero] at h₁ h₂
  rw [h₁, h₂, cdp.dpow_toCompletedRing n a ha.1 y rfl]
  exact DividedPowers.Quotient.dpow_apply (canonicalDividedPowers A W)
    (augmentationIdeal_inf_isSubDPIdeal p A W e) ha.1

private theorem eval_isDPMorphism (e : ℕ) :
    cdp.dividedPowers.IsDPMorphism (quotientAugmentationDividedPowers p A W e)
      (AdicCompletion.evalₐ (pAdicIdeal p) e).toRingHom where
  ideal_comp := Ideal.map_le_iff_le_comap.mpr fun x hx =>
    completedAugmentation_eval_mem p A W e x hx
  dpow_comp := by
    intro n x hx
    exact continuousDividedPowers_eval p A W cdp n e x hx

private theorem completedAugmentationIdeal_map_eval (e : ℕ) :
    (completedAugmentationIdeal p A W).map
        (AdicCompletion.evalₐ (pAdicIdeal p) e).toRingHom =
      (augmentationIdeal A W).map (Ideal.Quotient.mk (pAdicIdeal p ^ e)) := by
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    intro x hx
    exact completedAugmentation_eval_mem p A W e x hx
  · apply Ideal.map_le_iff_le_comap.mpr
    intro x hx
    exact Ideal.mem_map_of_mem _ (toCompletedRing_mem_augmentationIdeal p A W x hx)

private theorem completedRing_pAdicPow_eq_ker_eval (e : ℕ) :
    pAdicIdeal (A := completedRing p A W) p ^ e =
      RingHom.ker (AdicCompletion.evalₐ (pAdicIdeal p) e).toRingHom := by
  apply le_antisymm (completedRing_eval_kills_pAdicPow p A W e)
  intro x hx
  exact completedRing_mem_pAdicPow_of_eval_eq_zero p A W e x hx

private def completedDifferentialsModPowEquiv (e : ℕ) :
    { E : (differentials p A W cdp ⧸
        pAdicIdeal (A := completedRing p A W) p ^ e •
          (⊤ : Submodule (completedRing p A W) (differentials p A W cdp))) ≃+
        dividedPowerDifferentials (A := A) (quotientAugmentationDividedPowers p A W e) //
      ∀ x, E (Submodule.Quotient.mk x) =
        mapDifferentialsOfDPMorphism (A := A)
          (J := completedAugmentationIdeal p A W) (delta := cdp.dividedPowers)
          (quotientAugmentationDividedPowers p A W e)
          ((AdicCompletion.evalₐ (pAdicIdeal p) e).restrictScalars A)
          (eval_isDPMorphism p A W cdp e) x } := by
  apply differentialsSurjectionInfEquiv (completedAugmentationIdeal p A W)
    cdp.dividedPowers (quotientAugmentationDividedPowers p A W e)
    ((AdicCompletion.evalₐ (pAdicIdeal p) e).restrictScalars A)
    (eval_isDPMorphism p A W cdp e)
    (AdicCompletion.surjective_evalₐ _ e)
    (completedAugmentationIdeal_map_eval p A W e) _
    (completedRing_pAdicPow_eq_ker_eval p A W e)
  intro x hx
  exact dividedPowerDifferential_mem_pAdicPow _ cdp.dividedPowers p e hx

private def differentialsModPowComparison (e : ℕ) :
    (differentials p A W cdp ⧸
      pAdicIdeal (A := completedRing p A W) p ^ e •
        (⊤ : Submodule (completedRing p A W) (differentials p A W cdp))) ≃+
      (dividedPowerDifferentials (A := A) (canonicalDividedPowers A W) ⧸
        pAdicIdeal (A := dividedPowerPolynomialRing A W) p ^ e •
          (⊤ : Submodule (dividedPowerPolynomialRing A W)
            (dividedPowerDifferentials (A := A) (canonicalDividedPowers A W)))) :=
  (completedDifferentialsModPowEquiv p A W cdp e).1.trans
    (differentialsQuotientInfEquiv (A := A) (augmentationIdeal A W)
      (canonicalDividedPowers A W)
      (pAdicIdeal (A := dividedPowerPolynomialRing A W) p ^ e)
      (augmentationIdeal_inf_isSubDPIdeal p A W e)
      (fun _ hx => dividedPowerDifferential_mem_pAdicPow _
        (canonicalDividedPowers A W) p e hx)).1.toAddEquiv.symm

private def completedRingAugmentationAt (e : ℕ) :
    completedRing p A W →ₐ[A] A ⧸ pAdicIdeal (A := A) p ^ e :=
  (Ideal.Quotient.liftₐ (pAdicIdeal (A := dividedPowerPolynomialRing A W) p ^ e)
    ((Ideal.Quotient.mkₐ A _).comp (dividedPowerPolynomialAugmentation A W)) (by
      intro a ha
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      have h := Ideal.mem_map_of_mem (dividedPowerPolynomialAugmentation A W).toRingHom ha
      simpa [pAdicIdeal, Ideal.map_pow, Ideal.map_span] using h)).comp
    ((AdicCompletion.evalₐ (pAdicIdeal p) e).restrictScalars A)

private theorem completedRingAugmentationAt_of (e : ℕ) (a : dividedPowerPolynomialRing A W) :
    completedRingAugmentationAt p A W e (toCompletedRing p A W a) =
      Ideal.Quotient.mk _ (dividedPowerPolynomialAugmentation A W a) := by
  rfl

private def completedRingAugmentation :
    completedRing p A W →ₐ[A] AdicCompletion (pAdicIdeal (A := A) p) A :=
  AdicCompletion.liftAlgHom _ (completedRingAugmentationAt p A W) (by
    intro m n hmn
    ext x
    obtain ⟨c, rfl⟩ := AdicCompletion.mk_surjective
      (pAdicIdeal (A := dividedPowerPolynomialRing A W) p) _ x
    change Ideal.Quotient.mk _ (dividedPowerPolynomialAugmentation A W (c n)) =
      Ideal.Quotient.mk _ (dividedPowerPolynomialAugmentation A W (c m))
    apply Ideal.Quotient.eq.mpr
    have hc := SModEq.sub_mem.mp (c.property hmn)
    have hc' : c n - c m ∈ pAdicIdeal p ^ m := by
      simpa [Ideal.smul_eq_mul, Ideal.mul_top, neg_sub] using
        (pAdicIdeal p ^ m • (⊤ : Submodule _ _)).neg_mem hc
    have h := Ideal.mem_map_of_mem (dividedPowerPolynomialAugmentation A W).toRingHom hc'
    simpa [pAdicIdeal, Ideal.map_pow, Ideal.map_span, map_sub] using h)

private theorem pAdicIdeal_fg : (pAdicIdeal (A := A) p).FG :=
  Submodule.fg_span_singleton _

private def adicLiftLinear {R X Y : Type*} [CommRing R]
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    (I : Ideal R) [IsAdicComplete I Y] (f : X →ₗ[R] Y) :
    AdicCompletion I X →ₗ[R] Y :=
  (AdicCompletion.ofLinearEquiv I Y).symm.toLinearMap.comp
    ((AdicCompletion.map I f).restrictScalars R)

private theorem adicLiftLinear_of {R X Y : Type*} [CommRing R]
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    (I : Ideal R) [IsAdicComplete I Y] (f : X →ₗ[R] Y) (x : X) :
    adicLiftLinear I f (AdicCompletion.of I X x) = f x := by
  change (AdicCompletion.ofLinearEquiv I Y).symm
    (AdicCompletion.map I f (AdicCompletion.of I X x)) = f x
  rw [AdicCompletion.map_of, ← AdicCompletion.ofLinearEquiv_apply,
    LinearEquiv.symm_apply_apply]

private def zeroFormsAugmentation :
    forms p A W cdp 0 →ₗ[A] AdicCompletion (pAdicIdeal (A := A) p) A where
  toFun x := completedRingAugmentation p A W
    (exteriorPower.zeroEquiv (completedRing p A W) (differentials p A W cdp) x)
  map_add' x y := by
    let e := exteriorPower.zeroEquiv (completedRing p A W) (differentials p A W cdp)
    exact (congrArg (completedRingAugmentation p A W) (e.map_add x y)).trans
      ((completedRingAugmentation p A W).map_add _ _)
  map_smul' r x := by
    let e := exteriorPower.zeroEquiv (completedRing p A W) (differentials p A W cdp)
    exact (congrArg (completedRingAugmentation p A W)
      ((e.restrictScalars A).map_smul r x)).trans
      ((completedRingAugmentation p A W).toLinearMap.map_smul r (e x))

private def completedZeroFormsAugmentation :
    completedForms p A W cdp 0 →ₗ[A] AdicCompletion (pAdicIdeal (A := A) p) A := by
  letI := AdicCompletion.isAdicComplete (M := A) (pAdicIdeal_fg p A)
  exact adicLiftLinear (pAdicIdeal (A := A) p) (zeroFormsAugmentation p A W cdp)

private theorem completedZeroFormsAugmentation_one :
    completedZeroFormsAugmentation p A W cdp
      (AdicCompletion.of (pAdicIdeal (A := A) p) (forms p A W cdp 0)
        ((exteriorPower.zeroEquiv (completedRing p A W)
          (differentials p A W cdp)).symm 1)) = 1 := by
  let := AdicCompletion.isAdicComplete (M := A) (pAdicIdeal_fg p A)
  let z : forms p A W cdp 0 :=
    (exteriorPower.zeroEquiv (completedRing p A W) (differentials p A W cdp)).symm 1
  calc
    _ = zeroFormsAugmentation p A W cdp z :=
      adicLiftLinear_of (pAdicIdeal p) (zeroFormsAugmentation p A W cdp) z
    _ = 1 := by
      change completedRingAugmentation p A W
        ((exteriorPower.zeroEquiv (completedRing p A W) (differentials p A W cdp))
          ((exteriorPower.zeroEquiv (completedRing p A W) (differentials p A W cdp)).symm 1)) = 1
      rw [LinearEquiv.apply_symm_apply, map_one]

private def completedTensorAugmentationRetraction :
    completedTensorForms p A W cdp M 0 →ₗ[A]
      AdicCompletion (pAdicIdeal (A := A) p) M := by
  let I := pAdicIdeal (A := A) p
  letI := AdicCompletion.isAdicComplete (M := M) (pAdicIdeal_fg p A)
  let b : M →ₗ[A] AdicCompletion I A →ₗ[A] AdicCompletion I M :=
    LinearMap.mk₂ A (fun m a => a • AdicCompletion.of I M m)
      (by intros; simp only [map_add, smul_add])
      (by intro r m a; rw [map_smul]; exact smul_comm a r _)
      (by intros; exact add_smul _ _ _)
      (by intros; exact smul_assoc _ _ _)
  let f := (TensorProduct.lift b).comp
    ((completedZeroFormsAugmentation p A W cdp).lTensor M)
  exact adicLiftLinear I f

private theorem completedTensorAugmentationRetraction_augmentation (m : M) :
    completedTensorAugmentationRetraction p A W cdp M (augmentation p A W cdp M m) =
      AdicCompletion.of (pAdicIdeal (A := A) p) M m := by
  let I := pAdicIdeal (A := A) p
  let := AdicCompletion.isAdicComplete (M := M) (pAdicIdeal_fg p A)
  let z : completedForms p A W cdp 0 := AdicCompletion.of I (forms p A W cdp 0)
    ((exteriorPower.zeroEquiv (completedRing p A W) (differentials p A W cdp)).symm 1)
  change adicLiftLinear I _ (AdicCompletion.of I (M ⊗[A] completedForms p A W cdp 0)
    (m ⊗ₜ[A] z)) = _
  rw [adicLiftLinear_of]
  change completedZeroFormsAugmentation p A W cdp z • AdicCompletion.of I M m = _
  rw [show completedZeroFormsAugmentation p A W cdp z = 1 from
    completedZeroFormsAugmentation_one p A W cdp, one_smul]

private theorem completedTensor_exact_of_splitting
    {R X Y Z N : Type*} [CommRing R]
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    [AddCommGroup Z] [Module R Z] [AddCommGroup N] [Module R N]
    (I : Ideal R) (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z)
    (s : Y →ₗ[R] X) (t : Z →ₗ[R] Y)
    (hgf : g.comp f = 0) (hs : f.comp s + t.comp g = LinearMap.id) :
    Function.Exact (AdicCompletion.map I (f.lTensor N))
      (AdicCompletion.map I (g.lTensor N)) := by
  have hgf' : (g.lTensor N).comp (f.lTensor N) = 0 := by
    rw [← LinearMap.lTensor_comp, hgf, LinearMap.lTensor_zero]
  have hs' : (f.lTensor N).comp (s.lTensor N) +
      (t.lTensor N).comp (g.lTensor N) = LinearMap.id := by
    rw [← LinearMap.lTensor_comp, ← LinearMap.lTensor_comp,
      ← LinearMap.lTensor_add, hs, LinearMap.lTensor_id]
  have H : (AdicCompletion.map I (f.lTensor N)).comp
      (AdicCompletion.map I (s.lTensor N)) +
      (AdicCompletion.map I (t.lTensor N)).comp
        (AdicCompletion.map I (g.lTensor N)) = LinearMap.id := by
    rw [AdicCompletion.map_comp, AdicCompletion.map_comp,
      ← map_add, hs', AdicCompletion.map_id]
  intro y
  constructor
  · intro hy
    refine ⟨AdicCompletion.map I (s.lTensor N) y, ?_⟩
    have h := LinearMap.congr_fun H y
    simpa only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply,
      hy, map_zero, add_zero] using h
  · rintro ⟨x, rfl⟩
    rw [AdicCompletion.map_comp_apply, hgf', AdicCompletion.map_zero, LinearMap.zero_apply]

private theorem completedTensor_exact_of_contractible
    {R : Type*} [CommRing R] (I : Ideal R)
    (C : CochainComplex (ModuleCat.{uW} R) ℕ)
    (h : Homotopy (CategoryTheory.CategoryStruct.id C) 0)
    (N : Type*) [AddCommGroup N] [Module R N] (n : ℕ) :
    Function.Exact (AdicCompletion.map I ((C.d n (n + 1)).hom.lTensor N))
      (AdicCompletion.map I ((C.d (n + 1) (n + 1 + 1)).hom.lTensor N)) := by
  apply completedTensor_exact_of_splitting I _ _
    (h.hom (n + 1) n).hom (h.hom (n + 1 + 1) (n + 1)).hom
  · exact congrArg ModuleCat.Hom.hom (C.d_comp_d n (n + 1) (n + 1 + 1))
  · have hc := h.comm (n + 1)
    rw [dNext_eq _ (show (ComplexShape.up ℕ).Rel (n + 1) (n + 1 + 1) from rfl),
      prevD_eq _ (show (ComplexShape.up ℕ).Rel n (n + 1) from rfl)] at hc
    have H := congrArg ModuleCat.Hom.hom hc
    simpa only [HomologicalComplex.id_f, HomologicalComplex.zero_f,
      ModuleCat.hom_id, ModuleCat.hom_add, ModuleCat.hom_comp, ModuleCat.hom_zero,
      add_zero, zero_add, add_comm] using H.symm

private theorem completedPolynomialTensor_exact (n : ℕ) :
    Function.Exact
      (AdicCompletion.map (pAdicIdeal (A := A) p)
        (((augmentedDividedPowerDeRhamComplex A W).d n (n + 1)).hom.lTensor M))
      (AdicCompletion.map (pAdicIdeal (A := A) p)
        (((augmentedDividedPowerDeRhamComplex A W).d
          (n + 1) (n + 1 + 1)).hom.lTensor M)) := by
  obtain ⟨h⟩ := augmentedDividedPowerDeRhamComplex_contractible A W
  exact completedTensor_exact_of_contractible _ _ h M n

end

end CompletedPoincare

end Crystalline

end
