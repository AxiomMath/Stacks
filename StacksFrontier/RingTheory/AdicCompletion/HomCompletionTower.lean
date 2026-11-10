module

public import StacksFrontier.RingTheory.AdicCompletion.HomCompletion

/-!
# Compatible families of maps into the truncations of a module

Let `A` be a Noetherian ring, `I ⊆ A` an ideal and `M`, `N` finite `A`-modules.  The levels of
`AdicCompletion.homCompletionEquiv`, which identifies the `I`-adic completion of `Hom_A(M, N)`
with `Hom_A(M, N̂)`, are computed by representatives: if `s` is represented at level `n` by
`f : M →ₗ[A] N`, then the image of `m` is represented at level `n` by `f m`.

As a consequence, compatible families of elements of `Hom_A(M, N) / Iⁿ⁺¹ Hom_A(M, N)` are the
same as compatible families of maps `M ⟶ Qₙ` into any tower `(Qₙ)` presenting the truncations
`N / Iⁿ⁺¹ N`: this is the algebraic content of Stacks 0882 and 08B6.

## Main results

* `AdicCompletion.homCompletionEquiv_apply_val`: the level formula.
* `AdicCompletion.bijective_homTowerFamilyMap`: compatible families of truncated homomorphisms are
  compatible families of maps into the truncations.
-/

@[expose] public noncomputable section

namespace AdicCompletion

universe u

variable {A M N : Type u} [CommRing A] [IsNoetherianRing A]
  [AddCommGroup M] [Module A M] [Module.Finite A M]
  [AddCommGroup N] [Module A N] [Module.Finite A N]

/-- **The levels of `homCompletionEquiv`.**  If `s` is represented at level `n` by `f`, then
`homCompletionEquiv I s m` is represented at level `n` by `f m`. -/
theorem homCompletionEquiv_apply_val (I : Ideal A) (s : AdicCompletion I (M →ₗ[A] N)) (n : ℕ)
    (f : M →ₗ[A] N) (hf : s.val n = Submodule.Quotient.mk f) (m : M) :
    ((homCompletionEquiv I s) m).val n = Submodule.Quotient.mk (f m) := by
  have hd : s - of I (M →ₗ[A] N) f ∈ I ^ n • (⊤ : Submodule A (AdicCompletion I (M →ₗ[A] N))) := by
    rw [pow_smul_top_eq_ker_eval I.fg_of_isNoetherianRing, LinearMap.mem_ker, map_sub, eval_of]
    change s.val n - _ = 0
    rw [hf, Submodule.mkQ_apply, sub_self]
  have hd' : (homCompletionEquiv I (s - of I (M →ₗ[A] N) f)) m ∈
      I ^ n • (⊤ : Submodule A (AdicCompletion I N)) := by
    have h1 := Submodule.mem_map_of_mem (f := ((LinearMap.applyₗ m).comp
      (homCompletionEquiv I).toLinearMap)) hd
    rw [Submodule.map_smul''] at h1
    exact Submodule.smul_mono le_rfl le_top h1
  have h0 : ((homCompletionEquiv I (s - of I (M →ₗ[A] N) f)) m).val n = 0 :=
    pow_smul_top_le_ker_eval (I := I) (M := N) n hd'
  rw [map_sub, LinearMap.sub_apply, homCompletionEquiv_of_apply] at h0
  exact (sub_eq_zero.1 h0).trans (eval_of I N n (f m))

section Tower

variable (I : Ideal A) {Q : ℕ → Type u} [∀ k, AddCommGroup (Q k)] [∀ k, Module A (Q k)]
  (π : ∀ k, N →ₗ[A] Q k) (hπ : ∀ k, Function.Surjective (π k))
  (hker : ∀ k, LinearMap.ker (π k) = I ^ (k + 1) • (⊤ : Submodule A N))
  (τ : ∀ k, Q (k + 1) →ₗ[A] Q k) (hτ : ∀ k, τ k ∘ₗ π (k + 1) = π k)

/-- Postcomposition with `π k`, on homomorphisms modulo `Iᵏ⁺¹`. -/
def homTowerMap (k : ℕ) :
    ((M →ₗ[A] N) ⧸ (I ^ (k + 1) • (⊤ : Submodule A (M →ₗ[A] N)))) →ₗ[A] (M →ₗ[A] Q k) :=
  Submodule.liftQ _ (LinearMap.compRight A (π k)) (by
    refine Submodule.smul_le.2 fun a ha f _ => ?_
    rw [LinearMap.mem_ker]
    ext m
    change π k (a • f m) = 0
    rw [← LinearMap.mem_ker, hker]
    exact Submodule.smul_mem_smul ha Submodule.mem_top)

omit [IsNoetherianRing A] [Module.Finite A M] [Module.Finite A N] in
/-- `homTowerMap` sends the class of `f` to `π k ∘ₗ f`. -/
theorem homTowerMap_mk (k : ℕ) (f : M →ₗ[A] N) :
    homTowerMap I π hker k (Submodule.Quotient.mk f) = (π k) ∘ₗ f :=
  rfl

/-- The identification `N / Iᵏ⁺¹ N ≃ Q k` induced by `π k`. -/
def towerQuotEquiv (k : ℕ) : (N ⧸ (I ^ (k + 1) • (⊤ : Submodule A N))) ≃ₗ[A] Q k :=
  (Submodule.quotEquivOfEq _ _ (hker k).symm).trans ((π k).quotKerEquivOfSurjective (hπ k))

omit [IsNoetherianRing A] [Module.Finite A N] in
/-- `towerQuotEquiv` sends the class of `x` to `π k x`. -/
theorem towerQuotEquiv_mk (k : ℕ) (x : N) :
    towerQuotEquiv I π hπ hker k (Submodule.Quotient.mk x) = π k x :=
  rfl

include hτ in
omit [IsNoetherianRing A] [Module.Finite A N] in
/-- Under the identifications `towerQuotEquiv`, the transition `τ k` corresponds to the
projection `N / Iᵏ⁺² N → N / Iᵏ⁺¹ N`. -/
theorem towerQuotEquiv_symm_τ (k : ℕ) (y : Q (k + 1)) :
    (towerQuotEquiv I π hπ hker k).symm (τ k y) =
      Submodule.factorPow I N (Nat.le_add_right (k + 1) 1)
        ((towerQuotEquiv I π hπ hker (k + 1)).symm y) := by
  obtain ⟨x, rfl⟩ := (towerQuotEquiv I π hπ hker (k + 1)).surjective y
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_eq, towerQuotEquiv_mk]
  change _ = π k x
  rw [← hτ k]
  rfl

omit [IsNoetherianRing A] in
/-- The projections `P / Iᶜ P → P / Iᵇ P → P / Iᵃ P` compose to the projection
`P / Iᶜ P → P / Iᵃ P`. -/
theorem factorPow_factorPow_apply (P : Type u) [AddCommGroup P] [Module A P] {a b c : ℕ}
    (h1 : a ≤ b) (h2 : b ≤ c) (x : P ⧸ (I ^ c • (⊤ : Submodule A P))) :
    Submodule.factorPow I P h1 (Submodule.factorPow I P h2 x) =
      Submodule.factorPow I P (h1.trans h2) x := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

/-- A family of elements of the truncations `P / Iᵏ⁺¹ P`, compatible under the transitions, as
an element of the `I`-adic completion of `P`. -/
def ofSuccFamily (P : Type u) [AddCommGroup P] [Module A P]
    (s : ∀ k, P ⧸ (I ^ (k + 1) • (⊤ : Submodule A P)))
    (hs : ∀ k, Submodule.factorPow I P (Nat.le_add_right (k + 1) 1) (s (k + 1)) = s k) :
    AdicCompletion I P :=
  ⟨fun n => Submodule.factorPow I P (Nat.le_add_right n 1) (s n), by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => exact factorPow_factorPow_apply I P le_rfl _ _
    | succ n hmn ih =>
      dsimp only at ih ⊢
      rw [← ih, ← hs n]
      simp only [factorPow_factorPow_apply]⟩

omit [IsNoetherianRing A] in
/-- The level `k + 1` component of `ofSuccFamily I P s hs` is `s k`. -/
theorem ofSuccFamily_val_succ (P : Type u) [AddCommGroup P] [Module A P]
    (s : ∀ k, P ⧸ (I ^ (k + 1) • (⊤ : Submodule A P)))
    (hs : ∀ k, Submodule.factorPow I P (Nat.le_add_right (k + 1) 1) (s (k + 1)) = s k) (k : ℕ) :
    (ofSuccFamily I P s hs).val (k + 1) = s k :=
  hs k

omit [IsNoetherianRing A] in
variable {I} in
/-- Any two elements of the `I`-adic completion of `P` agree at level `0`. -/
theorem val_zero_eq (P : Type u) [AddCommGroup P] [Module A P] (x y : AdicCompletion I P) :
    x.val 0 = y.val 0 := by
  have : Subsingleton (P ⧸ (I ^ 0 • (⊤ : Submodule A P))) := by
    rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]
    exact Submodule.Quotient.subsingleton_iff.2 rfl
  exact Subsingleton.elim _ _

include hτ in
omit [IsNoetherianRing A] [Module.Finite A M] [Module.Finite A N] in
/-- For a compatible family `s` of truncated homomorphisms, the maps `homTowerMap I π hker k (s k)`
are compatible under the transitions `τ k`. -/
theorem homTowerMap_compat (s : ∀ k, (M →ₗ[A] N) ⧸ (I ^ (k + 1) • (⊤ : Submodule A (M →ₗ[A] N))))
    (hs : ∀ k, Submodule.factorPow I (M →ₗ[A] N) (Nat.le_add_right (k + 1) 1) (s (k + 1)) = s k)
    (k : ℕ) : τ k ∘ₗ homTowerMap I π hker (k + 1) (s (k + 1)) = homTowerMap I π hker k (s k) := by
  rw [← hs k]
  obtain ⟨f, hf⟩ := Submodule.Quotient.mk_surjective _ (s (k + 1))
  rw [← hf]
  change τ k ∘ₗ (π (k + 1) ∘ₗ f) = π k ∘ₗ f
  rw [← LinearMap.comp_assoc, hτ]

/-- The map from compatible families of truncated homomorphisms to compatible families of maps
into the truncations. -/
def homTowerFamilyMap :
    {s : ∀ k, (M →ₗ[A] N) ⧸ (I ^ (k + 1) • (⊤ : Submodule A (M →ₗ[A] N))) //
        ∀ k, Submodule.factorPow I (M →ₗ[A] N) (Nat.le_add_right (k + 1) 1) (s (k + 1)) = s k} →
      {t : ∀ k, M →ₗ[A] Q k // ∀ k, τ k ∘ₗ t (k + 1) = t k} :=
  fun s => ⟨fun k => homTowerMap I π hker k (s.1 k), homTowerMap_compat I π hker τ hτ s.1 s.2⟩

/-- If `s k` is represented by `f`, then the image of `m` under
`homCompletionEquiv I (ofSuccFamily I _ s hs)` is represented at level `k + 1` by `f m`. -/
theorem homCompletionEquiv_ofSuccFamily_val_succ
    (s : ∀ k, (M →ₗ[A] N) ⧸ (I ^ (k + 1) • (⊤ : Submodule A (M →ₗ[A] N))))
    (hs : ∀ k, Submodule.factorPow I (M →ₗ[A] N) (Nat.le_add_right (k + 1) 1) (s (k + 1)) = s k)
    (k : ℕ) (f : M →ₗ[A] N) (hf : s k = Submodule.Quotient.mk f) (m : M) :
    ((homCompletionEquiv I (ofSuccFamily I _ s hs)) m).val (k + 1) = Submodule.Quotient.mk (f m) :=
  homCompletionEquiv_apply_val I _ (k + 1) f ((ofSuccFamily_val_succ I _ s hs k).trans hf) m

/-- `homTowerFamilyMap` is injective. -/
theorem injective_homTowerFamilyMap :
    Function.Injective (homTowerFamilyMap (M := M) I π hker τ hτ) := by
  intro s s' h
  have hk : ∀ k, homTowerMap I π hker k (s.1 k) = homTowerMap I π hker k (s'.1 k) := fun k =>
    congrArg (fun t => t.1 k) h
  have heq : ofSuccFamily I _ s.1 s.2 = ofSuccFamily I _ s'.1 s'.2 := by
    apply (homCompletionEquiv I).injective
    ext m n
    cases n with
    | zero => exact val_zero_eq N _ _
    | succ k =>
      obtain ⟨f, hf⟩ := Submodule.Quotient.mk_surjective _ (s.1 k)
      obtain ⟨f', hf'⟩ := Submodule.Quotient.mk_surjective _ (s'.1 k)
      rw [homCompletionEquiv_ofSuccFamily_val_succ I s.1 s.2 k f hf.symm m,
        homCompletionEquiv_ofSuccFamily_val_succ I s'.1 s'.2 k f' hf'.symm m,
        Submodule.Quotient.eq, ← hker k, LinearMap.mem_ker, map_sub, sub_eq_zero]
      have h1 := LinearMap.congr_fun (hk k) m
      rwa [← hf, ← hf'] at h1
  refine Subtype.ext (funext fun k => ?_)
  rw [← ofSuccFamily_val_succ I _ s.1 s.2 k, heq, ofSuccFamily_val_succ]

include hπ in
/-- `homTowerFamilyMap` is surjective. -/
theorem surjective_homTowerFamilyMap :
    Function.Surjective (homTowerFamilyMap (M := M) I π hker τ hτ) := by
  intro t
  let ρ := towerQuotEquiv I π hπ hker
  let u : ∀ n, M →ₗ[A] N ⧸ (I ^ n • (⊤ : Submodule A N)) := fun n =>
    Submodule.factorPow I N (Nat.le_add_right n 1) ∘ₗ (ρ n).symm.toLinearMap ∘ₗ t.1 n
  have hρ : ∀ (n : ℕ) (x : M), Submodule.factorPow I N (Nat.le_add_right (n + 1) 1)
      ((ρ (n + 1)).symm (t.1 (n + 1) x)) = (ρ n).symm (t.1 n x) := fun n x => by
    rw [← t.2 n, LinearMap.comp_apply, towerQuotEquiv_symm_τ I π hπ hker τ hτ]
  have hstep : ∀ n, transitionMap I N (Nat.le_add_right n 1) ∘ₗ u (n + 1) = u n := by
    intro n
    ext x
    exact congrArg (Submodule.factorPow I N (Nat.le_add_right n 1)) (hρ n x)
  have hu : ∀ {m n : ℕ} (hle : m ≤ n), transitionMap I N hle ∘ₗ u n = u m := by
    intro m n hle
    induction n, hle using Nat.le_induction with
    | base =>
      ext x
      exact factorPow_factorPow_apply I N le_rfl (Nat.le_add_right m 1) _
    | succ n hmn ih =>
      rw [← ih, ← hstep n]
      ext x
      simp only [LinearMap.comp_apply]
      exact (factorPow_factorPow_apply I N hmn (Nat.le_add_right n 1) _).symm
  let g := lift I u hu
  let sh := (homCompletionEquiv I).symm g
  refine ⟨⟨fun k => sh.val (k + 1), fun k => transitionMap_comp_eval_apply I _ _ sh⟩, ?_⟩
  refine Subtype.ext (funext fun k => ?_)
  obtain ⟨f, hf⟩ := Submodule.Quotient.mk_surjective _ (sh.val (k + 1))
  change homTowerMap I π hker k (sh.val (k + 1)) = t.1 k
  rw [← hf]
  ext x
  change π k (f x) = t.1 k x
  have h1 : ((homCompletionEquiv I sh) x).val (k + 1) = Submodule.Quotient.mk (f x) :=
    homCompletionEquiv_apply_val I sh (k + 1) f hf.symm x
  rw [LinearEquiv.apply_symm_apply] at h1
  exact (ρ k).eq_symm_apply.1 (h1.symm.trans (hρ k x))

include hπ in
/-- **Compatible families of truncated homomorphisms are compatible families of maps into the
truncations**: for `M`, `N` finite over a Noetherian ring and a tower `(Q k)` presenting the
truncations `N / Iᵏ⁺¹ N`, postcomposition is a bijection. -/
theorem bijective_homTowerFamilyMap :
    Function.Bijective (homTowerFamilyMap (M := M) I π hker τ hτ) :=
  ⟨injective_homTowerFamilyMap I π hker τ hτ, surjective_homTowerFamilyMap I π hπ hker τ hτ⟩

end Tower

end AdicCompletion

end
