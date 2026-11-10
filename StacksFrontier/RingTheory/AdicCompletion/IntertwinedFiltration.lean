module

public import Mathlib.RingTheory.AdicCompletion.Basic

/-!
# Intertwined filtrations have the same completion

Let `A` be a commutative ring, `I ⊆ A` an ideal and `M` an `A`-module. A descending filtration
`(K n)` of `M` by submodules is *intertwined with the `I`-adic filtration with shift `c`* when

* `I ^ n M ≤ K n` for every `n`, and
* `K n ≤ I ^ (n - c) M` for every `n ≥ c`.

Then the limit of the tower `n ↦ M ⧸ K n` is the `I`-adic completion `M^∧_I`.

Moreover, let `(P n)` be a tower of `A`-modules with compatible maps `π n : M → P n`, let
`K n = ker (π n)` be intertwined as above, and assume `im (P k → P n) = im (π n)` whenever
`k ≥ n + c`. Then the limit of `(P n)` is `M^∧_I` as well.

## Main definitions

* `Stacks.IntertwinedFiltration.towerLimit` — the limit of an `ℕ`-indexed tower of `A`-modules,
  realised as the submodule of compatible families in the product.
* `Stacks.IntertwinedFiltration.quotTransition` — the transition maps of the tower `M ⧸ K n`.
* `Stacks.IntertwinedFiltration.toAdicCompletion`, `Stacks.IntertwinedFiltration.ofAdicCompletion`
  — the two comparison maps between `lim_n M ⧸ K n` and `M^∧_I`.
* `Stacks.IntertwinedFiltration.quotKerEmbed` — the injection `M ⧸ ker (π n) ↪ P n`.

## Main results

* `Stacks.IntertwinedFiltration.adicCompletionEquiv` — an intertwined filtration computes the
  `I`-adic completion: `lim_n M ⧸ K n ≃ₗ[A] M^∧_I`.
* `Stacks.IntertwinedFiltration.towerComparison_bijective` and
  `Stacks.IntertwinedFiltration.towerLimitEquivQuotTowerLimit` — the limit of `(P n)` agrees with
  the limit of `(M ⧸ ker (π n))`.
* `Stacks.IntertwinedFiltration.adicCompletionEquivTowerLimit` — the assembled statement
  `M^∧_I ≃ₗ[A] lim_n P n`.

## References

* [Stacks Project, Tag 02OC](https://stacks.math.columbia.edu/tag/02OC)
* [Stacks Project, Tag 02OB](https://stacks.math.columbia.edu/tag/02OB)
-/

@[expose] public section

namespace Stacks.IntertwinedFiltration

variable {A : Type*} [CommRing A]

/-! ### The limit of an `ℕ`-indexed tower -/

section Tower

variable (P : ℕ → Type*) [∀ n, AddCommGroup (P n)] [∀ n, Module A (P n)]
  (T : ∀ m n : ℕ, m ≤ n → P n →ₗ[A] P m)

/-- The limit `lim_n P n` of a tower of `A`-modules with transition maps `T`, realised as the
submodule of the product consisting of the families compatible with every transition. -/
public def towerLimit : Submodule A (∀ n, P n) where
  carrier := {x | ∀ (m n : ℕ) (h : m ≤ n), T m n h (x n) = x m}
  add_mem' := by
    intro x y hx hy m n h
    simp only [Pi.add_apply, map_add, hx m n h, hy m n h]
  zero_mem' := by
    intro m n h
    simp only [Pi.zero_apply, map_zero]
  smul_mem' := by
    intro a x hx m n h
    simp only [Pi.smul_apply, map_smul, hx m n h]

variable {P T}

/-- A family in the limit is compatible with every transition map of the tower. -/
public theorem towerLimit_compat (x : towerLimit P T) (m n : ℕ) (h : m ≤ n) :
    T m n h ((x : ∀ k, P k) n) = (x : ∀ k, P k) m :=
  x.2 m n h

/-- Two elements of the limit agree as soon as all their components do. -/
public theorem towerLimit_ext {x y : towerLimit P T}
    (h : ∀ n, (x : ∀ k, P k) n = (y : ∀ k, P k) n) : x = y :=
  Subtype.ext (funext h)

/-- The projection from the limit onto the `k`-th term of the tower. -/
public def towerLimit.proj (k : ℕ) : towerLimit P T →ₗ[A] P k where
  toFun x := (x : ∀ n, P n) k
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `towerLimit.proj k` sends a family to its `k`-th component. -/
@[simp]
public theorem towerLimit.proj_apply (k : ℕ) (x : towerLimit P T) :
    towerLimit.proj k x = (x : ∀ n, P n) k :=
  rfl

end Tower

/-! ### The tower of quotients by a descending filtration -/

section Quot

variable {M : Type*} [AddCommGroup M] [Module A M]

/-- The map induced by the identity of `M` on the quotients by two nested submodules sends a
class to the class of the same representative. -/
public theorem factor_quotient_mk {p q : Submodule A M} (H : p ≤ q) (a : M) :
    Submodule.factor H (Submodule.Quotient.mk a) = (Submodule.Quotient.mk a : M ⧸ q) :=
  rfl

/-- The transition maps of the tower `n ↦ M ⧸ K n` attached to an antitone filtration `K`. -/
public def quotTransition (K : ℕ → Submodule A M) (hK : Antitone K) (m n : ℕ) (h : m ≤ n) :
    M ⧸ K n →ₗ[A] M ⧸ K m :=
  Submodule.factor (hK h)

/-- The limit `lim_n M ⧸ K n` of the tower of quotients of an antitone filtration `K`. -/
public abbrev quotTowerLimit (K : ℕ → Submodule A M) (hK : Antitone K) :
    Submodule A (∀ n, M ⧸ K n) :=
  towerLimit (fun n ↦ M ⧸ K n) (quotTransition K hK)

end Quot

/-! ### Comparison of an intertwined filtration with the `I`-adic filtration -/

section Intertwined

variable {M : Type*} [AddCommGroup M] [Module A M] (I : Ideal A) (K : ℕ → Submodule A M) (c : ℕ)

/-- The upper intertwining bound, with the shift absorbed into the index: `K (n + c) ≤ I ^ n M`. -/
public theorem le_pow_smul_top
    (hKge : ∀ n, c ≤ n → K n ≤ I ^ (n - c) • (⊤ : Submodule A M)) (n : ℕ) :
    K (n + c) ≤ (I ^ n • ⊤ : Submodule A M) := by
  simpa using hKge (n + c) (Nat.le_add_left c n)

/-- The comparison map `lim_n M ⧸ K n → M^∧_I`, whose `n`-th component is induced by the
component of the family at level `n + c`. -/
public noncomputable def toAdicCompletion (hK : Antitone K)
    (hKge : ∀ n, c ≤ n → K n ≤ I ^ (n - c) • (⊤ : Submodule A M)) :
    quotTowerLimit K hK →ₗ[A] AdicCompletion I M :=
  AdicCompletion.lift I
    (fun n ↦ (Submodule.factor (le_pow_smul_top I K c hKge n)).comp
      (towerLimit.proj (n + c))) <| by
    intro m n hmn
    ext x
    simp only [LinearMap.coe_comp, Function.comp_apply, towerLimit.proj_apply]
    rw [← towerLimit_compat x (m + c) (n + c) (Nat.add_le_add_right hmn c)]
    exact (Submodule.factor_comp_apply (le_pow_smul_top I K c hKge n)
        (Submodule.pow_smul_top_le I M hmn) _).trans
      (Submodule.factor_comp_apply (hK (Nat.add_le_add_right hmn c))
        (le_pow_smul_top I K c hKge m) _).symm

/-- The `n`-th component of `toAdicCompletion` is the image of the component at level
`n + c`. -/
@[simp]
public theorem toAdicCompletion_val (hK : Antitone K)
    (hKge : ∀ n, c ≤ n → K n ≤ I ^ (n - c) • (⊤ : Submodule A M))
    (x : quotTowerLimit K hK) (n : ℕ) :
    (toAdicCompletion I K c hK hKge x).val n =
      Submodule.factor (le_pow_smul_top I K c hKge n) ((x : ∀ k, M ⧸ K k) (n + c)) :=
  rfl

/-- The comparison map `M^∧_I → lim_n M ⧸ K n`, induced levelwise by the lower intertwining
bound `I ^ n M ≤ K n`. -/
public noncomputable def ofAdicCompletion (hK : Antitone K)
    (hKle : ∀ n, I ^ n • (⊤ : Submodule A M) ≤ K n) :
    AdicCompletion I M →ₗ[A] quotTowerLimit K hK :=
  LinearMap.codRestrict _
    (LinearMap.pi fun n ↦ (Submodule.factor (hKle n)).comp (AdicCompletion.eval I M n)) <| by
    intro z m n hmn
    simp only [LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply,
      AdicCompletion.eval_apply]
    rw [← z.property hmn]
    exact (Submodule.factor_comp_apply (hKle n) (hK hmn) _).trans
      (Submodule.factor_comp_apply (Submodule.pow_smul_top_le I M hmn) (hKle m) _).symm

/-- The `n`-th component of `ofAdicCompletion` is the image of the `n`-th component. -/
@[simp]
public theorem ofAdicCompletion_coe (hK : Antitone K)
    (hKle : ∀ n, I ^ n • (⊤ : Submodule A M) ≤ K n) (z : AdicCompletion I M) (n : ℕ) :
    ((ofAdicCompletion I K hK hKle z : ∀ k, M ⧸ K k)) n =
      Submodule.factor (hKle n) (z.val n) :=
  rfl

/-- If the descending filtration `(K n)`
of `M` satisfies `I ^ n M ≤ K n` for all `n` and `K n ≤ I ^ (n - c) M` for all `n ≥ c`, then the
limit of the tower `n ↦ M ⧸ K n` is the `I`-adic completion of `M`. -/
public noncomputable def adicCompletionEquiv (hK : Antitone K)
    (hKle : ∀ n, I ^ n • (⊤ : Submodule A M) ≤ K n)
    (hKge : ∀ n, c ≤ n → K n ≤ I ^ (n - c) • (⊤ : Submodule A M)) :
    quotTowerLimit K hK ≃ₗ[A] AdicCompletion I M :=
  LinearEquiv.ofLinearMap (toAdicCompletion I K c hK hKge) (ofAdicCompletion I K hK hKle)
    (LinearMap.ext fun z ↦ AdicCompletion.ext fun n ↦ by
      change Submodule.factor (le_pow_smul_top I K c hKge n)
          ((ofAdicCompletion I K hK hKle z : ∀ k, M ⧸ K k) (n + c)) = z.val n
      rw [ofAdicCompletion_coe]
      exact (Submodule.factor_comp_apply (hKle (n + c))
          (le_pow_smul_top I K c hKge n) _).trans (z.property (Nat.le_add_right n c)))
    (LinearMap.ext fun x ↦ towerLimit_ext fun n ↦ by
      change Submodule.factor (hKle n) ((toAdicCompletion I K c hK hKge x).val n) =
        (x : ∀ k, M ⧸ K k) n
      rw [toAdicCompletion_val]
      exact (Submodule.factor_comp_apply (le_pow_smul_top I K c hKge n) (hKle n) _).trans
        (towerLimit_compat x n (n + c) (Nat.le_add_right n c)))

end Intertwined

/-! ### The tower of a compatible family of maps out of `M` -/

section TowerOfMaps

variable {M : Type*} [AddCommGroup M] [Module A M]
  (P : ℕ → Type*) [∀ n, AddCommGroup (P n)] [∀ n, Module A (P n)]
  (T : ∀ m n : ℕ, m ≤ n → P n →ₗ[A] P m) (π : ∀ n, M →ₗ[A] P n)

/-- The kernels of a compatible family of maps out of `M` form a descending filtration. -/
public theorem antitone_ker (hπ : ∀ (m n : ℕ) (h : m ≤ n), (T m n h).comp (π n) = π m) :
    Antitone fun n ↦ LinearMap.ker (π n) := by
  intro m n h x hx
  rw [LinearMap.mem_ker] at hx ⊢
  rw [← LinearMap.congr_fun (hπ m n h) x]
  simp [hx]

/-- The injection `M ⧸ ker (π n) ↪ P n` given by the first isomorphism theorem. -/
public def quotKerEmbed (n : ℕ) : M ⧸ LinearMap.ker (π n) →ₗ[A] P n :=
  (LinearMap.ker (π n)).liftQ (π n) le_rfl

/-- `quotKerEmbed` sends the class of `a` to `π n a`. -/
@[simp]
public theorem quotKerEmbed_mk (n : ℕ) (a : M) :
    quotKerEmbed P π n (Submodule.Quotient.mk a) = π n a :=
  rfl

/-- The first isomorphism theorem: `M ⧸ ker (π n) → P n` is injective. -/
public theorem quotKerEmbed_injective (n : ℕ) : Function.Injective (quotKerEmbed P π n) :=
  LinearMap.ker_eq_bot.1 (Submodule.ker_liftQ_eq_bot _ _ _ le_rfl)

/-- The injections `M ⧸ ker (π n) ↪ P n` are compatible with the transition maps. -/
public theorem quotKerEmbed_compat (hπ : ∀ (m n : ℕ) (h : m ≤ n), (T m n h).comp (π n) = π m)
    (y : quotTowerLimit (fun n ↦ LinearMap.ker (π n)) (antitone_ker P T π hπ))
    (m n : ℕ) (h : m ≤ n) :
    T m n h (quotKerEmbed P π n ((y : ∀ k, M ⧸ LinearMap.ker (π k)) n)) =
      quotKerEmbed P π m ((y : ∀ k, M ⧸ LinearMap.ker (π k)) m) := by
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective (LinearMap.ker (π n))
    ((y : ∀ k, M ⧸ LinearMap.ker (π k)) n)
  rw [← towerLimit_compat y m n h, ← ha]
  change T m n h (quotKerEmbed P π n (Submodule.Quotient.mk a)) =
    quotKerEmbed P π m (Submodule.factor (antitone_ker P T π hπ h) (Submodule.Quotient.mk a))
  rw [factor_quotient_mk, quotKerEmbed_mk, quotKerEmbed_mk]
  exact LinearMap.congr_fun (hπ m n h) a

/-- The comparison map `lim_n M ⧸ ker (π n) → lim_n P n`, built from the injections
`M ⧸ ker (π n) ↪ P n`. -/
public def towerComparison (hπ : ∀ (m n : ℕ) (h : m ≤ n), (T m n h).comp (π n) = π m) :
    quotTowerLimit (fun n ↦ LinearMap.ker (π n)) (antitone_ker P T π hπ) →ₗ[A] towerLimit P T :=
  LinearMap.codRestrict _
    (LinearMap.pi fun n ↦ (quotKerEmbed P π n).comp (towerLimit.proj n))
    fun y m n h ↦ quotKerEmbed_compat P T π hπ y m n h

/-- The `n`-th component of `towerComparison` is `quotKerEmbed` of the `n`-th component. -/
@[simp]
public theorem towerComparison_coe (hπ : ∀ (m n : ℕ) (h : m ≤ n), (T m n h).comp (π n) = π m)
    (y : quotTowerLimit (fun n ↦ LinearMap.ker (π n)) (antitone_ker P T π hπ)) (n : ℕ) :
    ((towerComparison P T π hπ y : ∀ k, P k)) n =
      quotKerEmbed P π n ((y : ∀ k, M ⧸ LinearMap.ker (π k)) n) :=
  rfl

/-- If every map `P k → P n` with `k ≥ n + c` has image exactly `im (π n)`, then the comparison
map from the limit of the tower `(M ⧸ ker (π n))` to the limit of the tower `(P n)` is
bijective. -/
public theorem towerComparison_bijective (c : ℕ)
    (hπ : ∀ (m n : ℕ) (h : m ≤ n), (T m n h).comp (π n) = π m)
    (hrange : ∀ (n k : ℕ) (h : n ≤ k), n + c ≤ k →
      LinearMap.range (T n k h) = LinearMap.range (π n)) :
    Function.Bijective (towerComparison P T π hπ) := by
  constructor
  · intro y y' hyy'
    refine towerLimit_ext fun n ↦ quotKerEmbed_injective P π n ?_
    rw [← towerComparison_coe P T π hπ y n, ← towerComparison_coe P T π hπ y' n, hyy']
  · intro x
    have hmem : ∀ n : ℕ, ∃ a : M, π n a = (x : ∀ k, P k) n := fun n ↦ by
      rw [← LinearMap.mem_range, ← hrange n (n + c) (Nat.le_add_right n c) le_rfl]
      exact ⟨(x : ∀ k, P k) (n + c), towerLimit_compat x n (n + c) (Nat.le_add_right n c)⟩
    choose a ha using hmem
    refine ⟨⟨fun n ↦ Submodule.Quotient.mk (a n), ?_⟩, towerLimit_ext fun n ↦ ?_⟩
    · intro m n h
      change Submodule.factor (antitone_ker P T π hπ h) (Submodule.Quotient.mk (a n)) =
        (Submodule.Quotient.mk (a m) : M ⧸ LinearMap.ker (π m))
      rw [factor_quotient_mk, Submodule.Quotient.eq, LinearMap.mem_ker, map_sub, sub_eq_zero]
      rw [← LinearMap.congr_fun (hπ m n h) (a n), LinearMap.comp_apply, ha n,
        towerLimit_compat x m n h, ha m]
    · rw [towerComparison_coe]
      exact (quotKerEmbed_mk P π n (a n)).trans (ha n)

/-- The limit of the tower `(P n)` is the limit of the tower `(M ⧸ ker (π n))`. -/
public noncomputable def towerLimitEquivQuotTowerLimit (c : ℕ)
    (hπ : ∀ (m n : ℕ) (h : m ≤ n), (T m n h).comp (π n) = π m)
    (hrange : ∀ (n k : ℕ) (h : n ≤ k), n + c ≤ k →
      LinearMap.range (T n k h) = LinearMap.range (π n)) :
    quotTowerLimit (fun n ↦ LinearMap.ker (π n)) (antitone_ker P T π hπ) ≃ₗ[A] towerLimit P T :=
  LinearEquiv.ofBijective _ (towerComparison_bijective P T π c hπ hrange)

/-- Let `(P n)` be a tower of `A`-modules with compatible maps `π n : M → P n`. Assume there is
a `c` with

* `I ^ n M ≤ ker (π n)` for all `n`;
* `ker (π n) ≤ I ^ (n - c) M` for all `n ≥ c`;
* `im (P k → P n) = im (π n)` whenever `k ≥ n + c`.

Then the `I`-adic completion of `M` is the limit of the tower `(P n)`. -/
public noncomputable def adicCompletionEquivTowerLimit (I : Ideal A) (c : ℕ)
    (hπ : ∀ (m n : ℕ) (h : m ≤ n), (T m n h).comp (π n) = π m)
    (hker : ∀ n, I ^ n • (⊤ : Submodule A M) ≤ LinearMap.ker (π n))
    (hker' : ∀ n, c ≤ n → LinearMap.ker (π n) ≤ I ^ (n - c) • (⊤ : Submodule A M))
    (hrange : ∀ (n k : ℕ) (h : n ≤ k), n + c ≤ k →
      LinearMap.range (T n k h) = LinearMap.range (π n)) :
    AdicCompletion I M ≃ₗ[A] towerLimit P T :=
  (adicCompletionEquiv I (fun n ↦ LinearMap.ker (π n)) c (antitone_ker P T π hπ) hker
      hker').symm.trans
    (towerLimitEquivQuotTowerLimit P T π c hπ hrange)

end TowerOfMaps

end Stacks.IntertwinedFiltration

end
