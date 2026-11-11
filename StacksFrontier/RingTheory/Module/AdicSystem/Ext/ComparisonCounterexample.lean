module

public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.RingTheory.Polynomial.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Module.AdicSystem.Ext.DelayedIso

/-!
# Ext over adic quotients: one exponent does not suffice (Tag 0EGZ)

Remark 0EGZ of the Stacks project asserts a single `c ≥ 0` such that for `m ≫ n ≫ 0` there are
maps `I ^ c Eₘ / I ^ n Eₘ → Eₙ / Eₙ[I ^ c]` with kernel and cokernel annihilated by `I ^ c`, where
`Eₙ = Ext^i_{Aₙ}(Mₙ, Nₙ)`. This file shows that no such `c` exists, for any choice of maps, when
`A = k[x, y, z]`, `I = (x, y, z)`, `M = A / (x)`, `N = A / (x²)` and `i = 0`.

Here `Eₙ` is the module of `x`-torsion elements of `Nₙ = A / (x², Iⁿ)`: up to a part killed by
`I`, it is `x · k[y, z] / (y, z) ^ (n - 1)`, a copy of the adic quotients of `k[y, z]` shifted by
one degree. Counting dimensions over `k` shows that the kernel of any map of the displayed shape is
too large to be killed by `I ^ c`: multiplication by `z ^ c` must factor through the image, which
lies in a space of dimension about `(n - c) ^ 2 / 2`, while it has rank about
`(n - c) ^ 2 / 2 + (n - c) - c ^ 2`.
-/

@[expose] public section

/-! ## Tag 0EGZ -/

section

open CategoryTheory CategoryTheory.Abelian Filter MvPolynomial Finsupp

universe u

namespace Stacks.AdicSystem.ExtComparisonCounterexample

open Stacks.Modules.AdicSystem Stacks.Modules.AdicSystem.AdicModuleSystem
  Stacks.AdicSystem.ExtDelayedIso

noncomputable section

/-! ### Transport along linear equivalences -/

section Transport

variable {A : Type*} [CommRing A] (I : Ideal A)

private theorem smul_top_le_comap {X X' : Type*} [AddCommGroup X] [Module A X]
    [AddCommGroup X'] [Module A X'] (g : X →ₗ[A] X') (J : Ideal A) :
    J • (⊤ : Submodule A X) ≤ (J • (⊤ : Submodule A X')).comap g :=
  Submodule.smul_le.mpr fun r hr x _ => by
    rw [Submodule.mem_comap, map_smul]
    exact Submodule.smul_mem_smul hr Submodule.mem_top

/-- The map induced by `g` on `I ^ c X / I ^ n X`. -/
private def sourceMap {X X' : Type*} [AddCommGroup X] [Module A X]
    [AddCommGroup X'] [Module A X'] (g : X →ₗ[A] X') (c n : ℕ) :
    (↥(I ^ c • (⊤ : Submodule A X)) ⧸
        (I ^ n • (⊤ : Submodule A X)).comap (I ^ c • (⊤ : Submodule A X)).subtype) →ₗ[A]
      (↥(I ^ c • (⊤ : Submodule A X')) ⧸
        (I ^ n • (⊤ : Submodule A X')).comap (I ^ c • (⊤ : Submodule A X')).subtype) :=
  Submodule.mapQ _ _ (g.restrict fun _ hx => smul_top_le_comap g (I ^ c) hx) fun _ hx =>
    smul_top_le_comap g (I ^ n) hx

private theorem sourceMap_symm_apply {X X' : Type*} [AddCommGroup X] [Module A X]
    [AddCommGroup X'] [Module A X'] (e : X ≃ₗ[A] X') (c n : ℕ) (z) :
    sourceMap I e.toLinearMap c n (sourceMap I e.symm.toLinearMap c n z) = z := by
  induction z using Submodule.Quotient.induction_on with
  | H x =>
    change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    congr 1
    exact Subtype.ext (e.apply_symm_apply x.1)

/-- The map induced by `g` on `Y / Y[I ^ c]`. -/
private def targetMap {Y Y' : Type*} [AddCommGroup Y] [Module A Y]
    [AddCommGroup Y'] [Module A Y'] (g : Y →ₗ[A] Y') (c : ℕ) :
    (Y ⧸ Submodule.torsionBySet A Y (↑(I ^ c) : Set A)) →ₗ[A]
      (Y' ⧸ Submodule.torsionBySet A Y' (↑(I ^ c) : Set A)) :=
  Submodule.mapQ _ _ g fun y hy => by
    rw [Submodule.mem_comap, Submodule.mem_torsionBySet_iff]
    intro a
    rw [← map_smul, (Submodule.mem_torsionBySet_iff _ _).mp hy a, map_zero]

private theorem targetMap_symm_apply {Y Y' : Type*} [AddCommGroup Y] [Module A Y]
    [AddCommGroup Y'] [Module A Y'] (e : Y ≃ₗ[A] Y') (c : ℕ) (z) :
    targetMap I e.symm.toLinearMap c (targetMap I e.toLinearMap c z) = z := by
  induction z using Submodule.Quotient.induction_on with
  | H y =>
    change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    rw [LinearEquiv.coe_coe, LinearEquiv.coe_coe, e.symm_apply_apply]

/-- A map `I ^ c X / I ^ n X → Y / Y[I ^ d]` whose kernel is killed by `I ^ d` transports along
linear equivalences of `X` and of `Y`. -/
private theorem transport {X X' Y Y' : Type*} [AddCommGroup X] [Module A X]
    [AddCommGroup X'] [Module A X'] [AddCommGroup Y] [Module A Y] [AddCommGroup Y'] [Module A Y']
    (e : X ≃ₗ[A] X') (e' : Y ≃ₗ[A] Y') (c n d : ℕ)
    (f : (↥(I ^ c • (⊤ : Submodule A X)) ⧸
        (I ^ n • (⊤ : Submodule A X)).comap (I ^ c • (⊤ : Submodule A X)).subtype) →ₗ[A]
      (Y ⧸ Submodule.torsionBySet A Y (↑(I ^ d) : Set A)))
    (hf : ∀ z, f z = 0 → ∀ a ∈ I ^ d, a • z = 0) :
    ∃ f' : (↥(I ^ c • (⊤ : Submodule A X')) ⧸
        (I ^ n • (⊤ : Submodule A X')).comap (I ^ c • (⊤ : Submodule A X')).subtype) →ₗ[A]
      (Y' ⧸ Submodule.torsionBySet A Y' (↑(I ^ d) : Set A)),
      ∀ z, f' z = 0 → ∀ a ∈ I ^ d, a • z = 0 := by
  refine ⟨targetMap I e'.toLinearMap d ∘ₗ f ∘ₗ sourceMap I e.symm.toLinearMap c n, ?_⟩
  intro z hz a ha
  have h1 : f (sourceMap I e.symm.toLinearMap c n z) = 0 := by
    have := congrArg (targetMap I e'.symm.toLinearMap d) hz
    rwa [LinearMap.comp_apply, LinearMap.comp_apply, targetMap_symm_apply, map_zero] at this
  have h2 := hf _ h1 a ha
  rw [← map_smul] at h2
  rw [← sourceMap_symm_apply I e c n (a • z), h2, map_zero]

end Transport

/-! ### `Ext⁰` over `Aₙ` of a cyclic module -/

namespace ExtZero

variable {A : Type u} [CommRing A] (I : Ideal A) (x : A) (N : Type u) [AddCommGroup N]
  [Module A N]

private theorem quotient_isScalarTower {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (J : Ideal R) : IsScalarTower R (R ⧸ J) (M ⧸ J • (⊤ : Submodule R M)) :=
  IsScalarTower.of_algebraMap_smul fun r y => by
    induction y using Submodule.Quotient.induction_on with
    | H y => rfl

attribute [local instance] quotient_isScalarTower

/-- `Mₙ = (A / (x)) / Iⁿ`. -/
private abbrev Mq (n : ℕ) :=
  (A ⧸ Ideal.span {x}) ⧸ (I ^ n • (⊤ : Submodule A (A ⧸ Ideal.span {x})))

/-- `Nₙ = N / Iⁿ N`. -/
private abbrev Nq (n : ℕ) := N ⧸ (I ^ n • (⊤ : Submodule A N))

/-- The generator of `Mₙ`. -/
private def gM (n : ℕ) : Mq I x n := Submodule.Quotient.mk (Ideal.Quotient.mk _ 1)

private theorem smul_gM (n : ℕ) (a : A) :
    a • gM I x n = Submodule.Quotient.mk (Ideal.Quotient.mk _ a) := by
  have h : a • (Ideal.Quotient.mk (Ideal.span {x}) 1) = Ideal.Quotient.mk _ a := by
    rw [Algebra.smul_def, map_one, mul_one]
    rfl
  rw [gM, ← Submodule.Quotient.mk_smul, h]

private theorem x_smul_gM (n : ℕ) : x • gM I x n = 0 := by
  rw [smul_gM, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _),
    Submodule.Quotient.mk_zero]

private theorem exists_eq_smul_gM (n : ℕ) (y : Mq I x n) : ∃ a : A, y = a • gM I x n := by
  obtain ⟨y', rfl⟩ := Submodule.Quotient.mk_surjective _ y
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y'
  exact ⟨a, (smul_gM I x n a).symm⟩

private theorem smul_Nq_eq_zero {n : ℕ} {r : A} (hr : r ∈ I ^ n) (z : Nq I N n) : r • z = 0 :=
  Module.isTorsionBySet_quotient_ideal_smul N (I ^ n) (x := z) (a := ⟨r, hr⟩)

private def ext0Equiv' {R : Type u} [CommRing R] (X Y : Type u) [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y] :
    Ext (ModuleCat.of R X) (ModuleCat.of R Y) 0 ≃ₗ[R] (X →ₗ[R] Y) :=
  Ext.linearEquiv₀.trans ModuleCat.homLinearEquiv

variable [IsNoetherianRing A] [Module.Finite A N]

/-- Evaluation at the generator, `Ext⁰_{Aₙ}(Mₙ, Nₙ) → Nₙ[x]`. -/
private def evalGen (n : ℕ+) :
    ↑(underlying (extOfAdicQuotientsSystem I (A ⧸ Ideal.span {x}) N 0) n) →ₗ[A]
      Submodule.torsionBy A (Nq I N n) x where
  toFun w := ⟨ext0Equiv' (R := A ⧸ I ^ (n : ℕ)) (Mq I x n) (Nq I N n) w (gM I x n), by
    rw [Submodule.mem_torsionBy_iff, ← LinearMap.map_smul_of_tower, x_smul_gM, map_zero]⟩
  map_add' w w' := by
    apply Subtype.ext
    exact congrArg (fun φ => φ (gM I x n))
      (map_add (ext0Equiv' (R := A ⧸ I ^ (n : ℕ)) (Mq I x n) (Nq I N n)) w w')
  map_smul' a w := by
    apply Subtype.ext
    exact (congrArg (fun φ => φ (gM I x n))
      (map_smul (ext0Equiv' (R := A ⧸ I ^ (n : ℕ)) (Mq I x n) (Nq I N n))
        (Ideal.Quotient.mk (I ^ (n : ℕ)) a)
        (show Ext (ModuleCat.of (A ⧸ I ^ (n : ℕ)) (Mq I x n))
          (ModuleCat.of (A ⧸ I ^ (n : ℕ)) (Nq I N n)) 0 from w))).trans
      (algebraMap_smul (A ⧸ I ^ (n : ℕ)) a _)

private theorem evalGen_bijective (n : ℕ+) : Function.Bijective (evalGen I x N n) := by
  constructor
  · intro w w' hww
    have h : ext0Equiv' (R := A ⧸ I ^ (n : ℕ)) (Mq I x n) (Nq I N n) w (gM I x n) =
        ext0Equiv' (R := A ⧸ I ^ (n : ℕ)) (Mq I x n) (Nq I N n) w' (gM I x n) :=
      congrArg Subtype.val hww
    apply (ext0Equiv' (R := A ⧸ I ^ (n : ℕ)) (Mq I x n) (Nq I N n)).injective
    refine LinearMap.ext fun y => ?_
    obtain ⟨a, rfl⟩ := exists_eq_smul_gM I x n y
    rw [LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower, h]
  · intro v
    let ψA : Mq I x n →ₗ[A] Nq I N n :=
      (I ^ (n : ℕ) • (⊤ : Submodule A (A ⧸ Ideal.span {x}))).liftQ
        ((Ideal.span {x}).liftQ (LinearMap.toSpanSingleton _ _ v.1) (by
            rw [Ideal.span, Submodule.span_le, Set.singleton_subset_iff]
            exact (Submodule.mem_torsionBy_iff _ _).mp v.2))
        (Submodule.smul_le.mpr fun r hr y _ => by
          rw [LinearMap.mem_ker, map_smul]
          exact smul_Nq_eq_zero I N hr _)
    let ψ : Mq I x n →ₗ[A ⧸ I ^ (n : ℕ)] Nq I N n :=
      ψA.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
    refine ⟨(ext0Equiv' (R := A ⧸ I ^ (n : ℕ)) (Mq I x n) (Nq I N n)).symm ψ, Subtype.ext ?_⟩
    change ext0Equiv' (R := A ⧸ I ^ (n : ℕ)) (Mq I x n) (Nq I N n)
      ((ext0Equiv' (R := A ⧸ I ^ (n : ℕ)) (Mq I x n) (Nq I N n)).symm ψ) (gM I x n) = v.1
    rw [LinearEquiv.apply_symm_apply]
    change (1 : A) • v.1 = v.1
    exact one_smul _ _

/-- `Ext⁰_{Aₙ}(Mₙ, Nₙ) ≅ Nₙ[x]` as `A`-modules, for `M = A / (x)`. -/
private def underlyingEquiv (n : ℕ+) :
    ↑(underlying (extOfAdicQuotientsSystem I (A ⧸ Ideal.span {x}) N 0) n) ≃ₗ[A]
      Submodule.torsionBy A (Nq I N n) x :=
  LinearEquiv.ofBijective (evalGen I x N n) (evalGen_bijective I x N n)

end ExtZero

/-! ### Polynomial bookkeeping in `k[x, y, z]` -/

variable (k : Type u) [Field k]

/-- The ideal `(x²) + Iᴺ` of `k[x, y, z]`, where `I` is generated by the variables. -/
private abbrev J (N : ℕ) : Ideal (MvPolynomial (Fin 3) k) :=
  Ideal.span {(X 0 : MvPolynomial (Fin 3) k) ^ 2} ⊔ idealOfVars (Fin 3) k ^ N

/-- The exponent of `x ^ e y ^ a z ^ b`. -/
private def ex (e a b : ℕ) : Fin 3 →₀ ℕ := single 0 e + single 1 a + single 2 b

private theorem ex_apply_zero (e a b : ℕ) : ex e a b 0 = e := by simp [ex]

private theorem ex_apply_one (e a b : ℕ) : ex e a b 1 = a := by simp [ex]

private theorem ex_apply_two (e a b : ℕ) : ex e a b 2 = b := by simp [ex]

private theorem degree_ex (e a b : ℕ) : degree (ex e a b) = e + a + b := by
  simp [ex, map_add, degree_single]

private theorem eq_ex (s : Fin 3 →₀ ℕ) : s = ex (s 0) (s 1) (s 2) := by
  ext i
  fin_cases i <;> simp [ex]

private theorem ex_inj {e a b e' a' b' : ℕ} (h : ex e a b = ex e' a' b') :
    e = e' ∧ a = a' ∧ b = b' := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [ex_apply_zero] using congrArg (· 0) h
  · simpa [ex_apply_one] using congrArg (· 1) h
  · simpa [ex_apply_two] using congrArg (· 2) h

private theorem ex_add (e a b e' a' b' : ℕ) :
    ex e a b + ex e' a' b' = ex (e + e') (a + a') (b + b') := by
  ext i
  fin_cases i <;> simp [ex]

private theorem X_zero_eq : (X 0 : MvPolynomial (Fin 3) k) = monomial (ex 1 0 0) 1 := by
  simp [ex, X]

/-- Coefficients below degree `N` and of `x`-degree at most one vanish on `(x²) + Iᴺ`. -/
private theorem coeff_eq_zero_of_mem_J {N : ℕ} {p : MvPolynomial (Fin 3) k} (hp : p ∈ J k N)
    {s : Fin 3 →₀ ℕ} (h0 : s 0 < 2) (hd : degree s < N) : p.coeff s = 0 := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hp
  rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, (mem_pow_idealOfVars_iff' N b).mp hb s hd,
    add_zero]
  obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp ha
  rw [X_pow_eq_monomial, coeff_mul_monomial', ite_eq_right_iff]
  intro h
  rw [Finsupp.single_le_iff] at h
  omega

/-- A polynomial all of whose monomials have `x`-degree at least two or degree at least `N` lies
in `(x²) + Iᴺ`. -/
private theorem mem_J_of_support {N : ℕ} {p : MvPolynomial (Fin 3) k}
    (h : ∀ s ∈ p.support, 2 ≤ s 0 ∨ N ≤ degree s) : p ∈ J k N := by
  rw [p.as_sum]
  refine Submodule.sum_mem _ fun s hs => ?_
  rcases h s hs with h0 | hd
  · apply Ideal.mem_sup_left
    refine Ideal.mem_span_singleton'.mpr ⟨monomial (s - single 0 2) (p.coeff s), ?_⟩
    rw [X_pow_eq_monomial, monomial_mul_monomial, mul_one,
      tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr h0)]
  · apply Ideal.mem_sup_right
    rw [mem_pow_idealOfVars_iff]
    intro t ht
    rw [Finset.mem_singleton.mp (support_monomial_subset ht)]
    exact hd

private theorem monomial_mem_pow {s : Fin 3 →₀ ℕ} {d : ℕ} (h : d ≤ degree s) :
    (monomial s (1 : k)) ∈ idealOfVars (Fin 3) k ^ d :=
  (monomial_mem_pow_idealOfVars_iff d s one_ne_zero).mpr h

private theorem J_mono {N N' : ℕ} (h : N ≤ N') : J k N' ≤ J k N :=
  sup_le_sup_left (Ideal.pow_le_pow_right h) _

private theorem mul_mem_J {c N : ℕ} {r q : MvPolynomial (Fin 3) k}
    (hr : r ∈ idealOfVars (Fin 3) k ^ c) (hq : q ∈ J k N) : r * q ∈ J k (c + N) := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hq
  rw [mul_add]
  refine add_mem (Ideal.mem_sup_left (Ideal.mul_mem_left _ _ ha)) (Ideal.mem_sup_right ?_)
  rw [pow_add]
  exact Ideal.mul_mem_mul hr hb

/-- If `x g ∈ (x²) + Iᵐ` with `m ≥ 2`, then `g` has no constant term. -/
private theorem mem_idealOfVars_of_X_mul_mem {m : ℕ} (hm : 2 ≤ m) {g : MvPolynomial (Fin 3) k}
    (hg : X 0 * g ∈ J k m) : g ∈ idealOfVars (Fin 3) k := by
  rw [← pow_one (idealOfVars (Fin 3) k), mem_pow_idealOfVars_iff']
  intro t ht
  have ht0 : t = 0 := (degree_eq_zero_iff t).mp (by omega)
  subst ht0
  have := coeff_eq_zero_of_mem_J k (s := 0 + single 0 1) hg (by simp) (by
    simp [degree_single]; omega)
  rwa [mul_comm, coeff_mul_X] at this

/-! ### The modules `Nₙ` and their `x`-torsion -/

private abbrev Nmod := MvPolynomial (Fin 3) k ⧸ Ideal.span {(X 0 : MvPolynomial (Fin 3) k) ^ 2}

private abbrev Nq (n : ℕ) :=
  Nmod k ⧸ (idealOfVars (Fin 3) k ^ n • (⊤ : Submodule (MvPolynomial (Fin 3) k) (Nmod k)))

/-- The quotient map `k[x, y, z] → Nₙ`. -/
private def πq (n : ℕ) : MvPolynomial (Fin 3) k →ₗ[MvPolynomial (Fin 3) k] Nq k n :=
  (Submodule.mkQ _) ∘ₗ (Submodule.mkQ (Ideal.span {(X 0 : MvPolynomial (Fin 3) k) ^ 2}))

private theorem πq_surjective (n : ℕ) : Function.Surjective (πq k n) :=
  (Submodule.mkQ_surjective _).comp (Submodule.mkQ_surjective _)

private theorem πq_eq_zero_iff (n : ℕ) (p : MvPolynomial (Fin 3) k) :
    πq k n p = 0 ↔ p ∈ J k n := by
  rw [πq, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero, Ideal.smul_top_eq_map, Submodule.restrictScalars_mem]
  change Ideal.Quotient.mk _ p ∈ _ ↔ _
  rw [Ideal.Quotient.algebraMap_eq, Ideal.mem_quotient_iff_mem_sup, sup_comm]

/-- The `x`-torsion of `Nₙ`, which is `Hom_{Aₙ}(Mₙ, Nₙ)`. -/
private abbrev Pq (n : ℕ) : Submodule (MvPolynomial (Fin 3) k) (Nq k n) :=
  Submodule.torsionBy (MvPolynomial (Fin 3) k) (Nq k n) (X 0)

private theorem πq_mem_Pq_iff (n : ℕ) (p : MvPolynomial (Fin 3) k) :
    πq k n p ∈ Pq k n ↔ X 0 * p ∈ J k n := by
  rw [Submodule.mem_torsionBy_iff, ← map_smul, smul_eq_mul, πq_eq_zero_iff]

private theorem X_mul_mem_J (n : ℕ) (h : MvPolynomial (Fin 3) k) :
    X 0 * (X 0 * h) ∈ J k n :=
  Ideal.mem_sup_left (Ideal.mem_span_singleton'.mpr ⟨h, by ring⟩)

/-- Elements of `Iⁿ Pₘ` lift to `Iⁿ⁺¹`. -/
private theorem exists_lift_of_mem_smul {n m : ℕ} (hm : 2 ≤ m) {v : Pq k m}
    (hv : v ∈ idealOfVars (Fin 3) k ^ n • (⊤ : Submodule (MvPolynomial (Fin 3) k) (Pq k m))) :
    ∃ p ∈ idealOfVars (Fin 3) k ^ (n + 1), v.1 = πq k m p := by
  refine Submodule.smul_induction_on (p := fun v : Pq k m =>
    ∃ p ∈ idealOfVars (Fin 3) k ^ (n + 1), v.1 = πq k m p) hv ?_ ?_
  · intro r hr w _
    obtain ⟨g, hg⟩ := πq_surjective k m w.1
    have hgP : X 0 * g ∈ J k m := (πq_mem_Pq_iff k m g).mp (hg ▸ w.2)
    refine ⟨r * g, ?_, ?_⟩
    · rw [pow_succ]
      exact Ideal.mul_mem_mul hr (mem_idealOfVars_of_X_mul_mem k hm hgP)
    · rw [Submodule.coe_smul, ← hg, ← smul_eq_mul, map_smul]
  · intro v w hv hw
    obtain ⟨p, hp, hpv⟩ := hv
    obtain ⟨q, hq, hqw⟩ := hw
    exact ⟨p + q, add_mem hp hq, by rw [Submodule.coe_add, hpv, hqw, map_add]⟩

/-! ### Counting -/

private theorem card_biUnion_antidiagonal (s : Finset ℕ) :
    (s.biUnion Finset.antidiagonal).card = ∑ e ∈ s, (e + 1) := by
  rw [Finset.card_biUnion]
  · simp
  · intro a _ b _ hab
    rw [Function.onFun, Finset.disjoint_left]
    intro p hpa hpb
    exact hab ((Finset.mem_antidiagonal.mp hpa).symm.trans (Finset.mem_antidiagonal.mp hpb))

private theorem sum_lt_sum_Ico {c n : ℕ} (hn : c * c + 2 * c + 2 ≤ n) :
    ∑ e ∈ Finset.range (n - 1 - c), (e + 1) < ∑ e ∈ Finset.Ico c (n - c), (e + 1) := by
  obtain ⟨K, hK⟩ : ∃ K, n - c = K + 1 := ⟨n - c - 1, by omega⟩
  have h1 : n - 1 - c = K := by omega
  rw [h1, hK]
  have hcK : c ≤ K + 1 := by have := hn; generalize c * c = q at this; omega
  have h2 := Finset.sum_range_add_sum_Ico (fun e => e + 1) hcK
  rw [Finset.sum_range_succ] at h2
  have h3 : ∑ e ∈ Finset.range c, (e + 1) ≤ c * c := by
    calc ∑ e ∈ Finset.range c, (e + 1) ≤ ∑ _e ∈ Finset.range c, c :=
          Finset.sum_le_sum fun e he => Finset.mem_range.mp he
      _ = c * c := by simp
  have h4 : c * c + c + 1 ≤ K := by have := hn; generalize c * c = q at this ⊢; omega
  generalize c * c = q at h3 h4
  generalize ∑ e ∈ Finset.range c, (e + 1) = a at h2 h3
  generalize ∑ e ∈ Finset.range K, (e + 1) = b at h2 ⊢
  generalize ∑ e ∈ Finset.Ico c (K + 1), (e + 1) = d at h2 ⊢
  omega

/-! ### The core count -/

/-- The source `I ^ c Pₘ / I ^ n Pₘ`. -/
private abbrev Src (c n m : ℕ) :=
  ↥(idealOfVars (Fin 3) k ^ c • (⊤ : Submodule (MvPolynomial (Fin 3) k) ↥(Pq k m))) ⧸
    (idealOfVars (Fin 3) k ^ n • (⊤ : Submodule (MvPolynomial (Fin 3) k) ↥(Pq k m))).comap
      (idealOfVars (Fin 3) k ^ c • (⊤ : Submodule (MvPolynomial (Fin 3) k) ↥(Pq k m))).subtype

/-- The target `Pₙ / Pₙ[I ^ c]`. -/
private abbrev Tgt (c n : ℕ) :=
  ↥(Pq k n) ⧸ Submodule.torsionBySet (MvPolynomial (Fin 3) k) ↥(Pq k n)
    (↑(idealOfVars (Fin 3) k ^ c) : Set (MvPolynomial (Fin 3) k))

/-- The class of `x` in `Pₘ`. -/
private def baseElt (m : ℕ) : Pq k m :=
  ⟨πq k m (X 0), (πq_mem_Pq_iff k m _).mpr (by simpa using X_mul_mem_J k m 1)⟩

/-- `r ↦ r x`, from `I ^ c` to `I ^ c Pₘ / I ^ n Pₘ`. -/
private def Ψ (c n m : ℕ) : ↥(idealOfVars (Fin 3) k ^ c) →ₗ[MvPolynomial (Fin 3) k] Src k c n m :=
  (Submodule.mkQ _) ∘ₗ
    (LinearMap.codRestrict _
      ((LinearMap.toSpanSingleton (MvPolynomial (Fin 3) k) (Pq k m) (baseElt k m)) ∘ₗ
        (idealOfVars (Fin 3) k ^ c).subtype)
      fun r => Submodule.smul_mem_smul r.2 Submodule.mem_top)

private theorem mul_X_mem_J_of_Ψ_eq_zero {c n m : ℕ} (hn : 1 ≤ n) (hm : n + 1 ≤ m)
    (r : ↥(idealOfVars (Fin 3) k ^ c)) (hr : Ψ k c n m r = 0) :
    r.1 * X 0 ∈ J k (n + 1) := by
  rw [Ψ, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
    Submodule.mem_comap] at hr
  obtain ⟨p, hp, hpv⟩ := exists_lift_of_mem_smul k (by omega) hr
  have hv : πq k m (r.1 * X 0) = πq k m p := by
    rw [← hpv]
    change πq k m (r.1 * X 0) = r.1 • πq k m (X 0)
    rw [← map_smul, smul_eq_mul]
  rw [← sub_eq_zero, ← map_sub, πq_eq_zero_iff] at hv
  have := add_mem (J_mono k hm hv) (Ideal.mem_sup_right hp :
    p ∈ J k (n + 1))
  rwa [sub_add_cancel] at this

/-- `h ↦ x h`, from `k[x, y, z]` to `Pₙ / Pₙ[I ^ c]`. -/
private def Λ (c n : ℕ) : MvPolynomial (Fin 3) k →ₗ[MvPolynomial (Fin 3) k] Tgt k c n :=
  (Submodule.mkQ _) ∘ₗ
    (LinearMap.codRestrict (Pq k n)
      ((πq k n) ∘ₗ LinearMap.mulLeft (MvPolynomial (Fin 3) k) (X 0))
      fun h => (πq_mem_Pq_iff k n _).mpr (X_mul_mem_J k n h))

private theorem mem_lowSet {K : ℕ} {j : ℕ × ℕ} :
    j ∈ (Finset.range K).biUnion Finset.antidiagonal ↔ j.1 + j.2 < K := by
  simp [Finset.mem_biUnion, Finset.mem_antidiagonal]

private theorem mem_bandSet {c K : ℕ} {j : ℕ × ℕ} :
    j ∈ (Finset.Ico c K).biUnion Finset.antidiagonal ↔ c ≤ j.1 + j.2 ∧ j.1 + j.2 < K := by
  simp [Finset.mem_biUnion, Finset.mem_antidiagonal]

private theorem coeff_sum_monomial {ι : Type*} (T : Finset ι) (φ : ι → Fin 3 →₀ ℕ)
    (hφ : Set.InjOn φ T) (g : ι → k) {j : ι} (hj : j ∈ T) :
    (∑ i ∈ T, monomial (φ i) (g i)).coeff (φ j) = g j := by
  rw [coeff_sum, Finset.sum_eq_single j]
  · simp
  · intro i hi hij
    rw [coeff_monomial, ite_eq_right_iff.mpr fun h => absurd (hφ hi hj h) hij]
  · intro h
    exact absurd hj h

/-- `Pₙ / Pₙ[I ^ c]` is spanned by the classes of `x y ^ a z ^ b` with `a + b < n - 1 - c`. -/
private theorem mem_span_Λ {c n : ℕ} (hc : 1 ≤ c) (hcn : c ≤ n) (v : Tgt k c n) :
    v ∈ Submodule.span k (Set.range fun j : ↥((Finset.range (n - 1 - c)).biUnion
      Finset.antidiagonal) => Λ k c n (monomial (ex 0 j.1.1 j.1.2) 1)) := by
  induction v using Submodule.Quotient.induction_on with
  | H w =>
    set T := (Finset.range (n - 1 - c)).biUnion Finset.antidiagonal
    obtain ⟨g, hg⟩ := πq_surjective k n w.1
    have hgP : X 0 * g ∈ J k n := (πq_mem_Pq_iff k n g).mp (hg ▸ w.2)
    set h := ∑ j ∈ T, monomial (ex 0 j.1 j.2) (g.coeff (ex 1 j.1 j.2))
    have hdiff : g - X 0 * h ∈ J k (n - c) := by
      apply mem_J_of_support
      intro s hs
      by_contra hcon
      push Not at hcon
      apply (MvPolynomial.mem_support_iff.mp hs)
      rw [coeff_sub, mul_comm (X 0) h]
      have hs0 : s 0 = 0 ∨ s 0 = 1 := by omega
      rcases hs0 with hs0 | hs0
      · rw [coeff_mul_X', ite_eq_right_iff.mpr fun h => absurd h (by simpa using hs0), sub_zero]
        have := coeff_eq_zero_of_mem_J k (s := s + single 0 1) hgP (by simp [hs0])
          (by simp [degree_single]; omega)
        rwa [mul_comm, coeff_mul_X] at this
      · have e1 : s = ex 1 (s 1) (s 2) := by
          conv_lhs => rw [eq_ex s]
          rw [hs0]
        generalize s 1 = a at e1
        generalize s 2 = b at e1
        subst e1
        have hdeg := degree_ex 1 a b
        have hT : (a, b) ∈ T := mem_lowSet.mpr (by simp only; omega)
        have hsplit : ex 1 a b = ex 0 a b + single 0 1 := by
          ext i; fin_cases i <;> simp [ex]
        rw [show (h * X 0 : MvPolynomial (Fin 3) k).coeff (ex 1 a b) = h.coeff (ex 0 a b) by
          rw [hsplit, coeff_mul_X]]
        have := coeff_sum_monomial k T (fun j => ex 0 j.1 j.2)
          (fun i _ j _ hij => by
            obtain ⟨-, h1, h2⟩ := ex_inj hij
            exact Prod.ext h1 h2) (fun j => g.coeff (ex 1 j.1 j.2)) hT
        simp only at this
        rw [this, sub_self]
    have key : Submodule.Quotient.mk w = Λ k c n h := by
      rw [eq_comm]
      apply (Submodule.Quotient.eq _).mpr
      rw [Submodule.mem_torsionBySet_iff]
      rintro ⟨a, ha⟩
      apply Subtype.ext
      change a • (πq k n (X 0 * h) - w.1) = 0
      rw [← hg, ← map_sub, ← map_smul, smul_eq_mul, πq_eq_zero_iff]
      have := mul_mem_J k ha (neg_mem hdiff)
      rwa [Nat.add_sub_cancel' hcn, neg_sub] at this
    rw [key]
    have hh : h = ∑ j ∈ T, g.coeff (ex 1 j.1 j.2) • monomial (ex 0 j.1 j.2) (1 : k) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_monomial, smul_eq_mul, mul_one]
    refine (Submodule.mem_comap (f := (Λ k c n).restrictScalars k)).mp ?_
    rw [hh]
    exact Submodule.sum_mem _ fun j hj =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩)



/-- The polynomial `y ^ a z ^ b`, as an element of `I ^ cs` when `cs ≤ c ≤ a + b`. -/
private def qElt {cs c : ℕ} (hcs : cs ≤ c) {K : ℕ}
    (j : ↥((Finset.Ico c K).biUnion Finset.antidiagonal)) :
    ↥(idealOfVars (Fin 3) k ^ cs) :=
  ⟨monomial (ex 0 j.1.1 j.1.2) 1, monomial_mem_pow k (by
    rw [degree_ex]; have := (mem_bandSet.mp j.2).1; omega)⟩

private theorem zc_mul (a b c : ℕ) :
    (monomial (ex 0 0 c) 1 : MvPolynomial (Fin 3) k) * monomial (ex 0 a b) 1 =
      monomial (ex 0 a (b + c)) 1 := by
  rw [monomial_mul_monomial, one_mul, ex_add, zero_add, zero_add, add_comm c b]

/-- The classes of `z ^ c y ^ a z ^ b x` with `c ≤ a + b < n - c` are linearly independent in
`I ^ cs Pₘ / I ^ n Pₘ`, over `k` acting through constants. -/
private theorem eq_zero_of_Ψ_sum_eq_zero {cs c n m : ℕ} (hcs : cs ≤ c) (hn : 1 ≤ n)
    (hm : n + 1 ≤ m) (g : ↥((Finset.Ico c (n - c)).biUnion Finset.antidiagonal) → k)
    (hg : Ψ k cs n m ((monomial (ex 0 0 c) 1 : MvPolynomial (Fin 3) k) •
      ∑ i, (C (g i) : MvPolynomial (Fin 3) k) • qElt k hcs i) = 0)
    (j : ↥((Finset.Ico c (n - c)).biUnion Finset.antidiagonal)) : g j = 0 := by
  classical
  have hJ := mul_X_mem_J_of_Ψ_eq_zero k hn hm _ hg
  have hr1 : (((monomial (ex 0 0 c) 1 : MvPolynomial (Fin 3) k) •
      ∑ i, (C (g i) : MvPolynomial (Fin 3) k) • qElt k hcs i :
        ↥(idealOfVars (Fin 3) k ^ cs)) : MvPolynomial (Fin 3) k) =
      ∑ i, monomial (ex 0 i.1.1 (i.1.2 + c)) (g i) := by
    rw [Submodule.coe_smul, Submodule.coe_sum, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Submodule.coe_smul, smul_eq_mul]
    change monomial (ex 0 0 c) 1 * (C (g i) * monomial (ex 0 i.1.1 i.1.2) 1) = _
    rw [mul_left_comm, zc_mul, C_mul_monomial, mul_one]
  obtain ⟨⟨a, b⟩, hj⟩ := j
  have hband := mem_bandSet.mp hj
  simp only at hband
  have hco := coeff_eq_zero_of_mem_J k hJ (s := ex 1 a (b + c)) (by simp [ex_apply_zero])
    (by rw [degree_ex]; omega)
  have hsplit : ex 1 a (b + c) = ex 0 a (b + c) + single 0 1 := by
    ext i; fin_cases i <;> simp [ex]
  rw [hsplit, coeff_mul_X, hr1] at hco
  have := coeff_sum_monomial k Finset.univ (fun i : ↥((Finset.Ico c (n - c)).biUnion
      Finset.antidiagonal) => ex 0 i.1.1 (i.1.2 + c))
    (fun i _ i' _ hii => by
      obtain ⟨-, h1, h2⟩ := ex_inj hii
      exact Subtype.ext (Prod.ext h1 (by omega)))
    g (Finset.mem_univ ⟨(a, b), hj⟩)
  simp only at this
  rwa [this] at hco

/-- No map `I ^ cs Pₘ / I ^ n Pₘ → Pₙ / Pₙ[I ^ c]` has kernel killed by `I ^ c`, once
`1 ≤ c`, `cs ≤ c`, `n ≥ c² + 2c + 2` and `m > n`. -/
private theorem core {cs c n m : ℕ} (hcs : cs ≤ c) (hc : 1 ≤ c) (hn : c * c + 2 * c + 2 ≤ n)
    (hm : n + 1 ≤ m) (f : Src k cs n m →ₗ[MvPolynomial (Fin 3) k] Tgt k c n)
    (hf : ∀ z, f z = 0 → ∀ a ∈ idealOfVars (Fin 3) k ^ c, a • z = 0) : False := by
  classical
  have hn1 : 1 ≤ n := by have := hn; generalize c * c = q at this; omega
  have hcn : c ≤ n := by have := hn; generalize c * c = q at this; omega
  let Q := (Finset.Ico c (n - c)).biUnion Finset.antidiagonal
  let P := (Finset.range (n - 1 - c)).biUnion Finset.antidiagonal
  let t : ↥P → Tgt k c n := fun j => Λ k c n (monomial (ex 0 j.1.1 j.1.2) 1)
  let Θ := f ∘ₗ Ψ k cs n m
  have hli : LinearIndependent k fun j : ↥Q => Θ (qElt k hcs j) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have h1 : Θ (∑ i, (C (g i) : MvPolynomial (Fin 3) k) • qElt k hcs i) = 0 := by
      rw [← hg, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul]
      exact algebraMap_smul (MvPolynomial (Fin 3) k) (g i) _
    have h2 := hf _ h1 (monomial (ex 0 0 c) 1) (monomial_mem_pow k (by simp [degree_ex]))
    rw [← map_smul] at h2
    exact eq_zero_of_Ψ_sum_eq_zero k hcs hn1 hm g h2 j
  have hspan : Set.range (fun j : ↥Q => Θ (qElt k hcs j)) ≤
      Submodule.span k (Set.range t) := fun v _ => mem_span_Λ k hc hcn v
  have hcard := linearIndependent_le_span' _ hli (Set.range t) hspan
  rw [Cardinal.mk_fintype, Fintype.card_coe] at hcard
  have h3 : Fintype.card (Set.range t) ≤ P.card :=
    (Fintype.card_range_le t).trans (Fintype.card_coe P).le
  have h4 : P.card < Q.card := by
    rw [card_biUnion_antidiagonal, card_biUnion_antidiagonal]
    exact sum_lt_sum_Ico hn
  norm_cast at hcard
  omega

/-! ### `Ext⁰` over `Aₙ` is the `x`-torsion of `Nₙ` -/

private abbrev Mmod := MvPolynomial (Fin 3) k ⧸ Ideal.span {(X 0 : MvPolynomial (Fin 3) k)}

/-- `Ext⁰_{Aₙ}(Mₙ, Nₙ) ≅ Pₙ` as `A`-modules. -/
private def underlyingEquiv (n : ℕ+) :
    ↑(underlying (extOfAdicQuotientsSystem (idealOfVars (Fin 3) k) (Mmod k) (Nmod k) 0) n)
      ≃ₗ[MvPolynomial (Fin 3) k] Pq k n :=
  ExtZero.underlyingEquiv (idealOfVars (Fin 3) k) (X 0) (Nmod k) n

end

/-- **Stacks 0EGZ is false as stated.** Remark 0EGZ asserts a single `c ≥ 0` such that for
`m ≫ n ≫ 0` there are maps `I ^ c Eₘ / I ^ n Eₘ → Eₙ / Eₙ[I ^ c]`, with
`Eₙ = Ext^i_{Aₙ}(Mₙ, Nₙ)`, whose kernel and cokernel are annihilated by `I ^ c`. For
`A = k[x, y, z]`, `I = (x, y, z)`, `M = A / (x)`, `N = A / (x²)` and `i = 0` no such `c` exists,
whatever maps are allowed: even the kernel condition alone fails. The corrected statement, with
the kernel and cokernel killed by a possibly larger power, is
`Stacks.AdicSystem.ExtComparison.exists_eventually_extOfAdicQuotients_comparison`. -/
@[stacks 0EGZ "counterexample: for A = k[x, y, z], I = (x, y, z), M = A/(x), N = A/(x²), \
i = 0, no c and no maps I^c E_m / I^n E_m → E_n / E_n[I^c] have kernel killed by I^c"]
public theorem not_exists_extOfAdicQuotients_comparison_one_exponent (k : Type u) [Field k] :
    let A := MvPolynomial (Fin 3) k
    let I : Ideal A := idealOfVars (Fin 3) k
    let M := A ⧸ Ideal.span {(X 0 : A)}
    let N := A ⧸ Ideal.span {(X 0 : A) ^ 2}
    let F := extOfAdicQuotientsSystem I M N 0
    ¬ ∃ c : ℕ, ∀ᶠ n : ℕ+ in atTop, ∀ᶠ m : ℕ+ in atTop, n ≤ m →
      ∃ f : (powerPart F m c ⧸ (powerPart F m (n : ℕ)).comap (powerPart F m c).subtype) →ₗ[A]
          underlying F n ⧸ torsionPart F n c,
        Module.IsTorsionBySet A (LinearMap.ker f) (↑(I ^ c) : Set A) ∧
        Module.IsTorsionBySet A
          ((underlying F n ⧸ torsionPart F n c) ⧸ LinearMap.range f) (↑(I ^ c) : Set A) := by
  intro A I M N F
  rintro ⟨c, hc⟩
  obtain ⟨n0, hn0⟩ := eventually_atTop.mp hc
  let n : ℕ+ := max n0 ⟨(c + 1) * (c + 1) + 2 * (c + 1) + 2, by positivity⟩
  have hn : (c + 1) * (c + 1) + 2 * (c + 1) + 2 ≤ (n : ℕ) := by
    have := le_max_right n0 ⟨(c + 1) * (c + 1) + 2 * (c + 1) + 2, by positivity⟩
    exact_mod_cast this
  obtain ⟨m0, hm0⟩ := eventually_atTop.mp (hn0 n (le_max_left _ _))
  let m : ℕ+ := max m0 (n + 1)
  have hm : (n : ℕ) + 1 ≤ m := by
    have := le_max_right m0 (n + 1)
    exact_mod_cast this
  obtain ⟨f, hker, -⟩ := hm0 m (le_max_left _ _) (by
    have := le_max_right m0 (n + 1)
    exact le_of_lt (lt_of_lt_of_le (PNat.lt_add_right n 1) this))
  have hker' : ∀ z, f z = 0 → ∀ a ∈ I ^ c, a • z = 0 := fun z hz a ha =>
    congrArg Subtype.val (hker (x := ⟨z, hz⟩) (a := ⟨a, ha⟩))
  rcases Nat.eq_zero_or_pos c with rfl | hc1
  · let g := HomRepresentative.quotientTransition F n 0 ∘ₗ f
    have hg : ∀ z, g z = 0 → ∀ a ∈ I ^ 1, a • z = 0 := by
      intro z hz a ha
      change HomRepresentative.quotientTransition F n 0 (f z) = 0 at hz
      have hfa : f (a • z) = 0 := by
        rw [map_smul]
        obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (f z)
        rw [← hy] at hz ⊢
        have hy1 : y ∈ torsionPart F n (0 + 1) := (Submodule.Quotient.mk_eq_zero _).mp hz
        rw [← Submodule.Quotient.mk_smul, (Submodule.mem_torsionBySet_iff _ _).mp hy1 ⟨a, ha⟩,
          Submodule.Quotient.mk_zero]
      have := hker' _ hfa 1 (by rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top)
      rwa [one_smul] at this
    obtain ⟨g', hg'⟩ := transport I (underlyingEquiv k m) (underlyingEquiv k n) 0 n 1 g hg
    exact core k (cs := 0) (c := 1) (Nat.zero_le _) le_rfl (by simpa using hn) (by simpa using hm)
      g' hg'
  · obtain ⟨f', hf'⟩ := transport I (underlyingEquiv k m) (underlyingEquiv k n) c n c f hker'
    refine core k le_rfl hc1 ?_ hm f' hf'
    nlinarith

end Stacks.AdicSystem.ExtComparisonCounterexample

end

end
