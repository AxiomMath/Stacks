module

public import StacksFrontier.RingTheory.Etale.QuotientSingletonDifferential
public import StacksFrontier.RingTheory.Etale.SeparatingDivisorAux
public import StacksFrontier.RingTheory.Smooth.LocallyStandardSmoothKaehler
public import StacksFrontier.RingTheory.NoetherNormalization.SeparatingCurve
public import StacksFrontier.RingTheory.Polynomial.MonicSeparableCoprime
public import Mathlib.RingTheory.RingHom.LocallyStandardSmooth
public import Mathlib.RingTheory.Kaehler.TensorProduct
public import Mathlib.RingTheory.Localization.Algebra

/-!
# An étale divisor of a family of smooth curves

Let `A` be a noetherian domain of characteristic `p` and `B` an `A`-algebra of finite type,
locally standard smooth of relative dimension one, whose generic fibre `B_K` (`K = Frac A`) has
dimension one. Then there are `a ≠ 0` in `A`, `t ∈ B` and a monic `h ∈ A[X]` of positive degree
such that

* every `x ∈ B` becomes integral over `A[X]` (through `X ↦ t`) after multiplication by a power
  of `a`: over `D(a)` the coordinate `t` is finite;
* over `D(a)` the divisor `V(h(t))` is finite étale: `B_a ⧸ (h(t))` is finite and étale over
  `A_a`.

The proof: the generic fibre has a separating finite coordinate `t₁`
(`Polynomial.exists_finite_aeval_forall_minimalPrimes_ne_zero`), which we scale into `B`. The
module `Ω[B_K⁄K] ⧸ (dt)` vanishes at the minimal primes of `B_K`, so it is killed by `b(t)` for a
nonzero `b ∈ K[X]` (`Polynomial.exists_ne_zero_aeval_smul_eq_zero`); a monic separable `h` coprime
to `b` (`Polynomial.exists_monic_separable_isCoprime_map`) then has `Ω[B_K⁄K] = ⟨dt⟩ + h(t) Ω`,
which descends to `B` up to a denominator. Over `D(a)`, `dh(t) = h'(t) dt` with `h'(t)` a unit
modulo `h(t)` (`h` separable), so `1 ⊗ dh(t)` generates `B_a ⧸ (h(t)) ⊗ Ω`, and the quotient is
étale (`Algebra.etale_quotient_span_singleton_of_span_D`); it is finite since `t` is integral
over `A_a` modulo `h(t)`.

This is the divisor, finite étale over the base and meeting every component of every geometric
fibre (`t` is finite on each fibre), along which the Gysin map of `R² g_!` is taken in the
reduction of the weight bound of Weil II ([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)).

## Main results

* `Algebra.smooth_of_locally_isStandardSmoothOfRelativeDimension`.
* `Polynomial.exists_etale_divisor_of_locally_isStandardSmooth`.
-/

public section

open TensorProduct Polynomial Pointwise

universe u

/-- **Locally standard smooth algebras are smooth.** -/
theorem Algebra.smooth_of_locally_isStandardSmoothOfRelativeDimension {R S : Type u} [CommRing R]
    [CommRing S] [Algebra R S] {n : ℕ}
    (h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) (algebraMap R S)) :
    Algebra.Smooth R S := by
  rw [← RingHom.smooth_algebraMap, RingHom.smooth_iff_locally_isStandardSmooth]
  exact RingHom.locally_of_locally
    (fun {_ _ _ _ f} hf =>
      RingHom.IsStandardSmoothOfRelativeDimension.isStandardSmooth (n := n) f hf) h

namespace Polynomial

/-- Localizing `A` and `B` at `M` preserves being locally standard smooth of relative dimension
one, and so gives a smooth algebra. -/
private theorem locally_isStandardSmoothOfRelativeDimension_one_of_isLocalization
    {A B A' B' : Type u} [CommRing A] [CommRing B] [CommRing A'] [CommRing B'] [Algebra A B]
    [Algebra A A'] [Algebra B B'] [Algebra A' B'] [Algebra A B'] [IsScalarTower A A' B']
    [IsScalarTower A B B'] (M : Submonoid A) [IsLocalization M A']
    [IsLocalization (Algebra.algebraMapSubmonoid B M) B']
    (hsm : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1) (algebraMap A B)) :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1) (algebraMap A' B') ∧
      Algebra.Smooth A' B' := by
  have : Algebra.IsPushout A B A' B' := Algebra.isPushout_of_isLocalization M A' B B'
  have h := RingHom.locally_isStableUnderBaseChange
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso
    (RingHom.isStandardSmoothOfRelativeDimension_isStableUnderBaseChange 1) A B A' B' hsm
  exact ⟨h, Algebra.smooth_of_locally_isStandardSmoothOfRelativeDimension h⟩

/-- Localizing `A` and `B` at `M` localizes `Ω[B⁄A]` at `M`. -/
private theorem isLocalizedModule_kaehlerDifferential_map
    {A B A' B' : Type u} [CommRing A] [CommRing B] [CommRing A'] [CommRing B'] [Algebra A B]
    [Algebra A A'] [Algebra B B'] [Algebra A' B'] [Algebra A B'] [IsScalarTower A A' B']
    [IsScalarTower A B B'] (M : Submonoid A) [IsLocalization M A']
    [IsLocalization (Algebra.algebraMapSubmonoid B M) B'] :
    IsLocalizedModule M ((KaehlerDifferential.map A A' B B').restrictScalars A) := by
  have : IsLocalizedModule M (IsScalarTower.toAlgHom A B B').toLinearMap :=
    isLocalizedModule_iff_isLocalization.2 inferInstance
  exact KaehlerDifferential.isLocalizedModule_of_isLocalizedModule A A' B B' M

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

/-- **An étale divisor of a family of smooth curves**: for `A` a noetherian domain of
characteristic `p` and `B` of finite type over `A`, locally standard smooth of relative dimension
one with one-dimensional generic fibre, there are `a ≠ 0`, `t ∈ B` and `h ∈ A[X]` monic of
positive degree such that every element of `B` times a power of `a` is integral over `A[X]`
through `X ↦ t`, and `B_a ⧸ (h(t))` is finite and étale over `A_a`. -/
theorem exists_etale_divisor_of_locally_isStandardSmooth [IsDomain A] [IsNoetherianRing A]
    (p : ℕ) [Fact p.Prime] [CharP A p] [Algebra.FiniteType A B]
    (hsm : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1) (algebraMap A B))
    (hdim : ringKrullDim (Localization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A))) = 1) :
    ∃ (a : A) (t : B) (h : A[X]), a ≠ 0 ∧ h.Monic ∧ 0 < h.natDegree ∧
      (∀ x : B, ∃ n : ℕ, (aeval t : A[X] →ₐ[A] B).toRingHom.IsIntegralElem (a ^ n • x)) ∧
      ∀ (A' B' : Type u) [CommRing A'] [CommRing B'] [Algebra A A'] [Algebra B B']
        [Algebra A' B'] [Algebra A B'] [IsScalarTower A A' B'] [IsScalarTower A B B']
        [IsLocalization.Away a A'] [IsLocalization (Algebra.algebraMapSubmonoid B
          (Submonoid.powers a)) B'],
        Algebra.Etale A' (B' ⧸ Ideal.span {algebraMap B B' (aeval t h)}) ∧
        Module.Finite A' (B' ⧸ Ideal.span {algebraMap B B' (aeval t h)}) := by
  classical
  -- the generic fibre `B_K`
  let K := FractionRing A
  let BK := Localization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A))
  obtain ⟨hsmK, _⟩ := locally_isStandardSmoothOfRelativeDimension_one_of_isLocalization
    (A' := K) (B' := BK) (nonZeroDivisors A) hsm
  have : Nontrivial BK := by
    by_contra hBK
    rw [not_nontrivial_iff_subsingleton] at hBK
    rw [ringKrullDim_eq_bot_of_subsingleton] at hdim
    exact absurd hdim (by decide)
  have : CharP K p := charP_of_injective_algebraMap (IsFractionRing.injective A K) p
  obtain ⟨t₁, hfin₁, hdt₁⟩ := exists_finite_aeval_forall_minimalPrimes_ne_zero K BK p hdim
    (fun P _ => Algebra.nontrivial_residueField_tensor_kaehlerDifferential_of_locally (n := 0)
      hsmK P.asIdeal)
  -- clear the denominator of `t₁`
  obtain ⟨⟨t, m⟩, ht⟩ := IsLocalization.surj (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) t₁
  obtain ⟨s, hs, hsm'⟩ := m.2
  set σ : K := algebraMap A K s with hσdef
  have hσ : σ ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
  set t' : BK := algebraMap B BK t with ht'def
  have ht' : t' = σ • t₁ := by
    rw [Algebra.smul_def, ← IsScalarTower.algebraMap_apply A K BK,
      IsScalarTower.algebraMap_apply A B BK, hsm', mul_comm]
    exact ht.symm
  -- `t'` is finite over `K`
  have hfin : (aeval t' : K[X] →ₐ[K] BK).Finite := by
    have hcomp : (aeval t' : K[X] →ₐ[K] BK) = (aeval t₁).comp (aeval (C σ * X)) := by
      apply Polynomial.algHom_ext
      rw [aeval_X, AlgHom.comp_apply, aeval_X, map_mul, aeval_C, aeval_X, ht', Algebra.smul_def]
    have hsurj : Function.Surjective (aeval (C σ * X) : K[X] →ₐ[K] K[X]) := by
      intro q
      refine ⟨aeval (C σ⁻¹ * X) q, ?_⟩
      rw [← AlgHom.comp_apply]
      have : (aeval (C σ * X) : K[X] →ₐ[K] K[X]).comp (aeval (C σ⁻¹ * X)) =
          AlgHom.id K K[X] := by
        apply Polynomial.algHom_ext
        rw [AlgHom.comp_apply, aeval_X, map_mul, aeval_C, aeval_X, Polynomial.algebraMap_eq,
          ← mul_assoc, ← C_mul, inv_mul_cancel₀ hσ, C_1, one_mul, AlgHom.id_apply]
      rw [this]
      rfl
    rw [hcomp]
    exact hfin₁.comp (AlgHom.Finite.of_surjective _ hsurj)
  -- `dt'` does not vanish at the minimal primes
  have hdt : ∀ P : PrimeSpectrum BK, P.asIdeal ∈ minimalPrimes BK →
      (1 : P.asIdeal.ResidueField) ⊗ₜ[BK] KaehlerDifferential.D K BK t' ≠ 0 := by
    intro P hP
    have h1 := hdt₁ P hP
    rw [ht', Derivation.map_smul, ← algebraMap_smul BK σ, TensorProduct.tmul_smul,
      ← algebraMap_smul P.asIdeal.ResidueField]
    refine smul_ne_zero ?_ h1
    exact (((Ne.isUnit hσ).map (algebraMap K BK)).map _).ne_zero
  -- `Ω[B_K⁄K] ⧸ ⟨dt'⟩` is killed by a nonzero `b(t')`
  obtain ⟨b, hb0, hb⟩ := exists_ne_zero_aeval_smul_eq_zero
    (N := Ω[BK⁄K] ⧸ Submodule.span BK {KaehlerDifferential.D K BK t'}) t' hfin
    (fun P _ hP => Submodule.subsingleton_residueField_tensor_quotient_span_singleton P _
      (Algebra.finrank_residueField_tensor_kaehlerDifferential_of_locally hsmK P)
      (hdt ⟨P, inferInstance⟩ hP))
  -- the polynomial `h`
  obtain ⟨h, hmon, hdeg, hsep, hcop⟩ := exists_monic_separable_isCoprime_map A K hb0
  set f : B := aeval t h with hfdef
  have hf' : aeval t' (h.map (algebraMap A K)) = algebraMap B BK f := by
    rw [aeval_map_algebraMap, ht'def, aeval_algebraMap_apply]
  -- `Ω[B_K⁄K] = ⟨dt'⟩ + f Ω[B_K⁄K]`
  have hcovK : ∀ ω : Ω[BK⁄K], ω ∈ Submodule.span BK {KaehlerDifferential.D K BK t'} ⊔
      algebraMap B BK f • (⊤ : Submodule BK Ω[BK⁄K]) := by
    intro ω
    obtain ⟨u, v, huv⟩ := hcop
    have h1 : aeval t' v * aeval t' b + aeval t' u * algebraMap B BK f = 1 := by
      rw [← hf', ← map_mul, ← map_mul, ← map_add, add_comm, huv, map_one]
    have hbω : aeval t' b • ω ∈ Submodule.span BK {KaehlerDifferential.D K BK t'} := by
      have := hb (Submodule.Quotient.mk ω)
      rwa [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at this
    rw [← one_smul BK ω, ← h1, add_smul]
    refine Submodule.add_mem_sup ?_ ?_
    · rw [mul_smul]
      exact Submodule.smul_mem _ _ hbω
    · rw [mul_comm, mul_smul]
      exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top
  -- descend to `B`
  have : IsLocalizedModule (nonZeroDivisors A)
      ((KaehlerDifferential.map A K B BK).restrictScalars A) :=
    isLocalizedModule_kaehlerDifferential_map (A' := K) (B' := BK) (nonZeroDivisors A)
  set L : Submodule B Ω[B⁄A] := Submodule.span B {KaehlerDifferential.D A B t} ⊔
    f • (⊤ : Submodule B Ω[B⁄A]) with hLdef
  have hloc : ∀ ω : Ω[B⁄A], ∃ s ∈ nonZeroDivisors A, s • ω ∈ L := fun ω =>
    Submodule.exists_smul_mem_sup_of_isLocalizedModule (nonZeroDivisors A)
      (KaehlerDifferential.map A K B BK) _ f ω (by
        rw [KaehlerDifferential.map_D]
        exact hcovK _)
  obtain ⟨n, gens, hgens⟩ := Module.Finite.exists_fin (R := B) (M := Ω[B⁄A])
  choose s₁ hs₁ hs₁L using fun i => hloc (gens i)
  set a₁ : A := ∏ i, s₁ i with ha₁def
  have ha₁ : a₁ ∈ nonZeroDivisors A := Submonoid.prod_mem _ fun i _ => hs₁ i
  have hL : ∀ ω : Ω[B⁄A], a₁ • ω ∈ L := by
    intro ω
    have hω : ω ∈ Submodule.span B (Set.range gens) := hgens ▸ Submodule.mem_top
    induction hω using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      rw [ha₁def, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i), mul_comm, mul_smul]
      exact Submodule.smul_of_tower_mem _ _ (hs₁L i)
    | zero => simp
    | add x y _ _ hx hy =>
      rw [smul_add]
      exact L.add_mem hx hy
    | smul c x _ hx =>
      rw [smul_comm]
      exact L.smul_mem c hx
  -- integrality over `A[X]` up to a denominator
  have hintx : ∀ x : B, ∃ c ∈ nonZeroDivisors A,
      (aeval t : A[X] →ₐ[A] B).toRingHom.IsIntegralElem (c • x) := by
    intro x
    let : Algebra A[X] K[X] := Polynomial.algebra A K
    have : IsLocalization ((nonZeroDivisors A).map C) K[X] :=
      Polynomial.isLocalization (nonZeroDivisors A) K
    let : Algebra K[X] BK := (aeval t' : K[X] →ₐ[K] BK).toRingHom.toAlgebra
    let : Algebra A[X] BK := ((algebraMap B BK).comp (aeval t : A[X] →ₐ[A] B).toRingHom).toAlgebra
    have : IsScalarTower A[X] K[X] BK := IsScalarTower.of_algebraMap_eq fun q => by
      change algebraMap B BK (aeval t q) = aeval t' (q.map (algebraMap A K))
      rw [aeval_map_algebraMap, ht'def, aeval_algebraMap_apply]
    obtain ⟨⟨_, c, hc, rfl⟩, hcx⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
      ((nonZeroDivisors A).map C) (algebraMap B BK x) (hfin.to_isIntegral _)
    have hcx' : ((algebraMap B BK).comp (aeval t : A[X] →ₐ[A] B).toRingHom).IsIntegralElem
        (algebraMap B BK (c • x)) := by
      have : (⟨C c, c, hc, rfl⟩ : (nonZeroDivisors A).map C) • algebraMap B BK x =
          algebraMap B BK (c • x) := by
        rw [Submonoid.smul_def, Algebra.smul_def, Algebra.smul_def, map_mul]
        congr 1
        change algebraMap B BK (aeval t (C c)) = _
        rw [aeval_C, ← IsScalarTower.algebraMap_apply]
      rw [← this]
      exact hcx
    obtain ⟨u, hu, hux⟩ := RingHom.IsIntegralElem.exists_smul_of_isLocalization
      (nonZeroDivisors A) t (c • x) hcx'
    exact ⟨u * c, Submonoid.mul_mem _ hu hc, by rw [mul_smul]; exact hux⟩
  let : Algebra A[X] B := (aeval t : A[X] →ₐ[A] B).toRingHom.toAlgebra
  have hintA : ∀ r : A, IsIntegral A[X] (algebraMap A B r) := fun r => by
    have : algebraMap A B r = algebraMap A[X] B (C r) := by
      change _ = aeval t (C r)
      rw [aeval_C]
    rw [this]
    exact isIntegral_algebraMap
  obtain ⟨gB, hgB⟩ := Algebra.FiniteType.out (R := A) (A := B)
  choose c₂ hc₂ hc₂x using fun x : gB => hintx x
  set a₂ : A := ∏ x : gB, c₂ x with ha₂def
  have ha₂ : a₂ ∈ nonZeroDivisors A := Submonoid.prod_mem _ fun i _ => hc₂ i
  have hsmul_int : ∀ (r : A) {y : B}, IsIntegral A[X] y → IsIntegral A[X] (r • y) :=
    fun r {y} hy => by rw [Algebra.smul_def]; exact (hintA r).mul hy
  have hint2 : ∀ x : B, ∃ k : ℕ, IsIntegral A[X] (a₂ ^ k • x) := by
    intro x
    have hx : x ∈ Algebra.adjoin A (gB : Set B) := hgB ▸ Algebra.mem_top
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      refine ⟨1, ?_⟩
      rw [pow_one, ha₂def, ← Finset.mul_prod_erase _ _ (Finset.mem_univ ⟨x, hx⟩), mul_comm,
        mul_smul]
      exact hsmul_int _ (hc₂x ⟨x, hx⟩)
    | algebraMap r =>
      exact ⟨0, by rw [pow_zero, one_smul]; exact hintA r⟩
    | add x y _ _ hx hy =>
      obtain ⟨k, hk⟩ := hx
      obtain ⟨l, hl⟩ := hy
      refine ⟨k + l, ?_⟩
      have e : a₂ ^ (k + l) • (x + y) = a₂ ^ l • (a₂ ^ k • x) + a₂ ^ k • (a₂ ^ l • y) := by
        rw [smul_add, smul_smul, smul_smul, ← pow_add, ← pow_add, add_comm l k]
      rw [e]
      exact (hsmul_int _ hk).add (hsmul_int _ hl)
    | mul x y _ _ hx hy =>
      obtain ⟨k, hk⟩ := hx
      obtain ⟨l, hl⟩ := hy
      refine ⟨k + l, ?_⟩
      rw [pow_add, ← smul_mul_smul_comm]
      exact hk.mul hl
  -- the choice of `a`
  have ha₁₂ : a₁ * a₂ ≠ 0 :=
    mul_ne_zero (nonZeroDivisors.ne_zero ha₁) (nonZeroDivisors.ne_zero ha₂)
  have hint3 : ∀ x : B, ∃ k : ℕ, IsIntegral A[X] ((a₁ * a₂) ^ k • x) := by
    intro x
    obtain ⟨k, hk⟩ := hint2 x
    exact ⟨k, by rw [mul_pow, mul_smul]; exact hsmul_int _ hk⟩
  refine ⟨a₁ * a₂, t, h, ha₁₂, hmon, hdeg, hint3, ?_⟩
  intro A' B' _ _ _ _ _ _ _ _ _ _
  set a := a₁ * a₂ with hadef
  obtain ⟨hsm', _⟩ := locally_isStandardSmoothOfRelativeDimension_one_of_isLocalization
    (A' := A') (B' := B') (Submonoid.powers a) hsm
  set t'' : B' := algebraMap B B' t with ht''def
  set f'' : B' := algebraMap B B' f with hf''def
  have hf''t : f'' = aeval t'' (h.map (algebraMap A A')) := by
    rw [aeval_map_algebraMap, ht''def, aeval_algebraMap_apply]
  have hua : ∀ k : ℕ, IsUnit (algebraMap A B' (a ^ k)) := fun k => by
    rw [IsScalarTower.algebraMap_apply A A' B', map_pow]
    exact ((IsLocalization.Away.algebraMap_isUnit a).pow k).map (algebraMap A' B')
  -- the differentials of `B'` over `A'` are a localization of those of `B` over `A`
  have : IsLocalizedModule (Submonoid.powers a)
      ((KaehlerDifferential.map A A' B B').restrictScalars A) :=
    isLocalizedModule_kaehlerDifferential_map (A' := A') (B' := B') (Submonoid.powers a)
  set L' : Submodule B' Ω[B'⁄A'] := Submodule.span B' {KaehlerDifferential.D A' B' t''} ⊔
    f'' • (⊤ : Submodule B' Ω[B'⁄A']) with hL'def
  have hmapL : ∀ y ∈ L, KaehlerDifferential.map A A' B B' y ∈ L' := by
    intro y hy
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.1 hy
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy₁
    obtain ⟨η, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hy₂
    rw [map_add, map_smul, map_smul, KaehlerDifferential.map_D]
    refine Submodule.add_mem_sup ?_ ?_
    · exact Submodule.smul_of_tower_mem _ c (Submodule.mem_span_singleton_self _)
    · rw [← algebraMap_smul B' f]
      exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top
  have hcov' : ∀ ω' : Ω[B'⁄A'], ω' ∈ L' := by
    intro ω'
    obtain ⟨⟨ω, ⟨_, k, rfl⟩⟩, hω⟩ := IsLocalizedModule.surj (Submonoid.powers a)
      ((KaehlerDifferential.map A A' B B').restrictScalars A) ω'
    have h1 : a • ω ∈ L := by
      rw [hadef, mul_comm, mul_smul]
      exact Submodule.smul_of_tower_mem _ _ (hL ω)
    have h2 : (a ^ (k + 1)) • ω' ∈ L' := by
      rw [pow_succ, mul_comm, mul_smul]
      have : (a ^ k) • ω' = KaehlerDifferential.map A A' B B' ω := hω
      rw [this, ← LinearMap.map_smul_of_tower]
      exact hmapL _ h1
    rw [← algebraMap_smul B' (a ^ (k + 1)) ω'] at h2
    exact (Submodule.smul_mem_iff_of_isUnit L' (hua (k + 1))).1 h2
  -- `1 ⊗ dt''` is a multiple of `1 ⊗ df''` modulo `f''`
  set T' := B' ⧸ Ideal.span {f''} with hT'def
  have hfT : algebraMap B' T' f'' = 0 := by
    rw [Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self _
  have hDf : KaehlerDifferential.D A' B' f'' =
      aeval t'' (derivative (h.map (algebraMap A A'))) • KaehlerDifferential.D A' B' t'' := by
    rw [hf''t, Derivation.map_aeval]
  obtain ⟨α, β, hαβ⟩ := hsep
  have hαβ' : aeval t'' (α.map (algebraMap A A')) * f'' +
      aeval t'' (β.map (algebraMap A A')) * aeval t'' (derivative (h.map (algebraMap A A'))) =
      1 := by
    rw [hf''t, derivative_map, ← map_mul, ← map_mul, ← map_add, ← Polynomial.map_mul,
      ← Polynomial.map_mul, ← Polynomial.map_add, hαβ, Polynomial.map_one, map_one]
  have hC2 : (1 : T') ⊗ₜ[B'] KaehlerDifferential.D A' B' t'' ∈
      Submodule.span T' {(1 : T') ⊗ₜ[B'] KaehlerDifferential.D A' B' f''} := by
    have e : (1 : T') ⊗ₜ[B'] KaehlerDifferential.D A' B' t'' =
        algebraMap B' T' (aeval t'' (β.map (algebraMap A A'))) •
          ((1 : T') ⊗ₜ[B'] KaehlerDifferential.D A' B' f'') := by
      conv_lhs => rw [← one_smul B' (KaehlerDifferential.D A' B' t''), ← hαβ', add_smul,
        TensorProduct.tmul_add, mul_smul, mul_smul, ← hDf, TensorProduct.tmul_smul,
        TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul']
      have hz : f'' • (1 : T') = 0 := by rw [Algebra.smul_def, hfT, zero_mul]
      rw [hz, smul_zero, TensorProduct.zero_tmul, zero_add, TensorProduct.tmul_smul,
        algebraMap_smul]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  -- `1 ⊗ df''` generates `T' ⊗ Ω[B'⁄A']`
  have hspan : Submodule.span T' {(1 : T') ⊗ₜ[B'] KaehlerDifferential.D A' B' f''} = ⊤ := by
    rw [eq_top_iff]
    rintro z -
    induction z using TensorProduct.inductionOn with
    | tmul τ ω' =>
      obtain ⟨y₁, hy₁, y₂, hy₂, hy⟩ := Submodule.mem_sup.1 (hcov' ω')
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy₁
      obtain ⟨η, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hy₂
      rw [← hy, TensorProduct.tmul_add]
      refine add_mem ?_ ?_
      · have : τ ⊗ₜ[B'] (c • KaehlerDifferential.D A' B' t'') =
            (τ * algebraMap B' T' c) • ((1 : T') ⊗ₜ[B'] KaehlerDifferential.D A' B' t'') := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, ← TensorProduct.smul_tmul,
            Algebra.smul_def, mul_comm]
        rw [this]
        exact Submodule.smul_mem _ _ hC2
      · have : τ ⊗ₜ[B'] (f'' • η) = 0 := by
          rw [← TensorProduct.smul_tmul, Algebra.smul_def, hfT, zero_mul,
            TensorProduct.zero_tmul]
        rw [this]
        exact zero_mem _
    | add x y hx hy => exact add_mem hx hy
  have : Algebra.Etale A' T' := Algebra.etale_quotient_span_singleton_of_span_D f'' hspan
    (fun q _ _ => Algebra.nontrivial_residueField_tensor_kaehlerDifferential_of_locally (n := 0)
      hsm' q)
  refine ⟨inferInstance, ?_⟩
  -- finiteness: `T'` is integral over `A'`
  set ψT : B →+* T' := (algebraMap B' T').comp (algebraMap B B') with hψT
  have htbar : IsIntegral A' (algebraMap B' T' t'') := by
    refine ⟨h.map (algebraMap A A'), hmon.map _, ?_⟩
    rw [← aeval_def, aeval_algebraMap_apply, ← hf''t, hfT]
  have hχ : ∀ q : A[X], IsIntegral A' (ψT (aeval t q)) := by
    intro q
    have e : ψT (aeval t q) = aeval (algebraMap B' T' t'') (q.map (algebraMap A A')) := by
      rw [aeval_map_algebraMap, aeval_algebraMap_apply, ht''def, aeval_algebraMap_apply]
      rfl
    rw [e]
    clear e
    induction q using Polynomial.induction_on with
    | C c =>
      rw [Polynomial.map_C, aeval_C]
      exact isIntegral_algebraMap
    | add p q hp hq =>
      rw [Polynomial.map_add, map_add]
      exact hp.add hq
    | monomial n c hn =>
      rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X, map_mul, map_pow, aeval_X,
        pow_succ, ← mul_assoc]
      rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X, map_mul, map_pow,
        aeval_X] at hn
      exact hn.mul htbar
  have hψa : ∀ k : ℕ, ψT (algebraMap A B (a ^ k)) = algebraMap A' T' (algebraMap A A' a ^ k) := by
    intro k
    rw [← map_pow, ← IsScalarTower.algebraMap_apply A A' T', hψT, RingHom.comp_apply,
      ← IsScalarTower.algebraMap_apply A B B', ← IsScalarTower.algebraMap_apply A B' T']
  have hinv : ∀ k : ℕ, algebraMap A' T' (IsLocalization.Away.invSelf a ^ k) *
      algebraMap A' T' (algebraMap A A' a ^ k) = 1 := by
    intro k
    rw [← map_mul, ← mul_pow, mul_comm, IsLocalization.Away.mul_invSelf, one_pow, map_one]
  have hψx : ∀ x : B, IsIntegral A' (ψT x) := by
    intro x
    obtain ⟨k, P, hPm, hP⟩ := hint3 x
    let R₁ := integralClosure A' T'
    let χ : A[X] →+* R₁ := (ψT.comp (aeval t : A[X] →ₐ[A] B).toRingHom).codRestrict
      R₁.toSubsemiring (fun q => hχ q)
    have hz : IsIntegral R₁ (ψT (a ^ k • x)) := by
      refine ⟨P.map χ, hPm.map _, ?_⟩
      rw [eval₂_map]
      have : (algebraMap R₁ T').comp χ = ψT.comp (aeval t : A[X] →ₐ[A] B).toRingHom := rfl
      rw [this, ← hom_eval₂]
      have hP' : eval₂ (aeval t : A[X] →ₐ[A] B).toRingHom (a ^ k • x) P = 0 := hP
      rw [hP', map_zero]
    have hz' := isIntegral_trans (R := A') (A := R₁) _ hz
    have e1 : ψT (a ^ k • x) = algebraMap A' T' (algebraMap A A' a ^ k) * ψT x := by
      rw [Algebra.smul_def, map_mul, hψa]
    have e : ψT x = algebraMap A' T' (IsLocalization.Away.invSelf a ^ k) * ψT (a ^ k • x) := by
      rw [e1, ← mul_assoc, hinv, one_mul]
    rw [e]
    exact isIntegral_algebraMap.mul hz'
  have : Algebra.IsIntegral A' T' := by
    constructor
    intro y
    obtain ⟨y₀, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨⟨x, m⟩, hx⟩ := IsLocalization.surj (Algebra.algebraMapSubmonoid B
      (Submonoid.powers a)) y₀
    obtain ⟨_, ⟨k, rfl⟩, hm⟩ := m.2
    have hx' : algebraMap B' T' y₀ * algebraMap A' T' (algebraMap A A' a ^ k) = ψT x := by
      have := congrArg (algebraMap B' T') hx
      rw [map_mul] at this
      have hm' : algebraMap A B (a ^ k) = (m : B) := hm
      rw [← hψa, hψT, RingHom.comp_apply, RingHom.comp_apply, ← this, hm']
    have e : Ideal.Quotient.mk (Ideal.span {f''}) y₀ =
        algebraMap A' T' (IsLocalization.Away.invSelf a ^ k) * ψT x := by
      rw [← hx', mul_comm (algebraMap B' T' y₀), ← mul_assoc, hinv, one_mul]
      rfl
    rw [e]
    exact isIntegral_algebraMap.mul (hψx x)
  exact Algebra.IsIntegral.finite

end Polynomial
