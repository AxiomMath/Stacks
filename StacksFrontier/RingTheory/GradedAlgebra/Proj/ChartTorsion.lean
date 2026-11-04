module

public import StacksFrontier.RingTheory.GradedAlgebra.Proj.DegreeOneUnitAway
public import StacksFrontier.Algebra.Module.IPowerTorsion

/-!
# Torsion read off the degree-zero localizations at products of consecutive degrees

Let `A` be a graded ring, `φ : M → N` a degree-preserving map of graded `A`-modules, and
`g = cb` with `c ∈ A_{m+1}` and `b ∈ A_m`. In `A[1/g]` the element `u = c²/g` is a unit of degree
one, so every homogeneous fraction of `M[1/g]` is a power of `u` times a degree-zero fraction
(`Stacks.DegreeOneUnitAway.exists_mk_eq_chartUnit_zpow_smul`). Consequently the behaviour of `φ`
after inverting `g` is controlled by its degree-zero part `M₍g₎ → N₍g₎`:

* if `M₍g₎ → N₍g₎` is injective, every element of the kernel of `φ` is killed by a power of `g`;
* if `M₍g₎ → N₍g₎` is surjective, a power of `g` moves every element of `N` into the range of `φ`.

When the elements `g` for which this holds avoid every prime not containing an ideal `𝔞`, the
kernel and the cokernel of `φ` are `𝔞`-power torsion (`isIPowerTorsion_of_forall_pow_smul`).

## Main results

* `Stacks.DegreeOneUnitAway.exists_pow_smul_eq_zero_of_map_eq_zero`: if `φ` is injective on
  degree-zero localizations at `g`, its kernel is `g`-power torsion.
* `Stacks.DegreeOneUnitAway.exists_pow_smul_mem_range`: if `φ` is surjective on degree-zero
  localizations at `g`, a power of `g` moves every element of `N` into the range of `φ`.
* `Stacks.DegreeOneUnitAway.isIPowerTorsion_of_forall_pow_smul`: power torsion for a family of
  elements avoiding every prime not containing `𝔞` is `𝔞`-power torsion.
* `Stacks.DegreeOneUnitAway.exists_liftQ_isIPowerTorsion`: the reduction modulo `Jⁿ⁺¹` of a map
  of quotients has `𝔞`-power torsion kernel and cokernel.
-/

@[expose] public noncomputable section

namespace Stacks.DegreeOneUnitAway

open HomogeneousLocalization Stacks.GradedLocalization

universe u v w

variable {A : Type u} [CommRing A]

/-- If every element of `K` is killed by a power of each element of `G`, and every prime not
containing the finitely generated ideal `𝔞` misses some element of `G`, then `K` is `𝔞`-power
torsion. -/
theorem isIPowerTorsion_of_forall_pow_smul {K : Type w} [AddCommGroup K] [Module A K]
    (𝔞 : Ideal A) (h𝔞 : 𝔞.FG) (G : Set A)
    (hG : ∀ p : Ideal A, p.IsPrime → ¬ 𝔞 ≤ p → ∃ g ∈ G, g ∉ p)
    (hK : ∀ x : K, ∀ g ∈ G, ∃ n : ℕ, g ^ n • x = 0) :
    IsIPowerTorsion A K 𝔞 := by
  intro x
  let J : Ideal A := (Submodule.span A {x}).annihilator
  have hmemJ : ∀ a : A, a ∈ J ↔ a • x = 0 := fun a => Submodule.mem_annihilator_span_singleton x a
  have hrad : 𝔞 ≤ J.radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf ?_
    rintro p ⟨hJp, hp⟩
    by_contra hnot
    obtain ⟨g, hg, hgp⟩ := hG p hp hnot
    obtain ⟨n, hn⟩ := hK x g hg
    exact hgp (hp.mem_of_pow_mem n (hJp ((hmemJ _).2 hn)))
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad h𝔞
  refine ⟨n + 1, Nat.succ_pos n, fun a ha => (hmemJ a).1 (hn ?_)⟩
  exact Ideal.pow_le_pow_right (Nat.le_succ n) ha

/-- A power of `g` moves every element of `J • T₀` into the image of `J • T₁`, as soon as it moves
every element of `T₀` into the range of `t`. -/
theorem exists_pow_smul_mem_map_smul_top {T₁ T₀ : Type w} [AddCommGroup T₁] [Module A T₁]
    [AddCommGroup T₀] [Module A T₀] (t : T₁ →ₗ[A] T₀) (J : Ideal A) (g : A)
    (hsurj : ∀ y : T₀, ∃ q : ℕ, g ^ q • y ∈ LinearMap.range t) {z : T₀}
    (hz : z ∈ J • (⊤ : Submodule A T₀)) :
    ∃ q : ℕ, g ^ q • z ∈ (J • (⊤ : Submodule A T₁)).map t := by
  refine Submodule.smul_induction_on hz (fun a ha y _ => ?_) (fun z z' hz hz' => ?_)
  · obtain ⟨q, x, hx⟩ := hsurj y
    refine ⟨q, ⟨a • x, Submodule.smul_mem_smul ha Submodule.mem_top, ?_⟩⟩
    rw [map_smul, hx, smul_comm]
  · obtain ⟨q, hq⟩ := hz
    obtain ⟨q', hq'⟩ := hz'
    refine ⟨q + q', ?_⟩
    rw [smul_add]
    refine add_mem ?_ ?_
    · rw [pow_add, mul_comm, mul_smul]
      exact Submodule.smul_of_tower_mem _ _ hq
    · rw [pow_add, mul_smul]
      exact Submodule.smul_of_tower_mem _ _ hq'

/-- A map `Mmap : T₁ / Jⁿ⁺² T₁ → T₀ / Jⁿ⁺¹ T₀` induced by `t` factors through the quotient by
`Jⁿ⁺¹`, with `𝔞`-power torsion kernel and cokernel, as soon as a power of each element of `G`
moves every element of `T₀` into the range of `t` and every element of the kernel of `t` into
`Jⁿ⁺¹ T₁`. -/
theorem exists_liftQ_isIPowerTorsion {T₁ T₀ : Type w} [AddCommGroup T₁] [Module A T₁]
    [AddCommGroup T₀] [Module A T₀] (t : T₁ →ₗ[A] T₀) (J 𝔞 : Ideal A) (h𝔞 : 𝔞.FG) (n : ℕ)
    (G : Set A) (hG : ∀ p : Ideal A, p.IsPrime → ¬ 𝔞 ≤ p → ∃ g ∈ G, g ∉ p)
    (hsurj : ∀ g ∈ G, ∀ y : T₀, ∃ q : ℕ, g ^ q • y ∈ LinearMap.range t)
    (hker : ∀ g ∈ G, ∀ x : T₁, t x = 0 → ∃ p : ℕ, g ^ p • x ∈ J ^ (n + 1) • (⊤ : Submodule A T₁))
    (Mmap : (T₁ ⧸ J ^ (n + 1 + 1) • (⊤ : Submodule A T₁)) →ₗ[A]
      (T₀ ⧸ J ^ (n + 1) • (⊤ : Submodule A T₀)))
    (hMmap : ∀ x : T₁, Mmap (Submodule.Quotient.mk x) = Submodule.Quotient.mk (t x)) :
    ∃ f : ((T₁ ⧸ J ^ (n + 1 + 1) • (⊤ : Submodule A T₁)) ⧸
        J ^ (n + 1) • (⊤ : Submodule A (T₁ ⧸ J ^ (n + 1 + 1) • (⊤ : Submodule A T₁)))) →ₗ[A]
          (T₀ ⧸ J ^ (n + 1) • (⊤ : Submodule A T₀)),
      (f.comp (J ^ (n + 1) •
        (⊤ : Submodule A (T₁ ⧸ J ^ (n + 1 + 1) • (⊤ : Submodule A T₁)))).mkQ = Mmap) ∧
      IsIPowerTorsion A (LinearMap.ker f) 𝔞 ∧
      IsIPowerTorsion A ((T₀ ⧸ J ^ (n + 1) • (⊤ : Submodule A T₀)) ⧸ LinearMap.range f) 𝔞 := by
  set P := J ^ (n + 1) • (⊤ : Submodule A (T₁ ⧸ J ^ (n + 1 + 1) • (⊤ : Submodule A T₁)))
    with hPdef
  have hP : P ≤ LinearMap.ker Mmap := by
    refine Submodule.smul_le.2 fun a ha x _ => ?_
    rw [LinearMap.mem_ker, map_smul]
    induction (Mmap x) using Submodule.Quotient.induction_on with
    | H y =>
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact Submodule.smul_mem_smul ha Submodule.mem_top
  have hmkQ : ∀ x : T₁, x ∈ J ^ (n + 1) • (⊤ : Submodule A T₁) →
      (Submodule.Quotient.mk x : T₁ ⧸ J ^ (n + 1 + 1) • (⊤ : Submodule A T₁)) ∈ P := by
    intro x hx
    have hle : J ^ (n + 1) • (⊤ : Submodule A T₁) ≤
        P.comap (J ^ (n + 1 + 1) • (⊤ : Submodule A T₁)).mkQ :=
      Submodule.smul_le.2 fun a ha y _ => by
        rw [Submodule.mem_comap, map_smul]
        exact Submodule.smul_mem_smul ha Submodule.mem_top
    exact hle hx
  refine ⟨P.liftQ Mmap hP, P.liftQ_mkQ Mmap hP, ?_, ?_⟩
  · refine isIPowerTorsion_of_forall_pow_smul 𝔞 h𝔞 G hG fun x g hg => ?_
    obtain ⟨x, hx⟩ := x
    induction x using Submodule.Quotient.induction_on with
    | H x =>
    induction x using Submodule.Quotient.induction_on with
    | H x =>
    rw [LinearMap.mem_ker, Submodule.liftQ_apply, hMmap, Submodule.Quotient.mk_eq_zero] at hx
    obtain ⟨q, x', hx', hx'eq⟩ := exists_pow_smul_mem_map_smul_top t (J ^ (n + 1)) g
      (hsurj g hg) hx
    have hz : t (g ^ q • x - x') = 0 := by rw [map_sub, map_smul, hx'eq, sub_self]
    obtain ⟨p, hp⟩ := hker g hg _ hz
    have hmem : g ^ (p + q) • x ∈ J ^ (n + 1) • (⊤ : Submodule A T₁) := by
      have h2 : g ^ (p + q) • x = g ^ p • (g ^ q • x - x') + g ^ p • x' := by
        rw [smul_sub, smul_smul, ← pow_add, sub_add_cancel]
      rw [h2]
      exact add_mem hp (Submodule.smul_of_tower_mem _ _ hx')
    refine ⟨p + q, Subtype.ext ?_⟩
    show g ^ (p + q) • (Submodule.Quotient.mk (Submodule.Quotient.mk x) : _ ⧸ P) = 0
    rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_eq_zero]
    exact hmkQ _ hmem
  · refine isIPowerTorsion_of_forall_pow_smul 𝔞 h𝔞 G hG fun x g hg => ?_
    induction x using Submodule.Quotient.induction_on with
    | H x =>
    induction x using Submodule.Quotient.induction_on with
    | H x =>
    obtain ⟨q, x', hx'⟩ := hsurj g hg x
    refine ⟨q, ?_⟩
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, ← Submodule.Quotient.mk_smul]
    refine ⟨Submodule.Quotient.mk (Submodule.Quotient.mk x'), ?_⟩
    rw [Submodule.liftQ_apply, hMmap, hx']

variable {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A] {𝒜 : ℕ → σ} [GradedRing 𝒜]

section Module

variable {M : Type v} [AddCommGroup M] [Module A M] {τ : Type*} [SetLike τ M]
  [AddSubgroupClass τ M] {𝓜 : ℤ → τ} [DirectSum.Decomposition 𝓜] [SetLike.GradedSMul 𝒜 𝓜]
  {N : Type v} [AddCommGroup N] [Module A N] {τ' : Type*} [SetLike τ' N]
  [AddSubgroupClass τ' N] {𝓝 : ℤ → τ'} [DirectSum.Decomposition 𝓝] [SetLike.GradedSMul 𝒜 𝓝]
  {c b g : A} {m : ℕ}

omit [SetLike.GradedSMul 𝒜 𝓜] [SetLike.GradedSMul 𝒜 𝓝] in
/-- A degree-preserving map commutes with taking homogeneous components. -/
theorem map_decompose (φ : M →ₗ[A] N) (hφ : ∀ (e : ℤ) (x : M), x ∈ 𝓜 e → φ x ∈ 𝓝 e)
    (x : M) (e : ℤ) :
    φ (DirectSum.decompose 𝓜 x e : M) = (DirectSum.decompose 𝓝 (φ x) e : N) := by
  classical
  induction x using DirectSum.Decomposition.inductionOn 𝓜 with
  | zero => simp
  | homogeneous x =>
      rename_i j
      have hφx : φ (x : M) ∈ 𝓝 j := hφ j x x.2
      by_cases hn : j = e
      · subst hn
        rw [DirectSum.decompose_of_mem_same 𝓜 x.2, DirectSum.decompose_of_mem_same 𝓝 hφx]
      · rw [DirectSum.decompose_of_mem_ne 𝓜 x.2 hn, DirectSum.decompose_of_mem_ne 𝓝 hφx hn,
          map_zero]
  | add x y hx hy =>
      rw [DirectSum.decompose_add, DirectSum.add_apply, AddMemClass.coe_add, map_add, hx, hy,
        map_add, DirectSum.decompose_add, DirectSum.add_apply, AddMemClass.coe_add]

omit [DirectSum.Decomposition 𝓜] [SetLike.GradedSMul 𝒜 𝓜] in
/-- The fraction with denominator one of a finite sum is the sum of the fractions. -/
theorem mk_sum_one {ι : Type*} (s : Finset ι) (w : ι → M) :
    LocalizedModule.mk (∑ i ∈ s, w i) (1 : Submonoid.powers g) =
      ∑ i ∈ s, LocalizedModule.mk (w i) (1 : Submonoid.powers g) :=
  map_sum (LocalizedModule.mkLinearMap (Submonoid.powers g) M) w s

/-- A homogeneous fraction with denominator one is a power of the chart unit times a degree-zero
fraction. -/
private theorem exists_mk_one_eq_chartUnit_zpow_smul (hc : c ∈ 𝒜 (m + 1)) (hb : b ∈ 𝒜 m)
    (hcb : c * b = g) {e : ℤ} {x : M} (hx : x ∈ 𝓜 e) :
    ∃ (j : ℤ) (z : LocalizedModule.Away (R := A) g M),
      z ∈ GradedModuleDegreeZeroLocalization 𝒜 𝓜 g ∧
        LocalizedModule.mk x (1 : Submonoid.powers g) =
          ((chartUnit hcb ^ j : (Localization.Away g)ˣ) : Localization.Away g) • z := by
  obtain ⟨z, hz, heq⟩ := exists_mk_eq_chartUnit_zpow_smul (𝓜 := 𝓜) hc hb hcb hx 0
  exact ⟨_, z, hz, by rwa [show genPow g 0 = 1 from Subtype.ext (pow_zero g)] at heq⟩

/-- Each homogeneous component killed by `φ` is a power of the chart unit times a degree-zero
fraction in the kernel of `φ`. -/
private theorem exists_mk_decompose_eq_smul_of_map_eq_zero (hc : c ∈ 𝒜 (m + 1))
    (hb : b ∈ 𝒜 m) (hcb : c * b = g) (φ : M →ₗ[A] N) {x : M} (e : ℤ)
    (hx : φ (DirectSum.decompose 𝓜 x e : M) = 0) :
    ∃ (j : ℤ) (z : LocalizedModule.Away (R := A) g M),
      z ∈ GradedModuleDegreeZeroLocalization 𝒜 𝓜 g ∧
        LocalizedModule.map (Submonoid.powers g) φ z = 0 ∧
        LocalizedModule.mk (DirectSum.decompose 𝓜 x e : M) (1 : Submonoid.powers g) =
          ((chartUnit hcb ^ j : (Localization.Away g)ˣ) : Localization.Away g) • z := by
  classical
  obtain ⟨j, z, hz, heq⟩ := exists_mk_one_eq_chartUnit_zpow_smul hc hb hcb
    (DirectSum.decompose 𝓜 x e).2
  have hmap : LocalizedModule.map (Submonoid.powers g) φ
      (LocalizedModule.mk (DirectSum.decompose 𝓜 x e : M) 1) = 0 := by
    rw [LocalizedModule.map_mk, hx, LocalizedModule.zero_mk]
  rw [heq, LinearMap.map_smul] at hmap
  refine ⟨j, z, hz, ?_, heq⟩
  have := congrArg (fun v => (((chartUnit hcb ^ j)⁻¹ : (Localization.Away g)ˣ) :
    Localization.Away g) • v) hmap
  simpa [smul_smul] using this

omit [SetLike.GradedSMul 𝒜 𝓝] in
/-- Elements of the kernel of `φ` are `g`-power torsion, as soon as `φ` is injective on
degree-zero localizations at `g = cb`. -/
theorem exists_pow_smul_eq_zero_of_map_eq_zero (hc : c ∈ 𝒜 (m + 1)) (hb : b ∈ 𝒜 m)
    (hcb : c * b = g) (φ : M →ₗ[A] N) (hφ : ∀ (e : ℤ) (x : M), x ∈ 𝓜 e → φ x ∈ 𝓝 e)
    (hinj : ∀ z ∈ GradedModuleDegreeZeroLocalization 𝒜 𝓜 g,
      LocalizedModule.map (Submonoid.powers g) φ z = 0 → z = 0)
    {x : M} (hx : φ x = 0) : ∃ p : ℕ, g ^ p • x = 0 := by
  classical
  have key : ∀ e : ℤ, LocalizedModule.mk (DirectSum.decompose 𝓜 x e : M)
      (1 : Submonoid.powers g) = 0 := by
    intro e
    obtain ⟨j, z, hz, hz0, heq⟩ := exists_mk_decompose_eq_smul_of_map_eq_zero hc hb hcb φ e
      (by rw [map_decompose φ hφ, hx, DirectSum.decompose_zero]; rfl)
    rw [heq, hinj z hz hz0, smul_zero]
  have hsum : LocalizedModule.mk x (1 : Submonoid.powers g) = 0 := by
    rw [← DirectSum.sum_support_decompose 𝓜 x, mk_sum_one]
    exact Finset.sum_eq_zero fun e _ => key e
  exact exists_pow_smul_eq_zero_of_mk_eq_zero _ hsum

/-- A power of `g` moves every element of `N` into the range of `φ`, as soon as `φ` is
surjective on degree-zero localizations at `g = cb`. -/
theorem exists_pow_smul_mem_range (hc : c ∈ 𝒜 (m + 1)) (hb : b ∈ 𝒜 m)
    (hcb : c * b = g) (φ : M →ₗ[A] N)
    (hsurj : ∀ z ∈ GradedModuleDegreeZeroLocalization 𝒜 𝓝 g,
      ∃ w ∈ GradedModuleDegreeZeroLocalization 𝒜 𝓜 g,
        LocalizedModule.map (Submonoid.powers g) φ w = z)
    (y : N) : ∃ p : ℕ, g ^ p • y ∈ LinearMap.range φ := by
  classical
  have key : ∀ e : ℤ, LocalizedModule.mk (DirectSum.decompose 𝓝 y e : N)
      (1 : Submonoid.powers g) ∈ LinearMap.range (LocalizedModule.map (Submonoid.powers g) φ) := by
    intro e
    obtain ⟨j, z, hz, heq⟩ := exists_mk_one_eq_chartUnit_zpow_smul (𝓜 := 𝓝) hc hb hcb
      (DirectSum.decompose 𝓝 y e).2
    obtain ⟨w, -, hw⟩ := hsurj z hz
    rw [heq, ← hw, ← LinearMap.map_smul]
    exact LinearMap.mem_range_self _ _
  have hmem : LocalizedModule.mk y (1 : Submonoid.powers g) ∈
      LinearMap.range (LocalizedModule.map (Submonoid.powers g) φ) := by
    rw [← DirectSum.sum_support_decompose 𝓝 y, mk_sum_one]
    exact Submodule.sum_mem _ fun e _ => key e
  obtain ⟨w, hw⟩ := hmem
  induction w using LocalizedModule.induction_on with
  | h x s =>
    rw [LocalizedModule.map_mk] at hw
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := LocalizedModule.mk_eq.mp hw
    obtain ⟨_, j, rfl⟩ := s
    refine ⟨k + j, ⟨g ^ k • x, ?_⟩⟩
    simp only [Submonoid.smul_def, one_smul] at hk
    rw [LinearMap.map_smul, hk, pow_add, mul_smul]

/-- The module `M[1/g]` over the degree-zero localization `Away 𝒜 g`, by restriction of scalars
along `Away 𝒜 g → A[1/g]`. -/
local instance moduleAway' (g : A) : Module (Away 𝒜 g) (LocalizedModule.Away (R := A) g M) :=
  Module.compHom (R := Localization.Away g) (LocalizedModule.Away (R := A) g M)
    (algebraMap (Away 𝒜 g) (Localization.Away g))

omit [DirectSum.Decomposition 𝓜] [SetLike.GradedSMul 𝒜 𝓜] in
/-- The fractions with numerator a multiple of `fᵏ` are stable under the action of `A[1/g]`. -/
theorem exists_mk_pow_smul_of_smul {f : A} (k : ℕ) (r : Localization.Away g)
    {v : LocalizedModule.Away (R := A) g M}
    (hv : ∃ (y : M) (t : Submonoid.powers g), v = LocalizedModule.mk (f ^ k • y) t) :
    ∃ (y : M) (t : Submonoid.powers g), r • v = LocalizedModule.mk (f ^ k • y) t := by
  obtain ⟨y, t, rfl⟩ := hv
  induction r using Localization.induction_on with
  | H r =>
    obtain ⟨a, s⟩ := r
    refine ⟨a • y, s * t, ?_⟩
    rw [LocalizedModule.mk_smul_mk, smul_comm]

omit [SetLike.GradedSMul 𝒜 𝓝] in
/-- Elements of the kernel of `φ` are, up to a power of `g`, multiples of `fᵏ`, as soon as on
degree-zero localizations at `g = cb` the kernel of `φ` consists of multiples of `wᵏ`, `w` the
chart ratio of the degree-one element `f`. -/
theorem exists_pow_smul_mem_of_map_eq_zero (hc : c ∈ 𝒜 (m + 1)) (hb : b ∈ 𝒜 m)
    (hcb : c * b = g) {f : A} (hf : f ∈ 𝒜 1) (k : ℕ) (φ : M →ₗ[A] N)
    (hφ : ∀ (e : ℤ) (x : M), x ∈ 𝓜 e → φ x ∈ 𝓝 e)
    (hker : ∀ z ∈ GradedModuleDegreeZeroLocalization 𝒜 𝓜 g,
      LocalizedModule.map (Submonoid.powers g) φ z = 0 →
        ∃ z' ∈ GradedModuleDegreeZeroLocalization 𝒜 𝓜 g, z = chartRatio hc hb hcb hf ^ k • z')
    {x : M} (hx : φ x = 0) :
    ∃ p : ℕ, g ^ p • x ∈ Ideal.span {f} ^ k • (⊤ : Submodule A M) := by
  classical
  have hg := mul_mem hc hb hcb
  have key : ∀ e : ℤ, ∃ (y : M) (t : Submonoid.powers g),
      LocalizedModule.mk (DirectSum.decompose 𝓜 x e : M) (1 : Submonoid.powers g) =
        LocalizedModule.mk (f ^ k • y) t := by
    intro e
    obtain ⟨j, z, hz, hz0, heq⟩ := exists_mk_decompose_eq_smul_of_map_eq_zero hc hb hcb φ e
      (by rw [map_decompose φ hφ, hx, DirectSum.decompose_zero]; rfl)
    obtain ⟨z', hz', rfl⟩ := hker z hz hz0
    obtain ⟨n, y, -, rfl⟩ := exists_eq_mk_of_mem hg hz'
    rw [heq]
    refine exists_mk_pow_smul_of_smul k _ ⟨b ^ (2 * k) • y, genPow g (n + k), ?_⟩
    rw [away_smul_eq]
    simpa only [away_smul_eq] using chartRatio_pow_smul_mk (M := M) hc hb hcb hf k n y
  have hsmem : ∀ e : ℤ, ∃ p : ℕ, g ^ p • (DirectSum.decompose 𝓜 x e : M) ∈
      Ideal.span {f} ^ k • (⊤ : Submodule A M) := by
    intro e
    obtain ⟨y, ⟨_, j, rfl⟩, hyt⟩ := key e
    obtain ⟨⟨_, q, rfl⟩, hq⟩ := LocalizedModule.mk_eq.mp hyt
    refine ⟨q + j, (mem_span_pow_smul_top_iff k _).2 ⟨g ^ q • y, ?_⟩⟩
    simp only [Submonoid.smul_def, one_smul] at hq
    rw [pow_add, mul_smul, smul_comm, ← hq, smul_comm]
  choose p hp using hsmem
  set S := (DirectSum.decompose 𝓜 x).support with hS
  refine ⟨∑ e ∈ S, p e, ?_⟩
  have hsum : g ^ (∑ e ∈ S, p e) • x =
      ∑ e ∈ S, g ^ (∑ e ∈ S, p e) • (DirectSum.decompose 𝓜 x e : M) := by
    rw [← Finset.smul_sum, hS, DirectSum.sum_support_decompose]
  rw [hsum]
  refine Submodule.sum_mem _ fun e he => ?_
  rw [← Finset.add_sum_erase _ _ he, pow_add, mul_comm, mul_smul]
  exact Submodule.smul_of_tower_mem _ _ (hp e)

omit [DirectSum.Decomposition 𝓝] [SetLike.GradedSMul 𝒜 𝓝] in
/-- Multiples of `fᵏ` are `g`-power torsion as soon as `wᵏ` kills the degree-zero
localization at `g = cb`, `w` the chart ratio of the degree-one element `f`. -/
theorem exists_pow_smul_pow_smul_eq_zero (hc : c ∈ 𝒜 (m + 1)) (hb : b ∈ 𝒜 m)
    (hcb : c * b = g) {f : A} (hf : f ∈ 𝒜 1) (k : ℕ)
    (hker : ∀ z ∈ GradedModuleDegreeZeroLocalization 𝒜 𝓜 g, chartRatio hc hb hcb hf ^ k • z = 0)
    (y : M) : ∃ p : ℕ, g ^ p • (f ^ k • y) = 0 := by
  classical
  have key : ∀ e : ℤ, LocalizedModule.mk (f ^ k • (DirectSum.decompose 𝓜 y e : M))
      (1 : Submonoid.powers g) = 0 := by
    intro e
    obtain ⟨j, z, hz, heq⟩ := exists_mk_one_eq_chartUnit_zpow_smul hc hb hcb
      (DirectSum.decompose 𝓜 y e).2
    have hsmul : LocalizedModule.mk (f ^ k • (DirectSum.decompose 𝓜 y e : M))
        (1 : Submonoid.powers g) =
          (algebraMap A (Localization.Away g) f) ^ k •
            LocalizedModule.mk (DirectSum.decompose 𝓜 y e : M) (1 : Submonoid.powers g) := by
      rw [← map_pow, algebraMap_smul, LocalizedModule.smul'_mk]
    rw [hsmul, heq, algebraMap_eq_chartRatio_mul hc hb hcb hf, mul_pow, mul_comm, mul_smul,
      smul_comm (((chartRatio hc hb hcb hf).val) ^ k), ← HomogeneousLocalization.val_pow]
    have h0 := hker z hz
    rw [away_smul_eq] at h0
    rw [h0, smul_zero, smul_zero]
  have hsum : LocalizedModule.mk (f ^ k • y) (1 : Submonoid.powers g) = 0 := by
    rw [← DirectSum.sum_support_decompose 𝓜 y, Finset.smul_sum, mk_sum_one]
    exact Finset.sum_eq_zero fun e _ => key e
  exact exists_pow_smul_eq_zero_of_mk_eq_zero _ hsum

end Module

end Stacks.DegreeOneUnitAway

end
