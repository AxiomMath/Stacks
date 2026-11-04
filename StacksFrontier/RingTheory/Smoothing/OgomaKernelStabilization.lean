module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Noetherian.Basic

@[expose] public section

/-
# Problem Description

Lemma (Stacks Tag 07FC, Ogoma).

Let $A$ be a Noetherian ring and let $M$ be a finite $A$-module. Let $S \subseteq A$
be a multiplicative subset, and let $\pi \in A$. Suppose that
$$\operatorname{Ker}(\pi : S^{-1}M \to S^{-1}M)
  = \operatorname{Ker}(\pi^2 : S^{-1}M \to S^{-1}M).$$
Then there exists an element $s \in S$ such that for every integer $n > 0$ we have
$$\operatorname{Ker}(s^n \pi : M \to M) = \operatorname{Ker}((s^n \pi)^2 : M \to M),$$
where $s^n \pi : M \to M$ denotes multiplication by the ring element
$s^n \pi \in A$, and $(s^n\pi)^2 : M \to M$ denotes multiplication by
$(s^n\pi)^2 = s^{2n}\pi^2 \in A$.
-/

/-
## Background and context

Throughout, $A$ is a commutative ring with $1$, $M$ is an $A$-module, and
$S \subseteq A$ is a multiplicative subset (i.e. $1 \in S$ and $S$ is closed under
multiplication); this is modelled by `S : Submonoid A`.

For a ring element $a \in A$ and an $A$-module $N$, scalar multiplication by $a$ is
the $A$-linear endomorphism `LinearMap.lsmul A N a : N →ₗ[A] N`, $x \mapsto a \cdot x$
(this is $A$-linear because $A$ is commutative). Its kernel is the $a$-torsion
submodule `(LinearMap.lsmul A N a).ker = {x ∈ N | a • x = 0}`.

The localization $S^{-1}M$ is `LocalizedModule S M`, an $A$-module (indeed an
$S^{-1}A$-module), with canonical $A$-linear map
`LocalizedModule.mkLinearMap S M : M →ₗ[A] LocalizedModule S M`, $x \mapsto x/1$.
Multiplication by $a \in A$ on $S^{-1}M$ is `LinearMap.lsmul A (LocalizedModule S M) a`.

`M` is a finite $A$-module (`Module.Finite A M`) if it is finitely generated.
`A` is Noetherian (`IsNoetherianRing A`) if every ideal is finitely generated.

## Notes on interpretation

- All maps named "$\pi$", "$\pi^2$", "$s^n\pi$", "$(s^n\pi)^2$" are
  multiplication-by-a-ring-element endomorphisms of the indicated module
  ($M$ or $S^{-1}M$).
- The conclusion asserts the existence of a *single* $s \in S$ that works
  *simultaneously* for all positive integers $n$.
- The inclusion $\operatorname{Ker}(\pi : S^{-1}M) \subseteq
  \operatorname{Ker}(\pi^2 : S^{-1}M)$ always holds; the hypothesis is the
  nontrivial reverse inclusion. Likewise on $M$ the inclusion
  $\operatorname{Ker}(s^n\pi) \subseteq \operatorname{Ker}((s^n\pi)^2)$ is automatic,
  so the equality is the nontrivial reverse inclusion.
-/

-- Main Statement

/-- Stacks Tag 07FC (Ogoma's lemma). Over a Noetherian ring `A`, for a finite
`A`-module `M`, a multiplicative subset `S` and `π : A`, if multiplication by `π`
and `π²` have the same kernel on the localization `S⁻¹M`, then there is a single
`s ∈ S` such that for all `n > 0`, multiplication by `sⁿπ` and `(sⁿπ)²` have the
same kernel on `M`. -/
@[stacks 07FC]
theorem ogoma_ker_eq_of_localization {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    [IsNoetherianRing A] [Module.Finite A M] (S : Submonoid A) (π : A)
    (h : LinearMap.ker (LinearMap.lsmul A (LocalizedModule S M) π)
      = LinearMap.ker (LinearMap.lsmul A (LocalizedModule S M) (π ^ 2))) :
    ∃ s ∈ S, ∀ n : ℕ, 0 < n →
      LinearMap.ker (LinearMap.lsmul A M (s ^ n * π))
        = LinearMap.ker (LinearMap.lsmul A M ((s ^ n * π) ^ 2)) := by
  classical
  set f := LocalizedModule.mkLinearMap S M with hf
  -- Each element of the kernel of the localization map is S-torsion.
  have htor : ∀ m ∈ LinearMap.ker f, ∃ s : S, (s : A) • m = 0 := by
    intro m hm
    rw [LinearMap.mem_ker] at hm
    exact (IsLocalizedModule.eq_zero_iff S f).mp hm
  -- The kernel of the localization map is finitely generated (M is Noetherian),
  -- hence annihilated by a single element s0 ∈ S.
  have hfg : (LinearMap.ker f).FG := IsNoetherian.noetherian _
  obtain ⟨s0, hs0S, hs0kill⟩ :
      ∃ s ∈ S, ∀ m ∈ LinearMap.ker f, (s : A) • m = 0 := by
    obtain ⟨gen, hgen⟩ := hfg
    have hgenmem : ∀ g ∈ gen, g ∈ LinearMap.ker f := by
      intro g hg; rw [← hgen]; exact Submodule.subset_span hg
    choose g hg using fun x (hx : x ∈ gen) => htor x (hgenmem x hx)
    set s0 : A := ∏ x ∈ gen.attach, (g x.1 x.2 : A) with hs0
    refine ⟨s0, Submonoid.prod_mem S (fun x _ => (g x.1 x.2).2), ?_⟩
    have hle : LinearMap.ker f ≤ LinearMap.ker (LinearMap.lsmul A M s0) := by
      rw [← hgen, Submodule.span_le]
      intro x hx
      simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.lsmul_apply]
      have hdvd : (g x hx : A) ∣ s0 := by
        rw [hs0]
        exact Finset.dvd_prod_of_mem (fun (y : gen) => (g y.1 y.2 : A))
          (Finset.mem_attach gen ⟨x, hx⟩)
      obtain ⟨c, hc⟩ := hdvd
      rw [hc, mul_comm, mul_smul, hg x hx, smul_zero]
    intro m hm
    simpa [LinearMap.mem_ker] using hle hm
  -- We claim s = s0 works.
  refine ⟨s0, hs0S, ?_⟩
  -- Elements of S are units on S⁻¹M, so a power of s0 killing y forces y = 0.
  have hinj : ∀ (k : ℕ) (y : LocalizedModule S M), s0 ^ k • y = 0 → y = 0 := fun k y hy =>
    IsLocalizedModule.smul_injective f ⟨s0 ^ k, pow_mem hs0S k⟩ (by simpa using hy)
  intro n hn
  apply le_antisymm
  · -- ker(a) ≤ ker(a^2): automatic
    intro x hx
    rw [LinearMap.mem_ker, LinearMap.lsmul_apply] at hx ⊢
    rw [pow_two, mul_smul, hx, smul_zero]
  · -- ker(a^2) ≤ ker(a): the main argument
    intro x hx
    rw [LinearMap.mem_ker, LinearMap.lsmul_apply] at hx ⊢
    -- hx : (s0^n*π)^2 • x = 0,  goal : (s0^n*π) • x = 0
    set w : M := (s0 ^ n * π) • x with hw
    -- Step A: w ∈ ker f (i.e. f w = 0)
    have hfx : π • f x = 0 := by
      -- from hx: (s0^n*π)^2 • f x = 0, s0 is a unit, then use hypothesis h
      have h0 : ((s0 ^ n * π) ^ 2) • f x = 0 := by
        have : f (((s0 ^ n * π) ^ 2) • x) = 0 := by rw [hx, map_zero]
        rwa [map_smul] at this
      -- rewrite (s0^n*π)^2 = s0^(2n) * π^2
      have hpow : ((s0 ^ n * π) ^ 2) = s0 ^ (2 * n) * π ^ 2 := by ring
      rw [hpow, mul_smul] at h0
      have hπ2 : π ^ 2 • f x = 0 := hinj _ _ h0
      -- f x ∈ ker(lsmul π^2) = ker(lsmul π)
      have hmem2 : f x ∈ LinearMap.ker (LinearMap.lsmul A (LocalizedModule S M) (π ^ 2)) := by
        rw [LinearMap.mem_ker, LinearMap.lsmul_apply]; exact hπ2
      rw [← h] at hmem2
      rw [LinearMap.mem_ker, LinearMap.lsmul_apply] at hmem2
      exact hmem2
    have hwker : w ∈ LinearMap.ker f := by
      rw [LinearMap.mem_ker, hw, map_smul]
      -- f((s0^n*π)•x) = (s0^n*π)• f x = s0^n • (π • f x) = 0
      have : (s0 ^ n * π) • f x = s0 ^ n • (π • f x) := by rw [mul_smul]
      rw [this, hfx, smul_zero]
    -- Step B: w = s0 • z with z = (s0^(n-1)*π)•x, and conclude w = 0
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    set z : M := (s0 ^ m * π) • x with hz
    have hsz : s0 • z = w := by
      rw [hz, hw]
      rw [smul_smul]
      congr 1
      rw [← mul_assoc]
      congr 1
      rw [← pow_succ']
    -- s0 • w = 0 since w ∈ ker f and s0 kills ker f
    have hs0w : s0 • w = 0 := hs0kill w hwker
    -- s0^2 • z = s0 • (s0 • z) = s0 • w = 0
    have hs2z : s0 • (s0 • z) = 0 := by rw [hsz, hs0w]
    -- so z ∈ ker f
    have hzker : z ∈ LinearMap.ker f := by
      rw [LinearMap.mem_ker]
      refine hinj 2 _ ?_
      rw [← map_smul, pow_two, mul_smul, hs2z, map_zero]
    -- s0 • z = 0 since z ∈ ker f, hence w = 0
    have : s0 • z = 0 := hs0kill z hzker
    rw [← hsz, this]
