module

public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.Localization.Module

@[expose] public section

/-
# Problem Description (Stacks Tag 0AV7)

Let $R$ be a Noetherian (commutative) ring. Let $\varphi : M \to N$ be a map of
$R$-modules. Assume that for every prime ideal $\mathfrak p$ of $R$ at least one of
the following holds:

1. the localized map $\varphi_{\mathfrak p} : M_{\mathfrak p} \to N_{\mathfrak p}$
   is injective, or
2. $\mathfrak p \notin \operatorname{Ass}(M)$.

Then $\varphi$ is injective.
-/

-- # Background and context
--
-- * Localization at a prime: for a prime $\mathfrak p$ and an $R$-module $M$, the
--   localization $M_{\mathfrak p}$ is `LocalizedModule p.primeCompl M`, and the
--   localized map $\varphi_{\mathfrak p}$ is `LocalizedModule.map p.primeCompl φ`.
-- * Associated primes: $\operatorname{Ass}(M)$ is `associatedPrimes R M`; a prime
--   $\mathfrak p$ is associated to $M$ iff `p.IsAssociatedPrime M`, i.e. `p.IsPrime`
--   and there is $m : M$ with $p = \operatorname{Ann}_R(m)$.
-- * "Noetherian ring" means `IsNoetherianRing R`.
-- * "$\varphi$ is injective" means `Function.Injective ⇑φ`.

-- # Main Statement(s)

variable {R : Type*} [CommRing R] [IsNoetherianRing R]
variable {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- Stacks Tag 0AV7. If for every prime ideal `p` of the Noetherian ring `R` either
the localized map `φ_p : M_p → N_p` is injective or `p` is not an associated prime
of `M`, then `φ : M → N` is injective. -/
@[stacks 0AV7]
theorem injective_of_injective_localized_at_associatedPrimes (φ : M →ₗ[R] N)
    (h : ∀ p : Ideal R, [p.IsPrime] →
      Function.Injective (LocalizedModule.map p.primeCompl φ) ∨ p ∉ associatedPrimes R M) :
    Function.Injective φ := by
  -- Proof (Stacks 0AV7). Suppose φ is not injective, so
  -- K := ker φ ≠ ⊥, i.e. K is nontrivial. Since R is Noetherian and K is nonzero,
  -- Ass(K) is nonempty (`associatedPrimes.nonempty`); pick p ∈ Ass(K). As K ⊆ M via
  -- the inclusion `K.subtype` (injective), Ass(K) ⊆ Ass(M)
  -- (`associatedPrimes.subset_of_injective`), so p ∈ Ass(M). By hypothesis the localized
  -- map φ_p is injective. p ∈ Ass(K) gives x ∈ K with p = radical(Ann x) and φ x = 0.
  -- Then mk x 1 = 0 in M_p (injectivity of φ_p), so ∃ u ∈ p.primeCompl with u • x = 0,
  -- i.e. u ∈ Ann(x) ⊆ radical(Ann x) = p (`Ideal.le_radical`, `hx.ge`); but u ∈ p.primeCompl
  -- means u ∉ p, contradiction.
  rw [← LinearMap.ker_eq_bot]
  by_contra hk
  set K := LinearMap.ker φ
  have : Nontrivial K := Submodule.nontrivial_iff_ne_bot.mpr hk
  obtain ⟨p, hp⟩ := associatedPrimes.nonempty R K
  have hpM : p ∈ associatedPrimes R M :=
    associatedPrimes.subset_of_injective (Submodule.injective_subtype K) hp
  obtain ⟨hprime, x, hx⟩ := hp
  rcases h p with hinj | hnot
  · have hxker : φ (x : M) = 0 := LinearMap.mem_ker.mp x.prop
    have hmkzero : (LocalizedModule.mk (x : M) 1 : LocalizedModule p.primeCompl M) = 0 :=
      (LinearMap.map_eq_zero_iff _ hinj).mp <| by
        rw [LocalizedModule.map_mk, hxker, LocalizedModule.zero_mk]
    rw [← LocalizedModule.zero_mk (1 : p.primeCompl), LocalizedModule.mk_eq] at hmkzero
    obtain ⟨u, hu⟩ := hmkzero
    simp only [one_smul, smul_zero] at hu
    have hcolon : (u : R) ∈ (⊥ : Submodule R K).colon {x} := by
      rw [Submodule.mem_colon_singleton, Submodule.mem_bot]
      apply Submodule.injective_subtype K
      simp only [SetLike.val_smul, K.subtype_apply]
      exact hu
    exact Ideal.mem_primeCompl_iff.mp u.prop (hx.ge (Ideal.le_radical hcolon))
  · exact hnot hpM
