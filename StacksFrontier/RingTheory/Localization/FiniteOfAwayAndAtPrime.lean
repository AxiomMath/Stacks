module

public import Mathlib.RingTheory.Localization.Finiteness

/-!
# Finiteness from finiteness away from a prime and at it

Let `R` be a ring, `M` an `R`-module, `𝔭 ⊂ R` a prime and `t ⊆ R` a finite set such that every
maximal ideal other than `𝔭` misses an element of `t`; geometrically, the basic opens `D(r)`,
`r ∈ t`, cover the maximal points of `Spec R` other than `𝔭`. If `M_r` is a finite `R_r`-module
for every `r ∈ t` and `M_𝔭` is a finite `R_𝔭`-module, then `M` is a finite `R`-module.

The proof: numerators of finitely many generators of each `M_r` and of `M_𝔭` span a submodule
`N ⊆ M` such that every `x ∈ M` has `r ^ n • x ∈ N` for each `r ∈ t` and `s • x ∈ N` for some
`s ∉ 𝔭`. The ideal `{a | a • x ∈ N}` is then contained in no maximal ideal, so `x ∈ N`.

## Main results

* `Module.Finite.exists_finset_smul_mem_span_of_isLocalizedModule`: if `S⁻¹M` is a finite
  `S⁻¹R`-module, finitely many elements of `M` span `M` up to multiplication by `S`.
* `Module.Finite.of_isLocalizedModule_away_of_isLocalizedModule_atPrime`: the statement above.
-/

@[expose] public section

namespace Module.Finite

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- If `S⁻¹M` is a finite `S⁻¹R`-module, there is a finite subset `F ⊆ M` such that every
element of `M` has a multiple by an element of `S` in the span of `F`. -/
theorem exists_finset_smul_mem_span_of_isLocalizedModule (S : Submonoid R)
    (Rₛ : Type*) [CommRing Rₛ] [Algebra R Rₛ] [IsLocalization S Rₛ]
    {Mₛ : Type*} [AddCommGroup Mₛ] [Module R Mₛ] [Module Rₛ Mₛ] [IsScalarTower R Rₛ Mₛ]
    (f : M →ₗ[R] Mₛ) [IsLocalizedModule S f] [h : Module.Finite Rₛ Mₛ] :
    ∃ F : Finset M, ∀ x : M, ∃ s : S, (s : R) • x ∈ Submodule.span R (F : Set M) := by
  classical
  obtain ⟨s₁, s₂⟩ := h.1
  refine ⟨IsLocalizedModule.finsetIntegerMultiple S f s₁, fun x => ?_⟩
  obtain ⟨m₁, hn₁⟩ := multiple_mem_span_of_mem_localization_span S Rₛ
    (s₁ : Set Mₛ) (IsLocalizedModule.mk' f x (1 : S)) (s₂ ▸ Submodule.mem_top)
  rw [Submonoid.smul_def, ← IsLocalizedModule.mk'_smul, IsLocalizedModule.mk'_one] at hn₁
  obtain ⟨m₂, hn₂⟩ := IsLocalizedModule.smul_mem_finsetIntegerMultiple_span S f _ s₁ hn₁
  rw [Submonoid.smul_def] at hn₂
  exact ⟨m₂ * m₁, by rwa [Submonoid.coe_mul, mul_smul]⟩

/-- **Finiteness from finiteness on a punctured neighbourhood and at the puncture.** Let `𝔭`
be a prime of `R` and `t` a finite subset of `R` such that every maximal ideal other than `𝔭`
misses some element of `t`. If `M_r` is a finite `R_r`-module for every `r ∈ t` and `M_𝔭` is a
finite `R_𝔭`-module, then `M` is a finite `R`-module. The localizations are given through their
universal properties (`IsLocalizedModule`), as in `Module.Finite.of_localizationSpan_finite'`,
which is the case where no maximal ideal contains `t` (then the `𝔭` hypothesis is not used). -/
theorem of_isLocalizedModule_away_of_isLocalizedModule_atPrime (p : Ideal R) [p.IsPrime]
    (t : Finset R) (ht : ∀ q : Ideal R, q.IsMaximal → q ≠ p → ∃ r ∈ t, r ∉ q)
    {Rₜ : ∀ (_ : t), Type*} [∀ g : t, CommRing (Rₜ g)] [∀ g : t, Algebra R (Rₜ g)]
    [∀ g : t, IsLocalization.Away g.val (Rₜ g)]
    {Mₜ : ∀ (_ : t), Type*} [∀ g : t, AddCommGroup (Mₜ g)] [∀ g : t, Module R (Mₜ g)]
    [∀ g : t, Module (Rₜ g) (Mₜ g)] [∀ g : t, IsScalarTower R (Rₜ g) (Mₜ g)]
    (f : ∀ g : t, M →ₗ[R] Mₜ g) [∀ g : t, IsLocalizedModule.Away g.val (f g)]
    (H : ∀ g : t, Module.Finite (Rₜ g) (Mₜ g))
    (Rₚ : Type*) [CommRing Rₚ] [Algebra R Rₚ] [IsLocalization.AtPrime Rₚ p]
    {Mₚ : Type*} [AddCommGroup Mₚ] [Module R Mₚ] [Module Rₚ Mₚ] [IsScalarTower R Rₚ Mₚ]
    (fₚ : M →ₗ[R] Mₚ) [IsLocalizedModule p.primeCompl fₚ] (Hₚ : Module.Finite Rₚ Mₚ) :
    Module.Finite R M := by
  classical
  choose F hF using fun g : t =>
    exists_finset_smul_mem_span_of_isLocalizedModule (Submonoid.powers g.val) (Rₜ g) (f g)
  obtain ⟨Fₚ, hFₚ⟩ := exists_finset_smul_mem_span_of_isLocalizedModule p.primeCompl Rₚ fₚ
  let G : Finset M := Fₚ ∪ t.attach.biUnion F
  refine ⟨⟨G, eq_top_iff.2 fun x _ => ?_⟩⟩
  set N := Submodule.span R (G : Set M)
  let I : Ideal R := N.comap (LinearMap.toSpanSingleton R M x)
  suffices I = ⊤ by
    have : (1 : R) ∈ I := this ▸ Submodule.mem_top
    simpa [I, LinearMap.toSpanSingleton_apply] using this
  by_contra hne
  obtain ⟨q, hq, hIq⟩ := Ideal.exists_le_maximal I hne
  have key : ∀ A ⊆ G, ∀ a : R, a • x ∈ Submodule.span R (A : Set M) → a ∈ q := fun A hA a ha =>
    hIq (by simpa [I, LinearMap.toSpanSingleton_apply] using
      Submodule.span_mono (Finset.coe_subset.2 hA) ha)
  obtain rfl | hqp := eq_or_ne q p
  · obtain ⟨s, hs⟩ := hFₚ x
    exact s.2 (key _ Finset.subset_union_left _ hs)
  · obtain ⟨r, hr, hrq⟩ := ht q hq hqp
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := hF ⟨r, hr⟩ x
    exact hrq (hq.isPrime.mem_of_pow_mem n (key _
      ((Finset.subset_biUnion_of_mem F (Finset.mem_attach _ _)).trans
        Finset.subset_union_right) _ hn))

end Module.Finite
