module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import StacksFrontier.RingTheory.Module.LocallyFree.FiniteProjective

/-!
# Factoring a power of `g` through a finite free module over `A ⧸ (f)`

Let `A` be a Noetherian ring, `f, g : A`, and let `M` be a finite `A`-module killed by `f`, so
that `M` is a module over `B = A ⧸ (f)`. If the localization of `M` at every prime of `B` lying
in the standard open `D(ḡ)` is free over the corresponding localization of `B`, then some power
of `g` on `M` factors through a finite free `B`-module, `A`-linearly.
-/

@[expose] public noncomputable section

universe u

namespace Stacks.BaseQuotientFactorization

/-- **Descent of a splitting along a localization at one element.** If `M` is a finitely
presented `R`-module whose localization `M_f` is projective over `R_f`, then a power of `f` on
`M` factors through a finite free `R`-module: lift a splitting of a presentation of `M_f` and
clear denominators. -/
theorem exists_pow_smul_comp_eq_of_projective_localizationAway
    {R : Type u} [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]
    [Module.FinitePresentation R M] (f : R)
    (hM : Module.Projective (Localization.Away f) (LocalizedModule.Away f M)) :
    ∃ (k d : ℕ) (a : (Fin d → R) →ₗ[R] M) (b : M →ₗ[R] (Fin d → R)),
      a ∘ₗ b = f ^ k • LinearMap.id := by
  let S := Submonoid.powers f
  let B := Localization.Away f
  obtain ⟨n, r, π, δ, hπ, hδ⟩ := Module.FinitePresentation.exists_fin' R M
  let F := Fin n → R
  let fF : F →ₗ[R] LocalizedModule.Away f F := LocalizedModule.mkLinearMap S F
  let fM : M →ₗ[R] LocalizedModule.Away f M := LocalizedModule.mkLinearMap S M
  let ρ := IsLocalizedModule.map S fF fM π
  have hρ : Function.Surjective ρ := IsLocalizedModule.map_surjective S fF fM π hπ
  let ρB := ρ.extendScalarsOfIsLocalization S B
  have : Module.Projective B (LocalizedModule.Away f M) := hM
  obtain ⟨sB, hsB⟩ := Module.projective_lifting_property ρB LinearMap.id hρ
  let sA := sB.restrictScalars R
  have hsA : ρ.comp sA = LinearMap.id := by
    ext x
    show ρB (sB x) = x
    exact congrArg (fun q : LocalizedModule.Away f M →ₗ[B] LocalizedModule.Away f M => q x) hsB
  obtain ⟨b, t, hb⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule
    S fF (sA.comp fM)
  change fF.comp b = t.1 • (sA.comp fM) at hb
  have hmap : ρ.comp fF = fM.comp π := IsLocalizedModule.map_comp S fF fM π
  have hlocal : fM.comp (π.comp b) = fM.comp (t.1 • LinearMap.id) := by
    calc
      fM.comp (π.comp b) = ρ.comp (fF.comp b) := by
        rw [← LinearMap.comp_assoc, ← hmap, LinearMap.comp_assoc]
      _ = ρ.comp (t.1 • (sA.comp fM)) := by rw [hb]
      _ = t.1 • ((ρ.comp sA).comp fM) := by
        rw [LinearMap.comp_smul, LinearMap.comp_assoc]
      _ = t.1 • fM := by rw [hsA, LinearMap.id_comp]
      _ = fM.comp (t.1 • LinearMap.id) := by
        simp [LinearMap.comp_smul]
  obtain ⟨t', ht'⟩ := Module.Finite.exists_smul_of_comp_eq_of_isLocalizedModule
    S fM (π.comp b) (t.1 • LinearMap.id) hlocal
  let a := t'.1 • π
  have hfactor : a.comp b = (t'.1 * t.1) • LinearMap.id := by
    ext x
    have hx := congrArg (fun q : M →ₗ[R] M => q x) ht'
    show (t'.1 • π) (b x) = ((t'.1 * t.1) • LinearMap.id) x
    simpa [Submonoid.smul_def, smul_smul] using hx
  have hpow : t'.1 * t.1 ∈ S := S.mul_mem t'.property t.property
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff (t'.1 * t.1) f).mp hpow
  exact ⟨k, n, a, b, by simpa [hk] using hfactor⟩

/-- **A power of `g` factors through a finite free module over `A ⧸ (f)`.** Here the `A`-module
`M` is presented as a module over `B = A ⧸ (f)` through a `Module B M` instance compatible with
the `A`-action (which forces `f • x = 0` for all `x`), and the hypothesis is that the
localization of `M` at every prime `q` of `B` with `ḡ ∉ q` is free over `B` localized at `q`. -/
theorem exists_pow_smul_factor_through_baseQuotient
    {A : Type u} [CommRing A] [IsNoetherianRing A] (f g : A)
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Module (A ⧸ Ideal.span {f}) M] [IsScalarTower A (A ⧸ Ideal.span {f}) M]
    (hfree : ∀ (q : Ideal (A ⧸ Ideal.span {f})) [q.IsPrime],
      Ideal.Quotient.mk (Ideal.span {f}) g ∉ q →
      Module.Free (Localization.AtPrime q) (LocalizedModule q.primeCompl M)) :
    ∃ (k d : ℕ) (a : (Fin d → (A ⧸ Ideal.span {f})) →ₗ[A] M)
        (b : M →ₗ[A] (Fin d → (A ⧸ Ideal.span {f}))),
      a ∘ₗ b = g ^ k • LinearMap.id := by
  have : Module.Finite (A ⧸ Ideal.span {f}) M :=
    Module.Finite.of_restrictScalars_finite A (A ⧸ Ideal.span {f}) M
  have : Module.FinitePresentation (A ⧸ Ideal.span {f}) M :=
    Module.finitePresentation_of_finite _ _
  have hsub : (PrimeSpectrum.basicOpen (Ideal.Quotient.mk (Ideal.span {f}) g) :
      Set (PrimeSpectrum (A ⧸ Ideal.span {f}))) ⊆ Module.freeLocus (A ⧸ Ideal.span {f}) M := by
    intro x hx
    exact hfree x.asIdeal (PrimeSpectrum.mem_basicOpen _ _ |>.mp hx)
  obtain ⟨k, d, a, b, hab⟩ := exists_pow_smul_comp_eq_of_projective_localizationAway
    (R := A ⧸ Ideal.span {f}) M (Ideal.Quotient.mk (Ideal.span {f}) g)
    (Module.basicOpen_subset_freeLocus_iff.mp hsub)
  refine ⟨k, d, a.restrictScalars A, b.restrictScalars A, ?_⟩
  ext x
  have hx := LinearMap.congr_fun hab x
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.smul_apply, LinearMap.id_coe,
    id_eq] at hx
  show a (b x) = g ^ k • x
  rw [hx, ← map_pow, ← Ideal.Quotient.algebraMap_eq, algebraMap_smul]

/-- **A power of `g` factors through a finite free module over `A ⧸ (f)`**, with the local
freeness hypothesis indexed by the primes `p` of `A` that contain `f` and avoid `g`: for such a
`p`, the localization of `M` at `p` — equivalently, at the prime `q = pB` of `B = A ⧸ (f)` it
corresponds to — is required to be free over `B` localized at `p`. -/
theorem exists_pow_smul_factor_through_baseQuotient_of_primes
    {A : Type u} [CommRing A] [IsNoetherianRing A] (f g : A)
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Module (A ⧸ Ideal.span {f}) M] [IsScalarTower A (A ⧸ Ideal.span {f}) M]
    (hfree : ∀ (p : Ideal A) [p.IsPrime] (q : Ideal (A ⧸ Ideal.span {f})) [q.IsPrime],
      q = p.map (Ideal.Quotient.mk (Ideal.span {f})) → g ∉ p → f ∈ p →
      Module.Free (Localization.AtPrime q) (LocalizedModule q.primeCompl M)) :
    ∃ (k d : ℕ) (a : (Fin d → (A ⧸ Ideal.span {f})) →ₗ[A] M)
        (b : M →ₗ[A] (Fin d → (A ⧸ Ideal.span {f}))),
      a ∘ₗ b = g ^ k • LinearMap.id := by
  refine exists_pow_smul_factor_through_baseQuotient f g M fun q _ hq ↦ ?_
  have hfmem : f ∈ q.comap (Ideal.Quotient.mk (Ideal.span {f})) := by
    rw [Ideal.mem_comap,
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self f)]
    exact q.zero_mem
  refine hfree (q.comap (Ideal.Quotient.mk (Ideal.span {f}))) q ?_ ?_ hfmem
  · exact (Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective q).symm
  · exact fun h ↦ hq (Ideal.mem_comap.mp h)

/-- **A power of `g` factors through a finite free module over `A ⧸ (f)`**, with the hypothesis
that `f` kills `M` written out. The module structure of `M` over `B = A ⧸ (f)` used to state the
local freeness hypothesis is the one produced by `Module.IsTorsionBy.module`; on it
`Ideal.Quotient.mk (Ideal.span {f}) a • x = a • x` holds by definition. -/
theorem exists_pow_smul_factor_through_baseQuotient_of_smul_eq_zero
    {A : Type u} [CommRing A] [IsNoetherianRing A] (f g : A)
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (hfM : ∀ x : M, f • x = 0)
    (hfree : letI : Module (A ⧸ Ideal.span {f}) M :=
        Module.IsTorsionBy.module (R := A) (M := M) (r := f) (fun ⦃x⦄ => hfM x)
      ∀ (q : Ideal (A ⧸ Ideal.span {f})) [q.IsPrime],
        Ideal.Quotient.mk (Ideal.span {f}) g ∉ q →
        Module.Free (Localization.AtPrime q) (LocalizedModule q.primeCompl M)) :
    ∃ (k d : ℕ) (a : (Fin d → (A ⧸ Ideal.span {f})) →ₗ[A] M)
        (b : M →ₗ[A] (Fin d → (A ⧸ Ideal.span {f}))),
      a ∘ₗ b = g ^ k • LinearMap.id := by
  let : Module (A ⧸ Ideal.span {f}) M :=
    Module.IsTorsionBy.module (R := A) (M := M) (r := f) (fun ⦃x⦄ => hfM x)
  have : IsScalarTower A (A ⧸ Ideal.span {f}) M := inferInstance
  exact exists_pow_smul_factor_through_baseQuotient f g M hfree

/-- **A power of `g` factors through a finite free module over `A ⧸ (f)`**, in the form the
caller wants: `M` is a finite `A`-module on which `f` acts as zero, and for every prime `p` of
`A` containing `f` and avoiding `g` the localization of `M` at `p` is free over the localization
of `B = A ⧸ (f)` at `p`, the latter being `B` localized at the prime `q = pB` of `B`
corresponding to `p`. -/
theorem exists_pow_smul_factor_through_baseQuotient'
    {A : Type u} [CommRing A] [IsNoetherianRing A] (f g : A)
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (hfM : ∀ x : M, f • x = 0)
    (hfree : letI : Module (A ⧸ Ideal.span {f}) M :=
        Module.IsTorsionBy.module (R := A) (M := M) (r := f) (fun ⦃x⦄ => hfM x)
      ∀ (p : Ideal A) [p.IsPrime] (q : Ideal (A ⧸ Ideal.span {f})) [q.IsPrime],
        q = p.map (Ideal.Quotient.mk (Ideal.span {f})) → g ∉ p → f ∈ p →
        Module.Free (Localization.AtPrime q) (LocalizedModule q.primeCompl M)) :
    ∃ (k d : ℕ) (a : (Fin d → (A ⧸ Ideal.span {f})) →ₗ[A] M)
        (b : M →ₗ[A] (Fin d → (A ⧸ Ideal.span {f}))),
      a ∘ₗ b = g ^ k • LinearMap.id := by
  let : Module (A ⧸ Ideal.span {f}) M :=
    Module.IsTorsionBy.module (R := A) (M := M) (r := f) (fun ⦃x⦄ => hfM x)
  have : IsScalarTower A (A ⧸ Ideal.span {f}) M := inferInstance
  exact exists_pow_smul_factor_through_baseQuotient_of_primes f g M hfree

/-- Non-vacuity probe: the hypotheses are satisfiable, with `M = A ⧸ (f)` itself. -/
example {A : Type u} [CommRing A] [IsNoetherianRing A] (f g : A) :
    ∃ (k d : ℕ) (a : (Fin d → (A ⧸ Ideal.span {f})) →ₗ[A] (A ⧸ Ideal.span {f}))
        (b : (A ⧸ Ideal.span {f}) →ₗ[A] (Fin d → (A ⧸ Ideal.span {f}))),
      a ∘ₗ b = g ^ k • LinearMap.id := by
  refine exists_pow_smul_factor_through_baseQuotient_of_primes f g (A ⧸ Ideal.span {f})
    fun p q hq hgp hfp ↦ ?_
  infer_instance

end Stacks.BaseQuotientFactorization

end
