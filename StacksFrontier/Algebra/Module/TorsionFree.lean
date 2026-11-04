module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.LinearMap.Basic
public import Mathlib.Algebra.Module.LocalizedModule.AtPrime
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Finsupp.Pi
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.LocalProperties.Exactness
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
public import Mathlib.RingTheory.TotallySplit
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Serre.Defs

/-!
# Torsion-free modules

Torsion-freeness is preserved by flat base change of domains and by extensions, it may be checked
at the maximal ideals, and a finite module over a domain is torsion-free exactly when it embeds
into a finite free module. Over a Noetherian domain a nonzero finite module is torsion-free exactly
when its only associated prime is zero, exactly when it satisfies `(S₁)` with zero in its support.
Over a Dedekind domain a finite torsion-free module is projective.

## Main results

* `isTorsionFree_baseChange_of_flat`: the base change of a torsion-free module over a domain along
  a flat algebra is torsion-free.
* `isTorsionFree_of_injective_of_exact`: an extension of torsion-free modules is torsion-free.
* `isTorsionFree_iff_isLocalized_maximal`: a module over a domain is torsion-free exactly when its
  localizations at all maximal ideals are.
* `isTorsionFree_iff_exists_injective_to_finite_free`: a finite module over a domain is
  torsion-free exactly when it embeds into a finite free module.
* `isTorsionFree_iff_finiteFreeEmbedding_iff_associatedPrimes_iff_propertyS1`: the
  characterizations of torsion-freeness of a nonzero finite module over a Noetherian domain.
* `projective_of_finite_isTorsionFree`: a finite torsion-free module over a Dedekind domain is
  projective.

## References

* [Stacks Project, Tag 0AXM](https://stacks.math.columbia.edu/tag/0AXM)
* [Stacks Project, Tag 0AUS](https://stacks.math.columbia.edu/tag/0AUS)
* [Stacks Project, Tag 0AUT](https://stacks.math.columbia.edu/tag/0AUT)
* [Stacks Project, Tag 0AUU](https://stacks.math.columbia.edu/tag/0AUU)
* [Stacks Project, Tag 0AUV](https://stacks.math.columbia.edu/tag/0AUV)
* [Stacks Project, Tag 0AUW](https://stacks.math.columbia.edu/tag/0AUW)
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u v w x

/-- The localization map of a torsion-free module over a domain, at the nonzero elements, is
injective. -/
private lemma injective_of_isLocalizedModule_nonZeroDivisors
    {R : Type*} [CommRing R] [IsDomain R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.IsTorsionFree R M]
    {N : Type*} [AddCommGroup N] [Module R N] (f : M →ₗ[R] N)
    [IsLocalizedModule (nonZeroDivisors R) f] : Function.Injective f :=
  (IsLocalizedModule.injective_iff_isRegular _ f).2 fun c =>
    Module.IsTorsionFree.isSMulRegular (IsRegular.of_ne_zero (nonZeroDivisors.ne_zero c.2))

/-- If `R` is a domain, `R'` is a flat `R`-algebra and `M` is a torsion-free `R`-module, then the
base change `R' ⊗[R] M` is a torsion-free `R'`-module. -/
@[stacks 0AXM, ega "IV 9.4.9" "partial"]
theorem isTorsionFree_baseChange_of_flat
    {R R' : Type*} [CommRing R] [CommRing R'] [Algebra R R']
    [IsDomain R] [Module.Flat R R']
    {M : Type*} [AddCommGroup M] [Module R M] [Module.IsTorsionFree R M] :
    Module.IsTorsionFree R' (TensorProduct R R' M) := by
  set S := nonZeroDivisors R
  set N := LocalizedModule S M
  let f : M →ₗ[R] N := LocalizedModule.mkLinearMap S M
  have hf : Function.Injective f := injective_of_isLocalizedModule_nonZeroDivisors f
  have hNflat : Module.Flat R N :=
    Module.Flat.trans R (Localization S) N
  have hbinj : Function.Injective (LinearMap.baseChange R' f) :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := R') f hf
  refine ⟨fun r hr x y hxy => hbinj ?_⟩
  refine Module.IsTorsionFree.isSMulRegular (M := TensorProduct R R' N) hr ?_
  simpa [map_smul] using congrArg (LinearMap.baseChange R' f) hxy

/-- For an injective exact pair of module maps, if the source and target modules are torsion-free,
then the middle module is torsion-free. -/
@[stacks 0AUS]
theorem isTorsionFree_of_injective_of_exact
    {R : Type u} [Semiring R]
    {M : Type v} {M' : Type w} {M'' : Type x}
    [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M']
    [AddCommGroup M''] [Module R M'']
    (f : M →ₗ[R] M') (g : M' →ₗ[R] M'')
    (hf : Function.Injective f) (hfg : Function.Exact f g)
    [Module.IsTorsionFree R M] [Module.IsTorsionFree R M''] :
    Module.IsTorsionFree R M' := by
  refine ⟨fun r hr y₁ y₂ hy ↦ ?_⟩
  have hgy : g y₁ = g y₂ := hr.isSMulRegular <| by
    simpa only [map_smul] using congrArg g hy
  have hdiff : g (y₁ - y₂) = 0 := by simp [hgy]
  obtain ⟨m, hm⟩ := (hfg (y₁ - y₂)).mp hdiff
  have hrm : r • m = 0 := hf <| by
    rw [map_zero, map_smul, hm, smul_sub]
    exact sub_eq_zero.mpr hy
  have hm0 : m = 0 := hr.smul_eq_zero_iff_right.mp hrm
  exact sub_eq_zero.mp <| by rw [← hm, hm0, map_zero]

/-! ### Detecting torsion-freeness after localization -/

/-- A module over a domain is torsion-free if and only if its localization at every maximal ideal
is torsion-free over the corresponding localized ring. -/
@[stacks 0AUT]
theorem isTorsionFree_iff_isLocalized_maximal
    {R : Type u} [CommRing R] [IsDomain R]
    {M : Type v} [AddCommMonoid M] [Module R M]
    (Rₚ : ∀ (P : Ideal R) [P.IsMaximal], Type w)
    [∀ (P : Ideal R) [P.IsMaximal], CommRing (Rₚ P)]
    [∀ (P : Ideal R) [P.IsMaximal], Algebra R (Rₚ P)]
    [∀ (P : Ideal R) [P.IsMaximal], IsLocalization.AtPrime (Rₚ P) P]
    (Mₚ : ∀ (P : Ideal R) [P.IsMaximal], Type x)
    [∀ (P : Ideal R) [P.IsMaximal], AddCommMonoid (Mₚ P)]
    [∀ (P : Ideal R) [P.IsMaximal], Module R (Mₚ P)]
    [∀ (P : Ideal R) [P.IsMaximal], Module (Rₚ P) (Mₚ P)]
    [∀ (P : Ideal R) [P.IsMaximal], IsScalarTower R (Rₚ P) (Mₚ P)]
    (f : ∀ (P : Ideal R) [P.IsMaximal], M →ₗ[R] Mₚ P)
    [∀ (P : Ideal R) [P.IsMaximal], IsLocalizedModule.AtPrime P (f P)] :
    Module.IsTorsionFree R M ↔
      ∀ (P : Ideal R) [P.IsMaximal], Module.IsTorsionFree (Rₚ P) (Mₚ P) := by
  constructor
  · intro h P _
    let := h
    exact IsLocalizedModule.isTorsionFree (f P) P.primeCompl
  · intro h
    constructor
    intro r hr m m' hmm'
    apply Module.eq_of_localization_maximal Mₚ f
    intro P _
    let := IsLocalization.isDomain_of_atPrime (Rₚ P) P
    let : Module.IsTorsionFree (Rₚ P) (Mₚ P) := h P
    have hr' : IsRegular (algebraMap R (Rₚ P) r) := isRegular_iff_ne_zero.mpr <| by
      simpa using
        (IsLocalization.injective (Rₚ P) P.primeCompl_le_nonZeroDivisors).ne hr.ne_zero
    apply hr'.isSMulRegular
    show algebraMap R (Rₚ P) r • f P m = algebraMap R (Rₚ P) r • f P m'
    rw [IsScalarTower.algebraMap_smul, IsScalarTower.algebraMap_smul]
    simpa only [map_smul] using congrArg (f P) hmm'

/-! ### Finite torsion-free modules embed into finite free modules -/

/-- A finite torsion-free module over a domain admits an injective linear map into a finite product
of copies of the ring. -/
private lemma exists_injective_to_finite_pi
    {R : Type u} [CommRing R] [IsDomain R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.IsTorsionFree R M] :
    ∃ (ι : Type (max u v)), Finite ι ∧
      ∃ f : M →ₗ[R] (ι → R), Function.Injective f := by
  let S := nonZeroDivisors R
  let K := FractionRing R
  let L := LocalizedModule S M
  let q : M →ₗ[R] L := LocalizedModule.mkLinearMap S M
  let ι := Module.Free.ChooseBasisIndex K L
  let B := Module.Free.chooseBasis K L
  let e : L ≃ₗ[K] (ι → K) :=
    B.repr ≪≫ₗ Finsupp.linearEquivFunOnFinite K K ι
  let g : M →ₗ[R] (ι → K) := e.toLinearMap.restrictScalars R ∘ₗ q
  have hg : Function.Injective g :=
    e.injective.comp (injective_of_isLocalizedModule_nonZeroDivisors q)
  let a : R →ₗ[R] K := Algebra.linearMap R K
  let j : (ι → R) →ₗ[R] (ι → K) :=
    LinearMap.pi fun i ↦ a ∘ₗ LinearMap.proj i
  have : IsLocalizedModule S j := inferInstance
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' R M
  obtain ⟨h, s, hs⟩ :=
    Module.FinitePresentation.exists_lift_of_isLocalizedModule S j (g ∘ₗ p)
  have hj : Function.Injective j := injective_of_isLocalizedModule_nonZeroDivisors j
  have hker : LinearMap.ker p ≤ LinearMap.ker h := fun x hx ↦ by
    rw [LinearMap.mem_ker] at hx ⊢
    exact hj (by simpa [hx] using LinearMap.congr_fun hs x)
  let h' : M →ₗ[R] (ι → R) :=
    Submodule.liftQ (LinearMap.ker p) h hker ∘ₗ
      (p.quotKerEquivOfSurjective hp).symm.toLinearMap
  have hcomm : j ∘ₗ h' = s • g := LinearMap.ext fun x ↦ by
    obtain ⟨x, rfl⟩ := hp x
    simpa [h', LinearMap.quotKerEquivOfSurjective_symm_apply] using LinearMap.congr_fun hs x
  refine ⟨ι, inferInstance, h', fun x y hxy ↦ hg ?_⟩
  exact (isRegular_iff_mem_nonZeroDivisors.mpr s.property).isSMulRegular <|
    (LinearMap.congr_fun hcomm x).symm.trans ((congr_arg j hxy).trans (LinearMap.congr_fun hcomm y))

/-- A finite module over a domain is torsion-free if and only if it embeds into a finite free
module. -/
@[stacks 0AUU]
theorem isTorsionFree_iff_exists_injective_to_finite_free
    {R : Type u} [CommRing R] [IsDomain R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Module.IsTorsionFree R M ↔
      ∃ N : ModuleCat.{max u v} R,
        Module.Finite R N ∧ Module.Free R N ∧
          ∃ f : M →ₗ[R] N, Function.Injective f := by
  constructor
  · intro h
    let := h
    obtain ⟨ι, hι, f, hf⟩ := exists_injective_to_finite_pi (R := R) (M := M)
    let := hι
    exact ⟨ModuleCat.of R (ι → R), inferInstance, inferInstance, f, hf⟩
  · rintro ⟨N, _, _, f, hf⟩
    exact hf.moduleIsTorsionFree f (fun r m ↦ f.map_smul r m)

/-! ### Characterizations over a Noetherian domain

For a nonzero finite module over a Noetherian domain, torsion-freeness coincides with embeddability
into a finite free module, with the associated primes reducing to the zero ideal, with Serre's
condition `(S₁)`, and with the absence of embedded associated primes. Property `(S₁)` is written
using the depth and support-dimension inequality at every prime, with the same conventions as
Stacks Project, Tag 031Q. -/

/-- Over a Noetherian domain a nonzero module is torsion-free exactly when the zero ideal is its
only associated prime. -/
private theorem isTorsionFree_iff_associatedPrimes_eq_singleton_bot
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Nontrivial M] :
    Module.IsTorsionFree R M ↔ associatedPrimes R M = {⊥} := by
  rw [Module.isTorsionFree_iff_smul_eq_zero]
  constructor
  · intro h
    have heq (p) (hp : p ∈ associatedPrimes R M) : p = ⊥ := le_bot_iff.mp fun r hr ↦ by
      obtain ⟨x, hx, hrx⟩ : r ∈ {r : R | ∃ x : M, x ≠ 0 ∧ r • x = 0} := by
        rw [← biUnion_associatedPrimes_eq_zero_divisors R M]
        exact Set.mem_iUnion₂_of_mem hp hr
      simpa using (h r x hrx).resolve_right hx
    ext p
    refine ⟨fun hp ↦ by simp [heq p hp], fun hp ↦ ?_⟩
    obtain ⟨q, hq⟩ := associatedPrimes.nonempty R M
    simpa [Set.mem_singleton_iff.mp hp, heq q hq] using hq
  · intro hass r x hrx
    refine or_iff_not_imp_right.mpr fun hx ↦ ?_
    have hr : r ∈ ⋃ p ∈ associatedPrimes R M, (p : Set R) := by
      rw [biUnion_associatedPrimes_eq_zero_divisors R M]
      exact ⟨x, hx, hrx⟩
    simpa [hass] using hr

/-- Having the zero ideal as unique associated prime is the same as having zero in the support
together with no embedded associated prime, i.e. every associated prime being minimal. -/
private theorem associatedPrimes_eq_singleton_bot_iff_noEmbedded
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M] :
    associatedPrimes R M = {⊥} ↔
      (⊥ : PrimeSpectrum R) ∈ Module.support R M ∧
        ∀ p ∈ associatedPrimes R M, Minimal (· ∈ associatedPrimes R M) p := by
  constructor
  · intro hass
    have hbot : (⊥ : Ideal R) ∈ associatedPrimes R M := by simp [hass]
    refine ⟨Module.mem_support_iff_of_finite.mpr ?_, ?_⟩
    · rw [← Submodule.annihilator_top]
      exact (AssociatedPrimes.mem_iff.mp hbot).annihilator_le
    intro p hp
    simpa [hass] using hp
  · rintro ⟨hbotSupport, hmin⟩
    have hann : Module.annihilator R M = ⊥ :=
      le_antisymm (Module.mem_support_iff_of_finite.mp hbotSupport) bot_le
    have hbot : (⊥ : Ideal R) ∈ associatedPrimes R M := by
      apply Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes R M
      rw [hann]
      show (⊥ : Ideal R) ∈ minimalPrimes R
      rw [IsDomain.minimalPrimes_eq_singleton_bot]
      simp
    ext p
    refine ⟨fun hp ↦ le_bot_iff.mp ((hmin p hp).le_of_le hbot bot_le), fun hp ↦ ?_⟩
    rwa [Set.mem_singleton_iff.mp hp]

/-- For a nonzero finite module over a Noetherian domain, the following are equivalent: it is
torsion-free; it embeds into a finite free module; its only associated prime is zero; zero lies in
its support and it satisfies `(S₁)`; and zero lies in its support and it has no embedded associated
prime. -/
@[stacks 0AUV]
theorem isTorsionFree_iff_finiteFreeEmbedding_iff_associatedPrimes_iff_propertyS1
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M] :
    (Module.IsTorsionFree R M ↔
      ∃ N : ModuleCat.{max u v} R,
        Module.Finite R N ∧ Module.Free R N ∧
          ∃ f : M →ₗ[R] N, Function.Injective f) ∧
    ((∃ N : ModuleCat.{max u v} R,
        Module.Finite R N ∧ Module.Free R N ∧
          ∃ f : M →ₗ[R] N, Function.Injective f) ↔
      associatedPrimes R M = {⊥}) ∧
    (associatedPrimes R M = {⊥} ↔
      (⊥ : PrimeSpectrum R) ∈ Module.support R M ∧
        ∀ p : PrimeSpectrum R,
          min 1 (Module.supportDim (Localization.AtPrime p.asIdeal)
              (LocalizedModule p.asIdeal.primeCompl M)) ≤
            (Module.depth (Localization.AtPrime p.asIdeal)
              (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
              (LocalizedModule p.asIdeal.primeCompl M) : WithBot ℕ∞)) ∧
    (((⊥ : PrimeSpectrum R) ∈ Module.support R M ∧
        ∀ p : PrimeSpectrum R,
          min 1 (Module.supportDim (Localization.AtPrime p.asIdeal)
              (LocalizedModule p.asIdeal.primeCompl M)) ≤
            (Module.depth (Localization.AtPrime p.asIdeal)
              (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
              (LocalizedModule p.asIdeal.primeCompl M) : WithBot ℕ∞)) ↔
      (⊥ : PrimeSpectrum R) ∈ Module.support R M ∧
        ∀ p ∈ associatedPrimes R M, Minimal (· ∈ associatedPrimes R M) p) := by
  let h₁₂ := isTorsionFree_iff_exists_injective_to_finite_free (R := R) (M := M)
  let h₁₃ := isTorsionFree_iff_associatedPrimes_eq_singleton_bot (R := R) (M := M)
  let h₃₅ := associatedPrimes_eq_singleton_bot_iff_noEmbedded (R := R) (M := M)
  let h₅₄ :
      ((⊥ : PrimeSpectrum R) ∈ Module.support R M ∧
          ∀ p ∈ associatedPrimes R M, Minimal (· ∈ associatedPrimes R M) p) ↔
        (⊥ : PrimeSpectrum R) ∈ Module.support R M ∧
          ∀ p : PrimeSpectrum R,
            min 1 (Module.supportDim (Localization.AtPrime p.asIdeal)
                (LocalizedModule p.asIdeal.primeCompl M)) ≤
              (Module.depth (Localization.AtPrime p.asIdeal)
                (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
                (LocalizedModule p.asIdeal.primeCompl M) : WithBot ℕ∞) :=
    and_congr Iff.rfl
      Module.forall_minimal_mem_associatedPrimes_iff_min_one_supportDim_le_depth
  exact ⟨h₁₂, h₁₂.symm.trans h₁₃,
    h₃₅.trans h₅₄, h₅₄.symm⟩

/-! ### Dedekind domains -/

/-- A finite torsion-free module over a Dedekind domain is projective, hence finite locally free.
-/
@[stacks 0AUW "(2)", ega "0 6.3.4" "finite, Dedekind domain"]
theorem projective_of_finite_isTorsionFree
    (R : Type u) [CommRing R] [IsDedekindDomain R]
    (M : Type v) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.IsTorsionFree R M] :
    Module.Projective R M := by
  let _ : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
  exact Module.Flat.projective_of_finitePresentation

/-! ### Results available in Mathlib

These are stated over a commutative semiring with regular scalars; over a domain the regular
scalars are the nonzero ones, by `Module.isTorsionFree_iff_smul_eq_zero`. -/

add_to_stacks 0536 "(1): torsion elements" Submodule.torsion
add_to_ega "I 7.4.1" "special case" Submodule.torsion
add_to_ega "I 7.4.7" "special case" Submodule.torsion
add_to_stacks 0536 "(2): torsion-free modules" Module.IsTorsionFree
add_to_sga "7 X 2.26" Module.IsTorsionFree
add_to_ega "I 7.4.1" "special case" Module.IsTorsionFree
add_to_ega "I 7.4.7" "special case" Module.IsTorsionFree
add_to_stacks 0536 "(3): torsion modules" Module.IsTorsion
add_to_ega "I 7.4.1" "special case" Module.IsTorsion
add_to_ega "I 7.4.7" "special case" Module.IsTorsion

add_to_stacks 0537 "the torsion submodule" Submodule.torsion
add_to_stacks 0537 "its elements are exactly the torsion elements" Submodule.mem_torsion_iff
add_to_stacks 0537 "the quotient by the torsion submodule is torsion-free"
  Submodule.QuotientTorsion.instIsTorsionFree
add_to_sga "7 I 1.3" "partial" Submodule.QuotientTorsion.instIsTorsionFree
add_to_ega "I 7.4.1" "special case" Submodule.QuotientTorsion.instIsTorsionFree

add_to_stacks 0538 Module.Flat.isTorsionFree
add_to_sga "1 IV 1.3" "more general" Module.Flat.isTorsionFree
add_to_sga "3 XV 4.7" "partial" Module.Flat.isTorsionFree
add_to_ega "0 6.3.4" "more general" Module.Flat.isTorsionFree
add_to_ega "IV 20.1.5" "special case" Module.Flat.isTorsionFree
add_to_ega "IV 21.5.3" "partial" Module.Flat.isTorsionFree

add_to_stacks 0539 "the bridge from trivial torsion submodule to torsion-freeness"
  Submodule.isTorsionFree_iff_torsion_eq_bot
add_to_ega "I 7.4.1" "special case" Submodule.isTorsionFree_iff_torsion_eq_bot

add_to_stacks 0AUR IsLocalizedModule.isTorsionFree

add_to_stacks 0AUW "(1), trivial torsion versus torsion-freeness"
  Submodule.isTorsionFree_iff_torsion_eq_bot
add_to_stacks 0AUW "(3), finite torsion-free modules over a PID are finite free"
  Module.free_iff_isTorsionFree
add_to_sga "6 IX 1.7" "more general" Module.free_iff_isTorsionFree
add_to_ega "0 6.3.4" "more general" Module.free_iff_isTorsionFree

add_to_stacks 0AUX "the semilinear form specializes to linear maps over a domain"
  LinearMap.instIsTorsionFree
