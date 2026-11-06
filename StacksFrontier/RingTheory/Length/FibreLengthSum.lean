module

public import StacksFrontier.RingTheory.Length.PrimeResidueDegree
public import StacksFrontier.RingTheory.Localization.LocalizedModuleTwoStep
public import StacksFrontier.RingTheory.Length.SemilocalDecomposition
public import StacksFrontier.RingTheory.Length.LocalizationModelIndependence
public import StacksFrontier.RingTheory.Length.Comparison
public import StacksFrontier.RingTheory.Support.FiniteDimensional

/-!
# Length of a localized module over a finite algebra, as a sum over the fibre

Let `A` be a Noetherian ring, `B` a finite `A`-algebra, `p` a prime of `A` and `N` a finite
`B`-module. Suppose that every prime `Q` in the support of `N` with `Q ∩ A ⊆ p` lies over `p`.
Then `N_p` has finite length over `A_p`, and

`length_{A_p}(N_p) = ∑_{Q ∩ A = p} [κ(Q) : κ(p)] · length_{B_Q}(N_Q)`.

## Main results

* `Stacks.Length.length_localizedModule_eq_finsum_fibre`: the formula above.
* `Stacks.Length.length_localizedModule_ne_top_of_fibre`: `N_p` has finite length over `A_p`.

## Implementation notes

Write `Bₚ` for the localization of `B` at the image of `A ∖ p`, a finite algebra over the local
ring `A_p`, and `Nₚ` for the corresponding localization of `N`. A prime of `Bₚ` in the support of
`Nₚ` contracts to a prime of `B` in the support of `N` over a prime contained in `p`, hence over
`p`, so it is maximal; therefore `Nₚ` has finite length over `Bₚ`. Stacks 02M0,
`Stacks.Length.length_eq_sum_finrank_mul_length_localizedModule`, applied to `A_p → Bₚ` and
`Nₚ`, writes the length as a sum over the maximal ideals of `Bₚ`, which correspond to the primes
of `B` over `p` by contraction. The terms are matched through the two-step localizations: the
composite `N → Nₚ → (Nₚ)_𝔮` is a localization of `N` at the contraction of `𝔮`, as a composite
of two base changes, and `IsLocalization.localizationLocalizationAtPrimeIsoLocalization`
identifies the local rings, hence the residue fields over `κ(p)`.

`Nₚ` carries no native `A_p`-action; it is given the one restricted from `Bₚ`, and
`Module.length_eq_of_isLocalization_of_isLocalizedModule` compares it with the formal
localization `LocalizedModule p.primeCompl N`.
-/

@[expose] public section

universe u

namespace Stacks.Length

open IsLocalRing

section TwoStep

variable {B : Type*} [CommRing B] (T : Submonoid B) (N : Type*) [AddCommGroup N] [Module B N]

/-- The length of `(T⁻¹N)_P` over `(T⁻¹B)_P` is the length of `N_Q` over `B_Q`, where `Q` is the
contraction of the prime `P` of `T⁻¹B` to `B`. -/
theorem length_localizedModule_localizedModule (P : Ideal (Localization T)) [P.IsPrime] :
    Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl (LocalizedModule T N)) =
      Module.length (Localization.AtPrime (P.comap (algebraMap B (Localization T))))
        (LocalizedModule (P.comap (algebraMap B (Localization T))).primeCompl N) :=
  have := Stacks.isLocalizedModule_comp_mkLinearMap T N P
  (Module.length_eq_of_isLocalization_of_isLocalizedModule _ (Localization.AtPrime P)
    (((LocalizedModule.mkLinearMap P.primeCompl (LocalizedModule T N)).restrictScalars B).comp
        (LocalizedModule.mkLinearMap T N))).symm

end TwoStep

section Fibre

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B]
  (p : Ideal A) [p.IsPrime]

local notation "Sₚ" => Algebra.algebraMapSubmonoid B p.primeCompl
local notation "Bₚ" => Localization (Algebra.algebraMapSubmonoid B p.primeCompl)

/-- A prime of `Bₚ` contracting to `p` in `A` is maximal: its contraction to the local ring
`A_p` is the maximal ideal, and `Bₚ` is integral over `A_p`. -/
theorem isMaximal_of_comap_comap_eq (P : Ideal Bₚ) [P.IsPrime]
    (h : (P.comap (algebraMap B Bₚ)).comap (algebraMap A B) = p) : P.IsMaximal := by
  have : Algebra.IsIntegral (Localization.AtPrime p) Bₚ := Algebra.IsIntegral.of_finite _ _
  apply Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := Localization.AtPrime p)
  have hJ : (P.comap (algebraMap (Localization.AtPrime p) Bₚ)).comap
      (algebraMap A (Localization.AtPrime p)) = p := by
    rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq A B Bₚ,
      ← Ideal.comap_comap, h]
  rw [Ideal.under, ← IsLocalization.map_under p.primeCompl (Localization.AtPrime p)
    (P.comap (algebraMap (Localization.AtPrime p) Bₚ)), Ideal.under, hJ,
    IsLocalization.AtPrime.map_eq_maximalIdeal]
  infer_instance

/-- A maximal ideal of `Bₚ` contracts to `p` in `A`. -/
theorem comap_comap_asIdeal_eq (q : MaximalSpectrum Bₚ) :
    (q.asIdeal.comap (algebraMap B Bₚ)).comap (algebraMap A B) = p := by
  rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq A B Bₚ,
    IsScalarTower.algebraMap_eq A (Localization.AtPrime p) Bₚ, ← Ideal.comap_comap,
    comap_asIdeal_eq_maximalIdeal q]
  exact IsLocalization.AtPrime.under_maximalIdeal (Localization.AtPrime p) p

omit [Module.Finite A B] in
/-- The residue degree of a maximal ideal `q` of `Bₚ` over the local ring `A_p` is the residue
degree `[κ(Q) : κ(p)]` of its contraction `Q` to `B`: the local rings `(Bₚ)_q` and `B_Q` are
identified over `A_p`, hence so are the residue fields over `κ(p)`. -/
theorem finrank_residueField_eq_primeResidueDegree (q : Ideal Bₚ) [q.IsMaximal]
    [IsLocalHom (algebraMap (Localization.AtPrime p) (Localization.AtPrime q))]
    (h : p = (q.comap (algebraMap B Bₚ)).comap (algebraMap A B)) :
    Module.finrank (ResidueField (Localization.AtPrime p))
        (ResidueField (Localization.AtPrime q)) =
      primeResidueDegree (algebraMap A B) p (q.comap (algebraMap B Bₚ)) := by
  rw [primeResidueDegree_of_eq _ _ _ h]
  let := (Ideal.ResidueField.map p (q.comap (algebraMap B Bₚ)) (algebraMap A B) h).toAlgebra
  let e := IsLocalization.localizationLocalizationAtPrimeIsoLocalization Sₚ q
  have he : e.toRingHom.comp (Localization.localRingHom p (q.comap (algebraMap B Bₚ))
      (algebraMap A B) h) = algebraMap (Localization.AtPrime p) (Localization.AtPrime q) := by
    apply IsLocalization.ringHom_ext p.primeCompl
    ext a
    simp only [RingHom.comp_apply, Localization.localRingHom_to_map]
    rw [← IsScalarTower.algebraMap_apply A (Localization.AtPrime p) (Localization.AtPrime q),
      IsScalarTower.algebraMap_apply A B (Localization.AtPrime q)]
    exact e.commutes (algebraMap A B a)
  symm
  refine Algebra.finrank_eq_of_equiv_equiv (RingEquiv.refl _)
    (ResidueField.mapEquiv e.toRingEquiv) (RingHom.ext fun x => ?_)
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective (R := Localization.AtPrime p) x
  show residue _ (algebraMap (Localization.AtPrime p) (Localization.AtPrime q) x) =
    ResidueField.map (e.toRingEquiv : Localization.AtPrime (q.comap (algebraMap B Bₚ)) →+*
        Localization.AtPrime q)
      (ResidueField.map (Localization.localRingHom p (q.comap (algebraMap B Bₚ))
        (algebraMap A B) h) (residue _ x))
  rw [ResidueField.map_residue, ResidueField.map_residue, ← he]
  rfl

/-- The maximal ideals of `Bₚ` correspond, by contraction, to the primes of `B` over `p`. -/
theorem image_comap_maximalSpectrum :
    (fun q : MaximalSpectrum Bₚ =>
      (⟨q.asIdeal.comap (algebraMap B Bₚ), inferInstance⟩ : PrimeSpectrum B)) '' Set.univ =
      {Q : PrimeSpectrum B | Q.asIdeal.comap (algebraMap A B) = p} := by
  ext Q
  refine ⟨fun ⟨q, _, hq⟩ => hq ▸ comap_comap_asIdeal_eq p q, fun hQ => ?_⟩
  have hdisj : Disjoint (Sₚ : Set B) Q.asIdeal := by
    rw [Set.disjoint_left]
    rintro _ ⟨a, ha, rfl⟩ haQ
    exact ha (hQ ▸ (Ideal.mem_comap.mpr haQ))
  have := IsLocalization.isPrime_of_isPrime_disjoint Sₚ Bₚ Q.asIdeal Q.isPrime hdisj
  have hcomap := IsLocalization.under_map_of_isPrime_disjoint Sₚ Bₚ Q.isPrime hdisj
  have hmax : (Q.asIdeal.map (algebraMap B Bₚ)).IsMaximal :=
    isMaximal_of_comap_comap_eq p _ (by rw [Ideal.under] at hcomap; rw [hcomap, hQ])
  exact ⟨⟨_, hmax⟩, trivial, PrimeSpectrum.ext hcomap⟩

omit [Module.Finite A B] in
/-- Contraction from `Bₚ` to `B` is injective on maximal ideals. -/
theorem injOn_comap_maximalSpectrum :
    Set.InjOn (fun q : MaximalSpectrum Bₚ =>
      (⟨q.asIdeal.comap (algebraMap B Bₚ), inferInstance⟩ : PrimeSpectrum B)) Set.univ := by
  intro q₁ _ q₂ _ h
  refine MaximalSpectrum.ext ?_
  rw [← IsLocalization.map_under Sₚ Bₚ q₁.asIdeal, ← IsLocalization.map_under Sₚ Bₚ q₂.asIdeal]
  exact congrArg (Ideal.map (algebraMap B Bₚ)) (congrArg PrimeSpectrum.asIdeal h)

variable {p} {N : Type u} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]

local notation "Nₚ" => LocalizedModule (Algebra.algebraMapSubmonoid B p.primeCompl) N

omit [Module A N] [IsScalarTower A B N] in
/-- A prime of `Bₚ` in the support of `Nₚ` is maximal, provided every prime of `B` in the
support of `N` lying over a prime contained in `p` lies over `p`. -/
theorem isMaximal_of_mem_support
    (hsupp : ∀ Q : PrimeSpectrum B, Q ∈ Module.support B N →
      Q.asIdeal.comap (algebraMap A B) ≤ p → Q.asIdeal.comap (algebraMap A B) = p)
    (P : PrimeSpectrum Bₚ) (hP : P ∈ Module.support Bₚ Nₚ) : P.asIdeal.IsMaximal := by
  set Q : PrimeSpectrum B := ⟨P.asIdeal.comap (algebraMap B Bₚ), inferInstance⟩
  have hQ : Q ∈ Module.support B N := by
    rw [Module.mem_support_iff] at hP ⊢
    have := Stacks.isLocalizedModule_comp_mkLinearMap Sₚ N P.asIdeal
    exact (IsLocalizedModule.iso (P.asIdeal.comap (algebraMap B Bₚ)).primeCompl
      (((LocalizedModule.mkLinearMap P.asIdeal.primeCompl Nₚ).restrictScalars B).comp
        (LocalizedModule.mkLinearMap Sₚ N))).toEquiv.nontrivial
  have hle : Q.asIdeal.comap (algebraMap A B) ≤ p := by
    intro a ha
    by_contra hap
    have hu : IsUnit (algebraMap B Bₚ (algebraMap A B a)) :=
      IsLocalization.map_units Bₚ (⟨algebraMap A B a, a, hap, rfl⟩ : Sₚ)
    exact P.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ ha hu)
  exact isMaximal_of_comap_comap_eq p P.asIdeal (hsupp Q hQ hle)

omit [Module A N] [IsScalarTower A B N] in
/-- Under the support hypothesis, `Nₚ` has finite length over `Bₚ`: its support is contained in
the finitely many maximal ideals of `Bₚ`. -/
theorem isFiniteLength_localizedModule [IsNoetherianRing A] [Module.Finite B N]
    (hsupp : ∀ Q : PrimeSpectrum B, Q ∈ Module.support B N →
      Q.asIdeal.comap (algebraMap A B) ≤ p → Q.asIdeal.comap (algebraMap A B) = p) :
    IsFiniteLength Bₚ Nₚ := by
  have : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  have : IsNoetherianRing Bₚ := IsLocalization.isNoetherianRing Sₚ Bₚ inferInstance
  have : Finite (MaximalSpectrum Bₚ) := finite_maximalSpectrum (A := Localization.AtPrime p)
  rw [Module.isFiniteLength_iff_support_finite_subset_closedPoints]
  exact ⟨(Set.finite_range (fun q : MaximalSpectrum Bₚ => q.toPrimeSpectrum)).subset
    fun P hP => ⟨⟨P.asIdeal, isMaximal_of_mem_support hsupp P hP⟩, rfl⟩,
    fun P hP => (PrimeSpectrum.isClosed_singleton_iff_isMaximal P).mpr
      (isMaximal_of_mem_support hsupp P hP)⟩

/-- **Stacks 02M0 over `A_p → Bₚ`.** Under the support hypothesis, the `A_p`-length of `N_p` is
the sum over the maximal ideals `q` of `Bₚ` of `[κ(q) : κ(p)] · length_{(Bₚ)_q}((Nₚ)_q)`, each
of the lengths being finite. -/
theorem length_localizedModule_eq_sum_maximalSpectrum [IsNoetherianRing A] [Module.Finite B N]
    (hsupp : ∀ Q : PrimeSpectrum B, Q ∈ Module.support B N →
      Q.asIdeal.comap (algebraMap A B) ≤ p → Q.asIdeal.comap (algebraMap A B) = p)
    [Fintype (MaximalSpectrum Bₚ)]
    [∀ q : MaximalSpectrum Bₚ,
      IsLocalHom (algebraMap (Localization.AtPrime p) (Localization.AtPrime q.asIdeal))] :
    (∀ q : MaximalSpectrum Bₚ, Module.length (Localization.AtPrime q.asIdeal)
      (LocalizedModule q.asIdeal.primeCompl Nₚ) ≠ ⊤) ∧
    Module.length (Localization.AtPrime p) (LocalizedModule p.primeCompl N) =
      ∑ q : MaximalSpectrum Bₚ,
        (Module.finrank (ResidueField (Localization.AtPrime p))
            (ResidueField (Localization.AtPrime q.asIdeal)) : ℕ∞) *
          Module.length (Localization.AtPrime q.asIdeal)
            (LocalizedModule q.asIdeal.primeCompl Nₚ) := by
  let : Module (Localization.AtPrime p) Nₚ :=
    Module.compHom Nₚ (algebraMap (Localization.AtPrime p) Bₚ)
  have : IsScalarTower (Localization.AtPrime p) Bₚ Nₚ :=
    ⟨fun x y n => by
      show (x • y) • n = algebraMap _ Bₚ x • y • n
      rw [Algebra.smul_def, mul_smul]⟩
  have : IsScalarTower A (Localization.AtPrime p) Nₚ :=
    ⟨fun a x n => by
      show algebraMap _ Bₚ (a • x) • n = a • algebraMap _ Bₚ x • n
      rw [Algebra.smul_def, map_mul, mul_smul,
        ← IsScalarTower.algebraMap_apply A (Localization.AtPrime p) Bₚ a,
        IsScalarTower.algebraMap_apply A B Bₚ a, algebraMap_smul, algebraMap_smul]⟩
  have hfl := isFiniteLength_localizedModule hsupp
  have : IsArtinian Bₚ Nₚ := (isFiniteLength_iff_isNoetherian_isArtinian.mp hfl).2
  have hfin : ∀ q : MaximalSpectrum Bₚ, Module.length (Localization.AtPrime q.asIdeal)
      (LocalizedModule q.asIdeal.primeCompl Nₚ) ≠ ⊤ := fun q =>
    ne_top_of_le_ne_top (Module.length_ne_top_iff.mpr hfl)
      (Module.length_localizedModule_le q.asIdeal.primeCompl)
  have := IsLocalizedModule.restrictScalars p.primeCompl (LocalizedModule.mkLinearMap Sₚ N)
  refine ⟨hfin, ?_⟩
  rw [Module.length_eq_of_isLocalization_of_isLocalizedModule p.primeCompl
      (Localization.AtPrime p) ((LocalizedModule.mkLinearMap Sₚ N).restrictScalars A)]
  exact length_eq_sum_finrank_mul_length_localizedModule (A := Localization.AtPrime p) Nₚ hfin

end Fibre

/-- **The length of a localized module over a finite algebra, as a sum over the fibre.** Let
`A` be Noetherian, `B` a finite `A`-algebra, `p` a prime of `A` and `N` a finite `B`-module
such that every prime of `B` in the support of `N` lying over a prime contained in `p` lies over
`p`. Then `length_{A_p}(N_p) = ∑_{Q ∩ A = p} [κ(Q) : κ(p)] · length_{B_Q}(N_Q)`. -/
theorem length_localizedModule_eq_finsum_fibre {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] [Module.Finite A B] [IsNoetherianRing A]
    (p : Ideal A) [p.IsPrime] (N : Type u) [AddCommGroup N] [Module B N] [Module A N]
    [IsScalarTower A B N] [Module.Finite B N]
    (hsupp : ∀ Q : PrimeSpectrum B, Q ∈ Module.support B N →
      Q.asIdeal.comap (algebraMap A B) ≤ p → Q.asIdeal.comap (algebraMap A B) = p) :
    Module.length (Localization.AtPrime p) (LocalizedModule p.primeCompl N) =
      ∑ᶠ Q ∈ {Q : PrimeSpectrum B | Q.asIdeal.comap (algebraMap A B) = p},
        (primeResidueDegree (algebraMap A B) p Q.asIdeal : ℕ∞) *
          Module.length (Localization.AtPrime Q.asIdeal)
            (LocalizedModule Q.asIdeal.primeCompl N) := by
  classical
  have : Fintype (MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid B p.primeCompl))) :=
    @Fintype.ofFinite _ (finite_maximalSpectrum (A := Localization.AtPrime p))
  have : ∀ q : MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid B p.primeCompl)),
      IsLocalHom (algebraMap (Localization.AtPrime p) (Localization.AtPrime q.asIdeal)) :=
    fun q => isLocalHom_algebraMap_localization q
  rw [(length_localizedModule_eq_sum_maximalSpectrum hsupp).2, ← image_comap_maximalSpectrum p,
    finsum_mem_image (injOn_comap_maximalSpectrum p), finsum_mem_univ, finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [length_localizedModule_localizedModule (Algebra.algebraMapSubmonoid B p.primeCompl) N
      q.asIdeal,
    finrank_residueField_eq_primeResidueDegree p q.asIdeal (comap_comap_asIdeal_eq p q).symm]

/-- Under the hypotheses of `Stacks.Length.length_localizedModule_eq_finsum_fibre`, the
localization `N_p` has finite length over `A_p`. -/
theorem length_localizedModule_ne_top_of_fibre {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] [Module.Finite A B] [IsNoetherianRing A]
    (p : Ideal A) [p.IsPrime] (N : Type u) [AddCommGroup N] [Module B N] [Module A N]
    [IsScalarTower A B N] [Module.Finite B N]
    (hsupp : ∀ Q : PrimeSpectrum B, Q ∈ Module.support B N →
      Q.asIdeal.comap (algebraMap A B) ≤ p → Q.asIdeal.comap (algebraMap A B) = p) :
    Module.length (Localization.AtPrime p) (LocalizedModule p.primeCompl N) ≠ ⊤ := by
  classical
  have : Fintype (MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid B p.primeCompl))) :=
    @Fintype.ofFinite _ (finite_maximalSpectrum (A := Localization.AtPrime p))
  have : ∀ q : MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid B p.primeCompl)),
      IsLocalHom (algebraMap (Localization.AtPrime p) (Localization.AtPrime q.asIdeal)) :=
    fun q => isLocalHom_algebraMap_localization q
  obtain ⟨hfin, h⟩ := length_localizedModule_eq_sum_maximalSpectrum hsupp
  rw [h]
  exact WithTop.sum_ne_top.mpr fun q _ => WithTop.mul_ne_top (ENat.natCast_ne_top _) (hfin q)

end Stacks.Length

end
