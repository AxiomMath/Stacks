module

public import StacksCore.RingTheory.Support
public import StacksFrontier.RingTheory.Flat.Localization
public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.RingTheory.LocalProperties.FinitePresentation
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

universe u v

/-!
# Finite projective modules are exactly the finite locally free ones

Let `R` be a commutative ring and `M` an `R`-module. This file proves the equivalence of the eight
conditions of Stacks 00NX: `M` finitely presented and flat, `M` finite projective, `M` a direct
summand of a finite free module, `M` finitely presented and free at every prime, resp. at every
maximal ideal, `M` finite and locally free, `M` finite locally free, and `M` finite with free
localizations and locally constant rank function.

## Main results

* `Stacks.LocallyFree.FiniteProjective.solution`: the eight conditions of Stacks 00NX are
  equivalent.

## References

* [StacksProject 00NX](https://stacks.math.columbia.edu/tag/00NX)
-/


namespace Stacks.LocallyFree.FiniteProjective

open Module PrimeSpectrum



variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- A ring possessing a maximal ideal is nontrivial. -/
public theorem nontrivial_of_isMaximal {J : Ideal R} (hJ : J.IsMaximal) : Nontrivial R := by
  rcases subsingleton_or_nontrivial R with h | h
  · exact absurd (Subsingleton.elim J ⊤) hJ.ne_top
  · exact h

/-- A property of ring elements that holds at some element outside every maximal ideal holds on a
set of elements generating the unit ideal. -/
public theorem exists_span_eq_top_of_forall_maximal (P : R → Prop)
    (h : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → ∃ g ∉ 𝔪, P g) :
    ∃ s : Set R, Ideal.span s = ⊤ ∧ ∀ g ∈ s, P g := by
  refine ⟨{g | P g}, ?_, fun _ hg ↦ hg⟩
  by_contra hne
  obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨g, hg, hPg⟩ := h 𝔪 h𝔪
  exact hg (hle (Ideal.subset_span hPg))

/-- A set spanning the localization of `M` at the powers of `a` also spans the localization at the
powers of `a * b`. -/
private theorem span_image_mkLinearMap_away_mul (a b : R) (s : Set M)
    (h : Submodule.span (Localization.Away a)
      (LocalizedModule.mkLinearMap (Submonoid.powers a) M '' s) = ⊤) :
    Submodule.span (Localization.Away (a * b))
      (LocalizedModule.mkLinearMap (Submonoid.powers (a * b)) M '' s) = ⊤ := by
  rw [Submodule.span_image_eq_top_iff _ (Submonoid.powers a) _ s] at h
  rw [Submodule.span_image_eq_top_iff _ (Submonoid.powers (a * b)) _ s]
  intro m
  obtain ⟨t, ht⟩ := h m
  obtain ⟨n, hn⟩ := t.2
  have hn' : (a : R) ^ n = (t : R) := hn
  refine ⟨⟨(a * b) ^ n, n, rfl⟩, ?_⟩
  change ((a * b) ^ n : R) • m ∈ _
  rw [mul_pow, mul_comm, mul_smul, hn']
  exact Submodule.smul_mem _ _ ht

/-- If `x₁, …, x_r` generate `M_h` and the rank of `M` is constant equal to `r` on `D(h)`, then
`M_h` is free over `R_h`. -/
private theorem free_localizedModule_away_of_span_eq_top [Module.Finite R M] [Module.Flat R M]
    {r : ℕ} {h : R} (x : Fin r → M)
    (hspan : Submodule.span (Localization.Away h)
      (LocalizedModule.mkLinearMap (Submonoid.powers h) M '' Set.range x) = ⊤)
    (hrank : ∀ q : PrimeSpectrum R, h ∉ q.asIdeal → rankAtStalk (R := R) M q = r) :
    Module.Free (Localization.Away h) (LocalizedModule.Away h M) := by
  set S := Submonoid.powers h with hS
  set R' := Localization.Away h
  set M' := LocalizedModule.Away h M
  set Ψ : (Fin r → R') →ₗ[R'] M' :=
    Fintype.linearCombination R' (fun i ↦ LocalizedModule.mkLinearMap S M (x i)) with hΨ
  have himg : (LocalizedModule.mkLinearMap S M) '' Set.range x
      = Set.range fun i ↦ LocalizedModule.mkLinearMap S M (x i) := (Set.range_comp _ _).symm
  have hsurj : Function.Surjective Ψ := by
    rw [← LinearMap.range_eq_top, hΨ, Fintype.range_linearCombination, ← himg]
    exact hspan
  have hinj : Function.Injective Ψ := by
    refine injective_of_localized_maximal Ψ fun J hJ ↦ ?_
    set RQ := Localization.AtPrime J
    set φ := LocalizedModule.map J.primeCompl Ψ with hφ
    have hφsurj : Function.Surjective φ := LocalizedModule.map_surjective _ Ψ hsurj
    have hfree₁ : Module.Free RQ (LocalizedModule J.primeCompl (Fin r → R')) :=
      Module.free_of_isLocalizedModule J.primeCompl (LocalizedModule.mkLinearMap _ _)
    have : Nontrivial R' := nontrivial_of_isMaximal hJ
    have hrk₁ : finrank RQ (LocalizedModule J.primeCompl (Fin r → R')) = r := by
      rw [Module.finrank_of_isLocalizedModule_of_free RQ J.primeCompl
        (LocalizedModule.mkLinearMap J.primeCompl (Fin r → R'))]
      simp
    have hfree₂ : Module.Free RQ (LocalizedModule J.primeCompl M') :=
      Module.free_of_flat_of_isLocalRing
    have hrk₂ : finrank RQ (LocalizedModule J.primeCompl M') = r := by
      have hbc := rankAtStalk_isBaseChange (M := M)
        (LocalizedModule.isBaseChange S M) ⟨J, hJ.isPrime⟩
      refine .trans ?_ (.trans hbc (hrank _ ?_))
      · rfl
      · intro hmem
        exact hJ.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem
          (IsLocalization.map_units R' ⟨h, Submonoid.mem_powers h⟩))
    let b₁ := Module.finBasisOfFinrankEq RQ (LocalizedModule J.primeCompl (Fin r → R')) hrk₁
    let b₂ := Module.finBasisOfFinrankEq RQ (LocalizedModule J.primeCompl M') hrk₂
    let e := b₂.equiv b₁ (Equiv.refl (Fin r))
    have hcomp : Function.Injective (e.toLinearMap ∘ₗ φ) :=
      OrzechProperty.injective_of_surjective_endomorphism _ (e.surjective.comp hφsurj)
    exact fun a b hab ↦ hcomp (by simpa using congrArg e hab)
  exact Module.Free.of_equiv (LinearEquiv.ofBijective Ψ ⟨hinj, hsurj⟩)

/-- **The implication (8) ⇒ (7) of Stacks 00NX, locally at one maximal ideal.** A finite flat
module whose rank function is locally constant becomes free on a standard open around every
maximal ideal. -/
@[sga "3 VIIB 0.3.7" "special case"]
private theorem exists_free_away_of_isLocallyConstant_rankAtStalk [Module.Finite R M]
    [Module.Flat R M] (hlc : IsLocallyConstant (rankAtStalk (R := R) M)) (𝔪 : Ideal R)
    (h𝔪 : 𝔪.IsMaximal) :
    ∃ g ∉ 𝔪, Module.Free (Localization.Away g) (LocalizedModule.Away g M) := by
  have : 𝔪.IsPrime := h𝔪.isPrime
  set r := finrank (Localization.AtPrime 𝔪) (LocalizedModule 𝔪.primeCompl M) with hr
  obtain ⟨V, ⟨g, hgV⟩, hpV, hVU⟩ :=
    isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (show (⟨𝔪, inferInstance⟩ : PrimeSpectrum R) ∈ {q | rankAtStalk (R := R) M q = r} from hr)
      (hlc.isOpen_fiber r)
  subst hgV
  have : Module.Free (Localization.AtPrime 𝔪) (LocalizedModule 𝔪.primeCompl M) :=
    Module.free_of_flat_of_isLocalRing
  obtain ⟨x, hx⟩ : ∃ x : Fin r → M, Submodule.span (Localization.AtPrime 𝔪)
      (LocalizedModule.mkLinearMap 𝔪.primeCompl M '' Set.range x) = ⊤ := by
    let b := Module.finBasisOfFinrankEq (Localization.AtPrime 𝔪)
      (LocalizedModule 𝔪.primeCompl M) hr.symm
    have hmk : ∀ y : LocalizedModule 𝔪.primeCompl M, ∃ (m : M) (t : 𝔪.primeCompl),
        y = LocalizedModule.mk m t := fun y ↦ LocalizedModule.induction_on
          (fun m s ↦ ⟨m, s, rfl⟩) y
    choose num den hnum using hmk
    refine ⟨fun i ↦ num (b i), ?_⟩
    rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hbi : b i = Localization.mk 1 (den (b i)) •
        LocalizedModule.mkLinearMap 𝔪.primeCompl M (num (b i)) := by
      rw [LocalizedModule.mkLinearMap_apply, LocalizedModule.mk_smul_mk, one_smul, mul_one]
      exact hnum (b i)
    rw [SetLike.mem_coe, hbi]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ⟨i, rfl⟩, rfl⟩)
  obtain ⟨f, hf, hspan⟩ := Submodule.exists_mem_and_span_image_eq_top 𝔪.primeCompl (Set.range x)
    ((Submodule.span_image_eq_top_iff _ 𝔪.primeCompl
      (LocalizedModule.mkLinearMap 𝔪.primeCompl M) _).1 hx)
  have hgm : g ∉ 𝔪 := hpV
  refine ⟨f * g, fun hmem ↦ ?_, ?_⟩
  · rcases (Ideal.IsPrime.mul_mem_iff_mem_or_mem ‹𝔪.IsPrime›).1 hmem with h | h
    exacts [hf h, hgm h]
  · refine free_localizedModule_away_of_span_eq_top x
      (span_image_mkLinearMap_away_mul f g _ (hspan (LocalizedModule.mkLinearMap _ M)))
      fun q hq ↦ hVU ?_
    simp only [SetLike.mem_coe, mem_basicOpen]
    exact fun hg ↦ hq (q.asIdeal.mul_mem_left f hg)

/-- **The implication (1) ⇒ (7) of Stacks 00NX, locally at one prime.** A finitely presented flat
module becomes free on a standard open around every prime. -/
@[sga "6 I 5.8.3" "(ii) ⇒ (i)", sga "6 III 5.2" "(iii), special case"]
private theorem exists_free_away_of_flat_of_finitePresentation [Module.FinitePresentation R M]
    [Module.Flat R M] (𝔭 : Ideal R) (h𝔭 : 𝔭.IsPrime) :
    ∃ g ∉ 𝔭, Module.Free (Localization.Away g) (LocalizedModule.Away g M) := by
  have := h𝔭
  have : Module.Free (Localization.AtPrime 𝔭) (LocalizedModule 𝔭.primeCompl M) :=
    Module.free_of_flat_of_isLocalRing
  obtain ⟨g, hg, hfree, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    𝔭.primeCompl (LocalizedModule.mkLinearMap 𝔭.primeCompl M) (Localization.AtPrime 𝔭)
  exact ⟨g, hg, hfree⟩

/-- A finite module that is free on a standard open around every maximal ideal is finite locally
free. -/
private theorem exists_span_free_finite_of_forall_maximal [Module.Finite R M]
    (h : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal →
      ∃ g ∉ 𝔪, Module.Free (Localization.Away g) (LocalizedModule.Away g M)) :
    ∃ s : Set R, Ideal.span s = ⊤ ∧ ∀ f ∈ s,
      Module.Free (Localization.Away f) (LocalizedModule.Away f M) ∧
        Module.Finite (Localization.Away f) (LocalizedModule.Away f M) := by
  obtain ⟨s, hs, hfree⟩ := exists_span_eq_top_of_forall_maximal _ h
  exact ⟨s, hs, fun g hg ↦ ⟨hfree g hg, inferInstance⟩⟩

/-- The eight conditions of `Module.finite_projective_tfae` on a module `M` over a commutative
ring `R` are equivalent. -/
public theorem solution (R : Type u) [CommRing R] (M : Type v)
    [AddCommGroup M] [Module R M] :
    List.TFAE
      [Module.FinitePresentation R M ∧ Module.Flat R M,
       Module.Finite R M ∧ Module.Projective R M,
       ∃ (n : ℕ) (f : (Fin n → R) →ₗ[R] M) (g : M →ₗ[R] (Fin n → R)), f ∘ₗ g = LinearMap.id,
       Module.FinitePresentation R M ∧ Module.freeLocus R M = Set.univ,
       Module.FinitePresentation R M ∧ ∀ (𝔪 : Ideal R) (_ : 𝔪.IsMaximal),
         Module.Free (Localization.AtPrime 𝔪) (LocalizedModule 𝔪.primeCompl M),
       Module.Finite R M ∧ ∃ s : Set R, Ideal.span s = ⊤ ∧
         ∀ f ∈ s, Module.Free (Localization.Away f) (LocalizedModule.Away f M),
       ∃ s : Set R, Ideal.span s = ⊤ ∧ ∀ f ∈ s,
         Module.Free (Localization.Away f) (LocalizedModule.Away f M) ∧
           Module.Finite (Localization.Away f) (LocalizedModule.Away f M),
       Module.Finite R M ∧ Module.freeLocus R M = Set.univ ∧
         IsLocallyConstant (Module.rankAtStalk (R := R) M)] := by
  tfae_have 1 → 2 := by
    rintro ⟨_, _⟩
    exact ⟨inferInstance, Module.Flat.projective_of_finitePresentation⟩
  tfae_have 2 → 3 := by
    rintro ⟨_, _⟩
    obtain ⟨n, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
    exact ⟨n, f, g, hfg⟩
  tfae_have 3 → 2 := by
    rintro ⟨n, f, g, hfg⟩
    have hsurj : Function.Surjective f := fun m ↦ ⟨g m, LinearMap.congr_fun hfg m⟩
    exact ⟨Module.Finite.of_surjective f hsurj, Module.Projective.of_split g f hfg⟩
  tfae_have 2 → 4 := by
    rintro ⟨_, _⟩
    have := Module.finitePresentation_of_projective R M
    exact ⟨inferInstance, Module.freeLocus_eq_univ_iff.2 inferInstance⟩
  tfae_have 4 → 5 := by
    rintro ⟨_, h⟩
    exact ⟨inferInstance, fun 𝔪 h𝔪 ↦ Module.mem_freeLocus.1
      (Set.eq_univ_iff_forall.1 h ⟨𝔪, h𝔪.isPrime⟩)⟩
  tfae_have 5 → 1 := by
    rintro ⟨_, h⟩
    refine ⟨inferInstance, (flat_iff_flat_localizedModule_atMaximal M).2 fun 𝔪 h𝔪 ↦ ?_⟩
    have := h 𝔪 h𝔪
    exact inferInstance
  tfae_have 1 → 7 := by
    rintro ⟨_, _⟩
    exact exists_span_free_finite_of_forall_maximal fun 𝔪 h𝔪 ↦
      exists_free_away_of_flat_of_finitePresentation 𝔪 h𝔪.isPrime
  tfae_have 7 → 6 := by
    rintro ⟨s, hs, h⟩
    exact ⟨Module.Finite.of_localizationSpan s hs fun g ↦ (h g g.2).2, s, hs,
      fun g hg ↦ (h g hg).1⟩
  tfae_have 6 → 7 := by
    rintro ⟨_, s, hs, h⟩
    exact ⟨s, hs, fun g hg ↦ ⟨h g hg, inferInstance⟩⟩
  tfae_have 7 → 1 := by
    rintro ⟨s, hs, h⟩
    have : Module.FinitePresentation R M :=
      Module.FinitePresentation.of_localizationSpan s hs fun g ↦ by
        have := (h g g.2).1
        have := (h g g.2).2
        exact Module.finitePresentation_of_projective _ _
    refine ⟨inferInstance, Module.flat_of_localized_span R M s hs fun g ↦ ?_⟩
    have := (h g g.2).1
    exact (flat_iff_flat_localization (Submonoid.powers g.1) (Localization.Away g.1) _).2
      inferInstance
  tfae_have 1 → 8 := by
    rintro ⟨_, _⟩
    exact ⟨inferInstance, Module.freeLocus_eq_univ, Module.isLocallyConstant_rankAtStalk⟩
  tfae_have 8 → 7 := by
    rintro ⟨_, hloc, hlc⟩
    have : Module.Flat R M := (flat_iff_forall_flat_atPrime M).2 fun P hP ↦ by
      have := hP
      have : Module.Free (Localization.AtPrime P) (LocalizedModule P.primeCompl M) :=
        Module.mem_freeLocus.1 (Set.eq_univ_iff_forall.1 hloc ⟨P, hP⟩)
      exact inferInstance
    exact exists_span_free_finite_of_forall_maximal
      (exists_free_away_of_isLocallyConstant_rankAtStalk hlc)
  tfae_finish

end Stacks.LocallyFree.FiniteProjective

/-!
# Eight characterizations of a finite projective module

Let `R` be a commutative ring and let `M` be an `R`-module. The following eight conditions on
`M` agree:

1. `M` is finitely presented and flat;
2. `M` is finite projective;
3. `M` is a direct summand of a finite free module `Rⁿ`;
4. `M` is finitely presented and `M_𝔭` is free over `R_𝔭` for every prime `𝔭`;
5. `M` is finitely presented and `M_𝔪` is free over `R_𝔪` for every maximal ideal `𝔪`;
6. `M` is finite and locally free;
7. `M` is finite locally free;
8. `M` is finite, `M_𝔭` is free for every prime `𝔭`, and the rank function
   `ρ_M : Spec(R) → ℕ`, `𝔭 ↦ dim_{κ(𝔭)} M ⊗_R κ(𝔭)`, is locally constant.

Here *locally free* means that `Spec(R)` is covered by standard opens `D(f)`, `f` ranging over a
family generating the unit ideal, with `M_f` free over `R_f`; *finite locally free* means that the
covering can be chosen with each `M_f` in addition finite over `R_f`. Over a local ring the list
collapses to "`M` is finite free", and the equivalence of (6), (7) and (8) with the rest is what
makes "finite projective" a Zariski-local condition, with the locally constant function `ρ_M` as
its rank.

## Main results

* `Module.finite_projective_tfae`: the eight conditions above are equivalent.

## Implementation notes

The eight conditions are the entries, in the source's order, of a single `List.TFAE`, so the
`n`-th entry is the source's item `(n)`.

Item (3) pins the splitting rather than asserting an unnamed isomorphism onto a summand: it
provides `f : Rⁿ →ₗ[R] M` and `g : M →ₗ[R] Rⁿ` with `f ∘ₗ g = LinearMap.id`, which is the shape of
`Module.Finite.exists_comp_eq_id_of_projective`, and exhibits `M` as the summand `range g` of
`Rⁿ` cut out by the idempotent `g ∘ₗ f`.

Items (4) and (8) use `Module.freeLocus R M = Set.univ`, Mathlib's spelling of "`M_𝔭` is free for
every `𝔭 ∈ Spec(R)`": `Module.mem_freeLocus` is `Iff.rfl` for
`Module.Free (Localization.AtPrime 𝔭.asIdeal) (LocalizedModule 𝔭.asIdeal.primeCompl M)`. Item (5)
quantifies over maximal ideals instead, for which there is no free-locus spelling, and its binder
shape `∀ (𝔪 : Ideal R) (_ : 𝔪.IsMaximal)` is that of `Module.projective_of_localization_maximal`.

In items (6) and (7) the covering of `Spec(R)` by the standard opens `D(f)`, `f ∈ s`, is recorded
algebraically as `Ideal.span s = ⊤` (`PrimeSpectrum.iSup_basicOpen_eq_top_iff`), and `s : Set R`
is an arbitrary set rather than a finite one: a finite covering is a set, and conversely
`Ideal.span s = ⊤` already exhibits `1` as a finite combination, so nothing is lost either way.
This is the shape of `Module.Invertible.exists_finset_free_localization`. Mathlib has no predicate
for a locally free module over a ring — `SheafOfModules.IsLocallyFree` is the sheaf-side notion —
so the two conditions are spelled out.

The function `ρ_M` of item (8) is `Module.rankAtStalk`, whose value at `𝔭` is the fibre dimension
`dim_{κ(𝔭)} κ(𝔭) ⊗_R M` of the source by `Module.rankAtStalk_eq`, and which takes values in `ℕ`
rather than in `ℤ`; local constancy is insensitive to that, being a condition on the fibres of the
function and hence unchanged by composing with the injection `ℕ → ℤ`.

## References

* [StacksProject 00NX](https://stacks.math.columbia.edu/tag/00NX)

## Tags

finite projective module, finite locally free, flat, finitely presented, free locus, rank
-/


@[expose] public section



/-- **Characterizations of finite projective modules.** For a module `M` over a commutative ring
`R` the following are equivalent: (1) `M` is finitely presented and flat; (2) `M` is finite
projective; (3) `M` is a direct summand of a finite free module; (4) `M` is finitely presented and
free at every prime; (5) `M` is finitely presented and free at every maximal ideal; (6) `M` is
finite and locally free; (7) `M` is finite locally free; (8) `M` is finite, free at every prime,
and its rank function `ρ_M = Module.rankAtStalk M` is locally constant on `Spec(R)`. -/
@[stacks 00NX,
  ega "III 7.3.4" "(1) => (8)",
  ega "IV 2.1.12" "affine, flat everywhere",
  sga "6 I 1.3.1" "affine case; (i)⇔(iii)",
  sga "6 I 2.15.1" "affine case, (3)⇒(7)",
  sga "6 I 5.8.3" "commutative ring case", ega "III 7.9.1", sga "6 I 6.0" "special case"]
public theorem Module.finite_projective_tfae (R : Type u) [CommRing R] (M : Type v)
    [AddCommGroup M] [Module R M] :
    List.TFAE
      [Module.FinitePresentation R M ∧ Module.Flat R M,
       Module.Finite R M ∧ Module.Projective R M,
       ∃ (n : ℕ) (f : (Fin n → R) →ₗ[R] M) (g : M →ₗ[R] (Fin n → R)), f ∘ₗ g = LinearMap.id,
       Module.FinitePresentation R M ∧ Module.freeLocus R M = Set.univ,
       Module.FinitePresentation R M ∧ ∀ (𝔪 : Ideal R) (_ : 𝔪.IsMaximal),
         Module.Free (Localization.AtPrime 𝔪) (LocalizedModule 𝔪.primeCompl M),
       Module.Finite R M ∧ ∃ s : Set R, Ideal.span s = ⊤ ∧
         ∀ f ∈ s, Module.Free (Localization.Away f) (LocalizedModule.Away f M),
       ∃ s : Set R, Ideal.span s = ⊤ ∧ ∀ f ∈ s,
         Module.Free (Localization.Away f) (LocalizedModule.Away f M) ∧
           Module.Finite (Localization.Away f) (LocalizedModule.Away f M),
       Module.Finite R M ∧ Module.freeLocus R M = Set.univ ∧
         IsLocallyConstant (Module.rankAtStalk (R := R) M)] :=
    by apply Stacks.LocallyFree.FiniteProjective.solution

end
