module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import StacksFrontier.AlgebraicGeometry.SemilocalFibre.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Freeness of a module of constant rank, after inverting one element of the base

Let `B` be an algebra module-finite over `A` and let `M` be a finite projective `B`-module whose
rank is the same integer `n` at every prime of `B`. For a prime `p` of `A` the ring
`B ⊗_A A_p` is semilocal, so `M` becomes free there (Lemma 02M9); this file spreads that
freeness out to a basic open of `Spec A`: there is `g ∉ p` such that `M ⊗_A A_g` is free over
`B ⊗_A A_g`.

## Main results

* `Stacks.RingTheory.SpreadFree.nonempty_basis_localizedModule_primeCompl`: `M` is free after
  localizing the base at a prime.
* `Stacks.RingTheory.SpreadFree.exists_mem_primeCompl_nonempty_basis_localizedModule` and
  `Stacks.RingTheory.SpreadFree.exists_mem_primeCompl_free_localizedModule`: `M` has a basis of
  `n` elements, in particular is free, after inverting a single element of `A` outside the
  prime.

## Implementation notes

Both localizations of `M` are taken at submonoids of `B` that are images of submonoids of `A`,
so that they are simultaneously localizations of the `A`-module `M`; the two models of the
localized module, `LocalizedModule T M` and `Localization T ⊗_B M`, are exchanged by
`LocalizedModule.equivTensorProduct`, which is what carries the rank computation
(`Module.rankAtStalk_baseChange`) over.

The spreading out has two halves. A basis of the localization at `p` consists of `n` fractions;
clearing their denominators and those of the finitely many generators of `M` over `B` produces
one `g ∉ p` for which the map `B_g^n → M_g` given by the numerators is *surjective* — this is the
argument of `Stacks.RingTheory.SemilocalModuleFinite.exists_mem_primeCompl_forall_exists_smul_eq`
at rank `n`. Injectivity is then free of charge rather than a second spreading out: `M_g` is
projective, so the surjection splits, and the complement of `M_g` in `B_g^n` is a finite
projective module of rank `0` at every prime, hence zero.

## References

* [Stacks Project, Tag 02M9](https://stacks.math.columbia.edu/tag/02M9)
-/

@[expose] public section

universe u

open scoped TensorProduct

namespace Stacks.RingTheory.SpreadFree

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
  (M : Type u) [AddCommGroup M] [Module B M]

section Rank

variable [Module.Finite B M] [Module.Flat B M]

/-- The rank of a localization of `M` at a submonoid of `B` is the rank of `M`. -/
private theorem rankAtStalk_localizedModule (T : Submonoid B) {n : ℕ}
    (hrk : ∀ q : PrimeSpectrum B, Module.rankAtStalk M q = n)
    (q : PrimeSpectrum (Localization T)) :
    Module.rankAtStalk (R := Localization T) (LocalizedModule T M) q = n := by
  have h := Module.rankAtStalk_eq_of_equiv (LocalizedModule.equivTensorProduct T M)
  rw [congrFun h q, Module.rankAtStalk_baseChange]
  exact hrk _

end Rank

/-- A localization of a finite projective module at a submonoid of `B` is projective. -/
private instance projective_localizedModule [Module.Projective B M] (T : Submonoid B) :
    Module.Projective (Localization T) (LocalizedModule T M) :=
  Module.Projective.of_equiv' (R := Localization T)
    (LocalizedModule.equivTensorProduct T M).symm

/-- Every element of a localized module is a fraction. -/
private theorem exists_eq_mk (T : Submonoid B) (z : LocalizedModule T M) :
    ∃ (m : M) (t : T), z = LocalizedModule.mk m t := by
  induction z using LocalizedModule.induction_on with
  | _ m t => exact ⟨m, t, rfl⟩

/-- **A finite projective module of constant rank over an algebra module-finite over `A` has a
basis after localizing `A` at a prime.** The localization of `B` is semilocal, and the localized
module is finite flat of the same constant rank, so Lemma 02M9 applies. -/
@[sga "3 V 4.1.1" "partial"]
theorem nonempty_basis_localizedModule_primeCompl [Module.Finite A B] [Module.Finite B M]
    [Module.Projective B M] {n : ℕ} (hrk : ∀ q : PrimeSpectrum B, Module.rankAtStalk M q = n)
    (p : Ideal A) [p.IsPrime] :
    Nonempty (Module.Basis (Fin n) (Localization (Algebra.algebraMapSubmonoid B p.primeCompl))
      (LocalizedModule (Algebra.algebraMapSubmonoid B p.primeCompl) M)) := by
  have : Module.Flat B M := Module.Flat.of_projective
  set T : Submonoid B := Algebra.algebraMapSubmonoid B p.primeCompl with hT
  have : Finite (MaximalSpectrum (Localization T)) :=
    Stacks.RingTheory.SemilocalModuleFinite.finite_maximalSpectrum_of_moduleFinite_of_isLocalRing
      (Localization.AtPrime p) (Localization T)
  have : Module.Flat (Localization T) (LocalizedModule T M) := Module.Flat.of_projective
  refine Module.nonempty_basis_of_flat_of_finrank_eq _ _ n fun P => ?_
  have hmax : P.asIdeal.IsMaximal := P.isMaximal
  let : Field (Localization T ⧸ P.asIdeal) := Ideal.Quotient.field _
  obtain ⟨q⟩ : Nonempty (PrimeSpectrum (Localization T ⧸ P.asIdeal)) := inferInstance
  have h1 := Module.rankAtStalk_baseChange (R := Localization T) (M := LocalizedModule T M)
    (S := Localization T ⧸ P.asIdeal) q
  have h2 := rankAtStalk_localizedModule M T hrk
    (PrimeSpectrum.comap (algebraMap (Localization T) (Localization T ⧸ P.asIdeal)) q)
  have h3 : Module.rankAtStalk (R := Localization T ⧸ P.asIdeal)
      ((Localization T ⧸ P.asIdeal) ⊗[Localization T] LocalizedModule T M) =
      (Module.finrank (Localization T ⧸ P.asIdeal)
        ((Localization T ⧸ P.asIdeal) ⊗[Localization T] LocalizedModule T M) :
          PrimeSpectrum (Localization T ⧸ P.asIdeal) → ℕ) :=
    Module.rankAtStalk_eq_finrank_of_free
  have h4 := congrFun h3 q
  simp only [Pi.natCast_apply, Nat.cast_id] at h4
  omega

/-- **The surjectivity half of the spreading out.** There are `g ∉ p` and `n` elements of `M`
that generate `M` after inverting `g`: a basis of the localization at `p` consists of `n`
fractions, and one `g` clears the denominators of those and of the finitely many generators of
`M` over `B`. -/
private theorem exists_mem_primeCompl_forall_mem_span [Module.Finite A B] [Module.Finite B M]
    [Module.Projective B M] {n : ℕ} (hrk : ∀ q : PrimeSpectrum B, Module.rankAtStalk M q = n)
    (p : Ideal A) [p.IsPrime] :
    ∃ g ∈ p.primeCompl, ∃ v : Fin n → M, ∀ y : M, ∃ c : Fin n → B,
      (algebraMap A B g) • y = ∑ i, c i • v i := by
  classical
  set T : Submonoid B := Algebra.algebraMapSubmonoid B p.primeCompl with hT
  obtain ⟨b⟩ := nonempty_basis_localizedModule_primeCompl M hrk p
  choose v tv hv using fun i => exists_eq_mk M T (b i)
  -- the numerators of a basis span the localization
  have hnum : ∀ i, (tv i : B) • b i = LocalizedModule.mk (v i) (1 : T) := by
    intro i
    rw [hv i, LocalizedModule.smul'_mk]
    exact LocalizedModule.mk_eq.mpr ⟨1, by simp [Submonoid.smul_def]⟩
  have hspan : Submodule.span (Localization T)
      (Set.range fun i => LocalizedModule.mk (v i) (1 : T)) = ⊤ := by
    rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    obtain ⟨u, hu⟩ := IsLocalization.map_units (Localization T) (tv i)
    have hbi : b i = (↑u⁻¹ : Localization T) • LocalizedModule.mk (v i) (1 : T) := by
      rw [← hnum i, ← algebraMap_smul (Localization T) (tv i : B) (b i), ← hu,
        smul_smul, u.inv_mul, one_smul]
    exact hbi ▸ Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  -- clearing denominators element by element
  have key : ∀ y : M, ∃ (s : T) (c : Fin n → B), (s : B) • y = ∑ i, c i • v i := by
    intro y
    have hmem : LocalizedModule.mk y (1 : T) ∈ Submodule.span (Localization T)
        (Set.range fun i => LocalizedModule.mk (v i) (1 : T)) := hspan ▸ Submodule.mem_top
    obtain ⟨s, hs⟩ := multiple_mem_span_of_mem_localization_span (M := T)
      (R' := Localization T) _ _ hmem
    rw [Submonoid.smul_def, LocalizedModule.smul'_mk] at hs
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun B).mp hs
    have hc' : LocalizedModule.mkLinearMap T M (∑ i, c i • v i) =
        LocalizedModule.mkLinearMap T M ((s : B) • y) := by
      rw [map_sum]
      simp only [map_smul, LocalizedModule.mkLinearMap_apply]
      rw [LocalizedModule.smul'_mk]
      exact hc
    obtain ⟨u, hu⟩ := (IsLocalizedModule.eq_iff_exists T (LocalizedModule.mkLinearMap T M)).mp hc'
    simp only [Submonoid.smul_def] at hu
    refine ⟨u * s, fun i => (u : B) * c i, ?_⟩
    rw [Submonoid.coe_mul, mul_smul, ← hu, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => (mul_smul _ _ _).symm
  -- one element of `A` for all of `M` at once
  obtain ⟨G, hG⟩ := (inferInstance : Module.Finite B M).fg_top
  choose sg cg hsc using key
  set σ : T := ∏ y ∈ G, sg y with hσ
  obtain ⟨g, hgp, hgσ⟩ : ∃ g ∈ p.primeCompl, algebraMap A B g = (σ : B) := by
    obtain ⟨g, hgp, hg⟩ : (σ : B) ∈ Algebra.algebraMapSubmonoid B p.primeCompl := hT ▸ σ.2
    exact ⟨g, hgp, hg⟩
  refine ⟨g, hgp, v, fun z => ?_⟩
  have hsub : (⊤ : Submodule B M) ≤
      Submodule.comap (LinearMap.lsmul B M (σ : B)) (Submodule.span B (Set.range v)) := by
    rw [← hG, Submodule.span_le]
    intro y hy
    have hfac : (σ : B) = ((∏ x ∈ G.erase y, sg x : T) : B) * (sg y : B) := by
      rw [hσ, ← Finset.mul_prod_erase G sg hy]
      push_cast
      ring
    change (σ : B) • y ∈ Submodule.span B (Set.range v)
    rw [hfac, mul_smul, hsc y]
    exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun B).mp
    (hsub (Submodule.mem_top : z ∈ ⊤))
  exact ⟨c, by rw [hgσ]; exact hc.symm⟩

/-- **A finite projective module of constant rank over an algebra module-finite over `A` is free
after inverting one element of `A` outside a given prime.** The `n` numerators of a basis of the
localization at `p` generate after inverting one `g ∉ p`; the resulting surjection `B_g^n → M_g`
splits, and its kernel is a finite projective module of rank `0`, hence zero. -/
@[ega "III 7.9.1" "special case"]
theorem exists_mem_primeCompl_nonempty_basis_localizedModule [Module.Finite A B]
    [Module.Finite B M] [Module.Projective B M] {n : ℕ}
    (hrk : ∀ q : PrimeSpectrum B, Module.rankAtStalk M q = n) (p : Ideal A) [p.IsPrime] :
    ∃ g ∈ p.primeCompl,
      Nonempty (Module.Basis (Fin n) (Localization (Submonoid.powers (algebraMap A B g)))
        (LocalizedModule (Submonoid.powers (algebraMap A B g)) M)) := by
  have : Module.Flat B M := Module.Flat.of_projective
  obtain ⟨g, hgp, v, hv⟩ := exists_mem_primeCompl_forall_mem_span M hrk p
  refine ⟨g, hgp, ?_⟩
  set T : Submonoid B := Submonoid.powers (algebraMap A B g) with hT
  set ψ : (Fin n → Localization T) →ₗ[Localization T] LocalizedModule T M :=
    Fintype.linearCombination (Localization T)
      (fun i => LocalizedModule.mk (v i) (1 : T)) with hψ
  have hsurj : Function.Surjective ψ := by
    intro z
    obtain ⟨y, t, rfl⟩ := exists_eq_mk M T z
    obtain ⟨c, hc⟩ := hv y
    have hγ : algebraMap A B g ∈ T := hT ▸ Submonoid.mem_powers _
    set γ : T := ⟨algebraMap A B g, hγ⟩ with hγdef
    have hbase : ∑ i, algebraMap B (Localization T) (c i) • LocalizedModule.mk (v i) (1 : T) =
        LocalizedModule.mk ((algebraMap A B g) • y) (1 : T) := by
      rw [hc, ← LocalizedModule.mkLinearMap_apply, map_sum]
      exact Finset.sum_congr rfl fun i _ => by
        rw [map_smul, LocalizedModule.mkLinearMap_apply, algebraMap_smul]
    refine ⟨fun i => Localization.mk 1 (γ * t) * algebraMap B (Localization T) (c i), ?_⟩
    rw [hψ, Fintype.linearCombination_apply]
    calc ∑ i, (Localization.mk 1 (γ * t) * algebraMap B (Localization T) (c i)) •
            LocalizedModule.mk (v i) (1 : T)
        = Localization.mk 1 (γ * t) •
            ∑ i, algebraMap B (Localization T) (c i) • LocalizedModule.mk (v i) (1 : T) := by
          rw [Finset.smul_sum]
          exact Finset.sum_congr rfl fun i _ => mul_smul _ _ _
      _ = Localization.mk 1 (γ * t) • LocalizedModule.mk ((algebraMap A B g) • y) (1 : T) := by
          rw [hbase]
      _ = LocalizedModule.mk y t := by
          rw [LocalizedModule.mk_smul_mk]
          exact LocalizedModule.mk_eq.mpr
            ⟨1, by simp [hγdef, Submonoid.smul_def, mul_smul, mul_comm]⟩
  -- the surjection splits, and its kernel has rank zero
  obtain ⟨h, hh⟩ := Module.projective_lifting_property ψ LinearMap.id hsurj
  set e := ((LinearMap.exact_subtype_ker_map ψ).splitSurjectiveEquiv
    (LinearMap.ker ψ).injective_subtype ⟨h, hh⟩).1 with he
  have : Module.Projective (Localization T) (LinearMap.ker ψ) :=
    Module.Projective.of_split (R := Localization T) (M := (Fin n → Localization T))
      (e.symm.toLinearMap ∘ₗ LinearMap.inl (Localization T) _ _)
      (LinearMap.fst (Localization T) _ _ ∘ₗ e.toLinearMap) (by ext x; simp)
  have : Module.Finite (Localization T) (LinearMap.ker ψ) :=
    Module.Finite.of_surjective (LinearMap.fst (Localization T) _ _ ∘ₗ e.toLinearMap)
      fun k => ⟨e.symm (k, 0), by simp⟩
  have : Module.Flat (Localization T) (LinearMap.ker ψ) := Module.Flat.of_projective
  have : Module.Flat (Localization T) (LocalizedModule T M) := Module.Flat.of_projective
  have hprod := Module.rankAtStalk_eq_of_equiv e
  rw [Module.rankAtStalk_prod] at hprod
  have hzero : Module.rankAtStalk (R := Localization T) (LinearMap.ker ψ) = 0 := by
    funext q
    have h1 := congrFun hprod q
    have hnt : Nontrivial (Localization T) := by
      rcases subsingleton_or_nontrivial (Localization T) with hsub | hsub
      · refine absurd ((Ideal.eq_top_iff_one _).mpr ?_) q.isPrime.ne_top
        rw [Subsingleton.elim (1 : Localization T) 0]
        exact Submodule.zero_mem _
      · exact hsub
    have h2 : Module.rankAtStalk (R := Localization T) (Fin n → Localization T) q = n := by
      simp
    have h3 := rankAtStalk_localizedModule M T hrk q
    simp only [Pi.add_apply, Pi.zero_apply] at h1 ⊢
    omega
  have hinj : Function.Injective ψ := by
    have hsub : Subsingleton (LinearMap.ker ψ) :=
      (Module.rankAtStalk_eq_zero_iff_subsingleton (R := Localization T)
        (M := LinearMap.ker ψ)).mp hzero
    rwa [← LinearMap.ker_eq_bot, ← Submodule.subsingleton_iff_eq_bot]
  exact ⟨(Pi.basisFun (Localization T) (Fin n)).map (LinearEquiv.ofBijective ψ ⟨hinj, hsurj⟩)⟩

/-- **A finite projective module of constant rank over an algebra module-finite over `A` is free
after inverting one element of `A` outside a given prime.** -/
@[ega "III 7.9.1" "special case"]
theorem exists_mem_primeCompl_free_localizedModule [Module.Finite A B] [Module.Finite B M]
    [Module.Projective B M] {n : ℕ} (hrk : ∀ q : PrimeSpectrum B, Module.rankAtStalk M q = n)
    (p : Ideal A) [p.IsPrime] :
    ∃ g ∈ p.primeCompl,
      Module.Free (Localization (Submonoid.powers (algebraMap A B g)))
        (LocalizedModule (Submonoid.powers (algebraMap A B g)) M) := by
  obtain ⟨g, hgp, ⟨b⟩⟩ := exists_mem_primeCompl_nonempty_basis_localizedModule M hrk p
  exact ⟨g, hgp, Module.Free.of_basis b⟩

end Stacks.RingTheory.SpreadFree

end
