module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.Spectrum.Prime.ConstructibleSet
public import Mathlib.Topology.Spectral.ConstructibleTopology
public import StacksFrontier.RingTheory.Module.LocallyFree.FiniteFlat
public import StacksFrontier.RingTheory.Module.LocallyFree.FiniteProjective

/-!
# Projectivity of a finite flat module from its reduction

Let `M` be a finite flat module over a commutative ring `R` and let `I` be an ideal contained in
the Jacobson radical, so that `V(I)` contains every closed point of `Spec R`. If the reduction
`M / IM` is projective over `R ⧸ I`, then `M` is already projective over `R`.

A finite flat module is free at every prime, so by the characterisation of finite projective
modules it is projective as soon as its rank function is locally constant. The rank function is
always upper semicontinuous, so what has to be produced is openness of each locus
`{𝔭 : n ≤ rank M_𝔭}`. That locus is closed and stable under generalization; projectivity of the
reduction makes its rank locally constant on `V(I)`, so the part of `V(I)` outside the locus is
compact, and a closed generalization-stable set whose complement meets `V(I)` compactly is
constructible, hence open.

## Main results

* `Module.projective_of_projective_quotient_of_le_jacobson`: the statement above.

## Implementation notes

The reduction `M / IM` is `M ⧸ I • ⊤` with its `R ⧸ I`-module structure, and the hypothesis on
`I` is the inclusion `I ≤ Ideal.jacobson ⊥`; `Ideal.le_ringJacobson_iff_isUnit_one_add` turns that
into the source's condition that every element of `1 + I` be a unit.

Upper semicontinuity of the rank of a finite flat module is reproved here as
`Module.isOpen_rankAtStalk_le_of_flat` because the copy in
`StacksFrontier.RingTheory.Module.LocallyFree.FiniteFlat` is `private` to that module; the two should
be merged into one provider.

## References

* [Stacks Project, Tag 0D48](https://stacks.math.columbia.edu/tag/0D48)
-/

universe u v

@[expose] public section

namespace Module

open PrimeSpectrum

attribute [local instance] Module.free_of_flat_of_isLocalRing

variable {R : Type u} [CommRing R]

/-- Reduction along `R → R ⧸ I` does not change the rank at a prime of the quotient. -/
private theorem rankAtStalk_quotient (I : Ideal R)
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Flat R M]
    (p : PrimeSpectrum (R ⧸ I)) :
    Module.rankAtStalk (R := R ⧸ I) (M ⧸ I • (⊤ : Submodule R M)) p =
      Module.rankAtStalk (R := R) M (p.comap (Ideal.Quotient.mk I)) := by
  let eR := TensorProduct.quotTensorEquivQuotSMul M I
  let e : TensorProduct R (R ⧸ I) M ≃ₗ[R ⧸ I] (M ⧸ I • (⊤ : Submodule R M)) :=
    { toEquiv := eR.toEquiv
      map_add' := eR.map_add
      map_smul' := fun s x => by
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective s
        exact eR.map_smul r x }
  simpa only [Ideal.Quotient.algebraMap_eq] using
    (congrFun (Module.rankAtStalk_eq_of_equiv e.symm) p).trans (Module.rankAtStalk_baseChange p)

/-- The rank of a finite flat module is upper semicontinuous: near a prime `𝔭`, a basis of `M_𝔭`
is already defined over a standard open neighbourhood and generates `M` there. -/
theorem isOpen_rankAtStalk_le_of_flat (M : Type v) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Flat R M] (n : ℕ) :
    IsOpen {q : PrimeSpectrum R | Module.rankAtStalk M q ≤ n} := by
  rw [isOpen_iff_forall_mem_open]
  intro p hp
  let Rₚ := Localization.AtPrime p.asIdeal
  let Mₚ := LocalizedModule p.asIdeal.primeCompl M
  let k := Module.rankAtStalk M p
  let f : (Fin k →₀ R) →ₗ[R] Fin k →₀ Rₚ := Finsupp.mapRange.linearMap (Algebra.linearMap R Rₚ)
  let g : M →ₗ[R] Mₚ := LocalizedModule.mkLinearMap p.asIdeal.primeCompl M
  obtain ⟨φ, -, -, hφps⟩ := Module.exists_localizedMap_surjective_of_surjective
    p.asIdeal.primeCompl f g ((Module.finBasis Rₚ Mₚ).repr.restrictScalars R).symm.surjective
  rw [IsLocalizedModule.map_surjective_iff_localizedModuleMap_surjective f g] at hφps
  obtain ⟨a, hap, hφas⟩ :=
    Module.exists_localizedMap_away_surjective_of_localizedMap_atPrime_surjective p.asIdeal φ hφps
  refine ⟨(basicOpen a : Set (PrimeSpectrum R)), ?_, (basicOpen a).2, by simpa using hap⟩
  intro q hq
  rw [LinearMap.localizedMap_surjective_iff_subsingleton_localized_coker,
    LocalizedModule.subsingleton_iff_support_subset] at hφas
  have hqa : a ∉ q.asIdeal := by simpa [PrimeSpectrum.mem_basicOpen] using hq
  have hqs : q ∉ Module.support R (M ⧸ φ.range) := fun h => hqa (hφas h rfl)
  rw [Module.notMem_support_iff] at hqs
  have hsurj : Function.Surjective (LocalizedModule.map q.asIdeal.primeCompl φ) := by
    rwa [LinearMap.localizedMap_surjective_iff_subsingleton_localized_coker]
  show Module.rankAtStalk M q ≤ n
  have : Nontrivial R := ⟨1, 0, fun h => q.isPrime.one_notMem (h ▸ q.asIdeal.zero_mem)⟩
  calc Module.rankAtStalk M q
      = Module.finrank (Localization.AtPrime q.asIdeal)
          (LocalizedModule q.asIdeal.primeCompl M) := rfl
    _ ≤ Module.finrank (Localization.AtPrime q.asIdeal)
          (LocalizedModule q.asIdeal.primeCompl (Fin k →₀ R)) :=
        LinearMap.finrank_le_finrank_of_surjective hsurj
    _ = Module.rankAtStalk (R := R) (Fin k →₀ R) q := rfl
    _ = k := by simp
    _ ≤ n := hp

/-- A closed, generalization-stable set is open as soon as its complement inside `V(I)` is
compact, for `I` contained in the Jacobson radical: the finitely many basic opens covering that
complement span an ideal cutting out the set, so its complement is compact, hence the set is
constructible. -/
private theorem isOpen_of_isCompact_zeroLocus_diff (I : Ideal R)
    (hI : I ≤ Ideal.jacobson (⊥ : Ideal R)) (Z : Set (PrimeSpectrum R)) (hclosed : IsClosed Z)
    (hgen : StableUnderGeneralization Z)
    (hcompact : IsCompact (zeroLocus (I : Set R) \ Z)) : IsOpen Z := by
  classical
  let J : Ideal R := vanishingIdeal Z
  have hZ : zeroLocus (J : Set R) = Z :=
    (zeroLocus_vanishingIdeal_eq_closure Z).trans hclosed.closure_eq
  have hcover : zeroLocus (I : Set R) \ Z ⊆ ⋃ x : J, basicOpen (x : R) := by
    intro p hp
    rw [Set.mem_iUnion]
    have hnJ : ¬ J ≤ p.asIdeal := fun hj => hp.2 (hZ ▸ (mem_zeroLocus _ _).2 hj)
    obtain ⟨x, hxJ, hxp⟩ := Set.not_subset.mp hnJ
    exact ⟨⟨x, hxJ⟩, by simpa [PrimeSpectrum.mem_basicOpen] using hxp⟩
  obtain ⟨s, hs⟩ := hcompact.elim_finite_subcover
    (fun x : J => basicOpen (x : R)) (fun x => (basicOpen (x : R)).2) hcover
  let K : Ideal R := Ideal.span ((s.image Subtype.val : Finset R) : Set R)
  have hKJ : K ≤ J := by
    refine Ideal.span_le.mpr fun x hx => ?_
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hx
    exact y.2
  have hZK : Z = zeroLocus (K : Set R) := by
    refine le_antisymm (hZ ▸ zeroLocus_anti_mono_ideal hKJ) fun p hpK => ?_
    by_contra hpZ
    obtain ⟨m, hm, hpm⟩ := p.asIdeal.exists_le_maximal p.isPrime.ne_top
    have hIm : I ≤ m := hI.trans (by exact sInf_le ⟨bot_le, hm⟩)
    have hmZ : (⟨m, hm.isPrime⟩ : PrimeSpectrum R) ∉ Z := fun hmZ =>
      hpZ (hgen ((PrimeSpectrum.le_iff_specializes p ⟨m, hm.isPrime⟩).1 hpm) hmZ)
    have hmT : (⟨m, hm.isPrime⟩ : PrimeSpectrum R) ∈ zeroLocus (I : Set R) \ Z :=
      ⟨(mem_zeroLocus _ _).2 hIm, hmZ⟩
    obtain ⟨y, hys, hmy⟩ := Set.mem_iUnion₂.mp (hs hmT)
    have hyK : (y : R) ∈ K := Ideal.subset_span (Finset.mem_image.mpr ⟨y, hys, rfl⟩)
    exact (by simpa [PrimeSpectrum.mem_basicOpen] using hmy : (y : R) ∉ m)
      (hpm ((mem_zeroLocus _ _).1 hpK hyK))
  have hcomp : IsCompact Zᶜ := by
    rw [hZK]
    exact (PrimeSpectrum.isCompact_isOpen_iff_ideal.mpr ⟨K, Submodule.fg_span
      (Finset.finite_toSet _), rfl⟩).1
  exact PrimeSpectrum.isOpen_of_stableUnderGeneralization_of_isConstructible hgen
    (by simpa only [compl_compl] using (hcomp.isConstructible hclosed.isOpen_compl).compl)

/-- Projectivity of the reduction makes every upper rank locus open. -/
private theorem isOpen_rankAtStalk_ge_of_projective_quotient (I : Ideal R)
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Flat R M]
    (hI : I ≤ Ideal.jacobson (⊥ : Ideal R))
    (hM : Module.Projective (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M))) (n : ℕ) :
    IsOpen {p : PrimeSpectrum R | n ≤ Module.rankAtStalk M p} := by
  classical
  let S := R ⧸ I
  let N := M ⧸ I • (⊤ : Submodule R M)
  let f : R →+* S := Ideal.Quotient.mk I
  let Z : Set (PrimeSpectrum R) := {p | n ≤ Module.rankAtStalk M p}
  have hclosed : IsClosed Z := by
    rcases n with _ | m
    · simp [Z]
    · have he : Z = {p : PrimeSpectrum R | Module.rankAtStalk M p ≤ m}ᶜ := by
        ext p
        simp only [Z, Set.mem_ofPred_eq, Set.mem_compl_iff, not_le]
        omega
      rw [he, isClosed_compl_iff]
      exact isOpen_rankAtStalk_le_of_flat M m
  have hgen : StableUnderGeneralization Z := fun x y hyx hx => by
    simpa only [Z, Set.mem_ofPred_eq, Module.rankAtStalk_eq_of_le_of_finite_of_flat M
      ((PrimeSpectrum.le_iff_specializes y x).2 hyx)] using hx
  have : Module.Projective S N := hM
  have : Module.Finite R N := Module.Finite.quotient R (I • (⊤ : Submodule R M))
  have : Module.Finite S N := Module.Finite.of_restrictScalars_finite R S N
  have : Module.FinitePresentation S N := Module.finitePresentation_of_projective S N
  have hlc : IsLocallyConstant (Module.rankAtStalk (R := S) N) :=
    Module.isLocallyConstant_rankAtStalk
  let W : Set (PrimeSpectrum S) := {q | Module.rankAtStalk N q < n}
  have hWclosed : IsClosed W := (isClosed_discrete {k : ℕ | k < n}).preimage hlc.continuous
  have hrange : Set.range (PrimeSpectrum.comap f) = zeroLocus (I : Set R) := by
    simpa only [f, S, Ideal.mk_ker] using
      (range_comap_of_surjective S f Ideal.Quotient.mk_surjective)
  have hW : W = PrimeSpectrum.comap f ⁻¹' Zᶜ := Set.ext fun q => by
    simp [Z, W, f, S, N, rankAtStalk_quotient I q]
  have himage : (PrimeSpectrum.comap f) '' W = zeroLocus (I : Set R) \ Z := by
    rw [hW, Set.image_preimage_eq_inter_range, hrange, Set.inter_comm, Set.sdiff_eq]
  have hcompact : IsCompact (zeroLocus (I : Set R) \ Z) := by
    rw [← himage]
    exact hWclosed.isCompact.image (PrimeSpectrum.continuous_comap f)
  exact isOpen_of_isCompact_zeroLocus_diff I hI Z hclosed hgen hcompact

/-- **Stacks 0D48.** Let `I` be an ideal contained in the Jacobson radical of `R`, equivalently an
ideal every element of whose coset `1 + I` is a unit. A finite flat `R`-module whose reduction
`M / IM` is projective over `R ⧸ I` is itself projective. -/
@[stacks 0D48]
theorem projective_of_projective_quotient_of_le_jacobson (I : Ideal R)
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Flat R M]
    (hI : I ≤ Ideal.jacobson (⊥ : Ideal R))
    (hM : Module.Projective (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M))) : Module.Projective R M := by
  have hlc : IsLocallyConstant (Module.rankAtStalk (R := R) M) := by
    refine IsLocallyConstant.iff_isOpen_fiber.mpr fun n => ?_
    show IsOpen {p : PrimeSpectrum R | Module.rankAtStalk M p = n}
    have he : {p : PrimeSpectrum R | Module.rankAtStalk M p = n} =
        {p | n ≤ Module.rankAtStalk M p} ∩ {p | Module.rankAtStalk M p ≤ n} :=
      Set.ext fun p => ⟨fun hp => ⟨hp.ge, hp.le⟩, fun hp => le_antisymm hp.2 hp.1⟩
    rw [he]
    exact (isOpen_rankAtStalk_ge_of_projective_quotient I hI hM n).inter
      (isOpen_rankAtStalk_le_of_flat M n)
  have h8 : Module.Finite R M ∧ Module.freeLocus R M = Set.univ ∧
      IsLocallyConstant (Module.rankAtStalk (R := R) M) :=
    ⟨inferInstance, Module.freeLocus_eq_univ, hlc⟩
  have hfp : Module.Finite R M ∧ Module.Projective R M :=
    ((Module.finite_projective_tfae R M).out 8 2).mp h8
  exact hfp.2

end Module
