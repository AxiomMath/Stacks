module

public import Mathlib.Algebra.Module.LocalizedModule.AtPrime
public import Mathlib.Algebra.Module.LocalizedModule.Exact
public import Mathlib.RingTheory.Support
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.CalculationMultiplicities.SupportLength
public import StacksFrontier.RingTheory.Support.Finite

/-!
# The kernel of the localization map of a module

The kernel of `M → M_S` is carried into itself by every endomorphism of `M`, so a two-periodic
complex on `M` restricts to one on the kernel of `M → M_q` and descends to one on the quotient.
Localizing at `q` kills that kernel, so `q` leaves its support. In the other direction, at a
minimal point `q` of the support of a finite module over a Noetherian ring a power of `q`
annihilates the quotient, so the support of the quotient lies in `V(q)`; over a local ring and in
support dimension one this pins the support of the quotient down to the closed point and `q`.

## Main results

* `Module.FiniteLength.mem_ker_mkLinearMap_of_mem`: the kernel is stable under every
  endomorphism.
* `Module.FiniteLength.subsingleton_localized_ker_mkLinearMap` and
  `Module.FiniteLength.notMem_support_ker_mkLinearMap`: the kernel of `M → M_q` vanishes after
  localizing at `q`, so `q` is not in its support.
* `Module.FiniteLength.exists_pow_smul_mem_ker_mkLinearMap`: at a minimal point of the support a
  power of `q` carries `M` into the kernel.
* `Module.FiniteLength.support_quotient_ker_subset_zeroLocus`: hence the support of the quotient
  lies in `V(q)`.
* `Module.FiniteLength.support_quotient_ker_subset_pair`: over a local ring in support dimension
  one, the support of the quotient is contained in the closed point together with `q`.
* `Module.FiniteLength.notMem_support_quotient_ker_of_minimal_ne`: at another minimal point the
  quotient vanishes.
* `Module.FiniteLength.bijective_localized_map_subtype_ker`: so at that point the kernel and the
  module become isomorphic.
* `Module.FiniteLength.bijective_localized_map_mkQ_ker`: at `q` itself the quotient and the
  module become isomorphic.
* `Module.FiniteLength.exact_map_iff_subsingleton_localized_quotient_range`: a two-periodic
  complex is exact after localizing exactly when its homology vanishes after localizing.
* `Module.FiniteLength.exact_map_of_bijective_of_exact`: exactness of a localized complex
  transports along an intertwining map that localizes to a bijection.
* `Module.FiniteLength.isFiniteLength_quotient_range_codRestrict_of_support_subset_pair`: the
  homology has finite length when the support meets only the closed point and `q` and the
  complex is exact at `q`.
* `Module.FiniteLength.exact_map_of_isFiniteLength_quotient_range_codRestrict`: conversely,
  finite-length homology makes the complex exact after localizing away from the closed point.

## Implementation notes

Localization of modules is `LocalizedModule`, the localization map is
`LocalizedModule.mkLinearMap`, and membership in its kernel is Mathlib's
`LocalizedModule.mem_ker_mkLinearMap_iff`. The annihilating power of `q` comes from finite length
of `M_q` over `R_q` at a minimal point of the support, which puts the support of `M_q` at the
closed point and so lets Tag 00L6 produce a power of the maximal ideal annihilating it; that
power is the image of a power of `q`. The last step uses that in support dimension one over a
local ring the minimal points of the support are exactly its nonclosed points, so a point of the
support above `q` is either the closed point or `q` itself.

## References

* [Stacks Project, Tag 02QD](https://stacks.math.columbia.edu/tag/02QD)
-/

@[expose] public section

open AlgebraicGeometry

namespace Module.FiniteLength

universe u v

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- The kernel of the localization map is carried into itself by every endomorphism. -/
theorem mem_ker_mkLinearMap_of_mem (S : Submonoid R) (φ : M →ₗ[R] M) (x : M)
    (hx : x ∈ LinearMap.ker (LocalizedModule.mkLinearMap S M)) :
    φ x ∈ LinearMap.ker (LocalizedModule.mkLinearMap S M) := by
  obtain ⟨r, hrS, hr⟩ := LocalizedModule.mem_ker_mkLinearMap_iff.mp hx
  refine LocalizedModule.mem_ker_mkLinearMap_iff.mpr ⟨r, hrS, ?_⟩
  rw [← LinearMap.map_smul, hr, map_zero]

/-- Localizing at `q` kills the kernel of the localization map at `q`. -/
theorem subsingleton_localized_ker_mkLinearMap (q : Ideal R) [q.IsPrime] :
    Subsingleton (LocalizedModule q.primeCompl
      ↥(LinearMap.ker (LocalizedModule.mkLinearMap q.primeCompl M))) := by
  refine subsingleton_of_forall_eq 0 fun c ↦ ?_
  induction c using LocalizedModule.induction_on with
  | h x s =>
      obtain ⟨r, hrS, hr⟩ := LocalizedModule.mem_ker_mkLinearMap_iff.mp x.2
      rw [← LocalizedModule.zero_mk s, LocalizedModule.mk_eq]
      refine ⟨⟨r, hrS⟩, ?_⟩
      simp only [smul_zero]
      refine Subtype.ext ?_
      have h2 : r • (s : R) • (x : M) = 0 := by
        rw [smul_comm r (s : R), hr, smul_zero]
      simpa [Submonoid.smul_def] using h2

/-- The prime `q` is not in the support of the kernel of the localization map at `q`. -/
theorem notMem_support_ker_mkLinearMap (q : PrimeSpectrum R) :
    q ∉ Module.support R
      ↥(LinearMap.ker (LocalizedModule.mkLinearMap q.asIdeal.primeCompl M)) :=
  Module.notMem_support_iff.mpr (subsingleton_localized_ker_mkLinearMap q.asIdeal)

/-- At a minimal point `q` of the support of a finite module over a Noetherian ring, some power
of `q` carries the whole module into the kernel of the localization map at `q`. -/
theorem exists_pow_smul_mem_ker_mkLinearMap [IsNoetherianRing R] [Module.Finite R M]
    (q : PrimeSpectrum R) (hq : Minimal (· ∈ Module.support R M) q) :
    ∃ n : ℕ, ∀ a ∈ q.asIdeal ^ n, ∀ x : M,
      a • x ∈ LinearMap.ker (LocalizedModule.mkLinearMap q.asIdeal.primeCompl M) := by
  have hfin : IsFiniteLength (Localization.AtPrime q.asIdeal)
      (LocalizedModule q.asIdeal.primeCompl M) :=
    Module.length_ne_top_iff.mp (localized_length_ne_top q hq)
  have hsupp : Module.support (Localization.AtPrime q.asIdeal)
      (LocalizedModule q.asIdeal.primeCompl M) ⊆
      PrimeSpectrum.zeroLocus
        (IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal) : Set _) := by
    rw [zeroLocus_maximalIdeal]
    rcases subsingleton_or_nontrivial (LocalizedModule q.asIdeal.primeCompl M) with h | h
    · rw [Module.support_eq_empty_iff.mpr h]
      exact Set.empty_subset _
    · exact (support_of_isFiniteLength hfin).le
  obtain ⟨n, hn⟩ :=
    (main_theorem_00l6 (IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal))).mpr hsupp
  refine ⟨n, fun a ha x ↦ ?_⟩
  have hmap : (q.asIdeal ^ n).map (algebraMap R (Localization.AtPrime q.asIdeal)) =
      IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal) ^ n := by
    rw [Ideal.map_pow, IsLocalization.AtPrime.map_eq_maximalIdeal]
  have hain : algebraMap R (Localization.AtPrime q.asIdeal) a ∈
      IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal) ^ n := by
    rw [← hmap]
    exact Ideal.mem_map_of_mem _ ha
  have hmem := Submodule.smul_mem_smul (r := algebraMap R (Localization.AtPrime q.asIdeal) a)
    (n := (LocalizedModule.mk x 1 : LocalizedModule q.asIdeal.primeCompl M)) hain Submodule.mem_top
  rw [hn, Submodule.mem_bot] at hmem
  have hlin : (LocalizedModule.mk (a • x) (1 : q.asIdeal.primeCompl) :
      LocalizedModule q.asIdeal.primeCompl M) = a • LocalizedModule.mk x 1 :=
    (LocalizedModule.mkLinearMap q.asIdeal.primeCompl M).map_smul a x
  change LocalizedModule.mk (a • x) 1 = 0
  rw [hlin, ← IsScalarTower.algebraMap_smul (Localization.AtPrime q.asIdeal) a]
  exact hmem

/-- The support of the quotient by the kernel of the localization map at a minimal point `q` of
the support lies in the zero locus of `q`. -/
theorem support_quotient_ker_subset_zeroLocus [IsNoetherianRing R] [Module.Finite R M]
    (q : PrimeSpectrum R) (hq : Minimal (· ∈ Module.support R M) q) :
    Module.support R
        (M ⧸ LinearMap.ker (LocalizedModule.mkLinearMap q.asIdeal.primeCompl M)) ⊆
      PrimeSpectrum.zeroLocus (q.asIdeal : Set R) := by
  obtain ⟨n, hn⟩ := exists_pow_smul_mem_ker_mkLinearMap q hq
  refine (main_theorem_00l6 q.asIdeal).mp ⟨n, le_bot_iff.mp (Submodule.smul_le.mpr ?_)⟩
  intro a ha z _
  induction z using Submodule.Quotient.induction_on with
  | H x =>
      rw [Submodule.mem_bot]
      change (LinearMap.ker (LocalizedModule.mkLinearMap q.asIdeal.primeCompl M)).mkQ (a • x) = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hn a ha x

/-- Over a Noetherian local ring, for a finite module whose support has dimension one and a
minimal point `q` of that support, the support of the quotient by the kernel of the localization
map at `q` is contained in the closed point together with `q`. -/
theorem support_quotient_ker_subset_pair [IsNoetherianRing R] [IsLocalRing R] [Module.Finite R M]
    (hdim : Module.supportDim R M = 1) (q : PrimeSpectrum R)
    (hq : Minimal (· ∈ Module.support R M) q) :
    Module.support R
        (M ⧸ LinearMap.ker (LocalizedModule.mkLinearMap q.asIdeal.primeCompl M)) ⊆
      {IsLocalRing.closedPoint R, q} := by
  intro p hp
  have hpM : p ∈ Module.support R M :=
    Module.support_subset_of_surjective _ (Submodule.mkQ_surjective _) hp
  have hqp : q ≤ p := support_quotient_ker_subset_zeroLocus q hq hp
  by_cases hcl : p = IsLocalRing.closedPoint R
  · exact Set.mem_insert_iff.mpr (Or.inl hcl)
  · have hpmin : Minimal (· ∈ Module.support R M) p :=
      (Set.ext_iff.mp (minimal_support_eq_nonclosed (R := R) (M := M) hdim) p).mpr ⟨hpM, hcl⟩
    exact Set.mem_insert_iff.mpr (Or.inr (le_antisymm (hpmin.2 hq.1 hqp) hqp))

/-- Distinct minimal points of the support are incomparable. -/
theorem not_le_of_minimal_of_ne {q p : PrimeSpectrum R}
    (hq : Minimal (· ∈ Module.support R M) q) (hp : Minimal (· ∈ Module.support R M) p)
    (hne : q ≠ p) : ¬ q ≤ p :=
  fun hle ↦ hne (le_antisymm hle (hp.2 hq.1 hle))

/-- The quotient by the kernel of the localization map at a minimal point of the support vanishes
after localizing at any other minimal point. -/
theorem notMem_support_quotient_ker_of_minimal_ne [IsNoetherianRing R] [Module.Finite R M]
    {q p : PrimeSpectrum R} (hq : Minimal (· ∈ Module.support R M) q)
    (hp : Minimal (· ∈ Module.support R M) p) (hne : q ≠ p) :
    p ∉ Module.support R
      (M ⧸ LinearMap.ker (LocalizedModule.mkLinearMap q.asIdeal.primeCompl M)) := fun hmem ↦
  not_le_of_minimal_of_ne hq hp hne (support_quotient_ker_subset_zeroLocus q hq hmem)

/-- If the quotient by a submodule vanishes after localizing, the localized inclusion of that
submodule is bijective. -/
theorem bijective_localized_map_subtype_of_subsingleton_quotient (S : Submonoid R)
    (K : Submodule R M) (h : Subsingleton (LocalizedModule S (M ⧸ K))) :
    Function.Bijective (LocalizedModule.map S K.subtype) := by
  refine ⟨LocalizedModule.map_injective S _ (Submodule.injective_subtype K), fun y ↦ ?_⟩
  exact (LocalizedModule.map_exact S K.subtype K.mkQ (LinearMap.exact_subtype_mkQ K) y).mp
    (Subsingleton.elim _ _)

/-- At a minimal point `p` of the support other than `q`, the inclusion of the kernel of the
localization map at `q` becomes an isomorphism. -/
theorem bijective_localized_map_subtype_ker [IsNoetherianRing R] [Module.Finite R M]
    {q p : PrimeSpectrum R} (hq : Minimal (· ∈ Module.support R M) q)
    (hp : Minimal (· ∈ Module.support R M) p) (hne : q ≠ p) :
    Function.Bijective (LocalizedModule.map p.asIdeal.primeCompl
      (LinearMap.ker (LocalizedModule.mkLinearMap q.asIdeal.primeCompl M)).subtype) :=
  bijective_localized_map_subtype_of_subsingleton_quotient _ _
    (Module.notMem_support_iff.mp (notMem_support_quotient_ker_of_minimal_ne hq hp hne))

/-- If a submodule vanishes after localizing, the localized quotient map is bijective. -/
theorem bijective_localized_map_mkQ_of_subsingleton_sub (S : Submonoid R)
    (K : Submodule R M) (h : Subsingleton (LocalizedModule S ↥K)) :
    Function.Bijective (LocalizedModule.map S K.mkQ) := by
  refine ⟨fun y z hyz ↦ ?_,
    LocalizedModule.map_surjective S _ (Submodule.mkQ_surjective K)⟩
  have hexact := LocalizedModule.map_exact S K.subtype K.mkQ (LinearMap.exact_subtype_mkQ K)
  have hzero : (LocalizedModule.map S K.mkQ) (y - z) = 0 := by
    rw [map_sub, hyz, sub_self]
  obtain ⟨w, hw⟩ := (hexact (y - z)).mp hzero
  refine sub_eq_zero.mp ?_
  rw [← hw, Subsingleton.elim w 0, map_zero]

/-- At a minimal point `q` of the support, the quotient by the kernel of the localization map at
`q` becomes isomorphic to the module itself after localizing at `q`. -/
theorem bijective_localized_map_mkQ_ker (q : Ideal R) [q.IsPrime] :
    Function.Bijective (LocalizedModule.map q.primeCompl
      (LinearMap.ker (LocalizedModule.mkLinearMap q.primeCompl M)).mkQ) :=
  bijective_localized_map_mkQ_of_subsingleton_sub _ _
    (subsingleton_localized_ker_mkLinearMap q)

/-- The two-periodic complex becomes exact after localizing exactly when its homology vanishes
after localizing. The homology in question is the quotient of `ker φ` by the image of `ψ`
corestricted to it. -/
theorem exact_map_iff_subsingleton_localized_quotient_range (S : Submonoid R)
    (φ ψ : M →ₗ[R] M) (h : ∀ x, ψ x ∈ LinearMap.ker φ) :
    Function.Exact (LocalizedModule.map S ψ) (LocalizedModule.map S φ) ↔
      Subsingleton (LocalizedModule S (↥(LinearMap.ker φ) ⧸
        LinearMap.range (LinearMap.codRestrict (LinearMap.ker φ) ψ h))) := by
  set ι := (LinearMap.ker φ).subtype
  set ψ' := LinearMap.codRestrict (LinearMap.ker φ) ψ h
  have hιinj : Function.Injective (LocalizedModule.map S ι) :=
    LocalizedModule.map_injective S _ (Submodule.injective_subtype _)
  have hιexact : Function.Exact (LocalizedModule.map S ι) (LocalizedModule.map S φ) :=
    LocalizedModule.map_exact S ι φ (LinearMap.exact_subtype_ker_map φ)
  have hmkQexact : Function.Exact (LocalizedModule.map S ψ')
      (LocalizedModule.map S (LinearMap.range ψ').mkQ) :=
    LocalizedModule.map_exact S ψ' _ (LinearMap.exact_iff.mpr (Submodule.ker_mkQ _))
  have hmkQsurj : Function.Surjective (LocalizedModule.map S (LinearMap.range ψ').mkQ) :=
    LocalizedModule.map_surjective S _ (Submodule.mkQ_surjective _)
  have hcompose : ∀ x, LocalizedModule.map S ι (LocalizedModule.map S ψ' x) =
      LocalizedModule.map S ψ x := by
    intro x
    induction x using LocalizedModule.induction_on with
    | h a s =>
        simp only [LocalizedModule.map_mk]
        rfl
  have hφι : ∀ z, LocalizedModule.map S φ (LocalizedModule.map S ι z) = 0 := by
    intro z
    induction z using LocalizedModule.induction_on with
    | h a s =>
        rw [LocalizedModule.map_mk, LocalizedModule.map_mk, show φ (ι a) = 0 from a.2]
        exact LocalizedModule.zero_mk s
  refine ⟨fun hex ↦ subsingleton_of_forall_eq 0 fun C ↦ ?_, fun hsub y ↦ ⟨fun hy ↦ ?_, ?_⟩⟩
  · obtain ⟨z, rfl⟩ := hmkQsurj C
    refine (hmkQexact z).mpr ?_
    obtain ⟨x, hx⟩ := (hex (LocalizedModule.map S ι z)).mp (hφι z)
    exact ⟨x, hιinj (by rw [hcompose x, hx])⟩
  · obtain ⟨z, hz⟩ := (hιexact y).mp hy
    obtain ⟨x, hx⟩ := (hmkQexact z).mp (Subsingleton.elim _ _)
    exact ⟨x, by rw [← hz, ← hx, hcompose x]⟩
  · rintro ⟨x, rfl⟩
    rw [← hcompose x, hφι]

/-- The image of `ψ` corestricted to `ker φ` is the copy of `range ψ` inside `ker φ`. -/
theorem range_codRestrict_eq_comap (φ ψ : M →ₗ[R] M) (h : ∀ x, ψ x ∈ LinearMap.ker φ) :
    LinearMap.range (LinearMap.codRestrict (LinearMap.ker φ) ψ h) =
      (LinearMap.range ψ).comap (LinearMap.ker φ).subtype := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, rfl⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, Subtype.ext hx⟩

/-- Exactness of a localized two-periodic complex transports along a linear map whose
localization is bijective and which intertwines the two pairs of differentials. -/
theorem exact_map_of_bijective_of_exact (S : Submonoid R) {N : Type v}
    [AddCommGroup N] [Module R N] (φ ψ : M →ₗ[R] M) (φ' ψ' : N →ₗ[R] N) (π : M →ₗ[R] N)
    (hφ : π ∘ₗ φ = φ' ∘ₗ π) (hψ : π ∘ₗ ψ = ψ' ∘ₗ π)
    (hbij : Function.Bijective (LocalizedModule.map S π))
    (hex : Function.Exact (LocalizedModule.map S ψ) (LocalizedModule.map S φ)) :
    Function.Exact (LocalizedModule.map S ψ') (LocalizedModule.map S φ') := by
  have hcomm : ∀ (α : M →ₗ[R] M) (α' : N →ₗ[R] N), π ∘ₗ α = α' ∘ₗ π →
      ∀ x, LocalizedModule.map S π (LocalizedModule.map S α x) =
        LocalizedModule.map S α' (LocalizedModule.map S π x) := by
    intro α α' hα x
    induction x using LocalizedModule.induction_on with
    | h a s =>
        simp only [LocalizedModule.map_mk]
        exact congrArg (fun m ↦ LocalizedModule.mk m s) (LinearMap.congr_fun hα a)
  have hcφ := hcomm φ φ' hφ
  have hcψ := hcomm ψ ψ' hψ
  intro y
  obtain ⟨x, rfl⟩ := hbij.2 y
  refine ⟨fun hy ↦ ?_, ?_⟩
  · obtain ⟨x', hx'⟩ := (hex x).mp (hbij.1 (by rw [hcφ x, hy, map_zero]))
    exact ⟨LocalizedModule.map S π x', by rw [← hcψ x', hx']⟩
  · rintro ⟨z, hz⟩
    obtain ⟨w, rfl⟩ := hbij.2 z
    have hxw : LocalizedModule.map S ψ w = x := hbij.1 (by rwa [hcψ w])
    rw [← hcφ x, ← hxw, (hex (LocalizedModule.map S ψ w)).mpr ⟨w, rfl⟩, map_zero]

/-- For a module whose support meets no prime other than the closed point and `q`, the homology
of a two-periodic complex that becomes exact after localizing at `q` has finite length. -/
theorem isFiniteLength_quotient_range_codRestrict_of_support_subset_pair
    [IsNoetherianRing R] [IsLocalRing R] [Module.Finite R M]
    (φ ψ : M →ₗ[R] M) (h : ∀ x, ψ x ∈ LinearMap.ker φ) (q : PrimeSpectrum R)
    (hsupp : Module.support R M ⊆ {IsLocalRing.closedPoint R, q})
    (hex : Function.Exact (LocalizedModule.map q.asIdeal.primeCompl ψ)
      (LocalizedModule.map q.asIdeal.primeCompl φ)) :
    IsFiniteLength R (↥(LinearMap.ker φ) ⧸
      LinearMap.range (LinearMap.codRestrict (LinearMap.ker φ) ψ h)) := by
  have hsuppH : Module.support R (↥(LinearMap.ker φ) ⧸
      LinearMap.range (LinearMap.codRestrict (LinearMap.ker φ) ψ h)) ⊆
      {IsLocalRing.closedPoint R, q} :=
    ((Module.support_subset_of_surjective _ (Submodule.mkQ_surjective _)).trans
      (Module.support_subset_of_injective _ (Submodule.injective_subtype _))).trans hsupp
  have hqH : q ∉ Module.support R (↥(LinearMap.ker φ) ⧸
      LinearMap.range (LinearMap.codRestrict (LinearMap.ker φ) ψ h)) :=
    Module.notMem_support_iff.mpr
      ((exact_map_iff_subsingleton_localized_quotient_range _ φ ψ h).mp hex)
  rcases subsingleton_or_nontrivial (↥(LinearMap.ker φ) ⧸
      LinearMap.range (LinearMap.codRestrict (LinearMap.ker φ) ψ h)) with hH | hH
  · exact IsFiniteLength.of_subsingleton
  · refine isFiniteLength_of_support (Set.Subset.antisymm (fun p hp ↦ ?_) ?_)
    · rcases Set.mem_insert_iff.mp (hsuppH hp) with hcl | hqq
      · exact hcl
      · exact absurd (Set.mem_singleton_iff.mp hqq ▸ hp) hqH
    · rintro p rfl
      exact IsLocalRing.closedPoint_mem_support R _

/-- If the homology of a two-periodic complex has finite length, the complex becomes exact after
localizing at any prime other than the closed point. -/
theorem exact_map_of_isFiniteLength_quotient_range_codRestrict
    [IsNoetherianRing R] [IsLocalRing R] [Module.Finite R M]
    (φ ψ : M →ₗ[R] M) (h : ∀ x, ψ x ∈ LinearMap.ker φ) (q : PrimeSpectrum R)
    (hqne : q ≠ IsLocalRing.closedPoint R)
    (hfin : IsFiniteLength R (↥(LinearMap.ker φ) ⧸
      LinearMap.range (LinearMap.codRestrict (LinearMap.ker φ) ψ h))) :
    Function.Exact (LocalizedModule.map q.asIdeal.primeCompl ψ)
      (LocalizedModule.map q.asIdeal.primeCompl φ) := by
  have hq : q ∉ Module.support R (↥(LinearMap.ker φ) ⧸
      LinearMap.range (LinearMap.codRestrict (LinearMap.ker φ) ψ h)) := by
    rcases subsingleton_or_nontrivial (↥(LinearMap.ker φ) ⧸
        LinearMap.range (LinearMap.codRestrict (LinearMap.ker φ) ψ h)) with hH | hH
    · rw [Module.support_eq_empty_iff.mpr hH]
      exact Set.notMem_empty q
    · rw [support_of_isFiniteLength hfin]
      exact hqne
  exact (exact_map_iff_subsingleton_localized_quotient_range _ φ ψ h).mpr
    (Module.notMem_support_iff.mp hq)

end Module.FiniteLength

end
