module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.LocalProperties.Projective
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Module.IPowerTorsion
public import StacksFrontier.Algebra.Module.IProjective
public import StacksFrontier.Homology.TwoTermComplex.Representative

/-!
# Annihilation of first Ext for two-term derived objects by a power of an ideal

For a derived object with cohomology only in degrees `-1` and `0`, annihilation of its first
Ext groups by a power of an ideal is equivalent to annihilation of its degree-minus-one
cohomology and relative projectivity of its degree-zero cohomology. Over a Noetherian ring with
finite cohomology, this can also be detected by projectivity after localization at finitely many
elements cutting out the same closed set as the ideal.

## Main results

* `TwoTermComplex.exists_power_ext_one_annihilated_iff_cohomology_conditions` (Stacks 0G9K).

## Implementation notes

The passage between the Ext groups and the cohomology modules goes through a free two-term
representative: `TwoTermComplex.ext_one_annihilated_iff_twoTerm_factorization` (Stacks 0G9F)
turns annihilation of `Ext¹` into a splitting of the differential of such a representative, and
the two cohomology modules of the object are the kernel and the cokernel of that differential.
Splitting the differential up to a scalar is then compared with killing the kernel and with
`I`-projectivity of the cokernel, the latter being measured by the ideal of scalars whose
multiplication map lifts along a chosen projective presentation.

Finite families are indexed by `Fin n`. Inclusions and equalities between their vanishing loci
are expressed by the corresponding inclusions and equalities of radical ideals. Localized
modules use the canonical `LocalizedModule` over `Localization.Away`.

## References

* [Stacks Project, Tag 0G9K](https://stacks.math.columbia.edu/tag/0G9K)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace TwoTermComplex

universe u v w

attribute [local instance] HasDerivedCategory.standard

section Modules

variable {R : Type u} [CommRing R]
variable {M : Type v} {P : Type w} {N : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup P] [Module R P] [AddCommGroup N] [Module R N]

private abbrev scalarLiftIdeal (q : P →ₗ[R] M) : Ideal R :=
  (LinearMap.range (LinearMap.llcomp R M P M q :
    (M →ₗ[R] P) →ₗ[R] (M →ₗ[R] M))).comap (LinearMap.lsmul R M)

private lemma mem_scalarLiftIdeal (q : P →ₗ[R] M) (a : R) :
    a ∈ scalarLiftIdeal q ↔ ∃ s : M →ₗ[R] P, q.comp s = a • LinearMap.id := Iff.rfl

private lemma isIProjective_iff_le_scalarLiftIdeal [Module.Projective R P]
    [Small.{max u v} P]
    (q : P →ₗ[R] M) (hq : Function.Surjective q) (I : Ideal R) :
    Module.IsIProjective R I M ↔ I ≤ scalarLiftIdeal q := by
  constructor
  · intro h a ha
    obtain ⟨Q, _, _, _, s, t, ht⟩ := h a ha
    obtain ⟨t', ht'⟩ := Module.projective_lifting_property q t hq
    refine ⟨t'.comp s, ?_⟩
    change q.comp (t'.comp s) = (LinearMap.lsmul R M) a
    rw [← LinearMap.comp_assoc, ht', ← ht]
  · intro h a ha
    obtain ⟨s, hs⟩ := h ha
    exact FactorsThroughProj.mk' s q hs.symm

private lemma isIProjective_of_equiv {N : Type v} [AddCommGroup N] [Module R N]
    (I : Ideal R) (e : M ≃ₗ[R] N)
    (h : Module.IsIProjective R I M) : Module.IsIProjective R I N := by
  intro a ha
  obtain ⟨P, _, _, _, s, t, ht⟩ := h a ha
  refine FactorsThroughProj.mk' (s.comp e.symm.toLinearMap) (e.toLinearMap.comp t) ?_
  ext x
  have he := LinearMap.congr_fun ht (e.symm x)
  simpa using congrArg e he

private abbrev differentialSplitIdeal (d : N →ₗ[R] P) : Ideal R where
  carrier := {a | ∃ h : P →ₗ[R] N, h.comp d = a • LinearMap.id}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro a b ⟨h, hh⟩ ⟨k, hk⟩
    exact ⟨h + k, by simp [LinearMap.add_comp, hh, hk, add_smul]⟩
  smul_mem' := by
    rintro a b ⟨h, hh⟩
    exact ⟨a • h, by simp [LinearMap.smul_comp, hh, smul_smul]⟩

private lemma cohomology_of_differentialSplit
    (d : N →ₗ[R] P) {a : R} (ha : a ∈ differentialSplitIdeal d) :
    (∀ x : d.ker, a • x = 0) ∧ a ∈ scalarLiftIdeal d.range.mkQ := by
  obtain ⟨h, hh⟩ := ha
  have hhx (x : N) : h (d x) = a • x := LinearMap.congr_fun hh x
  constructor
  · intro x
    apply Subtype.ext
    change a • (x : N) = 0
    rw [← hhx, x.property, map_zero]
  · let b : P →ₗ[R] P := a • LinearMap.id - d.comp h
    have hb : d.range ≤ b.ker := by
      rintro _ ⟨x, rfl⟩
      change a • d x - d (h (d x)) = 0
      rw [hhx, map_smul, sub_self]
    refine ⟨d.range.liftQ b hb, ?_⟩
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := d.range.mkQ_surjective x
    change d.range.mkQ (b y) = a • d.range.mkQ y
    simp [b]

private lemma differentialSplit_of_cohomology [Module.Projective R P]
    (d : N →ₗ[R] P) {a b : R} (ha : ∀ x : d.ker, a • x = 0)
    (hb : b ∈ scalarLiftIdeal d.range.mkQ) : a * b ∈ differentialSplitIdeal d := by
  obtain ⟨s, hs⟩ := hb
  let t : P →ₗ[R] P := b • LinearMap.id - s.comp d.range.mkQ
  have ht : ∀ x, t x ∈ d.range := by
    intro x
    rw [← Submodule.Quotient.mk_eq_zero]
    change d.range.mkQ (t x) = 0
    have hx := LinearMap.congr_fun hs (d.range.mkQ x)
    simpa [t, map_sub, map_smul] using sub_eq_zero.mpr hx.symm
  obtain ⟨h, hh⟩ := Module.projective_lifting_property d.rangeRestrict
    (t.codRestrict d.range ht) (by rintro ⟨y, x, rfl⟩; exact ⟨x, rfl⟩)
  have hhx (x : P) : d (h x) = t x :=
    congrArg Subtype.val (LinearMap.congr_fun hh x)
  refine ⟨a • h, ?_⟩
  ext x
  have hx : h (d x) - b • x ∈ d.ker := by
    change d (h (d x) - b • x) = 0
    rw [map_sub, map_smul, hhx]
    have hq : d.range.mkQ (d x) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).2 ⟨x, rfl⟩
    simp only [t, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      LinearMap.comp_apply, hq, map_zero, sub_zero, sub_self]
  have hk := congrArg Subtype.val (ha ⟨_, hx⟩)
  change a • (h (d x) - b • x) = 0 at hk
  simpa [smul_sub, sub_eq_zero, mul_smul] using hk

private lemma localizedMap_comp (S : Submonoid R) (f : M →ₗ[R] P) (g : P →ₗ[R] N) :
    LocalizedModule.map S (g.comp f) =
      (LocalizedModule.map S g).comp (LocalizedModule.map S f) := by
  apply LinearMap.ext
  apply LocalizedModule.induction_on
  intro m s
  simp

private lemma projective_localized_of_mem_radical [Module.Projective R P]
    (q : P →ₗ[R] M) {f : R} (hf : f ∈ (scalarLiftIdeal q).radical) :
    Module.Projective (Localization.Away f) (LocalizedModule (Submonoid.powers f) M) := by
  obtain ⟨n, s, hs⟩ := hf
  let S := Submonoid.powers f
  have hu := IsLocalization.map_units (Localization S) (⟨f ^ n, ⟨n, rfl⟩⟩ : S)
  let e : LocalizedModule S M ≃ₗ[Localization S] LocalizedModule S M :=
    LinearEquiv.smulOfUnit hu.unit
  have he : (LocalizedModule.map S q).comp (LocalizedModule.map S s) = e.toLinearMap := by
    rw [← localizedMap_comp]
    change q.comp s = f ^ n • LinearMap.id at hs
    rw [hs, map_smul, LocalizedModule.map_id]
    ext x
    change (f ^ n) • x = (hu.unit : Localization S) • x
    rw [IsUnit.unit_spec, algebraMap_smul]
  apply Module.Projective.of_split ((LocalizedModule.map S s).comp e.symm.toLinearMap)
    (LocalizedModule.map S q)
  rw [← LinearMap.comp_assoc, he, LinearEquiv.comp_symm]

private lemma mem_radical_of_projective_localized [Module.FinitePresentation R M]
    (q : P →ₗ[R] M) (hq : Function.Surjective q) {f : R}
    [Module.Projective (Localization.Away f) (LocalizedModule (Submonoid.powers f) M)] :
    f ∈ (scalarLiftIdeal q).radical := by
  let S := Submonoid.powers f
  obtain ⟨s, hs⟩ := Module.projective_lifting_property
    (LocalizedModule.map S q) LinearMap.id (LocalizedModule.map_surjective S q hq)
  obtain ⟨⟨t, a⟩, ha⟩ := IsLocalizedModule.surj S (LocalizedModule.map S) s
  have ht : LocalizedModule.map S (q.comp t) =
      LocalizedModule.map S ((a : R) • (LinearMap.id : M →ₗ[R] M)) := by
    rw [localizedMap_comp, ← ha]
    change (LocalizedModule.map S q).comp ((a : R) • s) = _
    rw [LinearMap.comp_smul, hs, map_smul, LocalizedModule.map_id]
  obtain ⟨b, hb⟩ := (IsLocalizedModule.eq_iff_exists S
    (LocalizedModule.map S (M := M) (N := M))).1 ht
  obtain ⟨i, hi⟩ := a.property
  obtain ⟨j, hj⟩ := b.property
  refine ⟨j + i, (b : R) • t, ?_⟩
  change q.comp ((b : R) • t) = (LinearMap.lsmul R M) (f ^ (j + i))
  rw [LinearMap.comp_smul]
  change (b : R) • q.comp t = (b : R) • ((a : R) • LinearMap.id) at hb
  rw [hb, smul_smul, ← hi, ← hj, ← pow_add]
  rfl

private lemma exists_power_annihilates_iff_torsion
    [Module.Finite R M] (I : Ideal R) (hI : I.FG) :
    (∃ c : ℕ, ∀ a ∈ I ^ c, ∀ x : M, a • x = 0) ↔ IsIPowerTorsion R M I := by
  constructor
  · rintro ⟨c, hc⟩ x
    refine ⟨c + 1, Nat.succ_pos c, fun a ha => hc a ?_ x⟩
    exact Ideal.pow_le_pow_right (Nat.le_succ c) ha
  · intro h
    have hs := (isIPowerTorsion_iff_support_subset R M I hI).1 h
    rw [Module.support_eq_zeroLocus, PrimeSpectrum.zeroLocus_subset_zeroLocus_iff] at hs
    obtain ⟨c, hc⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hs hI
    exact ⟨c, fun a ha => Module.mem_annihilator.mp (hc ha)⟩

/-- A finitely generated ideal is spanned by a finite family indexed by `Fin n` of its elements. -/
private lemma exists_fin_family_span_eq (I : Ideal R) (hI : I.FG) :
    ∃ (n : ℕ) (f : Fin n → R), Ideal.span (Set.range f) = I ∧ ∀ i, f i ∈ I := by
  obtain ⟨n, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hI
  change Ideal.span (Set.range f) = I at hf
  exact ⟨n, f, hf, fun i => hf ▸ Ideal.subset_span ⟨i, rfl⟩⟩

private lemma projective_localized_of_isIProjective
    (I : Ideal R) {c : ℕ} (h : Module.IsIProjective R (I ^ c) M) {f : R} (hf : f ∈ I) :
    Module.Projective (Localization.Away f) (LocalizedModule (Submonoid.powers f) M) := by
  let q : (M →₀ R) →ₗ[R] M := Finsupp.linearCombination R id
  have hq : Function.Surjective q := Finsupp.linearCombination_surjective R Function.surjective_id
  exact projective_localized_of_mem_radical q
    ⟨c, (isIProjective_iff_le_scalarLiftIdeal q hq _).1 h (Ideal.pow_mem_pow hf c)⟩

private lemma exists_power_isIProjective_iff_localized
    [Module.FinitePresentation R M] (I : Ideal R) (hI : I.FG) :
    (∃ c : ℕ, Module.IsIProjective R (I ^ c) M) ↔
      ∃ (n : ℕ) (f : Fin n → R), I.radical ≤ (Ideal.span (Set.range f)).radical ∧
        ∀ i, Module.Projective (Localization.Away (f i))
          (LocalizedModule (Submonoid.powers (f i)) M) := by
  let q : (M →₀ R) →ₗ[R] M := Finsupp.linearCombination R id
  have hq : Function.Surjective q := Finsupp.linearCombination_surjective R Function.surjective_id
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨n, f, hf, hmem⟩ := exists_fin_family_span_eq I hI
    exact ⟨n, f, by rw [hf], fun i => projective_localized_of_isIProjective I hc (hmem i)⟩
  · rintro ⟨n, f, hf, hp⟩
    have hJ : Ideal.span (Set.range f) ≤ (scalarLiftIdeal q).radical :=
      Ideal.span_le.mpr <| Set.range_subset_iff.2 fun i =>
        have := hp i
        mem_radical_of_projective_localized q hq
    have hle : I ≤ (scalarLiftIdeal q).radical :=
      Ideal.le_radical.trans (hf.trans (Ideal.radical_mono hJ |>.trans_eq
        (Ideal.radical_idem _)))
    obtain ⟨c, hc⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hle hI
    exact ⟨c, (isIProjective_iff_le_scalarLiftIdeal q hq _).2 hc⟩

end Modules

section Derived

variable {R : Type u} [CommRing R] [Small.{v} R]

private noncomputable def homologyNegEquivKer
    {K : DerivedCategory (ModuleCat.{v} R)}
    (L : CochainComplex (ModuleCat.{v} R) ℤ) [L.IsStrictlyGE (-1)]
    (e : DerivedCategory.Q.obj L ≅ K) :
    ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) (-1)).obj K) ≃ₗ[R]
      (L.d (-1) 0).hom.ker := by
  let h : (L.sc' (-2) (-1) 0).f = 0 :=
    (L.isZero_of_isStrictlyGE (-1) (-2) (by norm_num)).eq_of_src _ _
  exact (((DerivedCategory.homologyFunctor _ (-1)).mapIso e).symm ≪≫
    (DerivedCategory.homologyFunctorFactors _ (-1)).app L ≪≫
    L.homologyIsoSc' (-2) (-1) 0 (by simp) (by simp) ≪≫
    (ShortComplex.RightHomologyData.ofHasKernel _ h).homologyIso ≪≫
    ModuleCat.kernelIsoKer (L.d (-1) 0)).toLinearEquiv

private noncomputable def homologyZeroEquivCoker
    {K : DerivedCategory (ModuleCat.{v} R)}
    (L : CochainComplex (ModuleCat.{v} R) ℤ) [L.IsStrictlyLE 0]
    (e : DerivedCategory.Q.obj L ≅ K) :
    ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).obj K) ≃ₗ[R]
      (L.X 0 ⧸ (L.d (-1) 0).hom.range) := by
  let h : (L.sc' (-1) 0 1).g = 0 :=
    (L.isZero_of_isStrictlyLE 0 1 (by norm_num)).eq_of_tgt _ _
  exact (((DerivedCategory.homologyFunctor _ 0).mapIso e).symm ≪≫
    (DerivedCategory.homologyFunctorFactors _ 0).app L ≪≫
    L.homologyIsoSc' (-1) 0 1 (by simp) (by simp) ≪≫
    (ShortComplex.LeftHomologyData.ofHasCokernel _ h).homologyIso ≪≫
    ModuleCat.cokernelIsoRangeQuotient (L.d (-1) 0)).toLinearEquiv

private lemma ext_power_iff_cohomology
    (I : Ideal R) (K : DerivedCategory (ModuleCat.{v} R))
    (hK : ∀ i : ℤ, i ≠ -1 → i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj K)) :
    (∃ c : ℕ, ∀ (N : ModuleCat.{v} R) (a : R), a ∈ I ^ c →
      ∀ ξ : DerivedCategory.Ext K
        ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj N) 1, a • ξ = 0) ↔
    ∃ c : ℕ,
      (∀ a ∈ I ^ c, ∀ x : (DerivedCategory.homologyFunctor (ModuleCat.{v} R) (-1)).obj K,
        a • x = 0) ∧
      Module.IsIProjective R (I ^ c)
        ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).obj K) := by
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨L, hge, hle, hfree, ⟨e⟩, hf⟩ :=
      (ext_one_annihilated_iff_twoTerm_factorization (I ^ c) K hK).1.mp hc
    let := hge
    let := hle
    let := hfree
    let d := (L.d (-1) 0).hom
    have hd (a : R) (ha : a ∈ I ^ c) : a ∈ differentialSplitIdeal d := by
      obtain ⟨h, hh⟩ := hf a ha
      exact ⟨h.hom, congrArg ModuleCat.Hom.hom hh⟩
    let en := homologyNegEquivKer L e
    let ez := homologyZeroEquivCoker L e
    refine ⟨c, ?_, ?_⟩
    · intro a ha x
      apply en.injective
      rw [map_smul, map_zero]
      exact (cohomology_of_differentialSplit d (hd a ha)).1 _
    · exact isIProjective_of_equiv (I ^ c) ez.symm
        ((isIProjective_iff_le_scalarLiftIdeal d.range.mkQ d.range.mkQ_surjective _).2
          fun a ha => (cohomology_of_differentialSplit d (hd a ha)).2)
  · rintro ⟨c, hn, hz⟩
    have hbot : ∀ (N : ModuleCat.{v} R) (a : R), a ∈ (⊥ : Ideal R) →
        ∀ ξ : DerivedCategory.Ext K
          ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj N) 1, a • ξ = 0 := by
      intro N a ha ξ
      have ha' : a = 0 := ha
      simp [ha']
    obtain ⟨L, hge, hle, hfree, ⟨e⟩, _⟩ :=
      (ext_one_annihilated_iff_twoTerm_factorization ⊥ K hK).1.mp hbot
    let := hge
    let := hle
    let := hfree
    let d := (L.d (-1) 0).hom
    let en := homologyNegEquivKer L e
    let ez := homologyZeroEquivCoker L e
    have hz' : I ^ c ≤ scalarLiftIdeal d.range.mkQ :=
      (isIProjective_iff_le_scalarLiftIdeal d.range.mkQ d.range.mkQ_surjective _).1
        (isIProjective_of_equiv _ ez hz)
    have hd : I ^ (c + c) ≤ differentialSplitIdeal d := by
      rw [pow_add]
      apply Ideal.mul_le.mpr
      intro a ha b hb
      apply differentialSplit_of_cohomology d (b := b) _ (hz' hb)
      intro x
      obtain ⟨y, rfl⟩ := en.surjective x
      rw [← map_smul, hn a ha y, map_zero]
    refine ⟨c + c, ?_⟩
    apply (ext_one_annihilated_iff_twoTerm_factorization (I ^ (c + c)) K hK).1.mpr
    refine ⟨L, hge, hle, hfree, ⟨e⟩, ?_⟩
    intro a ha
    obtain ⟨h, hh⟩ := hd ha
    exact ⟨ModuleCat.ofHom h, ModuleCat.hom_ext hh⟩

end Derived

/-- **Stacks 0G9K.** For a two-term derived object, some power of an ideal annihilates all
first Ext groups if and only if some power annihilates degree-minus-one cohomology and makes
degree-zero cohomology relatively projective. Under Noetherian and finiteness hypotheses these
are also equivalent to the corresponding finite-module Ext condition and to projectivity of
degree-zero cohomology after localization on a finite cover of the complement of the ideal's
vanishing locus. -/
@[stacks 0G9K]
public theorem exists_power_ext_one_annihilated_iff_cohomology_conditions
    {R : Type u} [CommRing R] [Small.{v} R] (I : Ideal R)
    (K : DerivedCategory (ModuleCat.{v} R))
    (hK : ∀ i : ℤ, i ≠ -1 → i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj K)) :
    let Hneg := (DerivedCategory.homologyFunctor (ModuleCat.{v} R) (-1)).obj K
    let Hzero := (DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).obj K
    let moduleObject := fun N : ModuleCat.{v} R ↦
      (DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj N
    let extAnnihilatedBySomePower := ∃ c : ℕ, ∀ (N : ModuleCat.{v} R) (a : R),
      a ∈ I ^ c → ∀ ξ : DerivedCategory.Ext K (moduleObject N) 1, a • ξ = 0
    let cohomologyCondition := ∃ c : ℕ,
      (∀ (a : R), a ∈ I ^ c → ∀ x : Hneg, a • x = 0) ∧
        Module.IsIProjective R (I ^ c) Hzero
    let finiteExtAnnihilatedBySomePower := ∃ c : ℕ, ∀ (N : ModuleCat.{v} R),
      Module.Finite R N → ∀ (a : R), a ∈ I ^ c →
        ∀ ξ : DerivedCategory.Ext K (moduleObject N) 1, a • ξ = 0
    let localizedProjectiveOnNeighborhood :=
      IsIPowerTorsion R Hneg I ∧ ∃ (n : ℕ) (f : Fin n → R),
        I.radical ≤ (Ideal.span (Set.range f)).radical ∧
          ∀ i, Module.Projective (Localization.Away (f i))
            (LocalizedModule (Submonoid.powers (f i)) Hzero)
    let localizedProjectiveOnCover :=
      IsIPowerTorsion R Hneg I ∧ ∃ (n : ℕ) (f : Fin n → R),
        (∀ i, f i ∈ I) ∧ (Ideal.span (Set.range f)).radical = I.radical ∧
          ∀ i, Module.Projective (Localization.Away (f i))
            (LocalizedModule (Submonoid.powers (f i)) Hzero)
    let localizedProjectiveOnEveryCover :=
      IsIPowerTorsion R Hneg I ∧ ∀ (n : ℕ) (f : Fin n → R),
        (∀ i, f i ∈ I) → (Ideal.span (Set.range f)).radical = I.radical →
          ∀ i, Module.Projective (Localization.Away (f i))
            (LocalizedModule (Submonoid.powers (f i)) Hzero)
    (extAnnihilatedBySomePower ↔ cohomologyCondition) ∧
      (IsNoetherianRing R → Module.Finite R Hneg → Module.Finite R Hzero →
        (extAnnihilatedBySomePower ↔ finiteExtAnnihilatedBySomePower) ∧
        (finiteExtAnnihilatedBySomePower ↔ localizedProjectiveOnNeighborhood) ∧
        (localizedProjectiveOnNeighborhood ↔ localizedProjectiveOnCover) ∧
        (localizedProjectiveOnCover ↔ localizedProjectiveOnEveryCover)) := by
  intro Hneg Hzero moduleObject extAll cohom extFinite onNeighborhood onCover onEveryCover
  have hEC : extAll ↔ cohom := ext_power_iff_cohomology I K hK
  refine ⟨hEC, ?_⟩
  intro hR hn hz
  let := hR
  let := hn
  let := hz
  let := Module.finitePresentation_of_finite R Hzero
  have hI := IsNoetherian.noetherian I
  have hEF : extAll ↔ extFinite := exists_congr fun c =>
    (ext_one_annihilated_iff_twoTerm_factorization (I ^ c) K hK).2.2 hR hn hz |>.1
  have hCN : cohom ↔ onNeighborhood := by
    constructor
    · rintro ⟨c, hc, hp⟩
      exact ⟨(exists_power_annihilates_iff_torsion I hI).1 ⟨c, hc⟩,
        (exists_power_isIProjective_iff_localized I hI).1 ⟨c, hp⟩⟩
    · rintro ⟨ht, hp⟩
      obtain ⟨a, ha⟩ := (exists_power_annihilates_iff_torsion I hI).2 ht
      obtain ⟨b, hb⟩ := (exists_power_isIProjective_iff_localized I hI).2 hp
      refine ⟨max a b, ?_, ?_⟩
      · intro r hr x
        exact ha r (Ideal.pow_le_pow_right (le_max_left a b) hr) x
      · intro r hr
        exact hb r (Ideal.pow_le_pow_right (le_max_right a b) hr)
  have hNE : onNeighborhood → onEveryCover := by
    intro h
    obtain ⟨c, _, hc⟩ := hCN.2 h
    exact ⟨h.1, fun n f hf _ i => projective_localized_of_isIProjective I hc (hf i)⟩
  have hEV : onEveryCover → onCover := by
    intro h
    obtain ⟨n, f, hf, hmem⟩ := exists_fin_family_span_eq I hI
    have hrad : (Ideal.span (Set.range f)).radical = I.radical := congrArg Ideal.radical hf
    exact ⟨h.1, n, f, hmem, hrad, h.2 n f hmem hrad⟩
  have hVN : onCover → onNeighborhood := by
    rintro ⟨ht, n, f, _, hf, hp⟩
    exact ⟨ht, n, f, le_of_eq hf.symm, hp⟩
  exact ⟨hEF, hEF.symm.trans (hEC.trans hCN),
    ⟨fun h => hEV (hNE h), hVN⟩, ⟨fun h => hNE (hVN h), hEV⟩⟩

end TwoTermComplex
