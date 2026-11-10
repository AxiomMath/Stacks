module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.LocalProperties.Basic
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.Length
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import StacksFrontier.AlgebraicGeometry.Chow.PreparationTameSymbols.Basic
public import StacksFrontier.AlgebraicGeometry.SemilocalFibre.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.DeltaInvariant.Parameters
public import StacksFrontier.RingTheory.Length.SemilocalDecomposition
public import StacksFrontier.RingTheory.Localization.Glueing.RingHomGluing.Away
import StacksFrontier.RingTheory.Length.SemiLocal
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.PreparationTameSymbols.Preparation.Defs
import all StacksFrontier.AlgebraicGeometry.Chow.PreparationTameSymbols.Preparation.Defs

/-!
# Preparing nonzerodivisors for the tame symbol: orders in finite modifications

For an injective finite modification `A → S` of a one-dimensional Noetherian local ring whose
cokernel is killed by a power of the maximal ideal, the order of a nonzerodivisor `x` of `A` is
the length of `S / xS`, and hence the sum, over the maximal ideals of `S`, of the local orders of
`x` weighted by the residue degrees. This file proves these identities and the comparisons between
the order of `x` and its local orders that drive the induction of the construction in
`StacksFrontier.AlgebraicGeometry.Chow.PreparationTameSymbols.Preparation.Construction`.

## Main results

* `AlgebraicGeometry.ord_eq_length_quotient_of_finite_modification`: the order of `x` in `A` is
  the `A`-length of `B / xB` for such a finite modification `A → B`.

The private lemmas used by the construction show further that either some local order of a
nonunit `x` is smaller than its order in `A`, or `S` has a unique maximal ideal, of residue degree
one; and that in the second case the order of the cofactor left after dividing by a nonunit
factor drops below the order of `x`.

## References

* [Stacks Project, Tag 0EAG](https://stacks.math.columbia.edu/tag/0EAG)
-/

@[expose] public section

open IsLocalRing

universe u v

namespace AlgebraicGeometry

/-- The elementary Euler-characteristic identity for a two-term endomorphism
of a finite-length module. -/
private theorem artinian_quotient_maximalIdeal_pow
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (n : ℕ) : IsArtinianRing (R ⧸ maximalIdeal R ^ (n + 1)) := by
  let I : Ideal R := maximalIdeal R ^ (n + 1)
  have hI : I ≠ ⊤ := by
    change maximalIdeal R ^ (n + 1) ≠ ⊤
    simp only [ne_eq, Ideal.pow_eq_top_iff, not_or]
    exact ⟨(IsLocalRing.maximalIdeal.isMaximal R).ne_top, Nat.succ_ne_zero n⟩
  let : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  let : IsLocalRing (R ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let : IsNoetherianRing (R ⧸ I) := inferInstance
  let : IsLocalHom (Ideal.Quotient.mk I) :=
    IsLocalHom.of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hmap : (maximalIdeal R).map (Ideal.Quotient.mk I) =
      maximalIdeal (R ⧸ I) := by
    ext x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp [sup_eq_left.mpr (IsLocalRing.le_maximalIdeal hI)]
  apply (isArtinianRing_iff_isNilpotent_maximalIdeal (R ⧸ I)).mpr
  refine ⟨n + 1, ?_⟩
  rw [← hmap, ← Ideal.map_pow, Ideal.zero_eq_bot,
    Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]

private theorem finiteLength_of_maximalIdeal_pow_annihilates
    {R M : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    {n : ℕ} (h : maximalIdeal R ^ n ≤ Module.annihilator R M) :
    IsFiniteLength R M := by
  let I : Ideal R := maximalIdeal R ^ (n + 1)
  have hI : I ≤ Module.annihilator R M :=
    (Ideal.pow_le_pow_right (Nat.le_succ n)).trans h
  have htor : Module.IsTorsionBySet R M (I : Set R) :=
    (Module.isTorsionBySet_iff_subset_annihilator R M).mpr hI
  let : Module (R ⧸ I) M := htor.module
  let : IsScalarTower R (R ⧸ I) M := htor.isScalarTower
  have : IsArtinianRing (R ⧸ I) := artinian_quotient_maximalIdeal_pow n
  have hfinite : Module.Finite (R ⧸ I) M :=
    Module.Finite.of_surjective htor.semilinearMap Function.surjective_id
  have : Module.Finite (R ⧸ I) M := hfinite
  have hArt : IsArtinian (R ⧸ I) M := inferInstance
  have hArtR : IsArtinian R M :=
    isArtinian_of_surjective_algebraMap (S := R) (R := R ⧸ I)
      (Ideal.Quotient.mk_surjective (I := I))
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, hArtR⟩

private theorem finiteLength_quotient_of_power_smul_range
    {A B : Type*} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsLocalRing A] [Algebra A B]
    [Module.Finite A B]
    {n : ℕ} (h : maximalIdeal A ^ n • (⊤ : Submodule A B) ≤
      LinearMap.range (Algebra.linearMap A B)) :
    IsFiniteLength A (B ⧸ LinearMap.range (Algebra.linearMap A B)) := by
  let C := B ⧸ LinearMap.range (Algebra.linearMap A B)
  have : Module.Finite A C :=
    Module.Finite.of_surjective (Submodule.mkQ _) (Submodule.mkQ_surjective _)
  have hAnn : maximalIdeal A ^ n ≤ Module.annihilator A C := by
    intro a ha
    apply Module.mem_annihilator.mpr
    intro c
    induction c using Submodule.Quotient.induction_on with
    | H b =>
        rw [← Submodule.Quotient.mk_smul]
        exact (Submodule.Quotient.mk_eq_zero _).mpr
          ((Submodule.smul_le.mp h) a ha b (by simp))
  exact finiteLength_of_maximalIdeal_pow_annihilates hAnn

/-- The length of `N ⧸ U` is the length of `P ⧸ S` plus that of the cokernel of `φ : P → N`, when
`S` is the preimage of `U ≤ range φ`. -/
private theorem length_quotient_eq_add_of_comap_le
    {R P N : Type*} [CommRing R] [AddCommGroup P] [Module R P]
    [AddCommGroup N] [Module R N]
    (φ : P →ₗ[R] N) (S : Submodule R P) (U : Submodule R N)
    (hSU : ∀ s ∈ S, φ s ∈ U) (hU : U ≤ φ.range) (hS : ∀ p, φ p ∈ U → p ∈ S) :
    Module.length R (N ⧸ U) =
      Module.length R (P ⧸ S) + Module.length R (N ⧸ φ.range) := by
  have hinj : Function.Injective (S.mapQ U φ hSU) := by
    intro z z' hz
    obtain ⟨m, rfl⟩ := S.mkQ_surjective z
    obtain ⟨m', rfl⟩ := S.mkQ_surjective z'
    apply (Submodule.Quotient.eq S).mpr
    have hmem : φ (m - m') ∈ U := by
      simpa only [map_sub] using (Submodule.Quotient.eq U).mp hz
    exact hS _ hmem
  refine Module.length_eq_add_of_exact (S.mapQ U φ hSU) (Submodule.factor hU) hinj
    (Submodule.factor_surjective hU) (LinearMap.exact_iff.mpr ?_)
  ext z
  obtain ⟨n, rfl⟩ := U.mkQ_surjective z
  change φ.range.mkQ n = 0 ↔ _
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨m, rfl⟩
    exact ⟨S.mkQ m, rfl⟩
  · rintro ⟨w, hw⟩
    obtain ⟨m, rfl⟩ := S.mkQ_surjective w
    obtain ⟨k, hk⟩ := hU ((Submodule.Quotient.eq U).mp hw)
    exact ⟨m - k, by rw [map_sub, hk]; abel⟩

/-- Quotient length is unchanged by an injective finite modification with finite-length
cokernel, when multiplication by the chosen element is injective upstairs. -/
private theorem length_quotient_eq_of_finite_cokernel
    {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (hf : Function.Injective f) (x : R)
    (hx : Function.Injective (LinearMap.lsmul R N x))
    (hC : IsFiniteLength R (N ⧸ f.range)) :
    Module.length R (M ⧸ (LinearMap.lsmul R M x).range) =
      Module.length R (N ⧸ (LinearMap.lsmul R N x).range) := by
  let gN := LinearMap.lsmul R N x
  let U := (gN.comp f).range
  have hUF : U ≤ f.range := by
    rintro y ⟨m, rfl⟩
    exact ⟨x • m, by simp [gN]⟩
  have hUT : U ≤ gN.range := by
    rintro y ⟨m, rfl⟩
    exact ⟨f m, rfl⟩
  have h₀ := length_quotient_eq_add_of_comap_le f (LinearMap.lsmul R M x).range U
    (by
      rintro y ⟨m, rfl⟩
      exact ⟨m, by simp [gN]⟩)
    hUF (fun m ⟨k, hk⟩ => ⟨k, hf (by simpa [gN] using hk)⟩)
  have h₁ := length_quotient_eq_add_of_comap_le gN f.range U
    (by
      rintro y ⟨m, rfl⟩
      exact ⟨m, rfl⟩)
    hUT (fun n ⟨m, hm⟩ => ⟨m, hx (by simpa [gN] using hm)⟩)
  have hfin : Module.length R (N ⧸ f.range) ≠ ⊤ := Module.length_ne_top_iff.mpr hC
  apply WithTop.add_right_cancel hfin
  exact h₀.symm.trans (h₁.trans (add_comm _ _))

/-- The range of multiplication by `x` on `B` is the ideal of `B` generated by the image of `x`. -/
private theorem range_lsmul_eq_span_restrictScalars
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] (x : A) :
    (LinearMap.lsmul A B x).range = (Ideal.span {algebraMap A B x}).restrictScalars A := by
  ext b
  rw [Submodule.restrictScalars_mem, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t, by simp [Algebra.smul_def, mul_comm]⟩
  · rintro ⟨t, rfl⟩
    exact ⟨t, by simp [Algebra.smul_def, mul_comm]⟩

theorem ord_eq_length_quotient_of_finite_modification
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [IsLocalRing A] [Module.Finite A B]
    (hinj : Function.Injective (algebraMap A B))
    {x : A} (hx : IsRegular (algebraMap A B x))
    {n : ℕ} (hquot : maximalIdeal A ^ n • (⊤ : Submodule A B) ≤
      LinearMap.range (Algebra.linearMap A B)) :
    Ring.ord A x =
      Module.length A (B ⧸ (LinearMap.lsmul A B x).range) := by
  have hfin := finiteLength_quotient_of_power_smul_range hquot
  have hreg : Function.Injective (LinearMap.lsmul A B x) := by
    intro b c h
    apply hx.left
    simpa [Algebra.smul_def] using h
  have hlen := length_quotient_eq_of_finite_cokernel
    (Algebra.linearMap A B) hinj x hreg hfin
  have hspan : (LinearMap.lsmul A A x).range = Ideal.span {x} := by
    simpa using range_lsmul_eq_span_restrictScalars A A x
  rw [hspan] at hlen
  exact hlen

private theorem ord_eq_length_quotient_span_of_finite_modification
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [IsLocalRing A] [Module.Finite A B]
    (hinj : Function.Injective (algebraMap A B))
    {x : A} (hx : IsRegular (algebraMap A B x))
    {n : ℕ} (hquot : maximalIdeal A ^ n • (⊤ : Submodule A B) ≤
      LinearMap.range (Algebra.linearMap A B)) :
    Ring.ord A x =
      Module.length A (B ⧸ Ideal.span {algebraMap A B x}) := by
  have h := ord_eq_length_quotient_of_finite_modification hinj hx hquot
  let I : Ideal B := Ideal.span {algebraMap A B x}
  have hFI := range_lsmul_eq_span_restrictScalars A B x
  calc
    Ring.ord A x = Module.length A (B ⧸ (LinearMap.lsmul A B x).range) := h
    _ = Module.length A (B ⧸ I.restrictScalars A) :=
      (Submodule.quotEquivOfEq _ _ hFI).length_eq
    _ = Module.length A (B ⧸ I) :=
      (Submodule.Quotient.restrictScalarsEquiv A I).length_eq

private theorem length_localized_quotient_eq
    {B : Type*} [CommRing B] (q : MaximalSpectrum B) (b : B) :
    Module.length (Localization.AtPrime q.asIdeal)
        (LocalizedModule q.asIdeal.primeCompl (B ⧸ Ideal.span {b})) =
      Module.length (Localization.AtPrime q.asIdeal)
        ((Localization.AtPrime q.asIdeal) ⧸
          Ideal.span {algebraMap B (Localization.AtPrime q.asIdeal) b}) := by
  let M := q.asIdeal.primeCompl
  let Bq := Localization.AtPrime q.asIdeal
  have hsub : Submodule.localized' Bq M (Algebra.linearMap B Bq)
      (Ideal.span {b}) = Ideal.span {algebraMap B Bq b} := by
    rw [Submodule.localized'_span]
    simp [Algebra.linearMap_apply, Ideal.span]
  have e : LocalizedModule M (B ⧸ Ideal.span {b}) ≃ₗ[B]
      (Bq ⧸ Submodule.localized' Bq M (Algebra.linearMap B Bq)
        (Ideal.span {b})) :=
    IsLocalizedModule.iso M
      (Submodule.toLocalizedQuotient' Bq M (Algebra.linearMap B Bq)
        (Ideal.span {b}))
  have e' : LocalizedModule M (B ⧸ Ideal.span {b}) ≃ₗ[Bq]
      (Bq ⧸ Submodule.localized' Bq M (Algebra.linearMap B Bq)
        (Ideal.span {b})) :=
    LinearEquiv.extendScalarsOfIsLocalization M Bq e
  rw [LinearEquiv.length_eq e', hsub]

private theorem finite_residueField_of_module_finite
    {A S : Type*} [CommRing A] [IsLocalRing A]
    [CommRing S] [Algebra A S] [Module.Finite A S]
    (q : MaximalSpectrum S) :
    letI : Algebra (maximalIdeal A).ResidueField q.asIdeal.ResidueField :=
      residueFieldAlgebra q.asIdeal
        ((eq_maximalIdeal
          (inferInstance : (q.asIdeal.under A).IsMaximal)).symm)
    Module.Finite (maximalIdeal A).ResidueField q.asIdeal.ResidueField := by
  let : Algebra (maximalIdeal A).ResidueField q.asIdeal.ResidueField :=
    residueFieldAlgebra q.asIdeal
      ((eq_maximalIdeal
        (inferInstance : (q.asIdeal.under A).IsMaximal)).symm)
  let : Module.Finite A q.asIdeal.ResidueField := Module.Finite.trans S _
  let : IsScalarTower A (maximalIdeal A).ResidueField q.asIdeal.ResidueField :=
    IsScalarTower.of_algebraMap_eq' (by
      ext a
      exact (Ideal.ResidueField.map_algebraMap (maximalIdeal A)
        q.asIdeal (algebraMap A S)
        ((eq_maximalIdeal
          (inferInstance : (q.asIdeal.under A).IsMaximal)).symm) a).symm)
  exact Module.Finite.of_restrictScalars_finite A _ _

private theorem length_eq_sum_finite_localizations
    {A S M : Type*} [CommRing A] [IsLocalRing A]
    [CommRing S] [Algebra A S] [Module.Finite A S]
    [AddCommGroup M] [Module S M] [Module A M] [IsScalarTower A S M]
    (hM : IsFiniteLength S M) :
    ∃ (n : ℕ) (m : Fin n → Ideal S)
      (hmax : ∀ i, (m i).IsMaximal)
      (_hinj : Function.Injective m)
      (_hsurj : ∀ I : Ideal S, I.IsMaximal → ∃ i, m i = I)
      (hlies : ∀ i, maximalIdeal A = (m i).comap (algebraMap A S)),
      letI : ∀ i, (m i).IsMaximal := hmax
      letI : ∀ i, Algebra (maximalIdeal A).ResidueField (m i).ResidueField :=
        fun i => residueFieldAlgebra (m i) (hlies i)
      ∃ (_hres : ∀ i,
          Module.Finite (maximalIdeal A).ResidueField (m i).ResidueField),
        Module.length A M =
          ∑ i : Fin n,
            (Module.finrank (maximalIdeal A).ResidueField (m i).ResidueField : ℕ∞) *
              Module.length (Localization.AtPrime (m i))
                (LocalizedModule (m i).primeCompl M) := by
  classical
  let : Finite (MaximalSpectrum S) :=
    Stacks.RingTheory.SemilocalModuleFinite.finite_maximalSpectrum_of_moduleFinite_of_isLocalRing
      A S
  let : Fintype (MaximalSpectrum S) := Fintype.ofFinite _
  let n := Fintype.card (MaximalSpectrum S)
  let e : Fin n ≃ MaximalSpectrum S := (Fintype.equivFin _).symm
  let m : Fin n → Ideal S := fun i => (e i).asIdeal
  have hmax (i : Fin n) : (m i).IsMaximal := (e i).isMaximal
  have hinj : Function.Injective m := fun _ _ hij => e.injective (MaximalSpectrum.ext hij)
  have hsurj : ∀ I : Ideal S, I.IsMaximal → ∃ i, m i = I := by
    intro I hI
    exact ⟨e.symm ⟨I, hI⟩, by simp [m]⟩
  have hlies (i : Fin n) : maximalIdeal A = (m i).comap (algebraMap A S) :=
    (eq_maximalIdeal
      (inferInstance : ((m i).under A).IsMaximal)).symm
  let : ∀ i, (m i).IsMaximal := hmax
  let : ∀ i, Algebra (maximalIdeal A).ResidueField (m i).ResidueField :=
    fun i => residueFieldAlgebra (m i) (hlies i)
  have hres (i : Fin n) :
      Module.Finite (maximalIdeal A).ResidueField (m i).ResidueField :=
    finite_residueField_of_module_finite (A := A) (S := S) (⟨m i, hmax i⟩ : MaximalSpectrum S)
  obtain ⟨_, hlen⟩ :=
    length_eq_sum_residue_degree_mul_localized_length n m hmax hinj hsurj hlies hM hres
  exact ⟨n, m, hmax, hinj, hsurj, hlies, hres, hlen⟩

private theorem ord_eq_sum_local_orders_of_finite_modification
    {A S : Type*} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [CommRing S] [Algebra A S] [Module.Finite A S]
    (hdim : ringKrullDim A = 1)
    (hinj : Function.Injective (algebraMap A S))
    {x : A} (hx : IsRegular (algebraMap A S x))
    {k : ℕ} (hquot : maximalIdeal A ^ k • (⊤ : Submodule A S) ≤
      LinearMap.range (Algebra.linearMap A S)) :
    ∃ (n : ℕ) (m : Fin n → Ideal S)
      (hmax : ∀ i, (m i).IsMaximal)
      (_hinjm : Function.Injective m)
      (_hsurj : ∀ I : Ideal S, I.IsMaximal → ∃ i, m i = I)
      (hlies : ∀ i, maximalIdeal A = (m i).comap (algebraMap A S)),
      letI : ∀ i, (m i).IsMaximal := hmax
      letI : ∀ i, Algebra (maximalIdeal A).ResidueField (m i).ResidueField :=
        fun i => residueFieldAlgebra (m i) (hlies i)
      ∃ (_hres : ∀ i,
          Module.Finite (maximalIdeal A).ResidueField (m i).ResidueField),
        Ring.ord A x =
          ∑ i : Fin n,
            (Module.finrank (maximalIdeal A).ResidueField (m i).ResidueField : ℕ∞) *
              Ring.ord (Localization.AtPrime (m i))
                (algebraMap S (Localization.AtPrime (m i)) (algebraMap A S x)) := by
  let : IsNoetherianRing S := IsNoetherianRing.of_finite A S
  let : Ring.KrullDimLE 1 S := Ring.krullDimLE_iff.mpr (by
    calc
      ringKrullDim S ≤ ringKrullDim A := ringKrullDim_le_of_integral
      _ = 1 := hdim)
  have hM : IsFiniteLength S (S ⧸ Ideal.span {algebraMap A S x}) :=
    isFiniteLength_quotient_span_singleton S hx.mem_nonZeroDivisors
  obtain ⟨n, m, hmax, hinjm, hsurj, hlies, hres, hlen⟩ :=
    length_eq_sum_finite_localizations (A := A) (S := S)
      (M := S ⧸ Ideal.span {algebraMap A S x}) hM
  let : ∀ i, (m i).IsMaximal := hmax
  let : ∀ i, Algebra (maximalIdeal A).ResidueField (m i).ResidueField :=
    fun i => residueFieldAlgebra (m i) (hlies i)
  refine ⟨n, m, hmax, hinjm, hsurj, hlies, hres, ?_⟩
  rw [ord_eq_length_quotient_span_of_finite_modification hinj hx hquot]
  calc
    Module.length A (S ⧸ Ideal.span {algebraMap A S x}) =
        ∑ i : Fin n,
          (Module.finrank (maximalIdeal A).ResidueField (m i).ResidueField : ℕ∞) *
            Module.length (Localization.AtPrime (m i))
              (LocalizedModule (m i).primeCompl
                (S ⧸ Ideal.span {algebraMap A S x})) := hlen
    _ = ∑ i : Fin n,
          (Module.finrank (maximalIdeal A).ResidueField (m i).ResidueField : ℕ∞) *
            Ring.ord (Localization.AtPrime (m i))
              (algebraMap S (Localization.AtPrime (m i)) (algebraMap A S x)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [length_localized_quotient_eq
          (q := (⟨m i, hmax i⟩ : MaximalSpectrum S))
          (b := algebraMap A S x)]
        rfl

private theorem ENat.term_lt_sum_of_other_positive
    {n : ℕ} (f : Fin n → ℕ∞) (i j : Fin n)
    (hij : i ≠ j) (hfin : ∑ k, f k ≠ ⊤) (hj : 0 < f j) :
    f i < ∑ k, f k := by
  have hle : f i ≤ ∑ k, f k :=
    Finset.single_le_sum_of_canonicallyOrdered (f := f) (s := Finset.univ) (by simp)
  have hfi : f i ≠ ⊤ := by
    intro htop
    exact hfin (top_le_iff.mp (htop ▸ hle))
  have hpair : f i + f j ≤ ∑ k, f k := by
    calc
      f i + f j = ∑ k ∈ ({i, j} : Finset (Fin n)), f k := by
        simp [hij]
      _ ≤ ∑ k, f k := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · simp
        · intro k hk hnot
          exact bot_le
  have hlt : f i < f i + f j := by
    simpa [add_comm] using ENat.lt_add_left hfi hj
  exact hlt.trans_le hpair

private theorem ENat.lt_mul_nat_of_one_lt
    (a : ℕ∞) (ha : 0 < a) (hfin : a ≠ ⊤)
    (n : ℕ) (hn : 1 < n) : a < (n : ℕ∞) * a := by
  have hmul := ENat.mul_left_strictMono (ne_of_gt ha) hfin
  simpa only [one_mul] using hmul (by exact_mod_cast hn : (1 : ℕ∞) < n)

private theorem ord_pos_of_not_isUnit
    {R : Type*} [CommRing R] {x : R} (hx : ¬ IsUnit x) :
    0 < Ring.ord R x := by
  have hproper : Ideal.span ({x} : Set R) ≠ ⊤ :=
    mt Ideal.span_singleton_eq_top.mp hx
  have : Nontrivial (R ⧸ Ideal.span ({x} : Set R)) :=
    Ideal.Quotient.nontrivial_iff.mpr hproper
  exact Module.length_pos

private theorem local_order_pos_of_nonunit_base
    {A S : Type*} [CommRing A] [IsLocalRing A]
    [CommRing S] [Algebra A S] [Module.Finite A S]
    (q : MaximalSpectrum S) {x : A} (hx : ¬ IsUnit x) :
    0 < Ring.ord (Localization.AtPrime q.asIdeal)
      (algebraMap S (Localization.AtPrime q.asIdeal) (algebraMap A S x)) := by
  let : IsLocalHom (algebraMap A (Localization.AtPrime q.asIdeal)) :=
    isLocalHom_atPrime_of_module_finite (A := A) (B := S) q
  apply ord_pos_of_not_isUnit
  rw [← IsScalarTower.algebraMap_apply A S (Localization.AtPrime q.asIdeal)]
  exact (isUnit_map_iff (algebraMap A (Localization.AtPrime q.asIdeal)) x).not.mpr hx

/-- The order of a nonzerodivisor of `A` that stays regular in a finite extension is finite. -/
private theorem ord_ne_top_of_injective_regular
    {A S : Type*} [CommRing A] [IsNoetherianRing A] [CommRing S] [Algebra A S]
    (hdim : ringKrullDim A = 1) (hinj : Function.Injective (algebraMap A S))
    {x : A} (hx : IsRegular (algebraMap A S x)) : Ring.ord A x ≠ ⊤ := by
  let : Ring.KrullDimLE 1 A := Ring.krullDimLE_iff.mpr (by rw [hdim]; exact le_rfl)
  exact Ring.ord_ne_top (mem_nonZeroDivisors_of_injective hinj hx.mem_nonZeroDivisors)

private theorem local_order_lt_base_of_other_maximal
    {A S : Type*} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [CommRing S] [Algebra A S] [Module.Finite A S]
    (hdim : ringKrullDim A = 1)
    (hinj : Function.Injective (algebraMap A S))
    {x : A} (hx : IsRegular (algebraMap A S x))
    (hnotx : ¬ IsUnit x)
    {k : ℕ} (hquot : maximalIdeal A ^ k • (⊤ : Submodule A S) ≤
      LinearMap.range (Algebra.linearMap A S))
    (q q' : MaximalSpectrum S) (hqq' : q ≠ q') :
    Ring.ord (Localization.AtPrime q.asIdeal)
      (algebraMap S (Localization.AtPrime q.asIdeal) (algebraMap A S x)) <
      Ring.ord A x := by
  classical
  obtain ⟨n, m, hmax, hm_inj, hsurj, hlies, hres, hformula⟩ :=
    ord_eq_sum_local_orders_of_finite_modification hdim hinj hx hquot
  let : ∀ i, (m i).IsMaximal := hmax
  let : ∀ i, Algebra (maximalIdeal A).ResidueField (m i).ResidueField :=
    fun i => residueFieldAlgebra (m i) (hlies i)
  obtain ⟨i, hi⟩ := hsurj q.asIdeal q.isMaximal
  obtain ⟨j, hj⟩ := hsurj q'.asIdeal q'.isMaximal
  have hij : i ≠ j := by
    intro hij
    apply hqq'
    apply MaximalSpectrum.ext
    calc
      q.asIdeal = m i := hi.symm
      _ = m j := by rw [hij]
      _ = q'.asIdeal := hj
  let f : Fin n → ℕ∞ := fun t =>
    (Module.finrank (maximalIdeal A).ResidueField (m t).ResidueField : ℕ∞) *
      Ring.ord (Localization.AtPrime (m t))
        (algebraMap S (Localization.AtPrime (m t)) (algebraMap A S x))
  have hdeg_ne (t : Fin n) :
      (Module.finrank (maximalIdeal A).ResidueField (m t).ResidueField : ℕ∞) ≠ 0 := by
    let : Module.Finite (maximalIdeal A).ResidueField (m t).ResidueField := hres t
    exact_mod_cast Module.finrank_pos.ne'
  have hpositive (t : Fin n) : 0 < f t :=
    (local_order_pos_of_nonunit_base (⟨m t, hmax t⟩ : MaximalSpectrum S) hnotx).trans_le
      (ENat.self_le_mul_left _ (hdeg_ne t))
  have hfin : ∑ t, f t ≠ ⊤ := by
    rw [← hformula]
    exact ord_ne_top_of_injective_regular hdim hinj hx
  have hlt : Ring.ord (Localization.AtPrime (m i))
      (algebraMap S (Localization.AtPrime (m i)) (algebraMap A S x)) <
      Ring.ord A x := by
    calc
      Ring.ord (Localization.AtPrime (m i))
          (algebraMap S (Localization.AtPrime (m i)) (algebraMap A S x)) ≤
          f i := ENat.self_le_mul_left _ (hdeg_ne i)
      _ < ∑ t, f t := ENat.term_lt_sum_of_other_positive f i j hij hfin (hpositive j)
      _ = Ring.ord A x := hformula.symm
  have hq : (⟨m i, hmax i⟩ : MaximalSpectrum S) = q := MaximalSpectrum.ext hi
  cases hq
  exact hlt

private theorem local_order_lt_base_of_residue_degree_gt_one
    {A S : Type*} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [CommRing S] [Algebra A S] [Module.Finite A S]
    (hdim : ringKrullDim A = 1)
    (hinj : Function.Injective (algebraMap A S))
    {x : A} (hx : IsRegular (algebraMap A S x))
    (hnotx : ¬ IsUnit x)
    {k : ℕ} (hquot : maximalIdeal A ^ k • (⊤ : Submodule A S) ≤
      LinearMap.range (Algebra.linearMap A S))
    (q : MaximalSpectrum S)
    (hdegree :
      letI : Algebra (maximalIdeal A).ResidueField q.asIdeal.ResidueField :=
        residueFieldAlgebra q.asIdeal
          ((eq_maximalIdeal
            (inferInstance : (q.asIdeal.under A).IsMaximal)).symm)
      1 < Module.finrank (maximalIdeal A).ResidueField q.asIdeal.ResidueField) :
    Ring.ord (Localization.AtPrime q.asIdeal)
      (algebraMap S (Localization.AtPrime q.asIdeal) (algebraMap A S x)) <
      Ring.ord A x := by
  classical
  obtain ⟨n, m, hmax, hm_inj, hsurj, hlies, hres, hformula⟩ :=
    ord_eq_sum_local_orders_of_finite_modification hdim hinj hx hquot
  let : ∀ i, (m i).IsMaximal := hmax
  let : ∀ i, Algebra (maximalIdeal A).ResidueField (m i).ResidueField :=
    fun i => residueFieldAlgebra (m i) (hlies i)
  obtain ⟨i, hi⟩ := hsurj q.asIdeal q.isMaximal
  have hq : (⟨m i, hmax i⟩ : MaximalSpectrum S) = q := MaximalSpectrum.ext hi
  cases hq
  let o : ℕ∞ := Ring.ord (Localization.AtPrime (m i))
    (algebraMap S (Localization.AtPrime (m i)) (algebraMap A S x))
  let d : ℕ := Module.finrank (maximalIdeal A).ResidueField (m i).ResidueField
  have hd : 1 < d := hdegree
  have ho : 0 < o :=
    local_order_pos_of_nonunit_base (⟨m i, hmax i⟩ : MaximalSpectrum S) hnotx
  have hterm_le : (d : ℕ∞) * o ≤ Ring.ord A x := by
    rw [hformula]
    exact Finset.single_le_sum_of_canonicallyOrdered
      (f := fun t : Fin n =>
        (Module.finrank (maximalIdeal A).ResidueField (m t).ResidueField : ℕ∞) *
          Ring.ord (Localization.AtPrime (m t))
            (algebraMap S (Localization.AtPrime (m t)) (algebraMap A S x)))
      (s := Finset.univ) (by simp)
  have hterm_fin : (d : ℕ∞) * o ≠ ⊤ := by
    intro ht
    exact ord_ne_top_of_injective_regular hdim hinj hx (top_le_iff.mp (ht ▸ hterm_le))
  have hofin : o ≠ ⊤ := by
    intro ht
    have hdne : (d : ℕ∞) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (lt_trans Nat.zero_lt_one hd))
    have hle : o ≤ (d : ℕ∞) * o := ENat.self_le_mul_left o hdne
    exact hterm_fin (top_le_iff.mp (ht ▸ hle))
  exact (ENat.lt_mul_nat_of_one_lt o ho hofin d hd).trans_le hterm_le

private theorem local_order_drop_or_unique_degree_one
    {A S : Type*} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [CommRing S] [Algebra A S] [Module.Finite A S]
    (hdim : ringKrullDim A = 1)
    (hinj : Function.Injective (algebraMap A S))
    {x : A} (hx : IsRegular (algebraMap A S x))
    (hnotx : ¬ IsUnit x)
    {k : ℕ} (hquot : maximalIdeal A ^ k • (⊤ : Submodule A S) ≤
      LinearMap.range (Algebra.linearMap A S))
    (q : MaximalSpectrum S) :
    Ring.ord (Localization.AtPrime q.asIdeal)
      (algebraMap S (Localization.AtPrime q.asIdeal) (algebraMap A S x)) <
        Ring.ord A x ∨
      (∀ q' : MaximalSpectrum S, q' = q) ∧
        (letI : Algebra (maximalIdeal A).ResidueField q.asIdeal.ResidueField :=
          residueFieldAlgebra q.asIdeal
            ((eq_maximalIdeal
              (inferInstance : (q.asIdeal.under A).IsMaximal)).symm)
         Module.finrank (maximalIdeal A).ResidueField q.asIdeal.ResidueField = 1) := by
  by_cases hdrop : Ring.ord (Localization.AtPrime q.asIdeal)
      (algebraMap S (Localization.AtPrime q.asIdeal) (algebraMap A S x)) <
        Ring.ord A x
  · exact Or.inl hdrop
  right
  constructor
  · intro q'
    by_contra hne
    exact hdrop (local_order_lt_base_of_other_maximal hdim hinj hx hnotx hquot
      q q' (Ne.symm hne))
  · let : Algebra (maximalIdeal A).ResidueField q.asIdeal.ResidueField :=
      residueFieldAlgebra q.asIdeal
        ((eq_maximalIdeal
          (inferInstance : (q.asIdeal.under A).IsMaximal)).symm)
    let : Module.Finite (maximalIdeal A).ResidueField q.asIdeal.ResidueField :=
      finite_residueField_of_module_finite (A := A) (S := S) q
    have hpos : 0 < Module.finrank (maximalIdeal A).ResidueField
        q.asIdeal.ResidueField := Module.finrank_pos
    have hle : ¬ 1 < Module.finrank (maximalIdeal A).ResidueField
        q.asIdeal.ResidueField := by
      intro hdegree
      exact hdrop (local_order_lt_base_of_residue_degree_gt_one
        hdim hinj hx hnotx hquot q hdegree)
    omega

private theorem finite_modification_order_dichotomy
    {A S : Type*} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [CommRing S] [Algebra A S] [Module.Finite A S]
    (hdim : ringKrullDim A = 1)
    (hinj : Function.Injective (algebraMap A S))
    {x : A} (hx : IsRegular (algebraMap A S x))
    (hnotx : ¬ IsUnit x)
    {k : ℕ} (hquot : maximalIdeal A ^ k • (⊤ : Submodule A S) ≤
      LinearMap.range (Algebra.linearMap A S)) :
    (∀ q : MaximalSpectrum S,
      Ring.ord (Localization.AtPrime q.asIdeal)
        (algebraMap S (Localization.AtPrime q.asIdeal)
          (algebraMap A S x)) < Ring.ord A x) ∨
    ∃ q : MaximalSpectrum S,
      (∀ q' : MaximalSpectrum S, q' = q) ∧
      (letI : Algebra (maximalIdeal A).ResidueField q.asIdeal.ResidueField :=
        residueFieldAlgebra q.asIdeal
          ((eq_maximalIdeal
            (inferInstance : (q.asIdeal.under A).IsMaximal)).symm)
       Module.finrank (maximalIdeal A).ResidueField q.asIdeal.ResidueField = 1) := by
  classical
  by_cases h : ∃ q : MaximalSpectrum S,
      (∀ q' : MaximalSpectrum S, q' = q) ∧
      (let this : Algebra (maximalIdeal A).ResidueField q.asIdeal.ResidueField :=
        residueFieldAlgebra q.asIdeal
          ((eq_maximalIdeal
            (inferInstance : (q.asIdeal.under A).IsMaximal)).symm)
       Module.finrank (maximalIdeal A).ResidueField q.asIdeal.ResidueField = 1)
  · exact Or.inr h
  · left
    intro q
    rcases local_order_drop_or_unique_degree_one hdim hinj hx hnotx hquot q with
      hdrop | ⟨huniq, hdegree⟩
    · exact hdrop
    · exact (h ⟨q, huniq, hdegree⟩).elim

private theorem local_order_eq_base_of_unique_degree_one
    {A S : Type*} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [CommRing S] [Algebra A S] [Module.Finite A S]
    (hdim : ringKrullDim A = 1)
    (hinj : Function.Injective (algebraMap A S))
    {x : A} (hx : IsRegular (algebraMap A S x))
    {k : ℕ} (hquot : maximalIdeal A ^ k • (⊤ : Submodule A S) ≤
      LinearMap.range (Algebra.linearMap A S))
    (q : MaximalSpectrum S) (huniq : ∀ q' : MaximalSpectrum S, q' = q)
    (hdegree :
      letI : Algebra (maximalIdeal A).ResidueField q.asIdeal.ResidueField :=
        residueFieldAlgebra q.asIdeal
          ((eq_maximalIdeal
            (inferInstance : (q.asIdeal.under A).IsMaximal)).symm)
      Module.finrank (maximalIdeal A).ResidueField q.asIdeal.ResidueField = 1) :
    Ring.ord (Localization.AtPrime q.asIdeal)
      (algebraMap S (Localization.AtPrime q.asIdeal) (algebraMap A S x)) =
      Ring.ord A x := by
  classical
  obtain ⟨n, m, hmax, hm_inj, hsurj, hlies, hres, hformula⟩ :=
    ord_eq_sum_local_orders_of_finite_modification hdim hinj hx hquot
  let : ∀ i, (m i).IsMaximal := hmax
  let : ∀ i, Algebra (maximalIdeal A).ResidueField (m i).ResidueField :=
    fun i => residueFieldAlgebra (m i) (hlies i)
  obtain ⟨i, hi⟩ := hsurj q.asIdeal q.isMaximal
  have hq : (⟨m i, hmax i⟩ : MaximalSpectrum S) = q := MaximalSpectrum.ext hi
  cases hq
  have hall (j : Fin n) : j = i :=
    hm_inj (congrArg MaximalSpectrum.asIdeal
      ((huniq ⟨m j, hmax j⟩).trans (huniq ⟨m i, hmax i⟩).symm))
  have hsum :
      (∑ j : Fin n,
        (Module.finrank (maximalIdeal A).ResidueField (m j).ResidueField : ℕ∞) *
          Ring.ord (Localization.AtPrime (m j))
            (algebraMap S (Localization.AtPrime (m j)) (algebraMap A S x))) =
      (Module.finrank (maximalIdeal A).ResidueField (m i).ResidueField : ℕ∞) *
        Ring.ord (Localization.AtPrime (m i))
          (algebraMap S (Localization.AtPrime (m i)) (algebraMap A S x)) := by
    apply Finset.sum_eq_single i
    · intro j hj hji
      exact (hji (hall j)).elim
    · simp
  rw [hsum] at hformula
  have hdeg : Module.finrank (maximalIdeal A).ResidueField
      (m i).ResidueField = 1 := hdegree
  simpa [hdeg] using hformula.symm

private theorem ord_lt_of_nonunit_factor
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    (hdim : ringKrullDim R = 1) {c d a : R}
    (ha : IsRegular a) (hd : a = c * d) (hnot : ¬ IsUnit d) :
    Ring.ord R c < Ring.ord R a := by
  let : Ring.KrullDimLE 1 R :=
    Ring.krullDimLE_iff.mpr (by rw [hdim]; exact le_rfl)
  have hcd : IsRegular (c * d) := hd ▸ ha
  have hc : IsRegular c := (isRegular_mul_iff.mp hcd).1
  have hdreg : IsRegular d := (isRegular_mul_iff.mp hcd).2
  rw [hd, Ring.ord_mul R hdreg.mem_nonZeroDivisors, add_comm]
  exact ENat.lt_add_left (Ring.ord_ne_top hc.mem_nonZeroDivisors)
    (ord_pos_of_not_isUnit hnot)

private theorem residual_local_order_lt_base_of_unique_degree_one
    {A T : Type*} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [CommRing T] [Algebra A T] [Module.Finite A T]
    (hdim : ringKrullDim A = 1)
    (hinj : Function.Injective (algebraMap A T))
    {x : A} (hx : IsRegular (algebraMap A T x))
    (hnotx : ¬ IsUnit x)
    {k : ℕ} (hquot : maximalIdeal A ^ k • (⊤ : Submodule A T) ≤
      LinearMap.range (Algebra.linearMap A T))
    (q : MaximalSpectrum T) (huniq : ∀ q' : MaximalSpectrum T, q' = q)
    (hdegree :
      letI : Algebra (maximalIdeal A).ResidueField q.asIdeal.ResidueField :=
        residueFieldAlgebra q.asIdeal
          ((eq_maximalIdeal
            (inferInstance : (q.asIdeal.under A).IsMaximal)).symm)
      Module.finrank (maximalIdeal A).ResidueField q.asIdeal.ResidueField = 1)
    {c d : Localization.AtPrime q.asIdeal}
    (hfac : algebraMap T (Localization.AtPrime q.asIdeal)
        (algebraMap A T x) = c * d)
    (hnotd : ¬ IsUnit d) :
    Ring.ord (Localization.AtPrime q.asIdeal) c < Ring.ord A x := by
  have hxq : IsRegular
      (algebraMap T (Localization.AtPrime q.asIdeal) (algebraMap A T x)) :=
    isRegular_iff_mem_nonZeroDivisors.mpr
      (IsLocalization.map_nonZeroDivisors_le q.asIdeal.primeCompl
        (Localization.AtPrime q.asIdeal)
        ⟨algebraMap A T x, hx.mem_nonZeroDivisors, rfl⟩)
  have hdimq : ringKrullDim (Localization.AtPrime q.asIdeal) = 1 :=
    local_dimension_one_of_integral hdim
      ((mem_maximalIdeal x).2 hnotx) hx q.asIdeal
  let : IsNoetherianRing T := IsNoetherianRing.of_finite A T
  have hlt := ord_lt_of_nonunit_factor hdimq hxq hfac hnotd
  exact hlt.trans_eq
    (local_order_eq_base_of_unique_degree_one hdim hinj hx hquot q huniq hdegree)

end AlgebraicGeometry
