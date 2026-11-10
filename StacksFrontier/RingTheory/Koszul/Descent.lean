module

public import Mathlib.RingTheory.Finiteness.Descent
public import Mathlib.RingTheory.Ideal.CotangentBaseChange
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import StacksFrontier.RingTheory.Flat.FaithfullyFlat.Descent
public import StacksFrontier.RingTheory.Ideal.CotangentBaseChangeMap
public import StacksFrontier.RingTheory.Koszul.Concatenation
public import StacksFrontier.RingTheory.Koszul.FlatBaseChange
public import StacksFrontier.RingTheory.Koszul.Homotopy
public import StacksFrontier.RingTheory.Koszul.Quasiregular
public import StacksFrontier.RingTheory.Koszul.Relations
public import StacksFrontier.RingTheory.MvPolynomial.GenericLinearForm
public import StacksFrontier.RingTheory.Regular.Ideal
public import StacksFrontier.RingTheory.Regular.Quasiregular
public import StacksFrontier.RingTheory.Sequence.QuasiRegular.Basic
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

/-!
# Descent and ascent of Koszul-regularity along flat maps

Let `A → B` be a homomorphism of commutative rings. This file collects the two results of
Section 15.30 of the Stacks Project which compare regularity over `A` with regularity over a
flat extension of `A`.

The first is *descent*: if `A → B` is faithfully flat and `I ⊆ A` is an ideal whose extension
`IB` is a Koszul-regular (resp. `H₁`-regular, resp. quasi-regular) ideal of `B`, then `I`
already has that property in `A`.

The second goes the other way and *improves* a sequence by passing to a flat extension: a
Koszul-regular sequence `f₁, …, f_n` generating a proper ideal becomes an honest regular
sequence after a generic invertible upper-triangular change of generators, carried out over the
faithfully flat smooth extension `S = A[t_ij ; i ≤ j][1/t₁₁, …, 1/t_nn]`.

## Main results

* `Koszul.regular_ideals_of_faithfullyFlat` (Stacks Tag 068N): faithfully flat descent for all
  three notions of regular ideal.
* `Koszul.isRegular_upperTriangular_of_isKoszulRegular` (Stacks Tag 068Q): the generic
  upper-triangular combinations `gᵢ = ∑_{j ≥ i} t_ij fⱼ` generate the extended ideal and form a
  regular sequence over `S`, which is faithfully flat and smooth over `A`.

## Implementation notes

The extension of an ideal along a ring homomorphism is expressed by `Ideal.map`, and the
several assertions of each tag are packaged as a conjunction so that one declaration records
the complete lemma.

The descent of Tag 068N is local on the base. A quasi-regular ideal is finitely generated with
finite projective conormal module (Tags 07CW and 08RK), so after localizing at a suitable
element `g` of `A` the conormal module becomes free and `I` acquires a generating sequence
whose length is its rank. Regularity of that sequence is then read off from the faithfully flat
base change `A_g → A_g ⊗_A B` through
`Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right`, applied both to the Koszul
homology and to the comparison map defining quasi-regularity. The naturality of that comparison
map in the module is established here as `barMap`/`srcMap`/`tgtMap` together with
`Koszul.quasiRegularCanonicalMap_srcMap`.

For Tag 068Q the ring `S` is presented as the localization of the polynomial ring on the
upper-triangular index set `{ij : Fin n × Fin n // ij.1 ≤ ij.2}` away from the product of the
diagonal variables. Splitting off the variables of the first row and inverting `t₁₁` separately
exhibits `S` as an iterated construction of the same shape, which turns the statement into an
induction on `n`: the first combination `g₁ = ∑ⱼ t_1j fⱼ` is a nonzerodivisor by Tag 068P, and
the remaining `gᵢ` are the generic upper-triangular combinations of the images of `f₂, …, f_n`
in the quotient by `g₁`.

## References

* [Stacks Project, Tag 068N](https://stacks.math.columbia.edu/tag/068N)
* [Stacks Project, Tag 068Q](https://stacks.math.columbia.edu/tag/068Q)
-/

namespace Koszul

/-! ## Tag 068N: faithfully flat descent of regular ideals -/

section FaithfullyFlatDescent

open CategoryTheory.Limits
open scoped TensorProduct

private lemma isZero_of_faithfullyFlat_baseChange
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S]
    (M : Type*) [AddCommGroup M] [Module R M]
    (h : Subsingleton (S ⊗[R] M)) : Subsingleton M :=
  (Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right R S).mp h

private lemma fg_of_isQuasiRegularIdeal_map
    {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (hf : f.FaithfullyFlat)
    (I : Ideal A) (hI : Quasiregular.IsQuasiregularIdeal' (I.map f)) : I.FG := by
  let := f.toAlgebra
  have : Module.FaithfullyFlat A B := hf
  exact Ideal.FG.of_FG_map_of_faithfullyFlat (S := B)
    (Quasiregular.isQuasiregularIdeal_fg hI)

open RingTheory.Sequence

private lemma cotangent_finite_projective_descends
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B] (I : Ideal A)
    [Module.Finite (B ⧸ I.map (algebraMap A B)) (I.map (algebraMap A B)).Cotangent]
    [Module.Projective (B ⧸ I.map (algebraMap A B)) (I.map (algebraMap A B)).Cotangent] :
    Module.Finite (A ⧸ I) I.Cotangent ∧ Module.Projective (A ⧸ I) I.Cotangent := by
  let J := I.map (algebraMap A B)
  have : Module.FaithfullyFlat (A ⧸ I) (B ⧸ J) :=
    Module.FaithfullyFlat.of_linearEquiv (A ⧸ I) ((A ⧸ I) ⊗[A] B)
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I).toLinearEquiv
  let e := Ideal.quotientTensorCotangentEquivMap (B := B) I
  have : Module.Finite (B ⧸ J) ((B ⧸ J) ⊗[A ⧸ I] I.Cotangent) := Module.Finite.equiv e.symm
  have : Module.Projective (B ⧸ J) ((B ⧸ J) ⊗[A ⧸ I] I.Cotangent) :=
    Module.Projective.of_equiv e.symm
  refine ⟨Module.Finite.of_finite_tensorProduct_of_faithfullyFlat (B ⧸ J), ?_⟩
  exact Module.Projective.of_finite_of_isBaseChange_of_faithfullyFlat
    (TensorProduct.mk (A ⧸ I) (B ⧸ J) I.Cotangent 1)
    (IsBaseChange.of_equiv (LinearEquiv.refl (B ⧸ J) _) (fun _ => rfl))

private lemma exists_basis_localizedModule_powers_of_projective
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] (p : PrimeSpectrum R) :
    ∃ g : R, g ∉ p.asIdeal ∧ ∃ r : ℕ,
      Nonempty (Module.Basis (Fin r) (Localization.Away g) (LocalizedModule.Away g M)) := by
  have : Module.FinitePresentation R M := Module.finitePresentation_of_projective R M
  let Rp := Localization.AtPrime p.asIdeal
  let Mp := LocalizedModule p.asIdeal.primeCompl M
  have : Module.Free Rp Mp := Module.free_of_flat_of_isLocalRing
  let b := Module.finBasis Rp Mp
  obtain ⟨g, hg, b', _⟩ := Module.FinitePresentation.exists_basis_localizedModule_powers
    p.asIdeal.primeCompl (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M) Rp b
  exact ⟨g, hg, _, ⟨b'⟩⟩

private lemma exists_notMem_and_map_eq_of_le_sup_sq
    {R : Type*} [CommRing R] (I J : Ideal R) (hI : I.FG) (hJI : J ≤ I)
    (h : I ≤ J ⊔ I ^ 2) (p : PrimeSpectrum R) (hp : I ≤ p.asIdeal) :
    ∃ g : R, g ∉ p.asIdeal ∧
      I.map (algebraMap R (Localization.Away g)) =
        J.map (algebraMap R (Localization.Away g)) := by
  obtain ⟨g, hg, hle⟩ := Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup
    (I := I) hI le_rfl (show I ≤ J ⊔ I • I by simpa [sq, smul_eq_mul] using h)
  refine ⟨g, ?_, le_antisymm ?_ (Ideal.map_mono hJI)⟩
  · intro hgp
    apply p.isPrime.one_notMem
    simpa using p.asIdeal.sub_mem hgp (hp hg)
  · apply Ideal.map_le_iff_le_comap.mpr
    intro x hx
    have hmul : g * x ∈ J := hle (Submodule.smul_mem_pointwise_smul x g I hx)
    have hm : algebraMap R (Localization.Away g) g * algebraMap R (Localization.Away g) x ∈
        J.map (algebraMap R (Localization.Away g)) := by
      simpa using Ideal.mem_map_of_mem (algebraMap R (Localization.Away g)) hmul
    obtain ⟨u, hu⟩ := (IsLocalization.Away.algebraMap_isUnit g :
      IsUnit (algebraMap R (Localization.Away g) g))
    simpa [← hu, ← mul_assoc] using
      (J.map (algebraMap R (Localization.Away g))).mul_mem_left (↑u⁻¹) hm

private lemma cotangent_finite_projective_of_isQuasiregularIdeal_map
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B] (I : Ideal A)
    (hI : Quasiregular.IsQuasiregularIdeal' (I.map (algebraMap A B))) :
    Module.Finite (A ⧸ I) I.Cotangent ∧ Module.Projective (A ⧸ I) I.Cotangent := by
  obtain ⟨hfin, hproj⟩ := Quasiregular.cotangent_finite_projective_of_quasiregular _ hI
  exact cotangent_finite_projective_descends (B := B) I

attribute [local instance] RingHomInvPair.of_ringEquiv in
private lemma free_tensorProduct_of_free_localizedModule
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (s : R) (T : Type*) [CommRing T] [Algebra R T] [IsLocalization.Away s T]
    [Module.Free (Localization.Away s) (LocalizedModule.Away s M)] :
    Module.Free T (T ⊗[R] M) := by
  let L := Localization.Away s
  let N := LocalizedModule.Away s M
  let e := IsLocalization.algEquiv (Submonoid.powers s) T L
  let : Module T N := Module.compHom N e.toRingHom
  have : IsScalarTower R T N := IsScalarTower.of_algebraMap_smul fun r m => by
    change e (algebraMap R T r) • m = r • m
    rw [e.commutes, IsScalarTower.algebraMap_smul L]
  let eN : LinearEquiv (e.symm.toRingEquiv : L →+* T)
      (σ' := (e.toRingEquiv : T →+* L)) N N :=
    { toFun := id
      invFun := id
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun r m => by
        change r • m = e (e.symm r) • m
        rw [e.apply_symm_apply] }
  have : Module.Free T N := Module.Free.of_equiv eN
  let b := IsLocalizedModule.isBaseChange (Submonoid.powers s) T
    (LocalizedModule.mkLinearMap (Submonoid.powers s) M)
  exact Module.Free.of_equiv b.equiv.symm

private lemma exists_notMem_free_cotangent_map
    {R : Type*} [CommRing R] (I : Ideal R)
    [Module.Finite (R ⧸ I) I.Cotangent] [Module.Projective (R ⧸ I) I.Cotangent]
    (p : PrimeSpectrum R) (hp : I ≤ p.asIdeal) :
    ∃ g : R, g ∉ p.asIdeal ∧
      Module.Free ((Localization.Away g) ⧸ I.map (algebraMap R (Localization.Away g)))
        (I.map (algebraMap R (Localization.Away g))).Cotangent := by
  let q : PrimeSpectrum (R ⧸ I) :=
    ⟨p.asIdeal.map (Ideal.Quotient.mk I),
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
        (by simpa using hp)⟩
  obtain ⟨s, hs, n, ⟨b⟩⟩ := exists_basis_localizedModule_powers_of_projective
    (M := I.Cotangent) q
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective s
  have hg : g ∉ p.asIdeal := fun h => hs (Ideal.mem_map_of_mem _ h)
  refine ⟨g, hg, ?_⟩
  let T := (Localization.Away g) ⧸ I.map (algebraMap R (Localization.Away g))
  have : IsLocalization.Away (Ideal.Quotient.mk I g) T := by
    change IsLocalization (Submonoid.powers (algebraMap R (R ⧸ I) g))
      ((Localization.Away g) ⧸ I.map (algebraMap R (Localization.Away g)))
    simpa only [Algebra.algebraMapSubmonoid_powers] using
      (IsLocalization.instQuotientIdealAlgebraMapSubmonoidMapRingHomAlgebraMap
        (Submonoid.powers g) (Localization.Away g) I)
  have : Module.Free (Localization.Away (Ideal.Quotient.mk I g))
      (LocalizedModule.Away (Ideal.Quotient.mk I g) I.Cotangent) := Module.Free.of_basis b
  have : Module.Free T (T ⊗[R ⧸ I] I.Cotangent) :=
    free_tensorProduct_of_free_localizedModule (Ideal.Quotient.mk I g) T
  exact Module.Free.of_equiv (Ideal.quotientTensorCotangentEquivMap (B := Localization.Away g) I)

private lemma le_span_sup_sq_of_span_cotangent_eq_top
    {R : Type*} [CommRing R] (I : Ideal R) {ι : Type*} (v : ι → I)
    (hv : Submodule.span (R ⧸ I) (Set.range fun i => I.toCotangent (v i)) = ⊤) :
    I ≤ Ideal.span (Set.range fun i => (v i : R)) ⊔ I ^ 2 := by
  let K := Submodule.span R (Set.range v)
  have hmap : K.map I.toCotangent = ⊤ := by
    apply top_unique
    intro z hz0
    have hz : z ∈ Submodule.span (R ⧸ I) (Set.range fun i => I.toCotangent (v i)) :=
      hv ▸ Submodule.mem_top
    clear hz0
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨i, rfl⟩ := hz
      exact ⟨v i, Submodule.subset_span ⟨i, rfl⟩, rfl⟩
    | zero => exact Submodule.zero_mem _
    | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      exact (K.map I.toCotangent).smul_mem a hx
  intro x hx
  have hm : I.toCotangent ⟨x, hx⟩ ∈ K.map I.toCotangent := hmap ▸ Submodule.mem_top
  obtain ⟨y, hy, hxy⟩ := hm
  apply Submodule.mem_sup.mpr
  refine ⟨y, ?_, x - y, ?_, by simp⟩
  · have : (y : R) ∈ K.map I.subtype := ⟨y, hy, rfl⟩
    change (y : R) ∈ Submodule.span R (Set.range fun i => (v i : R))
    convert this using 1
    simp only [K, Submodule.map_span, ← Set.range_comp, Function.comp_def,
      Submodule.subtype_apply]
  · rw [← Ideal.toCotangent_eq_zero I ⟨x - y, I.sub_mem hx y.2⟩]
    change I.toCotangent (⟨x, hx⟩ - y) = 0
    rw [map_sub, hxy, sub_self]

/-- The extension of the ideal spanned by `f` along `φ` is spanned by the images of `f`. -/
private lemma map_span_range {R S ι : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (f : ι → R) :
    (Ideal.span (Set.range f)).map φ = Ideal.span (Set.range fun i => φ (f i)) := by
  rw [Ideal.map_span, ← Set.range_comp]
  rfl

private lemma exists_notMem_generators_of_free_cotangent
    {R : Type*} [CommRing R] (I : Ideal R) (hI : I.FG)
    [Module.Free (R ⧸ I) I.Cotangent] (p : PrimeSpectrum R) (hp : I ≤ p.asIdeal) :
    ∃ g : R, g ∉ p.asIdeal ∧ ∃ (r : ℕ) (v : Fin r → I),
      (∃ b : Module.Basis (Fin r) (R ⧸ I) I.Cotangent,
        ∀ i, I.toCotangent (v i) = b i) ∧
      I.map (algebraMap R (Localization.Away g)) =
        Ideal.span (Set.range fun i => algebraMap R (Localization.Away g) (v i)) := by
  classical
  have : Module.Finite R I := Module.Finite.of_fg hI
  have : Module.Finite R I.Cotangent := Module.Finite.of_surjective
    I.toCotangent I.toCotangent_surjective
  have : Module.Finite (R ⧸ I) I.Cotangent := Module.Finite.of_restrictScalars_finite R (R ⧸ I) _
  have : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr
    (ne_top_of_le_ne_top p.isPrime.ne_top hp)
  let b := Module.finBasis (R ⧸ I) I.Cotangent
  choose v hv using fun i => I.toCotangent_surjective (b i)
  have hspan : Submodule.span (R ⧸ I) (Set.range fun i => I.toCotangent (v i)) = ⊤ := by
    simpa only [hv] using b.span_eq
  obtain ⟨g, hg, he⟩ := exists_notMem_and_map_eq_of_le_sup_sq I
    (Ideal.span (Set.range fun i => (v i : R))) hI
    (Ideal.span_le.mpr (Set.range_subset_iff.mpr fun i => (v i).2))
    (le_span_sup_sq_of_span_cotangent_eq_top I v hspan) p hp
  refine ⟨g, hg, _, v, ⟨b, hv⟩, ?_⟩
  simpa only [map_span_range] using he

set_option backward.isDefEq.respectTransparency false in
/-- The monomial basis identifies the two canonical maps defining quasi-regularity. -/
private theorem isMQuasiregularSeq_iff_bijective_canonicalMap
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {r : ℕ} (f : Fin r → R) :
    Quasiregular.IsMQuasiregularSeq M f ↔
      Function.Bijective (quasiRegularCanonicalMap (M := M) f) := by
  classical
  let e := TensorProduct.equivFinsuppOfBasisLeft (N := qrMbar M f)
    (MvPolynomial.basisMonomials (Fin r) (qrRbar f))
  have hmap :
      (Finsupp.lsum R fun d => phiMonoR (M := M) f d) =
        (quasiRegularCanonicalMap (M := M) f).restrictScalars R ∘ₗ
          e.symm.toLinearMap.restrictScalars R := by
    apply Finsupp.lhom_ext
    intro d m
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      LinearEquiv.coe_coe, Finsupp.lsum_single]
    change phiMonoR f d m = quasiRegularCanonicalMap f (e.symm (Finsupp.single d m))
    simp only [e, TensorProduct.equivFinsuppOfBasisLeft_symm_apply, Finsupp.sum_single_index,
      TensorProduct.tmul_zero]
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective (Jid f • (⊤ : Submodule R M)) m
    exact (canonicalMap_srcMono f d m).symm
  let q : (M ⧸ Quasiregular.jpow (Ideal.span (Set.range f)) M 1) ≃ₗ[R] qrMbar M f :=
    Submodule.quotEquivOfEq _ _ (by simp [Quasiregular.jpow, Jid])
  let qf : ((Fin r →₀ ℕ) →₀ (M ⧸ Quasiregular.jpow (Ideal.span (Set.range f)) M 1)) ≃ₗ[R]
      ((Fin r →₀ ℕ) →₀ qrMbar M f) := Finsupp.mapRange.linearEquiv q
  have hphi : Quasiregular.qregPhi (M := M) f =
      (Finsupp.lsum R fun d => phiMonoR (M := M) f d) ∘ₗ qf.toLinearMap := by
    apply Finsupp.lhom_ext
    intro d m
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective _ m
    change Quasiregular.qregPhi f (Finsupp.single d (Submodule.Quotient.mk m)) =
      (Finsupp.lsum R fun d => phiMonoR f d)
        (qf (Finsupp.single d (Submodule.Quotient.mk m)))
    have hq : qf (Finsupp.single d (Submodule.Quotient.mk m)) =
        Finsupp.single d (Submodule.Quotient.mk m) := by
      simp [qf, Finsupp.mapRange.linearEquiv_apply, q]
    rw [hq]
    simp only [Quasiregular.qregPhi, Finsupp.lsum_single, LinearMap.comp_apply]
    change DirectSum.lof R ℕ (fun n => Tcomp M f n) (d.sum fun _ k => k)
      (Submodule.Quotient.mk ⟨(∏ i, f i ^ d i) • m, _⟩) = imgTargetLin f d m
    have hd : d.sum (fun _ k => k) = qrMdeg d := by
      simp [Finsupp.sum_fintype, qrMdeg]
    have hl : ∀ (n : ℕ) (hm : (∏ i, f i ^ d i) • m ∈ JpowM M f n),
        n = qrMdeg d →
        DirectSum.lof R ℕ (fun n => Tcomp M f n) n
          (Submodule.Quotient.mk ⟨(∏ i, f i ^ d i) • m, hm⟩) =
        imgTargetLin f d m := by
      intro n hm hn
      subst n
      rfl
    exact hl _ _ hd
  change Function.Bijective (Quasiregular.qregPhi (M := M) f) ↔ _
  rw [hphi, hmap]
  exact (qf.bijective.of_comp_iff _).trans (e.symm.bijective.of_comp_iff _)

section CanonicalMapNaturality

variable {R : Type*} (S : Type*) [CommRing R] [CommRing S] [Algebra R S] {M N : Type*}
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
  {c : ℕ} (f : Fin c → R) (bc : M →ₗ[R] N)

private lemma srcFinsuppEquiv_srcMap (x : Source M f) :
    srcFinsuppEquiv N (fun i => algebraMap R S (f i)) (srcMap S f bc x) =
      Finsupp.mapRange.linearMap (barMap S f bc) (srcFinsuppEquiv M f x) := by
  change srcFinsuppEquiv N (fun i => algebraMap R S (f i))
    ((srcFinsuppEquiv N (fun i => algebraMap R S (f i))).symm _) = _
  exact LinearEquiv.apply_symm_apply _ _

end CanonicalMapNaturality

private lemma barMap_injective_of_comap_map_le
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {r : ℕ} (f : Fin r → R)
    (h : (Jid (fun i => algebraMap R S (f i))).comap (algebraMap R S) ≤ Jid f) :
    Function.Injective (barMap S f (Algebra.linearMap R S)) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
  simp only [Submodule.mkQ_apply] at hx ⊢
  rw [barMap_mk, Submodule.Quotient.mk_eq_zero] at hx
  rw [Submodule.Quotient.mk_eq_zero]
  simp only [Ideal.smul_eq_mul, Ideal.mul_top] at hx ⊢
  exact h hx

private lemma bijective_canonicalMap_of_comap_map_le
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {r : ℕ} (f : Fin r → R)
    (h : (Jid (fun i => algebraMap R S (f i))).comap (algebraMap R S) ≤ Jid f)
    (hreg : Function.Bijective
      (quasiRegularCanonicalMap (M := S) (fun i => algebraMap R S (f i)))) :
    Function.Bijective (quasiRegularCanonicalMap (M := R) f) := by
  have hb := barMap_injective_of_comap_map_le f h
  have hs : Function.Injective (srcMap S f (Algebra.linearMap R S)) := by
    intro x y hxy
    apply (srcFinsuppEquiv R f).injective
    ext d
    apply hb
    have hd := congrArg
      (fun z => srcFinsuppEquiv S (fun i => algebraMap R S (f i)) z d) hxy
    simpa only [srcFinsuppEquiv_srcMap, Finsupp.mapRange.linearMap_apply,
      Finsupp.mapRange_apply] using hd
  refine ⟨fun x y hxy => hs (hreg.injective ?_), quasiRegularCanonicalMap_surjective f⟩
  simp only [quasiRegularCanonicalMap_srcMap, hxy]

private lemma isQuasiregularSeq_of_faithfullyFlat
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S] {r : ℕ} (f : Fin r → R)
    (hreg : Quasiregular.IsQuasiregularSeq (fun i => algebraMap R S (f i))) :
    Quasiregular.IsQuasiregularSeq f := by
  apply (isMQuasiregularSeq_iff_bijective_canonicalMap f).mpr
  apply bijective_canonicalMap_of_comap_map_le (S := S) f _
    ((isMQuasiregularSeq_iff_bijective_canonicalMap _).mp hreg)
  have he : Jid (fun i => algebraMap R S (f i)) = (Jid f).map (algebraMap R S) := by
    simp only [Jid, map_span_range]
  rw [he, Ideal.comap_map_eq_self_of_faithfullyFlat]

private lemma isQuasiregularSeq_iff_isQuasiRegular
    {R : Type*} [CommRing R] {r : ℕ} (f : Fin r → R) :
    Quasiregular.IsQuasiregularSeq f ↔ IsQuasiRegular R (List.ofFn f) := by
  rw [Quasiregular.IsQuasiregularSeq, isMQuasiregularSeq_iff_bijective_canonicalMap]
  let P := fun s : Σ n, Fin n → R =>
    Function.Bijective (quasiRegularCanonicalMap (M := R) s.2)
  change P ⟨r, f⟩ ↔ P (List.equivSigmaTuple (List.equivSigmaTuple.symm ⟨r, f⟩))
  rw [Equiv.apply_symm_apply]

private lemma mem_of_forall_prime_exists_notMem_mul_mem
    {R : Type*} [CommRing R] (I : Ideal R) (x : R)
    (h : ∀ p : PrimeSpectrum R, I ≤ p.asIdeal →
      ∃ g : R, g ∉ p.asIdeal ∧ g * x ∈ I) : x ∈ I := by
  let K := I.colon (Ideal.span {x})
  have hIK : I ≤ K := fun a ha => Ideal.mem_colon_span_singleton.mpr (I.mul_mem_right x ha)
  have hK : K = ⊤ := by
    by_contra hK
    obtain ⟨p, hp, hKp⟩ := K.exists_le_maximal hK
    obtain ⟨g, hg, hgx⟩ := h ⟨p, hp.isPrime⟩ (hIK.trans hKp)
    exact hg (hKp (Ideal.mem_colon_span_singleton.mpr hgx))
  have : (1 : R) ∈ K := hK ▸ Submodule.mem_top
  simpa using Ideal.mem_colon_span_singleton.mp this

private lemma mem_of_forall_prime_exists_notMem_mem_map
    {R : Type*} [CommRing R] (I : Ideal R) (x : R)
    (h : ∀ p : PrimeSpectrum R, I ≤ p.asIdeal → ∃ g : R, g ∉ p.asIdeal ∧
      algebraMap R (Localization.Away g) x ∈ I.map (algebraMap R (Localization.Away g))) :
    x ∈ I := by
  refine mem_of_forall_prime_exists_notMem_mul_mem I x fun p hp => ?_
  obtain ⟨g, hg, hx⟩ := h p hp
  obtain ⟨s, ⟨n, rfl⟩, hs⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff
      (Submonoid.powers g) (Localization.Away g) I x).mp hx
  exact ⟨g ^ n, fun hgn => hg (p.isPrime.mem_of_pow_mem n hgn), hs⟩

private lemma bijective_canonicalMap_of_localizations
    {R : Type*} [CommRing R] {r : ℕ} (f : Fin r → R)
    (h : ∀ p : PrimeSpectrum R, Jid f ≤ p.asIdeal → ∃ g : R, g ∉ p.asIdeal ∧
      Function.Bijective (quasiRegularCanonicalMap (M := Localization.Away g)
        (fun i => algebraMap R (Localization.Away g) (f i)))) :
    Function.Bijective (quasiRegularCanonicalMap (M := R) f) := by
  refine ⟨(injective_iff_map_eq_zero _).mpr ?_, quasiRegularCanonicalMap_surjective f⟩
  intro x hx
  apply (srcFinsuppEquiv R f).injective
  change srcFinsuppEquiv R f x = (srcFinsuppEquiv R f).toLinearMap 0
  rw [LinearMap.map_zero]
  ext d
  obtain ⟨a, ha⟩ := Submodule.mkQ_surjective (Jid f • (⊤ : Submodule R R))
    (srcFinsuppEquiv R f x d)
  rw [Finsupp.zero_apply, ← ha, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  simp only [Ideal.smul_eq_mul, Ideal.mul_top]
  apply mem_of_forall_prime_exists_notMem_mem_map (Jid f) a
  intro p hp
  obtain ⟨g, hg, hreg⟩ := h p hp
  let S := Localization.Away g
  have hs : srcMap S f (Algebra.linearMap R S) x = 0 := by
    apply hreg.injective
    rw [quasiRegularCanonicalMap_srcMap, hx, map_zero, map_zero]
  have hd := congrArg
    (fun z => srcFinsuppEquiv S (fun i => algebraMap R S (f i)) z d) hs
  have hb : barMap S f (Algebra.linearMap R S) (Submodule.Quotient.mk a) = 0 := by
    rw [srcFinsuppEquiv_srcMap] at hd
    have hz : srcFinsuppEquiv S (fun i => algebraMap R S (f i)) 0 = 0 :=
      (srcFinsuppEquiv S (fun i => algebraMap R S (f i))).toLinearMap.map_zero
    rw [hz] at hd
    change barMap S f (Algebra.linearMap R S) (srcFinsuppEquiv R f x d) = 0 at hd
    simpa only [← ha, Submodule.mkQ_apply] using hd
  rw [barMap_mk, Submodule.Quotient.mk_eq_zero] at hb
  refine ⟨g, hg, ?_⟩
  change algebraMap R S a ∈ (Jid f).map (algebraMap R S)
  simpa only [Ideal.smul_eq_mul, Ideal.mul_top, Jid, map_span_range,
    Algebra.linearMap_apply] using hb

private lemma subsingleton_of_localizations_on_support
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) (hI : I ≤ Module.annihilator R M)
    (h : ∀ p : PrimeSpectrum R, I ≤ p.asIdeal → ∃ g : R, g ∉ p.asIdeal ∧
      Subsingleton (Localization.Away g ⊗[R] M)) : Subsingleton M := by
  apply subsingleton_of_forall_eq 0
  intro m
  let K : Ideal R := (⊥ : Submodule R M).colon {m}
  have hIK : I ≤ K := fun a ha =>
    Submodule.mem_colon_singleton.mpr (Module.mem_annihilator.mp (hI ha) m)
  have hK : K = ⊤ := by
    by_contra hK
    obtain ⟨p, hp, hKp⟩ := K.exists_le_maximal hK
    obtain ⟨g, hg, hs⟩ := h ⟨p, hp.isPrime⟩ (hIK.trans hKp)
    have hz : TensorProduct.mk R (Localization.Away g) M 1 m = 0 := hs.elim _ _
    obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers g)
      (TensorProduct.mk R (Localization.Away g) M 1)).mp hz
    obtain ⟨n, hn⟩ := s.2
    have hsp : (s : R) ∈ p := hKp ((Submodule.mem_colon_singleton).mpr hs)
    exact hg (hp.isPrime.mem_of_pow_mem n (by simpa only [← hn] using hsp))
  have hm : (1 : R) ∈ K := hK ▸ Submodule.mem_top
  simpa using Submodule.mem_colon_singleton.mp hm

/-- The Koszul homology of a sequence with coefficients in a module only depends on the module up
to linear equivalence. -/
lemma homologyTensor_equiv_of_linearEquiv
    {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {r : ℕ} (f : Fin r → R) (e : M ≃ₗ[R] N) (i : ℕ) :
    Nonempty ((Koszul.seqComplexTensor f M).homology i ≃ₗ[R]
      (Koszul.seqComplexTensor f N).homology i) := by
  apply KoszulC.homologyTransport_of_degreewiseEquiv
    (fun n => e.lTensor (⋀[R]^n (Fin r → R))) _ i
  intro n m x
  by_cases hnm : m + 1 = n
  · subst n
    rw [Koszul.seqComplexTensor_d, Koszul.seqComplexTensor_d]
    have he : (e.lTensor (⋀[R]^m (Fin r → R))).toLinearMap ∘ₗ
        (Koszul.d (Koszul.seqDual f) m).rTensor M =
      (Koszul.d (Koszul.seqDual f) m).rTensor N ∘ₗ
        (e.lTensor (⋀[R]^(m + 1) (Fin r → R))).toLinearMap := by
      apply TensorProduct.ext
      ext a b
      rfl
    exact LinearMap.congr_fun he x
  · rw [(Koszul.seqComplexTensor f M).shape n m hnm,
      (Koszul.seqComplexTensor f N).shape n m hnm]
    exact (e.lTensor (⋀[R]^m (Fin r → R))).toLinearMap.map_zero

/-- Koszul homology commutes with flat base change. -/
lemma koszulHomology_baseChange_equiv
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
    {r : ℕ} (f : Fin r → R) (i : ℕ) :
    Nonempty ((Koszul.seqComplex (fun j => algebraMap R S (f j))).homology i ≃ₗ[S]
      (S ⊗[R] (Koszul.seqComplex f).homology i)) := by
  obtain ⟨e₁⟩ := KoszulC.homology_baseChange_linearEquiv (S := S) f R i
  obtain ⟨e₂⟩ := homologyTensor_equiv_of_linearEquiv
    (fun j => algebraMap R S (f j)) (TensorProduct.AlgebraTensorModule.rid R S S) i
  exact ⟨((e₂.trans (Koszul.homologySelfIso _ i).toLinearEquiv).symm.trans e₁).trans
    (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S S)
      (Koszul.homologySelfIso f i).toLinearEquiv)⟩

private lemma isZero_koszulHomology_of_faithfullyFlat
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S] {r : ℕ} (f : Fin r → R) (i : ℕ)
    (h : IsZero ((Koszul.seqComplex (fun j => algebraMap R S (f j))).homology i)) :
    IsZero ((Koszul.seqComplex f).homology i) := by
  rw [ModuleCat.isZero_iff_subsingleton] at h ⊢
  obtain ⟨e⟩ := koszulHomology_baseChange_equiv (S := S) f i
  exact isZero_of_faithfullyFlat_baseChange (R := R) (S := S) _ e.symm.toEquiv.subsingleton

private lemma isZero_koszulHomology_of_localizations
    {R : Type*} [CommRing R] {r : ℕ} (f : Fin r → R) (i : ℕ)
    (h : ∀ p : PrimeSpectrum R, Jid f ≤ p.asIdeal → ∃ g : R, g ∉ p.asIdeal ∧
      IsZero ((Koszul.seqComplex
        (fun j => algebraMap R (Localization.Away g) (f j))).homology i)) :
    IsZero ((Koszul.seqComplex f).homology i) := by
  rw [ModuleCat.isZero_iff_subsingleton]
  refine subsingleton_of_localizations_on_support (Jid f)
    ((Koszul.koszulSeq_smul_nullHomotopic_and_span_le_annihilator f).2 i) fun p hp => ?_
  obtain ⟨g, hg, hreg⟩ := h p hp
  rw [ModuleCat.isZero_iff_subsingleton] at hreg
  obtain ⟨e⟩ := koszulHomology_baseChange_equiv (S := Localization.Away g) f i
  exact ⟨g, hg, e.symm.toEquiv.subsingleton⟩

private lemma length_eq_of_basis_cotangent
    {R : Type*} [CommRing R] (g : R) (I : Ideal (Localization.Away g))
    (hI : I ≠ ⊤) {r s : ℕ}
    (b : Module.Basis (Fin r) ((Localization.Away g) ⧸ I) I.Cotangent)
    (f : Fin s → Localization.Away g) (hf : Quasiregular.IsQuasiregularSeq f)
    (hspan : Ideal.span (Set.range f) = I) : r = s := by
  subst I
  have : Nontrivial ((Localization.Away g) ⧸ Ideal.span (Set.range f)) :=
    Ideal.Quotient.nontrivial_iff.mpr hI
  obtain ⟨e⟩ := Quasiregular.nonempty_cotangent_quot_pi_linearEquiv g f hf
  let b' := (Pi.basisFun ((Localization.Away g) ⧸ Ideal.span (Set.range f)) (Fin s)).map e
  simpa using (Module.finrank_eq_card_basis b).symm.trans (Module.finrank_eq_card_basis b')

private lemma map_ne_top_of_notMem
    {R : Type*} [CommRing R] (I : Ideal R) (p : PrimeSpectrum R)
    (hp : I ≤ p.asIdeal) (g : R) (hg : g ∉ p.asIdeal) :
    I.map (algebraMap R (Localization.Away g)) ≠ ⊤ := by
  intro htop
  have h1 : algebraMap R (Localization.Away g) 1 ∈
      I.map (algebraMap R (Localization.Away g)) := htop ▸ Submodule.mem_top
  obtain ⟨s, ⟨n, rfl⟩, hs⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff
      (Submonoid.powers g) (Localization.Away g) I 1).mp h1
  exact hg (p.isPrime.mem_of_pow_mem n (hp (by simpa using hs)))

private lemma isQuasiregularSeq_of_isH1Regular
    {R : Type*} [CommRing R] {r : ℕ} {f : Fin r → R} (hf : Koszul.IsH1Regular f) :
    Quasiregular.IsQuasiregularSeq f :=
  (isQuasiregularSeq_iff_isQuasiRegular f).mpr
    (Koszul.isQuasiRegular_of_isH1RegularOn ((Koszul.isH1RegularOn_self_iff f).mpr hf))

private lemma regularity_of_basis_cotangent_of_eq_span
    {R : Type*} [CommRing R] (g : R) (I : Ideal (Localization.Away g))
    (hI : I ≠ ⊤) {r s : ℕ}
    (b : Module.Basis (Fin r) ((Localization.Away g) ⧸ I) I.Cotangent)
    (f : Fin r → Localization.Away g) (hf : Ideal.span (Set.range f) = I)
    (t : Fin s → Localization.Away g) (ht : Ideal.span (Set.range t) = I)
    (htq : Quasiregular.IsQuasiregularSeq t) :
    Quasiregular.IsQuasiregularSeq f ∧
      (Koszul.IsH1Regular t → Koszul.IsH1Regular f) ∧
      (Koszul.IsKoszulRegular t → Koszul.IsKoszulRegular f) := by
  obtain rfl := length_eq_of_basis_cotangent g I hI b t htq ht
  obtain ⟨hq, hh, hk⟩ := Koszul.regularity_of_generators_of_eq_span_range I f hf
  exact ⟨(isQuasiregularSeq_iff_isQuasiRegular f).mpr
      (hq ⟨t, ht, (isQuasiregularSeq_iff_isQuasiRegular t).mp htq⟩),
    fun h => hh ⟨t, ht, h⟩, fun h => hk ⟨t, ht, h⟩⟩

private lemma regularity_of_basis_cotangent
    {R : Type*} [CommRing R] (I : Ideal R) {r : ℕ}
    (f : Fin r → R) (hf : Ideal.span (Set.range f) = I)
    (b : Module.Basis (Fin r) (R ⧸ I) I.Cotangent) :
    (Ideal.IsKoszulRegular I → Koszul.IsKoszulRegular f) ∧
      (Ideal.IsH1Regular I → Koszul.IsH1Regular f) ∧
      (Quasiregular.IsQuasiregularIdeal' I → Quasiregular.IsQuasiregularSeq f) := by
  have key {s : ℕ} (p : PrimeSpectrum R) (hp : I ≤ p.asIdeal) (g : R) (hg : g ∉ p.asIdeal)
      (t : Fin s → Localization.Away g)
      (htI : I.map (algebraMap R (Localization.Away g)) = Ideal.span (Set.range t))
      (htq : Quasiregular.IsQuasiregularSeq t) :=
    regularity_of_basis_cotangent_of_eq_span g _ (map_ne_top_of_notMem I p hp g hg)
      ((b.baseChange _).map (Ideal.quotientTensorCotangentEquivMap (B := Localization.Away g) I))
      _ (by rw [← hf, map_span_range]) t htI.symm htq
  refine ⟨?_, ?_, ?_⟩
  · intro hreg i hi
    apply isZero_koszulHomology_of_localizations f i
    intro p hp
    obtain ⟨g, hg, s, t, ht, htI⟩ := hreg p (hf ▸ hp)
    exact ⟨g, hg, (key p (hf ▸ hp) g hg t htI
      (isQuasiregularSeq_of_isH1Regular (ht 1 (by decide)))).2.2 ht i hi⟩
  · intro hreg
    apply isZero_koszulHomology_of_localizations f 1
    intro p hp
    obtain ⟨g, hg, s, t, ht, htI⟩ := hreg p (hf ▸ hp)
    exact ⟨g, hg, (key p (hf ▸ hp) g hg t htI (isQuasiregularSeq_of_isH1Regular ht)).2.1 ht⟩
  · intro hreg
    apply (isMQuasiregularSeq_iff_bijective_canonicalMap f).mpr
    apply bijective_canonicalMap_of_localizations f
    intro p hp
    obtain ⟨g, hg, s, t, ht, htI⟩ := hreg p (hf ▸ hp)
    exact ⟨g, hg,
      (isMQuasiregularSeq_iff_bijective_canonicalMap _).mp (key p (hf ▸ hp) g hg t htI ht).1⟩

private lemma flat_awayMap
    {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (hφ : φ.Flat) (g : R) :
    (IsLocalization.Away.map (Localization.Away g) (Localization.Away (φ g)) φ g).Flat := by
  algebraize [φ, IsLocalization.Away.map (Localization.Away g) (Localization.Away (φ g)) φ g]
  have : IsScalarTower R (Localization.Away g) (Localization.Away (φ g)) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      change algebraMap S (Localization.Away (φ g)) (φ x) =
        IsLocalization.Away.map (Localization.Away g) (Localization.Away (φ g)) φ g
          (algebraMap R (Localization.Away g) x)
      exact (IsLocalization.map_eq (M := Submonoid.powers g)
        (T := Submonoid.powers (φ g)) _ x).symm
  rw [RingHom.Flat, Module.flat_iff_of_isLocalization (Localization.Away g) (Submonoid.powers g)]
  exact Module.Flat.trans R S (Localization.Away (φ g))

set_option maxHeartbeats 800000 in
-- Comparing the localization maps requires reducing their induced algebra structures.
private lemma locally_generated_map
    {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (I : Ideal R)
    (P : ∀ g : R, ∀ r : ℕ, (Fin r → Localization.Away g) → Prop)
    (Q : ∀ g : S, ∀ r : ℕ, (Fin r → Localization.Away g) → Prop)
    (hPQ : ∀ g r f, P g r f → Q (φ g) r
      (fun i => IsLocalization.Away.map (Localization.Away g) (Localization.Away (φ g)) φ g (f i)))
    (hI : ∀ p : PrimeSpectrum R, I ≤ p.asIdeal → ∃ g : R, g ∉ p.asIdeal ∧
      ∃ r f, P g r f ∧ I.map (algebraMap R (Localization.Away g)) = Ideal.span (Set.range f)) :
    ∀ p : PrimeSpectrum S, I.map φ ≤ p.asIdeal → ∃ g : S, g ∉ p.asIdeal ∧
      ∃ r f, Q g r f ∧ (I.map φ).map (algebraMap S (Localization.Away g)) =
        Ideal.span (Set.range f) := by
  intro p hp
  obtain ⟨g, hg, r, f, hf, hspan⟩ := hI (PrimeSpectrum.comap φ p)
    (Ideal.map_le_iff_le_comap.mp hp)
  refine ⟨φ g, hg, r, _, hPQ g r f hf, ?_⟩
  let ψ := IsLocalization.Away.map (Localization.Away g) (Localization.Away (φ g)) φ g
  have hcomm : ψ.comp (algebraMap R (Localization.Away g)) =
      (algebraMap S (Localization.Away (φ g))).comp φ := by
    ext x
    exact IsLocalization.map_eq (M := Submonoid.powers g)
      (T := Submonoid.powers (φ g)) (by rintro _ ⟨n, rfl⟩; exact ⟨n, (φ.map_pow g n).symm⟩) x
  change (I.map φ).map (algebraMap S (Localization.Away (φ g))) =
    Ideal.span (Set.range (ψ ∘ f))
  rw [Set.range_comp, ← Ideal.map_span, ← hspan, Ideal.map_map, Ideal.map_map, hcomm]

private lemma isZero_koszulHomology_map_flat
    {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (hφ : φ.Flat)
    {r : ℕ} (f : Fin r → R) (i : ℕ)
    (h : IsZero ((Koszul.seqComplex f).homology i)) :
    IsZero ((Koszul.seqComplex (fun j => φ (f j))).homology i) := by
  let := φ.toAlgebra
  have : Module.Flat R S := hφ
  rw [ModuleCat.isZero_iff_subsingleton] at h ⊢
  obtain ⟨e⟩ := koszulHomology_baseChange_equiv (S := S) f i
  exact e.toEquiv.subsingleton

private lemma isQuasiregularSeq_map_flat
    {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (hφ : φ.Flat)
    {r : ℕ} (f : Fin r → R) (h : Quasiregular.IsQuasiregularSeq f) :
    Quasiregular.IsQuasiregularSeq (fun j => φ (f j)) := by
  let := φ.toAlgebra
  have : Module.Flat R S := hφ
  apply (isQuasiregularSeq_iff_isQuasiRegular _).mpr
  have hq := ((isQuasiregularSeq_iff_isQuasiRegular f).mp h).of_flat_of_isBaseChange
    (IsBaseChange.linearMap R S)
  simpa only [List.map_ofFn, Function.comp_def, RingHom.algebraMap_toAlgebra] using hq

/-- Koszul-regular, `H₁`-regular and quasi-regular ideals are preserved by a flat ring
homomorphism: the extension of such an ideal along a flat map is again of the same kind. -/
public theorem regularIdeals_map_flat
    {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (hφ : φ.Flat) (I : Ideal R) :
    (Ideal.IsKoszulRegular I → Ideal.IsKoszulRegular (I.map φ)) ∧
      (Ideal.IsH1Regular I → Ideal.IsH1Regular (I.map φ)) ∧
      (Quasiregular.IsQuasiregularIdeal' I →
        Quasiregular.IsQuasiregularIdeal' (I.map φ)) := by
  refine ⟨?_, ?_, ?_⟩
  · apply locally_generated_map φ I (fun _ _ f => Koszul.IsKoszulRegular f)
      (fun _ _ f => Koszul.IsKoszulRegular f)
    intro g r f hf i hi
    exact isZero_koszulHomology_map_flat _ (flat_awayMap φ hφ g) f i (hf i hi)
  · apply locally_generated_map φ I (fun _ _ f => Koszul.IsH1Regular f)
      (fun _ _ f => Koszul.IsH1Regular f)
    intro g r f hf
    exact isZero_koszulHomology_map_flat _ (flat_awayMap φ hφ g) f 1 hf
  · apply locally_generated_map φ I (fun _ _ f => Quasiregular.IsQuasiregularSeq f)
      (fun _ _ f => Quasiregular.IsQuasiregularSeq f)
    intro g r f hf
    exact isQuasiregularSeq_map_flat _ (flat_awayMap φ hφ g) f hf

private lemma exists_local_generators_basis_cotangent
    {R : Type*} [CommRing R] (I : Ideal R) (hI : I.FG)
    [Module.Finite (R ⧸ I) I.Cotangent] [Module.Projective (R ⧸ I) I.Cotangent]
    (p : PrimeSpectrum R) (hp : I ≤ p.asIdeal) :
    ∃ g : R, g ∉ p.asIdeal ∧ ∃ (r : ℕ) (f : Fin r → Localization.Away g),
      Ideal.span (Set.range f) = I.map (algebraMap R (Localization.Away g)) ∧
      Nonempty (Module.Basis (Fin r)
        ((Localization.Away g) ⧸ I.map (algebraMap R (Localization.Away g)))
        (I.map (algebraMap R (Localization.Away g))).Cotangent) := by
  classical
  obtain ⟨g, hg, hfree⟩ := exists_notMem_free_cotangent_map I p hp
  let S := Localization.Away g
  let J := I.map (algebraMap R S)
  have hd : Disjoint (Submonoid.powers g : Set R) (p.asIdeal : Set R) := by
    rw [Set.disjoint_left]
    rintro x ⟨n, rfl⟩ hx
    exact hg (p.isPrime.mem_of_pow_mem n hx)
  let q : PrimeSpectrum S := ⟨p.asIdeal.map (algebraMap R S),
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers g) S p.asIdeal p.isPrime hd⟩
  obtain ⟨h, hh, r, v, ⟨b, hb⟩, hgen⟩ := exists_notMem_generators_of_free_cotangent J
    (hI.map _) q (Ideal.map_mono hp)
  let T := Localization.Away h
  let a := (IsLocalization.Away.sec g h).1
  have hassoc : Associated (algebraMap R S a) h := by
    have he := IsLocalization.Away.sec_spec g h
    change h * algebraMap R S (g ^ (IsLocalization.Away.sec g h).2) =
      algebraMap R S a at he
    rw [← he]
    exact associated_mul_unit_left h _ (by
      rw [map_pow]
      exact (IsLocalization.Away.algebraMap_isUnit g : IsUnit (algebraMap R S g)).pow _)
  have ha : a ∉ p.asIdeal := fun ha =>
    hh ((q.asIdeal.mem_iff_of_associated hassoc).mp (Ideal.mem_map_of_mem _ ha))
  have : IsLocalization.Away (g * a) T := IsLocalization.Away.mul_of_associated g a h hassoc
  let U := Localization.Away (g * a)
  let e := IsLocalization.algEquiv (Submonoid.powers (g * a)) T U
  let : Algebra T U := e.toRingHom.toAlgebra
  have : IsScalarTower R T U := IsScalarTower.of_algebraMap_eq
    (R := R) (S := T) (A := U) fun x => (e.commutes x).symm
  have : Module.Flat T U := RingHom.Flat.of_bijective e.bijective
  let K := J.map (algebraMap S T)
  let bT := (b.baseChange (T ⧸ K)).map (Ideal.quotientTensorCotangentEquivMap (B := T) J)
  let bU := (bT.baseChange (U ⧸ K.map (algebraMap T U))).map
    (Ideal.quotientTensorCotangentEquivMap (B := U) K)
  have hmap : K.map (algebraMap T U) = I.map (algebraMap R U) := by
    simp only [K, J, Ideal.map_map]
    congr 1
    ext x
    simp only [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply]
  refine ⟨g * a, fun hga => (p.isPrime.mem_or_mem hga).elim hg ha, r,
    fun i => algebraMap T U (algebraMap S T (v i)), ?_, ?_⟩
  · rw [← hmap]
    change _ = (J.map (algebraMap S T)).map (algebraMap T U)
    rw [hgen, map_span_range]
  · change Nonempty (Module.Basis (Fin r) (U ⧸ I.map (algebraMap R U))
      (I.map (algebraMap R U)).Cotangent)
    rw [← hmap]
    exact ⟨bU⟩

private lemma regularity_of_local_conormal_basis
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [Module.FaithfullyFlat A B]
    (I : Ideal A) (g : A) {r : ℕ} (t : Fin r → Localization.Away g)
    (ht : Ideal.span (Set.range t) = I.map (algebraMap A (Localization.Away g)))
    (b : Module.Basis (Fin r)
      ((Localization.Away g) ⧸ I.map (algebraMap A (Localization.Away g)))
      (I.map (algebraMap A (Localization.Away g))).Cotangent) :
    (Ideal.IsKoszulRegular (I.map (algebraMap A B)) → Koszul.IsKoszulRegular t) ∧
      (Ideal.IsH1Regular (I.map (algebraMap A B)) → Koszul.IsH1Regular t) ∧
      (Quasiregular.IsQuasiregularIdeal' (I.map (algebraMap A B)) →
        Quasiregular.IsQuasiregularSeq t) := by
  let R := Localization.Away g
  let S := R ⊗[A] B
  let : Algebra B S := Algebra.TensorProduct.rightAlgebra
  have : Module.FaithfullyFlat R S := inferInstance
  have : IsLocalization (Algebra.algebraMapSubmonoid B (Submonoid.powers g)) S :=
    inferInstance
  have hflat : (algebraMap B S).Flat :=
    RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat S
      (Algebra.algebraMapSubmonoid B (Submonoid.powers g)))
  let J := I.map (algebraMap A R)
  let K := J.map (algebraMap R S)
  have he : (I.map (algebraMap A B)).map (algebraMap B S) = K := by
    dsimp only [K, J]
    rw [Ideal.map_map, Ideal.map_map, ← IsScalarTower.algebraMap_eq,
      ← IsScalarTower.algebraMap_eq]
  let bS := (b.baseChange (S ⧸ K)).map (Ideal.quotientTensorCotangentEquivMap (B := S) J)
  have hgen : Ideal.span (Set.range fun i => algebraMap R S (t i)) = K := by
    change _ = (I.map (algebraMap A R)).map (algebraMap R S)
    rw [← ht, map_span_range]
  obtain ⟨hk, hh, hq⟩ := regularity_of_basis_cotangent K _ hgen bS
  obtain ⟨hak, hah, haq⟩ := regularIdeals_map_flat (algebraMap B S) hflat (I.map (algebraMap A B))
  rw [he] at hak hah haq
  exact ⟨fun h i hi => isZero_koszulHomology_of_faithfullyFlat (S := S) t i (hk (hak h) i hi),
    fun h => isZero_koszulHomology_of_faithfullyFlat (S := S) t 1 (hh (hah h)),
    fun h => isQuasiregularSeq_of_faithfullyFlat (S := S) t (hq (haq h))⟩

/-- **Stacks 068N.** Koszul-regular, `H₁`-regular, and quasi-regular ideals descend along a
faithfully flat homomorphism of commutative rings. -/
@[stacks 068N, sga "6 VII 1.5" "converse, affine case"]
public theorem regular_ideals_of_faithfullyFlat
    {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (hf : f.FaithfullyFlat)
    (I : Ideal A) :
    (Ideal.IsKoszulRegular (I.map f) → Ideal.IsKoszulRegular I) ∧
      (Ideal.IsH1Regular (I.map f) → Ideal.IsH1Regular I) ∧
      (Quasiregular.IsQuasiregularIdeal' (I.map f) →
        Quasiregular.IsQuasiregularIdeal' I) := by
  let := f.toAlgebra
  have : Module.FaithfullyFlat A B := hf
  have hlocal (hI : Quasiregular.IsQuasiregularIdeal' (I.map f))
      (p : PrimeSpectrum A) (hp : I ≤ p.asIdeal) :
      ∃ g : A, g ∉ p.asIdeal ∧ ∃ (r : ℕ) (t : Fin r → Localization.Away g),
        Ideal.span (Set.range t) = I.map (algebraMap A (Localization.Away g)) ∧
        (Ideal.IsKoszulRegular (I.map f) → Koszul.IsKoszulRegular t) ∧
        (Ideal.IsH1Regular (I.map f) → Koszul.IsH1Regular t) ∧
        (Quasiregular.IsQuasiregularIdeal' (I.map f) →
          Quasiregular.IsQuasiregularSeq t) := by
    have hfg := fg_of_isQuasiRegularIdeal_map f hf I hI
    obtain ⟨hfin, hproj⟩ := cotangent_finite_projective_of_isQuasiregularIdeal_map
      (B := B) I hI
    obtain ⟨g, hg, r, t, ht, ⟨b⟩⟩ := exists_local_generators_basis_cotangent I hfg p hp
    exact ⟨g, hg, r, t, ht, regularity_of_local_conormal_basis (B := B) I g t ht b⟩
  refine ⟨?_, ?_, ?_⟩
  · intro h p hp
    obtain ⟨g, hg, r, t, ht, hk, _⟩ := hlocal h.isQuasiregular p hp
    exact ⟨g, hg, r, t, hk h, ht.symm⟩
  · intro h p hp
    obtain ⟨g, hg, r, t, ht, _, hh, _⟩ := hlocal h.isQuasiregular p hp
    exact ⟨g, hg, r, t, hh h, ht.symm⟩
  · intro h p hp
    obtain ⟨g, hg, r, t, ht, _, _, hq⟩ := hlocal h p hp
    exact ⟨g, hg, r, t, hq h, ht.symm⟩

end FaithfullyFlatDescent

/-! ## Tag 068Q: the generic upper-triangular change of generators -/

section UpperTriangular

universe u v

open Matrix CategoryTheory
open scoped ExteriorAlgebra TensorProduct

private theorem faithfullyFlat_of_retraction {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Module.Flat R S] (e : S →ₐ[R] R) : Module.FaithfullyFlat R S := by
  apply Module.FaithfullyFlat.of_comap_surjective
  intro p
  refine ⟨PrimeSpectrum.comap e.toRingHom p, ?_⟩
  ext x
  change e (algebraMap R S x) ∈ p.asIdeal ↔ x ∈ p.asIdeal
  simp

private theorem span_mulVec_le {R ι κ : Type*} [CommRing R] [Fintype κ]
    (A : Matrix ι κ R) (f : κ → R) :
    Ideal.span (Set.range (A *ᵥ f)) ≤ Ideal.span (Set.range f) := by
  refine Ideal.span_le.mpr ?_
  rintro _ ⟨i, rfl⟩
  exact Ideal.sum_mem _ fun j _ ↦ Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)

private theorem span_mulVec_of_isUnit {R ι : Type*} [CommRing R] [Fintype ι]
    [DecidableEq ι] (A : Matrix ι ι R) (hA : IsUnit A) (f : ι → R) :
    Ideal.span (Set.range (A *ᵥ f)) = Ideal.span (Set.range f) := by
  obtain ⟨u, rfl⟩ := hA
  apply le_antisymm (span_mulVec_le _ _)
  have h := span_mulVec_le (↑u⁻¹ : Matrix ι ι R) ((u : Matrix ι ι R) *ᵥ f)
  simpa [Matrix.mulVec_mulVec] using h

private theorem faithfullyFlat_away_prod_X {R σ ι : Type*} [CommRing R]
    [Fintype ι] (v : ι → σ) :
    Module.FaithfullyFlat R
      (Localization.Away (∏ i, MvPolynomial.X (v i) : MvPolynomial σ R)) := by
  classical
  let P := MvPolynomial σ R
  let d : P := ∏ i, MvPolynomial.X (v i)
  let S := Localization.Away d
  have : Module.Flat R S := Module.Flat.trans R P S
  let e : P →ₐ[R] R := MvPolynomial.aeval (fun _ ↦ 1)
  have hd : e d = 1 := by
    change e (∏ i, MvPolynomial.X (v i)) = 1
    rw [map_prod]
    exact Finset.prod_eq_one fun i _ => MvPolynomial.aeval_X (R := R) (fun _ : σ ↦ (1 : R)) (v i)
  exact faithfullyFlat_of_retraction
    (IsLocalization.Away.liftAlgHom d (hd ▸ isUnit_one) : S →ₐ[R] R)

private theorem smooth_away_prod_X {R σ ι : Type*} [CommRing R]
    [_root_.Finite σ] [Fintype ι] (v : ι → σ) :
    Algebra.Smooth R
      (Localization.Away (∏ i, MvPolynomial.X (v i) : MvPolynomial σ R)) := by
  classical
  let : Algebra.Smooth R (MvPolynomial σ R) := {}
  let d : MvPolynomial σ R := ∏ i, MvPolynomial.X (v i)
  let : Algebra.Smooth (MvPolynomial σ R) (Localization.Away d) :=
    Algebra.Smooth.of_isLocalization_Away d
  exact Algebra.Smooth.comp R (MvPolynomial σ R) _

private theorem span_upperTriangular_of_isLocalization
    {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}
    [Algebra R S]
    [Algebra (MvPolynomial {ij : Fin n × Fin n // ij.1 ≤ ij.2} R) S]
    [IsScalarTower R (MvPolynomial {ij : Fin n × Fin n // ij.1 ≤ ij.2} R) S]
    [IsLocalization.Away
      (∏ i : Fin n, MvPolynomial.X ⟨(i, i), le_rfl⟩ :
        MvPolynomial {ij : Fin n × Fin n // ij.1 ≤ ij.2} R) S]
    (f : Fin n → R) :
    Ideal.map (algebraMap R S) (Ideal.span (Set.range f)) =
      Ideal.span (Set.range fun i : Fin n ↦
        ∑ j : Fin n, if hij : i ≤ j then
          algebraMap (MvPolynomial {ij : Fin n × Fin n // ij.1 ≤ ij.2} R) S
            (MvPolynomial.X ⟨(i, j), hij⟩) * algebraMap R S (f j)
        else 0) := by
  classical
  let P := MvPolynomial {ij : Fin n × Fin n // ij.1 ≤ ij.2} R
  let d : P := ∏ i : Fin n, MvPolynomial.X ⟨(i, i), le_rfl⟩
  let A : Matrix (Fin n) (Fin n) S := fun i j ↦
    if hij : i ≤ j then algebraMap P S (MvPolynomial.X ⟨(i, j), hij⟩) else 0
  have htri : A.IsUpperTriangular := fun i j hij => dite_eq_right (not_le.mpr hij)
  have hdet : IsUnit A.det := by
    rw [Matrix.det_of_isUpperTriangular htri]
    simpa [A, d, map_prod] using (IsLocalization.Away.algebraMap_isUnit d (S := S))
  have hunit : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).mpr hdet
  have hspan := span_mulVec_of_isUnit A hunit (fun i ↦ algebraMap R S (f i))
  rw [map_span_range]
  have heq : A *ᵥ (fun i ↦ algebraMap R S (f i)) =
      (fun i ↦ ∑ j : Fin n, if hij : i ≤ j then
        algebraMap P S (MvPolynomial.X ⟨(i, j), hij⟩) * algebraMap R S (f j) else 0) := by
    funext i
    change (∑ j, A i j * algebraMap R S (f j)) = _
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [A]
    split <;> simp_all
  rw [heq] at hspan
  exact hspan.symm

public theorem annihilator_eq_zero_of_isKoszulRegular {R : Type*} [CommRing R]
    {n : ℕ} (f : Fin (n + 1) → R) (hf : Koszul.IsKoszulRegular f)
    (x : R) (hx : ∀ i, x * f i = 0) : x = 0 := by
  classical
  have hφ : x • Koszul.seqDual f = 0 := by
    apply LinearMap.ext
    intro v
    simp only [LinearMap.smul_apply, Koszul.seqDual_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_eq_zero
    intro i _
    rw [mul_left_comm, hx i, mul_zero]
  have hd (w : ⋀[R]^(n + 1) (Fin (n + 1) → R)) :
      Koszul.d (Koszul.seqDual f) n (x • w) = 0 := by
    apply Subtype.ext
    change Koszul.contraction (Koszul.seqDual f) (x • (w : ExteriorAlgebra R _)) = 0
    rw [map_smul]
    change (x • (CliffordAlgebra.contractLeft (Koszul.seqDual f))) (w : ExteriorAlgebra R _) = 0
    rw [← map_smul, hφ, map_zero, LinearMap.zero_apply]
  have he := (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr (hf (n + 1) (by omega))
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff_ker_sub_range] at he
  simp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor'_obj_g,
    HomologicalComplex.shortComplexFunctor'_obj_f, Koszul.seqComplex_d] at he
  change LinearMap.ker (Koszul.d (Koszul.seqDual f) n) ≤
    LinearMap.range (Koszul.d (Koszul.seqDual f) (n + 1)) at he
  let b := Pi.basisFun R (Fin (n + 1))
  have : Subsingleton (⋀[R]^(n + 2) (Fin (n + 1) → R)) :=
    exteriorPower.subsingleton_of_span_eq_top_of_card_lt b b.span_eq _ (by simp)
  have hr : LinearMap.range (Koszul.d (Koszul.seqDual f) (n + 1)) = ⊥ := by
    have hz : Koszul.d (Koszul.seqDual f) (n + 1) = 0 := Subsingleton.elim _ _
    rw [hz, LinearMap.range_zero]
  rw [hr] at he
  let t : Set.powersetCard (Fin (n + 1)) (n + 1) := ⟨Finset.univ, by simp⟩
  have hz : x • (b.exteriorPower (n + 1)) t = 0 := he (hd _)
  simpa using congrArg (fun w ↦ (b.exteriorPower (n + 1)).repr w t) hz

private theorem isKoszulRegular_algebraMap
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
    {n : ℕ} (f : Fin n → R) (hf : Koszul.IsKoszulRegular f) :
    Koszul.IsKoszulRegular (fun i ↦ algebraMap R S (f i)) := fun i hi =>
  isZero_koszulHomology_map_flat (algebraMap R S)
    (RingHom.flat_algebraMap_iff.mpr inferInstance) f i (hf i hi)

private theorem isKoszulRegular_singleton_of_isSMulRegular
    {R : Type*} [CommRing R] (f : Fin 1 → R) (hf : IsSMulRegular R (f 0)) :
    Koszul.IsKoszulRegular f := by
  intro i hi
  rcases i with _ | _ | i
  · contradiction
  · apply (Koszul.isH1Regular_iff_ker_le_relSpan f).mpr
    intro v hv
    have hv0 : v 0 * f 0 = 0 := by
      simpa [Koszul.seqDual_apply] using hv
    have hvz : v = 0 := by
      ext j
      obtain rfl : j = 0 := Subsingleton.elim _ _
      apply (isSMulRegular_iff_right_eq_zero_of_smul.mp hf)
      simpa [smul_eq_mul, mul_comm] using hv0
    simp [hvz]
  · apply HomologicalComplex.ExactAt.isZero_homology
    apply HomologicalComplex.ExactAt.of_isZero
    apply ModuleCat.isZero_iff_subsingleton.mpr
    exact exteriorPower.subsingleton_of_span_eq_top_of_card_lt
      (Pi.basisFun R (Fin 1)) (Pi.basisFun R (Fin 1)).span_eq _ (by simp)

private theorem span_cons_sum_of_isUnit {R : Type*} [CommRing R] {n : ℕ}
    (f c : Fin (n + 1) → R) (hc : IsUnit (c 0)) :
    Ideal.span (Set.range (Fin.cons (∑ i, c i * f i) (Fin.tail f))) =
      Ideal.span (Set.range f) := by
  classical
  let g := Fin.cons (∑ i, c i * f i) (Fin.tail f)
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp only [Fin.cons_zero]
      exact Ideal.sum_mem _ fun j _ ↦ Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)
    · exact Ideal.subset_span ⟨j.succ, rfl⟩
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · have hsum : (∑ i, c i * f i) ∈ Ideal.span (Set.range g) :=
        Ideal.subset_span ⟨0, rfl⟩
      have htail : (∑ i : Fin n, c i.succ * f i.succ) ∈ Ideal.span (Set.range g) :=
        Ideal.sum_mem _ fun j _ ↦ Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j.succ, rfl⟩)
      have hmul : c 0 * f 0 ∈ Ideal.span (Set.range g) := by
        rw [Fin.sum_univ_succ] at hsum
        exact ((Ideal.span (Set.range g)).add_mem_iff_left htail).mp hsum
      obtain ⟨u, hu⟩ := hc
      rw [← hu] at hmul
      change f 0 ∈ Ideal.span (Set.range g)
      simpa [mul_assoc] using Ideal.mul_mem_left (Ideal.span (Set.range g)) (↑u⁻¹ : R) hmul
    · exact Ideal.subset_span ⟨j.succ, rfl⟩

private theorem isKoszulRegular_cons_sum_of_isUnit
    {R : Type*} [CommRing R] {n : ℕ} (f c : Fin (n + 1) → R)
    (hf : Koszul.IsKoszulRegular f) (hc : IsUnit (c 0)) :
    Koszul.IsKoszulRegular (Fin.cons (∑ i, c i * f i) (Fin.tail f)) :=
  (Koszul.regularity_of_generators_of_eq_span_range
    (Ideal.span (Set.range f)) _ (span_cons_sum_of_isUnit f c hc)).2.2 ⟨f, rfl, hf⟩

private theorem isKoszulRegular_cast {R : Type*} [CommRing R] {m n : ℕ}
    (h : m = n) (f : Fin n → R) (hf : Koszul.IsKoszulRegular f) :
    Koszul.IsKoszulRegular (f ∘ Fin.cast h) := by
  subst n
  simpa using hf

private theorem isKoszulRegular_tail_quotient
    {R : Type*} [CommRing R] {n : ℕ} (a : R) (f : Fin n → R)
    (ha : IsSMulRegular R a) (hf : Koszul.IsKoszulRegular (Fin.cons a f)) :
    Koszul.IsKoszulRegular (fun i ↦ Ideal.Quotient.mk (Ideal.span {a}) (f i)) := by
  have hs := isKoszulRegular_singleton_of_isSMulRegular (fun _ : Fin 1 ↦ a) ha
  have hc : Koszul.IsKoszulRegular (Fin.append (fun _ : Fin 1 ↦ a) f) := by
    rw [Fin.append_left_eq_cons]
    exact isKoszulRegular_cast _ _ hf
  have h := Koszul.koszulRegular_quotient_of_koszulRegular_append _ _ hs hc
  rwa [show Set.range (fun _ : Fin 1 ↦ a) = {a} from Set.range_const] at h

private theorem linearForm_isSMulRegular_of_isKoszulRegular
    {R : Type*} [CommRing R] {n : ℕ} (f : Fin (n + 1) → R)
    (hf : Koszul.IsKoszulRegular f) :
    IsSMulRegular (MvPolynomial (Fin (n + 1)) R) (Stacks.GenericLinearForm.linearForm f) :=
  IsSMulRegular.of_right_eq_zero_of_smul (Stacks.GenericLinearForm.linearForm_isNonZeroDivisor f
    (annihilator_eq_zero_of_isKoszulRegular f hf))

private theorem firstRow_regular_and_tail_koszul
    {R S : Type u} [CommRing R] [CommRing S] {n : ℕ}
    [Algebra R S] [Algebra (MvPolynomial (Fin (n + 1)) R) S]
    [IsScalarTower R (MvPolynomial (Fin (n + 1)) R) S]
    [IsLocalization.Away (MvPolynomial.X (0 : Fin (n + 1)) :
      MvPolynomial (Fin (n + 1)) R) S]
    (f : Fin (n + 1) → R) (hf : Koszul.IsKoszulRegular f) :
    let g : S := ∑ i : Fin (n + 1),
      algebraMap (MvPolynomial (Fin (n + 1)) R) S (MvPolynomial.X i) *
        algebraMap R S (f i)
    IsSMulRegular S g ∧ Koszul.IsKoszulRegular
      (fun i : Fin n ↦ Ideal.Quotient.mk (Ideal.span {g}) (algebraMap R S (f i.succ))) := by
  let P := MvPolynomial (Fin (n + 1)) R
  have : Module.Flat P S := IsLocalization.flat S
    (Submonoid.powers (MvPolynomial.X (0 : Fin (n + 1)) : P))
  have : Module.Flat R S := Module.Flat.trans R P S
  let c : Fin (n + 1) → S := fun i ↦ algebraMap P S (MvPolynomial.X i)
  let F : Fin (n + 1) → S := fun i ↦ algebraMap R S (f i)
  have hlin : (∑ i, c i * F i) = algebraMap P S (Stacks.GenericLinearForm.linearForm f) := by
    rw [Stacks.GenericLinearForm.linearForm, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul]
    change c i * F i = algebraMap P S (algebraMap R P (f i)) * c i
    rw [← IsScalarTower.algebraMap_apply R P S]
    exact mul_comm _ _
  have hreg : IsSMulRegular S (∑ i, c i * F i) := by
    rw [hlin]
    exact (linearForm_isSMulRegular_of_isKoszulRegular f hf).of_flat
  have hkos : Koszul.IsKoszulRegular (Fin.cons (∑ i, c i * F i) (Fin.tail F)) :=
    isKoszulRegular_cons_sum_of_isUnit F c (isKoszulRegular_algebraMap f hf)
      (IsLocalization.Away.algebraMap_isUnit (MvPolynomial.X (0 : Fin (n + 1))))
  exact ⟨hreg, isKoszulRegular_tail_quotient _ _ hreg hkos⟩

private theorem exists_quotient_localization_equiv
    {R S T σ : Type*} [CommRing R] [CommRing S] [CommRing T]
    (I : Ideal R) (d : MvPolynomial σ R)
    [Algebra R S] [Algebra (MvPolynomial σ R) S]
    [IsScalarTower R (MvPolynomial σ R) S] [IsLocalization.Away d S]
    [Algebra (MvPolynomial σ (R ⧸ I)) T]
    [IsLocalization.Away (MvPolynomial.map (Ideal.Quotient.mk I) d) T] :
    ∃ e : (S ⧸ I.map (algebraMap R S)) ≃+* T, ∀ p : MvPolynomial σ R,
      e (Ideal.Quotient.mk _ (algebraMap (MvPolynomial σ R) S p)) =
        algebraMap (MvPolynomial σ (R ⧸ I)) T (MvPolynomial.map (Ideal.Quotient.mk I) p) := by
  let M := Submonoid.powers d
  let m : MvPolynomial σ R →+* MvPolynomial σ (R ⧸ I) :=
    MvPolynomial.map (Ideal.Quotient.mk I)
  let : IsLocalization (M.map m) T := by
    simpa only [M, Submonoid.map_powers] using
      (inferInstance : IsLocalization.Away (m d) T)
  let q : S →+* T := IsLocalization.map T m (Submonoid.le_comap_map M)
  have hq : Function.Surjective q := IsLocalization.map_surjective_of_surjective M S T
    (MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective)
  have hker : RingHom.ker q = I.map (algebraMap R S) := by
    rw [IsLocalization.ker_map T m rfl, MvPolynomial.ker_map, Ideal.mk_ker, Ideal.map_map]
    congr 1
    ext x
    exact (IsScalarTower.algebraMap_apply R (MvPolynomial σ R) S x).symm
  refine ⟨(Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hq), ?_⟩
  intro p
  change (RingHom.quotientKerEquivOfSurjective hq)
    ((Ideal.quotEquivOfEq hker.symm) (Ideal.Quotient.mk _ (algebraMap (MvPolynomial σ R) S p))) = _
  rw [Ideal.quotEquivOfEq_mk]
  exact IsLocalization.map_eq (M := M) (T := M.map m) (Submonoid.le_comap_map M) p

private abbrev UpperTriangularIndex (n : ℕ) := {ij : Fin n × Fin n // ij.1 ≤ ij.2}

private def upperTriangularIndexSuccEquiv (n : ℕ) :
    UpperTriangularIndex (n + 1) ≃ UpperTriangularIndex n ⊕ Fin (n + 1) where
  toFun p := if h : p.1.1 = 0 then Sum.inr p.1.2 else
    Sum.inl ⟨(p.1.1.pred h, p.1.2.pred (by intro hj; have := p.2; simp_all)),
      by simpa using p.2⟩
  invFun p := match p with
    | Sum.inl q => ⟨(q.1.1.succ, q.1.2.succ), by simpa using q.2⟩
    | Sum.inr j => ⟨(0, j), Fin.zero_le _⟩
  left_inv p := by
    by_cases h : p.1.1 = 0
    · simp only [h, dite_true]
      apply Subtype.ext
      exact Prod.ext h.symm rfl
    · simp only [h, dite_false, Fin.succ_pred]
  right_inv p := by
    cases p <;> simp

private theorem upperTriangularIndexSuccEquiv_zero (n : ℕ) (j : Fin (n + 1)) :
    upperTriangularIndexSuccEquiv n ⟨(0, j), Fin.zero_le _⟩ = Sum.inr j := by
  simp [upperTriangularIndexSuccEquiv]

private theorem upperTriangularIndexSuccEquiv_succ (n : ℕ) (i j : Fin n) (h : i ≤ j) :
    upperTriangularIndexSuccEquiv n ⟨(i.succ, j.succ), by simpa using h⟩ =
      Sum.inl ⟨(i, j), h⟩ := by
  simp [upperTriangularIndexSuccEquiv]

private noncomputable def upperTriangularPolynomialSuccEquiv (R : Type*) [CommRing R] (n : ℕ) :
    MvPolynomial (UpperTriangularIndex (n + 1)) R ≃ₐ[R]
      MvPolynomial (UpperTriangularIndex n) (MvPolynomial (Fin (n + 1)) R) :=
  (MvPolynomial.renameEquiv R (upperTriangularIndexSuccEquiv n)).trans
    (MvPolynomial.sumAlgEquiv R _ _)

private theorem upperTriangularPolynomialSuccEquiv_X_zero
    (R : Type*) [CommRing R] (n : ℕ) (j : Fin (n + 1)) :
    upperTriangularPolynomialSuccEquiv R n (MvPolynomial.X ⟨(0, j), Fin.zero_le _⟩) =
      MvPolynomial.C (MvPolynomial.X j) := by
  simp [upperTriangularPolynomialSuccEquiv, upperTriangularIndexSuccEquiv_zero]

private theorem upperTriangularPolynomialSuccEquiv_X_succ
    (R : Type*) [CommRing R] (n : ℕ) (i j : Fin n) (h : i ≤ j) :
    upperTriangularPolynomialSuccEquiv R n
      (MvPolynomial.X ⟨(i.succ, j.succ), by simpa using h⟩) =
      MvPolynomial.X ⟨(i, j), h⟩ := by
  simp only [upperTriangularPolynomialSuccEquiv, AlgEquiv.trans_apply,
    MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X]
  rw [upperTriangularIndexSuccEquiv_succ, MvPolynomial.sumAlgEquiv_X_inl]

private noncomputable abbrev upperTriangularDiagonal (R : Type*) [CommRing R] (n : ℕ) :
    MvPolynomial (UpperTriangularIndex n) R :=
  ∏ i : Fin n, MvPolynomial.X ⟨(i, i), le_rfl⟩

private abbrev UpperTriangularRing (R : Type*) [CommRing R] (n : ℕ) :=
  Localization.Away (upperTriangularDiagonal R n)

private abbrev FirstRowRing (R : Type*) [CommRing R] (n : ℕ) :=
  Localization.Away (MvPolynomial.X (0 : Fin (n + 1)) : MvPolynomial (Fin (n + 1)) R)

section PolynomialAlgebras

attribute [local instance] MvPolynomial.algebraMvPolynomial

private theorem exists_upperTriangularRing_succ_equiv
    {R U S V : Type*} [CommRing R] [CommRing U] [CommRing S] [CommRing V] (n : ℕ)
    [Algebra R S] [Algebra (MvPolynomial (UpperTriangularIndex (n + 1)) R) S]
    [IsScalarTower R (MvPolynomial (UpperTriangularIndex (n + 1)) R) S]
    [IsLocalization.Away (upperTriangularDiagonal R (n + 1)) S]
    [Algebra R U] [Algebra (MvPolynomial (Fin (n + 1)) R) U]
    [IsScalarTower R (MvPolynomial (Fin (n + 1)) R) U]
    [IsLocalization.Away (MvPolynomial.X (0 : Fin (n + 1)) : MvPolynomial (Fin (n + 1)) R) U]
    [Algebra R V] [Algebra (MvPolynomial (UpperTriangularIndex n) U) V]
    [IsLocalization.Away (upperTriangularDiagonal U n) V]
    [Algebra (MvPolynomial (UpperTriangularIndex n) (MvPolynomial (Fin (n + 1)) R)) V]
    [IsScalarTower (MvPolynomial (UpperTriangularIndex n) (MvPolynomial (Fin (n + 1)) R))
      (MvPolynomial (UpperTriangularIndex n) U) V]
    [IsScalarTower R (MvPolynomial (UpperTriangularIndex n) (MvPolynomial (Fin (n + 1)) R)) V] :
    ∃ e : S ≃ₐ[R] V, ∀ p : MvPolynomial (UpperTriangularIndex (n + 1)) R,
      e (algebraMap _ S p) =
        algebraMap (MvPolynomial (UpperTriangularIndex n) (MvPolynomial (Fin (n + 1)) R))
          V (upperTriangularPolynomialSuccEquiv R n p) := by
  classical
  let Row := MvPolynomial (Fin (n + 1)) R
  let Q₀ := MvPolynomial (UpperTriangularIndex n) Row
  let Q := MvPolynomial (UpperTriangularIndex n) U
  let x : Row := MvPolynomial.X 0
  let z : Q₀ := upperTriangularDiagonal Row n
  let : IsLocalization.Away (MvPolynomial.C x : Q₀) Q := by
    have h := MvPolynomial.isLocalization (σ := UpperTriangularIndex n) (Submonoid.powers x) U
    simpa only [Submonoid.map_powers] using h
  have hz : algebraMap Q₀ Q z = upperTriangularDiagonal U n := by
    change (algebraMap Q₀ Q) (∏ i : Fin n, MvPolynomial.X ⟨(i, i), le_rfl⟩) = _
    rw [map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    exact congrArg (fun m : Q₀ →+* Q ↦ m (MvPolynomial.X ⟨(i, i), le_rfl⟩))
      (MvPolynomial.algebraMap_def (R := Row) (S := U)) |>.trans (MvPolynomial.map_X _ _)
  let : IsLocalization.Away (algebraMap Q₀ Q z) V := by
    rw [hz]
    infer_instance
  let : IsLocalization.Away (z * MvPolynomial.C x : Q₀) V :=
    IsLocalization.Away.mul Q V (MvPolynomial.C x) z
  have he : upperTriangularPolynomialSuccEquiv R n (upperTriangularDiagonal R (n + 1)) =
      z * MvPolynomial.C x := by
    rw [upperTriangularDiagonal, Fin.prod_univ_succ, map_mul, map_prod,
      upperTriangularPolynomialSuccEquiv_X_zero, mul_comm]
    congr 1
    exact Finset.prod_congr rfl fun i _ => upperTriangularPolynomialSuccEquiv_X_succ R n i i le_rfl
  have hm : (Submonoid.powers (upperTriangularDiagonal R (n + 1))).map
      (upperTriangularPolynomialSuccEquiv R n) = Submonoid.powers (z * MvPolynomial.C x) := by
    rw [Submonoid.map_powers, he]
  exact ⟨IsLocalization.algEquivOfAlgEquiv S V (upperTriangularPolynomialSuccEquiv R n) hm,
    fun p => IsLocalization.algEquivOfAlgEquiv_eq hm p⟩

private theorem isWeaklyRegular_cons_of_quotient {R : Type*} [CommRing R]
    (a : R) (l : List R) (ha : IsSMulRegular R a)
    (hl : RingTheory.Sequence.IsWeaklyRegular (R ⧸ Ideal.span {a})
      (l.map (Ideal.Quotient.mk (Ideal.span {a})))) :
    RingTheory.Sequence.IsWeaklyRegular R (a :: l) := by
  apply RingTheory.Sequence.IsWeaklyRegular.cons ha
  let e : QuotSMulTop a R ≃ₗ[R] R ⧸ Ideal.span {a} :=
    (QuotSMulTop.equivQuotTensor a R).trans (TensorProduct.rid R (R ⧸ Ideal.span {a}))
  apply (e.isWeaklyRegular_congr l).mpr
  exact (RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff
    (R ⧸ Ideal.span {a}) (R ⧸ Ideal.span {a}) l).mp hl

private theorem mvPolynomial_isScalarTower
    {A B C σ : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C] :
    IsScalarTower A (MvPolynomial σ B) (MvPolynomial σ C) := by
  apply IsScalarTower.of_algebraMap_eq'
  apply RingHom.ext
  intro a
  change MvPolynomial.C (algebraMap A C a) =
    (algebraMap (MvPolynomial σ B) (MvPolynomial σ C)) (MvPolynomial.C (algebraMap A B a))
  rw [MvPolynomial.algebraMap_def, MvPolynomial.map_C, ← IsScalarTower.algebraMap_apply A B C]

end PolynomialAlgebras

private theorem exists_upperTriangularRing_succ_equiv_canonical
    (R : Type u) [CommRing R] (n : ℕ) :
    ∃ e : UpperTriangularRing R (n + 1) ≃ₐ[R]
        UpperTriangularRing (FirstRowRing R n) n,
      ∀ p : MvPolynomial (UpperTriangularIndex (n + 1)) R,
        e (algebraMap _ (UpperTriangularRing R (n + 1)) p) =
          algebraMap (MvPolynomial (UpperTriangularIndex n) (FirstRowRing R n))
            (UpperTriangularRing (FirstRowRing R n) n)
            (MvPolynomial.map (algebraMap (MvPolynomial (Fin (n + 1)) R) (FirstRowRing R n))
              (upperTriangularPolynomialSuccEquiv R n p)) := by
  let Row := MvPolynomial (Fin (n + 1)) R
  let U := FirstRowRing R n
  let Q₀ := MvPolynomial (UpperTriangularIndex n) Row
  let Q := MvPolynomial (UpperTriangularIndex n) U
  let V := UpperTriangularRing U n
  let : Algebra Q₀ Q := MvPolynomial.algebraMvPolynomial
  let : Algebra Q₀ V := inferInstance
  let : IsScalarTower Q₀ Q V := inferInstance
  let : IsScalarTower R Q₀ Q := mvPolynomial_isScalarTower
  let : IsScalarTower R Q₀ V := IsScalarTower.to₁₂₄ R Q₀ Q V
  obtain ⟨e, he⟩ := exists_upperTriangularRing_succ_equiv
    (R := R) (U := U) (S := UpperTriangularRing R (n + 1)) (V := V) n
  refine ⟨e, fun p => ?_⟩
  rw [he]
  rfl

private noncomputable abbrev upperTriangularSequence
    {R : Type*} [CommRing R] {n : ℕ} (f : Fin n → R) :
    Fin n → UpperTriangularRing R n := fun i ↦
  ∑ j : Fin n, if hij : i ≤ j then
    algebraMap (MvPolynomial (UpperTriangularIndex n) R) (UpperTriangularRing R n)
      (MvPolynomial.X ⟨(i, j), hij⟩) * algebraMap R (UpperTriangularRing R n) (f j)
  else 0

private theorem exists_upperTriangularRing_succ_equiv_sequence
    {R : Type u} [CommRing R] {n : ℕ} (f : Fin (n + 1) → R) :
    let U := FirstRowRing R n
    let V := UpperTriangularRing U n
    let a : U := ∑ j : Fin (n + 1),
      algebraMap (MvPolynomial (Fin (n + 1)) R) U (MvPolynomial.X j) * algebraMap R U (f j)
    ∃ e : UpperTriangularRing R (n + 1) ≃ₐ[R] V,
      ∀ i, e (upperTriangularSequence f i) =
        Fin.cons (α := fun _ ↦ V) (algebraMap U V a)
          (upperTriangularSequence (fun j : Fin n ↦ algebraMap R U (f j.succ))) i := by
  classical
  dsimp only
  let Row := MvPolynomial (Fin (n + 1)) R
  let U := FirstRowRing R n
  let V := UpperTriangularRing U n
  let P := MvPolynomial (UpperTriangularIndex (n + 1)) R
  let S := UpperTriangularRing R (n + 1)
  let Q := MvPolynomial (UpperTriangularIndex n) U
  obtain ⟨e, he⟩ := exists_upperTriangularRing_succ_equiv_canonical R n
  have hzero (j : Fin (n + 1)) :
      e (algebraMap P S (MvPolynomial.X ⟨(0, j), Fin.zero_le _⟩)) =
        algebraMap U V (algebraMap Row U (MvPolynomial.X j)) := by
    rw [he, upperTriangularPolynomialSuccEquiv_X_zero, MvPolynomial.map_C]
    exact (IsScalarTower.algebraMap_apply U Q V _).symm
  have hsucc (i j : Fin n) (h : i ≤ j) :
      e (algebraMap P S (MvPolynomial.X ⟨(i.succ, j.succ), by simpa using h⟩)) =
        algebraMap Q V (MvPolynomial.X ⟨(i, j), h⟩) := by
    rw [he, upperTriangularPolynomialSuccEquiv_X_succ, MvPolynomial.map_X]
  refine ⟨e, Fin.cases ?_ (fun i ↦ ?_)⟩
  · simp only [upperTriangularSequence, Fin.zero_le, dite_true, map_sum, map_mul,
      AlgEquiv.commutes, Fin.cons_zero]
    apply Finset.sum_congr rfl
    intro j _
    rw [hzero, ← IsScalarTower.algebraMap_apply R U V]
  · have hi : ¬ i.succ ≤ (0 : Fin (n + 1)) := by simp
    simp only [upperTriangularSequence, map_sum, Fin.sum_univ_succ,
      hi, dite_false, zero_add, Fin.cons_succ]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : i ≤ j
    · simp only [Fin.succ_le_succ_iff, h, dite_true, map_mul, AlgEquiv.commutes]
      rw [hsucc, ← IsScalarTower.algebraMap_apply R U V]
    · simp only [Fin.succ_le_succ_iff, h, dite_false, map_zero]

private theorem exists_upperTriangularRing_quotient_equiv
    {R : Type u} [CommRing R] (n : ℕ) (I : Ideal R) :
    ∃ e : (UpperTriangularRing R n ⧸ I.map (algebraMap R (UpperTriangularRing R n))) ≃+*
        UpperTriangularRing (R ⧸ I) n,
      ∀ (f : Fin n → R) i,
        e (Ideal.Quotient.mk _ (upperTriangularSequence f i)) =
          upperTriangularSequence (fun j ↦ Ideal.Quotient.mk I (f j)) i := by
  classical
  let P := MvPolynomial (UpperTriangularIndex n) R
  let S := UpperTriangularRing R n
  let T := UpperTriangularRing (R ⧸ I) n
  have hd : MvPolynomial.map (Ideal.Quotient.mk I) (upperTriangularDiagonal R n) =
      upperTriangularDiagonal (R ⧸ I) n := by
    simp only [upperTriangularDiagonal, map_prod, MvPolynomial.map_X]
  let : IsLocalization.Away
      (MvPolynomial.map (Ideal.Quotient.mk I) (upperTriangularDiagonal R n)) T := by
    rw [hd]
    infer_instance
  obtain ⟨e, he⟩ := exists_quotient_localization_equiv (S := S) (T := T) I
    (upperTriangularDiagonal R n)
  have hC (r : R) : e (Ideal.Quotient.mk _ (algebraMap R S r)) =
      algebraMap (R ⧸ I) T (Ideal.Quotient.mk I r) := by
    have h := he (MvPolynomial.C r)
    rw [MvPolynomial.map_C] at h
    change e (Ideal.Quotient.mk _ (algebraMap P S (algebraMap R P r))) =
      algebraMap (MvPolynomial (UpperTriangularIndex n) (R ⧸ I)) T
        (algebraMap (R ⧸ I) _ (Ideal.Quotient.mk I r)) at h
    simpa only [← IsScalarTower.algebraMap_apply] using h
  refine ⟨e, fun f i ↦ ?_⟩
  simp only [upperTriangularSequence, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : i ≤ j
  · simp only [h, dite_true, map_mul]
    rw [he, MvPolynomial.map_X, hC]
  · simp only [h, dite_false, map_zero]

private theorem isWeaklyRegular_quotient_upperTriangular
    {R : Type u} [CommRing R] {n : ℕ} (I : Ideal R) (f : Fin n → R)
    (h : RingTheory.Sequence.IsWeaklyRegular (UpperTriangularRing (R ⧸ I) n)
      (List.ofFn (upperTriangularSequence (fun i ↦ Ideal.Quotient.mk I (f i))))) :
    RingTheory.Sequence.IsWeaklyRegular
      (UpperTriangularRing R n ⧸ I.map (algebraMap R (UpperTriangularRing R n)))
      ((List.ofFn (upperTriangularSequence f)).map
        (Ideal.Quotient.mk (I.map (algebraMap R (UpperTriangularRing R n))))) := by
  obtain ⟨e, he⟩ := exists_upperTriangularRing_quotient_equiv n I
  apply (isWeaklyRegular_ringEquiv e _).mpr
  simpa only [List.map_ofFn, Function.comp_def, he] using h

private theorem isWeaklyRegular_upperTriangular_of_isKoszulRegular
    {n : ℕ} {R : Type u} [CommRing R] (f : Fin n → R)
    (hf : Koszul.IsKoszulRegular f) :
    RingTheory.Sequence.IsWeaklyRegular (UpperTriangularRing R n)
      (List.ofFn (upperTriangularSequence f)) := by
  induction n generalizing R with
  | zero =>
    simp only [List.ofFn_zero]
    exact RingTheory.Sequence.IsWeaklyRegular.nil _ _
  | succ n ih =>
    let U := FirstRowRing R n
    let V := UpperTriangularRing U n
    let a : U := ∑ j : Fin (n + 1),
      algebraMap (MvPolynomial (Fin (n + 1)) R) U (MvPolynomial.X j) *
        algebraMap R U (f j)
    let F : Fin n → U := fun j ↦ algebraMap R U (f j.succ)
    have hfirst := firstRow_regular_and_tail_koszul (S := U) f hf
    change IsSMulRegular U a ∧
      Koszul.IsKoszulRegular (fun j ↦ Ideal.Quotient.mk (Ideal.span {a}) (F j)) at hfirst
    have : Module.Flat U V := Module.Flat.trans U (MvPolynomial (UpperTriangularIndex n) U) V
    have htail := isWeaklyRegular_quotient_upperTriangular (Ideal.span {a}) F
      (ih _ hfirst.2)
    have htail' : RingTheory.Sequence.IsWeaklyRegular
        (V ⧸ Ideal.span {algebraMap U V a})
        ((List.ofFn (upperTriangularSequence F)).map
          (Ideal.Quotient.mk (Ideal.span {algebraMap U V a}))) := by
      have hid : (Ideal.span {a}).map (algebraMap U V) =
          Ideal.span {algebraMap U V a} := by
        rw [Ideal.map_span, Set.image_singleton]
      exact hid ▸ htail
    have hcons := isWeaklyRegular_cons_of_quotient (algebraMap U V a)
      (List.ofFn (upperTriangularSequence F)) hfirst.1.of_flat htail'
    obtain ⟨e, he⟩ := exists_upperTriangularRing_succ_equiv_sequence f
    apply (isWeaklyRegular_ringEquiv e.toRingEquiv _).mpr
    rw [List.map_ofFn]
    have heq : (fun i ↦ e (upperTriangularSequence f i)) =
        Fin.cons (α := fun _ ↦ V) (algebraMap U V a) (upperTriangularSequence F) := funext he
    change RingTheory.Sequence.IsWeaklyRegular V
      (List.ofFn (fun i ↦ e (upperTriangularSequence f i)))
    rw [heq, List.ofFn_succ]
    simpa only [Fin.cons_zero, Fin.cons_succ] using hcons

/-- **Stacks 068Q.** A Koszul-regular sequence generating a proper ideal becomes a regular
sequence after a generic invertible upper-triangular change of generators. The resulting
polynomial localization is faithfully flat and smooth over the original ring, and the changed
sequence generates the extension of the original ideal. -/
@[stacks 068Q]
public theorem isRegular_upperTriangular_of_isKoszulRegular
    {R : Type*} [CommRing R] {n : ℕ} (f : Fin n → R)
    (hf : Koszul.IsKoszulRegular f)
    (hproper : Ideal.span (Set.range f) ≠ ⊤) :
    let σ := {ij : Fin n × Fin n // ij.1 ≤ ij.2}
    let P := MvPolynomial σ R
    let d : P := ∏ i : Fin n, MvPolynomial.X ⟨(i, i), le_rfl⟩
    let S := Localization.Away d
    let g : Fin n → S := fun i ↦
      ∑ j : Fin n, if hij : i ≤ j then
        algebraMap P S (MvPolynomial.X ⟨(i, j), hij⟩) * algebraMap R S (f j)
      else 0
    Module.FaithfullyFlat R S ∧ Algebra.Smooth R S ∧
      RingTheory.Sequence.IsRegular S (List.ofFn g) ∧
        Ideal.map (algebraMap R S) (Ideal.span (Set.range f)) =
          Ideal.span (Set.range g) := by
  classical
  change Module.FaithfullyFlat R (UpperTriangularRing R n) ∧
    Algebra.Smooth R (UpperTriangularRing R n) ∧
      RingTheory.Sequence.IsRegular (UpperTriangularRing R n)
        (List.ofFn (upperTriangularSequence f)) ∧
          Ideal.map (algebraMap R (UpperTriangularRing R n)) (Ideal.span (Set.range f)) =
            Ideal.span (Set.range (upperTriangularSequence f))
  let S := UpperTriangularRing R n
  let : Module.FaithfullyFlat R S := faithfullyFlat_away_prod_X
    (fun i : Fin n ↦ (⟨(i, i), le_rfl⟩ : UpperTriangularIndex n))
  have hspan := span_upperTriangular_of_isLocalization (S := S) f
  refine ⟨inferInstance, smooth_away_prod_X
    (fun i : Fin n ↦ (⟨(i, i), le_rfl⟩ : UpperTriangularIndex n)), ?_, hspan⟩
  apply (RingTheory.Sequence.isRegular_iff _ _).mpr
  refine ⟨isWeaklyRegular_upperTriangular_of_isKoszulRegular f hf, ?_⟩
  rw [Ideal.smul_eq_mul, Ideal.mul_top]
  have hl : Ideal.ofList (List.ofFn (upperTriangularSequence f)) =
      Ideal.span (Set.range (upperTriangularSequence f)) :=
    congrArg Ideal.span (Set.ext fun x ↦ List.mem_ofFn' _ x)
  rw [hl, ← hspan]
  intro ht
  apply hproper
  have hc := congrArg (Ideal.comap (algebraMap R S)) ht
  simpa only [Ideal.comap_top, Ideal.comap_map_eq_self_of_faithfullyFlat] using hc.symm

end UpperTriangular

end Koszul

end
