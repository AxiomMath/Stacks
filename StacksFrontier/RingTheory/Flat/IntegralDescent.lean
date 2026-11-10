module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.Noetherian.Nilpotent
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.FinitePresentation.ModuleDescent
public import StacksFrontier.RingTheory.Flat.FaithfullyFlat.Projective
public import StacksFrontier.RingTheory.Flat.FlatteningSectionsKernel
public import StacksFrontier.RingTheory.Flat.LocalCriteria
public import StacksFrontier.RingTheory.Flat.QuotientInf
public import StacksFrontier.RingTheory.Module.DirectLimit.FinitePresentation
public import StacksFrontier.RingTheory.Module.Projective.Lifting
public import StacksFrontier.RingTheory.Module.Projective.NilpotentIdeal
public import StacksFrontier.RingTheory.Polynomial.MonicSplitting
public import StacksFrontier.RingTheory.Spectrum.Image
public import StacksFrontier.RingTheory.SpreadingOut.FlatModel

@[expose] public section

/-!
# Descent of flatness and projectivity along an integral ring map

Let `R → S` be an injective ring map. This file proves that flatness and projectivity of an
`R`-module can be detected after the scalar extension to `S`, in two settings: when `R → S` is
finite and `R` is Noetherian, and — for flatness — when `R → S` is merely integral, provided the
module is finitely presented over a polynomial ring in finitely many variables over `R`.

## Main results

* `Module.Flat.of_finite_injective_baseChange`: flatness descends along a finite injective ring
  map of Noetherian rings.
* `Module.Projective.of_finite_injective_baseChange`: projectivity descends along a finite
  injective ring map of Noetherian rings.
* `Module.Flat.of_integral_injective_baseChange`: flatness descends along an injective integral
  ring map for a module finitely presented over a polynomial ring over `R`.

## Implementation notes

The source assumes both rings Noetherian in the finite case; since a finite algebra over a
Noetherian ring is Noetherian, only the hypothesis on the source ring is kept. The source writes
the scalar extension as `M ⊗[R] S`; we use the canonically isomorphic `S ⊗[R] M`, on which
Mathlib supplies the natural `S`-module structure.

The two finite-case arguments run along a common spine: after a finite free extension of the base
(`exists_finite_free_extension_quotient_split_polynomials`) the algebra is a quotient of a
polynomial ring in which each variable satisfies a polynomial that splits into linear factors, so
each multi-index of roots gives a retraction onto a quotient of the base
(`imageIdealQuotientAlgHom`), and the intersection of the corresponding image ideals is nilpotent
(`isNilpotent_iInf_imageIdeal`). Descent then follows from the local criterion at a nilpotent
ideal.

The integral case is reduced to the finite case by spreading out: the whole datum descends to a
subring of `R` of finite type over `ℤ`, the integral extension is the directed union of its
finite-type subalgebras, and flatness over a member of that system is obtained from Stacks 02JO
(3). Stacks 02JO (3) asks for all the rings of the directed system in one universe, so the
integral extension is replaced by a `ULift` copy before the system of subalgebras is formed.

## References

* [Stacks Project, Tag 0533](https://stacks.math.columbia.edu/tag/0533)
* [Stacks Project, Tag 0534](https://stacks.math.columbia.edu/tag/0534)
* [Stacks Project, Tag 0H7R](https://stacks.math.columbia.edu/tag/0H7R)
-/

open scoped TensorProduct

universe u v w uB uS

/-! ### Retractions onto quotients of the base -/

/-- The `R ⧸ I`-linear identification of `(R ⧸ I) ⊗[R] M` with `M ⧸ I • M`: the underlying
`R`-linear equivalence `TensorProduct.quotTensorEquivQuotSMul` is linear over `R ⧸ I` because
`R → R ⧸ I` is surjective. -/
private noncomputable def quotTensorEquivQuotSMulQuot {R : Type u} [CommRing R]
    {M : Type w} [AddCommGroup M] [Module R M] (I : Ideal R) :
    ((R ⧸ I) ⊗[R] M) ≃ₗ[R ⧸ I] M ⧸ I • (⊤ : Submodule R M) :=
  LinearEquiv.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
    (TensorProduct.quotTensorEquivQuotSMul M I)

/-- For each multi-index `k` of roots, evaluating the variables at those roots and reducing
modulo the image ideal `J_k` is a retraction `A → R ⧸ J_k` of the structure map, where
`A = R[x₁, …, xₙ] ⧸ J` is presented by `g` with kernel `J`. -/
private noncomputable def imageIdealQuotientAlgHom {R : Type u} [CommRing R]
    {A : Type v} [CommRing A] [Algebra R A] {n : ℕ} (d : Fin n → ℕ)
    (α : ∀ i, Fin (d i) → R) {g : MvPolynomial (Fin n) R →ₐ[R] A}
    (hg : Function.Surjective g) (k : Stacks.Spectrum.PolynomialQuotientImage.MultiIndex d) :
    A →ₐ[R] R ⧸ Stacks.Spectrum.PolynomialQuotientImage.imageIdeal d α k (RingHom.ker g) :=
  (Ideal.Quotient.liftₐ (RingHom.ker g)
      ((Ideal.Quotient.mkₐ R (Stacks.Spectrum.PolynomialQuotientImage.imageIdeal d α k (RingHom.ker
        g))).comp
        (Stacks.Spectrum.PolynomialQuotientImage.evalHom d α k))
      (fun _ hx ↦ Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hx))).comp
    (Ideal.quotientKerAlgEquivOfSurjective hg).symm.toAlgHom

/-- For a finite injective algebra `A` over a Noetherian ring `R`, presented as a quotient of
`R[x₁, …, xₙ]` in which each variable satisfies a polynomial split into linear factors, the
intersection of the image ideals `J_k` is nilpotent: its zero locus is all of `Spec R` because
`Spec A → Spec R` is surjective for a finite injective map, so the intersection is contained in
the nilradical, which is nilpotent over a Noetherian ring. -/
private lemma isNilpotent_iInf_imageIdeal {R : Type u} [CommRing R] [IsNoetherianRing R]
    {A : Type v} [CommRing A] [Algebra R A] [Module.Finite R A]
    (hRA : Function.Injective (algebraMap R A)) {n : ℕ} {d : Fin n → ℕ}
    {α : ∀ i, Fin (d i) → R} {g : MvPolynomial (Fin n) R →ₐ[R] A}
    (hg : Function.Surjective g)
    (hrel : ∀ i, Stacks.Spectrum.PolynomialQuotientImage.factoredPoly d α i ∈ RingHom.ker g) :
    IsNilpotent (⨅ k, Stacks.Spectrum.PolynomialQuotientImage.imageIdeal d α k (RingHom.ker g)) :=
      by
  set J : Ideal (MvPolynomial (Fin n) R) := RingHom.ker g with hJ
  set I : Ideal R := ⨅ k, Stacks.Spectrum.PolynomialQuotientImage.imageIdeal d α k J with hI
  have hcr (r : R) :
      (Ideal.quotientKerAlgEquivOfSurjective hg) (Ideal.Quotient.mk J (MvPolynomial.C r))
        = algebraMap R A r := by
    have hmk : Ideal.Quotient.mk J (MvPolynomial.C r)
        = algebraMap R (MvPolynomial (Fin n) R ⧸ J) r := by
      rw [← Ideal.Quotient.mk_algebraMap, MvPolynomial.algebraMap_eq]
    rw [hmk]
    exact AlgEquiv.commutes _ r
  have hzero : PrimeSpectrum.zeroLocus (I : Set R) = Set.univ := by
    rw [hI, ← Stacks.Spectrum.PolynomialQuotientImage.range_comap_eq_zeroLocus_iInf_imageIdeal d α J
      hrel]
    refine Set.eq_univ_of_forall fun p ↦ ?_
    have : FaithfulSMul R A := (faithfulSMul_iff_algebraMap_injective R A).mpr hRA
    obtain ⟨q, hq⟩ := Algebra.IsIntegral.comap_surjective R A p
    refine ⟨PrimeSpectrum.comap
      (Ideal.quotientKerAlgEquivOfSurjective hg).toRingEquiv.toRingHom q, ?_⟩
    ext r
    simpa [Stacks.Spectrum.PolynomialQuotientImage.structMap, hcr] using congrArg (fun z ↦ r ∈
      z.asIdeal) hq
  have hIle : I ≤ nilradical R := (PrimeSpectrum.zeroLocus_eq_univ_iff (I : Set R)).mp hzero
  obtain ⟨m, hm⟩ := IsNoetherianRing.isNilpotent_nilradical R
  exact ⟨m, le_bot_iff.mp ((pow_le_pow_left' hIle m).trans hm.le)⟩

/-! ### Flatness descends along a finite injective map -/

/-- Flatness of the base change `A ⊗[R] M` over `A` gives flatness of `M ⧸ I • M` over `R ⧸ I`
whenever the structure map `R → A` has an `R`-algebra retraction `A → R ⧸ I`. -/
private lemma flat_quotient_of_flat_baseChange_of_algHom {R : Type u} [CommRing R]
    {A : Type v} [CommRing A] [Algebra R A] {M : Type w} [AddCommGroup M] [Module R M]
    (I : Ideal R) (q : A →ₐ[R] R ⧸ I) (hM : Module.Flat A (A ⊗[R] M)) :
    Module.Flat (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M)) := by
  let : Algebra A (R ⧸ I) := q.toRingHom.toAlgebra
  have : IsScalarTower R A (R ⧸ I) :=
    IsScalarTower.of_algebraMap_eq fun r ↦ (q.commutes r).symm
  let : Module.Flat A (A ⊗[R] M) := hM
  let : Module.Flat (R ⧸ I) ((R ⧸ I) ⊗[A] (A ⊗[R] M)) :=
    Module.Flat.baseChange A (R ⧸ I) (A ⊗[R] M)
  let : Module.Flat (R ⧸ I) ((R ⧸ I) ⊗[R] M) :=
    Module.Flat.of_linearEquiv
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R A (R ⧸ I) (R ⧸ I) M).symm
  exact Module.Flat.of_linearEquiv (quotTensorEquivQuotSMulQuot I).symm

/-- The polynomial-presentation step of Stacks 0533. Let `R` be Noetherian. If `A` is a finite
injective `R`-algebra presented as a quotient of `R[x₁, …, xₙ]` in which each variable satisfies
a polynomial split into linear factors, then flatness of `A ⊗[R] M` over `A` descends to `M`. -/
private lemma flat_of_split_presentation {R : Type u} [CommRing R] [IsNoetherianRing R]
    {A : Type v} [CommRing A] [Algebra R A] [Module.Finite R A]
    {M : Type w} [AddCommGroup M] [Module R M]
    (hRA : Function.Injective (algebraMap R A)) (hM : Module.Flat A (A ⊗[R] M))
    {n : ℕ} (d : Fin n → ℕ) (α : ∀ i, Fin (d i) → R)
    {g : MvPolynomial (Fin n) R →ₐ[R] A} (hg : Function.Surjective g)
    (hrel : ∀ i, Stacks.Spectrum.PolynomialQuotientImage.factoredPoly d α i ∈ RingHom.ker g) :
    Module.Flat R M :=
  Module.Flat.of_flat_quotient_of_flat_tensorProduct_of_isNilpotent_of_injective (R' := A) _
    (isNilpotent_iInf_imageIdeal hRA hg hrel) hRA
    (Stacks.flat_quotient_iInf (fun k ↦ Stacks.Spectrum.PolynomialQuotientImage.imageIdeal d α k
      (RingHom.ker g))
      fun k ↦ flat_quotient_of_flat_baseChange_of_algHom _
        (imageIdealQuotientAlgHom d α hg k) hM)
    hM

/-- A surjection from the quotient of `R[x₁, …, xₙ]` by the split polynomials `∏ⱼ (xᵢ - αᵢⱼ)`
yields a surjection from `R[x₁, …, xₙ]` whose kernel contains each of these polynomials. -/
private lemma exists_surjective_factoredPoly_mem_ker {R : Type u} [CommRing R]
    {A : Type v} [CommRing A] [Algebra R A] {n : ℕ} (d : Fin n → ℕ) (α : ∀ i, Fin (d i) → R)
    (f : (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range fun i : Fin n ↦
      ∏ j : Fin (d i), (MvPolynomial.X i - MvPolynomial.C (α i j)))) →ₐ[R] A)
    (hf : Function.Surjective f) :
    ∃ g : MvPolynomial (Fin n) R →ₐ[R] A, Function.Surjective g ∧
      ∀ i, Stacks.Spectrum.PolynomialQuotientImage.factoredPoly d α i ∈ RingHom.ker g :=
  ⟨f.comp (Ideal.Quotient.mkₐ R _), hf.comp Ideal.Quotient.mk_surjective, fun i ↦ by
    rw [RingHom.mem_ker]
    exact (congrArg f (Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Set.mem_range_self i)))).trans (map_zero f)⟩

/-- Let `R → S` be a finite injective homomorphism of rings with `R` Noetherian and let `M` be an
`R`-module. If the scalar extension `S ⊗[R] M` is flat over `S`, then `M` is flat over `R`. -/
@[stacks 0533, ega "IV 11.5.5" "finite injective case"]
theorem Module.Flat.of_finite_injective_baseChange {R : Type u} [CommRing R] [IsNoetherianRing R]
    {S : Type v} [CommRing S] [Algebra R S] [Module.Finite R S]
    {M : Type w} [AddCommGroup M] [Module R M]
    (hRS : Function.Injective (algebraMap R S))
    (hM : Module.Flat S (S ⊗[R] M)) : Module.Flat R M := by
  classical
  cases subsingleton_or_nontrivial R with
  | inl hR =>
    let : Subsingleton R := hR
    rw [Module.Flat.iff_rTensor_injective']
    exact fun I ↦ Function.injective_of_subsingleton _
  | inr hR =>
    let : Nontrivial R := hR
    obtain ⟨R', _, _, _, hfree, hRR', n, d, α, f, hf⟩ :=
      exists_finite_free_extension_quotient_split_polynomials (R := R) (S := S)
    let S' := S ⊗[R] R'
    let : Algebra R' S' := Algebra.TensorProduct.rightAlgebra
    have : Nontrivial R' := hRR'.nontrivial
    let : Module.Free R R' := hfree
    have : Module.FaithfullyFlat R R' := inferInstance
    let : IsNoetherianRing R' := IsNoetherianRing.of_finite R R'
    let : Module.Finite R' S' := Module.Finite.of_restrictScalars_finite R R' S'
    have hR'S' : Function.Injective (algebraMap R' S') :=
      Algebra.TensorProduct.includeRight_injective hRS
    have hN : Module.Flat S' (S' ⊗[R'] (R' ⊗[R] M)) := by
      let : Module.Flat S (S ⊗[R] M) := hM
      let : Module.Flat S' (S' ⊗[S] (S ⊗[R] M)) := Module.Flat.baseChange S S' (S ⊗[R] M)
      let : Module.Flat S' (S' ⊗[R] M) :=
        Module.Flat.of_linearEquiv
          (TensorProduct.AlgebraTensorModule.cancelBaseChange R S S' S' M).symm
      exact Module.Flat.of_linearEquiv
        (TensorProduct.AlgebraTensorModule.cancelBaseChange R R' S' S' M)
    obtain ⟨g, hg, hrel⟩ := exists_surjective_factoredPoly_mem_ker d α f hf
    let : Module.Flat R' (R' ⊗[R] M) := flat_of_split_presentation hR'S' hN d α hg hrel
    exact Module.Flat.of_flat_tensorProduct R M R'

/-! ### Projectivity descends along a finite injective map -/

section Projective

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

/-- Projectivity of the base change `A ⊗[R] P` over `A` gives projectivity of `P ⧸ I • P` over
`R ⧸ I` whenever the structure map `R → A` has an `R`-algebra retraction `A → R ⧸ I`. -/
private lemma projective_quotient_of_projective_baseChange_of_algHom {R : Type u} [CommRing R]
    {A : Type v} [CommRing A] [Algebra R A] {P : Type w} [AddCommGroup P] [Module R P]
    (I : Ideal R) (f : A →ₐ[R] R ⧸ I) (hP : Module.Projective A (A ⊗[R] P)) :
    Module.Projective (R ⧸ I) (P ⧸ (I • (⊤ : Submodule R P))) := by
  let : Algebra A (R ⧸ I) := f.toRingHom.toAlgebra
  have : IsScalarTower R A (R ⧸ I) :=
    IsScalarTower.of_algebraMap_eq fun r ↦ (f.commutes r).symm
  have : Module.Projective A (A ⊗[R] P) := hP
  have : Module.Projective (R ⧸ I) ((R ⧸ I) ⊗[A] (A ⊗[R] P)) := inferInstance
  have : Module.Projective (R ⧸ I) ((R ⧸ I) ⊗[R] P) :=
    Module.Projective.of_equiv'
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R A (R ⧸ I) (R ⧸ I) P)
  exact Module.Projective.of_equiv' (quotTensorEquivQuotSMulQuot I)

/-- If `P ⧸ I • P` is projective over `R ⧸ I` and `P ⧸ J • P` is projective over `R ⧸ J`, then
`P ⧸ (I ⊓ J) • P` is projective over `R ⧸ (I ⊓ J)`: over `R ⧸ (I ⊓ J)` the images of `I` and `J`
meet in zero, so Stacks 0H7M applies once each reduction has been rewritten as a reduction of
`P ⧸ (I ⊓ J) • P`. -/
private lemma projective_quotient_inf {R : Type u} [CommRing R]
    {P : Type w} [AddCommGroup P] [Module R P] (I J : Ideal R)
    (hI : Module.Projective (R ⧸ I) (P ⧸ (I • (⊤ : Submodule R P))))
    (hJ : Module.Projective (R ⧸ J) (P ⧸ (J • (⊤ : Submodule R P)))) :
    Module.Projective (R ⧸ (I ⊓ J)) (P ⧸ ((I ⊓ J) • (⊤ : Submodule R P))) := by
  set K := I ⊓ J with hK
  set q : R →+* R ⧸ K := Ideal.Quotient.mk K with hq
  have hIJ : Ideal.map q I ⊓ Ideal.map q J = ⊥ := Ideal.map_mk_inf_map_mk_eq_bot I J
  have corner (L : Ideal R) (hKL : K ≤ L)
      (hL : Module.Projective (R ⧸ L) (P ⧸ (L • (⊤ : Submodule R P)))) :
      Module.Projective ((R ⧸ K) ⧸ Ideal.map q L)
        ((P ⧸ (K • (⊤ : Submodule R P))) ⧸
          (Ideal.map q L • (⊤ : Submodule (R ⧸ K) (P ⧸ (K • (⊤ : Submodule R P)))))) := by
    let α := DoubleQuot.quotQuotEquivQuotOfLE hKL
    let β := Submodule.quotientQuotientEquivQuotient (K • (⊤ : Submodule R P))
      (L • (⊤ : Submodule R P)) (Submodule.smul_mono hKL le_rfl)
    let γ := Submodule.quotEquivOfEq _ _
      (Submodule.restrictScalars_map_smul_top_eq_map_mkQ (M := P) K L).symm
    let δ := Submodule.Quotient.restrictScalarsEquiv R
      (Ideal.map q L • (⊤ : Submodule (R ⧸ K) (P ⧸ (K • (⊤ : Submodule R P)))))
    let ψ : ((P ⧸ (K • (⊤ : Submodule R P))) ⧸
          (Ideal.map q L • (⊤ : Submodule (R ⧸ K) (P ⧸ (K • (⊤ : Submodule R P)))))) ≃+
        (P ⧸ (L • (⊤ : Submodule R P))) :=
      δ.symm.toAddEquiv.trans (γ.symm.toAddEquiv.trans β.toAddEquiv)
    let ψ' : ((P ⧸ (K • (⊤ : Submodule R P))) ⧸
          (Ideal.map q L • (⊤ : Submodule (R ⧸ K) (P ⧸ (K • (⊤ : Submodule R P))))))
          ≃ₛₗ[(α : ((R ⧸ K) ⧸ Ideal.map q L) →+* (R ⧸ L))]
            (P ⧸ (L • (⊤ : Submodule R P))) :=
      { ψ with
        map_smul' := by
          intro a m
          obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ m
          obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ m
          obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
          obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
          rfl }
    exact Module.Projective.of_equiv ψ'.symm
  exact projective_of_projective_quotient_inter_zero (R ⧸ K) (Ideal.map q I) (Ideal.map q J) hIJ
    (P ⧸ (K • (⊤ : Submodule R P))) (corner I inf_le_left hI) (corner J inf_le_right hJ)

/-- If `P ⧸ I k • P` is projective over `R ⧸ I k` for each ideal of a finite family `I`, then
`P ⧸ (⨅ k, I k) • P` is projective over `R ⧸ ⨅ k, I k`, by iterating the binary case. -/
private lemma projective_quotient_iInf {R : Type u} [CommRing R]
    {P : Type w} [AddCommGroup P] [Module R P] {κ : Type*} [Finite κ] (I : κ → Ideal R)
    (hI : ∀ k, Module.Projective (R ⧸ I k) (P ⧸ (I k • (⊤ : Submodule R P)))) :
    Module.Projective (R ⧸ ⨅ k, I k) (P ⧸ ((⨅ k, I k) • (⊤ : Submodule R P))) := by
  classical
  let : Fintype κ := Fintype.ofFinite κ
  have hfin : ∀ s : Finset κ,
      Module.Projective (R ⧸ s.inf I) (P ⧸ (s.inf I • (⊤ : Submodule R P))) := by
    intro s
    induction s using Finset.induction with
    | empty =>
      rw [Finset.inf_empty]
      have : Subsingleton (P ⧸ ((⊤ : Ideal R) • (⊤ : Submodule R P))) :=
        Module.subsingleton (R ⧸ (⊤ : Ideal R)) _
      exact Module.Projective.of_free
    | @insert k s _ ih =>
      rw [Finset.inf_insert]
      exact projective_quotient_inf (I k) (s.inf I) (hI k) ih
  exact (Finset.inf_univ_eq_iInf I) ▸ hfin Finset.univ

/-- The polynomial-presentation step of Stacks 0H7R. Let `R` be Noetherian. If `A` is a finite
injective `R`-algebra presented as a quotient of `R[x₁, …, xₙ]` in which each variable satisfies
a polynomial split into linear factors, then projectivity of `A ⊗[R] P` over `A` descends to
`P`. -/
private lemma projective_of_split_presentation {R : Type u} [CommRing R] [IsNoetherianRing R]
    {A : Type v} [CommRing A] [Algebra R A] [Module.Finite R A]
    {P : Type w} [AddCommGroup P] [Module R P]
    (hRA : Function.Injective (algebraMap R A)) (hP : Module.Projective A (A ⊗[R] P))
    {n : ℕ} (d : Fin n → ℕ) (α : ∀ i, Fin (d i) → R)
    {g : MvPolynomial (Fin n) R →ₐ[R] A} (hg : Function.Surjective g)
    (hrel : ∀ i, Stacks.Spectrum.PolynomialQuotientImage.factoredPoly d α i ∈ RingHom.ker g) :
    Module.Projective R P := by
  have hAP : Module.Projective A (A ⊗[R] P) := hP
  have : Module.Flat R P := Module.Flat.of_finite_injective_baseChange (S := A) hRA inferInstance
  exact Module.Flat.projective_of_isNilpotent_of_projective_quotient_smul_top
    (isNilpotent_iInf_imageIdeal hRA hg hrel)
    (projective_quotient_iInf (fun k ↦ Stacks.Spectrum.PolynomialQuotientImage.imageIdeal d α k
      (RingHom.ker g))
      fun k ↦ projective_quotient_of_projective_baseChange_of_algHom _
        (imageIdealQuotientAlgHom d α hg k) hP)

/-- Let `R → S` be a finite injective homomorphism of rings with `R` Noetherian and let `P` be an
`R`-module. If the scalar extension `S ⊗[R] P` is projective over `S`, then `P` is projective
over `R`. -/
@[stacks 0H7R]
theorem Module.Projective.of_finite_injective_baseChange {R : Type u} [CommRing R]
    [IsNoetherianRing R] {S : Type v} [CommRing S] [Algebra R S] [Module.Finite R S]
    {P : Type w} [AddCommGroup P] [Module R P]
    (hRS : Function.Injective (algebraMap R S))
    [Module.Projective S (S ⊗[R] P)] : Module.Projective R P := by
  classical
  cases subsingleton_or_nontrivial R with
  | inl hR =>
    have : Subsingleton P := Module.subsingleton R P
    exact Module.Projective.of_free
  | inr hR =>
    obtain ⟨R', _, _, _, hfree, hRR', n, d, α, f, hf⟩ :=
      exists_finite_free_extension_quotient_split_polynomials (R := R) (S := S)
    let A := S ⊗[R] R'
    let : Algebra R' A := Algebra.TensorProduct.rightAlgebra
    have : Nontrivial R' := hRR'.nontrivial
    have : Module.Free R R' := hfree
    have : Module.FaithfullyFlat R R' := inferInstance
    have : IsNoetherianRing R' := IsNoetherianRing.of_finite R R'
    have : IsScalarTower R R' A := Algebra.TensorProduct.right_isScalarTower
    have : Module.Finite R' A := Module.Finite.of_restrictScalars_finite R R' A
    have hR'A : Function.Injective (algebraMap R' A) :=
      Algebra.TensorProduct.includeRight_injective hRS
    have hAP : Module.Projective A (A ⊗[R'] (R' ⊗[R] P)) := by
      have : Module.Projective A (A ⊗[S] (S ⊗[R] P)) := inferInstance
      exact Module.Projective.of_equiv'
        ((TensorProduct.AlgebraTensorModule.cancelBaseChange R S A A P).trans
          (TensorProduct.AlgebraTensorModule.cancelBaseChange R R' A A P).symm)
    obtain ⟨g, hg, hrel⟩ := exists_surjective_factoredPoly_mem_ker d α f hf
    have : Module.Projective R' (R' ⊗[R] P) :=
      projective_of_split_presentation hR'A hAP d α hg hrel
    exact Module.Projective.of_projective_tensorProduct (R := R) (M := P) R'

end Projective

/-! ### Flatness descends along an injective integral map -/

section Integral


/-- Flatness of a base change survives a further base change of the base: if `R ⊗[A] P` is flat
over `R`, then `S ⊗[A] P` is flat over `S` for any `R`-algebra `S`. -/
private lemma flat_baseChange_tower {A R S P : Type*} [CommRing A] [CommRing R] [CommRing S]
    [Algebra A R] [Algebra R S] [Algebra A S] [IsScalarTower A R S]
    [AddCommGroup P] [Module A P] [Module.Flat R (R ⊗[A] P)] :
    Module.Flat S (S ⊗[A] P) := by
  have : Module.Flat S (S ⊗[R] (R ⊗[A] P)) := Module.Flat.baseChange R S _
  exact Module.Flat.of_linearEquiv
    (TensorProduct.AlgebraTensorModule.cancelBaseChange A R S S P).symm

/-- For an algebra map `b : E → E'` of `B`-algebras and a `B`-module `P`, the map
`E ⊗[B] P → E' ⊗[B] P` induced by `b` is a base change along `b`, where `E' ⊗[B] P` carries the
`E`-module structure obtained by restriction of scalars along `b`. This is the base-change condition
for the module system of Stacks 02JO (3), in exactly the shape
`Module.Flat.eventually_flat_of_directed` asks for. The restricted `E`-module structure is equal
but not definitionally equal to the canonical one, so the instances are supplied explicitly. -/
private lemma isBaseChange_tensor_gate {B E E' P : Type*} [CommRing B] [CommRing E] [CommRing E']
    [Algebra B E] [Algebra B E'] [AddCommGroup P] [Module B P] (b : E →ₐ[B] E')
    (n : E ⊗[B] P →ₛₗ[b.toRingHom] E' ⊗[B] P) (hn : ∀ e p, n (e ⊗ₜ p) = b e ⊗ₜ p) :
    letI algI : Algebra E E' := b.toRingHom.toAlgebra
    letI modI : Module E (E' ⊗[B] P) := Module.compHom _ b.toRingHom
    @IsBaseChange E (E ⊗[B] P) (E' ⊗[B] P) E' _ _ _ _ algI _ modI _
      (IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl)
      ⟨n.toAddHom, fun x y ↦ n.map_smul' x y⟩ := by
  let algI : Algebra E E' := b.toRingHom.toAlgebra
  have : IsScalarTower B E E' := IsScalarTower.of_algebraMap_eq fun x ↦ (b.commutes x).symm
  have key := isBaseChange_tensorProduct_map (R := B) (P := P) E' (IsBaseChange.linearMap E E')
  have hfun : ∀ z, n z = TensorProduct.AlgebraTensorModule.map (Algebra.linearMap E E')
      (LinearMap.id (R := B) (M := P)) z := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul e p =>
      rw [hn]
      rfl
    | add z w hz hw => rw [map_add, map_add, hz, hw]
  convert key using 2
  · exact Module.ext' _ _ fun x y ↦ IsScalarTower.algebraMap_smul E' x y
  · exact DFunLike.ext _ _ hfun

set_option maxHeartbeats 1600000 in
-- The directed system below carries five interlocking towers of algebra and module
-- structures over `Finset S`, and both unification of the colimit data against Stacks 02JO (3)
-- and the instance searches for the tensor products exceed the default budget.
/-- Let `B` be an `A`-algebra of finite presentation, `P` a finitely presented `B`-module and `D`
a monotone family of `A`-subalgebras of `S` with `z ∈ D {z}` for every `z`, so that `S` is the
directed union of the `D s`. If `S ⊗[A] P` is flat over `S`, then `D s ⊗[A] P` is flat over `D s`
for some finite `s ⊆ S`. This is the spreading-out step of Stacks 0534: Stacks 02JO (3) applied
to the directed system of `D s`-algebras `D s ⊗[A] B` with the modules `(D s ⊗[A] B) ⊗[B] P`. -/
@[ega "IV 11.2.7" "special case"]
private lemma exists_flat_baseChange_of_monotone
    {A : Type*} {B : Type uB} {S : Type (max uB uS)} {P : Type*}
    [CommRing A] [CommRing B] [CommRing S]
    [Algebra A B] [Algebra A S] [Algebra.FinitePresentation A B]
    [AddCommGroup P] [Module B P] [Module A P] [IsScalarTower A B P]
    [Module.FinitePresentation B P]
    (D : Finset S → Subalgebra A S) (hD : Monotone D) (hmem : ∀ z, z ∈ D {z})
    (hflat : Module.Flat S (S ⊗[A] P)) :
    ∃ s : Finset S, Module.Flat (D s) ((D s) ⊗[A] P) := by
  classical
  let a (i j : Finset S) (h : i ≤ j) : D i →ₐ[A] D j := Subalgebra.inclusion (hD h)
  have : DirectedSystem (fun i ↦ ↥(D i)) (fun i j h ↦ ⇑(a i j h)) :=
    ⟨fun _ _ ↦ rfl, fun _ _ _ _ _ _ ↦ rfl⟩
  have hρ : ∀ i j (h : i ≤ j) (z : D i),
      algebraMap (D j) S (a i j h z) = algebraMap (D i) S z := fun _ _ _ _ ↦ rfl
  have hsurj : ∀ z : S, ∃ i, ∃ w : D i, algebraMap (D i) S w = z :=
    fun z ↦ ⟨{z}, ⟨z, hmem z⟩, rfl⟩
  have hzero : ∀ i (z : D i), algebraMap (D i) S z = 0 →
      ∃ j, ∃ (h : i ≤ j), a i j h z = 0 := fun i z hz ↦ ⟨i, le_rfl, Subtype.ext hz⟩
  let E (i : Finset S) := D i ⊗[A] B
  let T := S ⊗[A] B
  let : Algebra B T := Algebra.TensorProduct.rightAlgebra
  let (i : Finset S) : Algebra B (E i) := Algebra.TensorProduct.rightAlgebra
  have hfp (i : Finset S) : Algebra.FinitePresentation (D i) (E i) :=
    inferInstanceAs (Algebra.FinitePresentation (D i) (D i ⊗[A] B))
  let b (i j : Finset S) (h : i ≤ j) : E i →ₐ[B] E j :=
    { Algebra.TensorProduct.map (a i j h) (AlgHom.id A B) with
      commutes' := fun z ↦ by
        change (Algebra.TensorProduct.map (a i j h) (AlgHom.id A B)) ((1 : D i) ⊗ₜ[A] z)
          = (1 : D j) ⊗ₜ[A] z
        simp }
  let σ (i : Finset S) : E i →ₐ[B] T :=
    { Algebra.TensorProduct.map (IsScalarTower.toAlgHom A (D i) S) (AlgHom.id A B) with
      commutes' := fun z ↦ by
        change (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A (D i) S) (AlgHom.id A B))
          ((1 : D i) ⊗ₜ[A] z) = (1 : S) ⊗ₜ[A] z
        simp }
  have : DirectedSystem E (fun i j h ↦ ⇑(b i j h)) := by
    constructor
    · intro i z
      induction z using TensorProduct.inductionOn with
      | tmul _ _ => rfl
      | add z w hz hw => simp only [map_add, hz, hw]
    · intro k j i hij hjk z
      induction z using TensorProduct.inductionOn with
      | tmul _ _ => rfl
      | add z w hz hw => simp only [map_add, hz, hw]
  have hσ : ∀ i j (h : i ≤ j) (z : E i), σ j (b i j h z) = σ i z := by
    intro i j h z
    induction z using TensorProduct.inductionOn with
    | tmul _ _ => rfl
    | add z w hz hw => simp only [map_add, hz, hw]
  have hc := Stacks.ColimitPresentation.FPModules.isModuleColimit
    (fun i j (h : i ≤ j) ↦ a i j h) hρ hsurj hzero B
  have hEsurj : ∀ z : T, ∃ i, ∃ w : E i, σ i w = z := hc.jointly_surjective
  have hEzero : ∀ i (z : E i), σ i z = 0 → ∃ j, ∃ (h : i ≤ j), b i j h z = 0 := by
    intro i z hz
    obtain ⟨j, h, hj⟩ := hc.exists_eq_of_canonMod_eq i z 0
      (by change σ i z = σ i 0; simpa only [map_zero] using hz)
    refine ⟨j, h, ?_⟩
    change b i j h z = b i j h 0 at hj
    simpa only [map_zero] using hj
  let N (i : Finset S) := E i ⊗[B] P
  let Q := T ⊗[B] P
  let n (i j : Finset S) (h : i ≤ j) : N i →ₛₗ[(b i j h).toRingHom] N j :=
    { TensorProduct.map (b i j h).toLinearMap (LinearMap.id (R := B) (M := P)) with
      map_smul' := by
        intro c z
        simp only [LinearMap.toFun_eq_coe]
        induction z using TensorProduct.inductionOn with
        | tmul e p =>
          change b i j h (c * e) ⊗ₜ[B] p = (b i j h c * b i j h e) ⊗ₜ[B] p
          rw [map_mul]
        | add z w hz hw => simp only [smul_add, map_add, hz, hw] }
  have : DirectedSystem N (fun i j h ↦ ⇑(n i j h)) := by
    constructor
    · intro i z
      induction z using TensorProduct.inductionOn with
      | tmul e p =>
        change b i i le_rfl e ⊗ₜ[B] p = e ⊗ₜ[B] p
        rw [DirectedSystem.map_self' (fun i j h ↦ b i j h)]
      | add z w hz hw => simp only [map_add, hz, hw]
    · intro k j i hij hjk z
      induction z using TensorProduct.inductionOn with
      | tmul e p =>
        change b j k hjk (b i j hij e) ⊗ₜ[B] p = b i k (hij.trans hjk) e ⊗ₜ[B] p
        rw [DirectedSystem.map_map' (fun i j h ↦ b i j h) hij hjk]
      | add z w hz hw => simp only [map_add, hz, hw]
  let ν (i : Finset S) : N i →ₛₗ[(σ i).toRingHom] Q :=
    { TensorProduct.map (σ i).toLinearMap (LinearMap.id (R := B) (M := P)) with
      map_smul' := by
        intro c z
        simp only [LinearMap.toFun_eq_coe]
        induction z using TensorProduct.inductionOn with
        | tmul e p =>
          change σ i (c * e) ⊗ₜ[B] p = (σ i c * σ i e) ⊗ₜ[B] p
          rw [map_mul]
        | add z w hz hw => simp only [smul_add, map_add, hz, hw] }
  have hν : ∀ i j (h : i ≤ j) (z : N i), ν j (n i j h z) = ν i z := by
    intro i j h z
    induction z using TensorProduct.inductionOn with
    | tmul e p =>
      change σ j (b i j h e) ⊗ₜ[B] p = σ i e ⊗ₜ[B] p
      rw [hσ i j h]
    | add z w hz hw => simp only [map_add, hz, hw]
  have hNcolim : (∀ z : Q, ∃ i, ∃ w : N i, ν i w = z) ∧
      (∀ i (z : N i), ν i z = 0 → ∃ j, ∃ (h : i ≤ j), n i j h z = 0) := by
    let (i : Finset S) : Algebra (E i) T := (σ i).toRingHom.toAlgebra
    have (i : Finset S) : IsScalarTower B (E i) T :=
      IsScalarTower.of_algebraMap_eq fun z ↦ ((σ i).commutes z).symm
    have hmc := Stacks.ColimitPresentation.FPModules.isModuleColimit (A := B)
      (fun i j (h : i ≤ j) ↦ b i j h) hσ hEsurj hEzero P
    refine ⟨hmc.jointly_surjective, ?_⟩
    intro i z hz
    obtain ⟨j, h, hj⟩ := hmc.exists_eq_of_canonMod_eq i z 0
      (by change ν i z = ν i 0; simpa only [map_zero] using hz)
    refine ⟨j, h, ?_⟩
    change n i j h z = n i j h 0 at hj
    simpa only [map_zero] using hj
  have : Module.Flat S Q :=
    Module.Flat.of_linearEquiv (Algebra.IsPushout.cancelBaseChange A S B T P)
  have : Algebra.FinitePresentation S T := inferInstance
  have : Module.FinitePresentation T Q := inferInstance
  have hab : ∀ i j (h : i ≤ j),
      ((b i j h).toRingHom).comp (algebraMap (D i) (E i))
        = (algebraMap (D j) (E j)).comp ((a i j h).toRingHom) := fun i j h ↦ by ext z; rfl
  have hρσ : ∀ i : Finset S, ((σ i).toRingHom).comp (algebraMap (D i) (E i))
      = (algebraMap S T).comp (algebraMap (D i) S) := fun i ↦ by ext z; rfl
  have hpush : ∀ i j (h : i ≤ j), CategoryTheory.IsPushout
      (CommRingCat.ofHom ((a i j h).toRingHom))
      (CommRingCat.ofHom (algebraMap (D i) (E i)))
      (CommRingCat.ofHom (algebraMap (D j) (E j)))
      (CommRingCat.ofHom ((b i j h).toRingHom)) := by
    intro i j h
    let : Algebra (D i) (D j) := ((a i j h).toRingHom).toAlgebra
    have : IsScalarTower A (D i) (D j) :=
      IsScalarTower.of_algebraMap_eq fun z ↦ ((a i j h).commutes z).symm
    let : Algebra (E i) (E j) := ((b i j h).toRingHom).toAlgebra
    have : IsScalarTower (D i) (E i) (E j) :=
      IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    have : Algebra.IsPushout (D i) (D j) (E i) (E j) :=
      Algebra.IsPushout.tensorProduct_tensorProduct A B (D i) (D j) (by
        ext w
        change (Algebra.TensorProduct.map (a i j h) (AlgHom.id A B)) ((1 : D i) ⊗ₜ[A] w)
          = (1 : D j) ⊗ₜ[A] w
        simp)
    exact CommRingCat.isPushout_iff_isPushout.mpr ‹_›
  obtain ⟨i, hi⟩ := Module.Flat.eventually_flat_of_directed (R := S) (S := T) Q
    (fun i j h ↦ (a i j h).toRingHom) (fun i j h ↦ (b i j h).toRingHom) n hab
    (fun i ↦ algebraMap (D i) S) (fun i ↦ (σ i).toRingHom) ν hρ hσ hν hρσ hsurj hzero
    hEsurj hEzero hNcolim.1 hNcolim.2 hpush
    (fun i j h ↦ isBaseChange_tensor_gate (b i j h) (n i j h) fun _ _ ↦ rfl)
    hfp (fun i ↦ inferInstance)
  refine ⟨i, ?_⟩
  have hmod : Module.compHom (N i) (algebraMap (D i) (E i))
      = (inferInstance : Module (D i) (N i)) :=
    Module.ext' _ _ fun z w ↦ IsScalarTower.algebraMap_smul (E i) z w
  have hi' : @Module.Flat (D i) (N i) _ _
      (Module.compHom (N i) (algebraMap (D i) (E i))) := hi i le_rfl
  rw [hmod] at hi'
  have : Module.Flat (D i) (N i) := hi'
  exact Module.Flat.of_linearEquiv
    (Algebra.IsPushout.cancelBaseChange A (D i) B (E i) P).symm

/-- Finitely many elements of an integral extension `S` of `R` are integral over a single
subalgebra of `R` of finite type over the base. -/
private lemma exists_fg_subalgebra_isIntegral
    {A R S : Type*} [CommRing A] [CommRing R] [CommRing S]
    [Algebra A R] [Algebra R S] [Algebra A S] [IsScalarTower A R S]
    [Algebra.IsIntegral R S] (s : Finset S) :
    ∃ C : Subalgebra A R, C.FG ∧ ∀ z ∈ s, IsIntegral C z := by
  classical
  choose t ht hit using fun z : s ↦
    isIntegral_iff_isIntegral_closure_finite.mp
      (Algebra.IsIntegral.isIntegral (R := R) (z : S))
  have hc : (⋃ z : s, t z).Finite := Set.finite_iUnion ht
  refine ⟨Algebra.adjoin A (⋃ z : s, t z), (Subalgebra.fg_iff_finiteType _).mpr
      (Algebra.FiniteType.adjoin_of_finite hc), fun z hz ↦ ?_⟩
  have hle : Subring.closure (t ⟨z, hz⟩)
      ≤ (Algebra.adjoin A (⋃ z : s, t z)).toSubring :=
    Subring.closure_le.mpr fun r hr ↦
      Algebra.subset_adjoin (Set.mem_iUnion.mpr ⟨⟨z, hz⟩, hr⟩)
  let : Algebra (Subring.closure (t ⟨z, hz⟩)) (Algebra.adjoin A (⋃ z : s, t z)) :=
    (Subring.inclusion hle).toAlgebra
  have : IsScalarTower (Subring.closure (t ⟨z, hz⟩))
      (Algebra.adjoin A (⋃ z : s, t z)) S :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  exact (hit ⟨z, hz⟩).tower_top

set_option maxHeartbeats 1600000 in
-- The proof threads one module through six successive base changes, and both the descent datum
-- and the `ULift` of the integral extension force large unification problems.
/-- Flatness descends along an injective integral ring map for a module finitely presented over
an `R`-algebra `T` of finite presentation: if `S ⊗[R] M` is flat over `S`, then `M` is flat over
`R`. The datum `(R → T, M)` first descends to a subring `A` of `R` of finite type over `ℤ`
(Stacks 00R1); the integral extension is then the directed union of its finite-type
`A`-subalgebras, over which flatness holds eventually by Stacks 02JO (3); and a single finite
injective stage suffices by Stacks 0533. -/
@[ega "IV 11.5.5" "special case"]
private lemma flat_of_flat_baseChange_of_finitePresentation
    {R : Type u} {S : Type v} {T : Type u} {M : Type w}
    [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra.IsIntegral R S] [Algebra R T]
    [Algebra.FinitePresentation R T]
    [AddCommGroup M] [Module T M] [Module R M] [IsScalarTower R T M]
    [Module.FinitePresentation T M]
    (hinj : Function.Injective (algebraMap R S))
    (hflat : Module.Flat S (S ⊗[R] M)) : Module.Flat R M := by
  classical
  obtain ⟨A, B, P, _, _, _, _, _, _, _, _, f, hA, hB, hP, hpush, hbase⟩ :=
    Algebra.exists_subring_finiteType_int_isPushout_isBaseChange (R := R) (S := T) M
  have := hA
  have := hB
  have := hP
  have := hpush
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℤ A
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  have : Algebra.FinitePresentation A B := Algebra.FinitePresentation.of_finiteType.mp hB
  have : Module.FinitePresentation B P := Module.finitePresentation_of_finite B P
  let : Module A P := Module.compHom P (algebraMap A B)
  have : IsScalarTower A B P := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let e : (R ⊗[A] P) ≃ₗ[R] M :=
    (Algebra.IsPushout.cancelBaseChange A R B T P).symm.trans (hbase.equiv.restrictScalars R)
  have hSflat : Module.Flat S (S ⊗[A] P) :=
    Module.Flat.of_linearEquiv
      ((TensorProduct.AlgebraTensorModule.cancelBaseChange A R S S P).symm.trans
        (e.baseChange R S _ _))
  -- Move `S` into the universe of the descent datum, so that the directed system of finite-type
  -- subalgebras of `S` and the system of their base changes to `B` live in one universe.
  let S' := ULift.{u, v} S
  have hS'inj : Function.Injective (algebraMap R S') := fun x y hxy ↦
    hinj (congrArg ULift.down hxy)
  have : Algebra.IsIntegral R S' :=
    (ULift.algEquiv (R := R) (A := S)).isIntegral_iff.mpr inferInstance
  have : IsScalarTower A S S' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower A R S' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hS'flat : Module.Flat S' (S' ⊗[A] P) :=
    flat_baseChange_tower (A := A) (R := S) (S := S') (P := P)
  obtain ⟨D, hDmono, hDmem, hDle⟩ : ∃ D : Finset S' → Subalgebra A S', Monotone D ∧
      (∀ z, z ∈ D {z}) ∧ ∀ s, D s ≤ Algebra.adjoin A (s : Set S') :=
    ⟨fun s ↦ Algebra.adjoin A (s : Set S'),
      fun _ _ h ↦ Algebra.adjoin_mono (Finset.coe_subset.mpr h),
      fun z ↦ Algebra.subset_adjoin (by simp), fun _ ↦ le_rfl⟩
  obtain ⟨s, hs⟩ :=
    exists_flat_baseChange_of_monotone (B := B) (P := P) D hDmono hDmem hS'flat
  obtain ⟨R₁, hR₁, hint⟩ := exists_fg_subalgebra_isIntegral (A := A) (R := R) (S := S') s
  have : Algebra.FiniteType A R₁ := (Subalgebra.fg_iff_finiteType R₁).mp hR₁
  have : IsNoetherianRing R₁ := Algebra.FiniteType.isNoetherianRing A R₁
  have : Module.Finite R₁ (Algebra.adjoin R₁ (s : Set S')) :=
    Algebra.finite_adjoin_of_finite_of_isIntegral s.finite_toSet hint
  have hCflat : Module.Flat (Algebra.adjoin R₁ (s : Set S'))
      ((Algebra.adjoin R₁ (s : Set S')) ⊗[A] P) := by
    have hDC : D s ≤ (Algebra.adjoin R₁ (s : Set S')).restrictScalars A :=
      (hDle s).trans (Algebra.adjoin_le_iff.mpr fun z hz ↦ Algebra.subset_adjoin hz)
    let d : D s →ₐ[A] (Algebra.adjoin R₁ (s : Set S')) := Subalgebra.inclusion hDC
    let : Algebra (D s) (Algebra.adjoin R₁ (s : Set S')) := d.toAlgebra
    have : IsScalarTower A (D s) (Algebra.adjoin R₁ (s : Set S')) :=
      IsScalarTower.of_algebraMap_eq fun z ↦ (d.commutes z).symm
    have := hs
    exact flat_baseChange_tower (A := A) (R := D s)
      (S := Algebra.adjoin R₁ (s : Set S')) (P := P)
  have := hCflat
  have : Module.Flat (Algebra.adjoin R₁ (s : Set S'))
      ((Algebra.adjoin R₁ (s : Set S')) ⊗[R₁] (R₁ ⊗[A] P)) :=
    Module.Flat.of_linearEquiv (TensorProduct.AlgebraTensorModule.cancelBaseChange A R₁
      (Algebra.adjoin R₁ (s : Set S')) (Algebra.adjoin R₁ (s : Set S')) P)
  have hR₁C : Function.Injective (algebraMap R₁ (Algebra.adjoin R₁ (s : Set S'))) :=
    fun _ _ h ↦ Subtype.ext (hS'inj (congrArg Subtype.val h))
  have : Module.Flat R₁ (R₁ ⊗[A] P) :=
    Module.Flat.of_finite_injective_baseChange
      (S := Algebra.adjoin R₁ (s : Set S')) (M := R₁ ⊗[A] P) hR₁C inferInstance
  have : Module.Flat R (R ⊗[A] P) :=
    flat_baseChange_tower (A := A) (R := R₁) (S := R) (P := P)
  exact Module.Flat.of_linearEquiv e.symm

/-- Let `R → S` be an injective integral ring map and let `M` be a module over `R[x₁, …, xₙ]` that
is finitely presented there and carries the restricted `R`-action. If the scalar extension
`S ⊗[R] M` is flat over `S`, then `M` is flat over `R`. -/
@[stacks 0534]
theorem Module.Flat.of_integral_injective_baseChange
    {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S] [Algebra.IsIntegral R S]
    {n : ℕ} {M : Type w} [AddCommGroup M]
    [Module (MvPolynomial (Fin n) R) M] [Module R M]
    [IsScalarTower R (MvPolynomial (Fin n) R) M]
    [Module.FinitePresentation (MvPolynomial (Fin n) R) M]
    (hRS : Function.Injective (algebraMap R S))
    (hM : Module.Flat S (S ⊗[R] M)) : Module.Flat R M :=
  flat_of_flat_baseChange_of_finitePresentation (T := MvPolynomial (Fin n) R) hRS hM

end Integral
