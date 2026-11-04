module

public import StacksFrontier.RingTheory.Sequence.RegularLocus
public import StacksFrontier.RingTheory.SpreadingOut.FlatModel
public import StacksFrontier.RingTheory.FinitePresentation.FiniteTypeSystem
public import StacksFrontier.RingTheory.Spectrum.Prime.Specialization
public import StacksFrontier.RingTheory.RelativeDimension.Semicontinuity
public import StacksFrontier.RingTheory.RelativeDimension.BaseChange
public import StacksFrontier.RingTheory.RelativeDimension.Basic
public import StacksFrontier.RingTheory.CompleteIntersection.Relative
public import StacksFrontier.RingTheory.Syntomic.Morphisms
public import StacksFrontier.RingTheory.MvPolynomial.MaximalIdeal
public import StacksFrontier.RingTheory.CohenMacaulay.OpenLocus
public import StacksFrontier.RingTheory.Flat.LocalCriteria
public import StacksFrontier.RingTheory.Flat.OpenFlatLocus
public import StacksFrontier.RingTheory.QuasiFinite.Locus
public import StacksFrontier.RingTheory.CohenMacaulay.RegularSequence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Faithfully flat models of ring maps of finite presentation

This file proves Lemma 034Y, on spreading out faithfully flat ring maps of finite presentation.


**Lemma 034Y.** Let `R → A → B` be ring maps with `A → B` faithfully flat of finite presentation.
Then `A → B` is the base change of a faithfully flat ring map `A₀ → B₀` of finite presentation,
with `A₀` of finite presentation over `R`. The proof first treats `R = ℤ`. Write `A` as the
directed union of its finite type `ℤ`-subalgebras `A_λ` containing a subring `A_{λ₀}` over which
`A → B` is defined by a finite type algebra `B_{λ₀}`, and put `B_λ = A_λ ⊗_{A_{λ₀}} B_{λ₀}`, so
that `B = A ⊗_{A_λ} B_λ` for every `λ` (Lemma 00R1). Flatness of `B` over `A` gives a stage `λ`
at which `B_λ` is flat over `A_λ` (Lemma 02JO). The image `U` of `Spec(B_λ) → Spec(A_λ)` is open
(Proposition 00I1), say with complement `V(I)`. Since `Spec(B) → Spec(A)` is surjective
(Lemma 00HQ) and every prime of `A` maps into `U`, the ideal `IA` is the unit ideal; a relation
`∑ fᵢ rᵢ = 1` with `fᵢ ∈ I`, `rᵢ ∈ A` lives in some `A_μ ⊇ A_λ`, and then every prime of `A_μ`
maps into `U`. As the image of a base change is the preimage of the image,
`Spec(B_μ) → Spec(A_μ)` is surjective, and `B_μ` is faithfully flat over `A_μ`. For general `R`

## Main results

* `Algebra.exists_faithfullyFlat_finitePresentation_model`: Lemma 034Y.
* `Algebra.FiniteTypeSystem.exists_faithfullyFlat_stage`: in the system of Lemma 00R1 a faithfully
  flat algebra has a faithfully flat stage.
* `PrimeSpectrum.mem_range_comap_of_isPushout`: the image of `Spec` of a base change contains the
  preimage of the image.

## Implementation notes

In Lemma 034Y the commutative diagram is the data `R → A₀ → A` with `IsScalarTower R A₀ A` and
`A₀ → B₀ → B`, `A₀ → A → B` through a common `A₀ → B`, and `B = A ⊗_{A₀} B₀` is
`Algebra.IsPushout A₀ A B₀ B`.

## References

* [Stacks Project, Tag 034Y](https://stacks.math.columbia.edu/tag/034Y)
-/

@[expose] public section

universe u v

open scoped TensorProduct

/-- A prime of `R'` whose image in `Spec R` lies in the image of `Spec S` lies itself in the image
of `Spec S'`, for any pushout square `R → S`, `R' → S'`: the image of the base change is the
preimage of the image. -/
theorem PrimeSpectrum.mem_range_comap_of_isPushout {R S R' S' : Type*} [CommRing R] [CommRing S]
    [CommRing R'] [CommRing S'] [Algebra R S] [Algebra R R'] [Algebra S S'] [Algebra R' S']
    [Algebra R S'] [IsScalarTower R R' S'] [IsScalarTower R S S'] [Algebra.IsPushout R S R' S']
    (p' : PrimeSpectrum R')
    (h : PrimeSpectrum.comap (algebraMap R R') p' ∈
      Set.range (PrimeSpectrum.comap (algebraMap R S))) :
    p' ∈ Set.range (PrimeSpectrum.comap (algebraMap R' S')) := by
  rw [← PrimeSpectrum.nontrivial_iff_mem_rangeComap]
  set p : Ideal R := p'.asIdeal.comap (algebraMap R R')
  let _ : Algebra p.ResidueField p'.asIdeal.ResidueField :=
    (Ideal.ResidueField.map p p'.asIdeal (algebraMap R R') rfl).toAlgebra
  have : IsScalarTower R p.ResidueField p'.asIdeal.ResidueField :=
    .of_algebraMap_eq fun x => by
      rw [RingHom.algebraMap_toAlgebra, Ideal.ResidueField.map_algebraMap,
        ← IsScalarTower.algebraMap_apply]
  have hp : Nontrivial (p.ResidueField ⊗[R] S) :=
    (PrimeSpectrum.nontrivial_iff_mem_rangeComap (⟨p, inferInstance⟩ : PrimeSpectrum R)).mpr h
  have : Nontrivial (p'.asIdeal.ResidueField ⊗[p.ResidueField]
      (p.ResidueField ⊗[R] S)) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_left
      (R := p.ResidueField) (A := p'.asIdeal.ResidueField) (B := p.ResidueField ⊗[R] S)
      (algebraMap p.ResidueField (p.ResidueField ⊗[R] S)).injective
  have : Nontrivial (p'.asIdeal.ResidueField ⊗[R] S) :=
    (Algebra.TensorProduct.cancelBaseChange R p.ResidueField p.ResidueField
      p'.asIdeal.ResidueField S).injective.nontrivial
  have : Nontrivial (S ⊗[R] p'.asIdeal.ResidueField) :=
    (Algebra.TensorProduct.comm R _ S).injective.nontrivial
  have : Nontrivial (S' ⊗[R'] p'.asIdeal.ResidueField) :=
    (Algebra.IsPushout.cancelBaseChangeAlg R S R' S' _).symm.injective.nontrivial
  exact (Algebra.TensorProduct.comm R' S' _).injective.nontrivial

namespace Algebra.FiniteTypeSystem

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
  (R₀ : Subring A) (S₀ : Type u) [CommRing S₀] [Algebra R₀ S₀] [Algebra S₀ B]
  [IsScalarTower R₀ S₀ B] [Algebra.FiniteType ℤ R₀] [Algebra.FiniteType R₀ S₀]
  [Algebra.IsPushout R₀ A S₀ B]

omit [Algebra.FiniteType ℤ R₀] [Algebra.FiniteType R₀ S₀] [Algebra.IsPushout R₀ A S₀ B] in
/-- The square `R_λ → S_λ → B`, `R_λ → A → B` commutes. -/
theorem algebraMap_base_ring_comp (i : Index R₀) :
    (algebraMap (Ring R₀ S₀ i) B).comp (algebraMap (Base R₀ i) (Ring R₀ S₀ i)) =
      (algebraMap A B).comp (algebraMap (Base R₀ i) A) := by
  rw [← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]

/-- **A flat stage of the system.** If `B` is flat over `A`, then `S_λ` is flat over `R_λ` for
some `λ`. -/
theorem exists_flat_stage_self [Module.Flat A B] : ∃ i, Module.Flat (Base R₀ i) (Ring R₀ S₀ i) := by
  have e (C M : Type u) [CommRing C] [CommRing M] [Algebra S₀ M] [Algebra C M] :
      M ⊗[S₀] S₀ ≃ₗ[C] M :=
    (_root_.TensorProduct.rid S₀ M).toAddEquiv.toLinearEquiv fun a x => by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul m s =>
        simp only [TensorProduct.smul_tmul', LinearEquiv.coe_toAddEquiv]
        simp [Algebra.smul_def, mul_left_comm]
      | add x y hx hy => simp_all [smul_add]
  obtain ⟨i, hi⟩ := exists_flat_stage R₀ S₀ S₀ (S := B) fun q => by
    have : Module.Flat A (Localization.AtPrime q.asIdeal) := Module.Flat.trans A B _
    exact Module.Flat.of_linearEquiv (e A (Localization.AtPrime q.asIdeal))
  exact ⟨i, Module.Flat.of_linearEquiv (e (Base R₀ i) (Ring R₀ S₀ i)).symm⟩

variable (B) in
/-- **A faithfully flat stage of the system.** If `B` is faithfully flat over `A`, then `S_λ` is
faithfully flat over `R_λ` for some `λ`. -/
theorem exists_faithfullyFlat_stage [Module.FaithfullyFlat A B] :
    ∃ i, Module.FaithfullyFlat (Base R₀ i) (Ring R₀ S₀ i) := by
  obtain ⟨i, hi⟩ := exists_flat_stage_self R₀ S₀ (B := B)
  have : IsNoetherianRing (Base R₀ i) := Algebra.FiniteType.isNoetherianRing ℤ _
  have : Algebra.FinitePresentation (Base R₀ i) (Ring R₀ S₀ i) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  set U := Set.range (PrimeSpectrum.comap (algebraMap (Base R₀ i) (Ring R₀ S₀ i)))
  have hU : IsOpen U :=
    (primeSpectrum_comap_isOpenMap_of_flat_of_finitePresentation _ _).isOpen_range
  let I := PrimeSpectrum.vanishingIdeal Uᶜ
  have hZ : PrimeSpectrum.zeroLocus I = Uᶜ := by
    rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hU.isClosed_compl.closure_eq]
  have hI : I.map (algebraMap (Base R₀ i) A) = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨Q, hQ⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := A) (B := B)
      ⟨m, hm.isPrime⟩
    have h1 : PrimeSpectrum.comap (algebraMap (Base R₀ i) A) ⟨m, hm.isPrime⟩ ∈
        PrimeSpectrum.zeroLocus I := Ideal.map_le_iff_le_comap.mp hle
    rw [hZ] at h1
    refine h1 ⟨PrimeSpectrum.comap (algebraMap (Ring R₀ S₀ i) B) Q, ?_⟩
    rw [← hQ, ← PrimeSpectrum.comap_comp_apply, ← PrimeSpectrum.comap_comp_apply,
      algebraMap_base_ring_comp]
  classical
  obtain ⟨n, c, x, hx⟩ := Submodule.mem_span_set'.mp (hI ▸ Submodule.mem_top (x := (1 : A)))
  choose x' hx'I hx' using fun k => (x k).2
  choose k d hd using fun m => base_jointly_surjective R₀ (c m)
  obtain ⟨j, hj⟩ := (insert i (Finset.univ.image k)).exists_le
  have hij : i ≤ j := hj i (Finset.mem_insert_self _ _)
  have hkj (m : Fin n) : k m ≤ j :=
    hj _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ m)))
  have : Fact (i ≤ j) := ⟨hij⟩
  have hIj : I.map (algebraMap (Base R₀ i) (Base R₀ j)) = ⊤ := by
    refine (Ideal.eq_top_iff_one _).mpr ?_
    have hsum : ∑ m, baseMap R₀ (hkj m) (d m) * algebraMap (Base R₀ i) (Base R₀ j) (x' m) = 1 := by
      apply algebraMap_base_injective R₀ j
      rw [map_one, ← hx, map_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [map_mul, smul_eq_mul, ← hx', ← hd m]
      rfl
    rw [← hsum]
    exact Ideal.sum_mem _ fun m _ => Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (hx'I m))
  have : Module.Flat (Base R₀ j) (Ring R₀ S₀ j) :=
    Module.Flat.isBaseChange (Base R₀ i) (Base R₀ j) (Ring R₀ S₀ i) (Ring R₀ S₀ j)
      (ringMap_isPushout R₀ S₀ (i := i) (j := j)).out
  have : Algebra.IsPushout (Base R₀ i) (Ring R₀ S₀ i) (Base R₀ j) (Ring R₀ S₀ j) :=
    (ringMap_isPushout R₀ S₀ (i := i) (j := j)).symm
  refine ⟨j, Module.FaithfullyFlat.of_comap_surjective fun p => ?_⟩
  refine PrimeSpectrum.mem_range_comap_of_isPushout (R := Base R₀ i) (S := Ring R₀ S₀ i) p ?_
  by_contra hp
  rw [← Set.mem_compl_iff, ← hZ] at hp
  have : I.map (algebraMap (Base R₀ i) (Base R₀ j)) ≤ p.asIdeal := Ideal.map_le_iff_le_comap.mpr hp
  exact p.2.ne_top (top_le_iff.mp (hIj ▸ this))

end Algebra.FiniteTypeSystem

open Algebra.FiniteTypeSystem in
/-- **Stacks 034Y over `ℤ`.** A faithfully flat ring map `A → B` of finite presentation is the
base change of a faithfully flat ring map `A₀ → B₀` of finite presentation along a ring map
`A₀ → A` with `A₀` of finite presentation over `ℤ`. -/
theorem Algebra.exists_faithfullyFlat_finitePresentation_model_int {A B : Type u} [CommRing A]
    [CommRing B] [Algebra A B] [Module.FaithfullyFlat A B] [Algebra.FinitePresentation A B] :
    ∃ (A₀ B₀ : Type u) (_ : CommRing A₀) (_ : CommRing B₀) (_ : Algebra A₀ B₀) (_ : Algebra A₀ A)
      (_ : Algebra B₀ B) (_ : Algebra A₀ B) (_ : IsScalarTower A₀ A B) (_ : IsScalarTower A₀ B₀ B),
      Algebra.FinitePresentation ℤ A₀ ∧ Module.FaithfullyFlat A₀ B₀ ∧
        Algebra.FinitePresentation A₀ B₀ ∧ Algebra.IsPushout A₀ A B₀ B := by
  obtain ⟨R₀, S₀, -, _, _, _, _, -, -, -, -, -, hZ, hS₀, -, hpush, -⟩ :=
    Algebra.exists_subring_finiteType_int_isPushout_isBaseChange (R := A) (S := B) B
  obtain ⟨i, hi⟩ := exists_faithfullyFlat_stage B R₀ S₀
  have : IsNoetherianRing (Base R₀ i) := Algebra.FiniteType.isNoetherianRing ℤ _
  exact ⟨Base R₀ i, Ring R₀ S₀ i, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance,
    Algebra.FinitePresentation.of_finiteType.mp inferInstance, hi,
    Algebra.FinitePresentation.of_finiteType.mp inferInstance, ringToRing_isPushout R₀ S₀ i⟩

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- **Stacks 034Y.** Let `R → A → B` be ring maps with `A → B` faithfully flat of finite
presentation. Then there are an `R`-algebra `A₀` of finite presentation and a faithfully flat
`A₀`-algebra `B₀` of finite presentation, with maps `A₀ → A` of `R`-algebras and `B₀ → B`
compatible with `A₀ → B₀` and `A → B`, such that `B = A ⊗_{A₀} B₀`. -/
@[stacks 034Y "The diagram is the data `R → A₀ → A` with `IsScalarTower R A₀ A` (the left square)
and `A₀ → B₀ → B`, `A₀ → A → B` through a common `A₀ → B` (the right square); `B = A ⊗_{A₀} B₀` is
`Algebra.IsPushout A₀ A B₀ B`. The rings `A₀`, `B₀` live in the universe of `R`, `A` and `B`."]
theorem Algebra.exists_faithfullyFlat_finitePresentation_model {R : Type v} {A B : Type u}
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra A B] [Module.FaithfullyFlat A B]
    [Algebra.FinitePresentation A B] :
    ∃ (A₀ B₀ : Type (max u v)) (_ : CommRing A₀) (_ : CommRing B₀) (_ : Algebra R A₀)
      (_ : Algebra A₀ B₀) (_ : Algebra A₀ A) (_ : IsScalarTower R A₀ A) (_ : Algebra B₀ B)
      (_ : Algebra A₀ B) (_ : IsScalarTower A₀ A B) (_ : IsScalarTower A₀ B₀ B),
      Algebra.FinitePresentation R A₀ ∧ Module.FaithfullyFlat A₀ B₀ ∧
        Algebra.FinitePresentation A₀ B₀ ∧ Algebra.IsPushout A₀ A B₀ B := by
  obtain ⟨A', B', _, _, _, _, _, _, _, _, hA', hff, hfp, hpush⟩ :=
    Algebra.exists_faithfullyFlat_finitePresentation_model_int (A := A) (B := B)
  let A₀ := R ⊗[ℤ] A'
  let B₀ := A₀ ⊗[A'] B'
  let φ : A₀ →ₐ[ℤ] A :=
    Algebra.TensorProduct.productMap (algebraMap R A).toIntAlgHom (algebraMap A' A).toIntAlgHom
  let _ : Algebra A₀ A := φ.toRingHom.toAlgebra
  have : @IsScalarTower R A₀ A Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
      .of_algebraMap_eq fun r => by
    show algebraMap R A r = φ (r ⊗ₜ[ℤ] 1)
    rw [Algebra.TensorProduct.productMap_apply_tmul]
    simp
  have : IsScalarTower A' A₀ A := .of_algebraMap_eq fun a => by
    show algebraMap A' A a = φ (1 ⊗ₜ[ℤ] a)
    rw [Algebra.TensorProduct.productMap_apply_tmul]
    simp
  let _ : Algebra A₀ B := ((algebraMap A B).comp (algebraMap A₀ A)).toAlgebra
  have : IsScalarTower A₀ A B := .of_algebraMap_eq fun _ => rfl
  have : IsScalarTower A' A₀ B := .of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply A' A B, IsScalarTower.algebraMap_apply A' A₀ A,
      ← IsScalarTower.algebraMap_apply A₀ A B]
  let ψ : B₀ →ₐ[A'] B :=
    Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom A' A₀ B)
      (IsScalarTower.toAlgHom A' B' B)
  let _ : Algebra B₀ B := ψ.toRingHom.toAlgebra
  have : @IsScalarTower A₀ B₀ B Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
      .of_algebraMap_eq fun x => by
    show algebraMap A₀ B x = ψ (x ⊗ₜ[A'] 1)
    rw [Algebra.TensorProduct.productMap_apply_tmul]
    simp
  have : IsScalarTower A' B₀ B := .to₁₃₄ A' A₀ B₀ B
  have : @IsScalarTower B' B₀ B Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
      .of_algebraMap_eq fun b => by
    show algebraMap B' B b = ψ (1 ⊗ₜ[A'] b)
    rw [Algebra.TensorProduct.productMap_apply_tmul]
    simp
  refine ⟨A₀, B₀, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, ?_⟩
  exact (Algebra.IsPushout.comp_iff A' A₀ B' (T := A) (S' := B₀) (T' := B)).mp hpush
