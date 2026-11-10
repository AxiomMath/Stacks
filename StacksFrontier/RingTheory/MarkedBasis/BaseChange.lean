module

public import StacksFrontier.RingTheory.MarkedBasis.Basic
public import StacksFrontier.RingTheory.Module.LocallyFree.SheafBridge
public import Mathlib.RingTheory.Support
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.LocalProperties.Exactness
public import Mathlib.RingTheory.LocalProperties.Projective
public import Mathlib.RingTheory.Localization.Module

/-!
# Marked bases under base change

Let `R` be a commutative ring, `A` an `R`-algebra, `W : Fin d → A` and `J` an ideal of
`C ⊗[R] A` for an `R`-algebra `C`. This file studies how the property "the images of the
`1 ⊗ W l` form a `C`-basis of `(C ⊗[R] A) ⧸ J`" behaves under base change `C → C'`, which is the
algebra behind the openness of the charts `F_W` in the proof of [Stacks, Tag 0B99].

## Main results

* `Stacks.MarkedBasis.bijective_markedMap_map`: a marked basis stays a marked basis after any base
  change.
* `Stacks.MarkedBasis.exists_smul_mem_range_of_surjective`: (Nakayama) if the marked elements span
  the fibre over a field point `C → K` and `(C ⊗[R] A) ⧸ J` is a finite `C`-module, then some
  `f ∈ C` not vanishing at that point multiplies `(C ⊗[R] A) ⧸ J` into their span.
* `Stacks.MarkedBasis.smul_mem_range_markedMap_map`: such multipliers survive base change.
* `Stacks.MarkedBasis.surjective_markedMap_of_forall_isPrime`: the marked elements span as soon
  as there are such multipliers outside every prime.
* `Module.bijective_of_surjective_of_isFiniteLocallyFreeOfRank`: a surjection from `C^d` onto a
  finite locally free module of rank `d` is an isomorphism.

## References

* [Stacks Project, Tag 0B99](https://stacks.math.columbia.edu/tag/0B99)
* [Stacks Project, Tag 00O0](https://stacks.math.columbia.edu/tag/00O0)
-/

@[expose] public noncomputable section

open TensorProduct

universe u

/-- **A surjection from `C^d` onto a finite locally free module of rank `d` is bijective.** -/
theorem Module.bijective_of_surjective_of_isFiniteLocallyFreeOfRank {C M : Type u} [CommRing C]
    [AddCommGroup M] [Module C M] {d : ℕ} (h : Module.IsFiniteLocallyFreeOfRank C M d)
    (φ : (Fin d → C) →ₗ[C] M) (hφ : Function.Surjective φ) : Function.Bijective φ := by
  obtain ⟨ι, f, hspan, hb⟩ := h
  refine bijective_of_localized_span (Set.range f) hspan φ ?_
  rintro ⟨_, i, rfl⟩
  let S := Submonoid.powers (f i)
  have hs : Function.Surjective (LocalizedModule.map S φ) := LocalizedModule.map_surjective S φ hφ
  rcases subsingleton_or_nontrivial (Localization S) with hS | hS
  · have : Subsingleton (LocalizedModule S (Fin d → C)) := Module.subsingleton (Localization S) _
    exact ⟨Function.injective_of_subsingleton _, hs⟩
  have : Nontrivial C := (algebraMap C (Localization S)).domain_nontrivial
  have : Module.Finite (Localization S) (LocalizedModule S M) := Module.Finite.of_basis (hb i).some
  have : Module.Free (Localization S) (LocalizedModule S M) := Module.Free.of_basis (hb i).some
  have : Module.Free (Localization S) (LocalizedModule S (Fin d → C)) :=
    Module.free_of_isLocalizedModule S (LocalizedModule.mkLinearMap S (Fin d → C))
  refine OrzechProperty.bijective_of_surjective_of_finrank_le _ hs ?_
  rw [Module.finrank_of_isLocalizedModule_of_free (Localization S) S
    (LocalizedModule.mkLinearMap S (Fin d → C)), Module.finrank_fin_fun,
    Module.finrank_eq_card_basis (hb i).some, Fintype.card_fin]

namespace Stacks.MarkedBasis

variable {R : Type u} {A : Type u} [CommRing R] [CommRing A] [Algebra R A] {d : ℕ} (W : Fin d → A)

section BaseChange

/-- The marked map sends the standard basis vector `e_l` to the class of `1 ⊗ W l`. -/
theorem markedMap_single {C : Type u} [CommRing C] [Algebra R C] (J : Ideal (C ⊗[R] A))
    (l : Fin d) :
    markedMap W C J (Pi.single l 1) = Ideal.Quotient.mk J ((1 : C) ⊗ₜ W l) := by
  simp only [markedMap, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_eq_single l (fun b _ hb ↦ by simp [hb]) (by simp)]
  simp

/-- The classes of the elements `1 ⊗ a` span `(C ⊗[R] A) ⧸ J` over `C`. -/
theorem span_range_mk_one_tmul {C : Type u} [CommRing C] [Algebra R C] (J : Ideal (C ⊗[R] A)) :
    Submodule.span C (Set.range fun a : A ↦ Ideal.Quotient.mk J ((1 : C) ⊗ₜ[R] a)) = ⊤ := by
  refine Submodule.eq_top_iff'.mpr fun z ↦ ?_
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
  induction y using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add]; exact add_mem hx hy
  | tmul c a =>
    rw [mk_tmul_eq_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

variable {C C' : Type u} [CommRing C] [Algebra R C] [CommRing C'] [Algebra R C']

/-- **A marked basis stays a marked basis after any base change.** If the images of the
`1 ⊗ W l` form a `C`-basis of `(C ⊗[R] A) ⧸ J`, their images form a `C'`-basis of the quotient of
`C' ⊗[R] A` by the extended ideal, for every `R`-algebra map `C → C'`. -/
theorem bijective_markedMap_map {J : Ideal (C ⊗[R] A)} (hJ : Function.Bijective (markedMap W C J))
    (φ : C →ₐ[R] C') :
    Function.Bijective (markedMap W C' (J.map (Algebra.TensorProduct.map φ (AlgHom.id R A)))) := by
  have hJD : chartIdeal C (chartDataOfIdeal J hJ) = J :=
    congrArg Subtype.val ((chartDataEquiv (W := W) C).apply_symm_apply ⟨J, hJ⟩)
  rw [← hJD, map_chartIdeal]
  exact bijective_markedMap_chartIdeal _

/-- The map `(C ⊗[R] A) ⧸ J → (C' ⊗[R] A) ⧸ J'` induced by an `R`-algebra map `C → C'`. -/
def quotMap (φ : C →ₐ[R] C') (J : Ideal (C ⊗[R] A)) :
    (C ⊗[R] A) ⧸ J →ₐ[R] (C' ⊗[R] A) ⧸ J.map (Algebra.TensorProduct.map φ (AlgHom.id R A)) :=
  Ideal.quotientMapₐ _ (Algebra.TensorProduct.map φ (AlgHom.id R A)) Ideal.le_comap_map

/-- `quotMap` on classes. -/
theorem quotMap_mk (φ : C →ₐ[R] C') (J : Ideal (C ⊗[R] A)) (y : C ⊗[R] A) :
    quotMap φ J (Ideal.Quotient.mk J y) =
      Ideal.Quotient.mk _ (Algebra.TensorProduct.map φ (AlgHom.id R A) y) :=
  rfl

/-- `quotMap` is semilinear along `φ`. -/
theorem quotMap_smul (φ : C →ₐ[R] C') (J : Ideal (C ⊗[R] A)) (c : C) (q : (C ⊗[R] A) ⧸ J) :
    quotMap φ J (c • q) = φ c • quotMap φ J q := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [Algebra.smul_def, Algebra.smul_def, map_mul]
  congr 1

/-- `quotMap` is compatible with the marked maps. -/
theorem quotMap_markedMap (φ : C →ₐ[R] C') (J : Ideal (C ⊗[R] A)) (c : Fin d → C) :
    quotMap φ J (markedMap W C J c) =
      markedMap W C' (J.map (Algebra.TensorProduct.map φ (AlgHom.id R A))) (fun l ↦ φ (c l)) := by
  simp only [markedMap, LinearMap.coe_mk, AddHom.coe_mk, map_sum, quotMap_mk,
    Algebra.TensorProduct.map_tmul, AlgHom.id_apply]

/-- The classes of the elements `c' ⊗ a` span the base-changed quotient over `C'`, being
`c'`-multiples of images of classes from `C ⊗[R] A`. -/
theorem mem_span_range_quotMap (φ : C →ₐ[R] C') (J : Ideal (C ⊗[R] A))
    (z : (C' ⊗[R] A) ⧸ J.map (Algebra.TensorProduct.map φ (AlgHom.id R A))) :
    z ∈ Submodule.span C' (Set.range (quotMap φ J)) := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
  induction y using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add]; exact add_mem hx hy
  | tmul c' a =>
    have : Ideal.Quotient.mk (J.map (Algebra.TensorProduct.map φ (AlgHom.id R A))) (c' ⊗ₜ[R] a) =
        c' • quotMap φ J (Ideal.Quotient.mk J ((1 : C) ⊗ₜ a)) := by
      rw [quotMap_mk, Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply,
        Algebra.smul_def]
      change _ = Ideal.Quotient.mk _ (c' ⊗ₜ 1) * Ideal.Quotient.mk _ _
      rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

/-- **Multipliers into the span of the marked elements survive base change.** If `f ∈ C`
multiplies `(C ⊗[R] A) ⧸ J` into the span of the marked elements, then its image in `C'`
multiplies the base-changed quotient into the span of the marked elements. -/
theorem smul_mem_range_markedMap_map {J : Ideal (C ⊗[R] A)} {f : C}
    (hf : ∀ q : (C ⊗[R] A) ⧸ J, f • q ∈ LinearMap.range (markedMap W C J)) (φ : C →ₐ[R] C')
    (z : (C' ⊗[R] A) ⧸ J.map (Algebra.TensorProduct.map φ (AlgHom.id R A))) :
    φ f • z ∈
      LinearMap.range (markedMap W C' (J.map (Algebra.TensorProduct.map φ (AlgHom.id R A)))) := by
  induction mem_span_range_quotMap φ J z using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨q, rfl⟩ := hx
    obtain ⟨c, hc⟩ := hf q
    rw [← quotMap_smul, ← hc, quotMap_markedMap]
    exact ⟨_, rfl⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul c x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx

end BaseChange

section Nakayama

variable {C : Type u} [CommRing C] [Algebra R C] {K : Type u} [Field K] [Algebra C K]
  [Algebra R K] [IsScalarTower R C K]

/-- The `R`-algebra map `K ⊗[R] A → K ⊗[C] ((C ⊗[R] A) ⧸ J)`, `k ⊗ a ↦ k ⊗ [1 ⊗ a]`. -/
def fibreLift (J : Ideal (C ⊗[R] A)) : K ⊗[R] A →ₐ[R] K ⊗[C] ((C ⊗[R] A) ⧸ J) :=
  Algebra.TensorProduct.lift (Algebra.TensorProduct.includeLeft (R := C) (S := R))
    (((Algebra.TensorProduct.includeRight (R := C) (A := K)).restrictScalars R).comp
      ((Ideal.Quotient.mkₐ R J).comp Algebra.TensorProduct.includeRight)) fun _ _ ↦ .all _ _

/-- `fibreLift` on the image of `C ⊗[R] A`. -/
theorem fibreLift_map (J : Ideal (C ⊗[R] A)) (y : C ⊗[R] A) :
    fibreLift (K := K) J
        (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R C K) (AlgHom.id R A) y) =
      (1 : K) ⊗ₜ Ideal.Quotient.mk J y := by
  induction y using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, tmul_add]
  | tmul c a =>
    rw [Algebra.TensorProduct.map_tmul, fibreLift, Algebra.TensorProduct.lift_tmul]
    simp only [IsScalarTower.coe_toAlgHom', AlgHom.coe_comp, AlgHom.coe_restrictScalars',
      Function.comp_apply, Algebra.TensorProduct.includeLeft_apply,
      Algebra.TensorProduct.includeRight_apply, Ideal.Quotient.mkₐ_eq_mk, AlgHom.id_apply,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [mk_tmul_eq_smul J c a, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]

/-- The ring map `(K ⊗[R] A) ⧸ J_K → K ⊗[C] ((C ⊗[R] A) ⧸ J)` comparing the fibre of the quotient
with the tensor product. -/
def fibreComparison (J : Ideal (C ⊗[R] A)) :
    (K ⊗[R] A) ⧸
        J.map (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R C K) (AlgHom.id R A)) →+*
      K ⊗[C] ((C ⊗[R] A) ⧸ J) :=
  Ideal.Quotient.lift _ (fibreLift J).toRingHom <| by
    intro x hx
    refine (Ideal.map_le_iff_le_comap.mpr ?_ : _ ≤ RingHom.ker (fibreLift (K := K) J).toRingHom) hx
    intro y hy
    change fibreLift J _ = 0
    rw [fibreLift_map, Ideal.Quotient.eq_zero_iff_mem.mpr hy, tmul_zero]

/-- `fibreComparison` on the images of classes from `(C ⊗[R] A) ⧸ J`. -/
theorem fibreComparison_quotMap (J : Ideal (C ⊗[R] A)) (q : (C ⊗[R] A) ⧸ J) :
    fibreComparison (K := K) J (quotMap (IsScalarTower.toAlgHom R C K) J q) = (1 : K) ⊗ₜ q := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective q
  exact fibreLift_map J y

/-- `fibreComparison` is `K`-linear. -/
theorem fibreComparison_smul (J : Ideal (C ⊗[R] A)) (k : K)
    (z : (K ⊗[R] A) ⧸
      J.map (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R C K) (AlgHom.id R A))) :
    fibreComparison J (k • z) = k • fibreComparison J z := by
  rw [Algebra.smul_def, map_mul, Algebra.smul_def]
  congr 1
  change fibreLift J (k ⊗ₜ 1) = _
  rw [fibreLift, Algebra.TensorProduct.lift_tmul]
  simp [← Algebra.TensorProduct.one_def]

/-- `f` annihilates `M ⧸ N` iff it multiplies `M` into `N`. -/
private theorem mem_annihilator_quotient_iff {M : Type*} [AddCommGroup M] [Module C M]
    (N : Submodule C M) (f : C) :
    f ∈ Module.annihilator C (M ⧸ N) ↔ ∀ q : M, f • q ∈ N := by
  refine ⟨fun hf q ↦ ?_, fun hf ↦ Module.mem_annihilator.mpr fun m ↦ ?_⟩
  · have := Module.mem_annihilator.mp hf (N.mkQ q)
    rwa [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
  · obtain ⟨q, rfl⟩ := N.mkQ_surjective m
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hf q

/-- **Nakayama's lemma for marked elements.** Let `C → K` be a field point and suppose that
`(C ⊗[R] A) ⧸ J` is a finite `C`-module. If the marked elements span the fibre
`(K ⊗[R] A) ⧸ J_K` over `K`, then some `f ∈ C` not vanishing in `K` multiplies `(C ⊗[R] A) ⧸ J`
into the `C`-span of the marked elements. -/
theorem exists_smul_mem_range_of_surjective {J : Ideal (C ⊗[R] A)}
    [Module.Finite C ((C ⊗[R] A) ⧸ J)]
    (hK : Function.Surjective (markedMap W K
      (J.map (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R C K) (AlgHom.id R A))))) :
    ∃ f : C, algebraMap C K f ≠ 0 ∧
      ∀ q : (C ⊗[R] A) ⧸ J, f • q ∈ LinearMap.range (markedMap W C J) := by
  set N := LinearMap.range (markedMap W C J)
  by_contra! H
  let p : Ideal C := RingHom.ker (algebraMap C K)
  have hp : p.IsPrime := RingHom.ker_isPrime _
  have hann : Module.annihilator C (((C ⊗[R] A) ⧸ J) ⧸ N) ≤ p := by
    intro f hf
    by_contra hne
    obtain ⟨q, hq⟩ := H f hne
    exact hq ((mem_annihilator_quotient_iff N f).mp hf q)
  have hsupp : (⟨p, hp⟩ : PrimeSpectrum C) ∈ Module.support C (((C ⊗[R] A) ⧸ J) ⧸ N) := by
    rw [Module.support_eq_zeroLocus, PrimeSpectrum.mem_zeroLocus]
    exact hann
  rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct] at hsupp
  let : Algebra p.ResidueField K := (Ideal.ResidueField.lift p (algebraMap C K) le_rfl
    (fun x hx ↦ (isUnit_iff_ne_zero.mpr hx : IsUnit (algebraMap C K x)))).toAlgebra
  have : IsScalarTower C p.ResidueField K := IsScalarTower.of_algebraMap_eq fun x ↦
    (Ideal.ResidueField.lift_algebraMap p (algebraMap C K) _ _ x).symm
  have hnt : Nontrivial (K ⊗[p.ResidueField] (p.ResidueField ⊗[C] (((C ⊗[R] A) ⧸ J) ⧸ N))) :=
    (Module.FaithfullyFlat.nontrivial_tensorProduct_iff_right _ _).mpr hsupp
  have hnt' : Nontrivial (K ⊗[C] (((C ⊗[R] A) ⧸ J) ⧸ N)) :=
    (AlgebraTensorModule.cancelBaseChange C p.ResidueField K K _).nontrivial_congr.mp hnt
  have hzero : ∀ x : K ⊗[C] ((C ⊗[R] A) ⧸ J), N.mkQ.baseChange K x = 0 := by
    have h1 : ∀ q : (C ⊗[R] A) ⧸ J, N.mkQ.baseChange K ((1 : K) ⊗ₜ q) = 0 := by
      intro q
      obtain ⟨c, hc⟩ := hK (quotMap (IsScalarTower.toAlgHom R C K) J q)
      have h2 := congrArg (fibreComparison (K := K) J) hc
      rw [fibreComparison_quotMap] at h2
      rw [← h2]
      simp only [markedMap, LinearMap.coe_mk, AddHom.coe_mk, map_sum]
      refine Finset.sum_eq_zero fun l _ ↦ ?_
      rw [mk_tmul_eq_smul, fibreComparison_smul, map_smul]
      have h3 : Ideal.Quotient.mk _ ((1 : K) ⊗ₜ[R] W l) =
          quotMap (IsScalarTower.toAlgHom R C K) J (Ideal.Quotient.mk J ((1 : C) ⊗ₜ W l)) := by
        rw [quotMap_mk, Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
      rw [h3, fibreComparison_quotMap, LinearMap.baseChange_tmul, Submodule.mkQ_apply,
        (Submodule.Quotient.mk_eq_zero N).mpr ⟨Pi.single l 1, markedMap_single W J l⟩, tmul_zero,
        smul_zero]
    intro x
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => rw [map_add, hx, hy, add_zero]
    | tmul k q =>
      have : k ⊗ₜ[C] q = k • ((1 : K) ⊗ₜ q) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [this, map_smul, h1, smul_zero]
  obtain ⟨x, y, hxy⟩ := hnt'
  obtain ⟨x, rfl⟩ := LinearMap.lTensor_surjective K N.mkQ_surjective x
  obtain ⟨y, rfl⟩ := LinearMap.lTensor_surjective K N.mkQ_surjective y
  rw [← LinearMap.baseChange_eq_lTensor] at hxy
  exact hxy ((hzero x).trans (hzero y).symm)

/-- The marked elements span as soon as, at every prime, some element outside it multiplies the
quotient into their span. -/
theorem surjective_markedMap_of_forall_isPrime {J : Ideal (C ⊗[R] A)}
    (h : ∀ p : Ideal C, p.IsPrime → ∃ f ∉ p,
      ∀ q : (C ⊗[R] A) ⧸ J, f • q ∈ LinearMap.range (markedMap W C J)) :
    Function.Surjective (markedMap W C J) := by
  set N := LinearMap.range (markedMap W C J)
  have htop : Module.annihilator C (((C ⊗[R] A) ⧸ J) ⧸ N) = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨f, hf, hfN⟩ := h m hm.isPrime
    exact hf (hle ((mem_annihilator_quotient_iff N f).mpr hfN))
  intro q
  have := (mem_annihilator_quotient_iff N 1).mp (htop ▸ Submodule.mem_top) q
  rwa [one_smul] at this

end Nakayama

end Stacks.MarkedBasis

end
