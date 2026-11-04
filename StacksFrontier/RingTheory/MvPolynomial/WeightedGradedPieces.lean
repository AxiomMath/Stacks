module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Data.Int.Star
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

/-!
# Weighted-graded pieces of polynomial rings

For `S = R[x_1, …, x_n]` graded by positive integer weights `w`, each weighted-homogeneous
piece `S_d` is a finite free `R`-module. For a finite graded `S`-module `M` (graded by
`𝓜 : ℤ → Submodule R M`), this file shows that `M` has a finite homogeneous generating family
and that each graded piece `𝓜 d` is a finite `R`-module, flat when `M` is flat over `R`, and
free when moreover `R` is local.
-/

open MvPolynomial

/-- For positive integer weights `w`, the natural-number weight of `a` with respect to
`fun i => (w i).toNat`, cast to `ℤ`, equals `Finsupp.weight w a`. -/
theorem Finsupp.cast_weight_toNat {σ : Type*} (w : σ → ℤ) (hw : ∀ i, 0 < w i) (a : σ →₀ ℕ) :
    ((Finsupp.weight (fun i => (w i).toNat) a : ℕ) : ℤ) = Finsupp.weight w a := by
  simp only [Finsupp.weight_apply, Finsupp.sum, Nat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Int.toNat_of_nonneg (hw i).le]

/-- For positive integer weights `w` on a finite type, the set of exponents `a : σ →₀ ℕ` with
`Finsupp.weight w a = d` is finite. -/
theorem Finsupp.finite_of_int_weight_eq {σ : Type*} [Finite σ] (w : σ → ℤ) (hw : ∀ i, 0 < w i)
    (d : ℤ) : {a : σ →₀ ℕ | Finsupp.weight w a = d}.Finite := by
  rcases le_or_gt 0 d with hd | hd
  · refine Set.Finite.subset (Finsupp.finite_of_nat_weight_eq (fun i => (w i).toNat)
      (fun i => by have := hw i; omega) d.toNat) fun a ha => ?_
    simp only [Set.mem_ofPred_eq] at ha ⊢
    have hc := Finsupp.cast_weight_toNat w hw a
    rw [ha] at hc
    omega
  · refine Set.Finite.subset Set.finite_empty fun a ha => ?_
    simp only [Set.mem_ofPred_eq] at ha
    exfalso
    have hnn : (0 : ℤ) ≤ Finsupp.weight w a := by
      rw [← Finsupp.cast_weight_toNat w hw a]
      positivity
    omega

/-- The weighted-homogeneous piece of degree `d` of `MvPolynomial σ R` is `R`-linearly isomorphic
to the free `R`-module on the exponents of weight `d`. -/
noncomputable def MvPolynomial.weightedHomogeneousSubmoduleEquivFinsupp
    (R : Type*) [CommSemiring R] {σ M : Type*} [AddCommMonoid M] (w : σ → M) (d : M) :
    weightedHomogeneousSubmodule R w d ≃ₗ[R]
      (↑{a : σ →₀ ℕ | Finsupp.weight w a = d} : Set (σ →₀ ℕ)) →₀ R :=
  (LinearEquiv.ofEq _ _ (weightedHomogeneousSubmodule_eq_finsupp_supported R w d)).trans
    (AddMonoidAlgebra.supportedEquivFinsupp (R := R) (S := R) _)

/-- Each weighted-homogeneous piece of degree `d` of `MvPolynomial σ R` is a free `R`-module. -/
lemma MvPolynomial.weightedHomogeneousSubmodule_free
    (R : Type*) [CommSemiring R] {σ M : Type*} [AddCommMonoid M] (w : σ → M) (d : M) :
    Module.Free R (weightedHomogeneousSubmodule R w d) :=
  have : Module.Free R ((↑{a : σ →₀ ℕ | Finsupp.weight w a = d} : Set (σ →₀ ℕ)) →₀ R) :=
    Module.Free.finsupp _ _ _
  Module.Free.of_equiv (weightedHomogeneousSubmoduleEquivFinsupp R w d).symm

/-- For positive integer weights `w` on a finite type, each weighted-homogeneous piece of
degree `d` of `MvPolynomial σ R` is a finite `R`-module. -/
lemma MvPolynomial.weightedHomogeneousSubmodule_finite_of_pos
    (R : Type*) [CommSemiring R] {σ : Type*} [Finite σ] (w : σ → ℤ) (hw : ∀ i, 0 < w i) (d : ℤ) :
    Module.Finite R (weightedHomogeneousSubmodule R w d) :=
  have : Finite {a : σ →₀ ℕ | Finsupp.weight w a = d} := Finsupp.finite_of_int_weight_eq w hw d
  have : Module.Finite R ((↑{a : σ →₀ ℕ | Finsupp.weight w a = d} : Set (σ →₀ ℕ)) →₀ R) :=
    Module.Finite.finsupp
  Module.Finite.equiv (weightedHomogeneousSubmoduleEquivFinsupp R w d).symm

/-- If `M` is a flat `R`-module with a decomposition `𝓜 : ℤ → Submodule R M`, then each graded
piece `𝓜 d` is a flat `R`-module. -/
@[ega "0 6.1.2" "special case", ega "IV 11.3.4" "(iii), special case"]
lemma gradedPiece_flat_of_flat
    (R : Type*) [CommRing R]
    (M : Type*) [AddCommGroup M] [Module R M]
    (𝓜 : ℤ → Submodule R M) [DirectSum.Decomposition 𝓜] [Module.Flat R M] (d : ℤ) :
    Module.Flat R (𝓜 d) :=
  have : Module.Flat R (DirectSum ℤ fun i => ↥(𝓜 i)) :=
    Module.Flat.of_linearEquiv (DirectSum.decomposeLinearEquiv 𝓜).symm
  Module.Flat.directSum_iff.mp this d

/-- Let `M` be a module over `S` that is finite over `S`, with a decomposition
`𝓜 : ℤ → Submodule R M`. Then `M` is spanned over `S` by a finite family `m : Fin r → M` of
homogeneous elements, with `m i ∈ 𝓜 (deg i)`. -/
@[sga "6 VI 1.6" "partial"]
lemma exists_homogeneous_generators
    (R : Type*) [CommRing R] (S : Type*) [Ring S]
    (M : Type*) [AddCommGroup M] [Module S M] [Module R M]
    (𝓜 : ℤ → Submodule R M)
    [DirectSum.Decomposition 𝓜]
    [Module.Finite S M] :
    ∃ (r : ℕ) (m : Fin r → M) (deg : Fin r → ℤ),
      (∀ i, m i ∈ 𝓜 (deg i)) ∧ Submodule.span S (Set.range m) = ⊤ := by
  classical
  obtain ⟨k, s, hs⟩ := Module.Finite.exists_fin (R := S) (M := M)
  let I := Σ j : Fin k, (DirectSum.decompose 𝓜 (s j)).support
  let e := Fintype.equivFin I
  refine ⟨Fintype.card I, fun i => (DirectSum.decompose 𝓜 (s (e.symm i).1) (e.symm i).2 : M),
    fun i => ((e.symm i).2 : ℤ), fun i => SetLike.coe_mem _, ?_⟩
  rw [eq_top_iff, ← hs, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  rw [SetLike.mem_coe, ← DirectSum.sum_support_decompose 𝓜 (s j)]
  exact Submodule.sum_mem _ fun d hd => Submodule.subset_span
    ⟨e ⟨j, ⟨d, hd⟩⟩, by beta_reduce; rw [Equiv.symm_apply_apply]⟩

/-- A homogeneous polynomial of degree `a` sends `𝓜 e` into `𝓜 (a + e)`. -/
private theorem smul_mem_of_mem_weightedHomogeneousSubmodule
    {R : Type*} [CommRing R] {n : ℕ} {w : Fin n → ℤ}
    {M : Type*} [AddCommGroup M] [Module (MvPolynomial (Fin n) R) M] [Module R M]
    {𝓜 : ℤ → Submodule R M} [SetLike.GradedSMul (weightedHomogeneousSubmodule R w) 𝓜]
    {a e : ℤ} {p : MvPolynomial (Fin n) R} (hp : p ∈ weightedHomogeneousSubmodule R w a)
    {x : M} (hx : x ∈ 𝓜 e) : p • x ∈ 𝓜 (a + e) := by
  simpa using SetLike.GradedSMul.smul_mem
    (A := weightedHomogeneousSubmodule R w) (B := 𝓜) hp hx

/-- The degree `d` component of a finite sum is the sum of the degree `d` components. -/
private theorem coe_decompose_sum_apply
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (𝓜 : ℤ → Submodule R M) [DirectSum.Decomposition 𝓜] {ι : Type*} (s : Finset ι)
    (f : ι → M) (d : ℤ) :
    (DirectSum.decompose 𝓜 (∑ i ∈ s, f i) d : M) = ∑ i ∈ s, (DirectSum.decompose 𝓜 (f i) d : M) :=
  by simp [DirectSum.decompose_sum]

/-- If `M` is a module over `MvPolynomial (Fin n) R` graded by `𝓜 : ℤ → Submodule R M`
compatibly with the weighted grading by `w`, and `x` is homogeneous of degree `e`, then the
degree `d` component of `p • x` is the degree `d - e` component of `p` acting on `x`. -/
lemma gradedPiece_decompose_smul_of_mem
    (R : Type*) [CommRing R]
    {n : ℕ} (w : Fin n → ℤ)
    (M : Type*) [AddCommGroup M] [Module (MvPolynomial (Fin n) R) M] [Module R M]
    (𝓜 : ℤ → Submodule R M)
    [SetLike.GradedSMul (weightedHomogeneousSubmodule R w) 𝓜]
    [DirectSum.Decomposition 𝓜]
    [DirectSum.Decomposition (weightedHomogeneousSubmodule R w)]
    {e : ℤ} {x : M} (hx : x ∈ 𝓜 e) (p : MvPolynomial (Fin n) R) (d : ℤ) :
    (DirectSum.decompose 𝓜 (p • x) d : M)
      = (DirectSum.decompose (weightedHomogeneousSubmodule R w) p (d - e) :
          MvPolynomial (Fin n) R) • x := by
  classical
  have hsmul : p • x = ∑ f ∈ (DirectSum.decompose (weightedHomogeneousSubmodule R w) p).support,
      (DirectSum.decompose (weightedHomogeneousSubmodule R w) p f : MvPolynomial (Fin n) R)
        • x := by
    rw [← Finset.sum_smul, DirectSum.sum_support_decompose]
  have hmem : ∀ f : ℤ, (DirectSum.decompose (weightedHomogeneousSubmodule R w) p f :
      MvPolynomial (Fin n) R) • x ∈ 𝓜 (f + e) := fun f =>
    smul_mem_of_mem_weightedHomogeneousSubmodule (SetLike.coe_mem _) hx
  rw [hsmul, coe_decompose_sum_apply, Finset.sum_eq_single (d - e)]
  · refine DirectSum.decompose_of_mem_same 𝓜 ?_
    have := hmem (d - e)
    rwa [sub_add_cancel] at this
  · intro f _ hfne
    exact DirectSum.decompose_of_mem_ne 𝓜 (hmem f) (by omega)
  · intro hns
    simp [DFinsupp.notMem_support_iff.mp hns]

/-- Let `M` be a finite module over `MvPolynomial (Fin n) R`, graded by `𝓜 : ℤ → Submodule R M`
compatibly with the grading of `MvPolynomial (Fin n) R` by positive integer weights `w`. Then
each graded piece `𝓜 d` is a finite `R`-module. -/
lemma gradedPiece_finite_of_finite
    (R : Type*) [CommRing R]
    {n : ℕ} (w : Fin n → ℤ) (hw : ∀ i, 0 < w i)
    (M : Type*) [AddCommGroup M] [Module (MvPolynomial (Fin n) R) M]
    [Module R M] [IsScalarTower R (MvPolynomial (Fin n) R) M]
    (𝓜 : ℤ → Submodule R M)
    [SetLike.GradedSMul (weightedHomogeneousSubmodule R w) 𝓜]
    [DirectSum.Decomposition 𝓜]
    [Module.Finite (MvPolynomial (Fin n) R) M]
    (d : ℤ) :
    Module.Finite R (𝓜 d) := by
  classical
  let instS : DirectSum.Decomposition (weightedHomogeneousSubmodule R w) :=
    (weightedGradedAlgebra R w).toDecomposition
  obtain ⟨r, m, deg, hm, hspan⟩ := exists_homogeneous_generators R (MvPolynomial (Fin n) R) M 𝓜
  let F : (Π i : Fin r, weightedHomogeneousSubmodule R w (d - deg i)) →ₗ[R] M :=
    ∑ i : Fin r,
      (LinearMap.smulRight (R := R) (S := MvPolynomial (Fin n) R) (LinearMap.id) (m i)).comp
        ((weightedHomogeneousSubmodule R w (d - deg i)).subtype.comp (LinearMap.proj i))
  have hF : ∀ s, F s = ∑ i : Fin r, (s i : MvPolynomial (Fin n) R) • m i := by
    intro s
    simp only [F, LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply,
      LinearMap.proj_apply, Submodule.subtype_apply, LinearMap.smulRight_apply, LinearMap.id_apply]
  have hFmem : ∀ s, F s ∈ 𝓜 d := by
    intro s
    rw [hF]
    refine Submodule.sum_mem _ fun i _ => ?_
    have := smul_mem_of_mem_weightedHomogeneousSubmodule (SetLike.coe_mem (s i)) (hm i)
    rwa [sub_add_cancel] at this
  let F' : (Π i : Fin r, weightedHomogeneousSubmodule R w (d - deg i)) →ₗ[R] (𝓜 d) :=
    LinearMap.codRestrict (𝓜 d) F hFmem
  have hsurj : Function.Surjective F' := by
    rintro ⟨x, hx⟩
    have hxspan : x ∈ Submodule.span (MvPolynomial (Fin n) R) (Set.range m) := by
      simp [hspan]
    rw [Submodule.mem_span_range_iff_exists_fun] at hxspan
    obtain ⟨c, hc⟩ := hxspan
    refine ⟨fun i => ⟨(DirectSum.decompose (weightedHomogeneousSubmodule R w) (c i) (d - deg i) :
        MvPolynomial (Fin n) R), SetLike.coe_mem _⟩, Subtype.ext ?_⟩
    rw [LinearMap.codRestrict_apply, hF]
    show (∑ i : Fin r, (DirectSum.decompose (weightedHomogeneousSubmodule R w) (c i) (d - deg i) :
        MvPolynomial (Fin n) R) • m i) = x
    rw [← DirectSum.decompose_of_mem_same 𝓜 hx, ← hc, coe_decompose_sum_apply]
    exact Finset.sum_congr rfl fun i _ =>
      (gradedPiece_decompose_smul_of_mem R w M 𝓜 (hm i) (c i) d).symm
  have : ∀ i : Fin r, Module.Finite R (weightedHomogeneousSubmodule R w (d - deg i)) :=
    fun i => weightedHomogeneousSubmodule_finite_of_pos R w hw (d - deg i)
  have : Module.Finite R (Π i : Fin r, weightedHomogeneousSubmodule R w (d - deg i)) :=
    Module.Finite.pi
  exact Module.Finite.of_surjective F' hsurj

/-- Let `R` be a local ring and `M` a finite module over `MvPolynomial (Fin n) R` that is flat
over `R`, graded by `𝓜 : ℤ → Submodule R M` compatibly with the grading of `MvPolynomial (Fin n) R`
by positive integer weights `w`. Then each graded piece `𝓜 d` is a free `R`-module. -/
@[ega "IV 19.7.4" "special case"]
lemma gradedPiece_free_of_finite
    (R : Type*) [CommRing R] [IsLocalRing R]
    {n : ℕ} (w : Fin n → ℤ) (hw : ∀ i, 0 < w i)
    (M : Type*) [AddCommGroup M] [Module (MvPolynomial (Fin n) R) M]
    [Module R M] [IsScalarTower R (MvPolynomial (Fin n) R) M]
    (𝓜 : ℤ → Submodule R M)
    [SetLike.GradedSMul (weightedHomogeneousSubmodule R w) 𝓜]
    [DirectSum.Decomposition 𝓜]
    [Module.Finite (MvPolynomial (Fin n) R) M]
    [Module.Flat R M]
    (d : ℤ) :
    Module.Free R (𝓜 d) := by
  have : Module.Finite R (𝓜 d) := gradedPiece_finite_of_finite R w hw M 𝓜 d
  have : Module.Flat R (𝓜 d) := gradedPiece_flat_of_flat R M 𝓜 d
  exact Module.free_of_flat_of_isLocalRing
