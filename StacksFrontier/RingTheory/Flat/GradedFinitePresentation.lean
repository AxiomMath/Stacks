module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Algebra.Order.Star.Int
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Smooth.Quotient
public import Mathlib.RingTheory.TotallySplit
public import StacksFrontier.RingTheory.MvPolynomial.WeightedGradedPieces
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finite presentation of graded modules flat over a local ring

Let `R` be a local ring with maximal ideal `𝔪` and let `S = R[x_1, …, x_n]` be graded by
positive weights `w_i = deg(x_i) > 0`, via `MvPolynomial.weightedHomogeneousSubmodule R w`. A
graded `S`-module `M` is encoded by a family `𝓜 : ℤ → Submodule R M` together with
`SetLike.GradedSMul` and `DirectSum.Decomposition 𝓜`. If `M` is finite over `S` and flat over
`R`, then `M` is a finitely presented `S`-module.

## Main definitions

* `shiftPiece`: the degree-`d` piece of `S^r` for the grading shifted by `deg : Fin r → ℤ`.
* `descentProj`: the projection of `S^r` onto `shiftPiece`.

## Main results

* `graded_nakayama_vanish`: a bounded-below graded Nakayama lemma over a local ring.
* `gradedKernel_fg`: the kernel of a homogeneous presentation is finitely generated.
* `finitePresentation_of_finite_flat_of_isLocalRing`: a graded module over `S` that is finite
  over `S` and flat over the local ring `R` is finitely presented.

## References

* [Stacks Project, Tag 053C](https://stacks.math.columbia.edu/tag/053C)
-/

@[expose] public section

open MvPolynomial

/-- Let `J = IS` for a maximal ideal `I` of `R`. For any `m : Fin r → M`, the kernel `K` of
`S^r → M`, `e_i ↦ m_i`, contains finitely many elements `g_j` with `K ≤ span S {g_j} ⊔ J • S^r`. -/
lemma descent_image_mod_jacobson_le
    (R : Type*) [CommRing R]
    (n : ℕ)
    (M : Type*) [AddCommGroup M] [Module (MvPolynomial (Fin n) R) M]
    (I : Ideal R) [I.IsMaximal]
    {r : ℕ} (m : Fin r → M) :
    ∃ (t : ℕ) (g : Fin t → (Fin r → MvPolynomial (Fin n) R)),
      (∀ j, g j ∈ LinearMap.ker (Fintype.linearCombination (MvPolynomial (Fin n) R) m)) ∧
      LinearMap.ker (Fintype.linearCombination (MvPolynomial (Fin n) R) m) ≤
        Submodule.span (MvPolynomial (Fin n) R) (Set.range g)
          ⊔ (Ideal.map (algebraMap R (MvPolynomial (Fin n) R)) I)
              • (⊤ : Submodule (MvPolynomial (Fin n) R) (Fin r → MvPolynomial (Fin n) R)) := by
  classical
  set S := MvPolynomial (Fin n) R
  set P := (Fin r → S)
  set J : Ideal S := Ideal.map (algebraMap R S) I
  set F : P →ₗ[S] M := Fintype.linearCombination S m
  set K : Submodule S P := LinearMap.ker F
  set Q : Submodule S P := J • (⊤ : Submodule S P)
  have hJC : J = Ideal.map (MvPolynomial.C) I := rfl
  let : Field (R ⧸ I) := Ideal.Quotient.field I
  have e : MvPolynomial (Fin n) (R ⧸ I) ≃ₐ[R] (S ⧸ J) := by
    rw [hJC]
    exact MvPolynomial.quotientEquivQuotientMvPolynomial I
  have hnoeth : IsNoetherianRing (S ⧸ J) :=
    isNoetherianRing_of_surjective (MvPolynomial (Fin n) (R ⧸ I)) (S ⧸ J)
      e.toRingEquiv.toRingHom e.toRingEquiv.surjective
  have htor : Module.IsTorsionBySet S (P ⧸ Q) (↑J) := by
    intro q j
    refine Quotient.inductionOn' q fun p => ?_
    change (j : S) • (Submodule.Quotient.mk p : P ⧸ Q) = 0
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_smul j.2 trivial
  let inst1 : Module (S ⧸ J) (P ⧸ Q) := htor.module
  have inst2 : IsScalarTower S (S ⧸ J) (P ⧸ Q) := htor.isScalarTower
  have : Module.Finite (S ⧸ J) (P ⧸ Q) :=
    Module.Finite.of_restrictScalars_finite S (S ⧸ J) (P ⧸ Q)
  have : IsNoetherian (S ⧸ J) (P ⧸ Q) :=
    isNoetherian_of_isNoetherianRing_of_finite (S ⧸ J) (P ⧸ Q)
  have hsurj : Function.Surjective (algebraMap S (S ⧸ J)) := Ideal.Quotient.mk_surjective
  set N : Submodule S (P ⧸ Q) := Submodule.map Q.mkQ K
  obtain ⟨N', hN'⟩ : ∃ N' : Submodule (S ⧸ J) (P ⧸ Q), N'.restrictScalars S = N := by
    refine ⟨{ carrier := N, add_mem' := fun a b => N.add_mem a b, zero_mem' := N.zero_mem,
              smul_mem' := fun c x hx => ?_ }, rfl⟩
    obtain ⟨c0, rfl⟩ := hsurj c
    rw [algebraMap_smul]
    exact N.smul_mem c0 hx
  have hNfg : N.FG := by
    rw [← hN']
    exact Submodule.FG.restrictScalars_of_surjective (IsNoetherian.noetherian N') hsurj
  rw [Submodule.fg_iff_exists_fin_generating_family] at hNfg
  obtain ⟨t, s, hs⟩ := hNfg
  have hsmem : ∀ j, s j ∈ N := fun j => by
    rw [← hs]
    exact Submodule.subset_span ⟨j, rfl⟩
  choose g hgK hgmap using fun j => (Submodule.mem_map.mp (hsmem j))
  refine ⟨t, g, hgK, ?_⟩
  have hker : LinearMap.ker Q.mkQ = Q := Submodule.ker_mkQ Q
  rw [← hker, ← LinearMap.map_le_map_iff Q.mkQ, Submodule.map_span]
  have hrange : (⇑Q.mkQ) '' (Set.range g) = Set.range s := by
    rw [← Set.range_comp]
    congr 1
    funext j
    exact hgmap j
  rw [hrange, hs]

/-- Let `J = IS` for an ideal `I` of `R`. If `M` is flat over `R` and `m : Fin r → M` spans `M`
over `S`, the kernel `K` of `S^r → M`, `e_i ↦ m_i`, satisfies `K ⊓ J • S^r ≤ J • K`. -/
lemma descent_ker_inf_smul_le
    (R : Type*) [CommRing R]
    (n : ℕ)
    (M : Type*) [AddCommGroup M] [Module (MvPolynomial (Fin n) R) M]
    [Module R M] [IsScalarTower R (MvPolynomial (Fin n) R) M]
    [Module.Flat R M]
    (I : Ideal R)
    {r : ℕ} (m : Fin r → M)
    (hspan : Submodule.span (MvPolynomial (Fin n) R) (Set.range m) = ⊤) :
    LinearMap.ker (Fintype.linearCombination (MvPolynomial (Fin n) R) m)
        ⊓ ((Ideal.map (algebraMap R (MvPolynomial (Fin n) R)) I)
              • (⊤ : Submodule (MvPolynomial (Fin n) R) (Fin r → MvPolynomial (Fin n) R)))
      ≤ (Ideal.map (algebraMap R (MvPolynomial (Fin n) R)) I)
              • (LinearMap.ker (Fintype.linearCombination (MvPolynomial (Fin n) R) m)) := by
  set S := MvPolynomial (Fin n) R
  set P := Fin r → S
  set F := Fintype.linearCombination S m
  set K := LinearMap.ker F
  have hsurj : Function.Surjective F :=
    (span_range_eq_top_iff_surjective_fintypeLinearCombination S m).mp hspan
  have hsurjR : Function.Surjective (F.restrictScalars R) := hsurj
  intro z hz
  obtain ⟨hzK, hzJ⟩ := hz
  have hzKR : z ∈ LinearMap.ker (F.restrictScalars R) := by
    rwa [LinearMap.ker_restrictScalars, Submodule.restrictScalars_mem]
  have hzmR : z ∈ I • (⊤ : Submodule R P) := by
    have h := (Ideal.smul_restrictScalars I (⊤ : Submodule S P)).le
    rw [Submodule.restrictScalars_top] at h
    exact h (by rwa [Submodule.restrictScalars_mem])
  have habs :=
    (LinearMap.ker_inf_smul_top_eq_smul_of_flat I (F.restrictScalars R) hsurjR).le ⟨hzKR, hzmR⟩
  rw [LinearMap.ker_restrictScalars] at habs
  have hfin := (Ideal.smul_restrictScalars I K).ge habs
  rw [Submodule.restrictScalars_mem] at hfin
  exact hfin

/-- Let `J = 𝔪S`. If `M` is flat over `R` and `m : Fin r → M` spans `M` over `S`, the kernel
`K` of `S^r → M`, `e_i ↦ m_i`, contains finitely many elements `g_j` with
`K ≤ span S {g_j} ⊔ J • K`. -/
lemma descent_exists_gens_mod_jacobson
    (R : Type*) [CommRing R] [IsLocalRing R]
    (n : ℕ)
    (M : Type*) [AddCommGroup M] [Module (MvPolynomial (Fin n) R) M]
    [Module R M] [IsScalarTower R (MvPolynomial (Fin n) R) M]
    [Module.Flat R M]
    {r : ℕ} (m : Fin r → M)
    (hspan : Submodule.span (MvPolynomial (Fin n) R) (Set.range m) = ⊤) :
    ∃ (t : ℕ) (g : Fin t → (Fin r → MvPolynomial (Fin n) R)),
      (∀ j, g j ∈ LinearMap.ker (Fintype.linearCombination (MvPolynomial (Fin n) R) m)) ∧
      LinearMap.ker (Fintype.linearCombination (MvPolynomial (Fin n) R) m) ≤
        Submodule.span (MvPolynomial (Fin n) R) (Set.range g)
          ⊔ (Ideal.map (algebraMap R (MvPolynomial (Fin n) R)) (IsLocalRing.maximalIdeal R))
              • (LinearMap.ker (Fintype.linearCombination (MvPolynomial (Fin n) R) m)) := by
  classical
  set S := MvPolynomial (Fin n) R
  set F := Fintype.linearCombination S m
  set K := LinearMap.ker F
  set J : Ideal S := Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R)
  obtain ⟨t, g, hgker, hgle⟩ := descent_image_mod_jacobson_le R n M (IsLocalRing.maximalIdeal R) m
  have hB := descent_ker_inf_smul_le R n M (IsLocalRing.maximalIdeal R) m hspan
  refine ⟨t, g, hgker, ?_⟩
  intro x hx
  have hx' := hgle hx
  rw [Submodule.mem_sup] at hx'
  obtain ⟨s, hs, p, hp, hxsp⟩ := hx'
  have hsK : s ∈ K := Submodule.span_le.2 (by
    rintro _ ⟨j, rfl⟩; exact hgker j) hs
  have hpK : p ∈ K := by
    have : p = x - s := by rw [← hxsp]; ring
    rw [this]; exact K.sub_mem hx hsK
  have hpJK : p ∈ J • K := hB ⟨hpK, hp⟩
  rw [Submodule.mem_sup]
  exact ⟨s, hs, p, hpJK, hxsp⟩

/-- Shifted-degree piece of `S^r = Fin r → S`: the `R`-submodule of tuples whose
`i`-th coordinate is weighted-homogeneous of degree `d - deg i`. -/
noncomputable def shiftPiece (R : Type*) [CommRing R]
    (n : ℕ) (w : Fin n → ℤ) {r : ℕ} (deg : Fin r → ℤ) (d : ℤ) :
    Submodule R (Fin r → MvPolynomial (Fin n) R) where
  carrier := { x | ∀ i, x i ∈ weightedHomogeneousSubmodule R w (d - deg i) }
  add_mem' ha hb i := (weightedHomogeneousSubmodule R w (d - _)).add_mem (ha i) (hb i)
  zero_mem' i := (weightedHomogeneousSubmodule R w (d - deg i)).zero_mem
  smul_mem' c _ ha i := (weightedHomogeneousSubmodule R w (d - deg i)).smul_mem c (ha i)

/-- **`Fintype.linearCombination m` is degree-preserving.** If `m i ∈ 𝓜 (deg i)` for all `i`,
then `x ↦ ∑ i, x i • m i` sends `shiftPiece d` into `𝓜 d`. -/
lemma linearCombination_mem_of_mem_shiftPiece
    (R : Type*) [CommRing R]
    (n : ℕ) (w : Fin n → ℤ)
    (M : Type*) [AddCommGroup M] [Module (MvPolynomial (Fin n) R) M]
    [Module R M] [IsScalarTower R (MvPolynomial (Fin n) R) M]
    (𝓜 : ℤ → Submodule R M)
    [SetLike.GradedSMul (weightedHomogeneousSubmodule R w) 𝓜]
    {r : ℕ} {m : Fin r → M} {deg : Fin r → ℤ} (hm : ∀ i, m i ∈ 𝓜 (deg i))
    {d : ℤ} {x : Fin r → MvPolynomial (Fin n) R} (hx : x ∈ shiftPiece R n w deg d) :
    Fintype.linearCombination (MvPolynomial (Fin n) R) m x ∈ 𝓜 d := by
  rw [Fintype.linearCombination_apply]
  refine Submodule.sum_mem _ fun i _ => ?_
  have := SetLike.GradedSMul.smul_mem
    (A := weightedHomogeneousSubmodule R w) (B := 𝓜)
    (SetLike.coe_mem (⟨x i, hx i⟩ : weightedHomogeneousSubmodule R w (d - deg i))) (hm i)
  rwa [show (d - deg i) +ᵥ deg i = d from by rw [vadd_eq_add]; ring] at this

/-- **Bounded-below graded Nakayama.**
If an `R`-module `Q` over a local ring carries a degreewise family `Qg`, with each piece finitely
generated, the grading bounded below, and each piece contained in
`𝔪·(that piece) ⊔ (sum of strictly-lower pieces)`, then every piece vanishes. -/
@[ega "0 1.7.5" "Nakayama step"]
lemma graded_nakayama_vanish
    (R : Type*) [CommRing R] [IsLocalRing R]
    (Q : Type*) [AddCommGroup Q] [Module R Q]
    (Qg : ℤ → Submodule R Q)
    (hfin : ∀ d, (Qg d).FG)
    (d₀ : ℤ) (hbdd : ∀ d, d < d₀ → Qg d = ⊥)
    (hnak : ∀ d, Qg d ≤ IsLocalRing.maximalIdeal R • Qg d ⊔ (⨆ e ∈ Set.Iio d, Qg e)) :
    ∀ d, Qg d = ⊥ := by
  have key : ∀ d, (∀ e, e < d → Qg e = ⊥) → Qg d = ⊥ := by
    intro d hlow
    have hcollapse : (⨆ e ∈ Set.Iio d, Qg e) = ⊥ := by
      rw [iSup₂_eq_bot]
      intro e he
      exact hlow e (Set.mem_Iio.mp he)
    have hsmul : Qg d ≤ IsLocalRing.maximalIdeal R • Qg d := by
      have := hnak d
      rwa [hcollapse, sup_bot_eq] at this
    exact Submodule.eq_bot_of_le_smul_of_le_jacobson_bot
      (I := IsLocalRing.maximalIdeal R) (N := Qg d) (hfin d) hsmul
      (IsLocalRing.maximalIdeal_le_jacobson ⊥)
  have main : ∀ (k : ℕ) (d : ℤ), (d - d₀).toNat = k → Qg d = ⊥ := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro d hk
      apply key d
      intro e he
      by_cases hed : e < d₀
      · exact hbdd e hed
      · have hed' : d₀ ≤ e := not_lt.mp hed
        have hlt : (e - d₀).toNat < k := by
          rw [← hk]
          omega
        exact ih _ hlt e rfl
  intro d
  exact main (d - d₀).toNat d rfl

/-- Summing the shifted weighted homogeneous components `p_{d - s}` of `p` over any finset
`D` containing the shifted support recovers `p`. -/
lemma sum_decompose_sub_eq (R : Type*) [CommRing R] (n : ℕ) (w : Fin n → ℤ)
    (p : MvPolynomial (Fin n) R) (s : ℤ) (D : Finset ℤ) :
    letI : DirectSum.Decomposition (weightedHomogeneousSubmodule R w) :=
      (weightedGradedAlgebra R w).toDecomposition
    (∀ e, DirectSum.decompose (weightedHomogeneousSubmodule R w) p e ≠ 0 → e + s ∈ D) →
      ∑ d ∈ D, (DirectSum.decompose (weightedHomogeneousSubmodule R w) p (d - s) :
        MvPolynomial (Fin n) R) = p := by
  classical
  let : DirectSum.Decomposition (weightedHomogeneousSubmodule R w) :=
    (weightedGradedAlgebra R w).toDecomposition
  intro hD
  set E := (DirectSum.decompose (weightedHomogeneousSubmodule R w) p).support
  have hsub : E.image (· + s) ⊆ D := fun d hd => by
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hd
    exact hD e (DFinsupp.mem_support_iff.mp he)
  rw [← Finset.sum_subset hsub fun d _ hd => ?_,
    Finset.sum_image (by intro a _ b _ hab; simpa using hab)]
  · refine (Finset.sum_congr rfl fun e _ => ?_).trans
      (DirectSum.sum_support_decompose (weightedHomogeneousSubmodule R w) p)
    rw [add_sub_cancel_right]
  · have hns : d - s ∉ E := fun hmem => hd (Finset.mem_image.mpr ⟨d - s, hmem, by ring⟩)
    rw [DFinsupp.notMem_support_iff.mp hns]; rfl

/-- Pieces `v f ∈ 𝓜 f` of a graded module that sum to zero over `D` all vanish. -/
private theorem eq_zero_of_sum_eq_zero_of_mem_graded
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (𝓜 : ℤ → Submodule R M) [DirectSum.Decomposition 𝓜] (D : Finset ℤ) (v : ℤ → M)
    (hv : ∀ f ∈ D, v f ∈ 𝓜 f) (hsum : ∑ f ∈ D, v f = 0) {e : ℤ} (he : e ∈ D) : v e = 0 := by
  have key : (DirectSum.decompose 𝓜 (∑ f ∈ D, v f) e : M) = v e := by
    rw [DirectSum.decompose_sum, DFinsupp.finsetSum_apply, AddSubmonoidClass.coe_finsetSum,
      Finset.sum_eq_single e]
    · exact DirectSum.decompose_of_mem_same 𝓜 (hv e he)
    · exact fun f hf hfe => DirectSum.decompose_of_mem_ne 𝓜 (hv f hf) hfe
    · exact fun hns => absurd he hns
  rw [hsum, DirectSum.decompose_zero, DFinsupp.zero_apply] at key
  simpa using key.symm

/-- Every `x : S^r` is the finite sum of its coordinatewise homogeneous components of degree
`d - deg i`, all other components being zero. -/
private theorem exists_finset_sum_decompose_sub (R : Type*) [CommRing R]
    (n : ℕ) (w : Fin n → ℤ) {r : ℕ} (deg : Fin r → ℤ) (x : Fin r → MvPolynomial (Fin n) R) :
    letI : DirectSum.Decomposition (weightedHomogeneousSubmodule R w) :=
      (weightedGradedAlgebra R w).toDecomposition
    ∃ D : Finset ℤ,
      (∑ d ∈ D, fun i => (DirectSum.decompose (weightedHomogeneousSubmodule R w) (x i) (d - deg i) :
        MvPolynomial (Fin n) R)) = x ∧
      ∀ f ∉ D, ∀ i, (DirectSum.decompose (weightedHomogeneousSubmodule R w) (x i) (f - deg i) :
        MvPolynomial (Fin n) R) = 0 := by
  classical
  let instS : DirectSum.Decomposition (weightedHomogeneousSubmodule R w) :=
    (weightedGradedAlgebra R w).toDecomposition
  set D : Finset ℤ := Finset.univ.biUnion (fun i : Fin r =>
    (DirectSum.decompose (weightedHomogeneousSubmodule R w) (x i)).support.image (· + deg i)) with
      hDdef
  refine ⟨D, ?_, fun f hf i => ?_⟩
  · funext i
    simp only [Finset.sum_apply]
    refine sum_decompose_sub_eq R n w (x i) (deg i) D fun e he => ?_
    rw [hDdef]
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i,
      Finset.mem_image.mpr ⟨e, DFinsupp.mem_support_iff.mpr he, rfl⟩⟩
  · have hns : f - deg i ∉
        (DirectSum.decompose (weightedHomogeneousSubmodule R w) (x i)).support := by
      intro hmem
      apply hf
      rw [hDdef]
      simp only [Finset.mem_biUnion]
      exact ⟨i, Finset.mem_univ i, Finset.mem_image.mpr ⟨f - deg i, hmem, by ring⟩⟩
    rw [DFinsupp.notMem_support_iff.mp hns]; rfl

/-- **Homogeneity of `K = ker F`.** If `m i ∈ 𝓜 (deg i)` for all `i`, the kernel of
`F = Fintype.linearCombination S m` is, as an `R`-submodule, the supremum of its pieces
`K ⊓ shiftPiece d`. -/
lemma descent_K_homogeneous
    (R : Type*) [CommRing R]
    (n : ℕ) (w : Fin n → ℤ)
    (M : Type*) [AddCommGroup M] [Module (MvPolynomial (Fin n) R) M]
    [Module R M] [IsScalarTower R (MvPolynomial (Fin n) R) M]
    (𝓜 : ℤ → Submodule R M)
    [SetLike.GradedSMul (weightedHomogeneousSubmodule R w) 𝓜]
    [DirectSum.Decomposition 𝓜]
    {r : ℕ} (m : Fin r → M) (deg : Fin r → ℤ)
    (hm : ∀ i, m i ∈ 𝓜 (deg i)) :
    (LinearMap.ker (Fintype.linearCombination (MvPolynomial (Fin n) R) m)).restrictScalars R
      = ⨆ d, ((LinearMap.ker (Fintype.linearCombination (MvPolynomial (Fin n) R)
          m)).restrictScalars R
          ⊓ shiftPiece R n w deg d) := by
  classical
  set S := MvPolynomial (Fin n) R
  let instS : DirectSum.Decomposition (weightedHomogeneousSubmodule R w) :=
    (weightedGradedAlgebra R w).toDecomposition
  set F := Fintype.linearCombination S m with hFdef
  set K := LinearMap.ker F with hKdef
  let comp : S → ℤ → S := fun p e =>
    (DirectSum.decompose (weightedHomogeneousSubmodule R w) p e : S)
  let xd : (Fin r → S) → ℤ → (Fin r → S) := fun x d i => comp (x i) (d - deg i)
  have hxd_mem : ∀ x d, xd x d ∈ shiftPiece R n w deg d := fun _ _ _ => SetLike.coe_mem _
  have hFdeg : ∀ x d, x ∈ shiftPiece R n w deg d → F x ∈ 𝓜 d := fun x d hx => by
    rw [hFdef]; exact linearCombination_mem_of_mem_shiftPiece R n w M 𝓜 hm hx
  apply le_antisymm
  · intro x hx
    rw [Submodule.restrictScalars_mem, hKdef, LinearMap.mem_ker, hFdef,
      Fintype.linearCombination_apply] at hx
    obtain ⟨D, hsum, -⟩ := exists_finset_sum_decompose_sub R n w deg x
    have hxd_ker : ∀ d ∈ D, xd x d ∈ K := fun d hd =>
      eq_zero_of_sum_eq_zero_of_mem_graded 𝓜 D (fun d => F (xd x d))
        (fun d _ => hFdeg _ _ (hxd_mem x d))
        (by rwa [← map_sum, hsum, hFdef, Fintype.linearCombination_apply]) hd
    rw [← hsum]
    refine Submodule.sum_mem _ fun d hd => ?_
    refine Submodule.mem_iSup_of_mem d ?_
    refine Submodule.mem_inf.mpr ⟨?_, hxd_mem x d⟩
    rw [Submodule.restrictScalars_mem]
    exact hxd_ker d hd
  · exact iSup_le (fun d => inf_le_left)

/-- **Degreewise finiteness of `K`.** If every `𝓜 d` is free over `R` and `m` is a
homogeneous generating family, the piece `K ⊓ shiftPiece d` of `K = ker F` is finite
over `R`. -/
lemma descent_Kpiece_finite
    (R : Type*) [CommRing R]
    (n : ℕ) (w : Fin n → ℤ) (hw : ∀ i, 0 < w i)
    (M : Type*) [AddCommGroup M] [Module (MvPolynomial (Fin n) R) M]
    [Module R M] [IsScalarTower R (MvPolynomial (Fin n) R) M]
    (𝓜 : ℤ → Submodule R M)
    [SetLike.GradedSMul (weightedHomogeneousSubmodule R w) 𝓜]
    [DirectSum.Decomposition 𝓜]
    (hMfree : ∀ d, Module.Free R (𝓜 d))
    {r : ℕ} (m : Fin r → M) (deg : Fin r → ℤ)
    (hm : ∀ i, m i ∈ 𝓜 (deg i))
    (hspan : Submodule.span (MvPolynomial (Fin n) R) (Set.range m) = ⊤)
    (d : ℤ) :
    Module.Finite R
      (↥((LinearMap.ker (Fintype.linearCombination (MvPolynomial (Fin n) R) m)).restrictScalars R
        ⊓ shiftPiece R n w deg d)) := by
  classical
  let instS : DirectSum.Decomposition (weightedHomogeneousSubmodule R w) :=
    (weightedGradedAlgebra R w).toDecomposition
  let π : M →ₗ[R] M := (𝓜 d).subtype.comp
    ((DirectSum.component R ℤ (fun j => (𝓜 j : Submodule R M)) d).comp
      (DirectSum.decomposeLinearEquiv 𝓜).toLinearMap)
  have hπ : ∀ y : M, π y = (DirectSum.decompose 𝓜 y d : M) := fun y => rfl
  have hπx : ∀ (x : M), x ∈ 𝓜 d → π x = x := fun x hx => by
    rw [hπ, DirectSum.decompose_of_mem_same 𝓜 hx]
  have hπ0 : ∀ (e : ℤ) (x : M), x ∈ 𝓜 e → e ≠ d → π x = 0 := fun e x hx hed => by
    rw [hπ, DirectSum.decompose_of_mem_ne 𝓜 hx hed]
  have key : ∀ (e : ℤ) (mi : M), mi ∈ 𝓜 e → ∀ (p : MvPolynomial (Fin n) R),
      π (p • mi)
        = ((DirectSum.decompose (weightedHomogeneousSubmodule R w) p (d - e) :
            MvPolynomial (Fin n) R)) • mi := by
    intro e mi hmi p
    have hp : p = ∑ f ∈ (DirectSum.decompose (weightedHomogeneousSubmodule R w) p).support,
        ((DirectSum.decompose (weightedHomogeneousSubmodule R w) p f : MvPolynomial (Fin n) R)) :=
      (DirectSum.sum_support_decompose (weightedHomogeneousSubmodule R w) p).symm
    have hsmul : p • mi = ∑ f ∈ (DirectSum.decompose (weightedHomogeneousSubmodule R w) p).support,
        ((DirectSum.decompose (weightedHomogeneousSubmodule R w) p f : MvPolynomial (Fin n) R))
          • mi := by
      conv_lhs => rw [hp]
      rw [Finset.sum_smul]
    rw [hsmul, map_sum]
    have hmem : ∀ f : ℤ, ((DirectSum.decompose (weightedHomogeneousSubmodule R w) p f :
        MvPolynomial (Fin n) R)) • mi ∈ 𝓜 (f + e) := by
      intro f
      simpa using SetLike.GradedSMul.smul_mem
        (A := weightedHomogeneousSubmodule R w) (B := 𝓜)
        (SetLike.coe_mem (DirectSum.decompose (weightedHomogeneousSubmodule R w) p f)) hmi
    rw [Finset.sum_eq_single (d - e)]
    · apply hπx
      have := hmem (d - e)
      rwa [show (d - e) + e = d from by ring] at this
    · intro f hf hfne
      apply hπ0 (f + e) _ (hmem f)
      exact fun h => hfne (by omega)
    · intro hns
      have hz : (DirectSum.decompose (weightedHomogeneousSubmodule R w) p) (d - e) = 0 :=
        DFinsupp.notMem_support_iff.mp hns
      rw [hz, ZeroMemClass.coe_zero, zero_smul, map_zero]
  let F0 : (Π i : Fin r, weightedHomogeneousSubmodule R w (d - deg i)) →ₗ[R] M :=
    ∑ i : Fin r,
      (LinearMap.smulRight (R := R) (S := MvPolynomial (Fin n) R) (LinearMap.id) (m i)).comp
        ((weightedHomogeneousSubmodule R w (d - deg i)).subtype.comp (LinearMap.proj i))
  have hF0 : ∀ s, F0 s = ∑ i : Fin r, ((s i : MvPolynomial (Fin n) R)) • m i := by
    intro s
    simp only [F0, LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply,
      LinearMap.proj_apply, Submodule.subtype_apply, LinearMap.smulRight_apply, LinearMap.id_apply]
  have hF0mem : ∀ s, F0 s ∈ 𝓜 d := fun s => by
    have := linearCombination_mem_of_mem_shiftPiece R n w M 𝓜 hm (d := d)
      (x := fun i => ((s i : MvPolynomial (Fin n) R))) fun i => SetLike.coe_mem (s i)
    rwa [Fintype.linearCombination_apply, ← hF0] at this
  let φ : (Π i : Fin r, weightedHomogeneousSubmodule R w (d - deg i)) →ₗ[R] (𝓜 d) :=
    LinearMap.codRestrict (𝓜 d) F0 hF0mem
  have hsurj : Function.Surjective φ := by
    rintro ⟨x, hx⟩
    have hxspan : x ∈ Submodule.span (MvPolynomial (Fin n) R) (Set.range m) := by
      rw [hspan]; trivial
    rw [Submodule.mem_span_range_iff_exists_fun] at hxspan
    obtain ⟨c, hc⟩ := hxspan
    refine ⟨fun i => ⟨(DirectSum.decompose (weightedHomogeneousSubmodule R w) (c i) (d - deg i) :
        MvPolynomial (Fin n) R), SetLike.coe_mem _⟩, ?_⟩
    apply Subtype.ext
    rw [LinearMap.codRestrict_apply, hF0]
    change (∑ i : Fin r, (DirectSum.decompose (weightedHomogeneousSubmodule R w) (c i) (d - deg i) :
        MvPolynomial (Fin n) R) • m i) = x
    rw [← hπx x hx, ← hc, map_sum]
    exact Finset.sum_congr rfl fun i _ => (key (deg i) (m i) (hm i) (c i)).symm
  have : ∀ i : Fin r, Module.Finite R (weightedHomogeneousSubmodule R w (d - deg i)) :=
    fun i => weightedHomogeneousSubmodule_finite_of_pos R w hw (d - deg i)
  have : ∀ i : Fin r, Module.Free R (weightedHomogeneousSubmodule R w (d - deg i)) :=
    fun i => weightedHomogeneousSubmodule_free R w (d - deg i)
  have hPfin : Module.Finite R (Π i : Fin r, weightedHomogeneousSubmodule R w (d - deg i)) :=
    Module.Finite.pi
  have : Module.Free R (𝓜 d) := hMfree d
  obtain ⟨σ, hσ⟩ := LinearMap.exists_rightInverse_of_surjective φ
    (LinearMap.range_eq_top.mpr hsurj)
  let pmap : (Π i : Fin r, weightedHomogeneousSubmodule R w (d - deg i)) →ₗ[R]
      (Π i : Fin r, weightedHomogeneousSubmodule R w (d - deg i)) :=
    LinearMap.id - σ.comp φ
  have hpmem : ∀ x : (Π i : Fin r, weightedHomogeneousSubmodule R w (d - deg i)),
      pmap x ∈ LinearMap.ker φ := by
    intro x
    change φ (pmap x) = 0
    rw [show pmap x = x - σ (φ x) from rfl, map_sub]
    have : φ (σ (φ x)) = φ x := by
      rw [← LinearMap.comp_apply, hσ, LinearMap.id_apply]
    rw [this, sub_self]
  let p : (Π i : Fin r, weightedHomogeneousSubmodule R w (d - deg i)) →ₗ[R] LinearMap.ker φ :=
    LinearMap.codRestrict (LinearMap.ker φ) pmap hpmem
  have hpsurj : Function.Surjective p := by
    rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    apply Subtype.ext
    rw [LinearMap.codRestrict_apply]
    change y - σ (φ y) = y
    have hφy : φ y = 0 := by rwa [LinearMap.mem_ker] at hy
    rw [hφy, map_zero, sub_zero]
  have hkerfin : Module.Finite R (LinearMap.ker φ) := Module.Finite.of_surjective p hpsurj
  set T : Submodule R (Fin r → MvPolynomial (Fin n) R) :=
    (LinearMap.ker (Fintype.linearCombination (MvPolynomial (Fin n) R) m)).restrictScalars R
      ⊓ shiftPiece R n w deg d with hT
  have hshift : ∀ x : (Fin r → MvPolynomial (Fin n) R), x ∈ shiftPiece R n w deg d ↔
      ∀ i, x i ∈ weightedHomogeneousSubmodule R w (d - deg i) := fun x => Iff.rfl
  have hfwdmem : ∀ x : T,
      (fun i => (⟨(x : Fin r → MvPolynomial (Fin n) R) i, (hshift _).mp x.2.2 i⟩ :
      weightedHomogeneousSubmodule R w (d - deg i))) ∈ LinearMap.ker φ := by
    rintro ⟨x, hxK, hxS⟩
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    rw [LinearMap.codRestrict_apply, hF0]
    have hFx : (Fintype.linearCombination (MvPolynomial (Fin n) R) m) x = 0 := by
      rwa [← LinearMap.mem_ker, ← Submodule.restrictScalars_mem R]
    rw [Fintype.linearCombination_apply] at hFx
    simpa using hFx
  let toKer : T →ₗ[R] LinearMap.ker φ :=
    { toFun := fun x => ⟨fun i => ⟨(x : Fin r → MvPolynomial (Fin n) R) i, (hshift _).mp x.2.2 i⟩,
        hfwdmem x⟩
      map_add' := by intro a b; apply Subtype.ext; funext i; apply Subtype.ext; rfl
      map_smul' := by intro c a; apply Subtype.ext; funext i; apply Subtype.ext; rfl }
  have hinvmem : ∀ s : LinearMap.ker φ,
      (fun i => ((s : Π i : Fin r, weightedHomogeneousSubmodule R w (d - deg i)) i :
        MvPolynomial (Fin n) R)) ∈ T := by
    rintro ⟨s, hs⟩
    rw [hT]
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · rw [Submodule.restrictScalars_mem, LinearMap.mem_ker, Fintype.linearCombination_apply]
      have hφs : φ s = 0 := by rwa [LinearMap.mem_ker] at hs
      have : (φ s : M) = 0 := by rw [hφs]; rfl
      rw [LinearMap.codRestrict_apply, hF0] at this
      simpa using this
    · intro i; exact (s i).2
  let invKer : LinearMap.ker φ →ₗ[R] T :=
    { toFun := fun s =>
        ⟨fun i => ((s : Π i : Fin r, weightedHomogeneousSubmodule R w (d - deg i)) i :
        MvPolynomial (Fin n) R), hinvmem s⟩
      map_add' := by intro a b; apply Subtype.ext; funext i; rfl
      map_smul' := by intro c a; apply Subtype.ext; funext i; rfl }
  let e : T ≃ₗ[R] LinearMap.ker φ :=
    { toKer with
      invFun := invKer
      left_inv := by intro x; apply Subtype.ext; funext i; rfl
      right_inv := by intro s; apply Subtype.ext; funext i; apply Subtype.ext; rfl }
  exact Module.Finite.equiv e.symm

/-- For positive weights, a weighted-homogeneous polynomial of negative degree is `0`. -/
lemma whs_bot_of_neg (R : Type*) [CommRing R] {σ : Type*} (w : σ → ℤ) (hw : ∀ i, 0 < w i)
    (e : ℤ) (he : e < 0) : weightedHomogeneousSubmodule R w e = ⊥ := by
  rw [eq_bot_iff]
  intro p hp
  rw [mem_weightedHomogeneousSubmodule] at hp
  rw [Submodule.mem_bot]
  by_contra hpne
  obtain ⟨a, ha⟩ := MvPolynomial.ne_zero_iff.mp hpne
  have hwa : Finsupp.weight w a = e := hp ha
  have hnn : (0:ℤ) ≤ Finsupp.weight w a := by
    rw [Finsupp.weight_apply, Finsupp.sum]
    apply Finset.sum_nonneg
    intro i _
    have := hw i
    positivity
  omega

/-- **Bounded below.** For positive weights there is `d₀` with `shiftPiece d = ⊥` for all
`d < d₀`. -/
lemma descent_shiftPiece_bot_of_lt
    (R : Type*) [CommRing R]
    (n : ℕ) (w : Fin n → ℤ) (hw : ∀ i, 0 < w i)
    {r : ℕ} (deg : Fin r → ℤ) :
    ∃ d₀ : ℤ, ∀ d : ℤ, d < d₀ → shiftPiece R n w deg d = ⊥ := by
  classical
  obtain hr | hr := Nat.eq_zero_or_pos r
  · subst hr
    refine ⟨0, fun d _ => ?_⟩
    rw [eq_bot_iff]
    intro x _
    rw [Submodule.mem_bot]
    funext i
    exact absurd i.2 (by simp)
  · have hne : (Finset.univ : Finset (Fin r)).Nonempty := by
      rw [Finset.univ_nonempty_iff]; exact ⟨⟨0, hr⟩⟩
    refine ⟨(Finset.univ.inf' hne deg), fun d hd => ?_⟩
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_bot]
    funext i
    have hdi : d - deg i < 0 := by
      have : Finset.univ.inf' hne deg ≤ deg i := Finset.inf'_le deg (Finset.mem_univ i)
      omega
    have := hx i
    rw [whs_bot_of_neg R w hw (d - deg i) hdi, Submodule.mem_bot] at this
    simpa using this

/-- **Degree-`e` projection on `S^r`.**  Coordinatewise weighted-homogeneous
component: `(descentProj e x) i = (x i)_{e - deg i}`.  An `R`-linear endomorphism of
`S^r` whose image at degree `e` is `shiftPiece e`, fixing `shiftPiece e`. -/
noncomputable def descentProj (R : Type*) [CommRing R]
    (n : ℕ) (w : Fin n → ℤ) {r : ℕ} (deg : Fin r → ℤ) (e : ℤ) :
    (Fin r → MvPolynomial (Fin n) R) →ₗ[R] (Fin r → MvPolynomial (Fin n) R) :=
  letI : DirectSum.Decomposition (weightedHomogeneousSubmodule R w) :=
    (weightedGradedAlgebra R w).toDecomposition
  LinearMap.pi (fun i =>
    ((weightedHomogeneousSubmodule R w (e - deg i)).subtype.comp
      ((DirectSum.component R ℤ (fun j => (weightedHomogeneousSubmodule R w j : Submodule R _))
        (e - deg i)).comp
        (DirectSum.decomposeLinearEquiv (weightedHomogeneousSubmodule R w)).toLinearMap)).comp
      (LinearMap.proj i))

/-- The defining formula for `descentProj`: it picks out the `(e - deg i)` weighted
homogeneous component in each coordinate. -/
lemma descentProj_apply (R : Type*) [CommRing R]
    (n : ℕ) (w : Fin n → ℤ) {r : ℕ} (deg : Fin r → ℤ) (e : ℤ)
    (x : Fin r → MvPolynomial (Fin n) R) (i : Fin r) :
    letI : DirectSum.Decomposition (weightedHomogeneousSubmodule R w) :=
      (weightedGradedAlgebra R w).toDecomposition
    descentProj R n w deg e x i =
      (DirectSum.decompose (weightedHomogeneousSubmodule R w) (x i) (e - deg i) :
        MvPolynomial (Fin n) R) := by
  rfl

/-- `descentProj e x` lands in `shiftPiece e`. -/
lemma descentProj_mem (R : Type*) [CommRing R]
    (n : ℕ) (w : Fin n → ℤ) {r : ℕ} (deg : Fin r → ℤ) (e : ℤ)
    (x : Fin r → MvPolynomial (Fin n) R) :
    descentProj R n w deg e x ∈ shiftPiece R n w deg e := fun i => by
  rw [descentProj_apply]; exact SetLike.coe_mem _

/-- On `shiftPiece e`, `descentProj e` is the identity. -/
lemma descentProj_eq_self (R : Type*) [CommRing R]
    (n : ℕ) (w : Fin n → ℤ) {r : ℕ} (deg : Fin r → ℤ) (e : ℤ)
    (x : Fin r → MvPolynomial (Fin n) R) (hx : x ∈ shiftPiece R n w deg e) :
    descentProj R n w deg e x = x := by
  let instS : DirectSum.Decomposition (weightedHomogeneousSubmodule R w) :=
    (weightedGradedAlgebra R w).toDecomposition
  funext i
  rw [descentProj_apply]
  exact DirectSum.decompose_of_mem_same (weightedHomogeneousSubmodule R w) (hx i)

/-- **Degree projection of a scalar multiple of a homogeneous element.**  If `h` is
homogeneous of degree `δ`, then `descentProj e (c • h) = (c)_{e - δ} • h`, the
degree-`(e - δ)` weighted-homogeneous component of `c` times `h`. -/
lemma descentProj_smul_homog (R : Type*) [CommRing R]
    (n : ℕ) (w : Fin n → ℤ) {r : ℕ} (deg : Fin r → ℤ) (e δ : ℤ)
    (c : MvPolynomial (Fin n) R) (h : Fin r → MvPolynomial (Fin n) R)
    (hh : h ∈ shiftPiece R n w deg δ) :
    letI : DirectSum.Decomposition (weightedHomogeneousSubmodule R w) :=
      (weightedGradedAlgebra R w).toDecomposition
    descentProj R n w deg e (c • h)
      = (DirectSum.decompose (weightedHomogeneousSubmodule R w) c (e - δ) :
        MvPolynomial (Fin n) R) • h := by
  classical
  let : DirectSum.Decomposition (weightedHomogeneousSubmodule R w) :=
    (weightedGradedAlgebra R w).toDecomposition
  have : GradedRing (weightedHomogeneousSubmodule R w) := weightedGradedAlgebra R w
  funext i
  set φ : MvPolynomial (Fin n) R →ₗ[R] MvPolynomial (Fin n) R :=
    (weightedHomogeneousSubmodule R w (e - deg i)).subtype.comp
      ((DirectSum.component R ℤ (fun j => (weightedHomogeneousSubmodule R w j : Submodule R _))
        (e - deg i)).comp
        (DirectSum.decomposeLinearEquiv (weightedHomogeneousSubmodule R w)).toLinearMap)
  have hφ : ∀ x, φ x = (DirectSum.decompose (weightedHomogeneousSubmodule R w) x (e - deg i) :
      MvPolynomial (Fin n) R) :=
    fun x => rfl
  change φ ((c • h) i) = (DirectSum.decompose (weightedHomogeneousSubmodule R w) c (e - δ) :
      MvPolynomial (Fin n) R) * h i
  have hci : (c • h) i = c * h i := rfl
  rw [hci]
  set Ec := (DirectSum.decompose (weightedHomogeneousSubmodule R w) c).support
  have hmul : c * h i = ∑ f ∈ Ec,
      (DirectSum.decompose (weightedHomogeneousSubmodule R w) c f : MvPolynomial (Fin n) R)
        * h i := by
    conv_lhs => rw [show c = ∑ f ∈ Ec,
      (DirectSum.decompose (weightedHomogeneousSubmodule R w) c f : MvPolynomial (Fin n) R) from
      (DirectSum.sum_support_decompose (weightedHomogeneousSubmodule R w) c).symm]
    rw [Finset.sum_mul]
  rw [hmul, map_sum]
  simp only [hφ]
  have hmem : ∀ f, (DirectSum.decompose (weightedHomogeneousSubmodule R w) c f : MvPolynomial (Fin
      n) R) * h i
      ∈ weightedHomogeneousSubmodule R w (f + (δ - deg i)) :=
    fun f => SetLike.mul_mem_graded (SetLike.coe_mem _) (hh i)
  rw [Finset.sum_eq_single (e - δ)]
  · rw [DirectSum.decompose_of_mem_same (weightedHomogeneousSubmodule R w) ?_]
    · have := hmem (e - δ)
      rwa [show (e - δ) + (δ - deg i) = e - deg i from by ring] at this
  · intro f hf hfne
    rw [DirectSum.decompose_of_mem_ne (weightedHomogeneousSubmodule R w) (hmem f) ?_]
    intro hcontra; apply hfne; omega
  · intro hns
    have hz : (DirectSum.decompose (weightedHomogeneousSubmodule R w) c (e - δ)) = 0 :=
      DFinsupp.notMem_support_iff.mp hns
    rw [hz]; simp

/-- **Decomposition into homogeneous components.**  Every `x : S^r` is the finite sum
of its degree-`e` projections `descentProj e x`, all other projections being zero. -/
lemma descentProj_sum_eq (R : Type*) [CommRing R]
    (n : ℕ) (w : Fin n → ℤ) {r : ℕ} (deg : Fin r → ℤ)
    (x : Fin r → MvPolynomial (Fin n) R) :
    ∃ D : Finset ℤ, (∑ e ∈ D, descentProj R n w deg e x = x) ∧
      ∀ f ∉ D, descentProj R n w deg f x = 0 := by
  obtain ⟨D, hsum, hzero⟩ := exists_finset_sum_decompose_sub R n w deg x
  exact ⟨D, hsum, fun f hf => funext (hzero f hf)⟩

/-- **`K = ker F` is closed under the degree projection:** each homogeneous component
of an element of `K` is again in `K`. -/
lemma descent_K_proj_mem
    (R : Type*) [CommRing R]
    (n : ℕ) (w : Fin n → ℤ)
    (M : Type*) [AddCommGroup M] [Module (MvPolynomial (Fin n) R) M]
    [Module R M] [IsScalarTower R (MvPolynomial (Fin n) R) M]
    (𝓜 : ℤ → Submodule R M)
    [SetLike.GradedSMul (weightedHomogeneousSubmodule R w) 𝓜]
    [DirectSum.Decomposition 𝓜]
    {r : ℕ} (m : Fin r → M) (deg : Fin r → ℤ)
    (hm : ∀ i, m i ∈ 𝓜 (deg i))
    (e : ℤ) (z : Fin r → MvPolynomial (Fin n) R)
    (hz : z ∈ (LinearMap.ker (Fintype.linearCombination (MvPolynomial (Fin n) R)
        m)).restrictScalars R) :
    descentProj R n w deg e z ∈
      (LinearMap.ker (Fintype.linearCombination (MvPolynomial (Fin n) R) m)).restrictScalars R := by
  classical
  let instS : DirectSum.Decomposition (weightedHomogeneousSubmodule R w) :=
    (weightedGradedAlgebra R w).toDecomposition
  have hFdeg : ∀ x c, x ∈ shiftPiece R n w deg c →
      Fintype.linearCombination (MvPolynomial (Fin n) R) m x ∈ 𝓜 c :=
    fun _ _ hx => linearCombination_mem_of_mem_shiftPiece R n w M 𝓜 hm hx
  rw [Submodule.restrictScalars_mem, LinearMap.mem_ker] at hz
  rw [Submodule.restrictScalars_mem, LinearMap.mem_ker]
  obtain ⟨D, hsum, hzero⟩ := descentProj_sum_eq R n w deg z
  by_cases heD : e ∈ D
  · have hFsum : ∑ f ∈ D,
        Fintype.linearCombination (MvPolynomial (Fin n) R) m (descentProj R n w deg f z)
          = 0 := by
      rwa [← map_sum, hsum]
    exact eq_zero_of_sum_eq_zero_of_mem_graded 𝓜 D
      (fun f => Fintype.linearCombination (MvPolynomial (Fin n) R) m (descentProj R n w deg f z))
      (fun f _ => hFdeg _ _ (descentProj_mem R n w deg f z)) hFsum heD
  · rw [hzero e heD, map_zero]

/-- **Span of homogeneous elements is graded.**  If `K' = span S (range g)` with each
`g j` homogeneous (`g j ∈ shiftPiece δⱼ`), then `K'` (as an `R`-submodule) is closed
under the degree-`e` projection `descentProj e`. -/
lemma descent_span_proj_mem
    (R : Type*) [CommRing R]
    (n : ℕ) (w : Fin n → ℤ)
    {r : ℕ} (deg : Fin r → ℤ)
    {t : ℕ} (g : Fin t → (Fin r → MvPolynomial (Fin n) R))
    (hghom : ∀ j, ∃ δ : ℤ, g j ∈ shiftPiece R n w deg δ)
    (e : ℤ) (s : Fin r → MvPolynomial (Fin n) R)
    (hs : s ∈ (Submodule.span (MvPolynomial (Fin n) R) (Set.range g)).restrictScalars R) :
    descentProj R n w deg e s ∈
      (Submodule.span (MvPolynomial (Fin n) R) (Set.range g)).restrictScalars R := by
  classical
  let instS : DirectSum.Decomposition (weightedHomogeneousSubmodule R w) :=
    (weightedGradedAlgebra R w).toDecomposition
  rw [Submodule.restrictScalars_mem] at hs
  rw [Submodule.mem_span_range_iff_exists_fun] at hs
  obtain ⟨c, rfl⟩ := hs
  rw [map_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  obtain ⟨δ, hδ⟩ := hghom j
  rw [descentProj_smul_homog R n w deg e δ (c j) (g j) hδ]
  rw [Submodule.restrictScalars_mem]
  exact (Submodule.span (MvPolynomial (Fin n) R) (Set.range g)).smul_mem _
    (Submodule.subset_span ⟨j, rfl⟩)

/-- **Graded Nakayama relation.** Let `K' = span S {g_j}` with each `g_j` homogeneous and
`K ≤ K' ⊔ 𝔪S • K`. In `Q := S^r / K'`, the image `Qg d` of `K ⊓ shiftPiece d` satisfies
`Qg d ≤ 𝔪 • Qg d ⊔ (lower pieces)`. -/
lemma descent_smul_graded
    (R : Type*) [CommRing R] [IsLocalRing R]
    (n : ℕ) (w : Fin n → ℤ)
    (M : Type*) [AddCommGroup M] [Module (MvPolynomial (Fin n) R) M]
    [Module R M] [IsScalarTower R (MvPolynomial (Fin n) R) M]
    (𝓜 : ℤ → Submodule R M)
    [SetLike.GradedSMul (weightedHomogeneousSubmodule R w) 𝓜]
    [DirectSum.Decomposition 𝓜]
    {r : ℕ} (m : Fin r → M) (deg : Fin r → ℤ)
    (hm : ∀ i, m i ∈ 𝓜 (deg i))
    {t : ℕ} (g : Fin t → (Fin r → MvPolynomial (Fin n) R))
    (hghom : ∀ j, ∃ δ : ℤ, g j ∈ shiftPiece R n w deg δ)
    (hle : LinearMap.ker (Fintype.linearCombination (MvPolynomial (Fin n) R) m) ≤
        Submodule.span (MvPolynomial (Fin n) R) (Set.range g)
          ⊔ (Ideal.map (algebraMap R (MvPolynomial (Fin n) R)) (IsLocalRing.maximalIdeal R))
              • (LinearMap.ker (Fintype.linearCombination (MvPolynomial (Fin n) R) m)))
    (d : ℤ) :
    (((LinearMap.ker (Fintype.linearCombination (MvPolynomial (Fin n) R) m)).restrictScalars R
        ⊓ shiftPiece R n w deg d).map
        (Submodule.mkQ ((Submodule.span (MvPolynomial (Fin n) R) (Set.range g)).restrictScalars R)))
      ≤ IsLocalRing.maximalIdeal R •
          (((LinearMap.ker (Fintype.linearCombination (MvPolynomial (Fin n) R) m)).restrictScalars R
            ⊓ shiftPiece R n w deg d).map
            (Submodule.mkQ ((Submodule.span (MvPolynomial (Fin n) R) (Set.range g)).restrictScalars
                R)))
        ⊔ (⨆ e ∈ Set.Iio d,
            (((LinearMap.ker (Fintype.linearCombination (MvPolynomial (Fin n) R)
                m)).restrictScalars R
              ⊓ shiftPiece R n w deg e).map
              (Submodule.mkQ
                ((Submodule.span (MvPolynomial (Fin n) R) (Set.range g)).restrictScalars
                  R)))) := by
  classical
  let instS : DirectSum.Decomposition (weightedHomogeneousSubmodule R w) :=
    (weightedGradedAlgebra R w).toDecomposition
  set K := LinearMap.ker (Fintype.linearCombination (MvPolynomial (Fin n) R) m)
  set KR := K.restrictScalars R with hKRdef
  set K' := Submodule.span (MvPolynomial (Fin n) R) (Set.range g)
  set K'R := K'.restrictScalars R with hK'Rdef
  set J : Ideal (MvPolynomial (Fin n) R) :=
    Ideal.map (algebraMap R (MvPolynomial (Fin n) R)) (IsLocalRing.maximalIdeal R)
  set mk := Submodule.mkQ K'R with hmkdef
  set Qd : Submodule R _ := (KR ⊓ shiftPiece R n w deg d).map mk with hQddef
  refine le_trans ?_ le_sup_left
  rw [Submodule.map_le_iff_le_comap]
  intro x hx
  rw [Submodule.mem_inf] at hx
  obtain ⟨hxK, hxsp⟩ := hx
  rw [Submodule.mem_comap]
  have hxK' : x ∈ K := by rwa [hKRdef, Submodule.restrictScalars_mem] at hxK
  have hxle := hle hxK'
  rw [Submodule.mem_sup] at hxle
  obtain ⟨s, hs, p, hp, hxsp_eq⟩ := hxle
  have hsR : s ∈ K'R := by rwa [hK'Rdef, Submodule.restrictScalars_mem]
  have hpR : p ∈ ((J • K).restrictScalars R) := by rwa [Submodule.restrictScalars_mem]
  have hxproj : descentProj R n w deg d x = x :=
    descentProj_eq_self R n w deg d x hxsp
  have hsproj : descentProj R n w deg d s ∈ K'R :=
    descent_span_proj_mem R n w deg g hghom d s hsR
  have hmk_s : mk (descentProj R n w deg d s) = 0 := by
    rwa [hmkdef, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  have hp𝔪 : p ∈ IsLocalRing.maximalIdeal R • KR :=
    (Ideal.smul_restrictScalars (IsLocalRing.maximalIdeal R) K).le hpR
  have hpproj : descentProj R n w deg d p ∈
      IsLocalRing.maximalIdeal R • (KR ⊓ shiftPiece R n w deg d) := by
    refine Submodule.smul_induction_on hp𝔪 ?_ ?_
    · intro a ha z hz
      rw [map_smul]
      refine Submodule.smul_mem_smul ha ?_
      rw [Submodule.mem_inf]
      refine ⟨descent_K_proj_mem R n w M 𝓜 m deg hm d z hz, descentProj_mem R n w deg d z⟩
    · intro y₁ y₂ hy₁ hy₂
      rw [map_add]
      exact Submodule.add_mem _ hy₁ hy₂
  have hxeq : x = descentProj R n w deg d s + descentProj R n w deg d p := by
    rw [← map_add, hxsp_eq, hxproj]
  have hmkx : mk x = mk (descentProj R n w deg d p) := by
    rw [hxeq, map_add, hmk_s, zero_add]
  have hfin : mk (descentProj R n w deg d p) ∈
      IsLocalRing.maximalIdeal R • Qd := by
    rw [hQddef, ← Submodule.map_smul'']
    exact Submodule.mem_map_of_mem hpproj
  rw [hmkx]
  exact hfin
/-- Let `J = 𝔪S`. If every `𝓜 d` is free over `R`, `m` is a homogeneous generating family of
`M` and `g_1, …, g_t` are homogeneous elements of `K = ker F` with
`K ≤ span S {g_j} ⊔ J • K`, then `K` is finitely generated. -/
lemma descent_nakayama_fg
    (R : Type*) [CommRing R] [IsLocalRing R]
    (n : ℕ) (w : Fin n → ℤ) (hw : ∀ i, 0 < w i)
    (M : Type*) [AddCommGroup M] [Module (MvPolynomial (Fin n) R) M]
    [Module R M] [IsScalarTower R (MvPolynomial (Fin n) R) M]
    (𝓜 : ℤ → Submodule R M)
    [SetLike.GradedSMul (weightedHomogeneousSubmodule R w) 𝓜]
    [DirectSum.Decomposition 𝓜]
    (hMfree : ∀ d, Module.Free R (𝓜 d))
    {r : ℕ} (m : Fin r → M) {deg : Fin r → ℤ}
    (hm : ∀ i, m i ∈ 𝓜 (deg i))
    (hspan : Submodule.span (MvPolynomial (Fin n) R) (Set.range m) = ⊤)
    {t : ℕ} (g : Fin t → (Fin r → MvPolynomial (Fin n) R))
    (hgker : ∀ j, g j ∈ LinearMap.ker (Fintype.linearCombination (MvPolynomial (Fin n) R) m))
    (hghom : ∀ j, ∃ δ : ℤ, g j ∈ shiftPiece R n w deg δ)
    (hle : LinearMap.ker (Fintype.linearCombination (MvPolynomial (Fin n) R) m) ≤
        Submodule.span (MvPolynomial (Fin n) R) (Set.range g)
          ⊔ (Ideal.map (algebraMap R (MvPolynomial (Fin n) R)) (IsLocalRing.maximalIdeal R))
              • (LinearMap.ker (Fintype.linearCombination (MvPolynomial (Fin n) R) m))) :
    (LinearMap.ker (Fintype.linearCombination (MvPolynomial (Fin n) R) m)).FG := by
  classical
  set K := LinearMap.ker (Fintype.linearCombination (MvPolynomial (Fin n) R) m)
  set K' := Submodule.span (MvPolynomial (Fin n) R) (Set.range g) with hK'def
  have hK'fg : K'.FG := Submodule.fg_span (Set.finite_range g)
  have hK'leK : K' ≤ K := by
    rw [hK'def]; exact Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact hgker j)
  suffices hKleK' : K ≤ K' by
    have hKK' : K = K' := le_antisymm hKleK' hK'leK
    rw [hKK']; exact hK'fg
  set KR := K.restrictScalars R with hKRdef
  set K'R := K'.restrictScalars R with hK'Rdef
  set mk := Submodule.mkQ K'R with hmkdef
  set Qg : ℤ → Submodule R ((Fin r → MvPolynomial (Fin n) R) ⧸ K'R) :=
    fun d => (KR ⊓ shiftPiece R n w deg d).map mk with hQgdef
  have hvanish : ∀ d, Qg d = ⊥ := by
    have hfin : ∀ d, (Qg d).FG := by
      intro d
      have : Module.Finite R (↥(KR ⊓ shiftPiece R n w deg d)) :=
        descent_Kpiece_finite R n w hw M 𝓜 hMfree m deg hm hspan d
      exact Module.Finite.iff_fg.1
        (Module.Finite.map (KR ⊓ shiftPiece R n w deg d) mk)
    obtain ⟨d₀, hd₀⟩ := descent_shiftPiece_bot_of_lt R n w hw deg
    have hbdd : ∀ d, d < d₀ → Qg d = ⊥ := by
      intro d hd
      rw [hQgdef]
      change (KR ⊓ shiftPiece R n w deg d).map mk = ⊥
      rw [hd₀ d hd, inf_bot_eq, Submodule.map_bot]
    have hnak : ∀ d, Qg d ≤ IsLocalRing.maximalIdeal R • Qg d ⊔ (⨆ e ∈ Set.Iio d, Qg e) := by
      intro d
      exact descent_smul_graded R n w M 𝓜 m deg hm g hghom hle d
    exact graded_nakayama_vanish R _ Qg hfin d₀ hbdd hnak
  have hKRimg : KR.map mk = ⊥ := by
    have hhom : KR = ⨆ d, (KR ⊓ shiftPiece R n w deg d) :=
      descent_K_homogeneous R n w M 𝓜 m deg hm
    rw [hhom, Submodule.map_iSup]
    have : ∀ d, (KR ⊓ shiftPiece R n w deg d).map mk = ⊥ := hvanish
    simp only [this, iSup_bot]
  intro x hx
  have hxR : x ∈ KR := by rwa [hKRdef, Submodule.restrictScalars_mem]
  have hmem : mk x ∈ KR.map mk := Submodule.mem_map_of_mem hxR
  rw [hKRimg, Submodule.mem_bot] at hmem
  have hxkerR : x ∈ K'R := by
    have : x ∈ LinearMap.ker mk := hmem
    rwa [hmkdef, Submodule.ker_mkQ] at this
  rw [hK'Rdef, Submodule.restrictScalars_mem] at hxkerR
  exact hxkerR

/-- If every `𝓜 d` is free over `R` and `m` is a homogeneous generating family of `M`,
the kernel of `F = Fintype.linearCombination S m : S^r → M` is finitely generated. -/
@[ega "IV 11.2.9.4" "special case"]
lemma gradedKernel_fg_descent
    (R : Type*) [CommRing R] [IsLocalRing R]
    (n : ℕ) (w : Fin n → ℤ) (hw : ∀ i, 0 < w i)
    (M : Type*) [AddCommGroup M] [Module (MvPolynomial (Fin n) R) M]
    [Module R M] [IsScalarTower R (MvPolynomial (Fin n) R) M]
    (𝓜 : ℤ → Submodule R M)
    [SetLike.GradedSMul (weightedHomogeneousSubmodule R w) 𝓜]
    [DirectSum.Decomposition 𝓜]
    [Module.Flat R M]
    (hMfree : ∀ d, Module.Free R (𝓜 d))
    {r : ℕ} (m : Fin r → M) {deg : Fin r → ℤ}
    (hm : ∀ i, m i ∈ 𝓜 (deg i))
    (hspan : Submodule.span (MvPolynomial (Fin n) R) (Set.range m) = ⊤) :
    (LinearMap.ker (Fintype.linearCombination (MvPolynomial (Fin n) R) m)).FG := by
  classical
  obtain ⟨t, g, hgker, hle⟩ := descent_exists_gens_mod_jacobson R n M m hspan
  have hDj : ∀ j, ∃ D : Finset ℤ, ∑ e ∈ D, descentProj R n w deg e (g j) = g j :=
    fun j => (descentProj_sum_eq R n w deg (g j)).imp fun _ h => h.1
  choose D hD using hDj
  let ι : Type := Σ j : Fin t, {e : ℤ // e ∈ D j}
  have : Fintype ι := by classical infer_instance
  let g'' : ι → (Fin r → MvPolynomial (Fin n) R) := fun p => descentProj R n w deg p.2.1 (g p.1)
  let eqv := (Fintype.equivFin ι).symm
  let g' : Fin (Fintype.card ι) → (Fin r → MvPolynomial (Fin n) R) := fun k => g'' (eqv k)
  have hgker' : ∀ k,
      g' k ∈ LinearMap.ker (Fintype.linearCombination (MvPolynomial (Fin n) R) m) := by
    intro k
    have hg : g (eqv k).1 ∈
        (LinearMap.ker (Fintype.linearCombination (MvPolynomial (Fin n) R) m)).restrictScalars
          R := by
      rw [Submodule.restrictScalars_mem]; exact hgker (eqv k).1
    have := descent_K_proj_mem R n w M 𝓜 m deg hm (eqv k).2.1 (g (eqv k).1) hg
    rwa [Submodule.restrictScalars_mem] at this
  have hghom' : ∀ k, ∃ δ : ℤ, g' k ∈ shiftPiece R n w deg δ :=
    fun k => ⟨(eqv k).2.1, descentProj_mem R n w deg (eqv k).2.1 (g (eqv k).1)⟩
  have hspan_le : Submodule.span (MvPolynomial (Fin n) R) (Set.range g)
      ≤ Submodule.span (MvPolynomial (Fin n) R) (Set.range g') := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, ← hD j]
    refine Submodule.sum_mem _ fun e he => ?_
    apply Submodule.subset_span
    refine ⟨eqv.symm ⟨j, ⟨e, he⟩⟩, ?_⟩
    change g'' (eqv (eqv.symm ⟨j, ⟨e, he⟩⟩)) = descentProj R n w deg e (g j)
    rw [Equiv.apply_symm_apply]
  have hle' : LinearMap.ker (Fintype.linearCombination (MvPolynomial (Fin n) R) m)
      ≤ Submodule.span (MvPolynomial (Fin n) R) (Set.range g')
        ⊔ (Ideal.map (algebraMap R (MvPolynomial (Fin n) R)) (IsLocalRing.maximalIdeal R))
            • LinearMap.ker (Fintype.linearCombination (MvPolynomial (Fin n) R) m) :=
    le_trans hle (sup_le_sup_right hspan_le _)
  exact descent_nakayama_fg R n w hw M 𝓜 hMfree m hm hspan g' hgker' hghom' hle'

/-- **The graded kernel is finitely generated.** If `m : Fin r → M` is a homogeneous
generating family of `M`, the kernel of `F = Fintype.linearCombination S m : S^r → M` is
finitely generated over `S`. -/
@[ega "IV 11.2.9.4" "special case", sga "6 VI 1.6" "partial"]
lemma gradedKernel_fg
    (R : Type*) [CommRing R] [IsLocalRing R]
    (n : ℕ) (w : Fin n → ℤ) (hw : ∀ i, 0 < w i)
    (M : Type*) [AddCommGroup M] [Module (MvPolynomial (Fin n) R) M]
    [Module R M] [IsScalarTower R (MvPolynomial (Fin n) R) M]
    (𝓜 : ℤ → Submodule R M)
    [SetLike.GradedSMul (weightedHomogeneousSubmodule R w) 𝓜]
    [DirectSum.Decomposition 𝓜]
    [Module.Finite (MvPolynomial (Fin n) R) M]
    [Module.Flat R M]
    {r : ℕ} (m : Fin r → M) {deg : Fin r → ℤ}
    (hm : ∀ i, m i ∈ 𝓜 (deg i))
    (hspan : Submodule.span (MvPolynomial (Fin n) R) (Set.range m) = ⊤) :
    (LinearMap.ker (Fintype.linearCombination (MvPolynomial (Fin n) R) m)).FG := by
  have hMfree : ∀ d, Module.Free R (𝓜 d) :=
    fun d => gradedPiece_free_of_finite R w hw M 𝓜 d
  exact gradedKernel_fg_descent R n w hw M 𝓜 hMfree m hm hspan

/-- A graded `S`-module `M` that is finite over `S` and flat over the local ring `R` admits
an `S`-linear surjection `F : S^r → M` with finitely generated kernel. -/
@[ega "IV 11.2.9.4" "special case", sga "6 VI 1.6" "partial"]
theorem exists_finitePresentation_of_graded_finite_flat
    (R : Type*) [CommRing R] [IsLocalRing R]
    (n : ℕ) (w : Fin n → ℤ) (hw : ∀ i, 0 < w i)
    (M : Type*) [AddCommGroup M] [Module (MvPolynomial (Fin n) R) M]
    [Module R M] [IsScalarTower R (MvPolynomial (Fin n) R) M]
    (𝓜 : ℤ → Submodule R M)
    [SetLike.GradedSMul (weightedHomogeneousSubmodule R w) 𝓜]
    [DirectSum.Decomposition 𝓜]
    [Module.Finite (MvPolynomial (Fin n) R) M]
    [Module.Flat R M] :
    ∃ (r : ℕ) (F : (Fin r → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R] M),
      Function.Surjective F ∧ (LinearMap.ker F).FG := by
  classical
  obtain ⟨r, m, deg, hm, hspan⟩ := exists_homogeneous_generators R (MvPolynomial (Fin n) R) M 𝓜
  refine ⟨r, Fintype.linearCombination (MvPolynomial (Fin n) R) m, ?_, ?_⟩
  · rw [← span_range_eq_top_iff_surjective_fintypeLinearCombination
          (R := MvPolynomial (Fin n) R)]
    exact hspan
  · exact gradedKernel_fg R n w hw M 𝓜 m hm hspan

/-- If a graded `S`-module `M` is finite over `S` and flat over the local ring `R`, the
kernel of every `S`-linear surjection `S^k → M` is finitely generated. -/
@[ega "IV 11.2.9.4" "special case", sga "6 VI 1.6" "partial"]
theorem ker_fg_of_finite_flat_graded
    (R : Type*) [CommRing R] [IsLocalRing R]
    (n : ℕ) (w : Fin n → ℤ) (hw : ∀ i, 0 < w i)
    (M : Type*) [AddCommGroup M] [Module (MvPolynomial (Fin n) R) M]
    [Module R M] [IsScalarTower R (MvPolynomial (Fin n) R) M]
    (𝓜 : ℤ → Submodule R M)
    [SetLike.GradedSMul (weightedHomogeneousSubmodule R w) 𝓜]
    [DirectSum.Decomposition 𝓜]
    [Module.Finite (MvPolynomial (Fin n) R) M]
    [Module.Flat R M]
    {k : ℕ} (f : (Fin k → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R] M)
    (hf : Function.Surjective f) :
    (LinearMap.ker f).FG := by
  obtain ⟨r, F, hFsurj, hFker⟩ :=
    exists_finitePresentation_of_graded_finite_flat R n w hw M 𝓜
  have hfp : Module.FinitePresentation (MvPolynomial (Fin n) R) M :=
    Module.finitePresentation_of_free_of_surjective F hFsurj hFker
  exact Module.FinitePresentation.fg_ker f hf

/-- **Stacks Tag 053C.** Let `R` be a local ring and let
`S = MvPolynomial (Fin n) R = R[x_1, ..., x_n]` be the graded polynomial algebra
with positive weights `w_i = deg(x_i) > 0`, graded by
`weightedHomogeneousSubmodule R w`.  Let `M` be a graded `S`-module, encoded by a
family of `R`-submodules `𝓜 : ℤ → Submodule R M` together with a compatible
graded scalar multiplication and a direct-sum decomposition.  If `M` is finite as
an `S`-module and flat as an `R`-module, then `M` is finitely presented as an
`S`-module. -/
@[stacks 053C, ega "IV 11.2.9.4" "special case", sga "6 VI 1.6" "partial"]
theorem finitePresentation_of_finite_flat_of_isLocalRing
    (R : Type*) [CommRing R] [IsLocalRing R]
    (n : ℕ) (w : Fin n → ℤ) (hw : ∀ i, 0 < w i)
    (M : Type*) [AddCommGroup M] [Module (MvPolynomial (Fin n) R) M]
    -- `R` acts on `M` through the structure map `R → S` compatibly
    [Module R M] [IsScalarTower R (MvPolynomial (Fin n) R) M]
    -- the grading on `M` over `ℤ`, as a family of `R`-submodules
    (𝓜 : ℤ → Submodule R M)
    [SetLike.GradedSMul (weightedHomogeneousSubmodule R w) 𝓜]
    [DirectSum.Decomposition 𝓜]
    -- `M` is finite as an `S`-module
    [Module.Finite (MvPolynomial (Fin n) R) M]
    -- `M` is flat as an `R`-module
    [Module.Flat R M] :
    Module.FinitePresentation (MvPolynomial (Fin n) R) M := by
  classical
  obtain ⟨k, f, hf⟩ := Module.Finite.exists_fin' (MvPolynomial (Fin n) R) M
  refine Module.finitePresentation_of_surjective f hf ?_
  exact ker_fg_of_finite_flat_graded R n w hw M 𝓜 f hf
