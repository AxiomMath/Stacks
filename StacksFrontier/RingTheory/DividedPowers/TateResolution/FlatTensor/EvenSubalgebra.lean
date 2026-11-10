module

public import Mathlib.Algebra.MvPolynomial.Counit
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.DividedPowers.Basic
public import Mathlib.RingTheory.DividedPowers.SubDPIdeal
public import Mathlib.RingTheory.GradedAlgebra.TensorProduct
public import Mathlib.RingTheory.RingHom.Flat
public import StacksFrontier.RingTheory.DividedPowers.Extend
public import StacksFrontier.RingTheory.DividedPowers.Ring
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.Basic

/-!
# Base change of divided powers on a differential graded algebra

Divided powers on the positive even part of a strictly graded-commutative differential graded
algebra `A` over `R` extend along an arbitrary ring homomorphism `R → R'`, together with their
compatibility with the differential. The base change is taken as `R' ⊗[R] A` with homogeneous
pieces `Submodule.baseChange R' (𝒜 i)`. The grading is homological and nonnegative.

This file contains the first part of the construction: divided powers extend along flat
base change, kernels of tensored surjections, the base change of the grading, of strict graded
commutativity and of the Leibniz rule, and the even subalgebra together with the isomorphism
`evenSubalgebra 𝒜 ⊗[R] P ≃ₐ[R] evenSubalgebra (fun i ↦ (𝒜 i).baseChange P)`. It continues in
`StacksFrontier.RingTheory.DividedPowers.TateResolution.FlatTensor.EvenDividedPowers` and
`StacksFrontier.RingTheory.DividedPowers.TateResolution.FlatTensor.DividedPowerStructure`, which
proves the main result.

## Main results

* `DividedPowers.TateResolution.exists_dividedPowerStructure_baseChange`: the base-changed
  differential graded algebra carries divided powers compatible with the base-changed
  differential, and the canonical map `A → R' ⊗[R] A` preserves every divided power:
  `γ'ₙ (1 ⊗ₜ x) = 1 ⊗ₜ γₙ x`.

## References

* [Stacks Project, Tag 09PL](https://stacks.math.columbia.edu/tag/09PL)
-/

@[expose] public section

namespace DividedPowers.TateResolution

open TensorProduct

universe u v w x y

private theorem dividedPowers_extends_to_flatTensor
    {R : Type u} {B : Type v} {P : Type w}
    [CommRing R] [CommRing B] [CommRing P] [Algebra R B] [Algebra R P]
    [Module.Flat R P] (I : Ideal B) (γ : _root_.DividedPowers I) :
    ∃ δ : _root_.DividedPowers
        (I.map (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[R] P)),
      _root_.DividedPowers.IsDPMorphism γ δ
        (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[R] P) := by
  let D : DividedPowerRing := ⟨B, I, γ⟩
  have hflat :
      (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[R] P).Flat := by
    change (algebraMap B (B ⊗[R] P)).Flat
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  exact
    DividedPowerRing.dividedPowers_extends_of_map_eq_bot_or_isPrincipal_or_flat
      D _ (Or.inr (Or.inr hflat))

/-- Elements of `I` map to `I.map includeLeftRingHom` under `x ↦ x ⊗ₜ 1`. -/
private theorem tmul_one_mem_map_includeLeft
    {R : Type u} {B : Type v} {P : Type w}
    [CommRing R] [CommRing B] [CommRing P] [Algebra R B] [Algebra R P]
    {I : Ideal B} {x : B} (hx : x ∈ I) :
    (x ⊗ₜ[R] (1 : P)) ∈
      I.map (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[R] P) :=
  Ideal.mem_map_of_mem (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[R] P) hx

private theorem dividedPowers_flatTensor_dpow_tmul
    {R : Type u} {B : Type v} {P : Type w}
    [CommRing R] [CommRing B] [CommRing P] [Algebra R B] [Algebra R P]
    (I : Ideal B) (γ : _root_.DividedPowers I)
    (δ : _root_.DividedPowers
      (I.map (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[R] P)))
    (hδ : _root_.DividedPowers.IsDPMorphism γ δ
      (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[R] P))
    (n : ℕ) (x : B) (hx : x ∈ I) (p : P) :
    δ.dpow n (x ⊗ₜ[R] p) =
      (1 ⊗ₜ[R] p) ^ n * (γ.dpow n x ⊗ₜ[R] (1 : P)) := by
  have htm : x ⊗ₜ[R] p =
      (1 ⊗ₜ[R] p) * (x ⊗ₜ[R] (1 : P)) := by
    simp [Algebra.TensorProduct.tmul_mul_tmul, mul_comm]
  rw [htm, δ.dpow_mul (tmul_one_mem_map_includeLeft hx)]
  congr 1
  simpa only [Algebra.TensorProduct.includeLeftRingHom_apply] using
    (hδ.map_dpow (n := n) hx).symm

private theorem ker_lTensor_of_surjective
    {R : Type u} {B : Type v} {P : Type x} {Q : Type y}
    [CommRing R] [AddCommGroup B] [Module R B]
    [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    (q : P →ₗ[R] Q) (hq : Function.Surjective q) :
    (LinearMap.lTensor B q).ker =
      (LinearMap.lTensor B q.ker.subtype).range :=
  LinearMap.exact_iff.mp (lTensor_exact B (LinearMap.exact_subtype_ker_map q) hq)

private theorem ker_lTensor_inter_range_of_split
    {R : Type u} {N : Type v} {M : Type w} {P : Type x} {Q : Type y}
    [CommRing R] [AddCommGroup N] [Module R N] [AddCommGroup M] [Module R M]
    [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    (i : N →ₗ[R] M) (r : M →ₗ[R] N) (hri : r.comp i = LinearMap.id)
    (q : P →ₗ[R] Q) (hq : Function.Surjective q) :
    (LinearMap.lTensor M q).ker ⊓ (LinearMap.rTensor P i).range =
      ((LinearMap.rTensor P i).comp (LinearMap.lTensor N q.ker.subtype)).range := by
  have hinj : Function.Injective (LinearMap.rTensor Q i) := by
    intro a b hab
    have hh := congrArg (LinearMap.rTensor Q r) hab
    simpa only [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, hri,
      LinearMap.rTensor_id, LinearMap.id_apply] using hh
  have hcomm : (LinearMap.lTensor M q).comp (LinearMap.rTensor P i) =
      (LinearMap.rTensor Q i).comp (LinearMap.lTensor N q) := by
    rw [LinearMap.lTensor_comp_rTensor, LinearMap.rTensor_comp_lTensor]
  apply le_antisymm
  · intro z hz
    obtain ⟨hzker, y, rfl⟩ := hz
    have hzero : (LinearMap.lTensor N q) y = 0 := by
      apply hinj
      have hh : (LinearMap.rTensor Q i) ((LinearMap.lTensor N q) y) = 0 := by
        rw [← LinearMap.comp_apply, ← hcomm, LinearMap.comp_apply]
        exact LinearMap.mem_ker.mp hzker
      simpa using hh
    have hy : y ∈ (LinearMap.lTensor N q).ker := by simpa using hzero
    rw [ker_lTensor_of_surjective q hq] at hy
    obtain ⟨t, rfl⟩ := hy
    exact ⟨t, rfl⟩
  · rintro z ⟨t, rfl⟩
    refine ⟨?_, _, rfl⟩
    change (LinearMap.lTensor M q)
        ((LinearMap.rTensor P i ∘ₗ LinearMap.lTensor N q.ker.subtype) t) = 0
    calc
      _ = (LinearMap.rTensor Q i)
          ((LinearMap.lTensor N q)
            ((LinearMap.lTensor N q.ker.subtype) t)) := by
              simpa only [LinearMap.comp_apply] using
                congrArg (fun f : N ⊗[R] P →ₗ[R] M ⊗[R] Q =>
                  f ((LinearMap.lTensor N q.ker.subtype) t)) hcomm
      _ = 0 := by
        have hzero' : (LinearMap.lTensor N q)
            ((LinearMap.lTensor N q.ker.subtype) t) = 0 := by
          change ((LinearMap.lTensor N q).comp
            (LinearMap.lTensor N q.ker.subtype)) t = 0
          rw [← LinearMap.lTensor_comp, LinearMap.comp_ker_subtype]
          simp
        rw [hzero']
        simp

private theorem tensorIdealKernel_range_le_mul
    {R : Type u} {B : Type v} {P : Type w} {Q : Type x}
    [CommRing R] [CommRing B] [CommRing P] [CommRing Q]
    [Algebra R B] [Algebra R P] [Algebra R Q]
    (I : Ideal B) (q : P →ₐ[R] Q) :
    ((LinearMap.rTensor P (Submodule.restrictScalars R I).subtype).comp
      (LinearMap.lTensor (Submodule.restrictScalars R I)
        q.toLinearMap.ker.subtype)).range ≤
      Submodule.restrictScalars R
        (I.map (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[R] P) *
          (RingHom.ker q.toRingHom).map
            (Algebra.TensorProduct.includeRight : P →ₐ[R] B ⊗[R] P)) := by
  intro z hz
  obtain ⟨t, rfl⟩ := hz
  induction t using TensorProduct.inductionOn with
  | tmul i f =>
      have hf : ((1 : B) ⊗ₜ[R] (f : P)) ∈
          (RingHom.ker q.toRingHom).map
            (Algebra.TensorProduct.includeRight : P →ₐ[R] B ⊗[R] P) := by
        change (Algebra.TensorProduct.includeRight : P →ₐ[R] B ⊗[R] P) f ∈ _
        exact Ideal.mem_map_of_mem _ f.property
      change ((i : B) ⊗ₜ[R] (f : P)) ∈ _
      rw [show ((i : B) ⊗ₜ[R] (f : P)) =
          ((i : B) ⊗ₜ[R] (1 : P)) * ((1 : B) ⊗ₜ[R] (f : P)) by
        simp [Algebra.TensorProduct.tmul_mul_tmul]]
      exact Ideal.mul_mem_mul (tmul_one_mem_map_includeLeft i.property) hf
  | add a b ha hb =>
      simpa only [map_add] using
        (Submodule.restrictScalars R
          (I.map (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[R] P) *
            (RingHom.ker q.toRingHom).map
              (Algebra.TensorProduct.includeRight : P →ₐ[R] B ⊗[R] P))).add_mem ha hb

private theorem baseChange_mapsTo
    {R : Type u} {R' : Type v} {A : Type w}
    [CommRing R] [CommRing R'] [Ring A] [Algebra R R'] [Algebra R A]
    (f : A →ₗ[R] A) (p q : Submodule R A)
    (h : ∀ x : A, x ∈ p → f x ∈ q) :
    ∀ x : R' ⊗[R] A, x ∈ p.baseChange R' →
      f.baseChange R' x ∈ q.baseChange R' := by
  intro x hx
  rw [Submodule.baseChange_eq_span] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
      rcases hx with ⟨a, ha, rfl⟩
      simpa only [TensorProduct.mk_apply, LinearMap.baseChange_tmul] using
        (Submodule.tmul_mem_baseChange_of_mem (A := R') 1 (h a ha))
  | zero => simp
  | add x y hx hy ihx ihy => simpa using (q.baseChange R').add_mem ihx ihy
  | smul a x hx ih => simpa using (q.baseChange R').smul_mem a ih

private theorem baseChange_iSup
    {R : Type u} {R' : Type v} {A : Type w}
    [CommRing R] [CommRing R'] [Ring A] [Algebra R R'] [Algebra R A]
    {ι : Type*} (p : ι → Submodule R A) :
    (⨆ i, p i).baseChange R' = ⨆ i, (p i).baseChange R' := by
  have h (i : ι) : (p i).baseChange R' =
      Submodule.span R' (TensorProduct.mk R R' A 1 '' (p i : Set A)) := by
    conv_lhs => rw [← (Submodule.span_eq (R := R) (p := p i))]
    exact Submodule.baseChange_span (R := R) (A := R') (M := A) (p i : Set A)
  calc
    (⨆ i, p i).baseChange R' =
        Submodule.span R' (TensorProduct.mk R R' A 1 '' ⋃ i, (p i : Set A)) := by
          rw [Submodule.iSup_eq_span, Submodule.baseChange_span]
    _ = ⨆ i, Submodule.span R' (TensorProduct.mk R R' A 1 '' (p i : Set A)) := by
      rw [Set.image_iUnion, Submodule.span_iUnion]
    _ = ⨆ i, (p i).baseChange R' := by simp only [← h]

private theorem evenPart_baseChange
    {R : Type u} {R' : Type v} {A : Type w}
    [CommRing R] [CommRing R'] [Ring A] [Algebra R R'] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) :
    evenPart (fun i ↦ (𝒜 i).baseChange R') =
      (evenPart 𝒜).baseChange R' :=
  (baseChange_iSup (R' := R') (fun d ↦ 𝒜 (2 * d))).symm

theorem positiveEvenPart_baseChange
    {R : Type u} {R' : Type v} {A : Type w}
    [CommRing R] [CommRing R'] [Ring A] [Algebra R R'] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) :
    positiveEvenPart (fun i ↦ (𝒜 i).baseChange R') =
      (positiveEvenPart 𝒜).baseChange R' :=
  (baseChange_iSup (R' := R') (fun d ↦ 𝒜 (2 * (d + 1)))).symm

private theorem graded_comm_baseChange
    {R : Type u} {R' : Type v} {A : Type w}
    [CommRing R] [CommRing R'] [Ring A] [Algebra R R'] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
    {i j : ℕ} {x y : R' ⊗[R] A}
    (hx : x ∈ (𝒜 i).baseChange R') (hy : y ∈ (𝒜 j).baseChange R') :
    x * y = (-1 : R') ^ (i * j) • (y * x) := by
  rw [Submodule.baseChange_eq_span] at hx hy
  induction hx using Submodule.span_induction with
  | mem x hx =>
      rcases hx with ⟨a, ha, rfl⟩
      induction hy using Submodule.span_induction with
      | mem y hy =>
          rcases hy with ⟨b, hb, rfl⟩
          simp only [TensorProduct.mk_apply, Algebra.TensorProduct.tmul_mul_tmul,
            one_mul]
          rw [IsStrictlyGradedComm.graded_comm ha hb]
          rw [TensorProduct.tmul_smul]
          simp [Algebra.smul_def]
      | zero => simp
      | add y z hy hz ihy ihz =>
          simp only [mul_add, add_mul, smul_add, ihy, ihz]
      | smul c y hy ih =>
          simp only [TensorProduct.mk_apply] at ih
          simp only [TensorProduct.mk_apply]
          calc
            _ = c • ((1 ⊗ₜ[R] a) * y) := by rw [mul_smul_comm]
            _ = c • ((-1 : R') ^ (i * j) • (y * (1 ⊗ₜ[R] a))) := by rw [ih]
            _ = (-1 : R') ^ (i * j) • ((c • y) * (1 ⊗ₜ[R] a)) := by
              rw [smul_comm, smul_mul_assoc]
  | zero => simp
  | add x z hx hz ihx ihz =>
      simp only [add_mul, mul_add, smul_add, ihx, ihz]
  | smul c x hx ih =>
      calc
        _ = c • (x * y) := by rw [smul_mul_assoc]
        _ = c • ((-1 : R') ^ (i * j) • (y * x)) := by rw [ih]
        _ = (-1 : R') ^ (i * j) • (y * (c • x)) := by
          rw [smul_comm, mul_smul_comm]

private theorem odd_sq_zero_baseChange
    {R : Type u} {R' : Type v} {A : Type w}
    [CommRing R] [CommRing R'] [Ring A] [Algebra R R'] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
    {d : ℕ} {x : R' ⊗[R] A}
    (hx : x ∈ (𝒜 (2 * d + 1)).baseChange R') : x ^ 2 = 0 := by
  rw [Submodule.baseChange_eq_span] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
      rcases hx with ⟨a, ha, rfl⟩
      simp only [TensorProduct.mk_apply, pow_two,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      rw [← pow_two, IsStrictlyGradedComm.odd_sq_zero ha]
      simp
  | zero => simp
  | add x y hx hy ihx ihy =>
      have hdodd : Odd (2 * d + 1) := ⟨d, by lia⟩
      have hodd : Odd ((2 * d + 1) * (2 * d + 1)) := hdodd.mul hdodd
      have hx' : x ∈ (𝒜 (2 * d + 1)).baseChange R' := by
        rwa [Submodule.baseChange_eq_span]
      have hy' : y ∈ (𝒜 (2 * d + 1)).baseChange R' := by
        rwa [Submodule.baseChange_eq_span]
      have hxy : x * y = -(y * x) := by
        simpa only [hodd.neg_one_pow, neg_one_smul] using
          (graded_comm_baseChange 𝒜 hx' hy')
      calc
        (x + y) ^ 2 = x * x + y * x + x * y + y * y := by
          simp [pow_two, add_mul, mul_add, add_assoc]
        _ = 0 := by rw [← pow_two, ihx, ← pow_two, ihy, hxy]; abel
  | smul c x hx ih =>
      calc
        (c • x) ^ 2 = c • (c • x ^ 2) := by
          simp only [pow_two, smul_mul_assoc, mul_smul_comm]
        _ = 0 := by simp [ih]

private theorem strictlyGradedComm_baseChange
    {R : Type u} {R' : Type v} {A : Type w}
    [CommRing R] [CommRing R'] [Ring A] [Algebra R R'] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜] :
    IsStrictlyGradedComm (fun i ↦ (𝒜 i).baseChange R') where
  graded_comm := graded_comm_baseChange 𝒜
  odd_sq_zero := odd_sq_zero_baseChange 𝒜

private theorem baseChange_zero_on
    {R : Type u} {R' : Type v} {A : Type w}
    [CommRing R] [CommRing R'] [Ring A] [Algebra R R'] [Algebra R A]
    (f : A →ₗ[R] A) (p : Submodule R A)
    (h : ∀ x : A, x ∈ p → f x = 0) :
    ∀ x : R' ⊗[R] A, x ∈ p.baseChange R' → f.baseChange R' x = 0 := by
  intro x hx
  have hy := baseChange_mapsTo (R' := R') f p ⊥
    (fun a ha ↦ by simpa using h a ha) x hx
  simpa only [Submodule.baseChange_bot, Submodule.mem_bot] using hy

private theorem one_tmul_smul
    {R : Type u} {R' : Type v} {A : Type w}
    [CommRing R] [CommRing R'] [Ring A] [Algebra R R'] [Algebra R A]
    (r : R) (a : A) :
    (1 : R') ⊗ₜ[R] (r • a) = (algebraMap R R' r) • ((1 : R') ⊗ₜ[R] a) := by
  rw [TensorProduct.tmul_smul]
  simp [Algebra.smul_def]

private theorem evenPart_mul_mem
    {R : Type u} {A : Type w}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    {x y : A} (hx : x ∈ evenPart 𝒜) (hy : y ∈ evenPart 𝒜) :
    x * y ∈ evenPart 𝒜 := by
  change x ∈ (⨆ d : ℕ, 𝒜 (2 * d)) at hx
  change y ∈ (⨆ d : ℕ, 𝒜 (2 * d)) at hy
  rw [Submodule.iSup_eq_span] at hx hy
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨d, hd⟩ := Set.mem_iUnion.mp hx
      induction hy using Submodule.span_induction with
      | mem y hy =>
          obtain ⟨e, he⟩ := Set.mem_iUnion.mp hy
          exact Submodule.mem_iSup_of_mem (d + e)
            (by
              have hdeg : 2 * d + 2 * e = 2 * (d + e) := by lia
              simpa only [hdeg] using SetLike.mul_mem_graded hd he)
      | zero => simp
      | add y z hy hz ihy ihz => simpa only [mul_add] using (evenPart 𝒜).add_mem ihy ihz
      | smul r y hy ih =>
          simpa only [mul_smul_comm] using (evenPart 𝒜).smul_mem r ih
  | zero => simp
  | add x z hx hz ihx ihz => simpa only [add_mul] using (evenPart 𝒜).add_mem ihx ihz
  | smul r x hx ih =>
      simpa only [smul_mul_assoc] using (evenPart 𝒜).smul_mem r ih

private theorem proj_zero_of_positive
    {R : Type u} {A : Type w}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] :
    ∀ x : A, x ∈ positiveEvenPart 𝒜 → (GradedAlgebra.proj 𝒜 0) x = 0 := by
  intro x hx
  change x ∈ (⨆ d : ℕ, 𝒜 (2 * (d + 1))) at hx
  have hle : (⨆ d : ℕ, 𝒜 (2 * (d + 1))) ≤
      (GradedAlgebra.proj 𝒜 0).ker := by
    apply iSup_le
    intro d x hx
    rw [LinearMap.mem_ker, GradedAlgebra.proj_apply]
    exact DirectSum.decompose_of_mem_ne 𝒜 hx (by lia)
  exact LinearMap.mem_ker.mp (hle hx)

private theorem sub_proj_zero_mem_positive
    {R : Type u} {A : Type w}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] :
    ∀ x : A, x ∈ evenPart 𝒜 →
      x - (GradedAlgebra.proj 𝒜 0) x ∈ positiveEvenPart 𝒜 := by
  intro x hx
  change x ∈ (⨆ d : ℕ, 𝒜 (2 * d)) at hx
  rw [Submodule.iSup_eq_span] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨d, hd⟩ := Set.mem_iUnion.mp hx
      cases d with
      | zero =>
          have hproj : (GradedAlgebra.proj 𝒜 0) x = x := by
            simpa only [GradedAlgebra.proj_apply] using
              (DirectSum.decompose_of_mem_same 𝒜 (by simpa using hd))
          simp [hproj]
      | succ d =>
          have hproj : (GradedAlgebra.proj 𝒜 0) x = 0 := by
            rw [GradedAlgebra.proj_apply]
            exact DirectSum.decompose_of_mem_ne 𝒜 hd (by lia)
          simpa only [hproj, sub_zero] using
            (Submodule.mem_iSup_of_mem d (by simpa using hd) :
              x ∈ positiveEvenPart 𝒜)
  | zero => simp
  | add x y hx hy ihx ihy =>
      simpa only [map_add, add_sub_add_comm] using
        (positiveEvenPart 𝒜).add_mem ihx ihy
  | smul r x hx ih =>
      simpa only [map_smul, smul_sub] using
        (positiveEvenPart 𝒜).smul_mem r ih

private theorem filtered_even_mem
    {R : Type u} {A : Type w} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (s : DirectSum ℕ (fun i => 𝒜 i)) :
    ((DirectSum.decomposeLinearEquiv 𝒜).symm
      (DFinsupp.filter Even s) : A) ∈ evenPart 𝒜 := by
  induction s using DirectSum.induction_on with
  | zero => simp
  | of i a =>
      change ((DirectSum.decomposeLinearEquiv 𝒜).symm
        (DFinsupp.filter Even (DFinsupp.single i a)) : A) ∈ evenPart 𝒜
      by_cases hi : Even i
      · obtain ⟨d, hd⟩ := hi
        have hi' : Even i := ⟨d, hd⟩
        rw [DFinsupp.filter_single_pos (β := fun j : ℕ => 𝒜 j) (p := Even) i a hi']
        change ((DirectSum.decomposeLinearEquiv 𝒜).symm
          ((DirectSum.lof R ℕ (fun j => 𝒜 j) i) a) : A) ∈ evenPart 𝒜
        rw [DirectSum.decomposeLinearEquiv_symm_lof]
        exact Submodule.mem_iSup_of_mem d (by simpa [hd, two_mul] using a.property)
      · rw [DFinsupp.filter_single_neg (β := fun j : ℕ => 𝒜 j) (p := Even) i a hi]
        simp
  | add s t hs ht =>
      rw [DFinsupp.filter_add]
      simp only [map_add]
      exact (evenPart 𝒜).add_mem hs ht

private def evenProjection
    {R : Type u} {A : Type w} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] :
    A →ₗ[R] evenPart 𝒜 := by
  let F : A →ₗ[R] A :=
    (DirectSum.decomposeLinearEquiv 𝒜).symm.toLinearMap.comp
      ((DFinsupp.filterLinearMap R (fun i => 𝒜 i) Even).comp
        (DirectSum.decomposeLinearEquiv 𝒜).toLinearMap)
  exact F.codRestrict (evenPart 𝒜) (fun x =>
    filtered_even_mem 𝒜 ((DirectSum.decomposeLinearEquiv 𝒜) x))

private theorem evenProjection_of_mem_grade
    {R : Type u} {A : Type w} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    {i : ℕ} {a : A} (ha : a ∈ 𝒜 i) (hi : Even i) :
    (evenProjection 𝒜 a : A) = a := by
  unfold evenProjection
  change (DirectSum.decomposeLinearEquiv 𝒜).symm
    (DFinsupp.filter Even ((DirectSum.decomposeLinearEquiv 𝒜) a)) = a
  rw [show a = (⟨a, ha⟩ : 𝒜 i) from rfl]
  rw [DirectSum.decomposeLinearEquiv_apply_coe]
  change (DirectSum.decomposeLinearEquiv 𝒜).symm
    (DFinsupp.filter Even (DFinsupp.single i ⟨a, ha⟩)) = a
  rw [DFinsupp.filter_single_pos (β := fun j : ℕ => 𝒜 j) (p := Even) i ⟨a, ha⟩ hi]
  change (DirectSum.decomposeLinearEquiv 𝒜).symm
    ((DirectSum.lof R ℕ (fun j => 𝒜 j) i) ⟨a, ha⟩) = a
  exact DirectSum.decomposeLinearEquiv_symm_lof 𝒜 i ⟨a, ha⟩

private theorem evenProjection_mem_even
    {R : Type u} {A : Type w} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (a : A) (ha : a ∈ evenPart 𝒜) : (evenProjection 𝒜 a : A) = a := by
  change a ∈ (⨆ d : ℕ, 𝒜 (2 * d)) at ha
  rw [Submodule.iSup_eq_span] at ha
  induction ha using Submodule.span_induction with
  | mem a ha =>
      obtain ⟨d, hd⟩ := Set.mem_iUnion.mp ha
      exact evenProjection_of_mem_grade 𝒜 hd ⟨d, by lia⟩
  | zero => simp
  | add a b ha hb iha ihb =>
      simpa only [map_add, Submodule.coe_add] using congrArg₂ (· + ·) iha ihb
  | smul r a ha ih =>
      simpa only [map_smul, SetLike.val_smul, RingHom.id_apply] using
        congrArg (fun z : A => r • z) ih

private def evenSubalgebra
    {R : Type u} {A : Type w}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] : Subalgebra R A where
  carrier := evenPart 𝒜
  add_mem' := (evenPart 𝒜).add_mem
  mul_mem' := evenPart_mul_mem 𝒜
  algebraMap_mem' r := by
    have hone : (1 : A) ∈ evenPart 𝒜 :=
      Submodule.mem_iSup_of_mem 0 (by simpa using SetLike.one_mem_graded 𝒜)
    change algebraMap R A r ∈ evenPart 𝒜
    rw [Algebra.algebraMap_eq_smul_one]
    exact (evenPart 𝒜).smul_mem r hone

private instance evenSubalgebraCommRing
    {R : Type u} {A : Type w}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜] :
    CommRing (evenSubalgebra 𝒜) :=
  { (inferInstance : Ring (evenSubalgebra 𝒜)) with
    mul_comm := fun x y ↦ Subtype.ext (evenPart_mul_comm 𝒜 x.property (y : A)) }

private def evenSubalgebraProjection
    {R : Type u} {A : Type w}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] :
    A →ₗ[R] evenSubalgebra 𝒜 where
  toFun x := ⟨(evenProjection 𝒜 x : A), (evenProjection 𝒜 x).property⟩
  map_add' x y := by
    apply Subtype.ext
    change (evenProjection 𝒜 (x + y) : A) =
      (evenProjection 𝒜 x : A) + (evenProjection 𝒜 y : A)
    simp
  map_smul' r x := by
    apply Subtype.ext
    change (evenProjection 𝒜 (r • x) : A) = r • (evenProjection 𝒜 x : A)
    simp

private theorem evenSubalgebraProjection_coe
    {R : Type u} {A : Type w}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (b : evenSubalgebra 𝒜) : evenSubalgebraProjection 𝒜 b = b :=
  Subtype.ext (evenProjection_mem_even 𝒜 b b.property)

private def evenSubalgebraTensorHom
    {R : Type u} {A : Type w} {P : Type v}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    [IsStrictlyGradedComm 𝒜]
    [CommRing P] [Algebra R P] :
    let 𝒜' : ℕ → Submodule P (P ⊗[R] A) := fun i => (𝒜 i).baseChange P
    evenSubalgebra 𝒜 ⊗[R] P →ₐ[R] evenSubalgebra (R := P) 𝒜' := by
  let 𝒜' : ℕ → Submodule P (P ⊗[R] A) := fun i => (𝒜 i).baseChange P
  letI : IsStrictlyGradedComm 𝒜' := strictlyGradedComm_baseChange 𝒜
  let Φ : evenSubalgebra 𝒜 ⊗[R] P →ₐ[R] P ⊗[R] A :=
    (Algebra.TensorProduct.comm R A P).toAlgHom.comp
      (Algebra.TensorProduct.map (Subalgebra.val (evenSubalgebra 𝒜))
        (AlgHom.id R P))
  refine Φ.codRestrict ((evenSubalgebra (R := P) 𝒜').restrictScalars R) ?_
  intro z
  change Φ z ∈ evenPart 𝒜'
  induction z using TensorProduct.inductionOn with
  | tmul b p =>
      have h : p ⊗ₜ[R] (b : A) ∈ (evenPart 𝒜).baseChange P :=
        Submodule.tmul_mem_baseChange_of_mem p b.property
      rw [evenPart_baseChange]
      simpa [Φ, Algebra.TensorProduct.map_tmul,
        Algebra.TensorProduct.comm_tmul] using h
  | add z t hz ht =>
      simpa only [map_add] using (evenPart 𝒜').add_mem hz ht

private def evenTensorRetract
    {R : Type u} {A : Type w} {P : Type v}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    [CommRing P] [Algebra R P] :
    P ⊗[R] A →ₗ[R] evenSubalgebra 𝒜 ⊗[R] P :=
  (TensorProduct.comm R P (evenSubalgebra 𝒜)).toLinearMap.comp
    (TensorProduct.map LinearMap.id (evenSubalgebraProjection 𝒜))

private theorem evenTensorRetract_tmul
    {R : Type u} {A : Type w} {P : Type v}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    [CommRing P] [Algebra R P] (p : P) (a : A) :
    evenTensorRetract 𝒜 (p ⊗ₜ[R] a) = evenSubalgebraProjection 𝒜 a ⊗ₜ[R] p := by
  simp [evenTensorRetract]

private theorem evenSubalgebraTensorHom_tmul
    {R : Type u} {A : Type w} {P : Type v}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    [IsStrictlyGradedComm 𝒜]
    [CommRing P] [Algebra R P]
    (b : evenSubalgebra 𝒜) (p : P) :
    ((evenSubalgebraTensorHom 𝒜 (b ⊗ₜ[R] p) :
      evenSubalgebra (R := P) (fun i => (𝒜 i).baseChange P)) : P ⊗[R] A) =
      p ⊗ₜ[R] (b : A) := by
  unfold evenSubalgebraTensorHom
  change (Algebra.TensorProduct.comm R A P)
    ((Algebra.TensorProduct.map (Subalgebra.val (evenSubalgebra 𝒜))
      (AlgHom.id R P)) (b ⊗ₜ[R] p)) = p ⊗ₜ[R] (b : A)
  simp only [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.comm_tmul,
    AlgHom.id_apply, Subalgebra.val_apply]

private theorem evenTensorRetract_tensorHom
    {R : Type u} {A : Type w} {P : Type v}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    [IsStrictlyGradedComm 𝒜]
    [CommRing P] [Algebra R P]
    (z : evenSubalgebra 𝒜 ⊗[R] P) :
    evenTensorRetract 𝒜 ((evenSubalgebraTensorHom 𝒜 z :
      evenSubalgebra (R := P) (fun i => (𝒜 i).baseChange P)) : P ⊗[R] A) = z := by
  induction z using TensorProduct.inductionOn with
  | tmul b p =>
      rw [evenSubalgebraTensorHom_tmul]
      simp [evenTensorRetract_tmul, evenSubalgebraProjection_coe]
  | add a b ha hb =>
      simpa only [map_add, Subalgebra.coe_add] using congrArg₂ (· + ·) ha hb

private theorem evenTensorHom_retract_of_mem
    {R : Type u} {A : Type w} {P : Type v}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    [IsStrictlyGradedComm 𝒜]
    [CommRing P] [Algebra R P]
  (y : P ⊗[R] A) (hy : y ∈ (evenPart 𝒜).baseChange P) :
    ((evenSubalgebraTensorHom 𝒜 (evenTensorRetract 𝒜 y) :
      evenSubalgebra (R := P) (fun i => (𝒜 i).baseChange P)) : P ⊗[R] A) = y := by
  obtain ⟨t, ht⟩ := Submodule.toBaseChange_surjective' P (evenPart 𝒜) hy
  suffices h : ∀ t : P ⊗[R] (evenPart 𝒜),
      ((evenSubalgebraTensorHom 𝒜
        (evenTensorRetract 𝒜 ((Submodule.toBaseChange P (evenPart 𝒜) t :
          (evenPart 𝒜).baseChange P) : P ⊗[R] A)) :
          evenSubalgebra (R := P) (fun i => (𝒜 i).baseChange P)) : P ⊗[R] A) =
        ((Submodule.toBaseChange P (evenPart 𝒜) t :
          (evenPart 𝒜).baseChange P) : P ⊗[R] A) by
    simpa only [ht] using h t
  intro t
  induction t using TensorProduct.inductionOn with
  | tmul p b =>
      rw [Submodule.coe_toBaseChange_tmul]
      have hb : (evenSubalgebraProjection 𝒜 (b : A) : evenSubalgebra 𝒜) = ⟨b, b.property⟩ :=
        evenSubalgebraProjection_coe 𝒜 ⟨b, b.property⟩
      rw [evenTensorRetract_tmul, hb, evenSubalgebraTensorHom_tmul]
  | add a b ha hb =>
      simpa only [map_add, Submodule.coe_add, Subalgebra.coe_add] using
        congrArg₂ (· + ·) ha hb

private theorem evenSubalgebraTensorHom_bijective
    {R : Type u} {A : Type w} {P : Type v}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    [IsStrictlyGradedComm 𝒜]
    [CommRing P] [Algebra R P] :
    Function.Bijective (evenSubalgebraTensorHom (P := P) 𝒜) := by
  constructor
  · intro x y h
    have hv := congrArg (fun z : evenSubalgebra (R := P)
      (fun i => (𝒜 i).baseChange P) => (z : P ⊗[R] A)) h
    have hr := congrArg (evenTensorRetract 𝒜) hv
    simpa only [evenTensorRetract_tensorHom] using hr
  · intro y
    have hy : (y : P ⊗[R] A) ∈ (evenPart 𝒜).baseChange P := by
      rw [← evenPart_baseChange]
      exact y.property
    exact ⟨evenTensorRetract 𝒜 y, Subtype.ext (evenTensorHom_retract_of_mem (P := P) 𝒜 y hy)⟩

private noncomputable def evenSubalgebraTensorEquiv
    {R : Type u} {A : Type w} {P : Type v}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    [IsStrictlyGradedComm 𝒜]
    [CommRing P] [Algebra R P] :
    let 𝒜' : ℕ → Submodule P (P ⊗[R] A) := fun i => (𝒜 i).baseChange P
    evenSubalgebra 𝒜 ⊗[R] P ≃ₐ[R] evenSubalgebra (R := P) 𝒜' :=
  AlgEquiv.ofBijective (evenSubalgebraTensorHom (P := P) 𝒜)
    (evenSubalgebraTensorHom_bijective (P := P) 𝒜)

private theorem differential_mul_baseChange
    {R : Type u} {R' : Type v} {A : Type w}
    [CommRing R] [CommRing R'] [Ring A] [Algebra R R'] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (d : A →ₗ[R] A)
    (h : ∀ (i j : ℕ) (x y : A), x ∈ 𝒜 i → y ∈ 𝒜 j →
      d (x * y) = d x * y + (-1 : R) ^ i • (x * d y))
    {i j : ℕ} {x y : R' ⊗[R] A}
    (hx : x ∈ (𝒜 i).baseChange R') (hy : y ∈ (𝒜 j).baseChange R') :
    (d.baseChange R') (x * y) = (d.baseChange R') x * y +
      (-1 : R') ^ i • (x * (d.baseChange R') y) := by
  rw [Submodule.baseChange_eq_span] at hx hy
  induction hx using Submodule.span_induction with
  | mem x hx =>
      rcases hx with ⟨a, ha, rfl⟩
      induction hy using Submodule.span_induction with
      | mem y hy =>
          rcases hy with ⟨b, hb, rfl⟩
          simp only [TensorProduct.mk_apply, Algebra.TensorProduct.tmul_mul_tmul,
            one_mul, LinearMap.baseChange_tmul]
          rw [h i j a b ha hb, TensorProduct.tmul_add,
            one_tmul_smul]
          simp
      | zero => simp
      | add y z hy hz ihy ihz =>
          simp only [mul_add, map_add, smul_add, ihy, ihz]
          abel
      | smul c y hy ih =>
          simp only [TensorProduct.mk_apply] at ih ⊢
          calc
            _ = c • (d.baseChange R') ((1 ⊗ₜ[R] a) * y) := by
              rw [mul_smul_comm, map_smul]
            _ = c • ((d.baseChange R') (1 ⊗ₜ[R] a) * y +
                (-1 : R') ^ i • ((1 ⊗ₜ[R] a) * (d.baseChange R') y)) := by rw [ih]
            _ = _ := by
              simp only [smul_add, mul_smul_comm, map_smul]
              congr 1
              exact smul_comm c ((-1 : R') ^ i) _
  | zero => simp
  | add x z hx hz ihx ihz =>
      simp only [add_mul, map_add, smul_add, ihx, ihz]
      abel
  | smul c x hx ih =>
      calc
        _ = c • (d.baseChange R') (x * y) := by
          rw [smul_mul_assoc, map_smul]
        _ = c • ((d.baseChange R') x * y +
            (-1 : R') ^ i • (x * (d.baseChange R') y)) := by rw [ih]
        _ = _ := by
          simp only [smul_add, smul_mul_assoc, map_smul]
          congr 1
          exact smul_comm c ((-1 : R') ^ i) _

private theorem differential_dpow_baseChange_tmul
    {R : Type u} {R' : Type v} {A : Type w}
    [CommRing R] [CommRing R'] [Ring A] [Algebra R R'] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
    (γ : DividedPowerStructure 𝒜) (d : A →ₗ[R] A)
    [IsCompatibleWithDifferential γ d]
    [IsStrictlyGradedComm (fun i ↦ (𝒜 i).baseChange R')]
    (γ' : DividedPowerStructure (fun i ↦ (𝒜 i).baseChange R'))
    (hγ : ∀ (n : ℕ) (x : A), x ∈ positiveEvenPart 𝒜 →
      γ'.dpow n (1 ⊗ₜ[R] x) = 1 ⊗ₜ[R] γ.dpow n x)
    (n : ℕ) (hn : n ≠ 0) (x : A) (hx : x ∈ positiveEvenPart 𝒜) :
    (d.baseChange R') (γ'.dpow n (1 ⊗ₜ[R] x)) =
      (d.baseChange R') (1 ⊗ₜ[R] x) * γ'.dpow (n - 1) (1 ⊗ₜ[R] x) := by
  rw [hγ n x hx, LinearMap.baseChange_tmul,
    IsCompatibleWithDifferential.d_dpow hn hx,
    LinearMap.baseChange_tmul, hγ (n - 1) x hx]
  simp

end DividedPowers.TateResolution
