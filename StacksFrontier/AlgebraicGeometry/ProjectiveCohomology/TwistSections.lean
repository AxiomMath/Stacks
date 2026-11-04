module

public import StacksFrontier.AlgebraicGeometry.ProjectiveCohomology.Basic
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwist
import StacksFrontier.AlgebraicGeometry.Divisors.ProjClosedSubschemeKernel
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Sections of a twist of the structure sheaf on a standard open of `Proj`

Let `A = ⨁_{d ≥ 0} 𝒜 d` be a graded ring and let `f ∈ 𝒜 k` be homogeneous of degree `k > 0`.
This file identifies the sections of the twist `𝒪_{Proj A}(d)` over the standard open `D₊(f)`
with the degree-`d` part of the localization `A[1/f]`, and shows that the family of degree
parts really is a grading of `A[1/f]` by `ℤ`.

The degree-`d` part is described concretely: it consists of the *single* fractions `a / fᵐ` with
`a` homogeneous of degree `m * k + d`. That this set of fractions is already closed under
addition and under multiplication by degree-zero fractions — so that no sums have to be taken —
is the content of the comparison with
`AlgebraicGeometry.ProjectiveSpectrum.Proj.GradedModuleDegreeZeroLocalization`, which is defined
as the span of those fractions.

Specialized to the polynomial ring `A = R[T₀, …, Tₙ]` and to `f = T_{i₀} ⋯ T_{i_p}` a product of
homogeneous coordinates, this is the identification

`Γ(D₊(T_{i₀} ⋯ T_{i_p}), 𝒪(d)) = (R[T₀, …, Tₙ, 1/(T_{i₀} ⋯ T_{i_p})])_d`

of the Čech term appearing in the proof of [Stacks, Tag 01XT]. The standard open is the
intersection of the coordinate charts `D₊(T_{i_j})`, by
`Stacks.ProjectiveCohomology.iInf_basicOpen_eq_basicOpen_prod`.

## Main definitions

* `Stacks.ProjectiveCohomology.awayGrading`: the degree-`d` part of `A[1/f]`, as the set of
  fractions `a / fᵐ` with `a` homogeneous of degree `m * k + d`.

## Main results

* `Stacks.ProjectiveCohomology.mem_degreeZeroLocalization_twistGrading_iff`: the span defining
  `A(d)₍f₎` is already the explicit set of fractions.
* `Stacks.ProjectiveCohomology.iSup_awayGrading_eq_top`,
  `Stacks.ProjectiveCohomology.iSupIndep_awayGrading` and
  `Stacks.ProjectiveCohomology.awayGradingDecomposition`: **the localization of a graded ring at
  a homogeneous element is `ℤ`-graded.**
* `Stacks.ProjectiveCohomology.sectionsTwistEquivAwayGrading`: **the sections of `𝒪(d)` over
  `D₊(f)` are the degree-`d` part of `A[1/f]`.**
* `Stacks.ProjectiveCohomology.sectionsTwistProdXEquiv`: the same for a product of homogeneous
  coordinates of a polynomial ring, i.e. for an intersection of standard coordinate charts.
* `Stacks.ProjectiveCohomology.coe_sectionsTwistEquivAwayGrading`: that identification is the
  underlying map of the `A₍f₎`-linear equivalence `associatedModuleSheafStandardOpenEquiv`.

The Laurent monomial basis of `R[T₀, …, Tₙ, 1/(T_{i₀} ⋯ T_{i_p})]`, its `ℤ^{n+1}`-graded
description, is `Stacks.PartialLaurent.basisProdX`.

## Implementation notes

The degree parts are `AddSubgroup`s of the module localization `LocalizedModule.Away f A`,
packaged as `Submodule ℤ` by `AddSubgroup.toIntSubmodule` so that the family has the same shape
as `AlgebraicGeometry.ProjectiveSpectrum.Proj.integerGrading` and is eligible to carry a
`DirectSum.Decomposition`. `LocalizedModule.Away f A` rather than `Localization.Away f` is used
because that is where `GradedModuleDegreeZeroLocalization` lives.

Two degenerate cases have to be carried through. A homogeneous element can lie in two different
graded pieces only if it is zero, and a power of `f` can be zero, in which case the localization
is the zero module; `localizedModule_eq_zero_of_pow_eq_zero` disposes of that branch.

`AlgebraicGeometry.ProjectiveSpectrum.Proj.mul_mem_integerGrading` comes from the private import
`StacksFrontier.AlgebraicGeometry.Divisors.ProjClosedSubschemeKernel`. Its natural home is
`StacksFrontier.AlgebraicGeometry.Constructions.ProjTwist`, where `integerGrading` is defined.

## References

* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
* [Stacks Project, Tag 01M6](https://stacks.math.columbia.edu/tag/01M6)
* [Stacks Project, Tag 01MN](https://stacks.math.columbia.edu/tag/01MN)
-/

@[expose] public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpectrum.Proj CategoryTheory
open TopologicalSpace Opposite

universe u

namespace Stacks.ProjectiveCohomology

section GradedAway

variable {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- If a power of `f` vanishes then the localization of any module away from `f` is zero. -/
theorem localizedModule_eq_zero_of_pow_eq_zero {f : A} {m : ℕ} (h : f ^ m = 0)
    (z : LocalizedModule.Away f A) : z = 0 :=
  have : Subsingleton (LocalizedModule.Away f A) :=
    LocalizedModule.subsingleton (by rw [← h]; exact ⟨m, rfl⟩)
  Subsingleton.elim _ _

variable {f : A} {k : ℕ}

/-- Multiplying a numerator of degree `m * k + d` by an element of degree `n * k` gives one of
degree `(n + m) * k + d`. -/
private theorem mul_mem_integerGrading_add_mul {x a : A} {c n m N : ℕ} {d : ℤ} (hx : x ∈ 𝒜 c)
    (hc : c = n * k) (ha : a ∈ integerGrading 𝒜 ((m * k : ℕ) + d)) (hN : n + m = N) :
    x * a ∈ integerGrading 𝒜 ((N * k : ℕ) + d) := by
  subst hc hN
  convert mul_mem_integerGrading 𝒜 hx ha using 2
  push_cast; ring

/-- The degree `d` part of the localization `A[1/f]` of a graded ring at a homogeneous element
of degree `k`, as an additive subgroup of the module localization: the fractions `a / fᵐ` whose
numerator is homogeneous of degree `m * k + d`. -/
@[ega "II 2.2.1", ega "II 2.2.7" "partial, special case", ega "II 8.2.1" "special case"]
def awayGradingAddSubgroup (hf : f ∈ 𝒜 k) (d : ℤ) :
    AddSubgroup (LocalizedModule.Away f A) where
  carrier := {z | ∃ (m : ℕ) (a : A), a ∈ integerGrading 𝒜 ((m * k : ℕ) + d) ∧
      z = LocalizedModule.mk a ⟨f ^ m, by exact ⟨m, rfl⟩⟩}
  zero_mem' := ⟨0, 0, zero_mem _, (LocalizedModule.zero_mk _).symm⟩
  add_mem' := by
    rintro x y ⟨m₁, a₁, h₁, rfl⟩ ⟨m₂, a₂, h₂, rfl⟩
    refine ⟨m₁ + m₂, f ^ m₂ * a₁ + f ^ m₁ * a₂, add_mem ?_ ?_, ?_⟩
    · convert mul_mem_integerGrading 𝒜 (SetLike.pow_mem_graded m₂ hf) h₁ using 2
      push_cast [smul_eq_mul]; ring
    · convert mul_mem_integerGrading 𝒜 (SetLike.pow_mem_graded m₁ hf) h₂ using 2
      push_cast [smul_eq_mul]; ring
    · rw [LocalizedModule.mk_add_mk]
      refine congrArg₂ _ ?_ (Subtype.ext ?_)
      · simp [Submonoid.smul_def]
      · simpa using (pow_add f m₁ m₂).symm
  neg_mem' := by
    rintro x ⟨m, a, h, rfl⟩
    exact ⟨m, -a, neg_mem h, LocalizedModule.mk_neg.symm⟩

/-- The degree `d` part of the localization `A[1/f]` of a graded ring at a homogeneous element
of degree `k`: the fractions `a / fᵐ` whose numerator is homogeneous of degree `m * k + d`. -/
@[ega "II 2.2.1", ega "II 8.2.1" "special case"]
def awayGrading (hf : f ∈ 𝒜 k) (d : ℤ) : Submodule ℤ (LocalizedModule.Away f A) :=
  AddSubgroup.toIntSubmodule (awayGradingAddSubgroup 𝒜 hf d)

/-- Membership in the degree `d` part of `A[1/f]`: being a fraction `a / fᵐ` with `a`
homogeneous of degree `m * k + d`. -/
theorem mem_awayGrading {hf : f ∈ 𝒜 k} {d : ℤ} {z : LocalizedModule.Away f A} :
    z ∈ awayGrading 𝒜 hf d ↔ ∃ (m : ℕ) (a : A), a ∈ integerGrading 𝒜 ((m * k : ℕ) + d) ∧
      z = LocalizedModule.mk a ⟨f ^ m, by exact ⟨m, rfl⟩⟩ := Iff.rfl

/-- Two fractions with the same denominator add by adding their numerators. -/
theorem mk_add_mk_same {S : Submonoid A} (a b : A) (s : S) :
    LocalizedModule.mk a s + LocalizedModule.mk b s = LocalizedModule.mk (a + b) s := by
  rw [LocalizedModule.mk_add_mk, LocalizedModule.mk_eq]
  exact ⟨1, by simp [smul_add, Submonoid.smul_def, mul_smul, smul_eq_mul]⟩

/-- A finite sum of fractions with the same denominator is the fraction of the sum of the
numerators. -/
theorem mk_sum {S : Submonoid A} {ι : Type*} (t : Finset ι) (g : ι → A) (s : S) :
    LocalizedModule.mk (∑ i ∈ t, g i) s = ∑ i ∈ t, LocalizedModule.mk (g i) s := by
  classical
  induction t using Finset.induction with
  | empty => simp
  | insert a u ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih, mk_add_mk_same]

/-- A fraction `a / fᵐ` with `a` homogeneous of degree `m * k + d` lies in the degree `d` part
of `A[1/f]`. -/
theorem mk_mem_awayGrading (hf : f ∈ 𝒜 k) {d : ℤ} {m : ℕ} {a : A}
    (ha : a ∈ integerGrading 𝒜 ((m * k : ℕ) + d)) :
    LocalizedModule.mk a (⟨f ^ m, by exact ⟨m, rfl⟩⟩ : Submonoid.powers f) ∈
      awayGrading 𝒜 hf d :=
  ⟨m, a, ha, rfl⟩

/-- A power of `f` that is homogeneous of some degree is homogeneous of the expected degree,
unless it is zero. -/
theorem pow_degree_eq (hf : f ∈ 𝒜 k) {m c : ℕ} (hm : f ^ m ∈ 𝒜 c) :
    f ^ m = 0 ∨ c = m * k := by
  classical
  by_cases h0 : f ^ m = 0
  · exact Or.inl h0
  · exact Or.inr
      (DirectSum.degree_eq_of_mem_mem 𝒜 hm (by simpa using SetLike.pow_mem_graded m hf) h0)

/-- **The span defining the degree-`d` part is already the set of single fractions.**
An element of `A[1/f]` lies in the degree-zero localization of the shifted module `A(d)` exactly
when it is a fraction `a / fᵐ` with `a` homogeneous of degree `m * k + d`. -/
@[ega "II 8.2.7" "partial", ega "II 8.2.9" "partial"]
theorem mem_degreeZeroLocalization_twistGrading_iff (hf : f ∈ 𝒜 k) (d : ℤ)
    (z : LocalizedModule.Away f A) :
    z ∈ GradedModuleDegreeZeroLocalization 𝒜 (twistGrading (S := A) 𝒜 d) f ↔
      z ∈ awayGrading 𝒜 hf d := by
  constructor
  · intro hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨c, m, hfc, a, ha, rfl⟩ := hx
      rcases pow_degree_eq 𝒜 hf (show f ^ m ∈ 𝒜 (m * c) by
        simpa using SetLike.pow_mem_graded m hfc) with h0 | hck
      · rw [localizedModule_eq_zero_of_pow_eq_zero h0 (LocalizedModule.mk a _)]
        exact zero_mem _
      · refine mk_mem_awayGrading 𝒜 hf ?_
        have he : ((m * k : ℕ) : ℤ) + d = m • (c : ℤ) + d := by
          rw [← hck, nsmul_eq_mul]; push_cast; ring
        rw [he]
        simpa using ha
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul r x _ hx =>
      obtain ⟨m, a, ha, rfl⟩ := hx
      obtain ⟨⟨i, num, den, hden⟩, rfl⟩ := HomogeneousLocalization.mk_surjective r
      have hden' : ∃ j, f ^ j = (den : A) := hden
      obtain ⟨j, hj⟩ := hden'
      have hsmul : HomogeneousLocalization.mk
            (⟨i, num, den, hden⟩ : HomogeneousLocalization.NumDenSameDeg 𝒜
              (Submonoid.powers f)) •
            LocalizedModule.mk a (⟨f ^ m, by exact ⟨m, rfl⟩⟩ : Submonoid.powers f) =
          Localization.mk (num : A) (⟨(den : A), hden⟩ : Submonoid.powers f) •
            LocalizedModule.mk a (⟨f ^ m, by exact ⟨m, rfl⟩⟩ : Submonoid.powers f) := rfl
      rw [hsmul]
      rcases pow_degree_eq 𝒜 hf (show f ^ j ∈ 𝒜 i by rw [hj]; exact den.2) with h0 | hik
      · convert zero_mem (awayGrading 𝒜 hf d)
        exact localizedModule_eq_zero_of_pow_eq_zero h0 _
      · have hval : Localization.mk (num : A) (⟨(den : A), hden⟩ : Submonoid.powers f) •
              LocalizedModule.mk a (⟨f ^ m, by exact ⟨m, rfl⟩⟩ : Submonoid.powers f) =
            LocalizedModule.mk ((num : A) * a)
              (⟨f ^ (j + m), by exact ⟨j + m, rfl⟩⟩ : Submonoid.powers f) := by
          rw [LocalizedModule.mk_smul_mk]
          refine congrArg₂ _ (by simp [smul_eq_mul]) (Subtype.ext ?_)
          simpa [← hj] using (pow_add f j m).symm
        rw [hval]
        refine mk_mem_awayGrading 𝒜 hf ?_
        exact mul_mem_integerGrading_add_mul 𝒜 num.2 hik ha rfl
  · rintro ⟨m, a, ha, rfl⟩
    refine Submodule.subset_span ⟨k, m, hf, a, ?_, rfl⟩
    have he : m • (k : ℤ) + d = ((m * k : ℕ) : ℤ) + d := by
      rw [nsmul_eq_mul]; push_cast; ring
    simpa [he] using ha

/-- The degree-`d` part `awayGrading` has the same underlying set as the `A₍f₎`-submodule
`GradedModuleDegreeZeroLocalization` of the shifted module `A(d)`. -/
theorem coe_degreeZeroLocalization_twistGrading (hf : f ∈ 𝒜 k) (d : ℤ) :
    (GradedModuleDegreeZeroLocalization 𝒜 (twistGrading (S := A) 𝒜 d) f :
        Set (LocalizedModule.Away f A)) =
      (awayGrading 𝒜 hf d : Set (LocalizedModule.Away f A)) :=
  Set.ext fun z => mem_degreeZeroLocalization_twistGrading_iff 𝒜 hf d z

/-! ### The localization of a graded ring at a homogeneous element is `ℤ`-graded -/

/-- The degree parts of `A[1/f]` span it. -/
theorem iSup_awayGrading_eq_top (hf : f ∈ 𝒜 k) :
    (⨆ d : ℤ, awayGrading 𝒜 hf d) = ⊤ := by
  classical
  refine top_unique fun z _ => ?_
  induction z using LocalizedModule.induction_on with
  | h a s =>
    obtain ⟨_, m, rfl⟩ := s
    rw [← DirectSum.sum_support_decompose 𝒜 a, mk_sum]
    refine sum_mem fun i _ => Submodule.mem_iSup_of_mem ((i : ℤ) - (m * k : ℕ)) ?_
    exact mk_mem_awayGrading 𝒜 hf (by simp)

/-- Homogeneous elements of pairwise distinct degrees `c + e`, for `e` in a finite set of
integers, that sum to zero all vanish. -/
theorem eq_zero_of_sum_integerGrading_eq_zero {s : Finset ℤ} (c : ℤ) (x : ℤ → A)
    (hx : ∀ e ∈ s, x e ∈ integerGrading 𝒜 (c + e)) (h0 : ∑ e ∈ s, x e = 0) :
    ∀ e ∈ s, x e = 0 := by
  classical
  have hindep : iSupIndep (integerGrading 𝒜) :=
    (DirectSum.Decomposition.isInternal (integerGrading 𝒜)).submodule_iSupIndep
  intro e he
  have hmem : c + e ∈ s.map ⟨(c + ·), add_right_injective c⟩ :=
    Finset.mem_map.mpr ⟨e, he, rfl⟩
  have hall : ∀ j ∈ s.map ⟨(c + ·), add_right_injective c⟩, x (j - c) ∈ integerGrading 𝒜 j := by
    intro j hj
    obtain ⟨e', he', rfl⟩ := Finset.mem_map.mp hj
    simpa using hx e' he'
  have hsum : ∑ j ∈ s.map ⟨(c + ·), add_right_injective c⟩, x (j - c) = 0 := by
    rw [Finset.sum_map]
    simpa using h0
  have := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero (integerGrading 𝒜)).mp hindep
    (s.map ⟨(c + ·), add_right_injective c⟩) (fun j => x (j - c)) hall hsum (c + e) hmem
  simpa using this

/-- A fraction with denominator a power of `f` vanishes iff some power of `f` kills its
numerator. -/
private theorem mk_pow_eq_zero_iff {a : A} {m : ℕ} :
    LocalizedModule.mk a (⟨f ^ m, by exact ⟨m, rfl⟩⟩ : Submonoid.powers f) = 0 ↔
      ∃ N : ℕ, f ^ N * a = 0 := by
  rw [← LocalizedModule.zero_mk (1 : Submonoid.powers f), LocalizedModule.mk_eq]
  constructor
  · rintro ⟨⟨_, N, rfl⟩, h⟩
    exact ⟨N, by simpa [Submonoid.smul_def] using h⟩
  · rintro ⟨N, h⟩
    exact ⟨⟨f ^ N, N, rfl⟩, by simpa [Submonoid.smul_def] using h⟩

/-- The degree parts of `A[1/f]` are independent. -/
theorem iSupIndep_awayGrading (hf : f ∈ 𝒜 k) :
    iSupIndep (fun d : ℤ => awayGrading 𝒜 hf d) := by
  classical
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
  intro s v hv hv0
  have hex : ∀ e ∈ s, ∃ (m : ℕ) (a : A), a ∈ integerGrading 𝒜 ((m * k : ℕ) + e) ∧
      v e = LocalizedModule.mk a (⟨f ^ m, by exact ⟨m, rfl⟩⟩ : Submonoid.powers f) :=
    fun e he => hv e he
  choose! m a ham hav using hex
  set M := ∑ e ∈ s, m e with hM
  have hle : ∀ e ∈ s, m e ≤ M := fun e he =>
    Finset.single_le_sum (f := m) (fun _ _ => Nat.zero_le _) he
  set b : ℤ → A := fun e => f ^ (M - m e) * a e with hb
  have hbmem : ∀ e ∈ s, b e ∈ integerGrading 𝒜 ((M * k : ℕ) + e) := by
    intro e he
    exact mul_mem_integerGrading_add_mul 𝒜 (SetLike.pow_mem_graded (M - m e) hf) (smul_eq_mul ..)
      (ham e he) (Nat.sub_add_cancel (hle e he))
  have hvb : ∀ e ∈ s, v e = LocalizedModule.mk (b e)
      (⟨f ^ M, by exact ⟨M, rfl⟩⟩ : Submonoid.powers f) := by
    intro e he
    rw [hav e he, LocalizedModule.mk_eq]
    refine ⟨1, ?_⟩
    have hcancel : m e + (M - m e) = M := Nat.add_sub_cancel' (hle e he)
    simp only [hb, Submonoid.smul_def, one_smul, smul_eq_mul]
    rw [← mul_assoc, ← pow_add, hcancel]
  have hzero : LocalizedModule.mk (∑ e ∈ s, b e)
      (⟨f ^ M, by exact ⟨M, rfl⟩⟩ : Submonoid.powers f) = 0 := by
    rw [mk_sum, ← hv0]
    exact (Finset.sum_congr rfl hvb).symm
  obtain ⟨N, hN⟩ := mk_pow_eq_zero_iff.mp hzero
  have hNmul : ∑ e ∈ s, f ^ N * b e = 0 := by rw [← Finset.mul_sum]; exact hN
  have hcomp : ∀ e ∈ s, f ^ N * b e = 0 := by
    exact eq_zero_of_sum_integerGrading_eq_zero 𝒜 (((N + M) * k : ℕ) : ℤ)
      (fun e => f ^ N * b e) (fun e he => mul_mem_integerGrading_add_mul 𝒜
        (SetLike.pow_mem_graded N hf) (smul_eq_mul ..) (hbmem e he) rfl) hNmul
  intro e he
  rw [hvb e he]
  exact mk_pow_eq_zero_iff.mpr ⟨N, hcomp e he⟩

/-- **The localization of a graded ring at a homogeneous element is `ℤ`-graded.** The degree
parts are the single fractions `a / fᵐ` with `a` homogeneous of degree `m * k + d`. -/
@[instance_reducible, ega "II 2.2.1" "partial", ega "II 8.2.1" "partial"]
def awayGradingDecomposition (hf : f ∈ 𝒜 k) :
    DirectSum.Decomposition (fun d : ℤ => awayGrading 𝒜 hf d) :=
  (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (iSupIndep_awayGrading 𝒜 hf) (iSup_awayGrading_eq_top 𝒜 hf)).chooseDecomposition

end GradedAway

/-! ### The sections of a twist over a standard open -/

section Sections

variable {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {f : A} {k : ℕ}

/-- **The sections of `𝒪_{Proj A}(d)` over the standard open `D₊(f)` are the degree-`d` part of
the localization `A[1/f]`.** This is the identification of the Čech terms in the proof of
[Stacks, Tag 01XT]; it is [Stacks, Tag 01M6] part (3) for the shifted module `A(d)`, combined
with the description of the degree-`d` part as single fractions. -/
def sectionsTwistEquivAwayGrading (hf : f ∈ 𝒜 k) (hk : 0 < k) (d : ℤ) :
    ((twistingSheaf 𝒜 d).val.obj (op (ProjectiveSpectrum.basicOpen 𝒜 f))) ≃+
      awayGrading 𝒜 hf d where
  toFun s := ⟨((associatedModuleSheafStandardOpenEquiv 𝒜 (twistGrading (S := A) 𝒜 d) hf hk s :
      LocalizedModule.Away f A)),
    (mem_degreeZeroLocalization_twistGrading_iff 𝒜 hf d _).mp
      (associatedModuleSheafStandardOpenEquiv 𝒜 (twistGrading (S := A) 𝒜 d) hf hk s).2⟩
  invFun z := (associatedModuleSheafStandardOpenEquiv 𝒜 (twistGrading (S := A) 𝒜 d) hf hk).symm
    ⟨(z : LocalizedModule.Away f A),
      (mem_degreeZeroLocalization_twistGrading_iff 𝒜 hf d _).mpr z.2⟩
  left_inv s :=
    (associatedModuleSheafStandardOpenEquiv 𝒜 (twistGrading (S := A) 𝒜 d) hf hk).symm_apply_apply s
  right_inv z := by
    refine Subtype.ext ?_
    simp only
    rw [(associatedModuleSheafStandardOpenEquiv 𝒜
      (twistGrading (S := A) 𝒜 d) hf hk).apply_symm_apply]
  map_add' s t := by
    refine Subtype.ext ?_
    simp

/-- **`sectionsTwistEquivAwayGrading` is the underlying map of an `A₍f₎`-linear equivalence**,
namely of the `HomogeneousLocalization.Away 𝒜 f`-linear equivalence
`associatedModuleSheafStandardOpenEquiv`. -/
theorem coe_sectionsTwistEquivAwayGrading (hf : f ∈ 𝒜 k) (hk : 0 < k) (d : ℤ)
    (s : (twistingSheaf 𝒜 d).val.obj (op (ProjectiveSpectrum.basicOpen 𝒜 f))) :
    ((sectionsTwistEquivAwayGrading 𝒜 hf hk d s : LocalizedModule.Away f A)) =
      (associatedModuleSheafStandardOpenEquiv 𝒜 (twistGrading (S := A) 𝒜 d) hf hk s :
        LocalizedModule.Away f A) := rfl

end Sections

/-! ### The Čech terms of the standard cover of projective space -/

section Polynomial

variable (R : Type u) [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- An intersection of finitely many coordinate standard opens of `Proj R[T₀, …, Tₙ]`, read in
the homogeneous spectrum rather than in the scheme. -/
@[ega "II 2.3.3" "special case"]
theorem iInf_projectiveSpectrum_basicOpen_X {n r : ℕ} (s : Fin (r + 1) → Fin (n + 1)) :
    (⨅ j, ProjectiveSpectrum.basicOpen
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X (s j))) =
      ProjectiveSpectrum.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (∏ j, MvPolynomial.X (s j)) :=
  iInf_basicOpen_eq_basicOpen_prod _ _

/-- **The Čech term of [Stacks, Tag 01XT].** The sections of the twist `𝒪(d)` over the
intersection `D₊(T_{i₀} ⋯ T_{i_p})` of coordinate standard opens of `Proj R[T₀, …, Tₙ]` are the
degree-`d` part of `R[T₀, …, Tₙ, 1/(T_{i₀} ⋯ T_{i_p})]`. -/
def sectionsTwistProdXEquiv {n r : ℕ} (s : Fin (r + 1) → Fin (n + 1)) (d : ℤ) :
    ((twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) d).val.obj
        (op (ProjectiveSpectrum.basicOpen _ (∏ j, MvPolynomial.X (s j))))) ≃+
      awayGrading (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (prod_X_mem_degree R s) d :=
  sectionsTwistEquivAwayGrading _ (prod_X_mem_degree R s) (Nat.succ_pos r) d

end Polynomial

end Stacks.ProjectiveCohomology

end
