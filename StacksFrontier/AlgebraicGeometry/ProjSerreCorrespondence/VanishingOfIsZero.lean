module

public import StacksFrontier.AlgebraicGeometry.ProjCoherentII.ReductionDegree
public import StacksFrontier.AlgebraicGeometry.ProjNoetherian.Basic
public import StacksFrontier.AlgebraicGeometry.ProjSerreCorrespondence.PowerTorsionOfIsZero
public import StacksFrontier.RingTheory.GradedAlgebra.AddSubgroupGrading
public import StacksFrontier.RingTheory.GradedAlgebra.PowerTorsionVanishing
public import StacksFrontier.RingTheory.GradedAlgebra.VeroneseFiniteness

/-!
# A finite graded module with vanishing associated sheaf vanishes in large divisible degrees

Let `A` be a graded ring which is Noetherian as a ring, let `M` be a finite graded `A`-module and
suppose the associated sheaf `M̃` on `Proj A` is the zero object. Then there is a positive `d` —
the least common multiple of the degrees of a finite set of homogeneous generators of `A` over
`A₀` — and a bound `n₀` such that `M_n = 0` for every `n ≥ n₀` divisible by `d`. The vanishing
holds more generally for every positive `d` divisible by that least common multiple.

The divisibility cannot be dropped: for `A = k[f]` with `deg f = 2` and `M = A(1)` the sheaf `M̃`
vanishes while `M_n ≠ 0` for every odd `n ≥ -1`.

## Main results

* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.dvd_of_mem_support_of_mem_veroneseSubmodule`:
  every degree occurring in the homogeneous decomposition of an element of the Veronese part is
  divisible by `d`.
* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.forall_eq_zero_of_isZero_of_lcm_dvd`: the
  statement above with the generating family and the degree `d` given, `d` any positive multiple
  of the lcm of the generator degrees.
* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.exists_forall_eq_zero_of_isZero`: the
  statement above, at the lcm itself.
* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.gradeEventuallyZero_of_isZero`: the same, in
  the form of the `GradeEventuallyZero` predicate of [Stacks, Tag 0BXE]; this is the converse of
  `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.exists_pow_smul_eq_zero_of_gradeEventuallyZero`

## References

* [Stacks Project, Tag 0B5R](https://stacks.math.columbia.edu/tag/0B5R)
* [Stacks Project, Tag 0BXE](https://stacks.math.columbia.edu/tag/0BXE)
-/

@[expose] public noncomputable section

open CategoryTheory DirectSum
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpectrum.Proj
open scoped Stacks.GradedLocalization

namespace Stacks.AlgebraicGeometry.ProjSerreCorrespondence

universe u v w t

variable {S : Type u} {M : Type v} {σ : Type w} {τ : Type t}
  [CommRing S] [AddCommGroup M] [Module S M]
  [SetLike σ S] [AddSubgroupClass σ S] (𝒜 : ℕ → σ) [GradedRing 𝒜]
  [SetLike τ M] [AddSubgroupClass τ M] (𝒨 : ℤ → τ) [DirectSum.Decomposition 𝒨]
  [SetLike.GradedSMul 𝒜 𝒨]

/-- **Only degrees divisible by `d` occur in the Veronese part.** If `x` lies in the Veronese
part `⨁ₙ M_{nd}`, then its homogeneous component of every degree not divisible by `d` vanishes. -/
theorem dvd_of_mem_support_of_mem_veroneseSubmodule (d : ℕ)
    {x : M} (hx : x ∈ Stacks.Veronese.veroneseSubmodule 𝒜 (Stacks.GradedModule.addSubgroupGrading
      (M := M) 𝒨) d) {k : ℤ} (hk : ¬ ((d : ℤ) ∣ k)) :
    ((DirectSum.decompose 𝒨 x k : 𝒨 k) : M) = 0 := by
  classical
  set T : AddSubgroup M :=
    { carrier := {y : M | ((DirectSum.decompose 𝒨 y k : 𝒨 k) : M) = 0}
      zero_mem' := by simp
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        rw [DirectSum.decompose_add, DFinsupp.add_apply, AddMemClass.coe_add, ha, hb,
          add_zero]
      neg_mem' := by
        intro a ha
        simp only [Set.mem_ofPred_eq] at ha ⊢
        rw [DirectSum.decompose_neg, DFinsupp.neg_apply, NegMemClass.coe_neg, ha, neg_zero] }
    with hT
  have hgen : Stacks.Veronese.veroneseModuleSet
      (Stacks.GradedModule.addSubgroupGrading (M := M) 𝒨) d ⊆ T := by
    simp only [Stacks.Veronese.veroneseModuleSet, Set.iUnion_subset_iff]
    intro n a ha
    have ha' : a ∈ 𝒨 (n * (d : ℤ)) := ha
    have hdn : (d : ℤ) ∣ n * (d : ℤ) := ⟨n, by ring⟩
    have hne : k ≠ n * (d : ℤ) := fun h => hk (h ▸ hdn)
    show ((DirectSum.decompose 𝒨 a k : 𝒨 k) : M) = 0
    rw [DirectSum.decompose_of_mem_ne 𝒨 ha' (Ne.symm hne)]
  exact AddSubgroup.closure_le T |>.mpr hgen
    ((Stacks.Veronese.mem_veroneseSubmodule_iff 𝒜 _ d).mp hx)

/-- **A finite graded module over a Noetherian graded ring whose associated sheaf vanishes is
zero in all large degrees divisible by `d`**, for every positive `d` divisible by the least
common multiple of the degrees of the given homogeneous generators `f` of the ring over its
degree-zero part.

The divisibility of `n` by `d` cannot be dropped: for `A = k[f]` with `f` of degree `2` and
`M = A(1)` the sheaf `M̃` on the one-point space `Proj A` is zero while `M_n ≠ 0` for every odd
`n ≥ -1`. -/
theorem forall_eq_zero_of_isZero_of_lcm_dvd [IsNoetherianRing S] [Module.Finite S M]
    (hzero : Limits.IsZero (associatedModuleSheaf 𝒜 𝒨))
    {r : ℕ} (f : Fin r → S) (deg : Fin r → ℕ) (hdeg : ∀ i, 0 < deg i)
    (hfdeg : ∀ i, f i ∈ 𝒜 (deg i))
    (hgen : Algebra.adjoin (Stacks.Veronese.gradeZero 𝒜) (Set.range f) = ⊤)
    {d : ℕ} (hd : 0 < d) (hdvd : Finset.univ.lcm deg ∣ d) :
    ∃ n₀ : ℤ, ∀ n : ℤ, n₀ ≤ n → (d : ℤ) ∣ n → ∀ x ∈ 𝒨 n, x = (0 : M) := by
  classical
  have hdegdvd : ∀ i, deg i ∣ d := fun i =>
    dvd_trans (Finset.dvd_lcm (Finset.mem_univ i)) hdvd
  set ℳ : ℤ → AddSubgroup M := Stacks.GradedModule.addSubgroupGrading (M := M) 𝒨 with hℳ
  have hfin := Stacks.Veronese.finite_veroneseSubmodule_of_lcm_dvd 𝒜 hdeg hfdeg hgen hd hdvd ℳ
  obtain ⟨s, hs⟩ : (Stacks.Veronese.veroneseSubmodule 𝒜 ℳ d).FG :=
    Module.Finite.iff_fg.mp hfin
  set ι : Type _ := Σ v : {x // x ∈ s}, {k : ℤ // k ∈ (DirectSum.decompose 𝒨 (v : M)).support}
    with hι
  set y : ι → M := fun j => ((DirectSum.decompose 𝒨 (j.1 : M) (j.2 : ℤ) : 𝒨 (j.2 : ℤ)) : M)
    with hy_def
  set c : ι → ℤ := fun j => (j.2 : ℤ) with hc_def
  have hy : ∀ j : ι, y j ∈ 𝒨 (c j) := fun j => (DirectSum.decompose 𝒨 (j.1 : M) (j.2 : ℤ)).2
  have hmemV : ∀ v ∈ s, v ∈ Stacks.Veronese.veroneseSubmodule 𝒜 ℳ d := by
    intro v hv
    rw [← hs]
    exact Submodule.subset_span hv
  have hcdvd : ∀ j : ι, (d : ℤ) ∣ c j := by
    intro j
    by_contra hk
    refine DFinsupp.mem_support_iff.mp j.2.2 (Subtype.ext ?_)
    rw [ZeroMemClass.coe_zero]
    exact dvd_of_mem_support_of_mem_veroneseSubmodule 𝒜 𝒨 d
      (hmemV (j.1 : M) j.1.2) hk
  have htor : ∀ (i : Fin r) (j : ι), ∃ N : ℕ, f i ^ N • y j = 0 := fun i j =>
    exists_pow_smul_eq_zero_of_isZero_of_dvd 𝒜 𝒨 hzero (hdeg i) (hfdeg i)
      (dvd_trans (Int.natCast_dvd_natCast.mpr (hdegdvd i)) (hcdvd j)) (hy j)
  choose N hN using htor
  set m : ι → ℤ := fun j => c j + ((∑ i, N i j * deg i : ℕ) : ℤ) with hm
  set B : ℕ := Finset.univ.sup (fun j : ι => (m j).toNat) with hB
  refine ⟨(B : ℤ) + 1, fun n hn hdn x hx => ?_⟩
  have hbound : ∀ j : ι, m j < n := by
    intro j
    have h1 : m j ≤ ((m j).toNat : ℤ) := Int.self_le_toNat _
    have h2 : ((m j).toNat : ℤ) ≤ (B : ℤ) := by
      exact_mod_cast Finset.le_sup (f := fun j : ι => (m j).toNat) (Finset.mem_univ j)
    omega
  have hxV : x ∈ Stacks.Veronese.veroneseSubmodule 𝒜 ℳ d := by
    obtain ⟨q, rfl⟩ := hdn
    refine (Stacks.Veronese.mem_veroneseSubmodule_iff 𝒜 ℳ d).mpr
      (AddSubgroup.subset_closure ((Stacks.Veronese.mem_veroneseModuleSet_iff ℳ).mpr ⟨q, ?_⟩))
    show x ∈ 𝒨 (q * (d : ℤ))
    rwa [mul_comm]
  have hspanS : ∀ z ∈ Stacks.Veronese.veroneseSubmodule 𝒜 ℳ d,
      z ∈ Submodule.span S (Set.range y) := by
    intro z hz
    rw [← hs] at hz
    induction hz using Submodule.span_induction with
    | mem v hv =>
        rw [← DirectSum.sum_support_decompose 𝒨 v]
        exact Submodule.sum_mem _ fun k hk => Submodule.subset_span ⟨⟨⟨v, hv⟩, ⟨k, hk⟩⟩, rfl⟩
    | zero => exact zero_mem _
    | add a b _ _ ha hb => exact add_mem ha hb
    | smul a z _ hz =>
        rw [Stacks.Veronese.veroneseModule_smul_def]
        exact Submodule.smul_mem _ _ hz
  exact Stacks.GradedModule.eq_zero_of_mem_span_of_sum_lt 𝒜 𝒨 f deg hfdeg hgen y c hy N hN
    hbound hx (hspanS x hxV)

/-- **A finite graded module over a Noetherian graded ring whose associated sheaf vanishes is
zero in all large degrees divisible by `d`**, where `d` is the least common multiple of the
degrees of a finite set of homogeneous generators of the ring over its degree-zero part.

The divisibility cannot be dropped: for `A = k[f]` with `f` of degree `2` and `M = A(1)` the
sheaf `M̃` on the one-point space `Proj A` is zero while `M_n ≠ 0` for every odd `n ≥ -1`. -/
theorem exists_forall_eq_zero_of_isZero [IsNoetherianRing S] [Module.Finite S M]
    (hzero : Limits.IsZero (associatedModuleSheaf 𝒜 𝒨)) :
    ∃ d : ℕ, 0 < d ∧ ∃ n₀ : ℤ,
      ∀ n : ℤ, n₀ ≤ n → (d : ℤ) ∣ n → ∀ x ∈ 𝒨 n, x = (0 : M) := by
  have hft : Algebra.FiniteType (𝒜 0) S :=
    Stacks.AlgebraicGeometry.Proj.finiteType_of_isNoetherianRing 𝒜
  obtain ⟨r, f, deg, hdeg, hfdeg, hgen⟩ :=
    Stacks.Veronese.homogeneous_generators_of_finiteType 𝒜 hft
  have hdpos : 0 < Finset.univ.lcm deg := Nat.pos_of_ne_zero fun h0 => by
    obtain ⟨i, -, hi⟩ := Finset.lcm_eq_zero_iff.mp h0
    exact Nat.pos_iff_ne_zero.mp (hdeg i) hi
  exact ⟨Finset.univ.lcm deg, hdpos, forall_eq_zero_of_isZero_of_lcm_dvd 𝒜 𝒨 hzero f deg hdeg
    hfdeg hgen hdpos dvd_rfl⟩

/-- **A finite graded module over a Noetherian graded ring whose associated sheaf vanishes is
zero in all large multiples of some positive `d`**, the `GradeEventuallyZero` predicate of
[Stacks, Tag 0BXE]. This is the converse of
`Stacks.AlgebraicGeometry.ProjSerreCorrespondence.exists_pow_smul_eq_zero_of_gradeEventuallyZero`.
-/
theorem gradeEventuallyZero_of_isZero [IsNoetherianRing S] [Module.Finite S M]
    (hzero : Limits.IsZero (associatedModuleSheaf 𝒜 𝒨)) :
    ∃ d : ℕ, 0 < d ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ x ∈ 𝒨 ((n : ℤ) * d), x = (0 : M) := by
  obtain ⟨d, hdpos, n₀, hn₀⟩ := exists_forall_eq_zero_of_isZero 𝒜 𝒨 hzero
  refine ⟨d, hdpos, n₀.toNat, fun n hn x hx => ?_⟩
  refine hn₀ ((n : ℤ) * d) ?_ ⟨(n : ℤ), by ring⟩ x hx
  calc n₀ ≤ (n₀.toNat : ℤ) := Int.self_le_toNat _
    _ ≤ (n : ℤ) := by exact_mod_cast hn
    _ ≤ (n : ℤ) * (d : ℤ) := le_mul_of_one_le_right (Int.natCast_nonneg n) (by exact_mod_cast hdpos)

end Stacks.AlgebraicGeometry.ProjSerreCorrespondence

end
