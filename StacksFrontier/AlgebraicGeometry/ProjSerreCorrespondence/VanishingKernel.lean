module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafifiedDirectSum
public import StacksFrontier.AlgebraicGeometry.ProjNoetherian.Basic
public import StacksFrontier.AlgebraicGeometry.ProjSerreCorrespondence.IrrelevantVanishing
public import StacksFrontier.AlgebraicGeometry.ProjSerreCorrespondence.PowerTorsionOfIsZero
public import StacksFrontier.RingTheory.GradedAlgebra.Veronese
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A finite graded module with vanishing associated sheaf is irrelevant

Let `A` be a graded ring which is Noetherian as a ring, let `X = Proj A`, and let `d` be a
positive integer such that `A` is generated over `A₀` by homogeneous elements whose degrees all
divide `d` — the degree of Stacks 0BXE, taken there to be the least common multiple of the
degrees of a finite homogeneous generating set. This file proves the **hard half of the kernel
identification** in the proof of Stacks 0BXF: a finitely generated graded `A`-module `M` with
`M̃ = 0` satisfies `M_{nd} = 0` for all large `n`, hence is irrelevant.

## Main results

* `exists_homogeneous_generators_of_isNoetherianRing`: a Noetherian graded ring is generated over
  its degree-zero part by finitely many homogeneous elements of positive degree.
* `smul_eq_zero_of_pow_smul_eq_zero`: if a power of each homogeneous generator kills `m`, every
  homogeneous element of large enough positive degree kills it.
* `exists_forall_smul_eq_zero_of_isZero`: if `M̃ = 0`, a homogeneous element of `M` whose degree
  is divisible by the degrees of the ring generators is killed by every homogeneous element of `A`
  of large enough degree.
* `gradeEventuallyZero_of_isZero_of_adjoin`: **`M̃ = 0 ⟹ M_{nd} = 0` for all large `n`.**
* `isIrrelevant_of_isZero`: **`M̃ = 0 ⟹ M` irrelevant.**

## References

* [Stacks Project, Tag 0BXF](https://stacks.math.columbia.edu/tag/0BXF)
* [Stacks Project, Tag 0B5R](https://stacks.math.columbia.edu/tag/0B5R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace DirectSum
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
  (associatedModuleSheaf associatedModuleSheafStandardOpenEquiv degreeZeroFraction)
open Stacks.AlgebraicGeometry.ProjSheafFunctoriality
open scoped Stacks.GradedLocalization

namespace Stacks.AlgebraicGeometry.ProjSerreCorrespondence

universe u v w

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-! ### Homogeneous generators of a Noetherian graded ring -/

/-- The degree-zero part of `𝒮`, read as a subring, and `𝒮 0`, read through its `SetLike`
coercion, have the same elements, so they generate the same subalgebra. -/
public theorem range_algebraMap_gradeZero :
    Set.range (algebraMap (Veronese.gradeZero 𝒮) S) = Set.range (algebraMap (𝒮 0) S) := by
  ext x
  constructor <;> rintro ⟨y, rfl⟩ <;> exact ⟨⟨(y : S), y.2⟩, rfl⟩

/-- Adjoining a set over the degree-zero subring and over `𝒮 0` gives the same subalgebra, as a
set of elements. -/
public theorem mem_adjoin_gradeZero_iff (t : Set S) (x : S) :
    x ∈ Algebra.adjoin (Veronese.gradeZero 𝒮) t ↔ x ∈ Algebra.adjoin (𝒮 0) t := by
  rw [Algebra.mem_adjoin_iff, Algebra.mem_adjoin_iff, range_algebraMap_gradeZero 𝒮]

/-- **A Noetherian graded ring is a finitely generated algebra over its degree-zero subring**
`Stacks.Veronese.gradeZero 𝒮`. -/
@[ega "II 2.1.5" "Necessity clause"]
public theorem finitelyGeneratedOverGradeZero_of_isNoetherianRing [IsNoetherianRing S] :
    Veronese.FinitelyGeneratedOverGradeZero 𝒮 := by
  obtain ⟨t, ht⟩ := (Stacks.AlgebraicGeometry.Proj.finiteType_of_isNoetherianRing 𝒮).out
  refine ⟨⟨t, eq_top_iff.2 fun x _ => ?_⟩⟩
  rw [mem_adjoin_gradeZero_iff 𝒮, ht]
  trivial

/-- **A Noetherian graded ring is generated over its degree-zero part by finitely many
homogeneous elements of positive degree.** -/
public theorem exists_homogeneous_generators_of_isNoetherianRing [IsNoetherianRing S] :
    ∃ (r : ℕ) (f : Fin r → S) (deg : Fin r → ℕ), (∀ i, 0 < deg i) ∧
      (∀ i, f i ∈ 𝒮 (deg i)) ∧
      Algebra.adjoin (Veronese.gradeZero 𝒮) (Set.range f) = ⊤ :=
  Veronese.homogeneous_generators_of_finiteType 𝒮
    (finitelyGeneratedOverGradeZero_of_isNoetherianRing 𝒮)

/-! ### Uniform annihilation by a whole homogeneous component -/

/-- **If a power of each homogeneous ring generator kills `m`, then every homogeneous element of
`A` of large enough positive degree kills `m`.** -/
public theorem smul_eq_zero_of_pow_smul_eq_zero
    {r : ℕ} (f : Fin r → S) (deg : Fin r → ℕ) (hdeg : ∀ i, 0 < deg i)
    (hf : ∀ i, f i ∈ 𝒮 (deg i))
    (hgen : Algebra.adjoin (Veronese.gradeZero 𝒮) (Set.range f) = ⊤)
    {M : Type v} [AddCommGroup M] [Module S M] {m : M}
    {k : Fin r → ℕ} (hk : ∀ i, f i ^ k i • m = 0)
    {c : ℕ} (hc0 : 0 < c) (hc : ∑ i, k i * deg i ≤ c) {a : S} (ha : a ∈ 𝒮 c) :
    a • m = 0 := by
  classical
  have hspan := Veronese.mem_span_monomials 𝒮 f deg hf hgen c ha
  have key : ∀ x ∈ Submodule.span (Veronese.gradeZero 𝒮)
      {x : S | ∃ e : Fin r → ℕ, (∑ i, e i * deg i = c) ∧ x = ∏ i, f i ^ e i}, x • m = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hxm =>
      obtain ⟨e, he, rfl⟩ := hxm
      have hex : ∃ i, k i ≤ e i := by
        by_contra hcon
        push Not at hcon
        have h1 : ∑ i, e i * deg i + ∑ i, deg i ≤ ∑ i, k i * deg i := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_le_sum fun i _ => ?_
          calc e i * deg i + deg i = (e i + 1) * deg i := by ring
            _ ≤ k i * deg i := Nat.mul_le_mul_right _ (by have := hcon i; omega)
        have h2 : ∑ i, deg i = 0 := by omega
        rcases isEmpty_or_nonempty (Fin r) with _ | hne
        · rw [Finset.univ_eq_empty, Finset.sum_empty] at he
          omega
        · obtain ⟨i⟩ := hne
          exact absurd (Finset.sum_eq_zero_iff.mp h2 i (Finset.mem_univ i)) (hdeg i).ne'
      obtain ⟨i, hi⟩ := hex
      have hfac : ∏ j, f j ^ e j
          = (f i ^ (e i - k i) * ∏ j ∈ Finset.univ.erase i, f j ^ e j) * f i ^ k i := by
        rw [← Finset.mul_prod_erase Finset.univ (fun j => f j ^ e j) (Finset.mem_univ i),
          ← pow_sub_mul_pow (f i) hi]
        ring
      rw [hfac, mul_smul, hk i, smul_zero]
    | zero => rw [zero_smul]
    | add x y _ _ hx hy => rw [add_smul, hx, hy, add_zero]
    | smul s x _ hx =>
      rw [show (s • x : S) = (s : S) * x from rfl, mul_smul, hx, smul_zero]
  exact key a hspan

/-- **A homogeneous element of degree divisible by `d` is killed by every homogeneous element of
`A` of large enough degree**, when `M̃ = 0` and the degrees of the ring generators divide `d`. -/
public theorem exists_forall_smul_eq_zero_of_isZero
    {r : ℕ} (f : Fin r → S) (deg : Fin r → ℕ) (hdeg : ∀ i, 0 < deg i)
    (hf : ∀ i, f i ∈ 𝒮 (deg i))
    (hgen : Algebra.adjoin (Veronese.gradeZero 𝒮) (Set.range f) = ⊤)
    {X : GradedModuleCat.{u, u, w} 𝒮} (hX : IsZero (associatedModuleSheaf 𝒮 X.grade))
    {δ : ℤ} (hδ : ∀ i, (deg i : ℤ) ∣ δ) {m : X.carrier} (hm : m ∈ X.grade δ) :
    ∃ C : ℕ, ∀ c : ℕ, 0 < c → C ≤ c → ∀ a ∈ 𝒮 c, a • m = 0 := by
  classical
  have hpow : ∀ i, ∃ k : ℕ, f i ^ k • m = 0 := fun i =>
    exists_pow_smul_eq_zero_of_isZero_of_dvd 𝒮 X.grade hX (hdeg i) (hf i) (hδ i) hm
  choose k hk using hpow
  exact ⟨∑ i, k i * deg i, fun c hc0 hc a ha =>
    smul_eq_zero_of_pow_smul_eq_zero 𝒮 f deg hdeg hf hgen hk hc0 hc ha⟩

/-! ### The vanishing of the sheaf forces vanishing in large degrees divisible by `d` -/

/-- **Stacks 0BXF, the hard half of the kernel identification.** Let `A` be Noetherian graded,
generated over `A₀` by homogeneous `f i` of positive degrees dividing `d`, and let `M` be a
finitely generated graded `A`-module with `M̃ = 0`. Then `M_{nd} = 0` for all large `n`. -/
public theorem gradeEventuallyZero_of_isZero_of_adjoin [IsNoetherianRing S]
    {r : ℕ} (f : Fin r → S) (deg : Fin r → ℕ) (hdeg : ∀ i, 0 < deg i)
    (hf : ∀ i, f i ∈ 𝒮 (deg i))
    (hgen : Algebra.adjoin (Veronese.gradeZero 𝒮) (Set.range f) = ⊤)
    {d : ℕ} (hd : 0 < d) (hdvd : ∀ i, deg i ∣ d)
    {X : GradedModuleCat.{u, u, w} 𝒮} [Module.Finite S X.carrier]
    (hX : IsZero (associatedModuleSheaf 𝒮 X.grade)) :
    GradeEventuallyZero 𝒮 d X := by
  classical
  have : IsNoetherian S X.carrier := isNoetherian_of_isNoetherianRing_of_finite S X.carrier
  set G : Set X.carrier := {x | ∃ j : ℤ, (d : ℤ) ∣ j ∧ x ∈ X.grade j} with hGdef
  obtain ⟨s, hs⟩ := IsNoetherian.noetherian (Submodule.span S G)
  have hsub : ∀ y ∈ s, ∃ t : Finset X.carrier,
      (↑t : Set X.carrier) ⊆ G ∧ y ∈ Submodule.span S (↑t : Set X.carrier) := fun y hy =>
    Submodule.mem_span_finite_of_mem_span (hs ▸ Submodule.subset_span hy)
  choose! t ht1 ht2 using hsub
  set G₀ : Finset X.carrier := s.biUnion t with hG₀def
  have hG₀G : ∀ x ∈ G₀, x ∈ G := by
    intro x hx
    obtain ⟨y, hy, hxt⟩ := Finset.mem_biUnion.mp hx
    exact ht1 y hy hxt
  have hLG₀ : Submodule.span S G ≤ Submodule.span S (↑G₀ : Set X.carrier) := by
    rw [← hs]
    refine Submodule.span_le.2 fun y hy => ?_
    refine Submodule.span_mono (fun z hz => ?_) (ht2 y hy)
    exact Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨y, hy, Finset.mem_coe.1 hz⟩)
  have hdata : ∀ x ∈ G₀, ∃ (j : ℤ) (C : ℕ), x ∈ X.grade j ∧ j < (C : ℤ) + 1 + j ∧
      ∀ c : ℕ, 0 < c → C ≤ c → ∀ a ∈ 𝒮 c, a • x = 0 := by
    intro x hx
    obtain ⟨j, hjd, hxj⟩ := hG₀G x hx
    obtain ⟨C, hC⟩ := exists_forall_smul_eq_zero_of_isZero 𝒮 f deg hdeg hf hgen hX
      (δ := j) (fun i => dvd_trans (Int.natCast_dvd_natCast.2 (hdvd i)) hjd) hxj
    exact ⟨j, C, hxj, by omega, hC⟩
  choose! jj CC hjjmem _ hCC using hdata
  refine ⟨(G₀.sup fun x => (jj x).toNat + CC x) + 1, fun n hn => ?_⟩
  have hbound : ∀ x ∈ G₀, jj x + (CC x : ℤ) + 1 ≤ (n : ℤ) * d := by
    intro x hx
    have h1 : (jj x).toNat + CC x ≤ G₀.sup fun y => (jj y).toNat + CC y :=
      Finset.le_sup (f := fun y => (jj y).toNat + CC y) hx
    have h2 : jj x ≤ ((jj x).toNat : ℤ) := Int.self_le_toNat _
    have h3 : ((G₀.sup fun y => (jj y).toNat + CC y : ℕ) : ℤ) + 1 ≤ (n : ℤ) := by
      exact_mod_cast hn
    have h4 : (n : ℤ) * 1 ≤ (n : ℤ) * d := by
      have hd' : (1 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
      exact mul_le_mul_of_nonneg_left hd' (by positivity)
    have h5 : (((jj x).toNat + CC x : ℕ) : ℤ) ≤
        ((G₀.sup fun y => (jj y).toNat + CC y : ℕ) : ℤ) := by exact_mod_cast h1
    push_cast at h5
    omega
  rw [eq_bot_iff]
  intro m hm
  have hmL : m ∈ Submodule.span S (↑G₀ : Set X.carrier) :=
    hLG₀ (Submodule.subset_span ⟨(n : ℤ) * d, dvd_mul_left _ _, hm⟩)
  rw [Submodule.mem_span_finset] at hmL
  obtain ⟨cf, -, hcf⟩ := hmL
  have hzero : (gradeComponent 𝒮 X ((n : ℤ) * d) m : X.carrier) = 0 := by
    rw [← hcf, map_sum]
    push_cast
    refine Finset.sum_eq_zero fun x hx => ?_
    refine gradeComponent_smul_eq_zero 𝒮 (hjjmem x hx) (by have := hbound x hx; omega)
      (fun k hk hki a ha => hCC x hx k hk ?_ a ha) (cf x)
    have := hbound x hx
    omega
  rw [gradeComponent_of_mem_same 𝒮 hm] at hzero
  simpa using hzero

/-- **Stacks 0BXF, the hard half of the kernel identification**, in the source's form: a
finitely generated graded module whose associated sheaf vanishes is irrelevant. -/
public theorem isIrrelevant_of_isZero [IsNoetherianRing S]
    {r : ℕ} (f : Fin r → S) (deg : Fin r → ℕ) (hdeg : ∀ i, 0 < deg i)
    (hf : ∀ i, f i ∈ 𝒮 (deg i))
    (hgen : Algebra.adjoin (Veronese.gradeZero 𝒮) (Set.range f) = ⊤)
    {d : ℕ} (hd : 0 < d) (hdvd : ∀ i, deg i ∣ d)
    {X : GradedModuleCat.{u, u, w} 𝒮} [Module.Finite S X.carrier]
    (hX : IsZero (associatedModuleSheaf 𝒮 X.grade)) :
    IsIrrelevant 𝒮 d X :=
  isIrrelevant_of_gradeEventuallyZero 𝒮
    (gradeEventuallyZero_of_isZero_of_adjoin 𝒮 f deg hdeg hf hgen hd hdvd hX)

end Stacks.AlgebraicGeometry.ProjSerreCorrespondence

end
