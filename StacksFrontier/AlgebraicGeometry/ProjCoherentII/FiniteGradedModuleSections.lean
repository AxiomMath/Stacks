module

public import StacksFrontier.AlgebraicGeometry.ProjCoherentII.ShiftedFiniteness
public import StacksFrontier.AlgebraicGeometry.ProjLargeDegrees.Main

/-!
# Finiteness of the truncated section modules over `Proj`

Let `A` be a Noetherian graded ring, let `f_1, …, f_r` be homogeneous generators of `A` over
`A_0` of positive degrees and let `d` be the least common multiple of those degrees. Let `M` be a
finite graded `A`-module, `X = Proj(A)`, `M̃` the associated quasi-coherent `𝒪_X`-module, and
`k ∈ ℤ`. Write

`N' = ⨁_{n ≥ k} H⁰(X, M(n)~)`   and   `N = ⨁_{n ≥ k} H⁰(X, M̃(n))`.

Then:

1. `N'` is a finite `A`-module;
2. `N` is a finite `A`-module;
3. there is a canonical map `N → N'`;
4. if `k` is small enough there is a canonical map `M → N'`;
5. `M_n → N'_n` is an isomorphism for all sufficiently large `n`;
6. `N_n → N'_n` is an isomorphism whenever `d` divides `n`.

## Main results

* `Stacks.AlgebraicGeometry.ProjCoherentII.degreeOpen_lcm_eq_top`: the standard opens of the
  homogeneous elements of degree `d` cover `Proj(A)`.
* `Stacks.AlgebraicGeometry.ProjCoherentII.exists_forall_lt_eq_zero_of_moduleFinite`: a finite
  graded module vanishes in all sufficiently negative degrees.
* `Stacks.AlgebraicGeometry.ProjCoherentII.twistedToShiftedSections_mem_truncation`: the
  comparison map carries `N` into `N'`.
* `Stacks.AlgebraicGeometry.ProjCoherentII.truncatedSections_finite_and_comparison`: the six
  assertions above, for every `k`.

## References

* [Stacks Project, Tag 0B5R](https://stacks.math.columbia.edu/tag/0B5R)
* [Stacks Project, Tag 0B5Q](https://stacks.math.columbia.edu/tag/0B5Q)
* [Stacks Project, Tag 0AG6](https://stacks.math.columbia.edu/tag/0AG6)
* [Stacks Project, Tag 0AG7](https://stacks.math.columbia.edu/tag/0AG7)
* [Stacks Project, Tag 01MQ](https://stacks.math.columbia.edu/tag/01MQ)
* [Stacks Project, Tag 01MR](https://stacks.math.columbia.edu/tag/01MR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace DirectSum
open AlgebraicGeometry.ProjectiveSpectrum.Proj (associatedModuleSheaf twistedGlobalSections)
open Stacks.AlgebraicGeometry.ProjShiftedSections
  (shiftedSectionsComponent globalSectionsModuleMap degreeNToGlobalSections)
open Stacks.AlgebraicGeometry.ProjTwistedSections (twistedGlobalSectionsModule)
open scoped Stacks.GradedLocalization

namespace Stacks.AlgebraicGeometry.ProjCoherentII

universe u

attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj
  Stacks.SheafOfModules.TensorSheafification.structureSheaf

variable {S M : Type u} {σ τ : Type u}
  [CommRing S] [AddCommGroup M] [Module S M]
  [SetLike σ S] [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]
  [SetLike τ M] [AddSubgroupClass τ M] (𝒨 : ℤ → τ) [DirectSum.Decomposition 𝒨]
  [SetLike.GradedSMul 𝒮 𝒨]

/-- Let `f_1, …, f_r` be homogeneous elements of positive degrees generating `A` over `A_0`, and
let `d` be the least common multiple of their degrees. Then the standard opens of the homogeneous
elements of degree `d` cover `Proj(A)`. -/
public theorem degreeOpen_lcm_eq_top {r : ℕ} (f : Fin r → S) (deg : Fin r → ℕ)
    (hdeg : ∀ i, 0 < deg i) (hf : ∀ i, f i ∈ 𝒮 (deg i))
    (hgen : Algebra.adjoin (Stacks.Veronese.gradeZero 𝒮) (Set.range f) = ⊤) :
    AlgebraicGeometry.Proj.degreeOpen 𝒮 (Finset.univ.lcm deg) = ⊤ := by
  have hLpos : 0 < Finset.univ.lcm deg := Nat.pos_of_ne_zero fun h0 => by
    obtain ⟨i, -, hi⟩ := Finset.lcm_eq_zero_iff.mp h0
    exact (hdeg i).ne' hi
  refine top_le_iff.mp <| (AlgebraicGeometry.Proj.iSup_basicOpen_eq_top' 𝒮 f
    (fun i => ⟨deg i, hf i⟩) hgen).ge.trans (iSup_le fun i => ?_)
  exact (AlgebraicGeometry.Proj.basicOpen_le_degreeOpen 𝒮 (hf i)).trans
    (AlgebraicGeometry.Proj.degreeOpen_le_of_dvd 𝒮 (Finset.dvd_lcm (Finset.mem_univ i)) hLpos)

include 𝒮 in
/-- A finite graded module vanishes in all sufficiently negative degrees: if the `ℤ`-graded
module `M` is finite over the `ℕ`-graded ring `A`, there is `k₀` with `M_n = 0` for every
`n < k₀`. -/
public theorem exists_forall_lt_eq_zero_of_moduleFinite [Module.Finite S M] :
    ∃ k₀ : ℤ, ∀ n : ℤ, n < k₀ → ∀ x ∈ 𝒨 n, x = (0 : M) := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := S) (M := M)
  set D : Finset ℤ := s.biUnion fun x => (DirectSum.decompose 𝒨 x).support with hD
  set k₀ : ℤ := if h : D.Nonempty then D.min' h else 0 with hk₀def
  have hk₀ : ∀ j ∈ D, k₀ ≤ j := fun j hj => by
    rw [hk₀def, dite_eq_left ⟨j, hj⟩]
    exact D.min'_le j hj
  let P₀ : AddSubmonoid M :=
    { carrier := {m | ∀ n < k₀, (DirectSum.decompose 𝒨 m n : M) = 0}
      add_mem' := fun {a b} ha hb n hn => by
        rw [DirectSum.decompose_add, DirectSum.add_apply, AddMemClass.coe_add, ha n hn, hb n hn,
          add_zero]
      zero_mem' := fun n _ => by simp }
  have hhom : ∀ {d : ℤ} {x : M}, k₀ ≤ d → x ∈ 𝒨 d → x ∈ P₀ := fun {d x} hd hx n hn =>
    DirectSum.decompose_of_mem_ne 𝒨 hx (by omega)
  have hsupp : ∀ m ∈ P₀, ∀ j ∈ (DirectSum.decompose 𝒨 m).support, k₀ ≤ j := fun m hm j hj =>
    not_lt.mp fun hlt => DFinsupp.mem_support_iff.mp hj (Subtype.ext (hm j hlt))
  let P : Submodule S M :=
    { P₀ with
      smul_mem' := fun c m hm => by
        change c • m ∈ P₀
        rw [← DirectSum.sum_support_decompose 𝒨 m, ← DirectSum.sum_support_decompose 𝒮 c,
          Finset.sum_smul]
        refine AddSubmonoid.sum_mem _ fun i _ => ?_
        rw [Finset.smul_sum]
        refine AddSubmonoid.sum_mem _ fun j hj => hhom ?_
          (SetLike.GradedSMul.smul_mem (A := 𝒮) (B := 𝒨) (DirectSum.decompose 𝒮 c i).2
            (DirectSum.decompose 𝒨 m j).2)
        have := hsupp m hm j hj
        change k₀ ≤ (i : ℤ) + j
        omega }
  have htop : (⊤ : Submodule S M) ≤ P := by
    rw [← hs, Submodule.span_le]
    intro x hx n hn
    by_contra hne
    have hmem : n ∈ D := by
      rw [hD, Finset.mem_biUnion]
      exact ⟨x, hx, DFinsupp.mem_support_iff.mpr fun h => hne (by rw [h, ZeroMemClass.coe_zero])⟩
    exact not_le.mpr hn (hk₀ n hmem)
  refine ⟨k₀, fun n hn x hx => ?_⟩
  rw [← DirectSum.decompose_of_mem_same 𝒨 hx]
  exact htop (Submodule.mem_top : x ∈ ⊤) n hn

/-- The comparison map `⨁_n H⁰(X, M̃(n)) → ⨁_n H⁰(X, M(n)~)` carries the degrees-`≥ k` part
`N = ⨁_{n ≥ k} H⁰(X, M̃(n))` into the degrees-`≥ k` part `N' = ⨁_{n ≥ k} H⁰(X, M(n)~)`. -/
public theorem twistedToShiftedSections_mem_truncation (k : ℤ)
    (x : twistedGlobalSections 𝒮 (associatedModuleSheaf 𝒮 𝒨))
    (hx : x ∈ twistedSectionsTruncation 𝒮 𝒨 k) :
    twistedToShiftedSections 𝒮 𝒨 x ∈ shiftedSectionsTruncation 𝒮 𝒨 k := fun n hn => by
  rw [twistedToShiftedSections_component]
  exact (congrArg (twistedToShiftedComponent 𝒮 𝒨 n) (hx n hn)).trans (map_zero _)

/-- Let `A` be a Noetherian graded ring, `f_1, …, f_r` homogeneous generators of `A` over `A_0` of
positive degrees `deg_1, …, deg_r`, and `d = lcm(deg_i)`. Let `M` be a finite graded `A`-module,
`X = Proj(A)`, `M̃` the associated quasi-coherent `𝒪_X`-module and `k ∈ ℤ` arbitrary, and set

`N' = ⨁_{n ≥ k} H⁰(X, M(n)~)`   and   `N = ⨁_{n ≥ k} H⁰(X, M̃(n))`.

Then, in order:

1. `N'` is a finite `A`-module;
2. `N` is a finite `A`-module;
3. the comparison map `⨁_n H⁰(X, M̃(n)) → ⨁_n H⁰(X, M(n)~)` carries `N` into `N'`, giving the
   canonical map `N → N'`;
4. for `k` small enough the canonical map `M → ⨁_n H⁰(X, M(n)~)` carries `M` into `N'`: there
   is `k₀` such that for every `k' ≤ k₀` it lands in `⨁_{n ≥ k'} H⁰(X, M(n)~)`;
5. `M_n → N'_n` is an isomorphism for all sufficiently large `n`;
6. `N_n → N'_n` is an isomorphism whenever `d` divides `n`. -/
@[stacks 0B5R "all six parts: (1) N' is a finite A-module; (2) N is a finite A-module; (3) the \
canonical map N → N'; (4) the canonical map M → N' for k small enough, i.e. for every k at most \
some k₀; (5) M_n → N'_n is an isomorphism in all sufficiently large degrees; (6) N_n → N'_n is an \
isomorphism for d | n, with d the lcm of the degrees of homogeneous generators of A over A_0; \
(1), (2), (3), (5) and (6) for every k ∈ ℤ"]
public theorem truncatedSections_finite_and_comparison [IsNoetherianRing S] [Module.Finite S M]
    {r : ℕ} (f : Fin r → S) (deg : Fin r → ℕ) (hdeg : ∀ i, 0 < deg i)
    (hf : ∀ i, f i ∈ 𝒮 (deg i))
    (hgen : Algebra.adjoin (Stacks.Veronese.gradeZero 𝒮) (Set.range f) = ⊤)
    (k : ℤ) :
    letI := (globalSectionsModuleMap 𝒮 𝒨).moduleInst
    letI := (twistedGlobalSectionsModule 𝒮 (associatedModuleSheaf 𝒮 𝒨)).moduleInst
    Module.Finite S ((globalSectionsModuleMap 𝒮 𝒨).truncation 𝒮 𝒨 k) ∧
      Module.Finite S ((twistedGlobalSectionsModule 𝒮
        (associatedModuleSheaf 𝒮 𝒨)).truncation 𝒮 (associatedModuleSheaf 𝒮 𝒨) k) ∧
      (∀ x ∈ twistedSectionsTruncation 𝒮 𝒨 k,
        twistedToShiftedSections 𝒮 𝒨 x ∈ shiftedSectionsTruncation 𝒮 𝒨 k) ∧
      (∃ k₀ : ℤ, ∀ k' ≤ k₀, ∀ m : M,
        (globalSectionsModuleMap 𝒮 𝒨).hom m ∈ shiftedSectionsTruncation 𝒮 𝒨 k') ∧
      (∃ n₀ : ℤ, ∀ n : ℤ, n₀ ≤ n → Function.Bijective (degreeNToGlobalSections 𝒮 𝒨 n)) ∧
      (∀ n : ℤ, ((Finset.univ.lcm deg : ℕ) : ℤ) ∣ n →
        Function.Bijective (twistedToShiftedComponent 𝒮 𝒨 n)) :=
  ⟨moduleFinite_shiftedTruncation 𝒮 𝒨 k,
    moduleFinite_twistedTruncation 𝒮 𝒨 k,
    twistedToShiftedSections_mem_truncation 𝒮 𝒨 k,
    (exists_forall_lt_eq_zero_of_moduleFinite 𝒮 𝒨).imp fun _ hk₀ k' hk' =>
      globalSectionsModuleMap_hom_mem_truncation 𝒮 𝒨 k' fun n hn => hk₀ n (hn.trans_le hk'),
    ProjLargeDegrees.exists_bijective_degreeNToGlobalSections_of_isNoetherian 𝒮 𝒨,
    fun _ hdn =>
      bijective_twistedToShiftedComponent 𝒮 𝒨 (degreeOpen_lcm_eq_top 𝒮 f deg hdeg hf hgen) hdn⟩

end Stacks.AlgebraicGeometry.ProjCoherentII

end
