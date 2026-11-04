module

public import StacksFrontier.AlgebraicGeometry.ProjCoherentII.ShiftedFinitenessDegreeOne
public import StacksFrontier.AlgebraicGeometry.ProjCoherentII.ShiftedTruncation
public import StacksFrontier.AlgebraicGeometry.ProjLargeDegreeSections.Basic
public import StacksFrontier.AlgebraicGeometry.ProjLargeDegrees.GradedCoefficients
public import StacksFrontier.AlgebraicGeometry.ProjLargeDegrees.KernelModule

/-!
# The cokernel of `M ⟶ ⨁_n Γ(Proj A, M(n)~)` in the degree-one case

Let `A = ⨁_{d ≥ 0} 𝒜 d` be a graded ring with `𝒜 0` Noetherian, generated over `𝒜 0` by finitely
many elements of `𝒜 1`, and let `M` be a finite graded `A`-module, `X = Proj A`. This file
constructs the *cokernel* half of the homogeneous generating data asked for by
`Stacks.AlgebraicGeometry.ProjLargeDegreeSections.exists_bijective_degreeNToGlobalSections`
([Stacks, Tag 0AG7]).

## Main results

* `Stacks.AlgebraicGeometry.ProjLargeDegrees.exists_irrelevant_pow_mem_image_of_section`: a power
  of the irrelevant ideal carries any one global section of `M(p)~` into the image of `M`.
* `Stacks.AlgebraicGeometry.ProjLargeDegrees.exists_fin_homogeneous_span`: a finite family of
  homogeneous elements of `N'`, read as a `Fin`-indexed family of sections.
* `Stacks.AlgebraicGeometry.ProjLargeDegrees.exists_homogeneous_section_span`: the generation
  statement, with the degrees bounded below by `0`.
* `Stacks.AlgebraicGeometry.ProjLargeDegrees.exists_cokernel_data`: **the cokernel half of
  Tag 0AG7's hypotheses.**

## References

* [Stacks Project, Tag 0AG7](https://stacks.math.columbia.edu/tag/0AG7)
* [Stacks Project, Tag 0B5R](https://stacks.math.columbia.edu/tag/0B5R)
* [Stacks Project, Tag 01MR](https://stacks.math.columbia.edu/tag/01MR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace DirectSum
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjShiftedSections
  (shiftedSectionsComponent shiftedModuleGlobalSections shiftedModuleGlobalSectionsGrading
    globalSectionsModuleMap degreeNToGlobalSections homogeneousScalarGlobalSections
    homogeneousScalarGlobalSections_zero_right homogeneousScalarGlobalSections_zero_left
    GlobalSectionsModuleMap)
open Stacks.AlgebraicGeometry.ProjLargeDegreeSections (ofDegreeEq)
open Stacks.GradedModule (shiftedGrading)
open scoped Stacks.GradedLocalization

namespace Stacks.AlgebraicGeometry.ProjLargeDegrees

universe u

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

variable {A : Type u} {M : Type u} {σ : Type u} {τ : Type u}
  [CommRing A] [AddCommGroup M] [Module A M]
  [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
  [SetLike τ M] [AddSubgroupClass τ M] (𝒨 : ℤ → τ) [DirectSum.Decomposition 𝒨]
  [SetLike.GradedSMul 𝒜 𝒨]

omit [DirectSum.Decomposition 𝒨] in
/-- Transporting a global section along an equality of degrees does not change its image in the
direct sum of all the degrees. -/
theorem of_ofDegreeEq {p q : ℤ} (h : p = q) (z : shiftedSectionsComponent 𝒜 𝒨 p) :
    DirectSum.of (fun k : ℤ => shiftedSectionsComponent 𝒜 𝒨 k) q (ofDegreeEq 𝒜 𝒨 h z) =
      DirectSum.of (fun k : ℤ => shiftedSectionsComponent 𝒜 𝒨 k) p z := by
  subst h
  rfl

omit [DirectSum.Decomposition 𝒨] in
/-- Transporting the zero section along an equality of degrees gives the zero section. -/
theorem ofDegreeEq_zero {p q : ℤ} (h : p = q) :
    ofDegreeEq 𝒜 𝒨 h (0 : shiftedSectionsComponent 𝒜 𝒨 p) = 0 := by
  subst h
  rfl

omit [DirectSum.Decomposition 𝒨] in
/-- The degree-`p` component of the tautological grading of `⨁_n Γ(X, M(n)~)` is read off by the
inclusion of the degree-`p` summand. -/
theorem gradedProj_shiftedModuleGlobalSectionsGrading (p : ℤ)
    (z : shiftedModuleGlobalSections 𝒜 𝒨) :
    gradedProj (shiftedModuleGlobalSectionsGrading 𝒜 𝒨) p z =
      DirectSum.of (fun k : ℤ => shiftedSectionsComponent 𝒜 𝒨 k) p
        (DirectSum.component ℤ ℤ (fun k : ℤ => shiftedSectionsComponent 𝒜 𝒨 k) p z) :=
  gradedProj_rangeGrading (V := fun k : ℤ => shiftedSectionsComponent 𝒜 𝒨 k)
    (shiftedModuleGlobalSectionsGrading 𝒜 𝒨) rfl p z

/-- The image of a single summand lies in the degree-`≥ k` truncation as soon as its degree is at
least `k`. -/
theorem of_mem_truncation {k n : ℤ} (hkn : k ≤ n) (s : shiftedSectionsComponent 𝒜 𝒨 n) :
    letI := (globalSectionsModuleMap 𝒜 𝒨).moduleInst
    (DirectSum.of (fun j : ℤ => shiftedSectionsComponent 𝒜 𝒨 j) n s :
        shiftedModuleGlobalSections 𝒜 𝒨) ∈
      (globalSectionsModuleMap 𝒜 𝒨).truncation 𝒜 𝒨 k := by
  let := (globalSectionsModuleMap 𝒜 𝒨).moduleInst
  rw [GlobalSectionsModuleMap.mem_truncation]
  intro q hq
  exact DirectSum.of_eq_of_ne _ _ _ (show q ≠ n by omega)

/-- **A finite family of homogeneous elements of `⨁_n Γ(X, M(n)~)`, reindexed by `Fin` and read
as a family of sections.** -/
theorem exists_fin_homogeneous_span {ι : Type*} [Fintype ι] (dy : ι → ℤ)
    (Y : ι → shiftedModuleGlobalSections 𝒜 𝒨)
    (hY : ∀ j, Y j ∈ shiftedModuleGlobalSectionsGrading 𝒜 𝒨 (dy j))
    (hdy : ∀ j, (0 : ℤ) ≤ dy j) :
    letI := (globalSectionsModuleMap 𝒜 𝒨).moduleInst
    ∃ (cq : ℕ) (dy' : Fin cq → ℤ)
      (y' : (k : Fin cq) → shiftedSectionsComponent 𝒜 𝒨 (dy' k)),
      (∀ k, (0 : ℤ) ≤ dy' k) ∧
        Submodule.span A (Set.range Y) ≤
          Submodule.span A (Set.range fun k =>
            (DirectSum.of (fun j : ℤ => shiftedSectionsComponent 𝒜 𝒨 j) (dy' k) (y' k) :
              shiftedModuleGlobalSections 𝒜 𝒨)) := by
  classical
  let := (globalSectionsModuleMap 𝒜 𝒨).moduleInst
  have hof : ∀ j : ι,
      DirectSum.of (fun k : ℤ => shiftedSectionsComponent 𝒜 𝒨 k) (dy j)
          (DirectSum.component ℤ ℤ (fun k : ℤ => shiftedSectionsComponent 𝒜 𝒨 k) (dy j)
            (Y j)) = Y j := by
    intro j
    rw [← gradedProj_shiftedModuleGlobalSectionsGrading,
      gradedProj_eq_self (shiftedModuleGlobalSectionsGrading 𝒜 𝒨) (hY j)]
  refine ⟨Fintype.card ι, fun k => dy ((Fintype.equivFin ι).symm k),
    fun k => DirectSum.component ℤ ℤ (fun j : ℤ => shiftedSectionsComponent 𝒜 𝒨 j)
      (dy ((Fintype.equivFin ι).symm k)) (Y ((Fintype.equivFin ι).symm k)),
    fun k => hdy _, Submodule.span_le.mpr ?_⟩
  rintro - ⟨j, rfl⟩
  obtain ⟨k, rfl⟩ : ∃ k, (Fintype.equivFin ι).symm k = j :=
    ⟨Fintype.equivFin ι j, Equiv.symm_apply_apply _ _⟩
  exact Submodule.subset_span ⟨k, hof _⟩

section DegreeOne

variable [IsNoetherianRing (𝒜 0)] {nx : ℕ} (xg : Fin (nx + 1) → A) (hxg : ∀ i, xg i ∈ 𝒜 1)
  (hxgen : Algebra.adjoin (𝒜 0) (Set.range xg) = ⊤)

include hxg hxgen

/-- **A power of the irrelevant ideal carries a global section of `M(p)~` into the image of `M`**
under the canonical map of Equation 01MR. -/
theorem exists_irrelevant_pow_mem_image_of_section [Module.Finite A M] (p : ℤ)
    (s : shiftedSectionsComponent 𝒜 𝒨 p) :
    ∃ N : ℕ, ∀ (i : ℕ) (a : 𝒜 i),
      (a : A) ∈ (HomogeneousIdeal.irrelevant 𝒜).toIdeal ^ N →
        ∃ m : 𝒨 ((i : ℤ) + p),
          homogeneousScalarGlobalSections 𝒜 𝒨 i p a s =
            degreeNToGlobalSections 𝒜 𝒨 ((i : ℤ) + p) m := by
  classical
  let := (globalSectionsModuleMap 𝒜 𝒨).moduleInst
  have : IsNoetherianRing A := Stacks.ProjCoherentDegreeOne.isNoetherianRing 𝒜 xg hxg hxgen
  have hspan : Ideal.span (Set.range xg) = (HomogeneousIdeal.irrelevant 𝒜).toIdeal :=
    (generates_algebra_iff_generates_irrelevant 𝒜 xg (fun _ => 1) (fun _ => Nat.one_pos)
      hxg).mp hxgen
  have hcover : ∀ y : ProjectiveSpectrum.top 𝒜,
      ∃ i, xg i ∈ y.asHomogeneousIdeal.toIdeal.primeCompl := by
    intro y
    by_contra hy
    have hle : Ideal.span (Set.range xg) ≤ y.asHomogeneousIdeal.toIdeal :=
      Ideal.span_le.mpr <| Set.range_subset_iff.mpr fun i =>
        Classical.byContradiction fun h => hy ⟨i, h⟩
    exact y.not_irrelevant_le ((HomogeneousIdeal.irrelevant_le 𝒜).mpr fun k hk g hg =>
      hle (hspan ▸ mem_irrelevant_of_mem_of_pos 𝒜 hg hk))
  set J : Ideal A :=
    Submodule.comap
      (LinearMap.toSpanSingleton A (shiftedModuleGlobalSections 𝒜 𝒨)
        (DirectSum.of (fun k : ℤ => shiftedSectionsComponent 𝒜 𝒨 k) p s))
      (LinearMap.range (globalSectionsModuleMap 𝒜 𝒨).hom) with hJ
  have hmemJ : ∀ a : A, a ∈ J ↔
      a • (DirectSum.of (fun k : ℤ => shiftedSectionsComponent 𝒜 𝒨 k) p s :
          shiftedModuleGlobalSections 𝒜 𝒨) ∈
        LinearMap.range (globalSectionsModuleMap 𝒜 𝒨).hom := fun a => Iff.rfl
  have hgenJ : ∀ i : Fin (nx + 1), xg i ∈ J.radical := by
    intro i
    obtain ⟨K, m, hm, hKm⟩ :=
      exists_pow_smul_eq_degreeNToGlobalSections 𝒜 𝒨 xg hxg hcover s i
    refine ⟨K, (hmemJ _).mpr ⟨m, ?_⟩⟩
    rw [GlobalSectionsModuleMap.smul_of 𝒜 𝒨 (globalSectionsModuleMap 𝒜 𝒨) K p
        ⟨xg i ^ K, by simpa using SetLike.pow_mem_graded K (hxg i)⟩ s, hKm]
    exact (globalSectionsModuleMap 𝒜 𝒨).map_homogeneous ((K : ℤ) + p) ⟨m, hm⟩
  obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg
    (hspan ▸ Ideal.span_le.mpr (Set.range_subset_iff.mpr hgenJ))
    (Ideal.fg_of_isNoetherianRing _)
  refine ⟨N, fun i a ha => ?_⟩
  obtain ⟨z, hz⟩ := (hmemJ (a : A)).mp (hN ha)
  refine ⟨DirectSum.decompose 𝒨 z ((i : ℤ) + p), ?_⟩
  have hc := ProjCoherentII.globalSectionsModuleMap_hom_component 𝒜 𝒨 z ((i : ℤ) + p)
  rwa [hz, GlobalSectionsModuleMap.smul_of 𝒜 𝒨 (globalSectionsModuleMap 𝒜 𝒨) i p a s,
    ← DirectSum.apply_eq_component, DirectSum.of_eq_same] at hc

/-- **The degree-`≥ 0` part of `⨁_n Γ(X, M(n)~)` is generated by finitely many homogeneous
sections, in degrees `≥ 0`.** -/
theorem exists_homogeneous_section_span [Module.Finite A M] :
    letI := (globalSectionsModuleMap 𝒜 𝒨).moduleInst
    ∃ (cq : ℕ) (dy : Fin cq → ℤ)
      (y : (k : Fin cq) → shiftedSectionsComponent 𝒜 𝒨 (dy k)),
      (∀ k, 0 ≤ dy k) ∧
        (globalSectionsModuleMap 𝒜 𝒨).truncation 𝒜 𝒨 0 ≤
          Submodule.span A (Set.range fun k =>
            (DirectSum.of (fun j : ℤ => shiftedSectionsComponent 𝒜 𝒨 j) (dy k) (y k) :
              shiftedModuleGlobalSections 𝒜 𝒨)) := by
  classical
  let := (globalSectionsModuleMap 𝒜 𝒨).moduleInst
  have hfin := ProjCoherentII.moduleFinite_shiftedTruncation_of_degreeOne 𝒜 xg hxg hxgen 𝒨 0
  obtain ⟨T, hT⟩ : ((globalSectionsModuleMap 𝒜 𝒨).truncation 𝒜 𝒨 0).FG :=
    Module.Finite.iff_fg.mp hfin
  have hTmem : ∀ v ∈ T, v ∈ (globalSectionsModuleMap 𝒜 𝒨).truncation 𝒜 𝒨 0 :=
    fun v hv => hT ▸ Submodule.subset_span hv
  have hsupp : ∀ v ∈ T,
      ∀ q ∈ (DirectSum.decompose (shiftedModuleGlobalSectionsGrading 𝒜 𝒨) v).support,
        (0 : ℤ) ≤ q := by
    intro v hv q hq
    by_contra hlt
    refine notMem_support_of_gradedProj_eq_zero (shiftedModuleGlobalSectionsGrading 𝒜 𝒨) ?_ hq
    rw [gradedProj_shiftedModuleGlobalSectionsGrading,
      (GlobalSectionsModuleMap.mem_truncation 𝒜 𝒨 (globalSectionsModuleMap 𝒜 𝒨) 0 v).mp
        (hTmem v hv) q (by omega),
      map_zero]
  obtain ⟨cq, dy, y, hdy0, hle⟩ := exists_fin_homogeneous_span 𝒜 𝒨
    (ι := Σ v : {z // z ∈ T},
      {q : ℤ // q ∈ (DirectSum.decompose (shiftedModuleGlobalSectionsGrading 𝒜 𝒨)
        (v : shiftedModuleGlobalSections 𝒜 𝒨)).support})
    (fun j => (j.2 : ℤ))
    (fun j => gradedProj (shiftedModuleGlobalSectionsGrading 𝒜 𝒨) (j.2 : ℤ)
      (j.1 : shiftedModuleGlobalSections 𝒜 𝒨))
    (fun j => (DirectSum.decompose (shiftedModuleGlobalSectionsGrading 𝒜 𝒨)
      (j.1 : shiftedModuleGlobalSections 𝒜 𝒨) (j.2 : ℤ)).2)
    (fun j => hsupp _ j.1.2 _ j.2.2)
  have hbase : (globalSectionsModuleMap 𝒜 𝒨).truncation 𝒜 𝒨 0 ≤
      Submodule.span A (Set.range fun j : Σ v : {z // z ∈ T},
        {q : ℤ // q ∈ (DirectSum.decompose (shiftedModuleGlobalSectionsGrading 𝒜 𝒨)
          (v : shiftedModuleGlobalSections 𝒜 𝒨)).support} =>
        gradedProj (shiftedModuleGlobalSectionsGrading 𝒜 𝒨) (j.2 : ℤ)
          (j.1 : shiftedModuleGlobalSections 𝒜 𝒨)) := by
    rw [← hT, Submodule.span_le]
    intro v hv
    rw [← sum_support_gradedProj (shiftedModuleGlobalSectionsGrading 𝒜 𝒨) v]
    exact Submodule.sum_mem _ fun q hq =>
      Submodule.subset_span ⟨⟨⟨v, Finset.mem_coe.mp hv⟩, ⟨q, hq⟩⟩, rfl⟩
  exact ⟨cq, dy, y, hdy0, hbase.trans hle⟩

/-- **The cokernel half of the hypotheses of [Stacks, Tag 0AG7], under degree-one generation.**
For `𝒜 0` Noetherian, `A` generated in degree one over `𝒜 0` by a finite family, and `M` a finite
graded `A`-module, there are finitely many global sections `y k` of `M(dy k)~` which generate
every `Γ(X, M(n)~)` with `n ≥ dy k` for all `k` with homogeneous coefficients, and each of which
a power of the irrelevant ideal carries into the image of `M`. -/
theorem exists_cokernel_data [Module.Finite A M] :
    ∃ (cq : ℕ) (dy : Fin cq → ℤ) (Ny : Fin cq → ℕ)
      (y : (k : Fin cq) → shiftedSectionsComponent 𝒜 𝒨 (dy k)),
      (∀ (k : Fin cq) (i : ℕ) (a : 𝒜 i),
        (a : A) ∈ (HomogeneousIdeal.irrelevant 𝒜).toIdeal ^ Ny k →
          ∃ m : 𝒨 ((i : ℤ) + dy k),
            homogeneousScalarGlobalSections 𝒜 𝒨 i (dy k) a (y k) =
              degreeNToGlobalSections 𝒜 𝒨 ((i : ℤ) + dy k) m) ∧
      ∀ (n : ℤ) (hn : ∀ k, dy k ≤ n) (s : shiftedSectionsComponent 𝒜 𝒨 n),
        ∃ (m : 𝒨 n) (a : (k : Fin cq) → 𝒜 (n - dy k).toNat),
          s = degreeNToGlobalSections 𝒜 𝒨 n m +
            ∑ k, ofDegreeEq 𝒜 𝒨 (show (((n - dy k).toNat : ℤ) + dy k) = n by
                have := hn k; omega)
              (homogeneousScalarGlobalSections 𝒜 𝒨 ((n - dy k).toNat) (dy k) (a k) (y k)) := by
  classical
  let := (globalSectionsModuleMap 𝒜 𝒨).moduleInst
  let := (globalSectionsModuleMap 𝒜 𝒨).gradedSMul
  obtain ⟨cq, dy, y, hdy0, hspan⟩ := exists_homogeneous_section_span 𝒜 𝒨 xg hxg hxgen
  choose Ny hNy using fun k : Fin cq =>
    exists_irrelevant_pow_mem_image_of_section 𝒜 𝒨 xg hxg hxgen (dy k) (y k)
  rcases Nat.eq_zero_or_pos cq with hcq | hcq
  · subst hcq
    have hzero : (globalSectionsModuleMap 𝒜 𝒨).truncation 𝒜 𝒨 0 ≤ ⊥ := by
      refine hspan.trans (Submodule.span_le.mpr ?_)
      rintro - ⟨k, rfl⟩
      exact absurd k.2 (by omega)
    refine ⟨1, fun _ => 0, fun _ => 0, fun _ => 0, fun k i a _ => ⟨0, ?_⟩, fun n hn s => ?_⟩
    · rw [homogeneousScalarGlobalSections_zero_right, map_zero]
    · refine ⟨0, fun _ => 0, ?_⟩
      have hn0 : (0 : ℤ) ≤ n := hn 0
      have hs0 : (DirectSum.of (fun j : ℤ => shiftedSectionsComponent 𝒜 𝒨 j) n s :
          shiftedModuleGlobalSections 𝒜 𝒨) = 0 := by
        simpa using hzero (of_mem_truncation 𝒜 𝒨 hn0 s)
      have hs : s = 0 :=
        DirectSum.of_injective (β := fun j : ℤ => shiftedSectionsComponent 𝒜 𝒨 j) n
          (hs0.trans (map_zero _).symm)
      rw [hs, map_zero, zero_add]
      refine (Finset.sum_eq_zero fun k _ => ?_).symm
      rw [homogeneousScalarGlobalSections_zero_left, ofDegreeEq_zero]
  · refine ⟨cq, dy, Ny, y, hNy, fun n hn s => ⟨0, ?_⟩⟩
    have hn0 : (0 : ℤ) ≤ n := le_trans (hdy0 ⟨0, hcq⟩) (hn ⟨0, hcq⟩)
    have hmem : (DirectSum.of (fun j : ℤ => shiftedSectionsComponent 𝒜 𝒨 j) n s :
        shiftedModuleGlobalSections 𝒜 𝒨) ∈
        Submodule.span A (Set.range fun k =>
          (DirectSum.of (fun j : ℤ => shiftedSectionsComponent 𝒜 𝒨 j) (dy k) (y k) :
            shiftedModuleGlobalSections 𝒜 𝒨)) :=
      hspan (of_mem_truncation 𝒜 𝒨 hn0 s)
    have hhom : ∀ k : Fin cq,
        (DirectSum.of (fun j : ℤ => shiftedSectionsComponent 𝒜 𝒨 j) (dy k) (y k) :
            shiftedModuleGlobalSections 𝒜 𝒨) ∈
          shiftedModuleGlobalSectionsGrading 𝒜 𝒨 (dy k) := fun k =>
      (DirectSum.mem_rangeGrading ℤ (fun j : ℤ => shiftedSectionsComponent 𝒜 𝒨 j) (dy k)
        _).mpr ⟨y k, rfl⟩
    obtain ⟨a, ha⟩ := exists_homogeneous_smul_coeffs 𝒜 (shiftedModuleGlobalSectionsGrading 𝒜 𝒨)
      (fun k => (DirectSum.of (fun j : ℤ => shiftedSectionsComponent 𝒜 𝒨 j) (dy k) (y k) :
        shiftedModuleGlobalSections 𝒜 𝒨))
      dy (fun k => (n - dy k).toNat) hhom (fun k => by have := hn k; omega)
      ((DirectSum.mem_rangeGrading ℤ (fun j : ℤ => shiftedSectionsComponent 𝒜 𝒨 j) n _).mpr
        ⟨s, rfl⟩)
      hmem
    refine ⟨a, ?_⟩
    rw [map_zero, zero_add]
    refine DirectSum.of_injective (β := fun j : ℤ => shiftedSectionsComponent 𝒜 𝒨 j) n ?_
    rw [map_sum]
    refine ha.trans (Finset.sum_congr rfl fun k _ => ?_)
    rw [GlobalSectionsModuleMap.smul_of 𝒜 𝒨 (globalSectionsModuleMap 𝒜 𝒨)
      ((n - dy k).toNat) (dy k) (a k) (y k)]
    exact (of_ofDegreeEq 𝒜 𝒨 _ _).symm

end DegreeOne

end Stacks.AlgebraicGeometry.ProjLargeDegrees

end
