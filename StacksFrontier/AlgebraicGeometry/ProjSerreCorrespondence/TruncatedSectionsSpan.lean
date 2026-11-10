module

public import StacksFrontier.AlgebraicGeometry.ProjCoherentII.ShiftedFinitenessDegreeOne
public import StacksFrontier.AlgebraicGeometry.ProjCoherentII.FiniteGradedModuleSections
public import StacksFrontier.AlgebraicGeometry.ProjSerreCorrespondence.DegreewiseIsoModSerre
public import StacksFrontier.AlgebraicGeometry.ProjSerreCorrespondence.EssentiallySurjective
public import StacksFrontier.AlgebraicGeometry.ProjSerreCorrespondence.TwistedShiftedGraded

/-!
# The span `M ⟶ N' ⟵ N` of Stacks 0B5R as morphisms of graded modules

Let `A` be a graded ring which is Noetherian as a ring, let `M` be a finite graded `A`-module,
`X = Proj A` and `k ∈ ℤ`, and write

`N' = ⨁_{n ≥ k} Γ(X, M(n)~)`   and   `N = ⨁_{n ≥ k} Γ(X, M̃(n))`

as in Stacks 0B5R. Parts (3) and (4) of that tag produce the two canonical maps `N → N'` and
`M → N'`, and parts (5) and (6) say that they are bijective in large degrees, respectively in the
degrees divisible by the source's `d`. This file realises `N'` as an object of the category of
graded modules and the two maps as morphisms of graded modules, and restates parts (5) and (6) at
these morphisms. The object `N` is
`Stacks.AlgebraicGeometry.ProjSerreCorrespondence.truncatedTwistedSectionsObj` at `M̃`, which is
finite by clause (4) of Stacks 0B5Q.

## Main definitions

* `shiftedTruncatedSectionsObj`: `N'` as an object of the category of graded modules.
* `truncatedTwistedToShiftedMor`: Stacks 0B5R (3) as a morphism of graded modules, `N ⟶ N'`.
* `moduleToShiftedTruncation`: Stacks 0B5R (4) as a morphism of graded modules, `M ⟶ N'`.

## Main results

* `moduleFinite_shiftedTruncatedSectionsObj`: `N'` is a finite `A`-module, part (1) of
  Stacks 0B5R.
* `eq_zero_of_moduleToShiftedTruncation_eq_zero` and `exists_moduleToShiftedTruncation_eq`: in a
  degree where the map of Tag 0AG2 is bijective, `M ⟶ N'` is injective on the homogeneous piece
  and its image contains the homogeneous piece of the target; this is part (5).
* `eq_zero_of_truncatedTwistedToShiftedMor_eq_zero` and `exists_truncatedTwistedToShiftedMor_eq`:
  the same for `N ⟶ N'` in a degree where the degreewise comparison is bijective, which is
  part (6).

## References

* [Stacks Project, Tag 0B5R](https://stacks.math.columbia.edu/tag/0B5R)
* [Stacks Project, Tag 0AG2](https://stacks.math.columbia.edu/tag/0AG2)
* [Stacks Project, Tag 01MQ](https://stacks.math.columbia.edu/tag/01MQ)
* [Stacks Project, Tag 01MR](https://stacks.math.columbia.edu/tag/01MR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry DirectSum
open AlgebraicGeometry.ProjectiveSpectrum.Proj (associatedModuleSheaf twistedGlobalSections)
open Stacks.AlgebraicGeometry.ProjCoherentII (twistedToShiftedComponent twistedToShiftedSections
  twistedToShiftedSections_mem_truncation
  globalSectionsModuleMap_hom_mem_truncation)
open Stacks.AlgebraicGeometry.ProjShiftedSections (shiftedSectionsComponent
  shiftedModuleGlobalSections shiftedModuleGlobalSectionsGrading globalSectionsModuleMap
  degreeNToGlobalSections homogeneousScalarGlobalSections)
open Stacks.AlgebraicGeometry.ProjTrivialization (projRingSheaf)
open Stacks.AlgebraicGeometry.ProjTwistedSections (twistedSectionsComponent
  twistedGlobalSectionsGrading twistedGlobalSectionsModule
  gradedActionTruncation_eq_truncationAbove)
open Stacks.AlgebraicGeometry.ProjSheafFunctoriality
open Stacks.GradedModule (truncationAbove truncationAboveGrading mem_truncationAbove_of_mem
  mem_truncationAboveGrading_iff)
open scoped Stacks.GradedLocalization

namespace Stacks.AlgebraicGeometry.ProjSerreCorrespondence

universe u

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {S : Type u} {σ : Type u} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

section Bare

variable {M : Type u} {τ : Type u} [AddCommGroup M] [Module S M]
  [SetLike τ M] [AddSubgroupClass τ M] (𝒨 : ℤ → τ) [DirectSum.Decomposition 𝒨]
  [SetLike.GradedSMul 𝒮 𝒨]

/-! ### The two spellings of `N'` -/

/-- **The two spellings of `N' = ⨁_{n ≥ k} Γ(X, M(n)~)` are the same submodule** of
`⨁_{n ∈ ℤ} Γ(X, M(n)~)`: the one cut out by the vanishing of the summands below `k`, and the
truncation of the tautological grading. -/
public theorem shiftedTruncation_eq_truncationAbove (k : ℤ) :
    letI := (globalSectionsModuleMap 𝒮 𝒨).moduleInst
    letI := (globalSectionsModuleMap 𝒮 𝒨).gradedSMul
    (globalSectionsModuleMap 𝒮 𝒨).truncation 𝒮 𝒨 k =
      truncationAbove 𝒮 (shiftedModuleGlobalSectionsGrading 𝒮 𝒨) k := by
  let := (globalSectionsModuleMap 𝒮 𝒨).moduleInst
  let := (globalSectionsModuleMap 𝒮 𝒨).gradedSMul
  exact SetLike.coe_injective
    (gradedActionTruncation_eq_truncationAbove 𝒮 (homogeneousScalarGlobalSections 𝒮 𝒨)
      ((globalSectionsModuleMap 𝒮 𝒨).smul_of 𝒮 𝒨) k)

/-- Membership in the truncation of the shifted global sections is the vanishing of all
components in degrees `< k`. -/
public theorem mem_truncationAbove_shiftedModuleGlobalSectionsGrading_iff (k : ℤ)
    (x : shiftedModuleGlobalSections 𝒮 𝒨) :
    letI := (globalSectionsModuleMap 𝒮 𝒨).moduleInst
    letI := (globalSectionsModuleMap 𝒮 𝒨).gradedSMul
    x ∈ truncationAbove 𝒮 (shiftedModuleGlobalSectionsGrading 𝒮 𝒨) k ↔
      ∀ n : ℤ, n < k →
        DirectSum.component ℤ ℤ (fun j : ℤ => shiftedSectionsComponent 𝒮 𝒨 j) n x = 0 := by
  let := (globalSectionsModuleMap 𝒮 𝒨).moduleInst
  let := (globalSectionsModuleMap 𝒮 𝒨).gradedSMul
  rw [← shiftedTruncation_eq_truncationAbove 𝒮 𝒨 k]
  exact Iff.rfl

/-- Membership in the truncation of the twisted global sections is the vanishing of all
components in degrees `< k`. -/
public theorem mem_truncationAbove_twistedGlobalSectionsGrading_iff
    (F : SheafOfModules.{u} (projRingSheaf 𝒮)) (k : ℤ) (x : twistedGlobalSections 𝒮 F) :
    letI := (twistedGlobalSectionsModule 𝒮 F).moduleInst
    letI := (twistedGlobalSectionsModule 𝒮 F).gradedSMul
    x ∈ truncationAbove 𝒮 (twistedGlobalSectionsGrading 𝒮 F) k ↔
      ∀ n : ℤ, n < k →
        DirectSum.component ℤ ℤ (fun j : ℤ => twistedSectionsComponent 𝒮 F j) n x = 0 := by
  let := (twistedGlobalSectionsModule 𝒮 F).moduleInst
  let := (twistedGlobalSectionsModule 𝒮 F).gradedSMul
  rw [← truncation_eq_truncationAbove 𝒮 F k]
  exact Iff.rfl

/-! ### Two degreewise formulas -/

/-- The canonical map of Equation 01MR sends a homogeneous element of degree `i` to the
degree-`i` summand, by the map of Tag 0AG2. -/
public theorem globalSectionsModuleMap_hom_of_mem (i : ℤ) (m : M) (hm : m ∈ 𝒨 i) :
    letI := (globalSectionsModuleMap 𝒮 𝒨).moduleInst
    (globalSectionsModuleMap 𝒮 𝒨).hom m =
      DirectSum.of (fun j : ℤ => shiftedSectionsComponent 𝒮 𝒨 j) i
        (degreeNToGlobalSections 𝒮 𝒨 i ⟨m, hm⟩) :=
  (globalSectionsModuleMap 𝒮 𝒨).map_homogeneous i ⟨m, hm⟩

/-- **The comparison of Stacks 0B5R (3) is degree-preserving**: it carries the degree-`i` piece of
the twisted global sections to the degree-`i` piece of the shifted ones, both tautologically
graded. -/
public theorem twistedToShiftedSections_mem_grading (i : ℤ)
    (x : twistedGlobalSections 𝒮 (associatedModuleSheaf 𝒮 𝒨))
    (hx : x ∈ twistedGlobalSectionsGrading 𝒮 (associatedModuleSheaf 𝒮 𝒨) i) :
    twistedToShiftedSections 𝒮 𝒨 x ∈ shiftedModuleGlobalSectionsGrading 𝒮 𝒨 i := by
  obtain ⟨t, rfl⟩ :=
    (DirectSum.mem_rangeGrading ℤ
      (fun j : ℤ => twistedSectionsComponent 𝒮 (associatedModuleSheaf 𝒮 𝒨) j) i x).mp hx
  exact (DirectSum.mem_rangeGrading ℤ (fun j : ℤ => shiftedSectionsComponent 𝒮 𝒨 j) i _).mpr
    ⟨twistedToShiftedComponent 𝒮 𝒨 i t, twistedToShiftedSections_of 𝒮 𝒨 i t⟩

/-! ### `N'` as an object of the category of graded modules -/

/-- **`N' = ⨁_{n ≥ k} Γ(X, M(n)~)` as an object of the category of graded modules.** The module
structure is the one of Equation 01MR, the grading the truncation of the tautological grading of
`⨁_{n ∈ ℤ} Γ(X, M(n)~)`. -/
public def shiftedTruncatedSectionsObj (k : ℤ) : GradedModuleCat.{u, u, u} 𝒮 :=
  letI := (globalSectionsModuleMap 𝒮 𝒨).moduleInst
  letI := (globalSectionsModuleMap 𝒮 𝒨).gradedSMul
  { carrier := ↥(truncationAbove 𝒮 (shiftedModuleGlobalSectionsGrading 𝒮 𝒨) k)
    grade := truncationAboveGrading 𝒮 (shiftedModuleGlobalSectionsGrading 𝒮 𝒨) k }

/-- The grading of `shiftedTruncatedSectionsObj` is the truncation of the tautological grading of
the shifted global sections. -/
@[simp]
public theorem grade_shiftedTruncatedSectionsObj (k : ℤ) :
    letI := (globalSectionsModuleMap 𝒮 𝒨).moduleInst
    letI := (globalSectionsModuleMap 𝒮 𝒨).gradedSMul
    (shiftedTruncatedSectionsObj 𝒮 𝒨 k).grade =
      truncationAboveGrading 𝒮 (shiftedModuleGlobalSectionsGrading 𝒮 𝒨) k := rfl

/-- **Part (1) of Stacks 0B5R at this spelling of the truncation**: `N'` is a finite
`A`-module. -/
public theorem moduleFinite_shiftedTruncatedSectionsObj [IsNoetherianRing S] [Module.Finite S M]
    (k : ℤ) :
    Module.Finite S (shiftedTruncatedSectionsObj 𝒮 𝒨 k).carrier := by
  let := (globalSectionsModuleMap 𝒮 𝒨).moduleInst
  let := (globalSectionsModuleMap 𝒮 𝒨).gradedSMul
  have := ProjCoherentII.moduleFinite_shiftedTruncation 𝒮 𝒨 k
  exact Module.Finite.equiv (LinearEquiv.ofEq _ _ (shiftedTruncation_eq_truncationAbove 𝒮 𝒨 k))

/-! ### Part (3) as a morphism of graded modules -/

/-- **Stacks 0B5R (3) as a morphism of graded modules**, `N ⟶ N'`. The underlying map is the
`A`-linear comparison `Stacks.AlgebraicGeometry.ProjCoherentII.twistedToShiftedLinearMap`,
corestricted to `N'`. -/
public def truncatedTwistedToShiftedMor (k : ℤ) :
    truncatedTwistedSectionsObj 𝒮 (associatedModuleSheaf 𝒮 𝒨) k ⟶
      shiftedTruncatedSectionsObj 𝒮 𝒨 k :=
  letI := (twistedGlobalSectionsModule 𝒮 (associatedModuleSheaf 𝒮 𝒨)).moduleInst
  letI := (twistedGlobalSectionsModule 𝒮 (associatedModuleSheaf 𝒮 𝒨)).gradedSMul
  letI := (globalSectionsModuleMap 𝒮 𝒨).moduleInst
  letI := (globalSectionsModuleMap 𝒮 𝒨).gradedSMul
  { toLinearMap := truncationAboveMap 𝒮
      (twistedGlobalSectionsGrading 𝒮 (associatedModuleSheaf 𝒮 𝒨))
      (shiftedModuleGlobalSectionsGrading 𝒮 𝒨)
      (ProjCoherentII.twistedToShiftedLinearMap 𝒮 𝒨
        (ProjCoherentII.twistedToShiftedSections_smul 𝒮 𝒨))
      (twistedToShiftedSections_mem_grading 𝒮 𝒨) k
    map_grade := truncationAboveMap_mem_grading 𝒮
      (twistedGlobalSectionsGrading 𝒮 (associatedModuleSheaf 𝒮 𝒨))
      (shiftedModuleGlobalSectionsGrading 𝒮 𝒨) _
      (twistedToShiftedSections_mem_grading 𝒮 𝒨) k }

/-- **Part (6) of Stacks 0B5R, the injectivity half, at the morphism of graded modules.** In a
degree where the degreewise comparison is injective, so is `N ⟶ N'` on the homogeneous piece. -/
public theorem eq_zero_of_truncatedTwistedToShiftedMor_eq_zero (k : ℤ) {n : ℤ}
    (hbij : Function.Bijective (twistedToShiftedComponent 𝒮 𝒨 n))
    (z : (truncatedTwistedSectionsObj 𝒮 (associatedModuleSheaf 𝒮 𝒨) k).carrier)
    (hz : z ∈ (truncatedTwistedSectionsObj 𝒮 (associatedModuleSheaf 𝒮 𝒨) k).grade n)
    (hzero : (truncatedTwistedToShiftedMor 𝒮 𝒨 k).toLinearMap z = 0) : z = 0 := by
  let := (twistedGlobalSectionsModule 𝒮 (associatedModuleSheaf 𝒮 𝒨)).moduleInst
  let := (twistedGlobalSectionsModule 𝒮 (associatedModuleSheaf 𝒮 𝒨)).gradedSMul
  let := (globalSectionsModuleMap 𝒮 𝒨).moduleInst
  let := (globalSectionsModuleMap 𝒮 𝒨).gradedSMul
  obtain ⟨zv, hzmem⟩ := z
  have hzg : zv ∈ twistedGlobalSectionsGrading 𝒮 (associatedModuleSheaf 𝒮 𝒨) n := hz
  obtain ⟨t, ht⟩ :=
    (DirectSum.mem_rangeGrading ℤ
      (fun j : ℤ => twistedSectionsComponent 𝒮 (associatedModuleSheaf 𝒮 𝒨) j) n zv).mp hzg
  have h1 : twistedToShiftedSections 𝒮 𝒨 zv = 0 := Subtype.ext_iff.mp hzero
  rw [ht, twistedToShiftedSections_of] at h1
  have ht0 : t = 0 :=
    hbij.1 ((DirectSum.of_injective (β := fun j : ℤ => shiftedSectionsComponent 𝒮 𝒨 j) n
      (h1.trans (map_zero _).symm)).trans (map_zero _).symm)
  have hz0 : zv = (0 : twistedGlobalSections 𝒮 (associatedModuleSheaf 𝒮 𝒨)) := by
    rw [ht, ht0, map_zero]
  exact Subtype.ext hz0

/-- **Part (6) of Stacks 0B5R, the surjectivity half, at the morphism of graded modules.** In a
degree `n ≥ k` where the degreewise comparison is surjective, the homogeneous piece of `N'` of
degree `n` lies in the image of `N ⟶ N'`. -/
public theorem exists_truncatedTwistedToShiftedMor_eq (k : ℤ) {n : ℤ} (hkn : k ≤ n)
    (hbij : Function.Bijective (twistedToShiftedComponent 𝒮 𝒨 n))
    (y : (shiftedTruncatedSectionsObj 𝒮 𝒨 k).carrier)
    (hy : y ∈ (shiftedTruncatedSectionsObj 𝒮 𝒨 k).grade n) :
    ∃ z, (truncatedTwistedToShiftedMor 𝒮 𝒨 k).toLinearMap z = y := by
  let := (twistedGlobalSectionsModule 𝒮 (associatedModuleSheaf 𝒮 𝒨)).moduleInst
  let := (twistedGlobalSectionsModule 𝒮 (associatedModuleSheaf 𝒮 𝒨)).gradedSMul
  let := (globalSectionsModuleMap 𝒮 𝒨).moduleInst
  let := (globalSectionsModuleMap 𝒮 𝒨).gradedSMul
  obtain ⟨yv, hymem⟩ := y
  have hyg : yv ∈ shiftedModuleGlobalSectionsGrading 𝒮 𝒨 n := hy
  obtain ⟨s, hs⟩ :=
    (DirectSum.mem_rangeGrading ℤ (fun j : ℤ => shiftedSectionsComponent 𝒮 𝒨 j) n yv).mp hyg
  obtain ⟨t, hts⟩ := hbij.2 s
  have hmem : (DirectSum.of
      (fun j : ℤ => twistedSectionsComponent 𝒮 (associatedModuleSheaf 𝒮 𝒨) j) n t :
        twistedGlobalSections 𝒮 (associatedModuleSheaf 𝒮 𝒨)) ∈
      truncationAbove 𝒮 (twistedGlobalSectionsGrading 𝒮 (associatedModuleSheaf 𝒮 𝒨)) k :=
    mem_truncationAbove_of_mem 𝒮
      (twistedGlobalSectionsGrading 𝒮 (associatedModuleSheaf 𝒮 𝒨)) k hkn
      ((DirectSum.mem_rangeGrading ℤ
        (fun j : ℤ => twistedSectionsComponent 𝒮 (associatedModuleSheaf 𝒮 𝒨) j) n _).mpr ⟨t, rfl⟩)
  refine ⟨(⟨_, hmem⟩ :
    ↥(truncationAbove 𝒮 (twistedGlobalSectionsGrading 𝒮 (associatedModuleSheaf 𝒮 𝒨)) k)),
    Subtype.ext ?_⟩
  change twistedToShiftedSections 𝒮 𝒨
      (DirectSum.of
        (fun j : ℤ => twistedSectionsComponent 𝒮 (associatedModuleSheaf 𝒮 𝒨) j) n t) = yv
  rw [twistedToShiftedSections_of, hts, hs]

end Bare

/-! ### Part (4) as a morphism of graded modules -/

section Module

variable (X : GradedModuleCat.{u, u, u} 𝒮) (k : ℤ)

/-- **Stacks 0B5R (4) as a morphism of graded modules**, `M ⟶ N'`, for `M` vanishing in degrees
`< k`. The underlying map is the `A`-linear map of Equation 01MR, corestricted to `N'`. -/
public def moduleToShiftedTruncation
    (hlow : ∀ n : ℤ, n < k → ∀ x ∈ X.grade n, x = (0 : X.carrier)) :
    X ⟶ shiftedTruncatedSectionsObj 𝒮 X.grade k :=
  letI := (globalSectionsModuleMap 𝒮 X.grade).moduleInst
  letI := (globalSectionsModuleMap 𝒮 X.grade).gradedSMul
  { toLinearMap := LinearMap.codRestrict _ (globalSectionsModuleMap 𝒮 X.grade).hom
      (fun m => by
        refine (mem_truncationAbove_shiftedModuleGlobalSectionsGrading_iff 𝒮 X.grade k _).mpr ?_
        exact globalSectionsModuleMap_hom_mem_truncation 𝒮 X.grade k hlow m)
    map_grade := fun i m hm => by
      change (globalSectionsModuleMap 𝒮 X.grade).hom m ∈
        shiftedModuleGlobalSectionsGrading 𝒮 X.grade i
      exact (DirectSum.mem_rangeGrading ℤ
        (fun j : ℤ => shiftedSectionsComponent 𝒮 X.grade j) i _).mpr
        ⟨degreeNToGlobalSections 𝒮 X.grade i ⟨m, hm⟩,
          globalSectionsModuleMap_hom_of_mem 𝒮 X.grade i m hm⟩ }

/-- **Part (5) of Stacks 0B5R, the injectivity half, at the morphism of graded modules.** In a
degree where the map of Tag 0AG2 is injective, so is `M ⟶ N'` on the homogeneous piece. -/
public theorem eq_zero_of_moduleToShiftedTruncation_eq_zero
    (hlow : ∀ n : ℤ, n < k → ∀ x ∈ X.grade n, x = (0 : X.carrier)) {n : ℤ}
    (hbij : Function.Bijective (degreeNToGlobalSections 𝒮 X.grade n))
    (m : X.carrier) (hm : m ∈ X.grade n)
    (hzero : (moduleToShiftedTruncation 𝒮 X k hlow).toLinearMap m = 0) : m = 0 := by
  let := (globalSectionsModuleMap 𝒮 X.grade).moduleInst
  let := (globalSectionsModuleMap 𝒮 X.grade).gradedSMul
  have h1 : (globalSectionsModuleMap 𝒮 X.grade).hom m = 0 := Subtype.ext_iff.mp hzero
  have hof : (globalSectionsModuleMap 𝒮 X.grade).hom m =
      DirectSum.of (fun j : ℤ => shiftedSectionsComponent 𝒮 X.grade j) n
        (degreeNToGlobalSections 𝒮 X.grade n ⟨m, hm⟩) :=
    globalSectionsModuleMap_hom_of_mem 𝒮 X.grade n m hm
  rw [hof] at h1
  have h2 : (⟨m, hm⟩ : X.grade n) = 0 :=
    hbij.1 ((DirectSum.of_injective
      (β := fun j : ℤ => shiftedSectionsComponent 𝒮 X.grade j) n
      (h1.trans (map_zero _).symm)).trans (map_zero _).symm)
  exact ZeroMemClass.coe_eq_zero.mpr h2

/-- **Part (5) of Stacks 0B5R, the surjectivity half, at the morphism of graded modules.** In a
degree where the map of Tag 0AG2 is surjective, the homogeneous piece of `N'` of that degree lies
in the image of `M ⟶ N'`. -/
public theorem exists_moduleToShiftedTruncation_eq
    (hlow : ∀ n : ℤ, n < k → ∀ x ∈ X.grade n, x = (0 : X.carrier)) {n : ℤ}
    (hbij : Function.Bijective (degreeNToGlobalSections 𝒮 X.grade n))
    (y : (shiftedTruncatedSectionsObj 𝒮 X.grade k).carrier)
    (hy : y ∈ (shiftedTruncatedSectionsObj 𝒮 X.grade k).grade n) :
    ∃ m, (moduleToShiftedTruncation 𝒮 X k hlow).toLinearMap m = y := by
  let := (globalSectionsModuleMap 𝒮 X.grade).moduleInst
  let := (globalSectionsModuleMap 𝒮 X.grade).gradedSMul
  obtain ⟨yv, hymem⟩ := y
  have hyg : yv ∈ shiftedModuleGlobalSectionsGrading 𝒮 X.grade n := hy
  obtain ⟨s, hs⟩ :=
    (DirectSum.mem_rangeGrading ℤ
      (fun j : ℤ => shiftedSectionsComponent 𝒮 X.grade j) n yv).mp hyg
  obtain ⟨m, hms⟩ := hbij.2 s
  refine ⟨(m : X.carrier), Subtype.ext ?_⟩
  have hof : (globalSectionsModuleMap 𝒮 X.grade).hom (m : X.carrier) =
      DirectSum.of (fun j : ℤ => shiftedSectionsComponent 𝒮 X.grade j) n
        (degreeNToGlobalSections 𝒮 X.grade n ⟨(m : X.carrier), m.2⟩) :=
    globalSectionsModuleMap_hom_of_mem 𝒮 X.grade n (m : X.carrier) m.2
  change (globalSectionsModuleMap 𝒮 X.grade).hom (m : X.carrier) = yv
  rw [hof, hs]
  exact congrArg (DirectSum.of (fun j : ℤ => shiftedSectionsComponent 𝒮 X.grade j) n) hms

end Module

end Stacks.AlgebraicGeometry.ProjSerreCorrespondence

end
